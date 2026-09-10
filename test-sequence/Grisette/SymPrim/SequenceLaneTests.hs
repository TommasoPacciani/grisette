{-# LANGUAGE GHC2024 #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}

-- Independent scalar-lane laws: literal observations establish pruning before
-- lowering; opaque whole-result bindings exercise the actual solver operations.
module Grisette.SymPrim.SequenceLaneTests (sequenceLaneTests) where

import Control.Concurrent (forkIO, newEmptyMVar, putMVar, takeMVar)
import Control.DeepSeq (force)
import Control.Exception (evaluate)
import Control.Monad (forM_)
import qualified Data.Binary as Binary
import Data.Bits ((.&.), (.|.))
import Data.List (foldl')
import Grisette
  ( AsKey (AsKey), BitCast (bitCast)
  , EvalSym (evalSym), ExtractSym (extractSym), Function ((#))
  , LogicalOp (symNot, (.&&)), SimpleMergeable (mrgIte)
  , Solvable (con, isym), SubstSym (substSym), SymEq ((.==))
  , SymOrd ((.<), (.<=))
  , SymBool, SymInteger, ToCon (toCon), TypedConstantSymbol, solve )
import Grisette.Internal.Backend.Solving (z3)
import Grisette.Internal.Core.Data.Class.IEEEFP
  ( IEEEFPConstants (fpNegativeZero, fpPositiveZero) )
import Grisette.Internal.Core.Data.Class.Solver (SolvingFailure (Unsat))
import Grisette.Internal.Core.Data.Class.SymIEEEFP
  ( SymIEEEFPTraits (symFpIsNegativeZero, symFpIsZero) )
import Grisette.Internal.SymPrim.AlgReal (AlgReal (AlgInexactRational))
import Grisette.Internal.SymPrim.Prim.Term
  ( LinkedRep (underlyingTerm, wrapTerm), toCurThread
  , pattern SeqLookupTerm, pattern SeqLookupValueTerm )
import Grisette.Internal.SymPrim.Prim.TermUtils (termSize)
import Grisette.SymPrim
  ( FP32, IntN, SymAlgReal, SymFP32, SymIntN, SymSeq, SymWordN, WordN
  , type (-~>), (-->) )
import Grisette.Unified (EvalModeTag (C, S))
import qualified Grisette.Unified as U
import System.Timeout (timeout)
import Test.Framework (Test, testGroup)
import Test.Framework.Providers.HUnit (testCase)
import Test.HUnit (Assertion, assertBool, assertEqual, assertFailure)

-- The public operations need only their scalar element's evidence, including
-- when that scalar is itself a sequence. No fold or product evidence leaks out.
resizeAndUpdate
  :: forall mode value. (U.UnifiedSeq mode, U.SeqValue mode value)
  => value -> U.GetInteger mode -> U.GetSeq mode value
  -> U.GetInteger mode -> value -> U.GetSeq mode value
resizeAndUpdate seed count source index value =
  U.updateSeq @mode index value (U.resizeSeq @mode seed count source)

data LaneFixture = LaneFixture
  { fixtureLabel :: String
  , fixtureSeed :: Integer
  , fixtureCount :: Integer
  , fixtureSource :: [Integer]
  , fixtureIndex :: Integer
  , fixtureReplacement :: Integer
  , fixtureResized :: [Integer]
  , fixtureUpdated :: [Integer]
  }

-- Explicit expected values are independent of both implementations. Source
-- lengths deliberately disagree with the requested logical extent.
laneFixtures :: [LaneFixture]
laneFixtures =
  [ LaneFixture "negative extent" 7 (-2) [1, 2] 0 99 [] []
  , LaneFixture "zero extent" 7 0 [1, 2] 0 99 [] []
  , LaneFixture "singleton extension" 7 1 [] 0 99 [7] [99]
  , LaneFixture "empty source extension" 7 3 [] 1 99 [7, 7, 7] [7, 99, 7]
  , LaneFixture "truncate source" 7 1 [1, 2, 3] 0 99 [1] [99]
  , LaneFixture "unchanged extent" 7 3 [1, 2, 3] 1 99 [1, 2, 3] [1, 99, 3]
  , LaneFixture "pad short source" 7 5 [1, 2] 3 99 [1, 2, 7, 7, 7] [1, 2, 7, 99, 7]
  , LaneFixture "negative update" 7 3 [1, 2] (-1) 99 [1, 2, 7] [1, 2, 7]
  , LaneFixture "update at upper bound" 7 3 [1, 2] 3 99 [1, 2, 7] [1, 2, 7]
  , LaneFixture "update beyond upper bound" 7 3 [1, 2] 8 99 [1, 2, 7] [1, 2, 7]
  ]

sequenceLaneTests :: Test
sequenceLaneTests = testGroup "total scalar sequence lanes"
  [ testCase "concrete resize and point update match explicit whole values" $
      forM_ laneFixtures $ \fixture -> do
        let resized = U.resizeSeq @'C (fixtureSeed fixture)
              (fixtureCount fixture) (fixtureSource fixture)
            updated = resizeAndUpdate @'C (fixtureSeed fixture)
              (fixtureCount fixture) (fixtureSource fixture)
              (fixtureIndex fixture) (fixtureReplacement fixture)
        assertEqual (fixtureLabel fixture ++ ": resize")
          (fixtureResized fixture) resized
        assertEqual (fixtureLabel fixture ++ ": update")
          (fixtureUpdated fixture) updated
        assertEqual (fixtureLabel fixture ++ ": update preserves normalized length")
          (length resized) (length updated)
  , testCase "symbolic literal length and cell observations require no solver" $
      forM_ laneFixtures $ \fixture -> do
        let resized = U.resizeSeq @'S (con (fixtureSeed fixture))
              (con (fixtureCount fixture)) (con (fixtureSource fixture))
            updated = resizeAndUpdate @'S (con (fixtureSeed fixture))
              (con (fixtureCount fixture)) (con (fixtureSource fixture))
              (con (fixtureIndex fixture)) (con (fixtureReplacement fixture))
        checkIntegerCells (fixtureLabel fixture ++ ": resize")
          (fixtureResized fixture) resized
        checkIntegerCells (fixtureLabel fixture ++ ": update")
          (fixtureUpdated fixture) updated
  , testCase "empty and nonpositive owner ranges fold to the exact initial state" $ do
      let initial = "lane.empty.initial" :: SymInteger
          template = U.FocusedCapture (0 :: SymInteger) U.FocusedNoCaptures
          prepared = U.prepareFocusedSeqFold @'S template $
            \(U.FocusedCapture scale U.FocusedNoCaptures) state index ->
              state + scale * index
          captures = U.FocusedCapture ("lane.empty.scale" :: SymInteger)
            U.FocusedNoCaptures
      forM_ [-3, 0] $ \count -> do
        let range = U.rangeSeq @'S (con count)
            folded = U.applyFocusedSeqFold @'S prepared captures initial range
        assertEqual "literal empty range" (Just [] :: Maybe [Integer]) (toCon range)
        assertEqual "no residual empty owner fold" (AsKey initial) (AsKey folded)
        assertEqual "nonpositive resize is literally empty"
          (Just [] :: Maybe [Integer])
          (toCon (U.resizeSeq @'S 7 (con count)
            ("lane.empty.source" :: SymSeq SymInteger)))
  , testCase "known vacant cells stay literal at arbitrary symbolic indices" $ do
      let index = "lane.vacant.index" :: SymInteger
          count = "lane.vacant.count" :: SymInteger
          target = "lane.vacant.target" :: SymInteger
          blank = con False :: SymBool
          population = U.resizeSeq @'S blank count U.nilSeq
      forM_ [[], [False], [False, False, False, False]] $ \values ->
        assertEqual "constant vacant population lookup" (Just False)
          (toCon (U.lookupSeqValue @'S blank (con values) index) :: Maybe Bool)
      assertEqual "symbolic blank replication lookup" (Just False)
        (toCon (U.lookupSeqValue @'S blank population index) :: Maybe Bool)
      assertEqual "writing the blank cannot revive a vacant population" (Just False)
        (toCon (U.lookupSeqValue @'S blank
          (U.updateSeq @'S target blank population) index) :: Maybe Bool)
      let nonzero = U.resizeSeq @'S (7 :: SymInteger) count U.nilSeq
      assertEqual "nonzero fallback is not generic zero" (Just 7)
        (toCon (U.lookupSeqValue @'S 7 nonzero index) :: Maybe Integer)
      assertEqual "homogeneous nonzero literal lookup" (Just 7)
        (toCon (U.lookupSeqValue @'S 7 (con [7, 7, 7 :: Integer]) index) :: Maybe Integer)
  , testCase "homogeneous literal reads are exact constant-size bounds choices" $ do
      let index = "lane.literal.shape.index" :: SymInteger
          symbolicSeed = "lane.literal.shape.seed" :: SymInteger
          empty = con [] :: SymSeq SymInteger
          absent = U.lookupSeq @'S symbolicSeed empty index
      assertEqual "empty value read preserves symbolic fallback"
        (AsKey symbolicSeed) (AsKey (U.lookupSeqValue @'S symbolicSeed empty index))
      assertEqual "empty checked read is absent" (Just False)
        (toCon (U.first @'S absent))
      assertEqual "empty checked read preserves symbolic fallback"
        (AsKey symbolicSeed) (AsKey (U.second @'S absent))
      forM_ [1, 2, 31, 257] $ \count ->
        forM_ [7, 41, symbolicSeed] $ \seed -> do
          let values = con (replicate count (7 :: Integer)) :: SymSeq SymInteger
              present = literalLookupRange (toInteger count) index
              expected = mrgIte present 7 seed
              value = U.lookupSeqValue @'S seed values index
              checked = U.lookupSeq @'S seed values index
              (partsPresent, partsValue) = U.lookupSeqParts @'S
                (con (toInteger count)) seed values index
          assertEqual "value-only read is exactly the scalar bounds ITE"
            (AsKey expected) (AsKey value)
          assertEqual "checked read exposes exactly the bounds"
            (AsKey present) (AsKey (U.first @'S checked))
          assertEqual "checked read exposes exactly the scalar bounds ITE"
            (AsKey expected) (AsKey (U.second @'S checked))
          assertEqual "authoritative parts retain exact presence"
            (AsKey present) (AsKey partsPresent)
          assertEqual "authoritative parts retain exact value"
            (AsKey expected) (AsKey partsValue)
          assertEqual "term size is the fixed-size bounds expression, not population size"
            (termSize (underlyingTerm expected)) (termSize (underlyingTerm value))
  , testCase "homogeneous literal bounds agree with explicit C and S observations" $ do
      let fixtures =
            [ ([], [(-1, False, 41), (0, False, 41), (1, False, 41)])
            , ([7], [(-1, False, 41), (0, True, 7), (1, False, 41)])
            , ([7, 7], [(-8, False, 41), (0, True, 7), (1, True, 7),
                (2, False, 41), (99, False, 41)])
            ] :: [([Integer], [(Integer, Bool, Integer)])]
          symbolicIndex = "lane.literal.bounds.index" :: SymInteger
      forM_ fixtures $ \(values, observations) -> do
        let readValue = U.lookupSeqValue @'S 41 (con values) symbolicIndex
            readPair = U.lookupSeq @'S 41 (con values) symbolicIndex
        forM_ observations $ \(index, present, value) -> do
          let substitute :: SubstSym a => a -> a
              substitute = substSym
                ("lane.literal.bounds.index" :: TypedConstantSymbol Integer)
                (con index)
          assertEqual "independent concrete checked read" (present, value)
            (U.lookupSeq @'C 41 values index)
          assertEqual "independent concrete value-only read" value
            (U.lookupSeqValue @'C 41 values index)
          assertEqual "symbolic-index substitution preserves checked read"
            (Just (present, value)) (toCon (substitute readPair))
          assertEqual "symbolic-index substitution preserves exact fallback"
            (Just value) (toCon (substitute readValue))
  , testCase "free homogeneous indices reach real-Z3 SAT and UNSAT with exact fallback" $
      within "homogeneous symbolic-index lowering" $ do
        let trials = zipWith trial [0 ..]
              [ (\index -> literalLookupRange 2 index, True, 7)
              , (\index -> index .< 0, False, 41)
              , (\index -> 2 .<= index, False, 41)
              ]
            trial ordinal (domain, expectedPresent, expectedValue) =
              let index = isym "lane.literal.solver.index" ordinal :: SymInteger
                  seed = isym "lane.literal.solver.seed" ordinal :: SymInteger
                  output = isym "lane.literal.solver.output" ordinal :: SymInteger
                  source = con [7, 7 :: Integer] :: SymSeq SymInteger
                  value = U.lookupSeqValue @'S seed source index
                  checked = U.lookupSeq @'S seed source index
                  trialInputs = domain index .&& (seed .== 41) .&& (output .== value)
                  trialFacts = (output .== con expectedValue)
                    .&& (U.first @'S checked .== con expectedPresent)
                    .&& (U.second @'S checked .== con expectedValue)
              in (trialInputs, trialFacts, output, checked, expectedPresent, expectedValue)
            inputs = conjunction [domain | (domain, _, _, _, _, _) <- trials]
            facts = conjunction [valid | (_, valid, _, _, _, _) <- trials]
        solve z3 (inputs .&& facts) >>= \case
          Left failure -> assertFailure $ "expected homogeneous real-Z3 SAT: " ++ show failure
          Right model -> forM_ trials $ \(_, _, output, checked, present, value) -> do
            assertEqual "free-index scalar output model" (Just value)
              (toCon (evalSym False model output))
            assertEqual "free-index presence and exact fallback model" (Just (present, value))
              (toCon (evalSym False model checked))
        expectUnsat (inputs .&& symNot facts)
  , testCase "one-bit Boolean decoding preserves both concrete bit patterns" $ do
      forM_ ([(0, False), (-1, True)] :: [(IntN 1, Bool)]) $ \(bits, expected) -> do
        assertEqual "concrete signed one-bit truth table" expected
          (bitCast bits :: Bool)
        assertEqual "symbolic signed one-bit truth table" (Just expected)
          (toCon (bitCast (con bits :: SymIntN 1) :: SymBool))
      forM_ ([(0, False), (1, True)] :: [(WordN 1, Bool)]) $ \(bits, expected) -> do
        assertEqual "concrete unsigned one-bit truth table" expected
          (bitCast bits :: Bool)
        assertEqual "symbolic unsigned one-bit truth table" (Just expected)
          (toCon (bitCast (con bits :: SymWordN 1) :: SymBool))
  , testCase "balanced one-bit choices decode to the exact Boolean choice tree" $ do
      let (expected, signed, unsigned) = booleanBitFixture
            ("lane.bit.flag" :: SymBool)
      assertEqual "signed choices retain all four independent flags"
        (AsKey expected) (AsKey (bitCast signed :: SymBool))
      assertEqual "unsigned choices retain all four independent flags"
        (AsKey expected) (AsKey (bitCast unsigned :: SymBool))
  , testCase "raw symbolic one-bit leaves retain their nonzero solver semantics" $
      within "raw one-bit Boolean lowering" $ do
        let signed = "lane.bit.raw.signed" :: SymIntN 1
            unsigned = "lane.bit.raw.unsigned" :: SymWordN 1
            signedBoolean = bitCast signed :: SymBool
            unsignedBoolean = bitCast unsigned :: SymBool
            signedNonzero = symNot (signed .== 0)
            unsignedNonzero = symNot (unsigned .== 0)
            facts = (signedBoolean .== signedNonzero)
              .&& (unsignedBoolean .== unsignedNonzero)
        solve z3 (signedNonzero .&& unsignedNonzero .&& facts) >>= \case
          Left failure -> assertFailure $ "expected one-bit real-Z3 SAT: " ++ show failure
          Right model -> do
            assertEqual "signed set bit is negative one" (Just (-1) :: Maybe (IntN 1))
              (toCon (evalSym False model signed))
            assertEqual "unsigned set bit is one" (Just 1 :: Maybe (WordN 1))
              (toCon (evalSym False model unsigned))
            assertEqual "signed set bit decodes to true" (Just True)
              (toCon (evalSym False model signedBoolean))
            assertEqual "unsigned set bit decodes to true" (Just True)
              (toCon (evalSym False model unsignedBoolean))
        expectUnsat (symNot facts)
  , testCase "shared deep one-bit choices decode to a linear Boolean DAG" $
      within "shared one-bit Boolean decoding" $ do
        let flag = "lane.bit.shared.flag" :: SymBool
            initial = (flag, mrgIte flag 1 0 :: SymIntN 1,
              mrgIte flag 1 0 :: SymWordN 1)
            extend (priorBoolean, priorSigned, priorUnsigned) ordinal =
              let outer = isym "lane.bit.shared.outer" ordinal :: SymBool
                  inner = isym "lane.bit.shared.inner" ordinal :: SymBool
              in ( mrgIte outer
                     (mrgIte inner priorBoolean (con False))
                     (mrgIte inner (con True) priorBoolean)
                 , mrgIte outer (mrgIte inner priorSigned 0)
                     (mrgIte inner 1 priorSigned)
                 , mrgIte outer (mrgIte inner priorUnsigned 0)
                     (mrgIte inner 1 priorUnsigned)
                 )
        forM_ [1, 8, 32, 64] $ \depth -> do
          let (expected, signed, unsigned) = foldl' extend initial [0 .. depth - 1]
              decodedSigned = bitCast signed :: SymBool
              decodedUnsigned = bitCast unsigned :: SymBool
              expectedSize = termSize (underlyingTerm expected)
          assertEqual "signed input retains shared branches" (5 * depth + 5)
            (termSize (underlyingTerm signed))
          assertEqual "unsigned input retains shared branches" (5 * depth + 5)
            (termSize (underlyingTerm unsigned))
          assertEqual "shared signed DAG has the exact Boolean meaning"
            (AsKey expected) (AsKey decodedSigned)
          assertEqual "shared unsigned DAG has the exact Boolean meaning"
            (AsKey expected) (AsKey decodedUnsigned)
          assertEqual "independent Boolean DAG remains linear" (5 * depth + 1)
            expectedSize
          assertEqual "signed decoding adds no residual bitcast nodes" expectedSize
            (termSize (underlyingTerm decodedSigned))
          assertEqual "unsigned decoding adds no residual bitcast nodes" expectedSize
            (termSize (underlyingTerm decodedUnsigned))
  , testCase "one-bit decoding canonicalizes binary-reconstructed input choices" $ do
      let (expected, signed, unsigned) = booleanBitFixture
            ("lane.bit.binary.flag" :: SymBool)
          signedRoundTrip = Binary.decode (Binary.encode signed) :: SymIntN 1
          unsignedRoundTrip = Binary.decode (Binary.encode unsigned) :: SymWordN 1
      assertEqual "signed input tree round-trips before decoding"
        (AsKey signed) (AsKey signedRoundTrip)
      assertEqual "unsigned input tree round-trips before decoding"
        (AsKey unsigned) (AsKey unsignedRoundTrip)
      assertEqual "binary-reconstructed signed input decodes canonically"
        (AsKey expected) (AsKey (bitCast signedRoundTrip :: SymBool))
      assertEqual "binary-reconstructed unsigned input decodes canonically"
        (AsKey expected) (AsKey (bitCast unsignedRoundTrip :: SymBool))
  , testCase "one-bit decoding canonicalizes substituted input choices" $ do
      let (_, signed, unsigned) = booleanBitFixture
            ("lane.bit.substitution.flag" :: SymBool)
          replacement = ("lane.bit.substitution.left" :: SymBool)
            .&& symNot ("lane.bit.substitution.right" :: SymBool)
          (expected, expectedSigned, expectedUnsigned) = booleanBitFixture replacement
          substitute :: SubstSym value => value -> value
          substitute = substSym
            ("lane.bit.substitution.flag" :: TypedConstantSymbol Bool) replacement
          substitutedSigned = substitute signed
          substitutedUnsigned = substitute unsigned
      assertEqual "signed input substitution preserves the complete tree"
        (AsKey expectedSigned) (AsKey substitutedSigned)
      assertEqual "unsigned input substitution preserves the complete tree"
        (AsKey expectedUnsigned) (AsKey substitutedUnsigned)
      assertEqual "substituted signed input decodes canonically"
        (AsKey expected) (AsKey (bitCast substitutedSigned :: SymBool))
      assertEqual "substituted unsigned input decodes canonically"
        (AsKey expected) (AsKey (bitCast substitutedUnsigned :: SymBool))
  , testCase "one-bit decoding canonicalizes general-function input choices" $ do
      let (_, signedBody, unsignedBody) = booleanBitFixture
            ("lane.bit.function.flag" :: SymBool)
          signedFunction :: SymBool -~> SymIntN 1
          signedFunction = con $
            ("lane.bit.function.flag" :: TypedConstantSymbol Bool) --> signedBody
          unsignedFunction :: SymBool -~> SymWordN 1
          unsignedFunction = con $
            ("lane.bit.function.flag" :: TypedConstantSymbol Bool) --> unsignedBody
          argument = "lane.bit.function.argument" :: SymBool
          (expected, expectedSigned, expectedUnsigned) = booleanBitFixture argument
          appliedSigned = signedFunction # argument
          appliedUnsigned = unsignedFunction # argument
      assertEqual "signed function reconstructs the complete input tree"
        (AsKey expectedSigned) (AsKey appliedSigned)
      assertEqual "unsigned function reconstructs the complete input tree"
        (AsKey expectedUnsigned) (AsKey appliedUnsigned)
      assertEqual "signed function result decodes canonically"
        (AsKey expected) (AsKey (bitCast appliedSigned :: SymBool))
      assertEqual "unsigned function result decodes canonically"
        (AsKey expected) (AsKey (bitCast appliedUnsigned :: SymBool))
  , testCase "one-bit decoding canonicalizes cross-thread input choices" $ do
      let (expected, signed, unsigned) = booleanBitFixture
            ("lane.bit.thread.flag" :: SymBool)
      box <- newEmptyMVar
      _ <- forkIO $ do
        signedChild <- toCurThread (underlyingTerm signed)
        unsignedChild <- toCurThread (underlyingTerm unsigned)
        inputs <- evaluate $ force (signedChild, unsignedChild)
        putMVar box inputs
      (signedChild, unsignedChild) <- takeMVar box
      signedRebuilt <- toCurThread signedChild
      unsignedRebuilt <- toCurThread unsignedChild
      let signedInput = wrapTerm signedRebuilt :: SymIntN 1
          unsignedInput = wrapTerm unsignedRebuilt :: SymWordN 1
      assertEqual "signed input survives both thread transfers"
        (AsKey signed) (AsKey signedInput)
      assertEqual "unsigned input survives both thread transfers"
        (AsKey unsigned) (AsKey unsignedInput)
      assertEqual "cross-thread signed input decodes canonically"
        (AsKey expected) (AsKey (bitCast signedInput :: SymBool))
      assertEqual "cross-thread unsigned input decodes canonically"
        (AsKey expected) (AsKey (bitCast unsignedInput :: SymBool))
  , testCase "nested and BV1 homogeneous literals preserve their actual element sorts" $
      within "nested and BV1 homogeneous lookup" $ do
        let index = "lane.literal.nested.index" :: SymInteger
            seed = "lane.literal.nested.seed" :: SymSeq SymInteger
            nested = con [[0 :: Integer]] :: SymSeq (SymSeq SymInteger)
            nestedValue = U.lookupSeqValue @'S seed nested index
            nestedPair = U.lookupSeq @'S seed nested index
            expectedNested = mrgIte (literalLookupRange 1 index) (con [0 :: Integer]) seed
            presenceIndex = "lane.literal.presence.index" :: SymInteger
            presence = con [1, 1 :: WordN 1] :: SymSeq (SymWordN 1)
            presenceValue = U.lookupSeqValue @'S 0 presence presenceIndex
            presencePair = U.lookupSeq @'S 0 presence presenceIndex
            expectedPresence = mrgIte (literalLookupRange 2 presenceIndex)
              (1 :: SymWordN 1) 0
            nestedOutput = "lane.literal.nested.output" :: SymSeq SymInteger
            presenceOutput = "lane.literal.presence.output" :: SymWordN 1
        assertEqual "nested element remains one sequence-valued bounds ITE"
          (underlyingTerm expectedNested) (underlyingTerm nestedValue)
        assertEqual "nested checked value shares the exact bounds ITE"
          (underlyingTerm expectedNested) (underlyingTerm (U.second @'S nestedPair))
        assertEqual "BV1 presence lane is not replaced by generic Boolean data"
          (AsKey expectedPresence) (AsKey presenceValue)
        assertEqual "BV1 checked value shares the exact bounds ITE"
          (AsKey expectedPresence) (AsKey (U.second @'S presencePair))
        forM_ [(True, [0 :: Integer], 1 :: WordN 1), (False, [-9], 0)] $
          \(inside, expectedNestedValue, expectedPresenceValue) -> do
            let domain = if inside
                  then literalLookupRange 1 index .&& literalLookupRange 2 presenceIndex
                  else (index .< 0) .&& (2 .<= presenceIndex)
                inputs = domain .&& (seed .== con [-9 :: Integer])
                  .&& (nestedOutput .== nestedValue) .&& (presenceOutput .== presenceValue)
                facts = (nestedOutput .== con expectedNestedValue)
                  .&& (presenceOutput .== con expectedPresenceValue)
                  .&& (U.first @'S nestedPair .== con inside)
                  .&& (U.first @'S presencePair .== con inside)
            solve z3 (inputs .&& facts) >>= \case
              Left failure -> assertFailure $ "expected nested/BV1 real-Z3 SAT: " ++ show failure
              Right model -> do
                assertEqual "nested output model" (Just expectedNestedValue)
                  (toCon (evalSym False model nestedOutput))
                assertEqual "BV1 output model" (Just expectedPresenceValue)
                  (toCon (evalSym False model presenceOutput))
            expectUnsat (inputs .&& symNot facts)
  , testCase "homogeneous reads compose with sequence choice and symbolic point updates" $ do
      let condition = "lane.literal.composition.choice" :: SymBool
          index = "lane.literal.composition.index" :: SymInteger
          target = "lane.literal.composition.target" :: SymInteger
          replacement = "lane.literal.composition.replacement" :: SymInteger
          seed = "lane.literal.composition.seed" :: SymInteger
          chosen = mrgIte condition (con [7, 7 :: Integer]) (con [9 :: Integer])
          selectedLength = mrgIte condition (2 :: SymInteger) 1
          selectedPresence = (0 .<= index) .&& (index .< selectedLength)
          writePresence = symNot (index .< 0) .&& (index .< selectedLength)
          original = mrgIte condition
            (mrgIte (literalLookupRange 2 index) 7 seed)
            (mrgIte (literalLookupRange 1 index) 9 seed)
          expected = mrgIte ((index .== target) .&& writePresence) replacement original
          actual = U.updateSeq @'S target replacement chosen
          checked = U.lookupSeq @'S seed actual index
      assertValid "complete sequence choice keeps both exact literal bounds"
        (U.lookupSeqValue @'S seed chosen index .== original)
      assertValid "point update uses the selected extent and exact original fallback"
        (U.lookupSeqValue @'S seed actual index .== expected)
      assertEqual "checked update retains selected presence"
        (AsKey selectedPresence) (AsKey (U.first @'S checked))
      assertValid "checked update retains the exact composed value"
        (U.second @'S checked .== expected)
  , testCase "heterogeneous and unconstrained sequences retain native lookup authority" $ do
      let seed = "lane.literal.native.seed" :: SymInteger
          index = "lane.literal.native.index" :: SymInteger
          opaque = "lane.literal.native.source" :: SymSeq SymInteger
          heterogeneous = con [7, 9 :: Integer] :: SymSeq SymInteger
          checkNative :: SymSeq SymInteger -> Assertion
          checkNative source = do
            case underlyingTerm (U.lookupSeqValue @'S seed source index) of
              SeqLookupValueTerm actualSeed actualSource actualIndex -> do
                assertEqual "native value fallback" (underlyingTerm seed) actualSeed
                assertEqual "native value source" (underlyingTerm source) actualSource
                assertEqual "native value index" (underlyingTerm index) actualIndex
              _ -> assertFailure "heterogeneous or unconstrained value lookup was expanded"
            case underlyingTerm (U.lookupSeq @'S seed source index) of
              SeqLookupTerm actualSeed actualSource actualIndex -> do
                assertEqual "native checked fallback" (underlyingTerm seed) actualSeed
                assertEqual "native checked source" (underlyingTerm source) actualSource
                assertEqual "native checked index" (underlyingTerm index) actualIndex
              _ -> assertFailure "heterogeneous or unconstrained checked lookup was expanded"
      checkNative heterogeneous
      checkNative opaque
      forM_ [(-1, False, 41), (0, True, 7), (1, True, 9), (2, False, 41)] $
        \(position, present, value) -> do
          let substitute :: SubstSym a => a -> a
              substitute = substSym
                ("lane.literal.native.seed" :: TypedConstantSymbol Integer) (41 :: SymInteger)
                . substSym ("lane.literal.native.index" :: TypedConstantSymbol Integer) (con position)
                . substSym ("lane.literal.native.source" :: TypedConstantSymbol [Integer]) heterogeneous
          assertEqual "explicit heterogeneous concrete oracle" (present, value)
            (U.lookupSeq @'C 41 [7, 9 :: Integer] position)
          forM_ [heterogeneous, opaque] $ \source -> do
            assertEqual "literal or substituted opaque value is exact" (Just value)
              (toCon (substitute (U.lookupSeqValue @'S seed source index)))
            assertEqual "literal or substituted opaque presence is exact" (Just (present, value))
              (toCon (substitute (U.lookupSeq @'S seed source index)))
  , testCase "literal classification never identifies direct or nested signed zeros" $ do
      let index = "lane.literal.signed-zero.index" :: SymInteger
          scalarSeed = "lane.literal.signed-zero.scalar.seed" :: SymFP32
          nestedSeed = "lane.literal.signed-zero.nested.seed" :: SymSeq SymFP32
          positive = fpPositiveZero :: FP32
          negative = fpNegativeZero :: FP32
          directSource = con [positive, negative] :: SymSeq SymFP32
          nestedSource = con [[positive], [negative]] :: SymSeq (SymSeq SymFP32)
          directRead = U.lookupSeqValue @'S scalarSeed directSource index
          nestedRead = U.lookupSeqValue @'S nestedSeed nestedSource index
          nestedElement = U.lookupSeqValue @'S (con (3 :: FP32)) nestedRead 0
          directPair = U.lookupSeq @'S scalarSeed directSource index
          nestedPair = U.lookupSeq @'S nestedSeed nestedSource index
          pairedNestedElement = U.lookupSeqValue @'S (con (3 :: FP32))
            (U.second @'S nestedPair) 0
      case underlyingTerm directRead of
        SeqLookupValueTerm {} -> pure ()
        _ -> assertFailure "opposite scalar signed zeros were treated as a homogeneous literal"
      case underlyingTerm nestedRead of
        SeqLookupValueTerm {} -> pure ()
        _ -> assertFailure "opposite nested signed zeros were treated as a homogeneous literal"
      case underlyingTerm directPair of
        SeqLookupTerm {} -> pure ()
        _ -> assertFailure "checked lookup collapsed opposite scalar signed zeros"
      case underlyingTerm nestedPair of
        SeqLookupTerm {} -> pure ()
        _ -> assertFailure "checked lookup collapsed opposite nested signed zeros"
      forM_ [(-1, False, False), (0, False, True), (1, True, True), (2, False, False)] $
        \(position, isNegative, isZero) -> do
          let substitute :: SubstSym a => a -> a
              substitute = substSym
                ("lane.literal.signed-zero.index" :: TypedConstantSymbol Integer) (con position)
                . substSym ("lane.literal.signed-zero.scalar.seed" :: TypedConstantSymbol FP32)
                  (con (1 :: FP32))
                . substSym ("lane.literal.signed-zero.nested.seed" :: TypedConstantSymbol [FP32])
                  (con [2 :: FP32])
          forM_ [U.first @'S directPair, U.first @'S nestedPair] $ \present ->
            assertEqual "checked signed-zero selection keeps exact presence" (Just isZero)
              (toCon (substitute present))
          forM_ [directRead, nestedElement, U.second @'S directPair, pairedNestedElement] $ \value -> do
            assertEqual "selected zero sign agrees with the explicit cell" (Just isNegative)
              (toCon (substitute (symFpIsNegativeZero value)))
            assertEqual "absent selection preserves its nonzero fallback" (Just isZero)
              (toCon (substitute (symFpIsZero value)))
  , testCase "non-exact algebraic-real literals never invoke unsupported equality" $ do
      let index = "lane.literal.inexact.index" :: SymInteger
          seed = "lane.literal.inexact.seed" :: SymAlgReal
          nestedSeed = "lane.literal.inexact.nested.seed" :: SymSeq SymAlgReal
          inexact = AlgInexactRational (3 / 2)
          source = con [inexact, inexact] :: SymSeq SymAlgReal
          nestedSource = con [[inexact], [inexact]] :: SymSeq (SymSeq SymAlgReal)
      case underlyingTerm (U.lookupSeqValue @'S seed source index) of
        SeqLookupValueTerm {} -> pure ()
        _ -> assertFailure "non-exact real classification must retain native lookup"
      case underlyingTerm (U.lookupSeq @'S seed source index) of
        SeqLookupTerm {} -> pure ()
        _ -> assertFailure "non-exact real classification must retain native checked lookup"
      case underlyingTerm (U.lookupSeqValue @'S nestedSeed nestedSource index) of
        SeqLookupValueTerm {} -> pure ()
        _ -> assertFailure "nested non-exact reals must retain native lookup"
      case underlyingTerm (U.lookupSeq @'S nestedSeed nestedSource index) of
        SeqLookupTerm {} -> pure ()
        _ -> assertFailure "nested non-exact reals must retain native checked lookup"
  , testCase "literal read plans never capture the caller's seed, index or thread" $ do
      let source = con [7, 7 :: Integer] :: SymSeq SymInteger
          firstSeed = "lane.literal.memo.first.seed" :: SymInteger
          nextSeed = "lane.literal.memo.next.seed" :: SymInteger
          firstIndex = "lane.literal.memo.first.index" :: SymInteger
          nextIndex = "lane.literal.memo.next.index" :: SymInteger
          firstRead = U.lookupSeqValue @'S firstSeed source firstIndex
          changedSeedRead = U.lookupSeqValue @'S nextSeed source firstIndex
          changedIndexRead = U.lookupSeqValue @'S firstSeed source nextIndex
          nextRead = U.lookupSeqValue @'S nextSeed source nextIndex
          changedSource = U.lookupSeqValue @'S firstSeed (con [9, 9 :: Integer]) firstIndex
      _ <- evaluate $ force firstRead
      _ <- evaluate $ force changedSeedRead
      _ <- evaluate $ force changedIndexRead
      _ <- evaluate $ force nextRead
      assertEqual "same index with a new seed keeps the new fallback"
        (AsKey (mrgIte (literalLookupRange 2 firstIndex) 7 nextSeed)) (AsKey changedSeedRead)
      assertEqual "same seed with a new index keeps the new bounds"
        (AsKey (mrgIte (literalLookupRange 2 nextIndex) 7 firstSeed)) (AsKey changedIndexRead)
      assertEqual "new caller seed and index both remain in the value"
        (extractSym (nextSeed, nextIndex)) (extractSym nextRead)
      assertEqual "shared literal does not reuse another caller's bounds or fallback"
        (AsKey (mrgIte (literalLookupRange 2 nextIndex) 7 nextSeed)) (AsKey nextRead)
      assertEqual "different literal does not reuse another population's element"
        (AsKey (mrgIte (literalLookupRange 2 firstIndex) 9 firstSeed)) (AsKey changedSource)
      assertEqual "returning to the first call preserves its exact term"
        (AsKey firstRead) (AsKey (U.lookupSeqValue @'S firstSeed source firstIndex))
      assertEqual "reduced read serialization retains caller context" (AsKey nextRead)
        (AsKey (Binary.decode (Binary.encode nextRead) :: SymInteger))
      let firstSubstitution = substSym
            ("lane.literal.memo.first.seed" :: TypedConstantSymbol Integer) (41 :: SymInteger)
            . substSym ("lane.literal.memo.first.index" :: TypedConstantSymbol Integer) (-1 :: SymInteger)
          nextSubstitution = substSym
            ("lane.literal.memo.next.seed" :: TypedConstantSymbol Integer) (99 :: SymInteger)
            . substSym ("lane.literal.memo.next.index" :: TypedConstantSymbol Integer) (2 :: SymInteger)
      assertEqual "first caller's negative fallback is exact" (Just 41 :: Maybe Integer)
        (toCon (firstSubstitution firstRead))
      assertEqual "next caller's upper-bound fallback is exact" (Just 99 :: Maybe Integer)
        (toCon (nextSubstitution nextRead))
      box <- newEmptyMVar
      _ <- forkIO $ do
        term <- evaluate $ force $ underlyingTerm $
          U.lookupSeqValue @'S ("lane.literal.memo.next.seed" :: SymInteger)
            (con [7, 7 :: Integer]) ("lane.literal.memo.next.index" :: SymInteger)
        putMVar box term
      rebuilt <- takeMVar box >>= toCurThread
      assertEqual "memoized literal read reconstructs in the current thread"
        (underlyingTerm nextRead) rebuilt
  , testCase "nonempty nested defaults retain their exact content and absence" $ do
      let blank = [7, 8 :: Integer]
          original = [[1], [2, 3 :: Integer]]
          expected = [[1], [2, 3], [9, 10], blank]
          concrete = resizeAndUpdate @'C blank 4 original 2 [9, 10]
          symbolic = resizeAndUpdate @'S (con blank :: SymSeq SymInteger)
            4 (con original) 2 (con [9, 10 :: Integer])
          count = "lane.nested.count" :: SymInteger
          index = "lane.nested.index" :: SymInteger
          target = "lane.nested.target" :: SymInteger
          population = U.resizeSeq @'S (con blank :: SymSeq SymInteger) count U.nilSeq
      assertEqual "concrete nested resize/update" expected concrete
      assertEqual "nested length" (Just 4 :: Maybe Integer)
        (toCon (U.lengthSeq @'S symbolic))
      forM_ (zip [0 ..] expected) $ \(position, value) ->
        assertEqual "literal nested cell" (Just value)
          (toCon (U.lookupSeqValue @'S (con [-41 :: Integer]) symbolic (con position)))
      forM_ [-1, 4, 9] $ \position ->
        assertEqual "nested OOB uses lookup fallback, not padding"
          (Just [-41 :: Integer])
          (toCon (U.lookupSeqValue @'S (con [-41 :: Integer]) symbolic (con position)))
      assertEqual "symbolic nested blank replication prunes locally" (Just blank)
        (toCon (U.lookupSeqValue @'S (con blank) population index))
      assertEqual "nested blank point update prunes locally" (Just blank)
        (toCon (U.lookupSeqValue @'S (con blank)
          (U.updateSeq @'S target (con blank) population) index))
  , testCase "point replacement keeps current packed bits outside an edited field" $ do
      let original = con [0xa3 :: WordN 8] :: SymSeq (SymWordN 8)
          stale = U.lookupSeqValue @'S 0 original 0
          current = U.updateSeq @'S 0 0xb5 original
          currentWord = U.lookupSeqValue @'S 0 current 0
          replacement = (currentWord .&. 0xf0) .|. (stale .&. 0x0f)
          edited = U.updateSeq @'S 0 replacement current
      assertEqual "newer high nibble survives stale low-nibble selection"
        (Just (0xb3 :: WordN 8)) (toCon (U.lookupSeqValue @'S 0 edited 0))
      assertEqual "one packed cell, unchanged length" (Just 1 :: Maybe Integer)
        (toCon (U.lengthSeq @'S edited))
  , testCase "structural update laws preserve length and latest same-index writes" $ do
      let source = "lane.update.source" :: SymSeq SymInteger
          index = "lane.update.index" :: SymInteger
          first = "lane.update.first" :: SymInteger
          lastValue = "lane.update.last" :: SymInteger
          updated = U.updateSeq @'S index first source
      assertEqual "negative update is structurally unchanged" (underlyingTerm source)
        (underlyingTerm (U.updateSeq @'S (-1) first source))
      assertEqual "update of empty source stays empty" (Just [] :: Maybe [Integer])
        (toCon (U.updateSeq @'S index first U.nilSeq))
      assertEqual "symbolic update preserves exact source length"
        (AsKey (U.lengthSeq @'S source)) (AsKey (U.lengthSeq @'S updated))
      assertEqual "latest same-index write subsumes its predecessor"
        (underlyingTerm (U.updateSeq @'S index lastValue source))
        (underlyingTerm (U.updateSeq @'S index lastValue updated))
      let condition = "lane.update.choice" :: SymBool
          chosen = mrgIte condition (U.updateSeq @'S 0 21 (con [1 :: Integer]))
            (U.updateSeq @'S 0 37 (con [2 :: Integer]))
      assertValid "lookup through complete branch choice keeps its guard"
        (U.lookupSeqValue @'S (-1) chosen 0 .== mrgIte condition (21 :: SymInteger) 37)
  , testCase "merged lane extents stay visible before resizing and point updates" $ do
      let condition = "lane.extent.choice" :: SymBool
          equalExtent = mrgIte condition (con [1, 2 :: Integer])
            (con [3, 4 :: Integer]) :: SymSeq SymInteger
          differentExtents = mrgIte condition (con [False])
            (con [False, False]) :: SymSeq SymBool
          expectedLength = mrgIte condition (1 :: SymInteger) 2
          updated = U.updateSeq @'S ("lane.extent.index" :: SymInteger)
            (con False) differentExtents
      assertEqual "equal branch lengths are literally known" (Just 2 :: Maybe Integer)
        (toCon (U.lengthSeq @'S equalExtent))
      assertEqual "aligned resize does not reconstruct merged lanes" (underlyingTerm equalExtent)
        (underlyingTerm (U.resizeSeq @'S 7 2 equalExtent))
      assertEqual "different branch extents retain the exact choice"
        (AsKey expectedLength) (AsKey (U.lengthSeq @'S differentExtents))
      assertEqual "point update preserves the chosen extent"
        (AsKey expectedLength) (AsKey (U.lengthSeq @'S updated))
      assertEqual "merged vacant cells and their OOB fallback prune after a write"
        (Just False) (toCon (U.lookupSeqValue @'S (con False) updated
          ("lane.extent.read" :: SymInteger)) :: Maybe Bool)
  , testCase "large blank replication and one point update remain compact terms" $ do
      let count = 1000000 :: SymInteger
          population = U.resizeSeq @'S (7 :: SymInteger) count U.nilSeq
          updated = U.updateSeq @'S ("lane.large.index" :: SymInteger)
            ("lane.large.value" :: SymInteger) population
      assertBool "replication expanded a million host cells"
        (termSize (underlyingTerm population) <= 5)
      assertBool "single point edit expanded its population"
        (termSize (underlyingTerm updated) <= 8)
      assertEqual "large logical extent is exact" (Just 1000000 :: Maybe Integer)
        (toCon (U.lengthSeq @'S updated))
      assertEqual "far read of replicated blank remains literal" (Just 7 :: Maybe Integer)
        (toCon (U.lookupSeqValue @'S 7 population 999999))
  , testCase "resize/update survive serialization, symbol extraction and substitution" $ do
      let seed = "lane.terms.seed" :: SymInteger
          count = "lane.terms.count" :: SymInteger
          source = "lane.terms.source" :: SymSeq SymInteger
          index = "lane.terms.index" :: SymInteger
          replacement = "lane.terms.replacement" :: SymInteger
          resized = U.resizeSeq @'S seed count source
          updated = U.updateSeq @'S index replacement resized
          decoded = Binary.decode (Binary.encode updated) :: SymSeq SymInteger
          substitute :: SymSeq SymInteger -> SymSeq SymInteger
          substitute = substSym ("lane.terms.source" :: TypedConstantSymbol [Integer])
              (con [1, 2 :: Integer])
            . substSym ("lane.terms.seed" :: TypedConstantSymbol Integer) (7 :: SymInteger)
            . substSym ("lane.terms.count" :: TypedConstantSymbol Integer) (4 :: SymInteger)
            . substSym ("lane.terms.index" :: TypedConstantSymbol Integer) (2 :: SymInteger)
            . substSym ("lane.terms.replacement" :: TypedConstantSymbol Integer) (99 :: SymInteger)
      assertEqual "resize binary round-trip" (underlyingTerm resized)
        (underlyingTerm (Binary.decode (Binary.encode resized) :: SymSeq SymInteger))
      assertEqual "both node tags and children round-trip"
        (underlyingTerm updated) (underlyingTerm decoded)
      assertEqual "every primitive child contributes its symbols"
        (extractSym (seed, count, source, index, replacement)) (extractSym updated)
      assertEqual "repeated construction is interned" (underlyingTerm updated)
        (underlyingTerm (resizeAndUpdate @'S seed count source index replacement))
      checkIntegerCells "substituted native operations" [1, 2, 99, 7] (substitute decoded)
  , testCase "general functions and cross-thread reconstruction retain both operations" $ do
      let source = "lane.transfer.source" :: SymSeq SymInteger
          count = "lane.transfer.count" :: SymInteger
          index = "lane.transfer.index" :: SymInteger
          expression = resizeAndUpdate @'S 7 count source index 99
          function :: SymSeq SymInteger -~> SymSeq SymInteger
          function = con $ ("lane.function.source" :: TypedConstantSymbol [Integer])
            --> resizeAndUpdate @'S 7 4
              ("lane.function.source" :: SymSeq SymInteger) 2 99
      checkIntegerCells "general-function substitution" [1, 2, 99, 7]
        (function # (con [1, 2 :: Integer]))
      box <- newEmptyMVar
      _ <- forkIO $ do
        term <- evaluate $ force $ underlyingTerm $
          resizeAndUpdate @'S (7 :: SymInteger)
            ("lane.transfer.count" :: SymInteger)
            ("lane.transfer.source" :: SymSeq SymInteger)
            ("lane.transfer.index" :: SymInteger) 99
        putMVar box term
      rebuilt <- takeMVar box >>= toCurThread
      assertEqual "cross-thread identity and child traversal" (underlyingTerm expression)
        rebuilt
  , testCase "opaque symbolic whole lanes lower and decode all total cases" $
      within "whole scalar lane lowering" $ do
        let trials = zipWith pinnedLane [0 ..] laneFixtures
            inputs = conjunction [domain | (domain, _, _, _, _) <- trials]
            facts = conjunction [valid | (_, valid, _, _, _) <- trials]
        solve z3 (inputs .&& facts) >>= \case
          Left failure -> assertFailure $ "expected real-Z3 SAT: " ++ show failure
          Right model -> forM_ trials $ \(_, _, output, expression, expected) -> do
            assertEqual "whole output decodes to explicit fixture" (Just expected)
              (toCon (evalSym False model output))
            checkIntegerCells "evaluated operation children" expected
              (evalSym False model expression)
        expectUnsat (inputs .&& symNot facts)
  , testCase "opaque nested default lanes lower without flattening their values" $
      within "nested scalar lane lowering" $ do
        let source = "lane.nested.lowering.source" :: SymSeq (SymSeq SymInteger)
            count = "lane.nested.lowering.count" :: SymInteger
            index = "lane.nested.lowering.index" :: SymInteger
            output = "lane.nested.lowering.output" :: SymSeq (SymSeq SymInteger)
            expression = resizeAndUpdate @'S (con [7, 8 :: Integer]) count
              source index (con [9, 10 :: Integer])
            inputs = (source .== con [[1], [2, 3 :: Integer]])
              .&& (count .== 4) .&& (index .== 2) .&& (output .== expression)
            expected = [[1], [2, 3], [9, 10], [7, 8 :: Integer]]
            facts = output .== con expected
        solve z3 (inputs .&& facts) >>= \case
          Left failure -> assertFailure $ "expected nested real-Z3 SAT: " ++ show failure
          Right model -> do
            assertEqual "nested whole output model" (Just expected)
              (toCon (evalSym False model output))
            forM_ (zip [0 ..] expected) $ \(position, value) ->
              assertEqual "evaluated nested operation children" (Just value)
                (toCon (U.lookupSeqValue @'S (con [-41 :: Integer])
                  (evalSym False model expression) (con position)))
        expectUnsat (inputs .&& symNot facts)
  ]

literalLookupRange :: Integer -> SymInteger -> SymBool
literalLookupRange count index = (0 .<= index) .&& (index .< con count)

-- The Boolean oracle is built from the flags themselves, never by decoding bits.
-- Both branches below each outer choice remain nontrivial ITEs in the bit input.
booleanBitFixture :: SymBool -> (SymBool, SymIntN 1, SymWordN 1)
booleanBitFixture firstFlag =
  let outer = "lane.bit.fixture.outer" :: SymBool
      left = "lane.bit.fixture.left" :: SymBool
      right = "lane.bit.fixture.right" :: SymBool
      secondFlag = "lane.bit.fixture.second" :: SymBool
      thirdFlag = "lane.bit.fixture.third" :: SymBool
      fourthFlag = "lane.bit.fixture.fourth" :: SymBool
      choose :: SimpleMergeable value => (value, value, value, value) -> value
      choose (first, second, third, fourth) =
        mrgIte outer (mrgIte left first second) (mrgIte right third fourth)
      flags = (firstFlag, secondFlag, thirdFlag, fourthFlag)
      encode :: (Num value, SimpleMergeable value) => SymBool -> value
      encode flag = mrgIte flag 1 0
      signedFlags = (encode firstFlag, encode secondFlag, encode thirdFlag,
        encode fourthFlag) :: (SymIntN 1, SymIntN 1, SymIntN 1, SymIntN 1)
      unsignedFlags = (encode firstFlag, encode secondFlag, encode thirdFlag,
        encode fourthFlag) :: (SymWordN 1, SymWordN 1, SymWordN 1, SymWordN 1)
  in (choose flags, choose signedFlags, choose unsignedFlags)

checkIntegerCells :: String -> [Integer] -> SymSeq SymInteger -> Assertion
checkIntegerCells label expected actual = do
  assertEqual (label ++ ": literal length") (Just (toInteger (length expected)))
    (toCon (U.lengthSeq @'S actual) :: Maybe Integer)
  forM_ (zip [0 ..] expected) $ \(index, value) ->
    assertEqual (label ++ ": cell " ++ show index) (Just value)
      (toCon (U.lookupSeqValue @'S (-41) actual (con index)) :: Maybe Integer)
  forM_ [-1, toInteger (length expected), toInteger (length expected) + 3] $ \index ->
    assertEqual (label ++ ": absent " ++ show index) (Just (-41))
      (toCon (U.lookupSeqValue @'S (-41) actual (con index)) :: Maybe Integer)

pinnedLane
  :: Int -> LaneFixture
  -> (SymBool, SymBool, SymSeq SymInteger, SymSeq SymInteger, [Integer])
pinnedLane ordinal fixture =
  let source = isym "lane.lowering.source" ordinal :: SymSeq SymInteger
      count = isym "lane.lowering.count" ordinal :: SymInteger
      seed = isym "lane.lowering.seed" ordinal :: SymInteger
      index = isym "lane.lowering.index" ordinal :: SymInteger
      value = isym "lane.lowering.value" ordinal :: SymInteger
      resized = isym "lane.lowering.resized" ordinal :: SymSeq SymInteger
      updated = isym "lane.lowering.updated" ordinal :: SymSeq SymInteger
      inputs = (source .== con (fixtureSource fixture))
        .&& (count .== con (fixtureCount fixture))
        .&& (seed .== con (fixtureSeed fixture))
        .&& (index .== con (fixtureIndex fixture))
        .&& (value .== con (fixtureReplacement fixture))
        .&& (resized .== U.resizeSeq @'S seed count source)
        .&& (updated .== U.updateSeq @'S index value resized)
      facts = (resized .== con (fixtureResized fixture))
        .&& (updated .== con (fixtureUpdated fixture))
  in (inputs, facts, updated, resizeAndUpdate @'S seed count source index value,
      fixtureUpdated fixture)

conjunction :: [SymBool] -> SymBool
conjunction = foldr (.&&) (con True)

within :: String -> IO value -> IO value
within label action = timeout 10000000 action >>= \case
  Nothing -> fail (label ++ " did not finish within 10 seconds")
  Just value -> pure value

expectUnsat :: SymBool -> Assertion
expectUnsat formula = solve z3 formula >>= \case
  Left Unsat -> pure ()
  Left failure -> assertFailure $ "expected real-Z3 UNSAT: " ++ show failure
  Right _ -> assertFailure "pinned inputs admitted an incorrect whole lane"

assertValid :: String -> SymBool -> Assertion
assertValid label proposition = within label $ solve z3 (symNot proposition) >>= \case
  Left Unsat -> pure ()
  Left failure -> assertFailure $ label ++ ": expected real-Z3 UNSAT: " ++ show failure
  Right _ -> assertFailure $ label ++ ": admitted an incorrect value"
