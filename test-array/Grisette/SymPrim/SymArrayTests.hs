{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

-- |
-- Soundness gate for Grisette's symbolic theory-of-arrays support.
--
-- The suite is organised in layers, from cheap/concrete to solver-backed:
--
--   1. Concrete model laws ('Array', QuickCheck) — pure, fast sanity.
--   2. Direct SBV backend probes ('Data.SBV') — isolate whether the solver
--      layer itself provides extensional array equality, independent of
--      Grisette's term layer.
--   3. Solver-backed axioms over 'SymArray' — the real semantics we rely on.
--   4. Soundness regressions — concrete arrays that are structurally different
--      but semantically equal (the non-canonical 'Eq' hazard) must NOT be
--      reported unequal.
--   5. Model decode round-trip — extracting concrete values from a model.
--
-- Any failure here is a potential soundness bug, because p4check relies on
-- @regA .== regB@ deciding semantic (extensional) register-state equality.
module Grisette.SymPrim.SymArrayTests (symArrayTests) where

import qualified Data.HashMap.Strict as HM
import Data.Hashable (hash)
import qualified Data.SBV as SBV
import Data.Word (Word8)
import GHC.Generics (Generic)
import GHC.Stack (HasCallStack)
import Generics.Deriving (Default (Default))
import Grisette
  ( EvalSym (evalSym),
    AllSyms (allSyms),
    ExtractSym (extractSym),
    ITEOp (symIte),
    LogicalOp (symImplies, symNot, (.&&)),
    Mergeable,
    Solvable (con),
    SubstSym (substSym),
    SymBool,
    SymEq ((./=), (.==)),
    SymInteger,
    SymWordN,
    ToCon (toCon),
    ToSym (toSym),
    TypedConstantSymbol,
    WordN,
    isEmptySet,
    solve,
  )
import Grisette.Internal.Backend.Solving (z3)
import Grisette.Internal.Core.Data.Class.Solver (SolvingFailure (Unsat))
import Grisette.Internal.SymPrim.Array (Array (Array))
import qualified Grisette.Internal.SymPrim.Array as Arr
-- Exercise the public re-exports: the type from the umbrella module and the
-- operations from the dedicated public module (imported qualified).
import Grisette.SymPrim (SymArray)
import qualified Grisette.SymPrim.SymArray as A
-- The unified array layer, exercised through the public umbrella. Imported
-- qualified so the unified '.==' / 'GetBool' do not clash with the base ones.
import Grisette.Unified (EvalModeTag (C, S))
import qualified Grisette.Unified as U
import Test.Framework (Test, testGroup)
import Test.Framework.Providers.HUnit (testCase)
import Test.Framework.Providers.QuickCheck2 (testProperty)
import Test.HUnit (Assertion, assertBool, assertEqual, assertFailure)
import Test.QuickCheck
  ( Gen,
    arbitrary,
    choose,
    forAll,
    vectorOf,
    (===),
    (==>),
  )

-- ---------------------------------------------------------------------------
-- Solver assertion helpers
-- ---------------------------------------------------------------------------

-- | The negation of the property is unsatisfiable, i.e. the property holds for
-- all models (it is VALID).
checkValid :: (HasCallStack) => SymBool -> Assertion
checkValid phi = do
  r <- solve z3 (symNot phi)
  case r of
    Left Unsat -> return ()
    Left e -> assertFailure $ "expected VALID, but solver failed: " ++ show e
    Right _ -> assertFailure "expected VALID, but found a counterexample"

-- | The property is satisfiable (there exists a model).
checkSat :: (HasCallStack) => SymBool -> Assertion
checkSat phi = do
  r <- solve z3 phi
  case r of
    Right _ -> return ()
    Left Unsat -> assertFailure "expected SAT, but UNSAT"
    Left e -> assertFailure $ "expected SAT, but solver failed: " ++ show e

-- | The property is unsatisfiable (a contradiction).
checkUnsat :: (HasCallStack) => SymBool -> Assertion
checkUnsat phi = do
  r <- solve z3 phi
  case r of
    Left Unsat -> return ()
    Left e -> assertFailure $ "expected UNSAT, but solver failed: " ++ show e
    Right _ -> assertFailure "expected UNSAT, but found a model"

-- ---------------------------------------------------------------------------
-- 1. Concrete model laws (pure, QuickCheck)
-- ---------------------------------------------------------------------------

genArray :: Gen (Array Int Int)
genArray = do
  root <- choose (0, 3)
  n <- choose (0, 6)
  kvs <- vectorOf n ((,) <$> choose (0, 5) <*> choose (0, 3))
  pure (Array (HM.fromList kvs) root)

concreteLaws :: Test
concreteLaws =
  testGroup
    "concrete model laws (Array, pure)"
    [ testProperty "select (store a k v) k == v" $
        forAll genArray $ \arr ->
          forAll arbitrary $ \(k, v) ->
            Arr.select (Arr.store arr (k :: Int) (v :: Int)) k === v,
      testProperty "k /= j ==> select (store a k v) j == select a j" $
        forAll genArray $ \arr ->
          forAll arbitrary $ \(k, j, v) ->
            (k :: Int) /= j
              ==> Arr.select (Arr.store arr k (v :: Int)) j === Arr.select arr j,
      testProperty "select (const c) k == c" $
        forAll arbitrary $ \(c, k) ->
          Arr.select (Arr.const (c :: Int) :: Array Int Int) (k :: Int) === c,
      testProperty "store (store a k u) k v == store a k v (last write wins)" $
        forAll genArray $ \arr ->
          forAll arbitrary $ \(k, u, v) ->
            Arr.select (Arr.store (Arr.store arr (k :: Int) (u :: Int)) k (v :: Int)) k
              === Arr.select (Arr.store arr k v) k
    ]

-- Build a canonical array via the smart constructors (store over const), so
-- the canonical invariant holds. Default is 0; values are drawn from a range
-- that includes the default (so some overrides get dropped) over keys [0..8].
genCanon :: Gen (Array Int Int)
genCanon = do
  n <- choose (0, 6)
  kvs <- vectorOf n ((,) <$> choose (0, 8) <*> choose (0, 3))
  pure (foldl (\a (k, v) -> Arr.store a k v) (Arr.const 0) kvs)

-- | Concrete-mode ('C carrier) equality. After canonicalize-on-construction,
-- the derived structural '==' on 'Array' is extensional for arrays that share a
-- default. These are the regressions for the non-canonical 'Eq' hazard that
-- unified 'C-mode register equality would otherwise hit.
concreteCanonicalEq :: Test
concreteCanonicalEq =
  testGroup
    "concrete canonical equality (Array, 'C-mode carrier)"
    [ testCase "storing the default value is a structural no-op" $
        assertEqual
          "store (const 0) 5 0 == const 0"
          (Arr.const 0 :: Array Int Int)
          (Arr.store (Arr.const 0) 5 0),
      testCase "overwriting back to the default cancels an override" $
        assertEqual
          "store (store (const 0) 3 7) 3 0 == const 0"
          (Arr.const 0 :: Array Int Int)
          (Arr.store (Arr.store (Arr.const 0) 3 7) 3 0),
      testCase "an override equal to the default does not distinguish arrays" $
        assertEqual
          "{3->7,5->0}/0 == {3->7}/0"
          (Arr.store (Arr.const 0) 3 7 :: Array Int Int)
          (Arr.store (Arr.store (Arr.const 0) 3 7) 5 0),
      testCase "genuinely different concrete arrays remain unequal" $
        assertBool
          "{3->7}/0 /= {}/0"
          (Arr.store (Arr.const 0) 3 7 /= (Arr.const 0 :: Array Int Int)),
      testCase "Hashable stays consistent with the canonical Eq" $
        assertEqual
          "equal arrays hash equally"
          (hash (Arr.store (Arr.const 0) 5 0 :: Array Int Int))
          (hash (Arr.const 0 :: Array Int Int)),
      testProperty "structural == agrees with pointwise equality (shared default)" $
        forAll genCanon $ \a ->
          forAll genCanon $ \b ->
            (a == b) === all (\k -> Arr.select a k == Arr.select b k) [0 .. 8]
    ]

-- ---------------------------------------------------------------------------
-- 2. Direct SBV backend probes (isolate the solver layer)
-- ---------------------------------------------------------------------------

sbvProbes :: Test
sbvProbes =
  testGroup
    "SBV backend probes (Data.SBV, isolate solver extensionality)"
    [ testCase "writeArray (constArray d) k d == constArray d  is a theorem" $ do
        ok <-
          SBV.isTheorem $
            let a0 = SBV.constArray (SBV.literal (0 :: Word8)) :: SBV.SArray Word8 Word8
                a1 = SBV.writeArray a0 (SBV.literal (5 :: Word8)) (SBV.literal (0 :: Word8))
             in a1 SBV..== a0
        assertBool
          "storing the default value must be extensionally a no-op"
          ok,
      testCase "writeArray a i (readArray a i) == a  is a theorem (extensionality)" $ do
        ok <- SBV.isTheorem $ do
          a <- SBV.sArray "a" :: SBV.Symbolic (SBV.SArray Word8 Word8)
          i <- SBV.free "i" :: SBV.Symbolic (SBV.SBV Word8)
          return (SBV.writeArray a i (SBV.readArray a i) SBV..== a)
        assertBool
          "rewriting an index with its current value must be extensionally a no-op"
          ok,
      testCase "distinct constant arrays are NOT a theorem of equality" $ do
        ok <-
          SBV.isTheorem $
            let a0 = SBV.constArray (SBV.literal (0 :: Word8)) :: SBV.SArray Word8 Word8
                a1 = SBV.writeArray a0 (SBV.literal (1 :: Word8)) (SBV.literal (7 :: Word8))
             in a1 SBV..== a0
        assertBool
          "arrays that genuinely differ must not be provably equal"
          (not ok)
    ]

-- ---------------------------------------------------------------------------
-- 3. Solver-backed axioms over SymArray
-- ---------------------------------------------------------------------------

-- Fresh symbolic helpers, two element/key flavours: infinite (Integer) and
-- finite (WordN 8).
aI :: SymArray SymInteger SymInteger
aI = "a"

bI :: SymArray SymInteger SymInteger
bI = "b"

iI, jI, uI, wI :: SymInteger
iI = "i"
jI = "j"
uI = "u"
wI = "w"

aW :: SymArray (SymWordN 8) (SymWordN 8)
aW = "aw"

bW :: SymArray (SymWordN 8) (SymWordN 8)
bW = "bw"

iW, jW, uW, wW :: SymWordN 8
iW = "iw"
jW = "jw"
uW = "uw"
wW = "ww"

axioms :: Test
axioms =
  testGroup
    "solver-backed axioms (SymArray)"
    [ testGroup
        "Integer keys/values (infinite domain)"
        [ testCase "select (store a i v) i == v" $
            checkValid (A.select (A.store aI iI uI) iI .== uI),
          testCase "i /= j ==> select (store a i v) j == select a j" $
            checkValid
              (symImplies (iI ./= jI) (A.select (A.store aI iI uI) jI .== A.select aI jI)),
          testCase "select (const c) i == c" $
            checkValid (A.select (A.const uI :: SymArray SymInteger SymInteger) iI .== uI),
          testCase "store overwrite: store (store a i u) i w == store a i w" $
            checkValid (A.store (A.store aI iI uI) iI wI .== A.store aI iI wI),
          testCase "store commute: i/=j ==> stores at i,j commute" $
            checkValid
              ( symImplies
                  (iI ./= jI)
                  ( A.store (A.store aI iI uI) jI wI
                      .== A.store (A.store aI jI wI) iI uI
                  )
              ),
          testCase "extensionality: store a i (select a i) == a" $
            checkValid (A.store aI iI (A.select aI iI) .== aI),
          testCase "reflexivity: a == a" $
            checkValid (aI .== aI),
          testCase "two fresh arrays may be equal (SAT)" $
            checkSat (aI .== bI),
          testCase "two fresh arrays may differ (SAT)" $
            checkSat (aI ./= bI),
          testCase "a == b && a /= b is UNSAT" $
            checkUnsat (aI .== bI .&& aI ./= bI)
        ],
      testGroup
        "WordN 8 keys/values (finite domain)"
        [ testCase "select (store a i v) i == v" $
            checkValid (A.select (A.store aW iW uW) iW .== uW),
          testCase "i /= j ==> select (store a i v) j == select a j" $
            checkValid
              (symImplies (iW ./= jW) (A.select (A.store aW iW uW) jW .== A.select aW jW)),
          testCase "select (const c) i == c" $
            checkValid (A.select (A.const uW :: SymArray (SymWordN 8) (SymWordN 8)) iW .== uW),
          testCase "store overwrite" $
            checkValid (A.store (A.store aW iW uW) iW wW .== A.store aW iW wW),
          testCase "extensionality: store a i (select a i) == a" $
            checkValid (A.store aW iW (A.select aW iW) .== aW)
        ],
      testGroup
        "ITE over arrays"
        [ testCase "symIte True a b == a" $
            checkValid (symIte (con True) aI bI .== aI),
          testCase "symIte c a a == a" $
            checkValid (symIte ("c" :: SymBool) aI aI .== aI),
          testCase "select distributes over ite" $
            checkValid
              ( A.select (symIte ("c" :: SymBool) aI bI) iI
                  .== symIte ("c" :: SymBool) (A.select aI iI) (A.select bI iI)
              )
        ]
    ]

-- ---------------------------------------------------------------------------
-- 4. Soundness regressions: non-canonical concrete arrays
-- ---------------------------------------------------------------------------

-- helper: build a concrete WordN8->WordN8 array literal
conW8 :: HM.HashMap (WordN 8) (WordN 8) -> WordN 8 -> SymArray (SymWordN 8) (SymWordN 8)
conW8 m d = con (Array m d)

soundnessRegressions :: Test
soundnessRegressions =
  testGroup
    "soundness regressions (non-canonical concrete arrays)"
    [ testCase "store-of-default override equals bare default array" $
        -- Array {5 -> 0} default 0  ==  Array {} default 0  (semantically equal)
        checkValid (conW8 (HM.fromList [(5, 0)]) 0 .== conW8 HM.empty 0),
      testCase "store-of-default override equals const default" $
        checkValid
          ( conW8 (HM.fromList [(5, 0)]) 0
              .== (A.const (con 0) :: SymArray (SymWordN 8) (SymWordN 8))
          ),
      testCase "genuinely different concrete arrays are provably unequal" $
        checkValid (conW8 (HM.fromList [(1, 5)]) 0 ./= conW8 (HM.fromList [(1, 6)]) 0),
      testCase "different concrete defaults are provably unequal (infinite key domain)" $
        -- WordN 8 has 256 keys; two single-entry overrides over different
        -- defaults differ at any uncovered key.
        checkValid (conW8 (HM.fromList [(1, 5)]) 0 ./= conW8 (HM.fromList [(1, 5)]) 9),
      testCase "finite full-cover, differing defaults masked: equal (WordN 1)" $
        -- Domain of WordN 1 is {0,1}; both keys overridden identically, so the
        -- default is irrelevant and the two arrays are extensionally equal.
        checkValid
          ( (con (Array (HM.fromList [(0, 5), (1, 7)]) 0) :: SymArray (SymWordN 1) (SymWordN 8))
              .== con (Array (HM.fromList [(0, 5), (1, 7)]) 9)
          )
    ]

-- ---------------------------------------------------------------------------
-- 5. Model decode round-trip (sbvToCon)
-- ---------------------------------------------------------------------------

modelRoundTrip :: Test
modelRoundTrip =
  testGroup
    "model decode round-trip (sbvToCon)"
    [ testCase "extract select values from a satisfying model" $ do
        let a = "a" :: SymArray (SymWordN 8) (SymWordN 8)
        r <-
          solve
            z3
            (A.select a (con 3) .== con 7 .&& A.select a (con 4) .== con 9)
        case r of
          Left e -> assertFailure $ "expected SAT: " ++ show e
          Right m -> do
            let v3 = evalSym False m (A.select a (con 3)) :: SymWordN 8
                v4 = evalSym False m (A.select a (con 4)) :: SymWordN 8
            assertEqual "select a 3" (Just 7) (toCon v3 :: Maybe (WordN 8))
            assertEqual "select a 4" (Just 9) (toCon v4 :: Maybe (WordN 8))
    ]

-- ---------------------------------------------------------------------------

-- ---------------------------------------------------------------------------
-- 6. Register-model machinery: ExtractSym / SubstSym + public re-export path
-- ---------------------------------------------------------------------------

-- | A Generic record embedding a 'SymArray', exactly as the p4 register model
-- embeds a lane. This declaration only compiles if 'SymArray' has 'Mergeable',
-- 'EvalSym', 'ExtractSym', and 'SubstSym' and they compose through 'Generic'
-- (the machinery the register state needs to flow through @mrgIf@, be solved
-- for, and be read back from a model).
newtype RegBox = RegBox (SymArray (SymWordN 8) (SymWordN 8))
  deriving stock (Generic)
  deriving (Mergeable, EvalSym, ExtractSym, SubstSym, AllSyms) via (Default RegBox)

machineryTests :: Test
machineryTests =
  testGroup
    "register-model machinery (ExtractSym / SubstSym / public re-exports)"
    [ testCase "ExtractSym: fresh array exposes its variable, concrete exposes none" $ do
        assertBool
          "fresh symbolic array must expose its variable"
          (not (isEmptySet (extractSym aW)))
        assertBool
          "concrete array must expose no variables"
          ( isEmptySet
              (extractSym (con (Array HM.empty 0) :: SymArray (SymWordN 8) (SymWordN 8)))
          ),
      testCase "SubstSym: substituting the array symbol rewrites the array" $ do
        -- aW is the symbol "aw"; replacing it with bW turns aW into bW, both
        -- directly and underneath a select.
        let aSym = "aw" :: TypedConstantSymbol (Array (WordN 8) (WordN 8))
        checkValid (substSym aSym bW aW .== bW)
        checkValid (A.select (substSym aSym bW aW) iW .== A.select bW iW),
      testCase "Generic container (RegBox) round-trips extractSym + evalSym" $ do
        assertBool
          "RegBox must expose the wrapped array's symbol"
          (not (isEmptySet (extractSym (RegBox aW))))
        r <- solve z3 (A.select aW (con 3) .== con 7)
        case r of
          Left e -> assertFailure $ "expected SAT: " ++ show e
          Right m -> do
            let RegBox a' = evalSym False m (RegBox aW)
                v = A.select a' (con 3) :: SymWordN 8
            assertEqual "evalSym through RegBox then select 3" (Just 7) (toCon v :: Maybe (WordN 8)),
      testCase "AllSyms: symbolic array is one primitive, concrete array is none" $ do
        assertEqual
          "a symbolic array contributes exactly one symbolic primitive"
          1
          (length (allSyms aW))
        assertEqual
          "a concrete array contributes no symbolic primitives"
          0
          (length (allSyms (Arr.const 0 :: Array (WordN 8) (WordN 8))))
        assertEqual
          "a Default-derived container surfaces the wrapped array's primitive"
          1
          (length (allSyms (RegBox aW))),
      testCase "public Grisette.SymPrim.SymArray select/store/const round-trip" $
        -- select/store/const here resolve through the public re-export module 'A'.
        checkValid
          ( A.select (A.store (A.const (con 0)) iW (con 5)) iW
              .== (con 5 :: SymWordN 8)
          ),
      testCase "ToSym then ToCon round-trips a concrete array" $ do
        let ca = Arr.store (Arr.store (Arr.const 0) 3 7) 4 9 :: Array (WordN 8) (WordN 8)
            sa = toSym ca :: SymArray (SymWordN 8) (SymWordN 8)
        assertEqual "toCon (toSym a) == Just a" (Just ca) (toCon sa),
      testCase "ToCon of a non-concrete symbolic array is Nothing" $
        assertEqual
          "toCon \"a\" == Nothing"
          (Nothing :: Maybe (Array (WordN 8) (WordN 8)))
          (toCon (aW :: SymArray (SymWordN 8) (SymWordN 8)))
    ]

-- ---------------------------------------------------------------------------
-- 7. Unified array layer (GetArray) — the mode-polymorphic interface that lets
--    p4check drop its lane type-family split. Imported only through the public
--    "Grisette.Unified": the abstract type 'U.GetArray' and the canonicalizing
--    smart constructors 'U.constArray'/'U.storeArray'/'U.selectArray' (the raw
--    'Array'/'SymArray' constructors are NOT exported there).
-- ---------------------------------------------------------------------------

-- | A single mode-polymorphic computation. It type-checks only if the entire
-- 'U.UnifiedArrayConstraint' bundle (the ops plus unified equality, ite, and
-- mergeability) resolves for @mode@. It is instantiated at both 'C and 'S
-- below, which is exactly the mode-generic register code p4check wants to write
-- once. By last-write-wins, @a@ and @b@ denote the same array, so the returned
-- unified equality is true ('C) / valid ('S).
unifiedRoundTrip ::
  forall mode k v.
  (U.DecideEvalMode mode, U.UnifiedArrayConstraint mode k v) =>
  v -> k -> v -> v -> (v, U.GetBool mode)
unifiedRoundTrip d key val val2 =
  let a = U.storeArray (U.storeArray (U.constArray d) key val) key val2 :: U.GetArray mode k v
      b = U.storeArray (U.constArray d) key val2 :: U.GetArray mode k v
   in (U.selectArray a key, (U..==) @mode a b)

unifiedLayer :: Test
unifiedLayer =
  testGroup
    "unified array layer (GetArray, abstract smart constructors)"
    [ testCase "'C: select after store reads the stored value" $
        assertEqual
          "select (store (const 0) 3 7) 3 == 7"
          (7 :: WordN 8)
          ( U.selectArray
              (U.storeArray (U.constArray 0 :: U.GetArray 'C (WordN 8) (WordN 8)) 3 7)
              3
          ),
      testCase "'C: store-of-default canonicalizes; unified == is a concrete Bool" $
        let z = U.constArray 0 :: U.GetArray 'C (WordN 8) (WordN 8)
            s = U.storeArray z 5 0
         in assertBool "store (const 0) 5 0 .== const 0" ((U..==) @'C s z),
      testCase "'C: mode-polymorphic round trip (last write wins, eq is True)" $
        let (v, eq) = unifiedRoundTrip @'C @(WordN 8) @(WordN 8) 0 3 7 9
         in do
              assertEqual "select after the two stores" (9 :: WordN 8) v
              assertBool "the two arrays are concretely equal" eq,
      testCase "'S: select after store is provable through unified ops" $
        checkValid
          ( (U..==) @'S
              ( U.selectArray
                  ( U.storeArray
                      (U.constArray (con 0) :: U.GetArray 'S (SymWordN 8) (SymWordN 8))
                      iW
                      (con 5)
                  )
                  iW
              )
              (con 5 :: SymWordN 8)
          ),
      testCase "'S: array-level unified equality is a solvable SymBool" $
        let a = U.storeArray (U.constArray (con 0)) iW (con 5) :: U.GetArray 'S (SymWordN 8) (SymWordN 8)
         in checkValid ((U..==) @'S a a),
      testCase "'S: mode-polymorphic round trip equality is valid" $
        let (_, eq) = unifiedRoundTrip @'S @(SymWordN 8) @(SymWordN 8) (con 0) iW (con 5) (con 9)
         in checkValid eq
    ]

-- ---------------------------------------------------------------------------

symArrayTests :: Test
symArrayTests =
  testGroup
    "SymArray"
    [ concreteLaws,
      concreteCanonicalEq,
      sbvProbes,
      axioms,
      soundnessRegressions,
      modelRoundTrip,
      machineryTests,
      unifiedLayer
    ]
