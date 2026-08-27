{-# LANGUAGE CPP #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

{-# HLINT ignore "Unused LANGUAGE pragma" #-}

-- {-# OPTIONS_GHC -ddump-simpl -dsuppress-module-prefixes -dsuppress-uniques #-}
-- {-# OPTIONS_GHC -ddump-timings #-}

module Grisette.Core.TH.DerivationTest (derivationTest) where

import Data.Bytes.Get (runGetS)
import Data.Bytes.Put (runPutS)
import Data.Bytes.Serial (Serial (deserialize, serialize))
import Data.Functor.Classes (showsPrec1, showsPrec2)
import Data.Proxy (Proxy (Proxy))
import qualified Data.Text as T
import GHC.TypeLits (KnownNat, type (<=))
import Grisette
  ( AsKey (AsKey),
    AsKey1 (AsKey1),
    FP32,
    ITEOp (symIte),
    Mergeable (rootStrategy),
    MergingStrategy,
    PPrint (pformat, pformatPrec),
    Solvable (con),
    SymBool,
    SymInteger,
    SymEq ((.==)),
    SymOrd (symCompare),
    ValidFP,
    WordN32,
    docToTextWithWidth,
    mrgSingle,
    pformatPrec1,
    pformatPrec2,
    symCompare1,
    symCompare2,
    symEq1,
    symEq2,
  )
import Grisette.Core.TH.DerivationData
  ( Extra (Extra),
    Ambiguous (Ambiguous),
    GGG (..),
    Serializable,
    gggToVVV,
    replaceVVVShown,
  )
import Grisette.Core.TH.PartialEvalMode (PartialEvalMode)
import Grisette.Internal.Core.Data.UnionBase
  ( UnionBase (UnionGroup, UnionIf, UnionSingle),
    ifWithStrategy,
  )
import Grisette.TestUtil.SymbolicAssertion ((.@?=))
import Grisette.Unified
  ( BaseMonad,
    EvalModeTag (C),
    GetBool,
    GetData,
    extractData,
  )
import qualified Grisette.Unified as GU
import Test.Framework (Test, testGroup)
import Test.Framework.Providers.HUnit (testCase)
import Test.Framework.Providers.QuickCheck2 (testProperty)
import Test.HUnit (assertFailure, (@?=))
import Test.QuickCheck.Property ((.&.), (===))

#if MIN_VERSION_base(4,16,0)
ftst ::
  forall mode n eb sb a.
  ( PartialEvalMode mode,
    KnownNat n,
    1 <= n,
    ValidFP eb sb,
    Mergeable a
  ) =>
  GetBool mode ->
  GetData mode (Extra mode n eb sb a) ->
  GetData mode (Extra mode n eb sb a) ->
  BaseMonad mode (Extra mode n eb sb a)
ftst c t f =
  GU.mrgIf @mode
    c
    (extractData t)
    (extractData f)

derivationExtraTest :: [Test]
derivationExtraTest =
  [ testCase "ftst" $ do
      let x = Extra True [1 :: WordN32] [] (0 :: FP32) 0 0 (0 :: Int)
      let y = Extra False [1 :: WordN32] [] (0 :: FP32) 0 0 (0 :: Int)
      let a = ftst @'C True (return x) (return y)
      a .@?= return x
  ]
#else
derivationExtraTest :: [Test]
derivationExtraTest = []
#endif

derivationTest :: Test
derivationTest =
  testGroup "Derivation" $
    [ testCase "derived Mergeable retains same-constructor payload groups" $ do
        let merged =
              ifWithStrategy
                (rootStrategy :: MergingStrategy (GGG (AsKey SymBool) Integer))
                "condition"
                (UnionSingle (GGG1 "left"))
                (UnionSingle (GGG1 "right"))
        case merged of
          UnionGroup {} -> pure ()
          _ -> assertFailure "Derived same-constructor merge flattened its typed group"
        AsKey merged
          @?= AsKey
            (UnionSingle (GGG1 (symIte "condition" "left" "right"))),
      testCase "derived Mergeable keeps different constructors distinct" $ do
        let merged =
              ifWithStrategy
                (rootStrategy :: MergingStrategy (GGG (AsKey SymBool) Integer))
                "condition"
                (UnionSingle GGG0)
                (UnionSingle (GGG1 "right"))
        case merged of
          UnionIf {} -> pure ()
          _ -> assertFailure "Derived different-constructor merge collapsed alternatives",
      testCase "derived GADT family groups an equal existential witness" $ do
        let merged =
              ifWithStrategy
                (rootStrategy :: MergingStrategy (Ambiguous Integer))
                "condition"
                (UnionSingle (Ambiguous (Proxy @SymBool)))
                (UnionSingle (Ambiguous (Proxy @SymBool)))
        case merged of
          UnionGroup {} -> pure ()
          _ -> assertFailure "Equal existential witnesses did not form a typed group",
      testCase "derived GADT family separates unequal existential witnesses" $ do
        let merged =
              ifWithStrategy
                (rootStrategy :: MergingStrategy (Ambiguous Integer))
                "condition"
                (UnionSingle (Ambiguous (Proxy @SymBool)))
                (UnionSingle (Ambiguous (Proxy @SymInteger)))
        case merged of
          UnionIf {} -> pure ()
          _ -> assertFailure "Unequal existential witnesses were collapsed",
      testProperty "GADT Show instance for regular types" $
        \(g :: GGG (GGG Int String) [Int]) ->
          let v = gggToVVV g
           in replaceVVVShown (T.pack (show g))
                === replaceVVVShown (T.pack (show v)),
      testProperty "GADT Show and Show1 are consistent" $
        \(g :: GGG (GGG Char String) [Int]) ->
          T.pack (show g)
            === T.pack (showsPrec1 0 g "")
            .&. T.pack (showsPrec 11 g "")
            === T.pack (showsPrec1 11 g ""),
      testProperty "GADT Show and Show2 are consistent" $
        \(g :: GGG (GGG Char String) [Int]) ->
          T.pack (show g)
            === T.pack (showsPrec2 0 g "")
            .&. T.pack (showsPrec 11 g "")
            === T.pack (showsPrec2 11 g ""),
      testProperty "GADT PPrint instance for regular types" $
        \(g :: GGG (GGG Int String) [Int]) ->
          let v = gggToVVV g
           in replaceVVVShown (docToTextWithWidth 1000 (pformat g))
                === replaceVVVShown (docToTextWithWidth 1000 (pformat v))
                .&. replaceVVVShown (docToTextWithWidth 0 (pformat g))
                === replaceVVVShown (docToTextWithWidth 0 (pformat v)),
      testProperty "GADT PPrint and PPrint1 are consistent" $
        \(g :: GGG (GGG Char String) [Int]) ->
          docToTextWithWidth 1000 (pformatPrec 0 g)
            === docToTextWithWidth 1000 (pformatPrec1 0 g)
            .&. docToTextWithWidth 1000 (pformatPrec 11 g)
            === docToTextWithWidth 1000 (pformatPrec1 11 g)
            .&. docToTextWithWidth 0 (pformatPrec 0 g)
            === docToTextWithWidth 0 (pformatPrec1 0 g)
            .&. docToTextWithWidth 0 (pformatPrec 11 g)
            === docToTextWithWidth 0 (pformatPrec1 11 g),
      testProperty "GADT PPrint and PPrint2 are consistent" $
        \(g :: GGG (GGG Char String) [Int]) ->
          docToTextWithWidth 1000 (pformatPrec 0 g)
            === docToTextWithWidth 1000 (pformatPrec2 0 g)
            .&. docToTextWithWidth 1000 (pformatPrec 11 g)
            === docToTextWithWidth 1000 (pformatPrec2 11 g)
            .&. docToTextWithWidth 0 (pformatPrec 0 g)
            === docToTextWithWidth 0 (pformatPrec2 0 g)
            .&. docToTextWithWidth 0 (pformatPrec 11 g)
            === docToTextWithWidth 0 (pformatPrec2 11 g),
      testProperty "GADT SymEq and Eq are consistent" $
        \(g1 :: GGG (GGG Int String) [Int]) g2 ->
          let v1 = gggToVVV g1
              v2 = gggToVVV g2
           in AsKey (con (g1 == g2)) === AsKey (v1 .== v2),
      testProperty "GADT SymEq1 and SymEq are consistent" $
        \(g1 :: GGG (GGG Int String) [Int]) g2 ->
          AsKey (symEq1 g1 g2) === AsKey (g1 .== g2),
      testProperty "GADT SymEq2 and SymEq are consistent" $
        \(g1 :: GGG (GGG Int String) [Int]) g2 ->
          AsKey (symEq2 g1 g2) === AsKey (g1 .== g2),
      testProperty "GADT SymOrd and Ord are consistent" $
        \(g1 :: GGG (GGG Int String) [Int]) g2 ->
          let v1 = gggToVVV g1
              v2 = gggToVVV g2
           in mrgSingle (g1 `compare` g2) === AsKey1 (v1 `symCompare` v2),
      testProperty "GADT SymOrd1 and SymOrd are consistent" $
        \(g1 :: GGG (GGG Int String) [Int]) g2 ->
          AsKey1 (symCompare1 g1 g2) === AsKey1 (g1 `symCompare` g2),
      testProperty "GADT SymOrd2 and SymOrd are consistent" $
        \(g1 :: GGG (GGG Int String) [Int]) g2 ->
          AsKey1 (symCompare2 g1 g2) === AsKey1 (g1 `symCompare` g2),
      testProperty "Serialize" $ do
        \(s :: Serializable Int) ->
          let bs = runPutS (serialize s)
              s' = runGetS deserialize bs
           in Right s === s'
    ]
      ++ derivationExtraTest
