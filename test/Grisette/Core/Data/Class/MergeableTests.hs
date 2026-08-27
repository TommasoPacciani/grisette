{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}

module Grisette.Core.Data.Class.MergeableTests (mergeableTests) where

import Control.Monad.Cont (ContT (ContT), runContT)
import Control.Monad.Except (ExceptT (ExceptT))
import Control.Monad.Identity
  ( Identity (Identity, runIdentity),
    IdentityT (IdentityT, runIdentityT),
  )
import Control.Monad.Reader (ReaderT (ReaderT, runReaderT))
import qualified Control.Monad.RWS.Lazy as RWSLazy
import qualified Control.Monad.RWS.Strict as RWSStrict
import qualified Control.Monad.State.Lazy as StateLazy
import qualified Control.Monad.State.Strict as StateStrict
import Control.Monad.Trans.Maybe (MaybeT (MaybeT))
import qualified Control.Monad.Writer.Lazy as WriterLazy
import qualified Control.Monad.Writer.Strict as WriterStrict
import qualified Data.ByteString.Char8 as C
import Data.Functor.Compose (Compose (Compose))
import Data.Functor.Sum (Sum (InL, InR))
import Data.Int (Int16, Int32, Int64, Int8)
import Data.Monoid (Endo (Endo, appEndo))
import Data.Proxy (Proxy (Proxy))
import Data.Word (Word16, Word32, Word64, Word8)
import Generics.Deriving (Default (Default), Default1 (Default1))
import GHC.Generics
  ( Generic,
    Generic1,
    K1 (K1),
    M1 (M1),
    Par1 (Par1),
    Rec1 (Rec1),
    (:.:) (Comp1),
    (:*:) ((:*:)),
    from,
    from1,
  )
import GHC.Stack (HasCallStack)
import Grisette
  ( AsKey (AsKey),
    AsKey1 (AsKey1),
    CBMCEither (CBMCEither),
    CBMCExceptT (CBMCExceptT),
    DynamicSortedIdx (DynamicStructuralIdx),
    FreshIndex (FreshIndex),
    FreshT (FreshT, runFreshTFromIndex),
    ITEOp (symIte),
    Mergeable (rootStrategy),
    MergingStrategy (NoStrategy, SimpleStrategy),
    ResolvedStrategy (ResolvedStrategy),
    Solvable (con, ssym),
    StructuralCase (StructuralCase),
    StructuralFamily (compareStructural, compareStructuralShape),
    StructuralOrdering (StructuralEQ, StructuralGT, StructuralLT),
    StructuralWrapper (unwrapValue, wrapValue),
    SymBool,
    Union,
    UnionView (singleView),
    mrgIf,
    mrgSingle,
    resolveStrategy,
    structuralStrategy,
    wrapStrategy,
  )
import Grisette.Internal.Core.Data.UnionBase
  ( UnionBase (UnionGroup, UnionIf, UnionSingle),
    eraseUnionGroups,
    fullReconstruct,
    ifWithStrategy,
  )
import Grisette.Internal.Core.Control.Monad.CBMCExcept
  ( CBMCEitherFamily (CBMCLeftFamily, CBMCRightFamily),
    CBMCExceptTWrapper (CBMCExceptTWrapper),
  )
import Grisette.Internal.Core.Data.Class.GenSym
  ( FreshTWrapper (FreshTWrapper),
  )
import Grisette.Internal.Core.Data.Class.Mergeable
  ( AsKey1Wrapper (AsKey1Wrapper),
    AsKeyWrapper (AsKeyWrapper),
    Comp1Wrapper (Comp1Wrapper),
    ComposeWrapper (ComposeWrapper),
    ContTWrapper (ContTWrapper),
    Default1Wrapper (Default1Wrapper),
    DefaultWrapper (DefaultWrapper),
    EitherFamily (LeftEitherFamily, RightEitherFamily),
    EndoWrapper (EndoWrapper),
    Generic1Wrapper (Generic1Wrapper),
    GenericProductWrapper (GenericProductWrapper),
    GenericWrapper (GenericWrapper),
    IdentityTWrapper (IdentityTWrapper),
    K1Wrapper (K1Wrapper),
    LazyRWSTWrapper (LazyRWSTWrapper),
    ListFamily (ConsListFamily, EmptyListFamily),
    M1Wrapper (M1Wrapper),
    MaybeFamily (JustMaybeFamily, NothingMaybeFamily),
    NominalWrapper (NominalWrapper),
    Par1Wrapper (Par1Wrapper),
    ReaderTWrapper (ReaderTWrapper),
    Rec1Wrapper (Rec1Wrapper),
    StrictRWSTWrapper (StrictRWSTWrapper),
  )
import Grisette.Internal.SymPrim.BV (WordN)
import Grisette.Internal.SymPrim.Nominal
  ( Nominal (Nominal),
    NominalDomain (Domain),
  )
import Grisette.Internal.SymPrim.SomeBV
  ( SomeBV (SomeBV),
    SomeBVFamily (LiteralSomeBVFamily, SizedSomeBVFamily),
  )
import Test.Framework (Test, testGroup)
import Test.Framework.Providers.HUnit (testCase)
import Test.Framework.Providers.QuickCheck2 (testProperty)
import Test.HUnit (Assertion, assertBool, assertFailure, (@?=))
import Test.QuickCheck (ioProperty)

newtype Box value = Box {unBox :: value}
  deriving (Eq, Show)

newtype GenericBox value = GenericBox value
  deriving (Eq, Show, Generic, Generic1)

data BoxWrapper target source where
  BoxWrapper :: BoxWrapper (Box value) value

instance StructuralFamily BoxWrapper where
  compareStructural BoxWrapper BoxWrapper = StructuralEQ
  compareStructuralShape BoxWrapper BoxWrapper = EQ

instance StructuralWrapper BoxWrapper where
  wrapValue BoxWrapper = Box
  unwrapValue BoxWrapper = unBox

instance (Mergeable value) => Mergeable (Box value) where
  rootStrategy = wrapStrategy BoxWrapper rootStrategy

data TestChoice left right
  = TestLeft left
  | TestRight right
  deriving (Eq, Show)

data TestChoiceFamily value payload where
  TestLeftFamily :: TestChoiceFamily (TestChoice left right) left
  TestRightFamily :: TestChoiceFamily (TestChoice left right) right

instance StructuralFamily TestChoiceFamily where
  compareStructural TestLeftFamily TestLeftFamily = StructuralEQ
  compareStructural TestLeftFamily TestRightFamily = StructuralLT
  compareStructural TestRightFamily TestLeftFamily = StructuralGT
  compareStructural TestRightFamily TestRightFamily = StructuralEQ

  compareStructuralShape TestLeftFamily TestLeftFamily = EQ
  compareStructuralShape TestLeftFamily TestRightFamily = LT
  compareStructuralShape TestRightFamily TestLeftFamily = GT
  compareStructuralShape TestRightFamily TestRightFamily = EQ

testChoiceSplit ::
  TestChoice left right ->
  StructuralCase TestChoiceFamily (TestChoice left right)
testChoiceSplit (TestLeft value) = StructuralCase TestLeftFamily value
testChoiceSplit (TestRight value) = StructuralCase TestRightFamily value

testChoicePayloadStrategy ::
  forall left right payload.
  (Mergeable left, Mergeable right) =>
  TestChoiceFamily (TestChoice left right) payload ->
  MergingStrategy payload
testChoicePayloadStrategy TestLeftFamily = rootStrategy
testChoicePayloadStrategy TestRightFamily = rootStrategy

testChoiceInject ::
  forall left right payload.
  TestChoiceFamily (TestChoice left right) payload ->
  payload ->
  TestChoice left right
testChoiceInject TestLeftFamily = TestLeft
testChoiceInject TestRightFamily = TestRight

instance (Mergeable left, Mergeable right) =>
    Mergeable (TestChoice left right) where
  rootStrategy =
    structuralStrategy
      testChoiceSplit
      testChoicePayloadStrategy
      testChoiceInject

data AlternateTestChoiceFamily value payload where
  AlternateTestLeftFamily ::
    AlternateTestChoiceFamily (TestChoice left right) left
  AlternateTestRightFamily ::
    AlternateTestChoiceFamily (TestChoice left right) right

instance StructuralFamily AlternateTestChoiceFamily where
  compareStructural AlternateTestLeftFamily AlternateTestLeftFamily = StructuralEQ
  compareStructural AlternateTestLeftFamily AlternateTestRightFamily = StructuralLT
  compareStructural AlternateTestRightFamily AlternateTestLeftFamily = StructuralGT
  compareStructural AlternateTestRightFamily AlternateTestRightFamily = StructuralEQ

  compareStructuralShape AlternateTestLeftFamily AlternateTestLeftFamily = EQ
  compareStructuralShape AlternateTestLeftFamily AlternateTestRightFamily = LT
  compareStructuralShape AlternateTestRightFamily AlternateTestLeftFamily = GT
  compareStructuralShape AlternateTestRightFamily AlternateTestRightFamily = EQ

alternateTestChoiceSplit ::
  TestChoice left right ->
  StructuralCase AlternateTestChoiceFamily (TestChoice left right)
alternateTestChoiceSplit (TestLeft value) =
  StructuralCase AlternateTestLeftFamily value
alternateTestChoiceSplit (TestRight value) =
  StructuralCase AlternateTestRightFamily value

alternateTestChoicePayloadStrategy ::
  forall left right payload.
  (Mergeable left, Mergeable right) =>
  AlternateTestChoiceFamily (TestChoice left right) payload ->
  MergingStrategy payload
alternateTestChoicePayloadStrategy AlternateTestLeftFamily = rootStrategy
alternateTestChoicePayloadStrategy AlternateTestRightFamily = rootStrategy

alternateTestChoiceInject ::
  forall left right payload.
  AlternateTestChoiceFamily (TestChoice left right) payload ->
  payload ->
  TestChoice left right
alternateTestChoiceInject AlternateTestLeftFamily = TestLeft
alternateTestChoiceInject AlternateTestRightFamily = TestRight

alternateTestChoiceStrategy ::
  (Mergeable left, Mergeable right) =>
  MergingStrategy (TestChoice left right)
alternateTestChoiceStrategy =
  structuralStrategy
    alternateTestChoiceSplit
    alternateTestChoicePayloadStrategy
    alternateTestChoiceInject

assertTwoSidedInverse ::
  (Eq source, Eq target) =>
  (source -> target) ->
  (target -> source) ->
  source ->
  target ->
  Assertion
assertTwoSidedInverse wrap unwrap source target = do
  assertBool "unwrap . wrap /= id" $ unwrap (wrap source) == source
  assertBool "wrap . unwrap /= id" $ wrap (unwrap target) == target

assertWrapperLaws ::
  (StructuralWrapper wrapper, Eq source, Eq target) =>
  wrapper target source ->
  source ->
  target ->
  Assertion
assertWrapperLaws witness source target = do
  assertTwoSidedInverse
    (wrapValue witness)
    (unwrapValue witness)
    source
    target
  assertShapeCoherent witness witness

assertObservedWrapperLaws ::
  (StructuralWrapper wrapper, Eq observation, Show observation) =>
  (source -> observation) ->
  (target -> observation) ->
  wrapper target source ->
  source ->
  target ->
  Assertion
assertObservedWrapperLaws observeSource observeTarget witness source target = do
  observeSource (unwrapValue witness (wrapValue witness source))
    @?= observeSource source
  observeTarget (wrapValue witness (unwrapValue witness target))
    @?= observeTarget target
  assertShapeCoherent witness witness

assertShapeCoherent ::
  (StructuralFamily structuralFamily) =>
  structuralFamily value leftPayload ->
  structuralFamily value rightPayload ->
  Assertion
assertShapeCoherent left right =
  compareStructuralShape left right @?= case compareStructural left right of
    StructuralLT -> LT
    StructuralEQ -> EQ
    StructuralGT -> GT

data SomeStructuralWitness structuralFamily value where
  SomeStructuralWitness ::
    structuralFamily value payload ->
    SomeStructuralWitness structuralFamily value

assertSomeShapeCoherent ::
  (StructuralFamily structuralFamily) =>
  SomeStructuralWitness structuralFamily value ->
  SomeStructuralWitness structuralFamily value ->
  Assertion
assertSomeShapeCoherent
  (SomeStructuralWitness left)
  (SomeStructuralWitness right) =
    assertShapeCoherent left right

assertSelfMerge ::
  forall value.
  (HasCallStack, Mergeable value, Eq value, Show value) =>
  value ->
  Assertion
assertSelfMerge value =
  case resolveStrategy rootStrategy value of
    ResolvedStrategy _ (SimpleStrategy merge) payload inject ->
      inject (merge "condition" payload payload) @?= value
    _ -> assertFailure $ "Expected a terminal SimpleStrategy for " <> show value

assertMerged ::
  forall value.
  ( HasCallStack,
    Mergeable value,
    Eq (AsKey (Union value)),
    Show (AsKey (Union value))
  ) =>
  SymBool ->
  value ->
  value ->
  value ->
  Assertion
assertMerged condition left right expected =
  AsKey
    (mrgIf condition (mrgSingle left) (mrgSingle right) :: Union value)
    @?= AsKey (mrgSingle expected)

assertConcreteSelection ::
  forall value.
  (Show value) =>
  MergingStrategy value ->
  value ->
  value ->
  Assertion
assertConcreteSelection strategy left right = do
  fmap show
    (singleView (ifWithStrategy strategy (con True) (UnionSingle left) (UnionSingle right)))
    @?= Just (show left)
  fmap show
    (singleView (ifWithStrategy strategy (con False) (UnionSingle left) (UnionSingle right)))
    @?= Just (show right)

historicalMergeableMatrix :: Test
historicalMergeableMatrix =
  testGroup
    "historical Mergeable instance matrix"
    [ testGroup
        "ordered terminal instances"
        [ testProperty "Bool" $
            ioProperty . \(value :: Bool) -> assertSelfMerge value,
          testProperty "Integer" $
            ioProperty . \(value :: Integer) -> assertSelfMerge value,
          testProperty "Char" $
            ioProperty . \(value :: Char) -> assertSelfMerge value,
          testProperty "Int" $
            ioProperty . \(value :: Int) -> assertSelfMerge value,
          testProperty "Int8" $
            ioProperty . \(value :: Int8) -> assertSelfMerge value,
          testProperty "Int16" $
            ioProperty . \(value :: Int16) -> assertSelfMerge value,
          testProperty "Int32" $
            ioProperty . \(value :: Int32) -> assertSelfMerge value,
          testProperty "Int64" $
            ioProperty . \(value :: Int64) -> assertSelfMerge value,
          testProperty "Word" $
            ioProperty . \(value :: Word) -> assertSelfMerge value,
          testProperty "Word8" $
            ioProperty . \(value :: Word8) -> assertSelfMerge value,
          testProperty "Word16" $
            ioProperty . \(value :: Word16) -> assertSelfMerge value,
          testProperty "Word32" $
            ioProperty . \(value :: Word32) -> assertSelfMerge value,
          testProperty "Word64" $
            ioProperty . \(value :: Word64) -> assertSelfMerge value,
          testCase "unit" $ assertSelfMerge (),
          testProperty "ByteString" $
            ioProperty . \(value :: String) -> assertSelfMerge (C.pack value)
        ],
      testGroup
        "algebraic instances"
        [ testCase "Either" $ do
            assertSelfMerge (Left 1 :: Either Integer Integer)
            assertSelfMerge (Right 2 :: Either Integer Integer)
            assertMerged
              "condition"
              (Left "left" :: Either (AsKey SymBool) Integer)
              (Left "right")
              (Left (symIte "condition" "left" "right")),
          testCase "Maybe" $ do
            assertSelfMerge (Nothing :: Maybe Integer)
            assertSelfMerge (Just 1 :: Maybe Integer)
            assertMerged
              "condition"
              (Just "left" :: Maybe (AsKey SymBool))
              (Just "right")
              (Just (symIte "condition" "left" "right")),
          testCase "List and nested List" $ do
            assertSelfMerge ([] :: [Integer])
            assertSelfMerge [1, 2 :: Integer]
            assertSelfMerge [[1], [], [2, 3 :: Integer]]
            assertMerged
              "condition"
              (["left0", "left1"] :: [AsKey SymBool])
              ["right0", "right1"]
              [ symIte "condition" "left0" "right0",
                symIte "condition" "left1" "right1"
              ]
        ],
      testGroup
        "tuples 2 through 8"
        [ testCase "pair" $
            assertMerged
              "condition"
              (("l1", "l2") :: (AsKey SymBool, AsKey SymBool))
              ("r1", "r2")
              ( symIte "condition" "l1" "r1",
                symIte "condition" "l2" "r2"
              ),
          testCase "triple" $
            assertMerged
              "condition"
              (("l1", "l2", "l3") ::
                (AsKey SymBool, AsKey SymBool, AsKey SymBool))
              ("r1", "r2", "r3")
              ( symIte "condition" "l1" "r1",
                symIte "condition" "l2" "r2",
                symIte "condition" "l3" "r3"
              ),
          testCase "4-tuple" $
            assertMerged
              "condition"
              (("l1", "l2", "l3", "l4") ::
                ( AsKey SymBool,
                  AsKey SymBool,
                  AsKey SymBool,
                  AsKey SymBool
                ))
              ("r1", "r2", "r3", "r4")
              ( symIte "condition" "l1" "r1",
                symIte "condition" "l2" "r2",
                symIte "condition" "l3" "r3",
                symIte "condition" "l4" "r4"
              ),
          testCase "5-tuple" $
            assertMerged
              "condition"
              (("l1", "l2", "l3", "l4", "l5") ::
                ( AsKey SymBool,
                  AsKey SymBool,
                  AsKey SymBool,
                  AsKey SymBool,
                  AsKey SymBool
                ))
              ("r1", "r2", "r3", "r4", "r5")
              ( symIte "condition" "l1" "r1",
                symIte "condition" "l2" "r2",
                symIte "condition" "l3" "r3",
                symIte "condition" "l4" "r4",
                symIte "condition" "l5" "r5"
              ),
          testCase "6-tuple" $
            assertMerged
              "condition"
              (("l1", "l2", "l3", "l4", "l5", "l6") ::
                ( AsKey SymBool,
                  AsKey SymBool,
                  AsKey SymBool,
                  AsKey SymBool,
                  AsKey SymBool,
                  AsKey SymBool
                ))
              ("r1", "r2", "r3", "r4", "r5", "r6")
              ( symIte "condition" "l1" "r1",
                symIte "condition" "l2" "r2",
                symIte "condition" "l3" "r3",
                symIte "condition" "l4" "r4",
                symIte "condition" "l5" "r5",
                symIte "condition" "l6" "r6"
              ),
          testCase "7-tuple" $
            assertMerged
              "condition"
              (("l1", "l2", "l3", "l4", "l5", "l6", "l7") ::
                ( AsKey SymBool,
                  AsKey SymBool,
                  AsKey SymBool,
                  AsKey SymBool,
                  AsKey SymBool,
                  AsKey SymBool,
                  AsKey SymBool
                ))
              ("r1", "r2", "r3", "r4", "r5", "r6", "r7")
              ( symIte "condition" "l1" "r1",
                symIte "condition" "l2" "r2",
                symIte "condition" "l3" "r3",
                symIte "condition" "l4" "r4",
                symIte "condition" "l5" "r5",
                symIte "condition" "l6" "r6",
                symIte "condition" "l7" "r7"
              ),
          testCase "8-tuple" $
            assertMerged
              "condition"
              (("l1", "l2", "l3", "l4", "l5", "l6", "l7", "l8") ::
                ( AsKey SymBool,
                  AsKey SymBool,
                  AsKey SymBool,
                  AsKey SymBool,
                  AsKey SymBool,
                  AsKey SymBool,
                  AsKey SymBool,
                  AsKey SymBool
                ))
              ("r1", "r2", "r3", "r4", "r5", "r6", "r7", "r8")
              ( symIte "condition" "l1" "r1",
                symIte "condition" "l2" "r2",
                symIte "condition" "l3" "r3",
                symIte "condition" "l4" "r4",
                symIte "condition" "l5" "r5",
                symIte "condition" "l6" "r6",
                symIte "condition" "l7" "r7",
                symIte "condition" "l8" "r8"
              )
        ],
      testGroup
        "function result strategies"
        [ testCase "simple result merges pointwise" $
            case rootStrategy ::
              MergingStrategy (Integer -> AsKey SymBool) of
              SimpleStrategy merge -> do
                let merged = merge "condition" (const "left") (const "right")
                merged 0 @?= symIte "condition" "left" "right"
              _ -> assertFailure "Expected pointwise function strategy",
          testCase "non-simple result has no function strategy" $
            case rootStrategy :: MergingStrategy (Integer -> Maybe Integer) of
              NoStrategy -> pure ()
              _ -> assertFailure "Expected NoStrategy for structural function result"
        ],
      testGroup
        "standard transformer instances"
        [ testCase "MaybeT" $ do
            assertSelfMerge
              (MaybeT Nothing :: MaybeT Maybe Integer)
            assertSelfMerge
              (MaybeT (Just Nothing) :: MaybeT Maybe Integer)
            assertSelfMerge
              (MaybeT (Just (Just 1)) :: MaybeT Maybe Integer)
            assertMerged
              "condition"
              ( MaybeT (Identity (Just "left")) ::
                  MaybeT Identity (AsKey SymBool)
              )
              (MaybeT (Identity (Just "right")))
              ( MaybeT
                  (Identity (Just (symIte "condition" "left" "right")))
              ),
          testCase "ExceptT" $ do
            assertSelfMerge
              (ExceptT Nothing :: ExceptT Integer Maybe Integer)
            assertSelfMerge
              (ExceptT (Just (Left 1)) :: ExceptT Integer Maybe Integer)
            assertSelfMerge
              (ExceptT (Just (Right 1)) :: ExceptT Integer Maybe Integer)
            assertMerged
              "condition"
              ( ExceptT (Identity (Left "left")) ::
                  ExceptT (AsKey SymBool) Identity (AsKey SymBool)
              )
              (ExceptT (Identity (Left "right")))
              ( ExceptT
                  (Identity (Left (symIte "condition" "left" "right")))
              )
            assertMerged
              "condition"
              ( ExceptT (Identity (Right "left")) ::
                  ExceptT (AsKey SymBool) Identity (AsKey SymBool)
              )
              (ExceptT (Identity (Right "right")))
              ( ExceptT
                  (Identity (Right (symIte "condition" "left" "right")))
              ),
          testCase "lazy StateT" $ do
            let left ::
                  StateLazy.StateT
                    Integer
                    (AsKey1 Union)
                    (AsKey SymBool)
                left = StateLazy.StateT $ \state ->
                  mrgSingle ("left", state + 1)
                right ::
                  StateLazy.StateT
                    Integer
                    (AsKey1 Union)
                    (AsKey SymBool)
                right = StateLazy.StateT $ \state ->
                  mrgSingle ("right", state + 2)
                merged =
                  ifWithStrategy
                    rootStrategy
                    "condition"
                    (UnionSingle left)
                    (UnionSingle right)
            case singleView merged of
              Just selected ->
                StateLazy.runStateT selected 3
                  @?= mrgIf
                    "condition"
                    (mrgSingle ("left", 4))
                    (mrgSingle ("right", 5))
              Nothing -> assertFailure "Lazy StateT strategy did not merge",
          testCase "strict StateT" $ do
            let left ::
                  StateStrict.StateT
                    Integer
                    (AsKey1 Union)
                    (AsKey SymBool)
                left = StateStrict.StateT $ \state ->
                  mrgSingle ("left", state + 1)
                right ::
                  StateStrict.StateT
                    Integer
                    (AsKey1 Union)
                    (AsKey SymBool)
                right = StateStrict.StateT $ \state ->
                  mrgSingle ("right", state + 2)
                merged =
                  ifWithStrategy
                    rootStrategy
                    "condition"
                    (UnionSingle left)
                    (UnionSingle right)
            case singleView merged of
              Just selected ->
                StateStrict.runStateT selected 3
                  @?= mrgIf
                    "condition"
                    (mrgSingle ("left", 4))
                    (mrgSingle ("right", 5))
              Nothing -> assertFailure "Strict StateT strategy did not merge",
          testCase "ContT" $
            case rootStrategy ::
              MergingStrategy
                ( ContT
                    (AsKey SymBool)
                    (AsKey1 Union)
                    (AsKey SymBool)
                ) of
              SimpleStrategy merge -> do
                let left = ContT ($ "left")
                    right = ContT ($ "right")
                runContT (merge "condition" left right) mrgSingle
                  @?= mrgIf
                    "condition"
                    (mrgSingle "left")
                    (mrgSingle "right")
              _ -> assertFailure "Expected ContT strategy to be simple",
          testCase "lazy RWST" $
            case rootStrategy ::
              MergingStrategy
                ( RWSLazy.RWST
                    Integer
                    Integer
                    Integer
                    (AsKey1 Union)
                    (AsKey SymBool)
                ) of
              SimpleStrategy merge -> do
                let left = RWSLazy.RWST $ \environment state ->
                      mrgSingle ("left", state + environment, 1)
                    right = RWSLazy.RWST $ \environment state ->
                      mrgSingle ("right", state - environment, 2)
                RWSLazy.runRWST (merge "condition" left right) 2 5
                  @?= mrgIf
                    "condition"
                    (mrgSingle ("left", 7, 1))
                    (mrgSingle ("right", 3, 2))
              _ -> assertFailure "Expected lazy RWST strategy to be simple",
          testCase "strict RWST" $
            case rootStrategy ::
              MergingStrategy
                ( RWSStrict.RWST
                    Integer
                    Integer
                    Integer
                    (AsKey1 Union)
                    (AsKey SymBool)
                ) of
              SimpleStrategy merge -> do
                let left = RWSStrict.RWST $ \environment state ->
                      mrgSingle ("left", state + environment, 1)
                    right = RWSStrict.RWST $ \environment state ->
                      mrgSingle ("right", state - environment, 2)
                RWSStrict.runRWST (merge "condition" left right) 2 5
                  @?= mrgIf
                    "condition"
                    (mrgSingle ("left", 7, 1))
                    (mrgSingle ("right", 3, 2))
              _ -> assertFailure "Expected strict RWST strategy to be simple",
          testCase "lazy WriterT" $ do
            let left = WriterLazy.WriterT (mrgSingle ("left", 1))
                right = WriterLazy.WriterT (mrgSingle ("right", 2))
                merged =
                  ifWithStrategy
                    ( rootStrategy ::
                        MergingStrategy
                          ( WriterLazy.WriterT
                              Integer
                              (AsKey1 Union)
                              (AsKey SymBool)
                          )
                    )
                    "condition"
                    (UnionSingle left)
                    (UnionSingle right)
            case singleView merged of
              Just selected ->
                WriterLazy.runWriterT selected
                  @?= mrgIf
                    "condition"
                    (mrgSingle ("left", 1))
                    (mrgSingle ("right", 2))
              Nothing -> assertFailure "Lazy WriterT strategy did not merge",
          testCase "strict WriterT" $ do
            let left = WriterStrict.WriterT (mrgSingle ("left", 1))
                right = WriterStrict.WriterT (mrgSingle ("right", 2))
                merged =
                  ifWithStrategy
                    ( rootStrategy ::
                        MergingStrategy
                          ( WriterStrict.WriterT
                              Integer
                              (AsKey1 Union)
                              (AsKey SymBool)
                          )
                    )
                    "condition"
                    (UnionSingle left)
                    (UnionSingle right)
            case singleView merged of
              Just selected ->
                WriterStrict.runWriterT selected
                  @?= mrgIf
                    "condition"
                    (mrgSingle ("left", 1))
                    (mrgSingle ("right", 2))
              Nothing -> assertFailure "Strict WriterT strategy did not merge",
          testCase "ReaderT" $
            case rootStrategy ::
              MergingStrategy
                (ReaderT Integer (AsKey1 Union) (AsKey SymBool)) of
              SimpleStrategy merge -> do
                let left = ReaderT $ \_ -> mrgSingle "left"
                    right = ReaderT $ \_ -> mrgSingle "right"
                runReaderT (merge "condition" left right) 0
                  @?= mrgIf
                    "condition"
                    (mrgSingle "left")
                    (mrgSingle "right")
              _ -> assertFailure "Expected ReaderT strategy to be simple"
        ],
      testGroup
        "identity, sum, and ordering instances"
        [ testCase "Identity" $ do
            assertSelfMerge (Identity (1 :: Integer))
            assertMerged
              "condition"
              (Identity "left" :: Identity (AsKey SymBool))
              (Identity "right")
              (Identity (symIte "condition" "left" "right")),
          testCase "IdentityT" $ do
            assertSelfMerge
              (IdentityT Nothing :: IdentityT Maybe Integer)
            assertMerged
              "condition"
              ( IdentityT (Just "left") ::
                  IdentityT Maybe (AsKey SymBool)
              )
              (IdentityT (Just "right"))
              (IdentityT (Just (symIte "condition" "left" "right"))),
          testCase "Sum" $ do
            assertSelfMerge (InL Nothing :: Sum Maybe Maybe Integer)
            assertSelfMerge (InL (Just 1) :: Sum Maybe Maybe Integer)
            assertSelfMerge (InR Nothing :: Sum Maybe Maybe Integer)
            assertSelfMerge (InR (Just 1) :: Sum Maybe Maybe Integer)
            assertMerged
              "condition"
              (InL (Just "left") :: Sum Maybe Maybe (AsKey SymBool))
              (InL (Just "right"))
              (InL (Just (symIte "condition" "left" "right"))),
          testCase "Ordering" $ do
            assertSelfMerge LT
            assertSelfMerge EQ
            assertSelfMerge GT
        ]
    ]

mergeableTests :: Test
mergeableTests =
  testGroup
    "Mergeable"
    [ testGroup
        "terminal strategies"
        [ testCase "symbolic boolean" $ do
            case rootStrategy :: MergingStrategy (AsKey SymBool) of
              SimpleStrategy merge -> do
                merge (con True) "left" "right" @?= "left"
                merge (con False) "left" "right" @?= "right"
                merge "condition" "left" "right"
                  @?= symIte "condition" "left" "right"
              _ -> assertFailure "Expected the symbolic boolean strategy to be simple",
          testProperty "ordered Bool" $
            ioProperty . \(value :: Bool) -> assertSelfMerge value,
          testProperty "ordered Integer" $
            ioProperty . \(value :: Integer) -> assertSelfMerge value,
          testProperty "ordered Char" $
            ioProperty . \(value :: Char) -> assertSelfMerge value,
          testProperty "ordered ByteString" $
            ioProperty . \(value :: String) -> assertSelfMerge (C.pack value),
          testCase "structural resolve retains a typed injector" $ do
            case resolveStrategy
              rootStrategy
              (Just (ssym "value") :: Maybe (AsKey SymBool)) of
              ResolvedStrategy
                (DynamicStructuralIdx _ : [])
                (SimpleStrategy merge)
                payload
                inject ->
                  inject (merge "condition" payload payload)
                    @?= Just (ssym "value")
              _ -> assertFailure "Expected one structural group and a simple payload"
        ],
      testGroup
        "actual structural alternatives"
        [ testCase "Either merges only equal constructors" $ do
            assertMerged
              "condition"
              (Left (ssym "left") :: Either (AsKey SymBool) Integer)
              (Left (ssym "right"))
              (Left (symIte "condition" "left" "right"))
            let divergent =
                  ifWithStrategy
                    (rootStrategy :: MergingStrategy (Either Integer Integer))
                    "condition"
                    (UnionSingle (Left 1))
                    (UnionSingle (Right 2))
            case divergent of
              UnionIf {} -> pure ()
              _ -> assertFailure "Different constructors were collapsed",
          testCase "Maybe merges a Just payload" $
            assertMerged
              "condition"
              (Just (ssym "left") :: Maybe (AsKey SymBool))
              (Just (ssym "right"))
              (Just (symIte "condition" "left" "right")),
          testCase "list uses Nil/Cons structure, not a length tag" $ do
            assertMerged
              "condition"
              [ssym "left0", ssym "left1" :: AsKey SymBool]
              [ssym "right0", ssym "right1"]
              [ symIte "condition" "left0" "right0",
                symIte "condition" "left1" "right1"
              ]
            let differentShapes =
                  ifWithStrategy
                    (rootStrategy :: MergingStrategy [Integer])
                    "condition"
                    (UnionSingle [])
                    (UnionSingle [1])
            case differentShapes of
              UnionIf {} -> pure ()
              _ -> assertFailure "Nil and Cons were collapsed",
          testCase "nested pair/list structure merges homogeneous payloads" $
            assertMerged
              "condition"
              ( Just (ssym "left" :: AsKey SymBool),
                [ssym "left0", ssym "left1" :: AsKey SymBool]
              )
              (Just (ssym "right"), [ssym "right0", ssym "right1"])
              ( Just (symIte "condition" "left" "right"),
                [ symIte "condition" "left0" "right0",
                  symIte "condition" "left1" "right1"
                ]
              ),
          testCase "structural comparison agrees with shape ordering" $ do
            case compareStructural TestLeftFamily TestLeftFamily of
              StructuralEQ -> pure ()
              _ -> assertFailure "Equal structural witnesses did not compare equal"
            case compareStructural TestLeftFamily TestRightFamily of
              StructuralLT -> pure ()
              _ -> assertFailure "Left structural witness did not sort first"
            case compareStructural TestRightFamily TestLeftFamily of
              StructuralGT -> pure ()
              _ -> assertFailure "Right structural witness did not sort last"
            compareStructuralShape TestLeftFamily TestLeftFamily @?= EQ
            compareStructuralShape TestLeftFamily TestRightFamily @?= LT
            compareStructuralShape TestRightFamily TestLeftFamily @?= GT
            assertShapeCoherent TestLeftFamily TestLeftFamily
            assertShapeCoherent TestLeftFamily TestRightFamily
            assertShapeCoherent TestRightFamily TestLeftFamily
            assertShapeCoherent TestRightFamily TestRightFamily
            assertShapeCoherent AlternateTestLeftFamily AlternateTestLeftFamily
            assertShapeCoherent AlternateTestLeftFamily AlternateTestRightFamily
            assertShapeCoherent AlternateTestRightFamily AlternateTestLeftFamily
            assertShapeCoherent AlternateTestRightFamily AlternateTestRightFamily
        ],
      testGroup
        "production structural family coherence"
        [ testCase "ListFamily" $ do
            let empty =
                  SomeStructuralWitness EmptyListFamily ::
                    SomeStructuralWitness ListFamily [Integer]
                cons =
                  SomeStructuralWitness ConsListFamily ::
                    SomeStructuralWitness ListFamily [Integer]
            mapM_
              (uncurry assertSomeShapeCoherent)
              [(empty, empty), (empty, cons), (cons, empty), (cons, cons)],
          testCase "EitherFamily" $ do
            let left =
                  SomeStructuralWitness LeftEitherFamily ::
                    SomeStructuralWitness EitherFamily (Either Integer Bool)
                right =
                  SomeStructuralWitness RightEitherFamily ::
                    SomeStructuralWitness EitherFamily (Either Integer Bool)
            mapM_
              (uncurry assertSomeShapeCoherent)
              [(left, left), (left, right), (right, left), (right, right)],
          testCase "MaybeFamily" $ do
            let nothing =
                  SomeStructuralWitness NothingMaybeFamily ::
                    SomeStructuralWitness MaybeFamily (Maybe Integer)
                just =
                  SomeStructuralWitness JustMaybeFamily ::
                    SomeStructuralWitness MaybeFamily (Maybe Integer)
            mapM_
              (uncurry assertSomeShapeCoherent)
              [(nothing, nothing), (nothing, just), (just, nothing), (just, just)],
          testCase "SomeBVFamily" $ do
            let literal =
                  SomeStructuralWitness LiteralSomeBVFamily ::
                    SomeStructuralWitness SomeBVFamily (SomeBV WordN)
                four =
                  SomeStructuralWitness (SizedSomeBVFamily (Proxy @4)) ::
                    SomeStructuralWitness SomeBVFamily (SomeBV WordN)
                five =
                  SomeStructuralWitness (SizedSomeBVFamily (Proxy @5)) ::
                    SomeStructuralWitness SomeBVFamily (SomeBV WordN)
            mapM_
              (uncurry assertSomeShapeCoherent)
              [ (literal, literal),
                (literal, four),
                (four, literal),
                (four, four),
                (four, five),
                (five, four),
                (five, five)
              ],
          testCase "CBMCEitherFamily" $ do
            let left =
                  SomeStructuralWitness CBMCLeftFamily ::
                    SomeStructuralWitness
                      CBMCEitherFamily
                      (CBMCEither Integer Bool)
                right =
                  SomeStructuralWitness CBMCRightFamily ::
                    SomeStructuralWitness
                      CBMCEitherFamily
                      (CBMCEither Integer Bool)
            mapM_
              (uncurry assertSomeShapeCoherent)
              [(left, left), (left, right), (right, left), (right, right)],
          testCase "concrete guards select exactly one structural arm" $ do
            assertConcreteSelection
              (rootStrategy :: MergingStrategy (Either Integer Integer))
              (Left 1)
              (Right 2)
            assertConcreteSelection
              (rootStrategy :: MergingStrategy (Maybe Integer))
              Nothing
              (Just 1)
            assertConcreteSelection
              (rootStrategy :: MergingStrategy [Integer])
              []
              [1]
            assertConcreteSelection
              (rootStrategy :: MergingStrategy (SomeBV WordN))
              (1 :: SomeBV WordN)
              (SomeBV (1 :: WordN 4))
            assertConcreteSelection
              ( rootStrategy ::
                  MergingStrategy (CBMCEither Integer Integer)
              )
              (CBMCEither (Left 1))
              (CBMCEither (Right 2))
        ],
      testGroup
        "relation-owned wrappers"
        [ testProperty "two-sided Box inverse" $ \(value :: Integer) ->
            unwrapValue BoxWrapper (wrapValue BoxWrapper value) == value
              && wrapValue BoxWrapper (unwrapValue BoxWrapper (Box value))
                == Box value,
          testGroup
            "production wrapper inverse laws"
            [ testCase "NominalWrapper" $ do
                let source = 1 :: Integer
                    target =
                      Nominal 2 ::
                        Nominal ('Domain "mergeable-test" '[]) Integer
                assertWrapperLaws NominalWrapper source target,
              testCase "ReaderTWrapper" $ do
                let source environment = Identity (environment + 1 :: Integer)
                    target = ReaderT $ \environment -> Identity (environment + 2)
                    sample = 3
                    observeSource function = runIdentity (function sample)
                    observeTarget reader = runIdentity (runReaderT reader sample)
                assertObservedWrapperLaws
                  observeSource
                  observeTarget
                  ReaderTWrapper
                  source
                  target,
              testCase "IdentityTWrapper" $ do
                let source = Identity (1 :: Integer)
                    target = IdentityT (Identity 2) :: IdentityT Identity Integer
                assertWrapperLaws IdentityTWrapper source target,
              testCase "ContTWrapper" $ do
                let source continuation = continuation (1 :: Integer)
                    target = ContT $ \continuation -> continuation 2
                    continuation value = Identity (value + 10)
                    observeSource function = runIdentity (function continuation)
                    observeTarget action =
                      runIdentity (runContT action continuation)
                assertObservedWrapperLaws
                  observeSource
                  observeTarget
                  ContTWrapper
                  source
                  target,
              testCase "LazyRWSTWrapper" $ do
                let source environment state =
                      Identity
                        (environment + state :: Integer, state + 1, ["source"])
                    target = RWSLazy.RWST $ \environment state ->
                      Identity
                        (environment - state :: Integer, state + 2, ["target"])
                    observeSource function = runIdentity (function 5 3)
                    observeTarget action =
                      runIdentity (RWSLazy.runRWST action 5 3)
                assertObservedWrapperLaws
                  observeSource
                  observeTarget
                  LazyRWSTWrapper
                  source
                  target,
              testCase "StrictRWSTWrapper" $ do
                let source environment state =
                      Identity
                        (environment + state :: Integer, state + 1, ["source"])
                    target = RWSStrict.RWST $ \environment state ->
                      Identity
                        (environment - state :: Integer, state + 2, ["target"])
                    observeSource function = runIdentity (function 5 3)
                    observeTarget action =
                      runIdentity (RWSStrict.runRWST action 5 3)
                assertObservedWrapperLaws
                  observeSource
                  observeTarget
                  StrictRWSTWrapper
                  source
                  target,
              testCase "ComposeWrapper" $ do
                let source = Just [1, 2] :: Maybe [Integer]
                    target = Compose (Just [3]) :: Compose Maybe [] Integer
                assertWrapperLaws ComposeWrapper source target,
              testCase "EndoWrapper" $ do
                let source = (+ 1) :: Integer -> Integer
                    target = Endo (* 2)
                    sample = 5
                assertObservedWrapperLaws
                  ($ sample)
                  (\action -> appEndo action sample)
                  EndoWrapper
                  source
                  target,
              testCase "GenericProductWrapper" $ do
                let source = (Identity (1 :: Integer), Identity 2)
                    target = Identity 3 :*: Identity 4
                assertWrapperLaws GenericProductWrapper source target,
              testCase "M1Wrapper" $ do
                let source = Identity (1 :: Integer)
                    target = M1 (Identity 2)
                assertWrapperLaws M1Wrapper source target,
              testCase "K1Wrapper" $ do
                let source = 1 :: Integer
                    target = K1 2
                assertWrapperLaws K1Wrapper source target,
              testCase "Par1Wrapper" $ do
                let source = 1 :: Integer
                    target = Par1 2
                assertWrapperLaws Par1Wrapper source target,
              testCase "Rec1Wrapper" $ do
                let source = Identity (1 :: Integer)
                    target = Rec1 (Identity 2)
                assertWrapperLaws Rec1Wrapper source target,
              testCase "Comp1Wrapper" $ do
                let source = Identity (Just (1 :: Integer))
                    target =
                      Comp1 (Identity (Just 2)) ::
                        (Identity :.: Maybe) Integer
                assertWrapperLaws Comp1Wrapper source target,
              testCase "DefaultWrapper" $ do
                let source = GenericBox (1 :: Integer)
                    target = Default (GenericBox 2)
                assertObservedWrapperLaws
                  id
                  (\(Default value) -> value)
                  DefaultWrapper
                  source
                  target,
              testCase "GenericWrapper" $ do
                let target = GenericBox (2 :: Integer)
                    source = from (GenericBox (1 :: Integer))
                assertWrapperLaws GenericWrapper source target,
              testCase "Default1Wrapper" $ do
                let source = GenericBox (1 :: Integer)
                    target = Default1 (GenericBox 2) :: Default1 GenericBox Integer
                assertObservedWrapperLaws
                  id
                  (\(Default1 value) -> value)
                  Default1Wrapper
                  source
                  target,
              testCase "Generic1Wrapper" $ do
                let target = GenericBox (2 :: Integer)
                    source = from1 (GenericBox (1 :: Integer))
                assertWrapperLaws Generic1Wrapper source target,
              testCase "AsKeyWrapper" $ do
                let source = 1 :: Integer
                    target = AsKey 2
                assertWrapperLaws AsKeyWrapper source target,
              testCase "AsKey1Wrapper" $ do
                let source = Just (1 :: Integer)
                    target = AsKey1 (Just 2) :: AsKey1 Maybe Integer
                assertObservedWrapperLaws
                  id
                  (\(AsKey1 value) -> value)
                  AsKey1Wrapper
                  source
                  target,
              testCase "FreshTWrapper" $ do
                let source _ index = Identity (1 :: Integer, index + 1)
                    target = FreshT $ \_ index -> Identity (2, index + 2)
                    observeSource function =
                      runIdentity
                        (function "mergeable-test" (FreshIndex 3))
                    observeTarget action =
                      runIdentity
                        (runFreshTFromIndex action "mergeable-test" (FreshIndex 3))
                assertObservedWrapperLaws
                  observeSource
                  observeTarget
                  FreshTWrapper
                  source
                  target,
              testCase "CBMCExceptTWrapper" $ do
                let source =
                      Identity
                        (CBMCEither (Right (1 :: Integer)) :: CBMCEither String Integer)
                    target =
                      CBMCExceptT
                        (Identity (CBMCEither (Left "target"))) ::
                        CBMCExceptT String Identity Integer
                assertWrapperLaws CBMCExceptTWrapper source target
            ],
          testCase "simple source remains simple" $
            assertMerged
              "condition"
              (Box (ssym "left") :: Box (AsKey SymBool))
              (Box (ssym "right"))
              (Box (symIte "condition" "left" "right")),
          testCase "structural source retains a typed group" $ do
            let wrapped =
                  ifWithStrategy
                    (rootStrategy :: MergingStrategy (Box (Maybe (AsKey SymBool))))
                    "condition"
                    (UnionSingle (Box (Just "left")))
                    (UnionSingle (Box (Just "right")))
            case wrapped of
              UnionGroup {} -> pure ()
              _ -> assertFailure "Witnessed wrapping flattened its structural group",
          testCase "ordinary fmap is transparent and erases the old group" $ do
            let grouped =
                  ifWithStrategy
                    (rootStrategy :: MergingStrategy (Maybe (AsKey SymBool)))
                    "condition"
                    (UnionSingle (Just "left"))
                    (UnionSingle (Just "right"))
            case grouped of
              UnionGroup {} -> pure ()
              _ -> assertFailure "Structural merge did not retain a group"
            case fmap (Box . maybe (con False) id) grouped of
              UnionSingle (Box actual) ->
                actual @?= symIte "condition" "left" "right"
              _ -> assertFailure "Ordinary fmap retained a stale typed group",
          testCase "bind traverses the homogeneous payload support" $ do
            let grouped =
                  ifWithStrategy
                    (rootStrategy :: MergingStrategy (Maybe (AsKey SymBool)))
                    "condition"
                    (UnionSingle (Just "left"))
                    (UnionSingle (Just "right"))
            case grouped >>= \value -> UnionSingle (maybe (con False) id value) of
              UnionSingle actual ->
                actual @?= symIte "condition" "left" "right"
              _ -> assertFailure "Bind re-expanded a merged homogeneous payload",
          testCase "normalizer retains nested structural groups" $ do
            let nested =
                  ifWithStrategy
                    ( rootStrategy ::
                        MergingStrategy
                          (Maybe (AsKey SymBool), [AsKey SymBool])
                    )
                    "condition"
                    (UnionSingle (Just "left", ["left-head", "left-tail"]))
                    (UnionSingle (Just "right", ["right-head", "right-tail"]))
            case nested of
              UnionGroup _ _ _ outerPayloads ->
                case outerPayloads of
                  UnionGroup {} -> pure ()
                  _ -> assertFailure "Nested structural payload group was flattened"
              _ -> assertFailure "Outer structural group was not retained",
          testCase "normalizer rebuilds a foreign structural family" $ do
            let foreignUnion =
                  ifWithStrategy
                    ( alternateTestChoiceStrategy ::
                        MergingStrategy (TestChoice Integer Integer)
                    )
                    "inner"
                    (UnionSingle (TestLeft 1))
                    (UnionSingle (TestLeft 2))
                canonicalForeign =
                  fullReconstruct
                    ( rootStrategy ::
                        MergingStrategy (TestChoice Integer Integer)
                    )
                    (eraseUnionGroups foreignUnion)
                actual =
                  ifWithStrategy
                    rootStrategy
                    "outer"
                    foreignUnion
                    (UnionSingle (TestLeft 3))
                expected =
                  ifWithStrategy
                    rootStrategy
                    "outer"
                    canonicalForeign
                    (UnionSingle (TestLeft 3))
            case actual of
              UnionGroup {} -> pure ()
              _ -> assertFailure "Foreign family was not rebuilt canonically"
            AsKey actual @?= AsKey expected,
          testCase "erase then reconstruct restores the structural normal form" $ do
            let original =
                  ifWithStrategy
                    ( rootStrategy ::
                        MergingStrategy (TestChoice Integer Integer)
                    )
                    "condition"
                    (UnionSingle (TestLeft 1))
                    (UnionSingle (TestLeft 2))
                erased = eraseUnionGroups original
                reconstructed = fullReconstruct rootStrategy erased
            case erased of
              UnionIf _ False _ _ _ -> pure ()
              _ -> assertFailure "Group erasure retained a stale merged invariant"
            case reconstructed of
              UnionGroup {} -> pure ()
              _ -> assertFailure "Reconstruction did not restore a typed group"
            AsKey reconstructed @?= AsKey original,
          testCase "IdentityT uses its owned relation" $ do
            assertMerged
              "condition"
              ( IdentityT (Identity (ssym "left")) ::
                  IdentityT Identity (AsKey SymBool)
              )
              (IdentityT (Identity (ssym "right")))
              (IdentityT (Identity (symIte "condition" "left" "right")))
            runIdentity (runIdentityT (IdentityT (Identity (1 :: Integer)))) @?= 1
        ],
      historicalMergeableMatrix
    ]
