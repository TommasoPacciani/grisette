{-# LANGUAGE GHC2024 #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}

module Grisette.SymPrim.TermUtilsTests (termUtilsTests) where

import Data.Foldable (toList)
import Data.List (foldl', sort)
import Grisette.Internal.Core.Data.Symbol (Symbol (IndexedSymbol), bound)
import Grisette.Internal.SymPrim.GeneralFun
  ( type (-->) (GeneralFun),
    freshArgSymbol,
    substTerm,
  )
import Grisette.Internal.SymPrim.Prim.SomeTerm (someTerm)
import Grisette.Internal.SymPrim.Prim.Term
  ( FocusedSeqFoldCallback
      ( FocusedSeqFoldCallbackBind,
        FocusedSeqFoldCallbackBody
      ),
    FocusedSeqFoldOperands
      ( FocusedSeqFoldOperand,
        NoFocusedSeqFoldOperands
      ),
    SomeTypedAnySymbol,
    Term,
    TypedAnySymbol,
    TypedConstantSymbol,
    TypedSymbol (TypedSymbol),
    addNumTerm,
    andTerm,
    conTerm,
    eqTerm,
    existsTerm,
    focusedSeqFoldTerm,
    forallTerm,
    iteTerm,
    seqLookupValueTerm,
    someTypedSymbol,
    symTerm,
    typedAnySymbol,
    typedConstantSymbol,
    pattern ForallTerm,
  )
import Grisette.Internal.SymPrim.Prim.TermUtils
  (extractSymSomeTermIncludeBoundedVars)
import Test.Framework (Test, testGroup)
import Test.Framework.Providers.HUnit (testCase)
import Test.HUnit (Assertion, assertEqual, assertFailure)

termUtilsTests :: Test
termUtilsTests = testGroup "all-symbol DAG collection"
  [ testCase "ordinary edges retain heterogeneous same-name symbols" $ do
      let condition = "same-name" :: TypedAnySymbol Bool
          index = "same-name" :: TypedAnySymbol Integer
          driver = "same-name" :: TypedAnySymbol [Integer]
          term = iteTerm (symTerm condition)
            (seqLookupValueTerm (conTerm 0) (symTerm driver) (symTerm index))
            (symTerm index)
      assertSymbols (conTerm (17 :: Integer)) []
      assertSymbols term [asAny condition, asAny index, asAny driver]
  , testCase "unused universal and existential binders are retained" $ do
      let universal = "unused-universal" :: TypedConstantSymbol Integer
          existential = "unused-existential" :: TypedConstantSymbol Bool
          condition = "quantified-condition" :: TypedAnySymbol Bool
      assertSymbols
        (forallTerm universal (existsTerm existential (symTerm condition)))
        [asAny universal, asAny existential, asAny condition]
  , testCase "nested function constants retain unused binders and body symbols" $ do
      let outer = "unused-outer" :: TypedConstantSymbol Integer
          inner = "unused-inner" :: TypedConstantSymbol Bool
          result = "function-result" :: TypedAnySymbol Integer
          term = conTerm $ GeneralFun outer $
            conTerm $ GeneralFun inner (symTerm result)
      assertSymbols term [asAny outer, asAny inner, asAny result]
  , testCase "shared nodes are collected independently of enclosing scope" $ do
      let binder = "shared-binder" :: TypedConstantSymbol Integer
          other = "shared-other" :: TypedAnySymbol Integer
          shared = eqTerm (symTerm binder) (symTerm other)
      assertSymbols (andTerm shared (forallTerm binder shared))
        [asAny binder, asAny other]
  , testCase "focused callback, binders, operands, initial and driver are retained" $ do
      let (term, expected) = focusedFixture
      assertSymbols term expected
  , testCase "nested focused callbacks retain every inner and outer edge" $ do
      let (inner, innerSymbols) = focusedFixture
          capture = typedConstantSymbol (bound "arg" 0)
            :: TypedConstantSymbol [Integer]
          state = "outer-state" :: TypedConstantSymbol Integer
          element = "outer-element" :: TypedConstantSymbol Integer
          operand = "outer-operand" :: TypedAnySymbol [Integer]
          initial = "outer-initial" :: TypedAnySymbol Integer
          driver = "outer-sequence" :: TypedAnySymbol [Integer]
          step = conTerm $ GeneralFun state $ conTerm $ GeneralFun element inner
          term = focusedSeqFoldTerm
            (FocusedSeqFoldCallbackBind capture (FocusedSeqFoldCallbackBody step))
            (FocusedSeqFoldOperand (symTerm operand) NoFocusedSeqFoldOperands)
            (symTerm initial) (symTerm driver)
      assertSymbols term $ innerSymbols ++
        [ asAny capture, asAny state, asAny element
        , asAny operand, asAny initial, asAny driver
        ]
  , testCase "freshness avoids every focused edge with exact type distinctions" $ do
      let (term, _) = focusedFixture
      assertEqual "Integer arg@1 is free despite the Bool binder at that name"
        (typedConstantSymbol (bound "arg" 1) :: TypedConstantSymbol Integer)
        (freshArgSymbol @Integer [someTerm term])
      assertEqual "Bool arg@0 is free despite the Integer binder at that name"
        (typedConstantSymbol (bound "arg" 0) :: TypedConstantSymbol Bool)
        (freshArgSymbol @Bool [someTerm term])
  , testCase "substitution freshness includes unused focused capture binders" $ do
      let (replacement, replacementSymbols) = focusedFixture
          source = "substitution-source" :: TypedAnySymbol Integer
          binder = typedConstantSymbol (bound "arg" 0)
            :: TypedConstantSymbol Integer
          renamed = typedConstantSymbol (bound "arg" 1)
            :: TypedConstantSymbol Integer
          body = forallTerm binder (eqTerm (symTerm source) (symTerm binder))
          substituted = substTerm source replacement mempty body
      case substituted of
        ForallTerm actualBinder _ ->
          assertEqual "the complete introduced set determines the fresh binder"
            (asAny renamed) (asAny actualBinder)
        _ -> assertFailure "substitution removed the universal quantifier"
      assertSymbols substituted (asAny renamed : replacementSymbols)
  , testCase "overlapping descendant sets in a shared DAG yield one exact union" $ do
      let symbols =
            [ typedAnySymbol (IndexedSymbol "dag-input" index)
                :: TypedAnySymbol Integer
            | index <- [0 .. 255]
            ]
          -- Each level shares the entire preceding graph through two edges.
          -- The result grows by one symbol, without unfolding that sharing.
          term = foldl'
            (\shared symbol -> addNumTerm shared (addNumTerm shared (symTerm symbol)))
            (conTerm 0) symbols
      assertSymbols term (asAny <$> symbols)
  ]

assertSymbols :: Term value -> [SomeTypedAnySymbol] -> Assertion
assertSymbols term expected = assertEqual "all mentioned symbols"
  (sort expected)
  (sort $ toList $ extractSymSomeTermIncludeBoundedVars $ someTerm term)

asAny :: forall kind value. TypedSymbol kind value -> SomeTypedAnySymbol
asAny (TypedSymbol symbol) = someTypedSymbol (typedAnySymbol @value symbol)

-- Raw construction deliberately retains unused binders. The all-symbol walk
-- must see them even though the free-symbol closure check omits them.
focusedFixture :: (Term Integer, [SomeTypedAnySymbol])
focusedFixture =
  ( focusedSeqFoldTerm
      (FocusedSeqFoldCallbackBind capture $
        FocusedSeqFoldCallbackBind unusedCapture $
          FocusedSeqFoldCallbackBody step)
      (FocusedSeqFoldOperand (symTerm operand) $
        FocusedSeqFoldOperand (symTerm booleanOperand) NoFocusedSeqFoldOperands)
      (symTerm initial) (symTerm driver)
  , [ asAny capture, asAny unusedCapture, asAny state, asAny element
    , asAny hidden, asAny operand, asAny booleanOperand
    , asAny initial, asAny driver
    ]
  )
  where
    capture = typedConstantSymbol (bound "arg" 0)
      :: TypedConstantSymbol Integer
    unusedCapture = typedConstantSymbol (bound "arg" 1)
      :: TypedConstantSymbol Bool
    state = typedConstantSymbol (bound "arg" 2)
      :: TypedConstantSymbol Integer
    element = typedConstantSymbol (bound "arg" 3)
      :: TypedConstantSymbol Integer
    operand = typedAnySymbol (bound "arg" 4) :: TypedAnySymbol Integer
    initial = typedAnySymbol (bound "arg" 5) :: TypedAnySymbol Integer
    driver = typedAnySymbol (bound "arg" 6) :: TypedAnySymbol [Integer]
    hidden = typedAnySymbol (bound "arg" 7) :: TypedAnySymbol Integer
    booleanOperand = "focused-boolean-operand" :: TypedAnySymbol Bool
    step = conTerm $ GeneralFun state $ conTerm $ GeneralFun element $
      addNumTerm (symTerm state) (symTerm hidden)
