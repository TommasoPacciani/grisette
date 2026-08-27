{-# LANGUAGE CPP #-}
{-# HLINT ignore "Eta reduce" #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveLift #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

-- |
-- Module      :   Grisette.Internal.SymPrim.GeneralFun
-- Copyright   :   (c) Sirui Lu 2024
-- License     :   BSD-3-Clause (see the LICENSE file)
--
-- Maintainer  :   siruilu@cs.washington.edu
-- Stability   :   Experimental
-- Portability :   GHC only
module Grisette.Internal.SymPrim.GeneralFun
  ( type (-->) (..),
    buildGeneralFun,
    buildGeneralFun2,
    buildGeneralFun3,
    buildFocusedGeneralFun,
    generalSubstSomeTerm,
    substTerm,
    freshArgSymbol,
    validateClosedSeqFold,
    validateClosedSeqFoldWith,
    checkClosedSeqFold,
    checkClosedSeqFoldWith,
    checkClosedFocusedSeqFold,
    validateClosedFocusedSeqFold,
    pevalClosedSeqFold,
    pevalClosedSeqFoldWith,
    pevalPreparedSeqFold,
    pevalPreparedSeqFoldWith,
    pevalPreparedFocusedSeqFold,
  )
where

#if MIN_VERSION_base(4,20,0)
#else
import Data.Foldable (Foldable (foldl'))
#endif

import Control.DeepSeq (NFData (rnf))
import qualified Control.Monad.State.Strict as State
import Data.Bifunctor (Bifunctor (second))
import qualified Data.HashMap.Strict as HM
import qualified Data.HashSet as HS
import Data.Hashable (Hashable (hashWithSalt))
import Data.List (sortOn)
import Data.Maybe (fromJust, mapMaybe)
import qualified Data.SBV as SBV
import qualified Data.SBV.Dynamic as SBVD
import GHC.Stack (HasCallStack)
import Grisette.Internal.Core.Data.Class.Function
  ( Apply (FunType, apply),
    Function ((#)),
  )
import Grisette.Internal.Core.Data.MemoUtils (htmemo)
import Grisette.Internal.Core.Data.Symbol
  ( Symbol (BoundSymbol),
  )
import Grisette.Internal.SymPrim.FunInstanceGen (supportedPrimFunUpTo)
import Grisette.Internal.SymPrim.Prim.Internal.Instances.PEvalFP ()
import Grisette.Internal.SymPrim.Prim.Internal.PartialEval (totalize2)
import Grisette.Internal.SymPrim.Prim.Internal.Term
  ( IsSymbolKind,
    LinkedRep (underlyingTerm, wrapTerm),
    NonFuncPrimConstraint,
    NonFuncSBVBaseType,
    type (-->) (GeneralFun),
    PEvalApplyTerm (pevalApplyTerm, sbvApplyTerm),
    PEvalBVTerm (pevalBVConcatTerm, pevalBVExtendTerm, pevalBVSelectTerm),
    PEvalBitCastOrTerm (pevalBitCastOrTerm),
    PEvalBitCastTerm (pevalBitCastTerm),
    PEvalBitwiseTerm
      ( pevalAndBitsTerm,
        pevalComplementBitsTerm,
        pevalOrBitsTerm,
        pevalXorBitsTerm
      ),
    PEvalDivModIntegralTerm
      ( pevalDivIntegralTerm,
        pevalModIntegralTerm
      ),
    PEvalFPTerm
      ( pevalFPBinaryTerm,
        pevalFPFMATerm,
        pevalFPRoundingBinaryTerm,
        pevalFPRoundingUnaryTerm,
        pevalFPTraitTerm,
        pevalFPUnaryTerm
      ),
    PEvalFloatingTerm (pevalFloatingUnaryTerm, pevalPowerTerm),
    PEvalFractionalTerm (pevalFdivTerm, pevalRecipTerm),
    PEvalFromIntegralTerm (pevalFromIntegralTerm),
    PEvalIEEEFPConvertibleTerm (pevalFromFPOrTerm, pevalToFPTerm),
    PEvalNumTerm
      ( pevalAbsNumTerm,
        pevalAddNumTerm,
        pevalMulNumTerm,
        pevalNegNumTerm,
        pevalSignumNumTerm
      ),
    PEvalOrdTerm (pevalLeOrdTerm, pevalLtOrdTerm),
    PEvalRotateTerm (pevalRotateRightTerm),
    PEvalShiftTerm (pevalShiftLeftTerm, pevalShiftRightTerm),
    pevalSelectTerm,
    pevalStoreTerm,
    pevalConstArrayTerm,
    pevalSeqConsTerm,
    pevalSeqAppendTerm,
    pevalSeqZipTerm,
    pevalSeqLengthTerm,
    pevalSeqRangeTerm,
    pevalSeqTailTerm,
    pevalSeqLookupTerm,
    pevalSeqLookupValueTerm,
    pevalSeqFoldTerm,
    pevalFocusedSeqFoldTerm,
    pevalSeqFoldWithTerm,
    pevalPairTerm,
    pevalFirstTerm,
    pevalSecondTerm,
    SBVRep (SBVType),
    SomeTypedAnySymbol,
    SomeTypedConstantSymbol,
    SupportedNonFuncPrim (withNonFuncPrim),
    SupportedPrim
      ( castTypedSymbol,
        defaultValue,
        parseSMTModelResult,
        pevalDistinctTerm,
        pevalITETerm,
        primTypeRep,
        withPrim
      ),
    SupportedPrimConstraint (PrimConstraint),
    SymRep (SymType),
    SymbolKind (AnyKind, ConstantKind),
    Term,
    FocusedSeqFoldBinderSymbols
      ( FocusedSeqFoldBinderSymbol,
        NoFocusedSeqFoldBinderSymbols
      ),
    FocusedSeqFoldCallback
      ( FocusedSeqFoldCallbackBind,
        FocusedSeqFoldCallbackBody
      ),
    FocusedSeqFoldOperands
      ( FocusedSeqFoldOperand,
        NoFocusedSeqFoldOperands
      ),
    focusedSeqFoldCallbackTerm,
    mapFocusedSeqFoldCallbackTerm,
    TypedAnySymbol,
    TypedConstantSymbol,
    TypedSymbol,
    applyTerm,
    conTerm,
    eqHeteroSymbol,
    existsTerm,
    forallTerm,
    partitionCVArg,
    pevalAndTerm,
    pevalEqTerm,
    pevalITEBasicTerm,
    pevalNotTerm,
    pevalOrTerm,
    pevalQuotIntegralTerm,
    pevalRemIntegralTerm,
    pevalRotateLeftTerm,
    pformatTerm,
    castSomeTypedSymbol,
    someTypedSymbol,
    symTerm,
    translateTypeError,
    typedAnySymbol,
    typedConstantSymbol,
    pattern AbsNumTerm,
    pattern AddNumTerm,
    pattern AndBitsTerm,
    pattern AndTerm,
    pattern ApplyTerm,
    pattern BVConcatTerm,
    pattern BVExtendTerm,
    pattern BVSelectTerm,
    pattern BitCastOrTerm,
    pattern BitCastTerm,
    pattern ComplementBitsTerm,
    pattern ConTerm,
    pattern DistinctTerm,
    pattern DivIntegralTerm,
    pattern EqTerm,
    pattern ExistsTerm,
    pattern FPBinaryTerm,
    pattern FPFMATerm,
    pattern FPRoundingBinaryTerm,
    pattern FPRoundingUnaryTerm,
    pattern FPTraitTerm,
    pattern FPUnaryTerm,
    pattern FdivTerm,
    pattern FloatingUnaryTerm,
    pattern ForallTerm,
    pattern FromFPOrTerm,
    pattern FromIntegralTerm,
    pattern ITETerm,
    pattern LeOrdTerm,
    pattern LtOrdTerm,
    pattern ModIntegralTerm,
    pattern MulNumTerm,
    pattern NegNumTerm,
    pattern NotTerm,
    pattern OrBitsTerm,
    pattern OrTerm,
    pattern PowerTerm,
    pattern QuotIntegralTerm,
    pattern RecipTerm,
    pattern RemIntegralTerm,
    pattern RotateLeftTerm,
    pattern RotateRightTerm,
    pattern ShiftLeftTerm,
    pattern ShiftRightTerm,
    pattern SignumNumTerm,
    pattern SupportedTypedSymbol,
    pattern SymTerm,
    pattern ToFPTerm,
    pattern XorBitsTerm,
    pattern SelectTerm,
    pattern StoreTerm,
    pattern ConstArrayTerm,
    pattern SeqConsTerm,
    pattern SeqAppendTerm,
    pattern SeqZipTerm,
    pattern SeqLengthTerm,
    pattern SeqRangeTerm,
    pattern SeqTailTerm,
    pattern SeqLookupTerm,
    pattern SeqLookupValueTerm,
    pattern SeqFoldTerm,
    pattern FocusedSeqFoldTerm,
    pattern SeqFoldWithTerm,
    pattern PairTerm,
    pattern FirstTerm,
    pattern SecondTerm,
  )

import Grisette.Internal.SymPrim.Prim.Pattern (pattern SubTerms)
import Grisette.Internal.SymPrim.Prim.SomeTerm (SomeTerm (SomeTerm), someTerm)
import Grisette.Internal.SymPrim.Prim.TermUtils (extractSymSomeTerm)
import Language.Haskell.TH.Syntax (Lift (liftTyped))
import Type.Reflection
  ( TypeRep,
    eqTypeRep,
    typeRep,
    pattern App,
    type (:~~:) (HRefl),
  )
import Unsafe.Coerce (unsafeCoerce)

-- $setup
-- >>> import Grisette.Core
-- >>> import Grisette.SymPrim

-- | General symbolic function type. Use the '#' operator to apply the function.
-- Note that this function should be applied to symbolic values only. It is by
-- itself already a symbolic value, but can be considered partially concrete
-- as the function body is specified. Use 'Grisette.SymPrim.SymPrim.-~>'
-- for uninterpreted general symbolic functions.
--
-- The result would be partially evaluated.
--
-- >>> let f = ("x" :: TypedConstantSymbol Integer) --> ("x" + 1 + "y" :: SymInteger) :: Integer --> Integer
-- >>> f # 1    -- 1 has the type SymInteger
-- (+ 2 y)
-- >>> f # "a"  -- "a" has the type SymInteger
-- (+ 1 (+ a y))
instance (LinkedRep a sa, LinkedRep b sb) => Function (a --> b) sa sb where
  (GeneralFun s t) # x = wrapTerm $ substTerm s (underlyingTerm x) HS.empty t

extractSymSomeTermIncludeBoundedVars ::
  SomeTerm -> HS.HashSet SomeTypedAnySymbol
extractSymSomeTermIncludeBoundedVars root =
  State.evalState (go root) HM.empty
  where
    -- The memo belongs to one extraction invocation. Every recursive edge uses
    -- it, preserving DAG sharing without retaining terms for the process lifetime.
    go
      :: SomeTerm
      -> State.State
          (HM.HashMap SomeTerm (HS.HashSet SomeTypedAnySymbol))
          (HS.HashSet SomeTypedAnySymbol)
    go term = do
      memo <- State.get
      case HM.lookup term memo of
        Just result -> pure result
        Nothing -> do
          result <- goUncached term
          result `seq` State.modify' (HM.insert term result)
          pure result

    goTyped :: Term a -> State.State
      (HM.HashMap SomeTerm (HS.HashSet SomeTypedAnySymbol))
      (HS.HashSet SomeTypedAnySymbol)
    goTyped = go . someTerm

    goUncached (SomeTerm (SymTerm (sym :: TypedAnySymbol a))) =
      pure $ HS.singleton $ someTypedSymbol sym
    goUncached (SomeTerm (ConTerm cv :: Term v)) =
      case (primTypeRep :: TypeRep v) of
        App (App gf _) _ ->
          case eqTypeRep (typeRep @(-->)) gf of
            Just HRefl ->
              case cv of
                GeneralFun (tsym :: TypedConstantSymbol x) tm -> do
                  body <- go (SomeTerm tm)
                  pure $ HS.insert
                    (someTypedSymbol $ fromJust $ castTypedSymbol tsym)
                    body
            Nothing -> pure HS.empty
        _ -> pure HS.empty
    goUncached (SomeTerm (ForallTerm sym arg)) =
      HS.insert (someTypedSymbol $ fromJust $ castTypedSymbol sym) <$> goTyped arg
    goUncached (SomeTerm (ExistsTerm sym arg)) =
      HS.insert (someTypedSymbol $ fromJust $ castTypedSymbol sym) <$> goTyped arg
    goUncached
        (SomeTerm (FocusedSeqFoldTerm callback operands initial sequence)) = do
      callbackSymbols <- goTyped (focusedSeqFoldCallbackTerm callback)
      operandSymbols <- goFocusedOperands operands
      initialSymbols <- goTyped initial
      sequenceSymbols <- goTyped sequence
      pure $
        focusedBinderSymbols callback
          <> callbackSymbols
          <> operandSymbols
          <> initialSymbols
          <> sequenceSymbols
    goUncached (SomeTerm (SubTerms tms)) = mconcat <$> traverse go tms

    focusedBinderSymbols
      :: FocusedSeqFoldCallback captures state element
      -> HS.HashSet SomeTypedAnySymbol
    focusedBinderSymbols (FocusedSeqFoldCallbackBody _) = HS.empty
    focusedBinderSymbols (FocusedSeqFoldCallbackBind symbol rest) =
      HS.insert
        (someTypedSymbol $ fromJust $ castTypedSymbol symbol)
        (focusedBinderSymbols rest)

    goFocusedOperands
      :: FocusedSeqFoldOperands captures
      -> State.State
          (HM.HashMap SomeTerm (HS.HashSet SomeTypedAnySymbol))
          (HS.HashSet SomeTypedAnySymbol)
    goFocusedOperands NoFocusedSeqFoldOperands = pure HS.empty
    goFocusedOperands (FocusedSeqFoldOperand operand rest) =
      (<>) <$> goTyped operand <*> goFocusedOperands rest

validateClosedSeqFold ::
  (HasCallStack, SupportedPrim function) =>
  Term function ->
  Term function
validateClosedSeqFold function =
  either error id (checkClosedSeqFold function)

validateClosedSeqFoldWith ::
  (HasCallStack, SupportedPrim function) =>
  Term function ->
  Term function
validateClosedSeqFoldWith function =
  either error id (checkClosedSeqFoldWith function)

checkClosedSeqFold ::
  SupportedPrim function =>
  Term function ->
  Either String (Term function)
checkClosedSeqFold = checkClosedSequenceFunction "foldSeq"

checkClosedSeqFoldWith ::
  SupportedPrim function =>
  Term function ->
  Either String (Term function)
checkClosedSeqFoldWith = checkClosedSequenceFunction "foldSeqWith"

validateClosedFocusedSeqFold ::
  ( HasCallStack,
    SupportedNonFuncPrim state,
    SupportedNonFuncPrim element,
    SupportedPrim (state --> element --> state)
  ) =>
  FocusedSeqFoldCallback captures state element ->
  FocusedSeqFoldCallback captures state element
validateClosedFocusedSeqFold callback =
  either error id (checkClosedFocusedSeqFold callback)

checkClosedFocusedSeqFold ::
  ( SupportedNonFuncPrim state,
    SupportedNonFuncPrim element,
    SupportedPrim (state --> element --> state)
  ) =>
  FocusedSeqFoldCallback captures state element ->
  Either String (FocusedSeqFoldCallback captures state element)
checkClosedFocusedSeqFold callback
  | hasDuplicateBinders =
      Left "focusedFold step function has duplicate capture binders"
  | otherwise =
      case extractSymSomeTerm @'AnyKind bounded
        (SomeTerm (focusedSeqFoldCallbackTerm callback)) of
        Nothing ->
          Left "BUG: focusedFold could not classify symbols in its step function"
        Just symbols ->
          case sortOn show (mapMaybe toCaptured (HS.toList symbols)) of
            [] -> Right callback
            captured ->
              Left $ "focusedFold step function captures solver values: "
                ++ unwords (show <$> captured)
  where
    binders = focusedCallbackBinders callback
    bounded = HS.fromList binders
    hasDuplicateBinders = HS.size bounded /= length binders
    toCaptured symbol = castSomeTypedSymbol @'ConstantKind symbol

    focusedCallbackBinders
      :: FocusedSeqFoldCallback cs s e -> [SomeTypedConstantSymbol]
    focusedCallbackBinders (FocusedSeqFoldCallbackBody _) = []
    focusedCallbackBinders (FocusedSeqFoldCallbackBind symbol rest) =
      someTypedSymbol symbol : focusedCallbackBinders rest

pevalClosedSeqFold ::
  ( HasCallStack,
    SupportedNonFuncPrim state,
    SupportedNonFuncPrim element,
    SupportedPrim (state --> element --> state)
  ) =>
  Term (state --> element --> state) ->
  Term state ->
  Term [element] ->
  Term state
pevalClosedSeqFold step initial sequence =
  let checked = validateClosedSeqFold step
   in checked `seq` pevalPreparedSeqFold checked initial sequence

pevalClosedSeqFoldWith ::
  forall environment state element.
  ( HasCallStack,
    SupportedNonFuncPrim environment,
    SupportedNonFuncPrim state,
    SupportedNonFuncPrim element,
    SupportedPrim (environment --> state --> element --> state)
  ) =>
  Term (environment --> state --> element --> state) ->
  Term environment ->
  Term state ->
  Term [element] ->
  Term state
pevalClosedSeqFoldWith step environment initial sequence =
  let checked = validateClosedSeqFoldWith step
   in checked `seq`
        pevalPreparedSeqFoldWith checked environment initial sequence

-- | Apply an already-validated closed sequence step.  The constructor for a
-- prepared public fold is private to 'SymSeq', so this internal operation can
-- omit the otherwise linear free-symbol traversal without admitting an
-- unchecked function term.
pevalPreparedSeqFold ::
  ( SupportedNonFuncPrim state,
    SupportedNonFuncPrim element,
    SupportedPrim (state --> element --> state)
  ) =>
  Term (state --> element --> state) ->
  Term state ->
  Term [element] ->
  Term state
pevalPreparedSeqFold checked initial sequence = case sequence of
  ConTerm elements -> foldConcreteSequence checked initial elements
  _ -> pevalSeqFoldTerm checked initial sequence

pevalPreparedFocusedSeqFold ::
  ( SupportedNonFuncPrim state,
    SupportedNonFuncPrim element,
    SupportedPrim (state --> element --> state)
  ) =>
  FocusedSeqFoldCallback captures state element ->
  FocusedSeqFoldOperands captures ->
  Term state ->
  Term [element] ->
  Term state
pevalPreparedFocusedSeqFold callback operands initial sequence = case sequence of
  ConTerm elements ->
    foldConcreteSequence (applyFocusedCallback callback operands) initial elements
  _ -> pevalFocusedSeqFoldTerm callback operands initial sequence
  where
    applyFocusedCallback
      :: FocusedSeqFoldCallback cs state element
      -> FocusedSeqFoldOperands cs
      -> Term (state --> element --> state)
    applyFocusedCallback (FocusedSeqFoldCallbackBody step)
        NoFocusedSeqFoldOperands = step
    applyFocusedCallback (FocusedSeqFoldCallbackBind symbol rest)
        (FocusedSeqFoldOperand operand operands') =
      let introduced = extractSymSomeTermIncludeBoundedVars (SomeTerm operand)
          captureSafeRest = avoidFocusedBinders introduced rest
       in applyFocusedCallback
            (mapFocusedSeqFoldCallbackTerm
              (substTerm symbol operand HS.empty) captureSafeRest)
            operands'

    avoidFocusedBinders
      :: HS.HashSet SomeTypedAnySymbol
      -> FocusedSeqFoldCallback cs state element
      -> FocusedSeqFoldCallback cs state element
    avoidFocusedBinders _ callback@FocusedSeqFoldCallbackBody {} = callback
    avoidFocusedBinders introduced
        (FocusedSeqFoldCallbackBind
          (symbol :: TypedConstantSymbol capture) rest) =
      let symbolAny = someTypedSymbol $
            fromJust
              (castTypedSymbol symbol :: Maybe (TypedAnySymbol capture))
          (renamedSymbol, renamedRest) =
            if HS.member symbolAny introduced
              then
                let fresh = freshArgSymbolAvoiding introduced
                      [SomeTerm (focusedSeqFoldCallbackTerm rest)]
                 in ( fresh,
                      mapFocusedSeqFoldCallbackTerm
                        (substTerm symbol (symTerm fresh) HS.empty) rest
                    )
              else (symbol, rest)
       in FocusedSeqFoldCallbackBind renamedSymbol
            (avoidFocusedBinders introduced renamedRest)

-- | 'pevalPreparedSeqFold' for a step with an explicit environment.
pevalPreparedSeqFoldWith ::
  forall environment state element.
  ( SupportedNonFuncPrim environment,
    SupportedNonFuncPrim state,
    SupportedNonFuncPrim element,
    SupportedPrim (environment --> state --> element --> state)
  ) =>
  Term (environment --> state --> element --> state) ->
  Term environment ->
  Term state ->
  Term [element] ->
  Term state
pevalPreparedSeqFoldWith checked environment initial sequence = case sequence of
  ConTerm elements ->
    withPrim @(environment --> state --> element --> state) $
      foldConcreteSequence
        (pevalApplyTerm checked environment)
        initial
        elements
  _ -> pevalSeqFoldWithTerm checked environment initial sequence

foldConcreteSequence ::
  forall state element.
  ( SupportedNonFuncPrim state,
    SupportedNonFuncPrim element,
    SupportedPrim (state --> element --> state)
  ) =>
  Term (state --> element --> state) ->
  Term state ->
  [element] ->
  Term state
foldConcreteSequence step =
  withPrim @(state --> element --> state) $
    foldl'
      (\state element ->
        pevalApplyTerm (pevalApplyTerm step state) (conTerm element)
      )

checkClosedSequenceFunction ::
  forall function.
  SupportedPrim function =>
  String ->
  Term function ->
  Either String (Term function)
checkClosedSequenceFunction operation function =
  case extractSymSomeTerm @'AnyKind HS.empty (SomeTerm function) of
    Nothing ->
      Left $
        "BUG: "
          ++ operation
          ++ " could not classify symbols in its step function"
    Just symbols ->
      case sortOn show (mapMaybe toCaptured (HS.toList symbols)) of
        [] -> Right function
        captured ->
          Left $
            operation
              ++ " step function captures solver values: "
              ++ unwords (show <$> captured)
  where
    toCaptured symbol = castSomeTypedSymbol @'ConstantKind symbol

-- | Generate a fresh argument symbol that is not used as bounded or unbounded
-- variables in the function body for a general symbolic function.
freshArgSymbol ::
  forall a. (SupportedNonFuncPrim a) => [SomeTerm] -> TypedConstantSymbol a
freshArgSymbol = freshArgSymbolAvoiding HS.empty

-- | 'freshArgSymbol' that also avoids an explicit symbol set.  Substitution uses
-- it to rename a binder away from the symbols the substitution introduces.
freshArgSymbolAvoiding ::
  forall a.
  (SupportedNonFuncPrim a) =>
  HS.HashSet SomeTypedAnySymbol ->
  [SomeTerm] ->
  TypedConstantSymbol a
freshArgSymbolAvoiding avoided terms = typedConstantSymbol $ go 0
  where
    allSymbols =
      HS.union avoided $
        mconcat $
          extractSymSomeTermIncludeBoundedVars <$> terms
    go :: Int -> Symbol
    go n =
      let currentSymbol = BoundSymbol "arg" n
          currentTypedSymbol =
            someTypedSymbol (typedAnySymbol currentSymbol :: TypedAnySymbol a)
       in if HS.member currentTypedSymbol allSymbols
            then go (n + 1)
            else currentSymbol

-- | Generate a fresh argument symbol from an already collected symbol set.
-- Multi-argument abstraction uses this helper so a hash-consed body is walked
-- once, rather than once for every nested binder.
freshArgSymbolFromSymbols ::
  forall a.
  (SupportedNonFuncPrim a) =>
  HS.HashSet SomeTypedAnySymbol ->
  TypedConstantSymbol a
freshArgSymbolFromSymbols allSymbols = typedConstantSymbol $ go 0
  where
    go :: Int -> Symbol
    go n =
      let currentSymbol = BoundSymbol "arg" n
          currentTypedSymbol =
            someTypedSymbol (typedAnySymbol currentSymbol :: TypedAnySymbol a)
       in if HS.member currentTypedSymbol allSymbols
            then go (n + 1)
            else currentSymbol

-- | Build a general symbolic function with a bounded symbol and a term.
buildGeneralFun ::
  forall a b.
  (SupportedNonFuncPrim a, SupportedPrim b) =>
  TypedConstantSymbol a ->
  Term b ->
  a --> b
buildGeneralFun arg v =
  GeneralFun
    argSymbol
    (substTerm arg (symTerm argSymbol) HS.empty v)
  where
    argSymbol = freshArgSymbol [SomeTerm v]

-- | Build a two-argument general function with one body scan and one
-- capture-avoiding substitution.  This is extensionally identical to two
-- nested 'buildGeneralFun' calls.  Choosing the innermost binder first retains
-- the same alpha-normal form and therefore the same interning opportunities.
buildGeneralFun2 ::
  forall a b c.
  ( SupportedNonFuncPrim a,
    SupportedNonFuncPrim b,
    SupportedPrim c,
    SupportedPrim (b --> c)
  ) =>
  TypedConstantSymbol a ->
  TypedConstantSymbol b ->
  Term c ->
  a --> b --> c
buildGeneralFun2 first second body =
  GeneralFun firstArgument $
    conTerm $ GeneralFun secondArgument renamedBody
  where
    bodySymbols = extractSymSomeTermIncludeBoundedVars (SomeTerm body)
    secondArgument = freshArgSymbolFromSymbols bodySymbols
    secondArgumentSymbol =
      someTypedSymbol $
        fromJust (castTypedSymbol secondArgument :: Maybe (TypedAnySymbol b))
    firstArgument =
      freshArgSymbolFromSymbols (HS.insert secondArgumentSymbol bodySymbols)
    firstArgumentSymbol =
      someTypedSymbol $
        fromJust (castTypedSymbol firstArgument :: Maybe (TypedAnySymbol a))
    introduced = HS.fromList [firstArgumentSymbol, secondArgumentSymbol]
    renamedBody =
      generalSubstSomeTerm replace introduced HS.empty body
    replace :: forall value. TypedSymbol 'AnyKind value -> Term value
    replace symbol
      | eqHeteroSymbol second symbol =
          unsafeCoerce (symTerm secondArgument)
      | eqHeteroSymbol first symbol =
          unsafeCoerce (symTerm firstArgument)
      | otherwise = symTerm symbol

-- | Build a three-argument general function with one body scan and one
-- capture-avoiding substitution.  Solver-native folds with an explicit
-- environment use this shape; avoiding three complete walks is material for
-- large, shared fold bodies while preserving their exact function term.
buildGeneralFun3 ::
  forall a b c d.
  ( SupportedNonFuncPrim a,
    SupportedNonFuncPrim b,
    SupportedNonFuncPrim c,
    SupportedPrim d,
    SupportedPrim (c --> d),
    SupportedPrim (b --> c --> d)
  ) =>
  TypedConstantSymbol a ->
  TypedConstantSymbol b ->
  TypedConstantSymbol c ->
  Term d ->
  a --> b --> c --> d
buildGeneralFun3 first second third body =
  GeneralFun firstArgument $
    conTerm $
      GeneralFun secondArgument $
        conTerm $ GeneralFun thirdArgument renamedBody
  where
    bodySymbols = extractSymSomeTermIncludeBoundedVars (SomeTerm body)
    thirdArgument = freshArgSymbolFromSymbols bodySymbols
    thirdArgumentSymbol =
      someTypedSymbol $
        fromJust (castTypedSymbol thirdArgument :: Maybe (TypedAnySymbol c))
    secondArgument =
      freshArgSymbolFromSymbols (HS.insert thirdArgumentSymbol bodySymbols)
    secondArgumentSymbol =
      someTypedSymbol $
        fromJust (castTypedSymbol secondArgument :: Maybe (TypedAnySymbol b))
    firstArgument = freshArgSymbolFromSymbols $
      HS.insert secondArgumentSymbol $
        HS.insert thirdArgumentSymbol bodySymbols
    firstArgumentSymbol =
      someTypedSymbol $
        fromJust (castTypedSymbol firstArgument :: Maybe (TypedAnySymbol a))
    introduced = HS.fromList
      [firstArgumentSymbol, secondArgumentSymbol, thirdArgumentSymbol]
    renamedBody =
      generalSubstSomeTerm replace introduced HS.empty body
    replace :: forall value. TypedSymbol 'AnyKind value -> Term value
    replace symbol
      | eqHeteroSymbol third symbol =
          unsafeCoerce (symTerm thirdArgument)
      | eqHeteroSymbol second symbol =
          unsafeCoerce (symTerm secondArgument)
      | eqHeteroSymbol first symbol =
          unsafeCoerce (symTerm firstArgument)
      | otherwise = symTerm symbol

data FocusedBinderRenamings captures where
  NoFocusedBinderRenamings :: FocusedBinderRenamings '[]
  FocusedBinderRenaming ::
    SupportedNonFuncPrim capture =>
    !(TypedConstantSymbol capture) ->
    !(TypedConstantSymbol capture) ->
    !(FocusedBinderRenamings rest) ->
    FocusedBinderRenamings (capture ': rest)

-- | Abstract every capture, state, and element binder with one symbol scan and
-- one capture-avoiding substitution traversal.
buildFocusedGeneralFun ::
  forall captures state element.
  ( SupportedNonFuncPrim state,
    SupportedNonFuncPrim element,
    SupportedPrim (element --> state),
    SupportedPrim (state --> element --> state)
  ) =>
  FocusedSeqFoldBinderSymbols captures ->
  TypedConstantSymbol state ->
  TypedConstantSymbol element ->
  Term state ->
  FocusedSeqFoldCallback captures state element
buildFocusedGeneralFun captureSymbols stateSymbol elementSymbol body =
  buildCallback renamings step
  where
    bodySymbols = extractSymSomeTermIncludeBoundedVars (SomeTerm body)
    elementArgument = freshArgSymbolFromSymbols bodySymbols
    elementAny = toAny elementArgument
    stateArgument = freshArgSymbolFromSymbols (HS.insert elementAny bodySymbols)
    stateAny = toAny stateArgument
    (renamings, allSymbols) =
      freshenCaptureSymbols captureSymbols
        (HS.insert stateAny (HS.insert elementAny bodySymbols))
    introduced = HS.difference allSymbols bodySymbols
    renamedBody = generalSubstSomeTerm replace introduced HS.empty body
    step = conTerm $ GeneralFun stateArgument $
      conTerm $ GeneralFun elementArgument renamedBody

    toAny :: forall value. SupportedNonFuncPrim value
      => TypedConstantSymbol value -> SomeTypedAnySymbol
    toAny symbol = someTypedSymbol $
      fromJust (castTypedSymbol symbol :: Maybe (TypedAnySymbol value))

    freshenCaptureSymbols
      :: FocusedSeqFoldBinderSymbols cs
      -> HS.HashSet SomeTypedAnySymbol
      -> (FocusedBinderRenamings cs, HS.HashSet SomeTypedAnySymbol)
    freshenCaptureSymbols NoFocusedSeqFoldBinderSymbols symbols =
      (NoFocusedBinderRenamings, symbols)
    freshenCaptureSymbols (FocusedSeqFoldBinderSymbol old rest) symbols =
      let (renamedRest, restSymbols) = freshenCaptureSymbols rest symbols
          new = freshArgSymbolFromSymbols restSymbols
       in ( FocusedBinderRenaming old new renamedRest,
            HS.insert (toAny new) restSymbols
          )

    replace :: forall value. TypedSymbol 'AnyKind value -> Term value
    replace symbol
      | eqHeteroSymbol elementSymbol symbol =
          unsafeCoerce (symTerm elementArgument)
      | eqHeteroSymbol stateSymbol symbol =
          unsafeCoerce (symTerm stateArgument)
      | otherwise = replaceCapture renamings symbol

    replaceCapture
      :: forall cs value.
         FocusedBinderRenamings cs
      -> TypedSymbol 'AnyKind value
      -> Term value
    replaceCapture NoFocusedBinderRenamings symbol = symTerm symbol
    replaceCapture (FocusedBinderRenaming old new rest) symbol
      | eqHeteroSymbol old symbol = unsafeCoerce (symTerm new)
      | otherwise = replaceCapture rest symbol

    buildCallback
      :: FocusedBinderRenamings cs
      -> Term (state --> element --> state)
      -> FocusedSeqFoldCallback cs state element
    buildCallback NoFocusedBinderRenamings finalStep =
      FocusedSeqFoldCallbackBody finalStep
    buildCallback (FocusedBinderRenaming _ new rest) finalStep =
      FocusedSeqFoldCallbackBind new (buildCallback rest finalStep)

-- | Checks if two formulas are the same. Not building the actual symbolic
-- equality formula.
--
-- The reason why we choose this behavior is to allow symbolic variables to be
-- used as keys in hash maps, which can be useful for memoization.
--
-- Use with caution. Usually you should use t'Grisette.Core.SymEq' instead.
instance Eq (a --> b) where
  GeneralFun sym1 tm1 == GeneralFun sym2 tm2 = sym1 == sym2 && tm1 == tm2

instance Show (a --> b) where
  show (GeneralFun sym tm) = "\\(" ++ show sym ++ ") -> " ++ pformatTerm tm

instance Lift (a --> b) where
  liftTyped (GeneralFun sym tm) = [||GeneralFun sym tm||]

instance Hashable (a --> b) where
  s `hashWithSalt` (GeneralFun sym tm) = s `hashWithSalt` sym `hashWithSalt` tm

instance NFData (a --> b) where
  rnf (GeneralFun sym tm) = rnf sym `seq` rnf tm

instance
  (SupportedNonFuncPrim a, SupportedPrim b) =>
  SupportedPrimConstraint (a --> b)
  where
  type
    PrimConstraint (a --> b) =
      ( SupportedNonFuncPrim a,
        SupportedPrim b,
        NonFuncPrimConstraint a,
        PrimConstraint b,
        SBVType (a --> b) ~ (SBV.SBV (NonFuncSBVBaseType a) -> SBVType b)
      )

instance
  (SupportedNonFuncPrim a, SupportedPrim b) =>
  SBVRep (a --> b)
  where
  type
    SBVType (a --> b) =
      SBV.SBV (NonFuncSBVBaseType a) ->
      SBVType b

instance (Apply st, LinkedRep ca sa, LinkedRep ct st) => Apply (ca --> ct) where
  type FunType (ca --> ct) = SymType ca -> FunType (SymType ct)
  apply uf a = apply (uf # a)

pevalGeneralFunApplyTerm ::
  ( SupportedNonFuncPrim a,
    SupportedPrim b,
    SupportedPrim (a --> b)
  ) =>
  Term (a --> b) ->
  Term a ->
  Term b
pevalGeneralFunApplyTerm = totalize2 doPevalApplyTerm applyTerm
  where
    doPevalApplyTerm (ConTerm (GeneralFun arg tm)) v =
      Just $ substTerm arg v HS.empty tm
    doPevalApplyTerm (ITETerm c l r) v =
      return $ pevalITETerm c (pevalApplyTerm l v) (pevalApplyTerm r v)
    doPevalApplyTerm _ _ = Nothing

instance
  ( SupportedPrim (a --> b),
    SupportedNonFuncPrim a,
    SupportedPrim b
  ) =>
  PEvalApplyTerm (a --> b) a b
  where
  pevalApplyTerm = pevalGeneralFunApplyTerm
  sbvApplyTerm f a =
    withPrim @(a --> b) $ withNonFuncPrim @a $ f a

parseGeneralFunSMTModelResult ::
  forall a b.
  (SupportedNonFuncPrim a, SupportedPrim b) =>
  Int ->
  ([([SBVD.CV], SBVD.CV)], SBVD.CV) ->
  a --> b
parseGeneralFunSMTModelResult level (l, s) =
  let sym = typedConstantSymbol $ BoundSymbol "arg" level
      funs =
        second
          ( \r ->
              case r of
                [([], v)] -> parseSMTModelResult (level + 1) ([], v)
                _ -> parseSMTModelResult (level + 1) (r, s)
          )
          <$> partitionCVArg @a l
      def = parseSMTModelResult (level + 1) ([], s)
      body =
        foldl'
          ( \acc (v, f) ->
              pevalITETerm
                (pevalEqTerm (symTerm sym) (conTerm v))
                (conTerm f)
                acc
          )
          (conTerm def)
          funs
   in buildGeneralFun sym body

{-# NOINLINE generalSubstSomeTerm #-}
-- | General procedure for substituting symbols in a term.
--
-- The second argument is every symbol the substitution can introduce.  A binder
-- whose symbol is in that set is renamed before the substitution descends under
-- it, so a replacement term is never captured: substituting @w := arg\@1@ into
-- @\\arg\@1. arg\@1 + w@ denotes @\\z. z + arg\@1@, not @\\z. z + z@.  Callers that
-- introduce nothing (model evaluation replaces symbols with concrete values)
-- pass an empty set and pay nothing.
generalSubstSomeTerm ::
  forall v.
  (forall a. TypedSymbol 'AnyKind a -> Term a) ->
  HS.HashSet SomeTypedAnySymbol ->
  HS.HashSet SomeTypedConstantSymbol ->
  Term v ->
  Term v
generalSubstSomeTerm subst introducedSymbols initialBoundedSymbols = go initialMemo
  where
    -- Rename a binder that the substitution would otherwise capture.  The
    -- replacement name avoids everything the body mentions, bound occurrences
    -- included, so renaming it in cannot capture anything either.  A symbol whose
    -- kind cast fails is renamed rather than skipped: renaming is always sound,
    -- skipping would not be.
    avoidCapture ::
      forall a b.
      (SupportedPrim b) =>
      TypedConstantSymbol a ->
      Term b ->
      (TypedConstantSymbol a, Term b)
    avoidCapture sym@SupportedTypedSymbol body
      | collides =
          let renamed = freshArgSymbolAvoiding introducedSymbols [SomeTerm body]
           in (renamed, substTerm sym (symTerm renamed) HS.empty body)
      | otherwise = (sym, body)
      where
        collides =
          maybe
            True
            (\anySymbol -> HS.member (someTypedSymbol (anySymbol :: TypedAnySymbol a)) introducedSymbols)
            (castTypedSymbol sym)
    go :: forall a. (SomeTerm -> SomeTerm) -> Term a -> Term a
    go memo a = case memo $ someTerm a of
      SomeTerm v -> unsafeCoerce v
    initialMemo :: SomeTerm -> SomeTerm
    initialMemo = htmemo (goSome initialMemo initialBoundedSymbols)
    {-# NOINLINE initialMemo #-}
    goSome ::
      (SomeTerm -> SomeTerm) ->
      HS.HashSet SomeTypedConstantSymbol ->
      SomeTerm ->
      SomeTerm
    goSome _ bs c@(SomeTerm (ConTerm cv :: Term x)) =
      case (primTypeRep :: TypeRep x) of
        App (App gf _) _ ->
          case eqTypeRep gf (typeRep @(-->)) of
            Just HRefl -> case cv of
              GeneralFun sym (tm :: Term r) ->
                let (sym', tm') = avoidCapture sym tm
                    newmemo =
                      htmemo
                        ( goSome
                            newmemo
                            (HS.union (HS.singleton (someTypedSymbol sym')) bs)
                        )
                    {-# NOINLINE newmemo #-}
                 in SomeTerm $ conTerm $ GeneralFun sym' (go newmemo tm')
            Nothing -> c
        _ -> c
    goSome _ bs c@(SomeTerm ((SymTerm sym) :: Term a)) =
      case castTypedSymbol sym of
        Just sym' | HS.member (someTypedSymbol sym') bs -> c
        _ -> SomeTerm $ subst sym
    goSome _ bs (SomeTerm (ForallTerm tsym b)) =
      let (tsym', b') = avoidCapture tsym b
          newmemo =
            htmemo (goSome newmemo (HS.insert (someTypedSymbol tsym') bs))
          {-# NOINLINE newmemo #-}
       in goUnary newmemo (forallTerm tsym') b'
    goSome _ bs (SomeTerm (ExistsTerm tsym b)) =
      let (tsym', b') = avoidCapture tsym b
          newmemo =
            htmemo (goSome newmemo (HS.insert (someTypedSymbol tsym') bs))
          {-# NOINLINE newmemo #-}
       in goUnary newmemo (existsTerm tsym') b'
    goSome memo _ (SomeTerm (NotTerm arg)) =
      goUnary memo pevalNotTerm arg
    goSome memo _ (SomeTerm (OrTerm arg1 arg2)) =
      goBinary memo pevalOrTerm arg1 arg2
    goSome memo _ (SomeTerm (AndTerm arg1 arg2)) =
      goBinary memo pevalAndTerm arg1 arg2
    goSome memo _ (SomeTerm (EqTerm arg1 arg2)) =
      goBinary memo pevalEqTerm arg1 arg2
    goSome memo _ (SomeTerm (DistinctTerm args)) =
      SomeTerm $ pevalDistinctTerm (fmap (go memo) args)
    goSome memo _ (SomeTerm (ITETerm cond arg1 arg2)) =
      goTernary memo pevalITETerm cond arg1 arg2
    goSome memo _ (SomeTerm (AddNumTerm arg1 arg2)) =
      goBinary memo pevalAddNumTerm arg1 arg2
    goSome memo _ (SomeTerm (NegNumTerm arg)) =
      goUnary memo pevalNegNumTerm arg
    goSome memo _ (SomeTerm (MulNumTerm arg1 arg2)) =
      goBinary memo pevalMulNumTerm arg1 arg2
    goSome memo _ (SomeTerm (AbsNumTerm arg)) =
      goUnary memo pevalAbsNumTerm arg
    goSome memo _ (SomeTerm (SignumNumTerm arg)) =
      goUnary memo pevalSignumNumTerm arg
    goSome memo _ (SomeTerm (LtOrdTerm arg1 arg2)) =
      goBinary memo pevalLtOrdTerm arg1 arg2
    goSome memo _ (SomeTerm (LeOrdTerm arg1 arg2)) =
      goBinary memo pevalLeOrdTerm arg1 arg2
    goSome memo _ (SomeTerm (AndBitsTerm arg1 arg2)) =
      goBinary memo pevalAndBitsTerm arg1 arg2
    goSome memo _ (SomeTerm (OrBitsTerm arg1 arg2)) =
      goBinary memo pevalOrBitsTerm arg1 arg2
    goSome memo _ (SomeTerm (XorBitsTerm arg1 arg2)) =
      goBinary memo pevalXorBitsTerm arg1 arg2
    goSome memo _ (SomeTerm (ComplementBitsTerm arg)) =
      goUnary memo pevalComplementBitsTerm arg
    goSome memo _ (SomeTerm (ShiftLeftTerm arg n)) =
      goBinary memo pevalShiftLeftTerm arg n
    goSome memo _ (SomeTerm (RotateLeftTerm arg n)) =
      goBinary memo pevalRotateLeftTerm arg n
    goSome memo _ (SomeTerm (ShiftRightTerm arg n)) =
      goBinary memo pevalShiftRightTerm arg n
    goSome memo _ (SomeTerm (RotateRightTerm arg n)) =
      goBinary memo pevalRotateRightTerm arg n
    goSome memo _ (SomeTerm (BitCastTerm (arg :: Term a) :: Term r)) =
      goUnary memo (pevalBitCastTerm @a @r) arg
    goSome memo _ (SomeTerm (BitCastOrTerm (d :: term r) (arg :: Term a) :: Term r)) =
      goBinary memo (pevalBitCastOrTerm @a @r) d arg
    goSome memo _ (SomeTerm (BVConcatTerm arg1 arg2)) =
      goBinary memo pevalBVConcatTerm arg1 arg2
    goSome memo _ (SomeTerm (BVSelectTerm ix w arg)) =
      goUnary memo (pevalBVSelectTerm ix w) arg
    goSome memo _ (SomeTerm (BVExtendTerm n signed arg)) =
      goUnary memo (pevalBVExtendTerm n signed) arg
    goSome memo _ (SomeTerm (ApplyTerm f arg)) =
      goBinary memo pevalApplyTerm f arg
    goSome memo _ (SomeTerm (DivIntegralTerm arg1 arg2)) =
      goBinary memo pevalDivIntegralTerm arg1 arg2
    goSome memo _ (SomeTerm (ModIntegralTerm arg1 arg2)) =
      goBinary memo pevalModIntegralTerm arg1 arg2
    goSome memo _ (SomeTerm (QuotIntegralTerm arg1 arg2)) =
      goBinary memo pevalQuotIntegralTerm arg1 arg2
    goSome memo _ (SomeTerm (RemIntegralTerm arg1 arg2)) =
      goBinary memo pevalRemIntegralTerm arg1 arg2
    goSome memo _ (SomeTerm (FPTraitTerm trait arg)) =
      goUnary memo (pevalFPTraitTerm trait) arg
    goSome memo _ (SomeTerm (FdivTerm arg1 arg2)) =
      goBinary memo pevalFdivTerm arg1 arg2
    goSome memo _ (SomeTerm (RecipTerm arg)) =
      goUnary memo pevalRecipTerm arg
    goSome memo _ (SomeTerm (FloatingUnaryTerm op arg)) =
      goUnary memo (pevalFloatingUnaryTerm op) arg
    goSome memo _ (SomeTerm (PowerTerm arg1 arg2)) =
      goBinary memo pevalPowerTerm arg1 arg2
    goSome memo _ (SomeTerm (FPUnaryTerm op arg)) =
      goUnary memo (pevalFPUnaryTerm op) arg
    goSome memo _ (SomeTerm (FPBinaryTerm op arg1 arg2)) =
      goBinary memo (pevalFPBinaryTerm op) arg1 arg2
    goSome memo _ (SomeTerm (FPRoundingUnaryTerm op mode arg)) =
      goUnary memo (pevalFPRoundingUnaryTerm op mode) arg
    goSome memo _ (SomeTerm (FPRoundingBinaryTerm op mode arg1 arg2)) =
      goBinary memo (pevalFPRoundingBinaryTerm op mode) arg1 arg2
    goSome memo _ (SomeTerm (FPFMATerm mode arg1 arg2 arg3)) =
      SomeTerm $
        pevalFPFMATerm
          (go memo mode)
          (go memo arg1)
          (go memo arg2)
          (go memo arg3)
    goSome memo _ (SomeTerm (FromIntegralTerm (arg :: Term a) :: Term b)) =
      goUnary memo (pevalFromIntegralTerm @a @b) arg
    goSome memo _ (SomeTerm (FromFPOrTerm d mode arg)) =
      goTernary memo pevalFromFPOrTerm d mode arg
    goSome
      memo
      _
      (SomeTerm (ToFPTerm mode (arg :: Term a) (_ :: p eb) (_ :: q sb))) =
        goBinary memo (pevalToFPTerm @a @eb @sb) mode arg
    goSome  memo _ (SomeTerm (SelectTerm arr key)) =
      goBinary memo pevalSelectTerm arr key
    goSome  memo _ (SomeTerm (StoreTerm arr key val)) =
      goTernary memo pevalStoreTerm arr key val
    goSome  memo _ (SomeTerm (ConstArrayTerm pkey val)) =
      goUnary memo (pevalConstArrayTerm pkey) val
    goSome memo _ (SomeTerm (SeqConsTerm element sequence)) =
      goBinary memo pevalSeqConsTerm element sequence
    goSome memo _ (SomeTerm (SeqAppendTerm left right)) =
      goBinary memo pevalSeqAppendTerm left right
    goSome memo _ (SomeTerm (SeqZipTerm left right)) =
      goBinary memo pevalSeqZipTerm left right
    goSome memo _ (SomeTerm (SeqLengthTerm sequence)) =
      goUnary memo pevalSeqLengthTerm sequence
    goSome memo _ (SomeTerm (SeqRangeTerm extent)) =
      goUnary memo pevalSeqRangeTerm extent
    goSome memo _ (SomeTerm (SeqTailTerm sequence)) =
      goUnary memo pevalSeqTailTerm sequence
    goSome memo _ (SomeTerm (SeqLookupTerm seed sequence index)) =
      goTernary memo pevalSeqLookupTerm seed sequence index
    goSome memo _ (SomeTerm (SeqLookupValueTerm seed sequence index)) =
      goTernary memo pevalSeqLookupValueTerm seed sequence index
    goSome memo _ (SomeTerm (SeqFoldTerm step initial sequence)) =
      let folded =
            pevalClosedSeqFold
              (go memo step)
              (go memo initial)
              (go memo sequence)
       in folded `seq` SomeTerm folded
    goSome memo bs
        (SomeTerm (FocusedSeqFoldTerm callback operands initial sequence)) =
      let (callback', callbackBounded) = goFocusedCallback memo bs callback
          operands' = goFocusedOperands memo operands
          rebuilt = pevalPreparedFocusedSeqFold
            callback' operands' (go memo initial) (go memo sequence)
       in callbackBounded `seq` SomeTerm rebuilt
      where
        goFocusedCallback
          :: (SomeTerm -> SomeTerm)
          -> HS.HashSet SomeTypedConstantSymbol
          -> FocusedSeqFoldCallback cs state element
          -> ( FocusedSeqFoldCallback cs state element,
               HS.HashSet SomeTypedConstantSymbol )
        goFocusedCallback currentMemo bounded
            (FocusedSeqFoldCallbackBody step) =
          (FocusedSeqFoldCallbackBody (go currentMemo step), bounded)
        goFocusedCallback _ bounded
            (FocusedSeqFoldCallbackBind symbol rest) =
          let body = focusedSeqFoldCallbackTerm rest
              (symbol', renamedBody) = avoidCapture symbol body
              rest' = mapFocusedSeqFoldCallbackTerm (const renamedBody) rest
              bounded' = HS.insert (someTypedSymbol symbol') bounded
              newMemo = htmemo (goSome newMemo bounded')
              {-# NOINLINE newMemo #-}
              (traversed, finalBounded) =
                goFocusedCallback newMemo bounded' rest'
           in (FocusedSeqFoldCallbackBind symbol' traversed, finalBounded)

        goFocusedOperands
          :: (SomeTerm -> SomeTerm)
          -> FocusedSeqFoldOperands cs
          -> FocusedSeqFoldOperands cs
        goFocusedOperands _ NoFocusedSeqFoldOperands = NoFocusedSeqFoldOperands
        goFocusedOperands currentMemo (FocusedSeqFoldOperand operand rest) =
          FocusedSeqFoldOperand (go currentMemo operand)
            (goFocusedOperands currentMemo rest)
    goSome memo _ (SomeTerm (SeqFoldWithTerm step environment initial sequence)) =
      let folded =
            pevalClosedSeqFoldWith
              (go memo step)
              (go memo environment)
              (go memo initial)
              (go memo sequence)
       in folded `seq` SomeTerm folded
    goSome memo _ (SomeTerm (PairTerm firstValue secondValue)) =
      goBinary memo pevalPairTerm firstValue secondValue
    goSome memo _ (SomeTerm (FirstTerm pairValue)) =
      goUnary memo pevalFirstTerm pairValue
    goSome memo _ (SomeTerm (SecondTerm pairValue)) =
      goUnary memo pevalSecondTerm pairValue
    goUnary memo f a = SomeTerm $ f (go memo a)
    goBinary memo f a b = SomeTerm $ f (go memo a) (go memo b)
    goTernary memo f a b c =
      SomeTerm $ f (go memo a) (go memo b) (go memo c)

-- | Substitute a term for a symbol in a term.
substTerm ::
  forall knd a b.
  (SupportedPrim a, SupportedPrim b, IsSymbolKind knd) =>
  TypedSymbol knd a ->
  Term a ->
  HS.HashSet SomeTypedConstantSymbol ->
  Term b ->
  Term b
substTerm sym@SupportedTypedSymbol a boundedSymbols =
  generalSubstSomeTerm
    ( \t ->
        if eqHeteroSymbol sym t
          then unsafeCoerce a
          else symTerm t
    )
    (extractSymSomeTermIncludeBoundedVars (SomeTerm a))
    boundedSymbols

supportedPrimFunUpTo
  [|buildGeneralFun (typedConstantSymbol "a") (conTerm defaultValue)|]
  [|
    \c t f -> case (t, f) of
      ( ConTerm (GeneralFun (ta :: TypedConstantSymbol a) a),
        ConTerm (GeneralFun tb b)
        ) ->
          conTerm $
            GeneralFun argSymbol $
              pevalITETerm
                c
                (substTerm ta (symTerm argSymbol) HS.empty a)
                (substTerm tb (symTerm argSymbol) HS.empty b)
          where
            argSymbol :: TypedConstantSymbol a
            argSymbol = freshArgSymbol [SomeTerm a, SomeTerm b]
      _ -> pevalITEBasicTerm c t f
    |]
  [|parseGeneralFunSMTModelResult|]
  ( \tyVars ->
      [|
        translateTypeError
          (Just "x")
          ( typeRep ::
              TypeRep
                $( foldl1 (\fty ty -> [t|$ty --> $fty|])
                     . reverse
                     $ tyVars
                 )
          )
        |]
  )
  "GeneralFun"
  "gfunc"
  ''(-->)
  8
