{-# LANGUAGE CPP #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE Trustworthy #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

-- |
-- Module      :   Grisette.Internal.Internal.Decl.Core.Data.UnionBase
-- Copyright   :   (c) Sirui Lu 2021-2024
-- License     :   BSD-3-Clause (see the LICENSE file)
--
-- Maintainer  :   siruilu@cs.washington.edu
-- Stability   :   Experimental
-- Portability :   GHC only
module Grisette.Internal.Internal.Decl.Core.Data.UnionBase
  ( -- * The union data structure.

    -- | Please consider using 'Grisette.Core.Union' instead.
    UnionBase (..),
    eraseUnionGroups,
    ifWithLeftMost,
    ifWithStrategy,
    fullReconstruct,
  )
where

import Control.Monad (ap)
import Grisette.Internal.Core.Data.Class.AsKey (AsKey (AsKey), KeyEq (keyEq), KeyEq1 (liftKeyEq), shouldUseAsKeyHasSymbolicVersionError)
import Grisette.Internal.Core.Data.Class.LogicalOp
  ( LogicalOp (symNot, (.&&), (.||)),
  )
import Grisette.Internal.Core.Data.Class.Solvable (pattern Con)
import Grisette.Internal.Core.Data.Class.UnionView
  ( IfViewResult (IfViewResult),
    UnionView (ifView, singleView),
  )
import Grisette.Internal.Internal.Decl.Core.Data.Class.Mergeable
  ( Mergeable (rootStrategy),
    Mergeable1 (liftRootStrategy),
    MergingStrategy (SimpleStrategy, SortedStrategy),
    StructuralStrategyCase (StructuralStrategyCase),
    StructuralStrategyView (StructuralStrategyView),
    StructuralOrdering (StructuralEQ, StructuralGT, StructuralLT),
    structuralStrategyView,
  )
import Grisette.Internal.Internal.Decl.Core.Data.Class.SimpleMergeable
  ( SimpleMergeable (mrgIte),
    SimpleMergeable1 (liftMrgIte),
    MergingBranching (mrgIfWithStrategy),
    SymBranching (mrgIfPropagatedStrategy),
    mrgIf,
  )
import Grisette.Internal.Internal.Decl.Core.Data.Class.TryMerge
  ( TryMerge (tryMergeWithStrategy),
  )
import Grisette.Internal.SymPrim.SymBool
  ( SymBool,
    symIteMergeGuard,
  )

-- | The base union implementation, which is an if-then-else tree structure.
data UnionBase a where
  -- | A single value
  UnionSingle :: a -> UnionBase a
  -- | A if value
  UnionIf ::
    -- | Cached leftmost value
    a ->
    -- | Is merged invariant already maintained?
    !Bool ->
    -- | If condition
    !SymBool ->
    -- | True branch
    UnionBase a ->
    -- | False branch
    UnionBase a ->
    UnionBase a
  -- | A homogeneous group selected by an actual structural ADT/GADT witness.
  -- The constructor is intentionally hidden by the public UnionBase facade.
  UnionGroup ::
    key payload ->
    MergingStrategy payload ->
    (payload -> a) ->
    UnionBase payload ->
    UnionBase a

instance Functor UnionBase where
  fmap f (UnionSingle value) = UnionSingle (f value)
  fmap f (UnionIf cached merged guard ifTrue ifFalse) =
    UnionIf
      (f cached)
      merged
      guard
      (fmap f ifTrue)
      (fmap f ifFalse)
  fmap f group@UnionGroup {} = fmap f (eraseUnionGroups group)
  {-# INLINE fmap #-}

-- | Remove the internal typed grouping while preserving the exact transparent
-- if-then-else semantics. Erased conditionals are marked unmerged so a caller
-- cannot accidentally reuse a representation invariant from another strategy.
eraseUnionGroups :: UnionBase a -> UnionBase a
eraseUnionGroups (UnionSingle value) = UnionSingle value
eraseUnionGroups (UnionIf _ _ guard ifTrue ifFalse) =
  ifWithLeftMost
    False
    guard
    (eraseUnionGroups ifTrue)
    (eraseUnionGroups ifFalse)
eraseUnionGroups (UnionGroup _ _ inject payloads) =
  fmap inject (eraseUnionGroups payloads)
{-# INLINE eraseUnionGroups #-}

instance (Eq a) => Eq (UnionBase a) where
  (==) = shouldUseAsKeyHasSymbolicVersionError "UnionBase" "(==)" "(.==)"

instance (Eq a) => KeyEq (UnionBase a) where
  keyEq = liftKeyEq (==)
  {-# INLINE keyEq #-}

instance KeyEq1 UnionBase where
  liftKeyEq f (UnionSingle l) (UnionSingle r) = f l r
  liftKeyEq f (UnionIf _ _ c l r) (UnionIf _ _ c' l' r') =
    keyEq c c' && liftKeyEq f l l' && liftKeyEq f r r'
  liftKeyEq f left@UnionGroup {} right =
    liftKeyEq f (eraseUnionGroups left) (eraseUnionGroups right)
  liftKeyEq f left right@UnionGroup {} =
    liftKeyEq f (eraseUnionGroups left) (eraseUnionGroups right)
  liftKeyEq _ _ _ = False
  {-# INLINE liftKeyEq #-}

instance Applicative UnionBase where
  pure = UnionSingle
  {-# INLINE pure #-}
  (<*>) = ap
  {-# INLINE (<*>) #-}

instance Monad UnionBase where
  return = pure
  {-# INLINE return #-}
  UnionSingle a >>= f = f a
  UnionIf _ _ c t f >>= f' = ifWithLeftMost False c (t >>= f') (f >>= f')
  UnionGroup _ _ inject payloads >>= f = payloads >>= (f . inject)
  {-# INLINE (>>=) #-}

instance TryMerge UnionBase where
  tryMergeWithStrategy = fullReconstruct
  {-# INLINE tryMergeWithStrategy #-}

-- | Fully reconstruct a 'Grisette.Core.Union' to maintain the merged invariant.
fullReconstruct :: MergingStrategy a -> UnionBase a -> UnionBase a
fullReconstruct strategy (UnionIf _ False cond t f) =
  ifWithStrategyInv
    strategy
    cond
    (fullReconstruct strategy t)
    (fullReconstruct strategy f)
fullReconstruct _ u = u
{-# INLINE fullReconstruct #-}

leftMost :: UnionBase a -> a
leftMost (UnionSingle a) = a
leftMost (UnionIf a _ _ _ _) = a
leftMost (UnionGroup _ _ inject payloads) = inject (leftMost payloads)
{-# INLINE leftMost #-}

-- | Build 'UnionIf' with leftmost cache correctly maintained.
--
-- Usually you should never directly try to build a 'UnionIf' with its
-- constructor.
ifWithLeftMost :: Bool -> SymBool -> UnionBase a -> UnionBase a -> UnionBase a
ifWithLeftMost _ (Con c) t f
  | c = t
  | otherwise = f
ifWithLeftMost inv cond t f = UnionIf (leftMost t) inv cond t f
{-# INLINE ifWithLeftMost #-}

-- | Use a specific strategy to build a 'UnionIf' value.
--
-- The merged invariant will be maintained in the result.
ifWithStrategy ::
  MergingStrategy a ->
  SymBool ->
  UnionBase a ->
  UnionBase a ->
  UnionBase a
ifWithStrategy strategy cond t@(UnionIf _ False _ _ _) f =
  ifWithStrategy strategy cond (fullReconstruct strategy t) f
ifWithStrategy strategy cond t f@(UnionIf _ False _ _ _) =
  ifWithStrategy strategy cond t (fullReconstruct strategy f)
ifWithStrategy strategy cond t f = ifWithStrategyInv strategy cond t f
{-# INLINE ifWithStrategy #-}

data ActiveStructuralUnion key a where
  ActiveStructuralGroup ::
    key payload ->
    UnionBase payload ->
    ActiveStructuralUnion key a
  ActiveStructuralIf ::
    a ->
    SymBool ->
    ActiveStructuralUnion key a ->
    ActiveStructuralUnion key a ->
    ActiveStructuralUnion key a

ifWithStrategyInv ::
  MergingStrategy a ->
  SymBool ->
  UnionBase a ->
  UnionBase a ->
  UnionBase a
ifWithStrategyInv _ (Con v) t f
  | v = t
  | otherwise = f
ifWithStrategyInv strategy cond (UnionIf _ True condTrue tt _) f
  | AsKey cond == AsKey condTrue = ifWithStrategyInv strategy cond tt f
-- {| symNot cond == condTrue || cond == symNot condTrue = ifWithStrategyInv strategy cond ft f
ifWithStrategyInv strategy cond t (UnionIf _ True condFalse _ ff)
  | AsKey cond == AsKey condFalse = ifWithStrategyInv strategy cond t ff
-- {| symNot cond == condTrue || cond == symNot condTrue = ifWithStrategyInv strategy cond t tf -- buggy here condTrue
ifWithStrategyInv strategy@(SimpleStrategy merge) cond ifTrue ifFalse =
  case (ifTrue, ifFalse) of
    (UnionSingle left, UnionSingle right) ->
      UnionSingle $ merge cond left right
    _ ->
      ifWithStrategy
        strategy
        cond
        (eraseUnionGroups ifTrue)
        (eraseUnionGroups ifFalse)
ifWithStrategyInv
  strategy@(SortedStrategy idxFun substrategy)
  cond
  ifTrue
  ifFalse = case (ifTrue, ifFalse) of
    (UnionIf {}, UnionIf {}) -> ggUnionIf cond ifTrue ifFalse
    (UnionIf {}, _) -> gsUnionIf cond ifTrue ifFalse
    (_, UnionIf {}) -> sgUnionIf cond ifTrue ifFalse
    _ -> ssUnionIf cond ifTrue ifFalse
    where
      ssUnionIf cond' ifTrue' ifFalse'
        | idxt < idxf = ifWithLeftMost True cond' ifTrue' ifFalse'
        | idxt == idxf =
            ifWithStrategyInv (substrategy idxt) cond' ifTrue' ifFalse'
        | otherwise = ifWithLeftMost True (symNot cond') ifFalse' ifTrue'
        where
          idxt = idxFun $ leftMost ifTrue'
          idxf = idxFun $ leftMost ifFalse'
      {-# INLINE ssUnionIf #-}
      sgUnionIf cond' ifTrue' ifFalse'@(UnionIf _ True condf ft ff)
        | idxft == idxff = ssUnionIf cond' ifTrue' ifFalse'
        | idxt < idxft = ifWithLeftMost True cond' ifTrue' ifFalse'
        | idxt == idxft =
            ifWithLeftMost
              True
              (cond' .|| condf)
              (ifWithStrategyInv (substrategy idxt) cond' ifTrue' ft)
              ff
        | otherwise =
            ifWithLeftMost
              True
              (symNot cond' .&& condf)
              ft
              (ifWithStrategyInv strategy cond' ifTrue' ff)
        where
          idxft = idxFun $ leftMost ft
          idxff = idxFun $ leftMost ff
          idxt = idxFun $ leftMost ifTrue'
      sgUnionIf cond' ifTrue' ifFalse' = ssUnionIf cond' ifTrue' ifFalse'
      {-# INLINE sgUnionIf #-}
      gsUnionIf cond' ifTrue'@(UnionIf _ True condt tt tf) ifFalse'
        | idxtt == idxtf = ssUnionIf cond' ifTrue' ifFalse'
        | idxtt < idxf =
            ifWithLeftMost True (cond' .&& condt) tt $
              ifWithStrategyInv strategy cond' tf ifFalse'
        | idxtt == idxf =
            ifWithLeftMost
              True
              (symNot cond' .|| condt)
              (ifWithStrategyInv (substrategy idxf) cond' tt ifFalse')
              tf
        | otherwise = ifWithLeftMost True (symNot cond') ifFalse' ifTrue'
        where
          idxtt = idxFun $ leftMost tt
          idxtf = idxFun $ leftMost tf
          idxf = idxFun $ leftMost ifFalse'
      gsUnionIf cond' ifTrue' ifFalse' = ssUnionIf cond' ifTrue' ifFalse'
      {-# INLINE gsUnionIf #-}
      ggUnionIf
        cond'
        ifTrue'@(UnionIf _ True condt tt tf)
        ifFalse'@(UnionIf _ True condf ft ff)
          | idxtt == idxtf = sgUnionIf cond' ifTrue' ifFalse'
          | idxft == idxff = gsUnionIf cond' ifTrue' ifFalse'
          | idxtt < idxft =
              ifWithLeftMost True (cond' .&& condt) tt $
                ifWithStrategyInv strategy cond' tf ifFalse'
          | idxtt == idxft =
              let newCond = symIteMergeGuard cond' condt condf
                  newUnionIfTrue =
                    ifWithStrategyInv (substrategy idxtt) cond' tt ft
                  newUnionIfFalse = ifWithStrategyInv strategy cond' tf ff
               in ifWithLeftMost True newCond newUnionIfTrue newUnionIfFalse
          | otherwise =
              ifWithLeftMost True (symNot cond' .&& condf) ft $
                ifWithStrategyInv strategy cond' ifTrue' ff
          where
            idxtt = idxFun $ leftMost tt
            idxtf = idxFun $ leftMost tf
            idxft = idxFun $ leftMost ft
            idxff = idxFun $ leftMost ff
      ggUnionIf cond' ifTrue' ifFalse' =
        case (ifTrue', ifFalse') of
          (UnionIf {}, _) -> gsUnionIf cond' ifTrue' ifFalse'
          _ -> sgUnionIf cond' ifTrue' ifFalse'
      {-# INLINE ggUnionIf #-}
ifWithStrategyInv strategy cond originalTrue originalFalse =
  case structuralStrategyView strategy of
    Just structuralView -> mergeWithStructuralView structuralView
    Nothing -> ifWithLeftMost True cond originalTrue originalFalse
  where
    mergeWithStructuralView
      ( StructuralStrategyView
          split
          compareKey
          _
          payloadStrategy
          inject
        ) =
        forgetActive $
          mergeStructural
            cond
            (normalizeStructuralOperand originalTrue)
            (normalizeStructuralOperand originalFalse)
      where
        forgetActive (ActiveStructuralGroup key payloads) =
          UnionGroup key (payloadStrategy key) (inject key) payloads
        forgetActive (ActiveStructuralIf cached cond' ifTrue ifFalse) =
          UnionIf
            cached
            True
            cond'
            (forgetActive ifTrue)
            (forgetActive ifFalse)

        activeLeftMost (ActiveStructuralGroup key payloads) =
          inject key (leftMost payloads)
        activeLeftMost (ActiveStructuralIf cached _ _ _) = cached

        activeIfWithLeftMost (Con selected) ifTrue ifFalse
          | selected = ifTrue
          | otherwise = ifFalse
        activeIfWithLeftMost cond' ifTrue ifFalse =
          ActiveStructuralIf
            (activeLeftMost ifTrue)
            cond'
            ifTrue
            ifFalse

        makeGroup value = case split value of
          StructuralStrategyCase key payload ->
            ActiveStructuralGroup key (UnionSingle payload)

        normalizeStructuralOperand = reconstructActive . eraseUnionGroups

        reconstructActive (UnionSingle value) = makeGroup value
        reconstructActive (UnionIf _ _ cond' ifTrue ifFalse) =
          mergeStructural
            cond'
            (reconstructActive ifTrue)
            (reconstructActive ifFalse)
        reconstructActive group@UnionGroup {} =
          reconstructActive (eraseUnionGroups group)

        rebuildStructural = normalizeStructuralOperand . forgetActive

        compareValues left right =
          case (split left, split right) of
            (StructuralStrategyCase leftKey _, StructuralStrategyCase rightKey _) ->
              case compareKey leftKey rightKey of
                StructuralLT -> LT
                StructuralEQ -> EQ
                StructuralGT -> GT

        mergeStructural cond' ifTrue ifFalse =
          case (ifTrue, ifFalse) of
            (left@ActiveStructuralGroup {}, right@ActiveStructuralGroup {}) ->
              mergeGroups cond' left right
            ( left@ActiveStructuralGroup {},
              right@(ActiveStructuralIf _ condRight rt rf)
              ) ->
                mergeGroupIf cond' left right condRight rt rf
            ( left@(ActiveStructuralIf _ condLeft lt lf),
              right@ActiveStructuralGroup {}
              ) ->
                mergeIfGroup cond' left condLeft lt lf right
            ( left@(ActiveStructuralIf _ condLeft lt lf),
              right@(ActiveStructuralIf _ condRight rt rf)
              ) ->
                mergeIfIf
                  cond'
                  left
                  condLeft
                  lt
                  lf
                  right
                  condRight
                  rt
                  rf

        mergeGroups
          cond'
          leftGroup@(ActiveStructuralGroup leftKey leftPayloads)
          rightGroup@(ActiveStructuralGroup rightKey rightPayloads) =
            case compareKey leftKey rightKey of
              StructuralLT ->
                activeIfWithLeftMost cond' leftGroup rightGroup
              StructuralEQ ->
                ActiveStructuralGroup
                  leftKey
                  ( ifWithStrategy
                      (payloadStrategy leftKey)
                      cond'
                      leftPayloads
                      rightPayloads
                  )
              StructuralGT ->
                activeIfWithLeftMost (symNot cond') rightGroup leftGroup
        mergeGroups cond' left right = mergeStructural cond' left right
        {-# INLINE mergeGroups #-}

        mergeGroupIf cond' ifTrue ifFalse condFalse ft ff =
          case compareValues (activeLeftMost ft) (activeLeftMost ff) of
            EQ ->
              mergeStructural cond' ifTrue (rebuildStructural ifFalse)
            GT ->
              mergeStructural cond' ifTrue (rebuildStructural ifFalse)
            LT ->
              case compareValues (activeLeftMost ifTrue) (activeLeftMost ft) of
                LT -> activeIfWithLeftMost cond' ifTrue ifFalse
                EQ ->
                  activeIfWithLeftMost
                    (cond' .|| condFalse)
                    (mergeStructural cond' ifTrue ft)
                    ff
                GT ->
                  activeIfWithLeftMost
                    (symNot cond' .&& condFalse)
                    ft
                    (mergeStructural cond' ifTrue ff)
        {-# INLINE mergeGroupIf #-}

        mergeIfGroup cond' ifTrue condTrue tt tf ifFalse =
          case compareValues (activeLeftMost tt) (activeLeftMost tf) of
            EQ ->
              mergeStructural cond' (rebuildStructural ifTrue) ifFalse
            GT ->
              mergeStructural cond' (rebuildStructural ifTrue) ifFalse
            LT ->
              case compareValues (activeLeftMost tt) (activeLeftMost ifFalse) of
                LT ->
                  activeIfWithLeftMost (cond' .&& condTrue) tt $
                    mergeStructural cond' tf ifFalse
                EQ ->
                  activeIfWithLeftMost
                    (symNot cond' .|| condTrue)
                    (mergeStructural cond' tt ifFalse)
                    tf
                GT ->
                  activeIfWithLeftMost (symNot cond') ifFalse ifTrue
        {-# INLINE mergeIfGroup #-}

        mergeIfIf
          cond'
          ifTrue
          condTrue
          tt
          tf
          ifFalse
          condFalse
          ft
          ff =
            case compareValues (activeLeftMost tt) (activeLeftMost tf) of
              EQ -> mergeStructural cond' (rebuildStructural ifTrue) ifFalse
              GT -> mergeStructural cond' (rebuildStructural ifTrue) ifFalse
              LT ->
                case compareValues (activeLeftMost ft) (activeLeftMost ff) of
                  EQ -> mergeStructural cond' ifTrue (rebuildStructural ifFalse)
                  GT -> mergeStructural cond' ifTrue (rebuildStructural ifFalse)
                  LT ->
                    case compareValues (activeLeftMost tt) (activeLeftMost ft) of
                      LT ->
                        activeIfWithLeftMost (cond' .&& condTrue) tt $
                          mergeStructural cond' tf ifFalse
                      EQ ->
                        let newCond = symIteMergeGuard cond' condTrue condFalse
                            newUnionIfTrue = mergeStructural cond' tt ft
                            newUnionIfFalse = mergeStructural cond' tf ff
                         in activeIfWithLeftMost
                              newCond
                              newUnionIfTrue
                              newUnionIfFalse
                      GT ->
                        activeIfWithLeftMost (symNot cond' .&& condFalse) ft $
                          mergeStructural cond' ifTrue ff
        {-# INLINE mergeIfIf #-}
{-# INLINE ifWithStrategyInv #-}

instance (Mergeable a) => Mergeable (UnionBase a) where
  rootStrategy = SimpleStrategy $ ifWithStrategy rootStrategy
  {-# INLINE rootStrategy #-}

instance Mergeable1 UnionBase where
  liftRootStrategy ms = SimpleStrategy $ ifWithStrategy ms
  {-# INLINE liftRootStrategy #-}

instance (Mergeable a) => SimpleMergeable (UnionBase a) where
  mrgIte = mrgIf

instance SimpleMergeable1 UnionBase where
  liftMrgIte m = mrgIfWithStrategy (SimpleStrategy m)

instance MergingBranching UnionBase where
  mrgIfWithStrategy = ifWithStrategy
  {-# INLINE mrgIfWithStrategy #-}

instance SymBranching UnionBase where
  mrgIfPropagatedStrategy = ifWithLeftMost False
  {-# INLINE mrgIfPropagatedStrategy #-}

instance UnionView UnionBase where
  singleView (UnionSingle a) = Just a
  singleView (UnionGroup _ _ inject payloads) =
    inject <$> singleView payloads
  singleView _ = Nothing
  {-# INLINE singleView #-}
  ifView (UnionIf _ _ cond ifTrue ifFalse) =
    Just (IfViewResult cond ifTrue ifFalse)
  ifView (UnionGroup key strategy inject payloads) =
    case ifView payloads of
      Just (IfViewResult cond ifTrue ifFalse) ->
        Just
          ( IfViewResult
              cond
              (UnionGroup key strategy inject ifTrue)
              (UnionGroup key strategy inject ifFalse)
          )
      Nothing -> Nothing
  ifView _ = Nothing
  {-# INLINE ifView #-}
