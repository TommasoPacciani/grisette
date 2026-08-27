{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RoleAnnotations #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE Trustworthy #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

-- |
-- Module      :   Grisette.Internal.Internal.Decl.Core.Data.Class.Mergeable
-- Copyright   :   (c) Sirui Lu 2021-2023
-- License     :   BSD-3-Clause (see the LICENSE file)
--
-- Maintainer  :   siruilu@cs.washington.edu
-- Stability   :   Experimental
-- Portability :   GHC only
module Grisette.Internal.Internal.Decl.Core.Data.Class.Mergeable
  ( -- * Merging strategy
    MergingStrategy (..),
    MergingIndex,
    StructuralOrdering (..),
    StructuralFamily (..),
    StructuralWrapper (..),
    StructuralCase (..),
    structuralStrategy,
    StructuralStrategyCase (..),
    StructuralStrategyView (..),
    structuralStrategyView,

    -- * Mergeable
    Mergeable (..),
    Mergeable1 (..),
    rootStrategy1,
    Mergeable2 (..),
    rootStrategy2,
    Mergeable3 (..),
    rootStrategy3,

    -- * Generic 'Mergeable'
    MergeableArgs (..),
    GMergeable (..),
    genericRootStrategy,
    genericLiftRootStrategy,

    -- * Combinators for manually building merging strategies
    wrapStrategy,
    pairStrategy,
    product2Strategy,
    DynamicSortedIdx (..),
    ResolvedStrategy (..),
    resolveStrategy,
    resolveStrategy',
    resolveMergeable1,

    -- * Internal structural law witnesses (not re-exported by the public facade)
    GenericProductWrapper (GenericProductWrapper),
    M1Wrapper (M1Wrapper),
    K1Wrapper (K1Wrapper),
    Par1Wrapper (Par1Wrapper),
    Rec1Wrapper (Rec1Wrapper),
    Comp1Wrapper (Comp1Wrapper),
    DefaultWrapper (DefaultWrapper),
    GenericWrapper (GenericWrapper),
    Default1Wrapper (Default1Wrapper),
    Generic1Wrapper (Generic1Wrapper),
    AsKeyWrapper (AsKeyWrapper),
    AsKey1Wrapper (AsKey1Wrapper),
  )
where

import Data.Kind (Type)
import Data.Typeable
  ( Typeable,
    eqT,
    type (:~:) (Refl),
  )
import Generics.Deriving
  ( Default (Default),
    Default1 (Default1),
    Generic (Rep, from, to),
    Generic1 (Rep1, from1, to1),
    K1 (K1, unK1),
    M1 (M1, unM1),
    Par1 (Par1, unPar1),
    Rec1 (Rec1, unRec1),
    U1,
    V1,
    (:.:) (Comp1, unComp1),
    type (:*:) ((:*:)),
    type (:+:) (L1, R1),
  )
import Grisette.Internal.Core.Data.Class.AsKey (AsKey (AsKey, getAsKey), AsKey1 (AsKey1, getAsKey1))
import Grisette.Internal.Core.Data.Class.ITEOp (ITEOp (symIte))
import Grisette.Internal.SymPrim.SymBool (SymBool)
import Grisette.Internal.Utils.Derive (Arity0, Arity1)
import Type.Reflection
  ( SomeTypeRep (SomeTypeRep),
    typeRep,
  )

-- | For a type to be used as an index in a 'SortedStrategy', it must be both
-- 'Ord' and 'Typeable'.
type MergingIndex a = (Ord a, Typeable a)

-- | A total comparison of two members of the same structural family.
--
-- 'StructuralEQ' carries the proof that equal structural witnesses have the
-- same payload type. Unlike a sorted index, the witness is the actual host
-- ADT/GADT constructor and is never encoded as a Boolean or numeric ordinal.
data StructuralOrdering a b where
  StructuralLT :: StructuralOrdering a b
  StructuralEQ :: StructuralOrdering a a
  StructuralGT :: StructuralOrdering a b

-- | A closed family of structural witnesses.
--
-- The first parameter of a witness is the value reconstructed by the family;
-- the second is the homogeneous payload stored in a typed union group.
-- Implementations must define one total order over actual witness shapes.
-- 'compareStructuralShape' must agree with 'compareStructural' whenever the
-- result indices coincide. A witness may contain evidence used by that order,
-- but it must not contain a strategy, injector, callback, or other behavior
-- that the comparison ignores.
class (Typeable structuralFamily) =>
    StructuralFamily (structuralFamily :: Type -> Type -> Type) where
  -- | Compare witnesses for one result type and, on equality, prove that their
  -- payload types agree.
  compareStructural ::
    structuralFamily value a ->
    structuralFamily value b ->
    StructuralOrdering a b

  -- | Compare witness shapes after erasing the result and payload indices.
  -- This is used only for host-side strategy-path ordering. Implementations
  -- must agree with 'compareStructural' whenever the result types coincide.
  compareStructuralShape ::
    structuralFamily leftValue a ->
    structuralFamily rightValue b ->
    Ordering

-- | A structural witness that owns a total isomorphism between its source and
-- target indices.
--
-- The two operations are methods of the witness family rather than closures
-- supplied to 'wrapStrategy'. This is essential for typed union groups: two
-- witnesses that compare as 'StructuralEQ' must necessarily reconstruct values
-- with the same relation.
--
-- Instances must satisfy both inverse laws for every witness:
--
-- @
-- wrapValue witness . unwrapValue witness = id
-- unwrapValue witness . wrapValue witness = id
-- @
class (StructuralFamily wrapper) => StructuralWrapper wrapper where
  wrapValue :: wrapper target source -> source -> target
  unwrapValue :: wrapper target source -> target -> source

-- | A value split into its actual structural witness and homogeneous payload.
data StructuralCase structuralFamily value where
  StructuralCase ::
    structuralFamily value payload ->
    payload ->
    StructuralCase structuralFamily value

-- | A source-specialized structural key used internally by strategy lifting.
-- The source index is fixed in the key type, so payload equality proofs remain
-- fully typed without making the strategy value parameter nominal.
data SpecializedStructuralKey structuralFamily source payload where
  SpecializedStructuralKey ::
    structuralFamily source payload ->
    SpecializedStructuralKey structuralFamily source payload

-- | An internal structural split whose key type already fixes its source.
data StructuralStrategyCase key where
  StructuralStrategyCase ::
    key payload ->
    payload ->
    StructuralStrategyCase key

-- | Merging strategies.
--
-- __You probably do not need to know the details of this type if you are only__
-- __going to use algebraic data types. You can get merging strategies for__
-- __them with type derivation.__
--
-- In Grisette, a merged union (if-then-else tree) follows the
-- __/hierarchical sorted representation invariant/__ with regards to some
-- merging strategy.
--
-- A merging strategy encodes how to merge a __/subset/__ of the values of a
-- given type. We have four types of merging strategies:
--
-- * Simple strategy
-- * Sorted strategy
-- * Structural strategy
-- * No strategy
--
-- The 'SimpleStrategy' merges values with a simple merge function.
-- For example,
--
--    * the symbolic boolean values can be directly merged with 'symIte'.
--
--    * the set @{1}@, which is a subset of the values of the type @Integer@,
--        can be simply merged as the set contains only a single value.
--
--    * a homogeneous payload group selected by an actual @Just@ witness can
--        merge its symbolic boolean payload with 'symIte'.
--
-- The 'SortedStrategy' merges values by first grouping the values with an
-- indexing function, and the values with the same index will be organized as
-- a sub-tree in the if-then-else structure of
-- 'Grisette.Core.Data.UnionBase.UnionBase'. Each group (sub-tree) will be
-- further merged with a sub-strategy for the index.
-- The index type should be a totally ordered type (with the 'Ord'
-- type class). Grisette will use the indexing function to partition the values
-- into sub-trees, and organize them in a sorted way. The sub-trees will further
-- be merged with the sub-strategies. For example,
--
--    * all the integers can be merged with 'SortedStrategy' by indexing with
--      the identity function and use the 'SimpleStrategy' shown before as the
--      sub-strategies.
--
-- Finite constructor identity must not be encoded as a sorted Boolean or
-- numeric index. Algebraic data types use 'StructuralStrategy' and actual
-- constructor witnesses instead.
--
-- The 'NoStrategy' does not perform any merging.
-- For example, we cannot merge values with function types that returns concrete
-- lists.
--
-- For ADTs, we can automatically derive the 'Mergeable' type class, which
-- provides a merging strategy.
--
-- If the derived version does not work for you, you should determine
-- if your type can be directly merged with a merging function. If so, you can
-- implement the merging strategy as a 'SimpleStrategy'.
-- If the type cannot be directly merged with a merging function, but could be
-- partitioned by genuine ordered domain data, use 'SortedStrategy'. For actual
-- ADT/GADT constructor alternatives, use 'StructuralStrategy'.
-- For easier building of the merging strategies, check out the combinators
-- like `wrapStrategy`.
--
-- For more details, please see the documents of the constructors, or refer to
-- [Grisette's paper](https://lsrcz.github.io/files/POPL23.pdf).
type role MergingStrategy representational

data MergingStrategy a where
  -- | Simple mergeable strategy.
  --
  -- For symbolic booleans, we can implement its merge strategy as follows:
  --
  -- > SimpleStrategy symIte :: MergingStrategy SymBool
  SimpleStrategy ::
    -- | Merge function.
    (SymBool -> a -> a -> a) ->
    MergingStrategy a
  -- | Sorted mergeable strategy.
  --
  -- For Integers, we can implement its merge strategy as follows:
  --
  -- > SortedStrategy id (\_ -> SimpleStrategy $ \_ t _ -> t)
  --
  -- Use this constructor only for genuine ordered domain data. Algebraic
  -- constructor identity belongs in 'StructuralStrategy'.
  SortedStrategy ::
    (MergingIndex idx) =>
    -- | Indexing function
    (a -> idx) ->
    -- | Sub-strategy function
    (idx -> MergingStrategy a) ->
    MergingStrategy a
  -- | A total, typed structural-family strategy. Values with the same actual
  -- host witness are retained in a homogeneous typed union group. Values with
  -- different witnesses remain separate groups in structural order.
  StructuralStrategy ::
    (StructuralFamily structuralFamily) =>
    (a -> StructuralCase structuralFamily source) ->
    ( forall payload.
      structuralFamily source payload -> MergingStrategy payload
    ) ->
    (forall payload. structuralFamily source payload -> payload -> a) ->
    MergingStrategy a
  -- | Internal source-specialized structural strategy. The key type fixes the
  -- witness source independently of @a@, preserving the representational role
  -- needed by newtype and deriving-via strategy transport.
  StructuralStrategyInternal ::
    (a -> StructuralStrategyCase key) ->
    (forall left right. key left -> key right -> StructuralOrdering left right) ->
    (forall payload. key payload -> DynamicSortedIdx) ->
    (forall payload. key payload -> MergingStrategy payload) ->
    (forall payload. key payload -> payload -> a) ->
    MergingStrategy a
  -- | For preventing the merging intentionally. This could be
  -- useful for keeping some value concrete and may help generate more efficient
  -- formulas.
  --
  -- See [Grisette's paper](https://lsrcz.github.io/files/POPL23.pdf) for
  -- details.
  NoStrategy :: MergingStrategy a

data StructuralStrategyView a where
  StructuralStrategyView ::
    (a -> StructuralStrategyCase key) ->
    (forall left right. key left -> key right -> StructuralOrdering left right) ->
    (forall payload. key payload -> DynamicSortedIdx) ->
    (forall payload. key payload -> MergingStrategy payload) ->
    (forall payload. key payload -> payload -> a) ->
    StructuralStrategyView a

structuralStrategyView ::
  forall a. MergingStrategy a -> Maybe (StructuralStrategyView a)
structuralStrategyView
  ( StructuralStrategy
      (split :: a -> StructuralCase structuralFamily source)
      payloadStrategy
      inject
    ) =
    Just $
      StructuralStrategyView
        splitSpecialized
        compareSpecialized
        indexSpecialized
        payloadStrategySpecialized
        injectSpecialized
    where
      splitSpecialized ::
        a -> StructuralStrategyCase (SpecializedStructuralKey structuralFamily source)
      splitSpecialized value = case split value of
        StructuralCase key payload ->
          StructuralStrategyCase (SpecializedStructuralKey key) payload

      compareSpecialized ::
        forall left right.
        SpecializedStructuralKey structuralFamily source left ->
        SpecializedStructuralKey structuralFamily source right ->
        StructuralOrdering left right
      compareSpecialized
        (SpecializedStructuralKey left)
        (SpecializedStructuralKey right) = compareStructural left right

      indexSpecialized ::
        forall payload.
        SpecializedStructuralKey structuralFamily source payload ->
        DynamicSortedIdx
      indexSpecialized (SpecializedStructuralKey key) =
        DynamicStructuralIdx key

      payloadStrategySpecialized ::
        forall payload.
        SpecializedStructuralKey structuralFamily source payload ->
        MergingStrategy payload
      payloadStrategySpecialized (SpecializedStructuralKey key) =
        payloadStrategy key

      injectSpecialized ::
        forall payload.
        SpecializedStructuralKey structuralFamily source payload ->
        payload ->
        a
      injectSpecialized (SpecializedStructuralKey key) = inject key
structuralStrategyView
  (StructuralStrategyInternal split compareKey indexKey payloadStrategy inject) =
    Just $
      StructuralStrategyView split compareKey indexKey payloadStrategy inject
structuralStrategyView _ = Nothing
{-# INLINE structuralStrategyView #-}

-- | Build a total typed structural-family merging strategy.
structuralStrategy ::
  (StructuralFamily structuralFamily) =>
  (a -> StructuralCase structuralFamily source) ->
  ( forall payload.
    structuralFamily source payload -> MergingStrategy payload
  ) ->
  (forall payload. structuralFamily source payload -> payload -> a) ->
  MergingStrategy a
structuralStrategy = StructuralStrategy
{-# INLINE structuralStrategy #-}

-- | Each type is associated with a root merge strategy given by 'rootStrategy'.
-- The root merge strategy should be able to merge every value of the type.
-- Grisette will use the root merge strategy to merge the values of the type in
-- a union.
--
-- __Note 1:__ This type class can be derived for algebraic data types.
-- You may need the @DerivingVia@ and @DerivingStrategies@ extensions.
--
-- > data X = ... deriving Generic deriving Mergeable via (Default X)
class Mergeable a where
  -- | The root merging strategy for the type.
  rootStrategy :: MergingStrategy a

  sortIndices :: a -> [DynamicSortedIdx]
  sortIndices value = case resolveStrategy rootStrategy value of
    ResolvedStrategy indices _ _ _ -> indices

-- | Lifting of the 'Mergeable' class to unary type constructors.
class
  (forall a. (Mergeable a) => Mergeable (u a)) =>
  Mergeable1 (u :: Type -> Type)
  where
  -- | Lift merge strategy through the type constructor.
  liftRootStrategy :: MergingStrategy a -> MergingStrategy (u a)

-- | Lift the root merge strategy through the unary type constructor.
rootStrategy1 :: (Mergeable a, Mergeable1 u) => MergingStrategy (u a)
rootStrategy1 = liftRootStrategy rootStrategy
{-# INLINE rootStrategy1 #-}

-- | Workaround as GHC prior to 9.6 doesn't support quantified constraints
-- reliably.
--
-- Similar to https://github.com/haskell/core-libraries-committee/issues/10,
-- which is only available with 9.6 or higher.
resolveMergeable1 ::
  forall f a r. (Mergeable1 f, Mergeable a) => ((Mergeable (f a)) => r) -> r
resolveMergeable1 v = v

-- | Lifting of the 'Mergeable' class to binary type constructors.
class
  (forall a. (Mergeable a) => Mergeable1 (u a)) =>
  Mergeable2 (u :: Type -> Type -> Type)
  where
  -- | Lift merge strategy through the type constructor.
  liftRootStrategy2 ::
    MergingStrategy a ->
    MergingStrategy b ->
    MergingStrategy (u a b)

-- | Lift the root merge strategy through the binary type constructor.
rootStrategy2 ::
  (Mergeable a, Mergeable b, Mergeable2 u) =>
  MergingStrategy (u a b)
rootStrategy2 = liftRootStrategy2 rootStrategy rootStrategy
{-# INLINE rootStrategy2 #-}

-- | Lifting of the 'Mergeable' class to ternary type constructors.
class
  (forall a. (Mergeable a) => Mergeable2 (u a)) =>
  Mergeable3 (u :: Type -> Type -> Type -> Type)
  where
  -- | Lift merge strategy through the type constructor.
  liftRootStrategy3 ::
    MergingStrategy a ->
    MergingStrategy b ->
    MergingStrategy c ->
    MergingStrategy (u a b c)

-- | Lift the root merge strategy through the binary type constructor.
rootStrategy3 ::
  (Mergeable a, Mergeable b, Mergeable c, Mergeable3 u) =>
  MergingStrategy (u a b c)
rootStrategy3 = liftRootStrategy3 rootStrategy rootStrategy rootStrategy
{-# INLINE rootStrategy3 #-}

-- | Useful utility function for building merge strategies manually.
--
-- The supplied witness owns the total source/target isomorphism. Constructor
-- alternatives are not wrappers: represent them directly with a
-- 'StructuralStrategy' whose splitter selects the actual constructor witness.
data WrappedStructuralKey key payload where
  WrappedStructuralKey :: key payload -> WrappedStructuralKey key payload

wrapStrategy ::
  forall wrapper source target.
  (StructuralWrapper wrapper) =>
  -- | The actual relation witness
  wrapper target source ->
  -- | The source merge strategy
  MergingStrategy source ->
  MergingStrategy target
wrapStrategy witness (SimpleStrategy merge) =
  SimpleStrategy
    ( \cond ifTrue ifFalse ->
        wrapValue witness $
          merge
            cond
            (unwrapValue witness ifTrue)
            (unwrapValue witness ifFalse)
    )
wrapStrategy witness (SortedStrategy index subStrategy) =
  SortedStrategy
    (index . unwrapValue witness)
    (\selected -> wrapStrategy witness (subStrategy selected))
wrapStrategy _ NoStrategy = NoStrategy
wrapStrategy witness strategy =
  case structuralStrategyView strategy of
    Just
      ( StructuralStrategyView
          split
          compareKey
          indexKey
          payloadStrategy
          inject
        ) ->
        StructuralStrategyInternal
          ( \target -> case split (unwrapValue witness target) of
              StructuralStrategyCase key payload ->
                StructuralStrategyCase (WrappedStructuralKey key) payload
          )
          ( \(WrappedStructuralKey left) (WrappedStructuralKey right) ->
              compareKey left right
          )
          (\(WrappedStructuralKey key) -> indexKey key)
          (\(WrappedStructuralKey key) -> payloadStrategy key)
          ( \(WrappedStructuralKey key) payload ->
              wrapValue witness (inject key payload)
          )
    Nothing -> NoStrategy
{-# INLINE wrapStrategy #-}

data PairFirstStructuralKey key right payload where
  PairFirstStructuralKey ::
    key leftPayload ->
    PairFirstStructuralKey key right (leftPayload, right)

data PairSecondStructuralKey key left payload where
  PairSecondStructuralKey ::
    key rightPayload ->
    PairSecondStructuralKey key left (left, rightPayload)

pairStrategy ::
  forall a b.
  MergingStrategy a ->
  MergingStrategy b ->
  MergingStrategy (a, b)
pairStrategy strategy1 strategy2 =
  case (strategy1, strategy2) of
    (NoStrategy, _) -> NoStrategy
    (_, NoStrategy) -> NoStrategy
    (SimpleStrategy mergeLeft, SimpleStrategy mergeRight) ->
      SimpleStrategy $ \guard (leftTrue, rightTrue) (leftFalse, rightFalse) ->
        ( mergeLeft guard leftTrue leftFalse,
          mergeRight guard rightTrue rightFalse
        )
    _ -> case structuralStrategyView strategy1 of
      Just
        ( StructuralStrategyView
            split
            compareKey
            indexKey
            payloadStrategy
            inject
          ) ->
          StructuralStrategyInternal
            ( \(left, right) -> case split left of
                StructuralStrategyCase key payload ->
                  StructuralStrategyCase
                    (PairFirstStructuralKey key)
                    (payload, right)
            )
            ( \(PairFirstStructuralKey left) (PairFirstStructuralKey right) ->
                case compareKey left right of
                  StructuralLT -> StructuralLT
                  StructuralEQ -> StructuralEQ
                  StructuralGT -> StructuralGT
            )
            (\(PairFirstStructuralKey key) -> indexKey key)
            ( \(PairFirstStructuralKey key) ->
                pairStrategy (payloadStrategy key) strategy2
            )
            ( \(PairFirstStructuralKey key) (payload, right) ->
                (inject key payload, right)
            )
      Nothing -> case strategy1 of
        leftStrategy@(SimpleStrategy _) ->
          case structuralStrategyView strategy2 of
            Just
              ( StructuralStrategyView
                  split
                  compareKey
                  indexKey
                  payloadStrategy
                  inject
                ) ->
                StructuralStrategyInternal
                  ( \(left, right) -> case split right of
                      StructuralStrategyCase key payload ->
                        StructuralStrategyCase
                          (PairSecondStructuralKey key)
                          (left, payload)
                  )
                  ( \(PairSecondStructuralKey left) (PairSecondStructuralKey right) ->
                      case compareKey left right of
                        StructuralLT -> StructuralLT
                        StructuralEQ -> StructuralEQ
                        StructuralGT -> StructuralGT
                  )
                  (\(PairSecondStructuralKey key) -> indexKey key)
                  ( \(PairSecondStructuralKey key) ->
                      pairStrategy leftStrategy (payloadStrategy key)
                  )
                  ( \(PairSecondStructuralKey key) (left, payload) ->
                      (left, inject key payload)
                  )
            Nothing -> case strategy2 of
              SortedStrategy index subStrategy ->
                SortedStrategy
                  (index . snd)
                  (\idx -> pairStrategy leftStrategy (subStrategy idx))
              _ -> NoStrategy
        SortedStrategy index subStrategy ->
          SortedStrategy
            (index . fst)
            (\idx -> pairStrategy (subStrategy idx) strategy2)
        _ -> NoStrategy
{-# INLINE pairStrategy #-}

-- | Useful utility function for building merge strategies for product types
-- manually.
--
-- For example, to build the merge strategy for the following product type,
-- one could write
--
-- > data X = X { x1 :: Int, x2 :: Bool }
-- > data XWrapper target source where
-- >   XWrapper :: XWrapper X (Int, Bool)
-- >
-- > product2Strategy XWrapper rootStrategy rootStrategy
-- >   :: MergingStrategy X
product2Strategy ::
  (StructuralWrapper wrapper) =>
  -- | The actual product relation witness
  wrapper r (a, b) ->
  -- | The first merge strategy to be wrapped
  MergingStrategy a ->
  -- | The second merge strategy to be wrapped
  MergingStrategy b ->
  MergingStrategy r
product2Strategy witness strategy1 strategy2 =
  wrapStrategy witness (pairStrategy strategy1 strategy2)
{-# INLINE product2Strategy #-}

-- Derivations

-- | The arguments to the generic merging strategy function.
data family MergeableArgs arity a :: Type

data instance MergeableArgs Arity0 _ = MergeableArgs0

newtype instance MergeableArgs Arity1 a = MergeableArgs1 (MergingStrategy a)

-- | The class of types that can be generically merged.
class GMergeable arity f where
  grootStrategy :: MergeableArgs arity a -> MergingStrategy (f a)

data GenericProductWrapper value payload where
  GenericProductWrapper ::
    GenericProductWrapper ((left :*: right) parameter) (left parameter, right parameter)

instance StructuralFamily GenericProductWrapper where
  compareStructural GenericProductWrapper GenericProductWrapper = StructuralEQ
  compareStructuralShape GenericProductWrapper GenericProductWrapper = EQ

instance StructuralWrapper GenericProductWrapper where
  wrapValue GenericProductWrapper (left, right) = left :*: right
  unwrapValue GenericProductWrapper (left :*: right) = (left, right)

data M1Wrapper value payload where
  M1Wrapper :: M1Wrapper (M1 index metadata value parameter) (value parameter)

instance StructuralFamily M1Wrapper where
  compareStructural M1Wrapper M1Wrapper = StructuralEQ
  compareStructuralShape M1Wrapper M1Wrapper = EQ

instance StructuralWrapper M1Wrapper where
  wrapValue M1Wrapper = M1
  unwrapValue M1Wrapper = unM1

data K1Wrapper value payload where
  K1Wrapper :: K1Wrapper (K1 index constant parameter) constant

instance StructuralFamily K1Wrapper where
  compareStructural K1Wrapper K1Wrapper = StructuralEQ
  compareStructuralShape K1Wrapper K1Wrapper = EQ

instance StructuralWrapper K1Wrapper where
  wrapValue K1Wrapper = K1
  unwrapValue K1Wrapper = unK1

data Par1Wrapper value payload where
  Par1Wrapper :: Par1Wrapper (Par1 parameter) parameter

instance StructuralFamily Par1Wrapper where
  compareStructural Par1Wrapper Par1Wrapper = StructuralEQ
  compareStructuralShape Par1Wrapper Par1Wrapper = EQ

instance StructuralWrapper Par1Wrapper where
  wrapValue Par1Wrapper = Par1
  unwrapValue Par1Wrapper = unPar1

data Rec1Wrapper value payload where
  Rec1Wrapper :: Rec1Wrapper (Rec1 value parameter) (value parameter)

instance StructuralFamily Rec1Wrapper where
  compareStructural Rec1Wrapper Rec1Wrapper = StructuralEQ
  compareStructuralShape Rec1Wrapper Rec1Wrapper = EQ

instance StructuralWrapper Rec1Wrapper where
  wrapValue Rec1Wrapper = Rec1
  unwrapValue Rec1Wrapper = unRec1

data Comp1Wrapper value payload where
  Comp1Wrapper ::
    Comp1Wrapper ((outer :.: inner) parameter) (outer (inner parameter))

instance StructuralFamily Comp1Wrapper where
  compareStructural Comp1Wrapper Comp1Wrapper = StructuralEQ
  compareStructuralShape Comp1Wrapper Comp1Wrapper = EQ

instance StructuralWrapper Comp1Wrapper where
  wrapValue Comp1Wrapper = Comp1
  unwrapValue Comp1Wrapper = unComp1

data DefaultWrapper value payload where
  DefaultWrapper :: DefaultWrapper (Default value) value

instance StructuralFamily DefaultWrapper where
  compareStructural DefaultWrapper DefaultWrapper = StructuralEQ
  compareStructuralShape DefaultWrapper DefaultWrapper = EQ

instance StructuralWrapper DefaultWrapper where
  wrapValue DefaultWrapper = Default
  unwrapValue DefaultWrapper (Default value) = value

data GenericWrapper value payload where
  GenericWrapper ::
    (Generic value) =>
    GenericWrapper value (Rep value ())

instance StructuralFamily GenericWrapper where
  compareStructural GenericWrapper GenericWrapper = StructuralEQ
  compareStructuralShape GenericWrapper GenericWrapper = EQ

instance StructuralWrapper GenericWrapper where
  wrapValue GenericWrapper = to
  unwrapValue GenericWrapper = from

data Default1Wrapper value payload where
  Default1Wrapper :: Default1Wrapper (Default1 function argument) (function argument)

instance StructuralFamily Default1Wrapper where
  compareStructural Default1Wrapper Default1Wrapper = StructuralEQ
  compareStructuralShape Default1Wrapper Default1Wrapper = EQ

instance StructuralWrapper Default1Wrapper where
  wrapValue Default1Wrapper = Default1
  unwrapValue Default1Wrapper (Default1 value) = value

data Generic1Wrapper value payload where
  Generic1Wrapper ::
    (Generic1 function) =>
    Generic1Wrapper (function argument) (Rep1 function argument)

instance StructuralFamily Generic1Wrapper where
  compareStructural Generic1Wrapper Generic1Wrapper = StructuralEQ
  compareStructuralShape Generic1Wrapper Generic1Wrapper = EQ

instance StructuralWrapper Generic1Wrapper where
  wrapValue Generic1Wrapper = to1
  unwrapValue Generic1Wrapper = from1

instance GMergeable arity V1 where
  grootStrategy _ = SimpleStrategy (\_ t _ -> t)
  {-# INLINE grootStrategy #-}

instance GMergeable arity U1 where
  grootStrategy _ = SimpleStrategy (\_ t _ -> t)
  {-# INLINE grootStrategy #-}

instance
  (GMergeable arity a, GMergeable arity b) =>
  GMergeable arity (a :*: b)
  where
  grootStrategy args =
    product2Strategy
      GenericProductWrapper
      (grootStrategy args)
      (grootStrategy args)
  {-# INLINE grootStrategy #-}

data GenericSumFamily value payload where
  GenericLeftFamily :: GenericSumFamily ((f :+: g) p) (f p)
  GenericRightFamily :: GenericSumFamily ((f :+: g) p) (g p)

instance StructuralFamily GenericSumFamily where
  compareStructural GenericLeftFamily GenericLeftFamily = StructuralEQ
  compareStructural GenericLeftFamily GenericRightFamily = StructuralLT
  compareStructural GenericRightFamily GenericLeftFamily = StructuralGT
  compareStructural GenericRightFamily GenericRightFamily = StructuralEQ

  compareStructuralShape GenericLeftFamily GenericLeftFamily = EQ
  compareStructuralShape GenericLeftFamily GenericRightFamily = LT
  compareStructuralShape GenericRightFamily GenericLeftFamily = GT
  compareStructuralShape GenericRightFamily GenericRightFamily = EQ

instance
  (GMergeable arity a, GMergeable arity b) =>
  GMergeable arity (a :+: b)
  where
  grootStrategy (args :: MergeableArgs arity parameter) =
    StructuralStrategy splitSum payloadStrategy injectSum
    where
      splitSum
        :: (a :+: b) parameter
        -> StructuralCase GenericSumFamily ((a :+: b) parameter)
      splitSum (L1 value) = StructuralCase GenericLeftFamily value
      splitSum (R1 value) = StructuralCase GenericRightFamily value

      payloadStrategy
        :: forall payload.
           GenericSumFamily ((a :+: b) parameter) payload
        -> MergingStrategy payload
      payloadStrategy GenericLeftFamily = grootStrategy args
      payloadStrategy GenericRightFamily = grootStrategy args

      injectSum
        :: forall payload.
           GenericSumFamily ((a :+: b) parameter) payload
        -> payload
        -> (a :+: b) parameter
      injectSum GenericLeftFamily = L1
      injectSum GenericRightFamily = R1
  {-# INLINE grootStrategy #-}

instance (GMergeable arity a) => GMergeable arity (M1 i c a) where
  grootStrategy arg = wrapStrategy M1Wrapper (grootStrategy arg)
  {-# INLINE grootStrategy #-}

instance (Mergeable c) => GMergeable arity (K1 i c) where
  grootStrategy _ = wrapStrategy K1Wrapper rootStrategy
  {-# INLINE grootStrategy #-}

instance GMergeable Arity1 Par1 where
  grootStrategy (MergeableArgs1 strategy) = wrapStrategy Par1Wrapper strategy
  {-# INLINE grootStrategy #-}

instance (Mergeable1 f) => GMergeable Arity1 (Rec1 f) where
  grootStrategy (MergeableArgs1 m) =
    wrapStrategy Rec1Wrapper (liftRootStrategy m)
  {-# INLINE grootStrategy #-}

instance
  (Mergeable1 f, GMergeable Arity1 g) =>
  GMergeable Arity1 (f :.: g)
  where
  grootStrategy targs =
    wrapStrategy Comp1Wrapper (liftRootStrategy (grootStrategy targs))
  {-# INLINE grootStrategy #-}

instance (Generic a, GMergeable Arity0 (Rep a)) => Mergeable (Default a) where
  rootStrategy =
    wrapStrategy DefaultWrapper (genericRootStrategy :: MergingStrategy a)
  {-# INLINE rootStrategy #-}

-- | Generic 'rootStrategy'.
genericRootStrategy ::
  forall a.
  (Generic a, GMergeable Arity0 (Rep a)) => MergingStrategy a
genericRootStrategy =
  wrapStrategy
    GenericWrapper
    (grootStrategy MergeableArgs0 :: MergingStrategy (Rep a ()))
{-# INLINE genericRootStrategy #-}

instance
  (Generic1 f, GMergeable Arity1 (Rep1 f), Mergeable a) =>
  Mergeable (Default1 f a)
  where
  rootStrategy = rootStrategy1
  {-# INLINE rootStrategy #-}

instance (Generic1 f, GMergeable Arity1 (Rep1 f)) => Mergeable1 (Default1 f) where
  liftRootStrategy (m :: MergingStrategy a) =
    wrapStrategy
      Default1Wrapper
      (genericLiftRootStrategy m :: MergingStrategy (f a))
  {-# INLINE liftRootStrategy #-}

-- | Generic 'liftRootStrategy'.
genericLiftRootStrategy ::
  (Generic1 f, GMergeable Arity1 (Rep1 f)) =>
  MergingStrategy a ->
  MergingStrategy (f a)
genericLiftRootStrategy m =
  wrapStrategy Generic1Wrapper (grootStrategy $ MergeableArgs1 m)
{-# INLINE genericLiftRootStrategy #-}

-- | Helper type for combining arbitrary number of indices into one.
-- Useful when trying to write efficient merge strategy for lists/vectors.
data DynamicSortedIdx where
  DynamicSortedIdx :: forall idx. (MergingIndex idx) => idx -> DynamicSortedIdx
  DynamicStructuralIdx ::
    forall structuralFamily value payload.
    (StructuralFamily structuralFamily) =>
    structuralFamily value payload ->
    DynamicSortedIdx

instance Eq DynamicSortedIdx where
  (DynamicSortedIdx (a :: a)) == (DynamicSortedIdx (b :: b)) = case eqT @a @b of
    Just Refl -> a == b
    _ -> False
  (DynamicStructuralIdx (a :: leftFamily leftValue leftPayload))
    == (DynamicStructuralIdx (b :: rightFamily rightValue rightPayload)) =
      case eqT @leftFamily @rightFamily of
        Just Refl -> compareStructuralShape a b == EQ
        Nothing -> False
  _ == _ = False
  {-# INLINE (==) #-}

instance Ord DynamicSortedIdx where
  compare (DynamicSortedIdx (a :: a)) (DynamicSortedIdx (b :: b)) = case eqT @a @b of
    Just Refl -> compare a b
    Nothing ->
      compare
        (SomeTypeRep (typeRep @a))
        (SomeTypeRep (typeRep @b))
  compare DynamicSortedIdx {} DynamicStructuralIdx {} = LT
  compare DynamicStructuralIdx {} DynamicSortedIdx {} = GT
  compare
    (DynamicStructuralIdx (a :: leftFamily leftValue leftPayload))
    (DynamicStructuralIdx (b :: rightFamily rightValue rightPayload)) =
      case eqT @leftFamily @rightFamily of
        Just Refl -> compareStructuralShape a b
        Nothing ->
          compare
            (SomeTypeRep (typeRep @leftFamily))
            (SomeTypeRep (typeRep @rightFamily))
  {-# INLINE compare #-}

instance Show DynamicSortedIdx where
  show (DynamicSortedIdx _) = "DynamicSortedIdx"
  show (DynamicStructuralIdx _) = "DynamicStructuralIdx"

-- | A strategy resolved to a homogeneous terminal payload without erasing its
-- type. The injector reconstructs the original value from that payload.
data ResolvedStrategy value where
  ResolvedStrategy ::
    [DynamicSortedIdx] ->
    MergingStrategy payload ->
    payload ->
    (payload -> value) ->
    ResolvedStrategy value

-- | Resolves the indices and the terminal merge strategy for a value of some
-- 'Mergeable' type.
resolveStrategy ::
  forall x.
  MergingStrategy x ->
  x ->
  ResolvedStrategy x
resolveStrategy s x = resolveStrategy' x s
{-# INLINE resolveStrategy #-}

-- | Resolves the indices and the terminal merge strategy for a value given a
-- merge strategy for its type.
resolveStrategy' ::
  forall x. x -> MergingStrategy x -> ResolvedStrategy x
resolveStrategy' value (SortedStrategy index subStrategy) =
  case resolveStrategy' value (subStrategy selectedIndex) of
    ResolvedStrategy indices terminal payload inject ->
      ResolvedStrategy
        (DynamicSortedIdx selectedIndex : indices)
        terminal
        payload
        inject
  where
    selectedIndex = index value
resolveStrategy'
  value
  (StructuralStrategy split payloadStrategy injectStructural) =
    case split value of
      StructuralCase key structuralPayload ->
        case resolveStrategy' structuralPayload (payloadStrategy key) of
          ResolvedStrategy indices terminal payload injectPayload ->
            ResolvedStrategy
              (DynamicStructuralIdx key : indices)
              terminal
              payload
              (injectStructural key . injectPayload)
resolveStrategy'
  value
  ( StructuralStrategyInternal
      split
      _
      indexKey
      payloadStrategy
      injectStructural
    ) =
    case split value of
      StructuralStrategyCase key structuralPayload ->
        case resolveStrategy' structuralPayload (payloadStrategy key) of
          ResolvedStrategy indices terminal payload injectPayload ->
            ResolvedStrategy
              (indexKey key : indices)
              terminal
              payload
              (injectStructural key . injectPayload)
resolveStrategy' value strategy = ResolvedStrategy [] strategy value id
{-# INLINE resolveStrategy' #-}

instance Mergeable SymBool where
  rootStrategy = SimpleStrategy symIte

instance Mergeable Ordering where
  rootStrategy =
    let sub = SimpleStrategy $ \_ t _ -> t
     in SortedStrategy id $ const sub

data AsKeyWrapper value payload where
  AsKeyWrapper :: AsKeyWrapper (AsKey value) value

instance StructuralFamily AsKeyWrapper where
  compareStructural AsKeyWrapper AsKeyWrapper = StructuralEQ
  compareStructuralShape AsKeyWrapper AsKeyWrapper = EQ

instance StructuralWrapper AsKeyWrapper where
  wrapValue AsKeyWrapper = AsKey
  unwrapValue AsKeyWrapper = getAsKey

data AsKey1Wrapper value payload where
  AsKey1Wrapper :: AsKey1Wrapper (AsKey1 function value) (function value)

instance StructuralFamily AsKey1Wrapper where
  compareStructural AsKey1Wrapper AsKey1Wrapper = StructuralEQ
  compareStructuralShape AsKey1Wrapper AsKey1Wrapper = EQ

instance StructuralWrapper AsKey1Wrapper where
  wrapValue AsKey1Wrapper = AsKey1
  unwrapValue AsKey1Wrapper = getAsKey1

instance (Mergeable a) => Mergeable (AsKey a) where
  rootStrategy = wrapStrategy AsKeyWrapper (rootStrategy @a)
  {-# INLINE rootStrategy #-}

instance (Mergeable (f a)) => Mergeable (AsKey1 f a) where
  rootStrategy = wrapStrategy AsKey1Wrapper (rootStrategy @(f a))
  {-# INLINE rootStrategy #-}

instance (Mergeable1 f) => Mergeable1 (AsKey1 f) where
  liftRootStrategy (s :: MergingStrategy a) =
    wrapStrategy AsKey1Wrapper (liftRootStrategy s)
  {-# INLINE liftRootStrategy #-}
