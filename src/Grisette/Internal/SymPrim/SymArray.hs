{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveLift #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RoleAnnotations #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}

-- |
-- Module      :   Grisette.Internal.SymPrim.Array
-- Copyright   :   (c) Sirui Lu 2021-2023
-- License     :   BSD-3-Clause (see the LICENSE file)
--
-- Maintainer  :   siruilu@cs.washington.edu
-- Stability   :   Experimental
-- Portability :   GHC only
module Grisette.Internal.SymPrim.SymArray 
  ( SymArray (..)
  , const
  , select
  , selectThroughIte
  , PreparedSliceThroughIte
  , prepareSliceThroughIte
  , applyPreparedSliceThroughIte
  , PreparedSliceSelectThroughIte
  , prepareSliceSelectThroughIte
  , applyPreparedSliceSelectThroughIte
  , store
  ) where

import Control.DeepSeq (NFData)
import Data.Binary qualified as Binary
import Data.Bytes.Serial (Serial (deserialize, serialize))
import Data.Data (Proxy(Proxy))
import Data.Serialize qualified as Cereal
import Data.String (IsString (fromString))
import Grisette.Internal.SymPrim.Array (Array)
import Grisette.Internal.Core.Data.MemoUtils (weakStableMemo, weakStableMemo2)
import Grisette.Internal.SymPrim.Prim.Internal.Term
  ( Term
  , SupportedNonFuncPrim
  , ConRep (ConType)
  , SymRep (SymType)
  , LinkedRep (underlyingTerm, wrapTerm)
  , conTerm
  , pevalITETerm
  , pevalSelectTerm
  , PEvalBVTerm(pevalBVSelectTerm)
  , typedConstantSymbol
  , symTerm
  , pformatTerm
  , pattern ConTerm
  , pattern ITETerm
  , pattern SelectTerm
  , pattern StoreTerm
  , pattern ConstArrayTerm
  )
import Grisette.Internal.SymPrim.BV (WordN)
import Grisette.Internal.SymPrim.SymBV (SymWordN)
import Grisette.Internal.SymPrim.Prim.Internal.Serialize ()
import Grisette.Internal.Internal.Decl.SymPrim.AllSyms
  ( AllSyms (allSymsS),
    SomeSym (SomeSym),
  )
import Grisette.Internal.Core.Data.Class.Solvable (Solvable (con, sym, conView), ssym)
import GHC.Generics (Generic)
import GHC.TypeNats (KnownNat, Nat, type (+), type (<=))
import Language.Haskell.TH.Syntax (Lift)
import Prelude (Show (show), Maybe (Just, Nothing), (<$>), ($), (.))

newtype SymArray k v = SymArray { underlyingArrayTerm :: Term (Array (ConType k) (ConType v)) }
  deriving (Lift, NFData, Generic)

instance ConRep (SymArray k v) where
  type ConType (SymArray k v) = Array (ConType k) (ConType v)

instance (SupportedNonFuncPrim k, SupportedNonFuncPrim v) => SymRep (Array k v) where
  type SymType (Array k v) = SymArray (SymType k) (SymType v)

instance
  ( SupportedNonFuncPrim ck,
    SupportedNonFuncPrim cv,
    LinkedRep ck sk,
    LinkedRep cv sv
  ) =>
  LinkedRep (Array ck cv) (SymArray sk sv) where
  underlyingTerm = underlyingArrayTerm
  wrapTerm = SymArray

instance
  ( SupportedNonFuncPrim ck,
    SupportedNonFuncPrim cv,
    LinkedRep ck sk,
    LinkedRep cv sv
  ) =>
  Solvable (Array ck cv) (SymArray sk sv) where
  con = wrapTerm . conTerm
  sym = wrapTerm . symTerm . typedConstantSymbol
  conView v = case underlyingTerm v of
    ConTerm t -> Just t
    _ -> Nothing

-- A symbolic array is a single SMT primitive (like a symbolic function), so it
-- contributes exactly itself to the list of symbolic primitives.
instance
  ( SupportedNonFuncPrim ck,
    SupportedNonFuncPrim cv,
    LinkedRep ck sk,
    LinkedRep cv sv
  ) =>
  AllSyms (SymArray sk sv) where
  allSymsS v = (SomeSym v :)

instance
  ( SupportedNonFuncPrim ck,
    SupportedNonFuncPrim cv,
    LinkedRep ck sk,
    LinkedRep cv sv
  ) =>
  IsString (SymArray sk sv) where
  fromString = ssym . fromString

instance Show (SymArray sk sv) where
  show = pformatTerm . underlyingArrayTerm

instance
  ( SupportedNonFuncPrim ck,
    SupportedNonFuncPrim cv,
    LinkedRep ck sk,
    LinkedRep cv sv
  ) =>
  Serial (SymArray sk sv) where
  serialize = serialize . underlyingTerm
  deserialize = wrapTerm <$> deserialize

instance
  ( SupportedNonFuncPrim ck,
    SupportedNonFuncPrim cv,
    LinkedRep ck sk,
    LinkedRep cv sv
  ) =>
  Cereal.Serialize (SymArray sk sv) where
  put = serialize
  get = deserialize

instance
  ( SupportedNonFuncPrim ck,
    SupportedNonFuncPrim cv,
    LinkedRep ck sk,
    LinkedRep cv sv
  ) =>
  Binary.Binary (SymArray sk sv) where
  put = serialize
  get = deserialize

const
  :: forall k v
   . SupportedNonFuncPrim (ConType k)
  => SupportedNonFuncPrim (ConType v)
  => LinkedRep (ConType k) k
  => LinkedRep (ConType v) v
  => v
  -> SymArray k v
const val = wrapTerm $ ConstArrayTerm Proxy (underlyingTerm val)

select
  :: forall k v
   . SupportedNonFuncPrim (ConType k)
  => SupportedNonFuncPrim (ConType v)
  => LinkedRep (ConType k) k
  => LinkedRep (ConType v) v
  => SymArray k v
  -> k
  -> v
select arr key = wrapTerm $ SelectTerm (underlyingTerm arr) (underlyingTerm key)

-- | Read an array after pushing only an array-valued choice through the read.
--
-- This is deliberately opt-in.  Globally distributing every array read would
-- grow unrelated terms, while physical column stores need the focused law
--
-- @select (ite c l r) k = ite c (select l k) (select r k)@.
--
-- The weak table is keyed by the two input term identities.  It shares repeated
-- reads at committed reconvergence points without retaining otherwise-dead
-- terms that Grisette's interning layer is able to reclaim.
selectThroughIte
  :: forall k v
   . SupportedNonFuncPrim (ConType k)
  => SupportedNonFuncPrim (ConType v)
  => LinkedRep (ConType k) k
  => LinkedRep (ConType v) v
  => SymArray k v
  -> k
  -> v
selectThroughIte array key = wrapTerm $
  selectThroughIteTerm (underlyingTerm array) (underlyingTerm key)

selectThroughIteTerm
  :: forall k v
   . (SupportedNonFuncPrim k, SupportedNonFuncPrim v)
  => Term (Array k v)
  -> Term k
  -> Term v
selectThroughIteTerm = weakStableMemo2 selectThroughIteTermUncached
{-# NOINLINE selectThroughIteTerm #-}

selectThroughIteTermUncached
  :: forall k v
   . (SupportedNonFuncPrim k, SupportedNonFuncPrim v)
  => Term (Array k v)
  -> Term k
  -> Term v
selectThroughIteTermUncached array key = case array of
  ITETerm condition left right ->
    pevalITETerm
      condition
      (selectThroughIteTerm left key)
      (selectThroughIteTerm right key)
  _ -> pevalSelectTerm array key

-- | A focused packed-value slice prepared for one statically known range.
-- The recursive worker distributes through value ITEs before slicing their
-- arms.  Its weak table is allocated once with the prepared physical split, so
-- repeated runtime reads neither rebuild a normalizer nor retain dead terms.
newtype PreparedSliceThroughIte
    (total :: Nat) (offset :: Nat) (width :: Nat) =
  PreparedSliceThroughIte (SymWordN total -> SymWordN width)

type role PreparedSliceThroughIte nominal nominal nominal

-- | Prepare one focused packed-value slice.
prepareSliceThroughIte
  :: forall offset width total
   . ( KnownNat total
     , KnownNat offset
     , KnownNat width
     , 1 <= total
     , 1 <= width
     , offset + width <= total
     )
  => Proxy offset
  -> Proxy width
  -> PreparedSliceThroughIte total offset width
prepareSliceThroughIte offset width = PreparedSliceThroughIte $ \value ->
  wrapTerm $ memoized (underlyingTerm value)
  where
    memoized :: Term (WordN total) -> Term (WordN width)
    memoized = weakStableMemo worker
    {-# NOINLINE memoized #-}

    worker value = case value of
      ITETerm condition left right ->
        pevalITETerm condition (memoized left) (memoized right)
      _ -> pevalBVSelectTerm offset width value
{-# NOINLINE prepareSliceThroughIte #-}

-- | Apply a retained focused packed-value slice.
applyPreparedSliceThroughIte
  :: PreparedSliceThroughIte total offset width
  -> SymWordN total
  -> SymWordN width
applyPreparedSliceThroughIte (PreparedSliceThroughIte apply) = apply

-- | A fused focused read/slice normalizer prepared for one statically known
-- packed-field slice.  Its weak table and recursive worker are allocated once
-- with the prepared field plan; runtime reads only apply this retained closure.
newtype PreparedSliceSelectThroughIte key
    (total :: Nat) (offset :: Nat) (width :: Nat) =
  PreparedSliceSelectThroughIte
    (SymArray key (SymWordN total) -> key -> SymWordN width)

type role PreparedSliceSelectThroughIte nominal nominal nominal nominal

-- | Prepare one focused packed-field read.  The recursive worker closes over
-- the exact memoized self, so every recursive and repeated read shares the same
-- weak term-identity table.  The proxy values are used only to select the
-- retained type dictionaries and are never memoization keys.
prepareSliceSelectThroughIte
  :: forall offset width key total
   . ( KnownNat total
     , KnownNat offset
     , KnownNat width
     , 1 <= total
     , 1 <= width
     , offset + width <= total
     , SupportedNonFuncPrim (ConType key)
     , LinkedRep (ConType key) key
     )
  => Proxy offset
  -> Proxy width
  -> PreparedSliceSelectThroughIte key total offset width
prepareSliceSelectThroughIte offset width =
  PreparedSliceSelectThroughIte $ \array key -> wrapTerm $
    memoized (underlyingTerm array) (underlyingTerm key)
  where
    memoized
      :: Term (Array (ConType key) (WordN total))
      -> Term (ConType key)
      -> Term (WordN width)
    memoized = weakStableMemo2 worker
    {-# NOINLINE memoized #-}

    worker array key = case array of
      ITETerm condition left right ->
        pevalITETerm condition (memoized left key) (memoized right key)
      _ -> pevalBVSelectTerm offset width (pevalSelectTerm array key)
{-# NOINLINE prepareSliceSelectThroughIte #-}

-- | Apply a retained focused packed-field read.
applyPreparedSliceSelectThroughIte
  :: PreparedSliceSelectThroughIte key total offset width
  -> SymArray key (SymWordN total)
  -> key
  -> SymWordN width
applyPreparedSliceSelectThroughIte (PreparedSliceSelectThroughIte apply) = apply

store
  :: forall k v
   . SupportedNonFuncPrim (ConType k)
  => SupportedNonFuncPrim (ConType v)
  => LinkedRep (ConType k) k
  => LinkedRep (ConType v) v
  => SymArray k v
  -> k
  -> v
  -> SymArray k v
store arr key val = do
  wrapTerm $ StoreTerm (underlyingTerm arr) (underlyingTerm key) (underlyingTerm val)
