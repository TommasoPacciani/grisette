{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveLift #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

-- |
-- Module      :   Grisette.Internal.SymPrim.Uninterp
-- Copyright   :   (c) Sirui Lu 2021-2023
-- License     :   BSD-3-Clause (see the LICENSE file)
--
-- Maintainer  :   siruilu@cs.washington.edu
-- Stability   :   Experimental
-- Portability :   GHC only
module Grisette.Internal.SymPrim.Uninterp
  ( Uninterp (..),
    uninterpConSBVPrefix,
  )
where

import Control.DeepSeq (NFData)
import Data.Binary qualified as Binary
import Data.Bytes.Serial (Serial (deserialize, serialize))
import Data.Hashable (Hashable)
import Data.Proxy (Proxy (Proxy))
import Data.SBV.Internals
  ( CV (CV),
    CVal (CADT),
    HasKind (kindOf),
    Kind (KADT),
    SatModel (parseCVs),
    SymVal (fromCV, literal, minMaxBound),
  )
import Data.Serialize qualified as Cereal
import GHC.Generics (Generic)
import GHC.TypeLits (KnownSymbol, Symbol, symbolVal)
import Language.Haskell.TH.Syntax (Lift)
import Test.QuickCheck (Arbitrary (arbitrary))

-- | Concrete carrier for a first-class /uninterpreted/ (abstract) SMT sort,
-- named at the type level by @n@. An inhabitant denotes an opaque first-order
-- identity — the only operations are fresh-symbol creation, equality, and use
-- as an uninterpreted-function argument. There is no arithmetic, ordering, or
-- bit-indexing, so the solver cannot exploit any structure the identity does
-- not have.
--
-- The type-level name @n@ keeps distinct opaque domains un-mixable: @Uninterp
-- \"payload\"@ and @Uninterp \"flowId\"@ are different Haskell types that lower
-- to different SMT sorts, so equating them is a type error rather than a silent
-- cross-domain confusion.
--
-- The 'String' payload is the opaque model-element tag (e.g. @\"payload_0\"@)
-- SBV reports for a member of the sort; it is only ever produced by model
-- read-back ('fromCV' \/ 'parseCVs'), never written by the user. The
-- t'HasKind' instance is what makes SBV treat the sort as opaque: it returns
-- @'KADT' name [] []@ (empty parameters, empty constructors), which SBV's
-- @isUninterpreted@ recognises and lowers to @(declare-sort name 0)@.
newtype Uninterp (n :: Symbol) = Uninterp String
  deriving stock (Show, Eq, Ord, Generic, Lift)
  deriving newtype (Hashable, NFData)

-- | Name prefix for the nullary uninterpreted SBV constant a concrete opaque
-- element lowers to (see the @conSBVTerm@ of the @SupportedPrim (Uninterp n)@
-- instance). Such constants are introduced internally — e.g. by
-- @funcDummyConstraint@ pinning a UF over the sort — and denote an arbitrary,
-- unnamed element, so they are dropped from solver-model read-back rather than
-- surfaced as user symbols (see @parseModel@ in @Grisette.Internal.Backend.Solving@).
uninterpConSBVPrefix :: String
uninterpConSBVPrefix = "grisette.uninterp.con."

instance (KnownSymbol n) => Serial (Uninterp n) where
  serialize (Uninterp s) = serialize s
  deserialize = Uninterp <$> deserialize

instance (KnownSymbol n) => Cereal.Serialize (Uninterp n) where
  put = serialize
  get = deserialize

instance (KnownSymbol n) => Binary.Binary (Uninterp n) where
  put = serialize
  get = deserialize

-- | The sort lowers to the empty-ADT SBV kind @KADT name [] []@, which SBV
-- recognises as an uninterpreted sort (fresh constants, equality\/distinct, and
-- UF-argument use only). The name is the type-level 'Symbol'.
instance (KnownSymbol n) => HasKind (Uninterp n) where
  kindOf _ = KADT (symbolVal (Proxy @n)) [] []

-- | An uninterpreted sort has no writable literals: 'literal' is unreachable
-- (mirrors SBV's own derived @literal@ stub for empty ADTs), because the sort
-- is never lowered from a concrete term. 'fromCV' decodes an opaque model
-- element (an empty-field ADT constructor) into its tag.
instance (KnownSymbol n) => SymVal (Uninterp n) where
  literal =
    error
      "Grisette.Internal.SymPrim.Uninterp: an uninterpreted sort has no \
      \literal; it is opaque and is never lowered from a concrete value."
  fromCV (CV _ (CADT (tag, []))) = Uninterp tag
  fromCV cv =
    error $
      "Grisette.Internal.SymPrim.Uninterp.fromCV: expected an opaque sort \
      \element (a zero-field ADT constructor), but got: "
        <> show cv

  -- An opaque sort is unordered and unbounded: no least/greatest element.
  minMaxBound = Nothing

instance (KnownSymbol n) => SatModel (Uninterp n) where
  parseCVs (CV _ (CADT (tag, [])) : rest) = Just (Uninterp tag, rest)
  parseCVs _ = Nothing

-- | Required by the 'SymVal' superclass; only used by QuickCheck-driven random
-- concrete generation, which is meaningless for an opaque identity.
instance (KnownSymbol n) => Arbitrary (Uninterp n) where
  arbitrary =
    error
      "Grisette.Internal.SymPrim.Uninterp: cannot generate an arbitrary \
      \concrete value for an uninterpreted sort."
