{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveLift #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE ExplicitForAll #-}
{-# LANGUAGE ImportQualifiedPost #-}

-- |
-- Module      :   Grisette.Internal.SymPrim.Array
-- Copyright   :   (c) Sirui Lu 2021-2023
-- License     :   BSD-3-Clause (see the LICENSE file)
--
-- Maintainer  :   siruilu@cs.washington.edu
-- Stability   :   Experimental
-- Portability :   GHC only
module Grisette.Internal.SymPrim.Array
  ( Array (..)
  , const
  , select
  , store
  ) where

import Control.DeepSeq (NFData)
import Data.Binary qualified as Binary
import Data.Bytes.Serial (Serial (serialize, deserialize))
import Data.Hashable (Hashable)
import Data.HashMap.Strict qualified as HM
import Data.Serialize qualified as Cereal
import GHC.Generics (Generic)
import Language.Haskell.TH.Syntax (Lift)
import Prelude (Show, Eq, Ord)

-- | Concrete model of a symbolic array: a finite map of overrides over a
-- default ("everything else") value. Mirrors SBV's @ArrayModel@ and the SMT
-- theory of arrays (@select@/@store@/@const@).
--
-- NOTE on equality: the derived 'Eq'/'Ord'/'Hashable' here are /structural/ and
-- therefore non-canonical — two values denoting the same array can differ
-- structurally (an override whose value equals the default, or, on finite key
-- domains, different defaults fully masked by overrides). This structural
-- instance is used only for term interning (where being conservative merely
-- reduces sharing and is always sound). Symbolic equality of arrays does NOT
-- rely on it: 'Grisette.Internal.SymPrim.Prim.Internal.Term.pevalArrayEqTerm'
-- never concrete-folds distinct arrays to unequal and defers to the solver's
-- extensional (object) array equality. Do not rely on this structural 'Eq' for
-- deciding semantic equality of concrete arrays on finite key domains.
data Array k v = Array (HM.HashMap k v) v
  deriving (Show, Eq, Ord, Generic, Lift, Hashable, NFData)

instance (Hashable k, Serial k, Serial v) => Serial (Array k v)

instance (Hashable k, Serial k, Serial v) => Cereal.Serialize (Array k v) where
  put = serialize
  get = deserialize

instance (Hashable k, Serial k, Serial v) => Binary.Binary (Array k v) where
  put = serialize
  get = deserialize

-- TODO: Perhaps it is nice to make this a typeclass and give it names that do
-- not require qualified imports? I don't necessarily mind the qualified import,
-- but we'll see what the library author thinks.
const :: forall k v. v -> Array k v
const = Array HM.empty

select :: forall k v. Hashable k => Array k v -> k -> v
select (Array entries root) key = HM.lookupDefault root key entries

store :: forall k v. Hashable k => Array k v -> k -> v -> Array k v
store (Array entries root) key value = do
  let entries' = HM.insert key value entries
  Array entries' root
