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
import Prelude (Show, Eq ((==)), Ord)

-- | Concrete model of a symbolic array: a finite map of overrides over a
-- default ("everything else") value. Mirrors SBV's @ArrayModel@ and the SMT
-- theory of arrays (@select@/@store@/@const@).
--
-- CANONICAL FORM. The smart constructors 'const' and 'store' (and model
-- decoding, @sbvToCon@) maintain the invariant that no override entry holds a
-- value equal to the default. With that invariant, two arrays that share a
-- default denote the same function iff they are structurally equal, so the
-- derived 'Eq'/'Ord'/'Hashable' coincide with semantic (extensional) equality
-- for same-default arrays — which is what concrete-mode register-state equality
-- relies on. Keeping the derived instances (rather than a hand-written semantic
-- 'Eq') also keeps 'Eq' and 'Hashable' mutually consistent, which term interning
-- depends on.
--
-- Residual: on a /finite/ key domain, two arrays with /different/ defaults whose
-- overrides cover the whole domain are extensionally equal yet structurally
-- distinct (the derived 'Eq' reports them unequal — a conservative
-- false-negative). This cannot arise under the uniform-default invariant
-- (register states being compared share one default), and in symbolic mode the
-- solver decides it extensionally (see @svArrEqual@ in the sbv backend and
-- @pevalArrayEqTerm@). The raw 'Array' constructor does /not/ canonicalize; build
-- through 'const'/'store' (the unified layer exposes only those).
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

store :: forall k v. (Hashable k, Eq v) => Array k v -> k -> v -> Array k v
store (Array entries root) key value =
  -- Canonicalize: an override equal to the default is dropped, so the
  -- representation never distinguishes @store a k (default a)@ from @a@.
  if value == root
    then Array (HM.delete key entries) root
    else Array (HM.insert key value entries) root
