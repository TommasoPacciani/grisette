{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

-- |
-- Module      :   Grisette.Internal.Unified.UnifiedArray
-- Copyright   :   (c) Sirui Lu 2024
-- License     :   BSD-3-Clause (see the LICENSE file)
--
-- Maintainer  :   siruilu@cs.washington.edu
-- Stability   :   Experimental
-- Portability :   GHC only
module Grisette.Internal.Unified.UnifiedArray
  ( GetArray,
    UnifiedArray (..),
    UnifiedArrayConstraint,
  )
where

import Data.Hashable (Hashable)
import Grisette.Internal.Core.Data.Class.Mergeable (Mergeable)
import Grisette.Internal.SymPrim.Array (Array)
import qualified Grisette.Internal.SymPrim.Array as CArr
import Grisette.Internal.SymPrim.Prim.Term
  ( ConRep (ConType),
    LinkedRep,
    SupportedNonFuncPrim,
  )
import Grisette.Internal.SymPrim.SymArray (SymArray)
import qualified Grisette.Internal.SymPrim.SymArray as SArr
import Grisette.Internal.Unified.Class.UnifiedITEOp (UnifiedITEOp)
import Grisette.Internal.Unified.Class.UnifiedSimpleMergeable
  ( UnifiedSimpleMergeable,
  )
import Grisette.Internal.Unified.Class.UnifiedSymEq (UnifiedSymEq)
import Grisette.Internal.Unified.EvalModeTag (EvalModeTag (C, S))

-- | Unified array type, the SMT theory of arrays under a unified evaluation
-- mode. Resolves to a concrete 'Grisette.Internal.SymPrim.Array.Array' in 'C'
-- mode, and a symbolic 'Grisette.Internal.SymPrim.SymArray.SymArray' in 'S'
-- mode.
--
-- When imported through "Grisette.Unified" the type is exposed /abstractly/:
-- only the canonicalizing smart constructors 'constArray'/'storeArray' (and the
-- reader 'selectArray') are available, never the raw data constructors. Unified
-- arrays are therefore always in canonical form, so equality (and concrete
-- 'C-mode '==') is extensional under the uniform-default invariant.
type family GetArray (mode :: EvalModeTag) k v = arr | arr -> mode k v where
  GetArray 'C k v = Array k v
  GetArray 'S k v = SymArray k v

-- | Mode-polymorphic array operations (the SMT theory of arrays:
-- @const@/@select@/@store@). The 'C-mode instance uses the concrete, canonical
-- array; the 'S-mode instance uses the symbolic array term.
class UnifiedArray (mode :: EvalModeTag) k v where
  -- | A constant array mapping every key to the given value.
  constArray :: v -> GetArray mode k v

  -- | Read the value stored at a key.
  selectArray :: GetArray mode k v -> k -> v

  -- | Write a value at a key. Writing a value equal to the array's default is
  -- canonicalized away, so the representation stays canonical.
  storeArray :: GetArray mode k v -> k -> v -> GetArray mode k v

instance (Hashable k, Eq v) => UnifiedArray 'C k v where
  constArray = CArr.const
  selectArray = CArr.select
  storeArray = CArr.store
  {-# INLINE constArray #-}
  {-# INLINE selectArray #-}
  {-# INLINE storeArray #-}

instance
  ( SupportedNonFuncPrim (ConType k),
    SupportedNonFuncPrim (ConType v),
    LinkedRep (ConType k) k,
    LinkedRep (ConType v) v
  ) =>
  UnifiedArray 'S k v
  where
  constArray = SArr.const
  selectArray = SArr.select
  storeArray = SArr.store
  {-# INLINE constArray #-}
  {-# INLINE selectArray #-}
  {-# INLINE storeArray #-}

-- | The constraint for a fully-featured unified array: the array operations
-- plus unified equality, if-then-else, and mergeability. With this in scope a
-- value containing a @GetArray mode k v@ can be compared with
-- 'Grisette.Unified..==', branched with unified if-then-else, and merged in
-- either mode.
type UnifiedArrayConstraint mode k v =
  ( UnifiedArray mode k v,
    Mergeable (GetArray mode k v),
    UnifiedSymEq mode (GetArray mode k v),
    UnifiedITEOp mode (GetArray mode k v),
    UnifiedSimpleMergeable mode (GetArray mode k v)
  )
