{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveLift #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

-- |
-- Module      :   Grisette.Internal.SymPrim.SymUninterp
-- Copyright   :   (c) Sirui Lu 2021-2023
-- License     :   BSD-3-Clause (see the LICENSE file)
--
-- Maintainer  :   siruilu@cs.washington.edu
-- Stability   :   Experimental
-- Portability :   GHC only
module Grisette.Internal.SymPrim.SymUninterp
  ( SymUninterp (..),
  )
where

import Control.DeepSeq (NFData)
import Data.Binary qualified as Binary
import Data.Bytes.Serial (Serial (deserialize, serialize))
import Data.String (IsString (fromString))
import GHC.Generics (Generic)
import GHC.TypeLits (KnownSymbol, Symbol)
import Grisette.Internal.Core.Data.Class.Solvable
  ( Solvable (con, conView, ssym, sym),
  )
import Grisette.Internal.Internal.Decl.SymPrim.AllSyms
  ( AllSyms (allSymsS),
    SomeSym (SomeSym),
  )
import Grisette.Internal.SymPrim.Prim.Term
  ( ConRep (ConType),
    LinkedRep (underlyingTerm, wrapTerm),
    SymRep (SymType),
    Term,
    conTerm,
    pformatTerm,
    symTerm,
    typedConstantSymbol,
    pattern ConTerm,
  )
import Grisette.Internal.SymPrim.Uninterp (Uninterp)
import Data.Serialize qualified as Cereal
import Language.Haskell.TH.Syntax (Lift)

-- | Symbolic value of a first-class /uninterpreted/ (abstract) SMT sort, named
-- at the type level by @n@ (see 'Grisette.Internal.SymPrim.Uninterp.Uninterp').
--
-- It is an opaque first-order identity: the only operations are fresh-symbol
-- creation ('ssym' \/ 'sym'), symbolic equality ('Grisette.Core.SymEq'), and
-- use as an uninterpreted-function argument. There is deliberately no @Num@,
-- @SymOrd@, or bit-indexing — the solver cannot exploit structure the identity
-- does not have. Distinct type-level names denote distinct SMT sorts, so
-- @SymUninterp \"payload\"@ and @SymUninterp \"flowId\"@ cannot be compared.
newtype SymUninterp (n :: Symbol) = SymUninterp
  { underlyingUninterpTerm :: Term (Uninterp n)
  }
  deriving (Lift, NFData, Generic)

instance ConRep (SymUninterp n) where
  type ConType (SymUninterp n) = Uninterp n

instance (KnownSymbol n) => SymRep (Uninterp n) where
  type SymType (Uninterp n) = SymUninterp n

instance (KnownSymbol n) => LinkedRep (Uninterp n) (SymUninterp n) where
  underlyingTerm = underlyingUninterpTerm
  wrapTerm = SymUninterp

instance (KnownSymbol n) => Solvable (Uninterp n) (SymUninterp n) where
  con = SymUninterp . conTerm
  sym = SymUninterp . symTerm . typedConstantSymbol
  conView (SymUninterp (ConTerm t)) = Just t
  conView _ = Nothing

-- A symbolic uninterpreted-sort value is a single SMT primitive, so it
-- contributes exactly itself to the list of symbolic primitives.
instance (KnownSymbol n) => AllSyms (SymUninterp n) where
  allSymsS v = (SomeSym v :)

instance (KnownSymbol n) => IsString (SymUninterp n) where
  fromString = ssym . fromString

instance Show (SymUninterp n) where
  show = pformatTerm . underlyingUninterpTerm

instance (KnownSymbol n) => Serial (SymUninterp n) where
  serialize = serialize . underlyingUninterpTerm
  deserialize = SymUninterp <$> deserialize

instance (KnownSymbol n) => Cereal.Serialize (SymUninterp n) where
  put = serialize
  get = deserialize

instance (KnownSymbol n) => Binary.Binary (SymUninterp n) where
  put = serialize
  get = deserialize
