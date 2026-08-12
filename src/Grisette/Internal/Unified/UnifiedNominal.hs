{-# LANGUAGE GHC2024 #-}
{-# LANGUAGE TypeFamilyDependencies #-}

-- |
-- Module      :   Grisette.Internal.Unified.UnifiedNominal
-- Copyright   :   (c) Sirui Lu 2021-2024
-- License     :   BSD-3-Clause (see the LICENSE file)
--
-- Mode-polymorphic solver-erased nominal values.
module Grisette.Internal.Unified.UnifiedNominal
  ( NominalBase,
    GetNominal,
    NominalValue,
    UnifiedNominal (..),
  )
where

import Grisette.Internal.SymPrim.Nominal
  ( KnownNominalDomain,
    Nominal (Nominal),
    NominalDomain,
    unNominal,
  )
import Grisette.Internal.SymPrim.Prim.Term
  ( LinkedRep (underlyingTerm, wrapTerm),
    PEvalBitCastTerm (pevalBitCastTerm),
    SupportedNonFuncPrim,
    SymRep (SymType),
  )
import Grisette.Internal.SymPrim.SymNominal
  ( SymNominal (SymNominal),
  )
import Grisette.Internal.Unified.EvalModeTag (EvalModeTag (C, S))

-- | Underlying value in an evaluation mode.
type family NominalBase (mode :: EvalModeTag) value where
  NominalBase 'C value = value
  NominalBase 'S value = SymType value

-- | A nominal value in an evaluation mode.
type family
  GetNominal (mode :: EvalModeTag) (domain :: NominalDomain) value = result
    | result -> mode domain value
  where
  GetNominal 'C domain value = Nominal domain value
  GetNominal 'S domain value = SymNominal domain value

-- | The underlying leaf must already have Grisette's ordinary concrete and
-- symbolic representations.
type NominalValue value =
  ( SupportedNonFuncPrim value,
    LinkedRep value (SymType value)
  )

-- | Wrap and unwrap a domain without adding an SMT coordinate.
class UnifiedNominal (mode :: EvalModeTag) where
  nominal ::
    (KnownNominalDomain domain, NominalValue value) =>
    NominalBase mode value ->
    GetNominal mode domain value
  nominalValue ::
    (KnownNominalDomain domain, NominalValue value) =>
    GetNominal mode domain value ->
    NominalBase mode value

instance UnifiedNominal 'C where
  nominal = Nominal
  nominalValue = unNominal

instance UnifiedNominal 'S where
  nominal value = SymNominal $ pevalBitCastTerm $ underlyingTerm value
  nominalValue (SymNominal value) = wrapTerm $ pevalBitCastTerm value
