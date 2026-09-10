{-# LANGUAGE GHC2024 #-}
{-# LANGUAGE PatternSynonyms #-}
-- Existing FP instance constraints relate the bit width through type families.
{-# LANGUAGE UndecidableInstances #-}

-- |
-- Module      :   Grisette.Internal.SymPrim.Prim.Internal.Instances.PEvalBitCastTerm
-- Copyright   :   (c) Sirui Lu 2024
-- License     :   BSD-3-Clause (see the LICENSE file)
--
-- Maintainer  :   siruilu@cs.washington.edu
-- Stability   :   Experimental
-- Portability :   GHC only
module Grisette.Internal.SymPrim.Prim.Internal.Instances.PEvalBitCastTerm
  ( doPevalBitCast,
  )
where

import qualified Data.SBV as SBV
import GHC.TypeLits (KnownNat, type (+), type (<=))
import Grisette.Internal.Core.Data.Class.BitCast
  ( BitCast (bitCast),
    BitCastOr (bitCastOr),
  )
import Grisette.Internal.Core.Data.MemoUtils (weakStableMemo)
import Grisette.Internal.SymPrim.BV (IntN, WordN)
import Grisette.Internal.SymPrim.FP (FP, ValidFP, withValidFPProofs)
import Grisette.Internal.SymPrim.Nominal
  ( KnownNominalDomain,
    Nominal,
  )
import Grisette.Internal.SymPrim.Prim.Internal.Term
  ( PEvalBitCastOrTerm (pevalBitCastOrTerm, sbvBitCastOr),
    PEvalBitCastTerm (pevalBitCastTerm, sbvBitCast),
    SupportedPrim (pevalITETerm),
    SupportedNonFuncPrim,
    Term,
    bitCastOrTerm,
    bitCastTerm,
    conTerm,
    pattern BitCastTerm,
    pattern ConTerm,
    pattern DynTerm,
    pattern ITETerm,
    pattern SupportedTerm,
  )
import Grisette.Internal.SymPrim.Prim.Internal.Unfold
  ( binaryUnfoldOnce,
    unaryUnfoldOnce,
  )

doPevalBitCastSameType ::
  forall x b. (SupportedPrim b) => Term x -> Maybe (Term b)
doPevalBitCastSameType (BitCastTerm (DynTerm (b :: Term b))) = Just b
doPevalBitCastSameType (BitCastTerm x) = doPevalBitCastSameType x
doPevalBitCastSameType _ = Nothing

-- | Partially evaluate a bitcast term. If no reduction is performed, return
-- Nothing.
doPevalBitCast :: (PEvalBitCastTerm a b, SupportedPrim b) => Term a -> Maybe (Term b)
doPevalBitCast (ConTerm v) = Just $ conTerm $ bitCast v
doPevalBitCast t = doPevalBitCastSameType t

pevalBitCastGeneral ::
  forall a b.
  (PEvalBitCastTerm a b, SupportedPrim b) =>
  Term a ->
  Term b
pevalBitCastGeneral = unaryUnfoldOnce doPevalBitCast bitCastTerm

instance
  (KnownNominalDomain domain, SupportedNonFuncPrim value) =>
  PEvalBitCastTerm value (Nominal domain value)
  where
  pevalBitCastTerm = pevalBitCastGeneral
  sbvBitCast = id

instance
  (KnownNominalDomain domain, SupportedNonFuncPrim value) =>
  PEvalBitCastTerm (Nominal domain value) value
  where
  pevalBitCastTerm = pevalBitCastGeneral
  sbvBitCast = id

doPevalBitCastOr ::
  (PEvalBitCastOrTerm a b) =>
  Term b ->
  Term a ->
  Maybe (Term b)
doPevalBitCastOr (ConTerm d) (ConTerm v) =
  Just $ conTerm $ bitCastOr d v
doPevalBitCastOr _ _ = Nothing

pevalBitCastOr ::
  forall a b.
  (PEvalBitCastOrTerm a b) =>
  Term b ->
  Term a ->
  Term b
pevalBitCastOr d@SupportedTerm =
  binaryUnfoldOnce doPevalBitCastOr bitCastOrTerm d

instance PEvalBitCastTerm Bool (IntN 1) where
  pevalBitCastTerm = pevalBitCastGeneral
  sbvBitCast x = SBV.ite x (SBV.literal 1) (SBV.literal 0)

instance PEvalBitCastTerm Bool (WordN 1) where
  pevalBitCastTerm = pevalBitCastGeneral
  sbvBitCast x = SBV.ite x (SBV.literal 1) (SBV.literal 0)

instance PEvalBitCastTerm (IntN 1) Bool where
  pevalBitCastTerm = pevalInt1ToBool
  sbvBitCast x = SBV.sTestBit x 0

instance PEvalBitCastTerm (WordN 1) Bool where
  pevalBitCastTerm = pevalWord1ToBool
  sbvBitCast x = SBV.sTestBit x 0

-- One-bit Boolean views must expose the whole choice DAG, including balanced
-- choices whose immediate branches are both ITEs. This unary elimination
-- creates no cross-product of alternatives. Monomorphic roots retain the weak
-- memo independently of class dictionaries and share common subexpressions.
pevalBoolChoice :: (Term a -> Term Bool) -> Term a -> Term Bool
pevalBoolChoice leaf = go
  where
    go = weakStableMemo $ \value -> case value of
      ITETerm condition selected fallback ->
        pevalITETerm condition (go selected) (go fallback)
      _ -> leaf value

pevalInt1ToBool :: Term (IntN 1) -> Term Bool
pevalInt1ToBool = pevalBoolChoice pevalBitCastGeneral
{-# NOINLINE pevalInt1ToBool #-}

pevalWord1ToBool :: Term (WordN 1) -> Term Bool
pevalWord1ToBool = pevalBoolChoice pevalBitCastGeneral
{-# NOINLINE pevalWord1ToBool #-}

instance
  (n ~ (eb + sb), ValidFP eb sb, KnownNat n, 1 <= n) =>
  PEvalBitCastTerm (WordN n) (FP eb sb)
  where
  pevalBitCastTerm = pevalBitCastGeneral
  sbvBitCast = withValidFPProofs @eb @sb $ SBV.sWordAsSFloatingPoint

instance
  (n ~ (eb + sb), ValidFP eb sb, KnownNat n, 1 <= n) =>
  PEvalBitCastTerm (IntN n) (FP eb sb)
  where
  pevalBitCastTerm = pevalBitCastGeneral
  sbvBitCast =
    withValidFPProofs @eb @sb $ SBV.sWordAsSFloatingPoint . SBV.sFromIntegral

instance
  (n ~ (eb + sb), ValidFP eb sb, KnownNat n, 1 <= n) =>
  PEvalBitCastOrTerm (FP eb sb) (WordN n)
  where
  pevalBitCastOrTerm = pevalBitCastOr
  sbvBitCastOr d v =
    withValidFPProofs @eb @sb $
      SBV.ite
        (SBV.fpIsNaN v)
        d
        (SBV.sFloatingPointAsSWord v)

instance
  (n ~ (eb + sb), ValidFP eb sb, KnownNat n, 1 <= n) =>
  PEvalBitCastOrTerm (FP eb sb) (IntN n)
  where
  pevalBitCastOrTerm = pevalBitCastOr
  sbvBitCastOr d v =
    withValidFPProofs @eb @sb $
      SBV.ite
        (SBV.fpIsNaN v)
        d
        (SBV.sFromIntegral $ SBV.sFloatingPointAsSWord v)
