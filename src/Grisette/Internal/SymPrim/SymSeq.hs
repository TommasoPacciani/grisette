{-# LANGUAGE GHC2024 #-}
{-# OPTIONS_GHC -Wno-missing-import-lists #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RoleAnnotations #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

-- |
-- Module      :   Grisette.Internal.SymPrim.SymSeq
-- Copyright   :   (c) Sirui Lu 2024
-- License     :   BSD-3-Clause (see the LICENSE file)
--
-- Solver-native finite symbolic sequences.
module Grisette.Internal.SymPrim.SymSeq
  ( SymSeq (..),
    nil,
    cons,
    append,
    range,
    tail,
    lookup,
    lookupValue,
    lookupParts,
    zip,
    length,
    fold,
    foldWith,
    PreparedSeqFold,
    PreparedSeqFoldWith,
    SymbolicFocusedCaptures (..),
    PreparedFocusedSeqFold,
    prepareFocusedFoldHost,
    applyPreparedFocusedFold,
    prepareFoldHost,
    prepareFoldWithHost,
    applyPreparedFold,
    applyPreparedFoldWith,
    foldHost,
    foldWithHost,
  )
where

import Control.DeepSeq (NFData)
import qualified Data.Binary as Binary
import Data.Bytes.Serial (Serial (deserialize, serialize))
import qualified Data.Serialize as Cereal
import Data.String (IsString (fromString))
import Data.Kind (Type)
import GHC.Generics (Generic)
import Grisette.Internal.Core.Data.Class.Solvable
  ( Solvable (con, conView, sym),
    ssym,
  )
import Grisette.Internal.Internal.Decl.SymPrim.AllSyms
  ( AllSyms (allSymsS),
    SomeSym (SomeSym),
  )
import Grisette.Internal.Core.Data.Symbol
  ( freshBoundSymbol,
  )
import Grisette.Internal.SymPrim.GeneralFun
  ( buildGeneralFun2,
    buildGeneralFun3,
    pevalClosedSeqFold,
    pevalClosedSeqFoldWith,
    pevalPreparedSeqFold,
    pevalPreparedSeqFoldWith,
    pevalPreparedFocusedSeqFold,
    buildFocusedGeneralFun,
    validateClosedFocusedSeqFold,
    validateClosedSeqFold,
    validateClosedSeqFoldWith,
    type (-->),
  )
import System.IO.Unsafe (unsafePerformIO)
import Grisette.Internal.SymPrim.Prim.Internal.Serialize ()
import Grisette.Internal.SymPrim.Prim.Internal.Term
  ( ConRep (ConType),
    LinkedRep (underlyingTerm, wrapTerm),
    SupportedNonFuncPrim,
    SupportedPrim,
    SymRep (SymType),
    Term,
    FocusedSeqFoldBinderSymbols
      ( FocusedSeqFoldBinderSymbol,
        NoFocusedSeqFoldBinderSymbols
      ),
    FocusedSeqFoldOperands
      ( FocusedSeqFoldOperand,
        NoFocusedSeqFoldOperands
      ),
    conTerm,
    pevalSeqAppendTerm,
    pevalSeqConsTerm,
    pevalSeqRangeTerm,
    pevalSeqTailTerm,
    pevalSeqLookupTerm,
    pevalSeqLookupValueTerm,
    PEvalOrdTerm (pevalLeOrdTerm, pevalLtOrdTerm),
    pevalAndTerm,
    pevalSeqZipTerm,
    pevalSeqLengthTerm,
    pformatTerm,
    symTerm,
    typedConstantSymbol,
    pattern ConTerm,
    pattern SupportedTerm,
  )
import Grisette.Internal.SymPrim.SymGeneralFun
  ( type (-~>) (SymGeneralFun),
  )
import Grisette.Internal.SymPrim.SymPair (SymPair)
import Grisette.Internal.SymPrim.SymBool (SymBool)
import Grisette.Internal.SymPrim.SymInteger (SymInteger)
import Language.Haskell.TH.Syntax (Lift)
import Prelude hiding (length, lookup, tail, zip)

newtype SymSeq a = SymSeq
  { underlyingSeqTerm :: Term [ConType a]
  }
  deriving (Lift, NFData, Generic)

-- | A closed, validated symbolic sequence step.  Its private application
-- closure retains both the checked term and the exact solver evidence used to
-- prepare it, so application needs no second constraint-solving pass.
newtype PreparedSeqFold state element = PreparedSeqFold
  (state -> SymSeq element -> state)

type role PreparedSeqFold nominal nominal

-- | 'PreparedSeqFold' with an explicit first-order environment.
newtype PreparedSeqFoldWith environment state element = PreparedSeqFoldWith
  (environment -> state -> SymSeq element -> state)

type role PreparedSeqFoldWith nominal nominal nominal

-- | Heterogeneous primitive lanes supplied to a prepared focused fold.  The
-- constructor constraints ensure every capture has a first-order solver sort;
-- a physical row itself therefore cannot be inserted into this bundle.
data SymbolicFocusedCaptures (captures :: [Type]) where
  FocusedNoCaptures :: SymbolicFocusedCaptures '[]
  FocusedCapture
    :: ( ConRep value
       , SupportedNonFuncPrim (ConType value)
       , LinkedRep (ConType value) value )
    => !value
    -> !(SymbolicFocusedCaptures rest)
    -> SymbolicFocusedCaptures (value ': rest)

infixr 5 `FocusedCapture`

type family FocusedConTypes (captures :: [Type]) :: [Type] where
  FocusedConTypes '[] = '[]
  FocusedConTypes (value ': rest) = ConType value ': FocusedConTypes rest

-- | A state/index fold whose binders and callback body were constructed once.
-- Application only substitutes the current primitive lanes for private typed
-- placeholders and applies the retained term; it never invokes the callback or
-- allocates another binder.
newtype PreparedFocusedSeqFold captures state element =
  PreparedFocusedSeqFold
    (SymbolicFocusedCaptures captures -> state -> SymSeq element -> state)

type role PreparedFocusedSeqFold nominal nominal nominal

instance ConRep (SymSeq a) where
  type ConType (SymSeq a) = [ConType a]

instance (SupportedNonFuncPrim a, SymRep a) => SymRep [a] where
  type SymType [a] = SymSeq (SymType a)

instance
  (SupportedNonFuncPrim ca, LinkedRep ca sa) =>
  LinkedRep [ca] (SymSeq sa)
  where
  underlyingTerm = underlyingSeqTerm
  wrapTerm = SymSeq

instance
  (SupportedNonFuncPrim ca, LinkedRep ca sa) =>
  Solvable [ca] (SymSeq sa)
  where
  con = wrapTerm . conTerm
  sym = wrapTerm . symTerm . typedConstantSymbol
  conView value = case underlyingTerm value of
    ConTerm concrete -> Just concrete
    _ -> Nothing

instance
  (SupportedNonFuncPrim ca, LinkedRep ca sa) =>
  AllSyms (SymSeq sa)
  where
  allSymsS value = (SomeSym value :)

instance
  (SupportedNonFuncPrim ca, LinkedRep ca sa) =>
  IsString (SymSeq sa)
  where
  fromString = ssym . fromString

instance Show (SymSeq a) where
  show = pformatTerm . underlyingSeqTerm

instance
  (SupportedNonFuncPrim ca, LinkedRep ca sa) =>
  Serial (SymSeq sa)
  where
  serialize = serialize . underlyingTerm
  deserialize = wrapTerm <$> deserialize

instance
  (SupportedNonFuncPrim ca, LinkedRep ca sa) =>
  Cereal.Serialize (SymSeq sa)
  where
  put = serialize
  get = deserialize

instance
  (SupportedNonFuncPrim ca, LinkedRep ca sa) =>
  Binary.Binary (SymSeq sa)
  where
  put = serialize
  get = deserialize

nil ::
  (SupportedNonFuncPrim (ConType a), LinkedRep (ConType a) a) =>
  SymSeq a
nil = wrapTerm (conTerm [])

cons ::
  (SupportedNonFuncPrim (ConType a), LinkedRep (ConType a) a) =>
  a ->
  SymSeq a ->
  SymSeq a
cons element sequence =
  wrapTerm $ pevalSeqConsTerm (underlyingTerm element) (underlyingTerm sequence)

append ::
  (SupportedNonFuncPrim (ConType a), LinkedRep (ConType a) a) =>
  SymSeq a ->
  SymSeq a ->
  SymSeq a
append left right =
  wrapTerm $ pevalSeqAppendTerm (underlyingTerm left) (underlyingTerm right)

range :: SymInteger -> SymSeq SymInteger
range = wrapTerm . pevalSeqRangeTerm . underlyingTerm

-- | Drop the first element; the tail of an empty sequence is empty.
tail ::
  (SupportedNonFuncPrim (ConType a), LinkedRep (ConType a) a) =>
  SymSeq a ->
  SymSeq a
tail = wrapTerm . pevalSeqTailTerm . underlyingTerm

lookup ::
  (SupportedNonFuncPrim (ConType a), LinkedRep (ConType a) a) =>
  a ->
  SymSeq a ->
  SymInteger ->
  SymPair SymBool a
lookup seed sequence index =
  wrapTerm $
    pevalSeqLookupTerm
      (underlyingTerm seed)
      (underlyingTerm sequence)
      (underlyingTerm index)

-- | Total value-only lookup.  Unlike projecting 'lookup', this operation never
-- creates a symbolic product term; an absent coordinate yields the exact seed.
lookupValue ::
  (SupportedNonFuncPrim (ConType a), LinkedRep (ConType a) a) =>
  a ->
  SymSeq a ->
  SymInteger ->
  a
lookupValue seed sequence index =
  wrapTerm $
    pevalSeqLookupValueTerm
      (underlyingTerm seed)
      (underlyingTerm sequence)
      (underlyingTerm index)

-- | Presence from a preparation-owned authoritative length together with a
-- value-only lane lookup.  The result is a Haskell product of two scalar terms,
-- never a solver pair.  Correlated columnar-sequence constructors establish
-- that the authoritative length equals every reachable lane length.
lookupParts ::
  (SupportedNonFuncPrim (ConType a), LinkedRep (ConType a) a) =>
  SymInteger ->
  a ->
  SymSeq a ->
  SymInteger ->
  (SymBool, a)
lookupParts authoritativeLength seed sequence index =
  ( wrapTerm $
      pevalAndTerm
        (pevalLeOrdTerm (conTerm (0 :: Integer)) (underlyingTerm index))
        (pevalLtOrdTerm
          (underlyingTerm index)
          (underlyingTerm authoritativeLength)),
    lookupValue seed sequence index
  )

zip ::
  ( SupportedNonFuncPrim (ConType a),
    SupportedNonFuncPrim (ConType b),
    LinkedRep (ConType a) a,
    LinkedRep (ConType b) b
  ) =>
  SymSeq a ->
  SymSeq b ->
  SymSeq (SymPair a b)
zip left right =
  wrapTerm $ pevalSeqZipTerm (underlyingTerm left) (underlyingTerm right)

length ::
  ( SupportedNonFuncPrim (ConType a),
    LinkedRep (ConType a) a,
    LinkedRep Integer integer
  ) =>
  SymSeq a ->
  integer
length = wrapTerm . pevalSeqLengthTerm . underlyingTerm

fold ::
  ( SupportedNonFuncPrim (ConType state),
    SupportedNonFuncPrim (ConType element),
    LinkedRep (ConType state) state,
    LinkedRep (ConType element) element
  ) =>
  (state -~> element -~> state) ->
  state ->
  SymSeq element ->
  state
fold (SymGeneralFun (stepTerm@SupportedTerm)) initial sequence =
  let folded =
        pevalClosedSeqFold
          stepTerm
          (underlyingTerm initial)
          (underlyingTerm sequence)
   in folded `seq` wrapTerm folded

foldWith ::
  ( SupportedNonFuncPrim (ConType environment),
    SupportedNonFuncPrim (ConType state),
    SupportedNonFuncPrim (ConType element),
    LinkedRep (ConType environment) environment,
    LinkedRep (ConType state) state,
    LinkedRep (ConType element) element
  ) =>
  (environment -~> state -~> element -~> state) ->
  environment ->
  state ->
  SymSeq element ->
  state
foldWith (SymGeneralFun (stepTerm@SupportedTerm)) environment initial sequence =
  let folded =
        pevalClosedSeqFoldWith
          stepTerm
          (underlyingTerm environment)
          (underlyingTerm initial)
          (underlyingTerm sequence)
   in folded `seq` wrapTerm folded

-- | Abstract an ordinary Haskell step over fresh private binders and validate
-- the resulting closed function once.  Applying the returned program never
-- executes the callback or traverses it for free symbols again.
prepareFoldHost ::
  forall state element.
  ( SupportedNonFuncPrim (ConType state),
    SupportedNonFuncPrim (ConType element),
    SupportedPrim (ConType element --> ConType state),
    SupportedPrim (ConType state --> ConType element --> ConType state),
    LinkedRep (ConType state) state,
    LinkedRep (ConType element) element
  ) =>
  (state -> element -> state) ->
  PreparedSeqFold state element
prepareFoldHost step = unsafePerformIO $ do
  stateSymbol <- typedConstantSymbol <$> freshBoundSymbol "foldSeq.state"
  elementSymbol <- typedConstantSymbol <$> freshBoundSymbol "foldSeq.element"
  let body =
        underlyingTerm
          ( step
              (wrapTerm (symTerm stateSymbol))
              (wrapTerm (symTerm elementSymbol))
          )
      checked = validateClosedSeqFold $
        conTerm (buildGeneralFun2 stateSymbol elementSymbol body)
      apply initial sequence =
        let folded = pevalPreparedSeqFold
              checked (underlyingTerm initial) (underlyingTerm sequence)
         in folded `seq` wrapTerm folded
  checked `seq` return (PreparedSeqFold apply)
{-# NOINLINE prepareFoldHost #-}

-- | Apply a prepared closed step to dynamic fold inputs.
applyPreparedFold ::
  PreparedSeqFold state element ->
  state ->
  SymSeq element ->
  state
applyPreparedFold (PreparedSeqFold apply) = apply

-- | One-shot host fold.  This remains the convenient semantic API; retained
-- owners should prepare once and call 'applyPreparedFold' repeatedly.
foldHost ::
  forall state element.
  ( SupportedNonFuncPrim (ConType state),
    SupportedNonFuncPrim (ConType element),
    SupportedPrim (ConType element --> ConType state),
    SupportedPrim (ConType state --> ConType element --> ConType state),
    LinkedRep (ConType state) state,
    LinkedRep (ConType element) element
  ) =>
  (state -> element -> state) ->
  state ->
  SymSeq element ->
  state
foldHost step = applyPreparedFold (prepareFoldHost step)
{-# NOINLINE foldHost #-}

-- | Prepare a closed fold step with an explicit environment.
prepareFoldWithHost ::
  forall environment state element.
  ( SupportedNonFuncPrim (ConType environment),
    SupportedNonFuncPrim (ConType state),
    SupportedNonFuncPrim (ConType element),
    SupportedPrim (ConType element --> ConType state),
    SupportedPrim (ConType state --> ConType element --> ConType state),
    SupportedPrim
      (ConType environment --> ConType state --> ConType element --> ConType state),
    LinkedRep (ConType environment) environment,
    LinkedRep (ConType state) state,
    LinkedRep (ConType element) element
  ) =>
  (environment -> state -> element -> state) ->
  PreparedSeqFoldWith environment state element
prepareFoldWithHost step = unsafePerformIO $ do
  environmentSymbol <-
    typedConstantSymbol <$> freshBoundSymbol "foldSeqWith.environment"
  stateSymbol <- typedConstantSymbol <$> freshBoundSymbol "foldSeqWith.state"
  elementSymbol <- typedConstantSymbol <$> freshBoundSymbol "foldSeqWith.element"
  let body =
        underlyingTerm
          ( step
              (wrapTerm (symTerm environmentSymbol))
              (wrapTerm (symTerm stateSymbol))
              (wrapTerm (symTerm elementSymbol))
          )
      checked = validateClosedSeqFoldWith $
        conTerm (buildGeneralFun3
          environmentSymbol stateSymbol elementSymbol body)
      apply environment initial sequence =
        let folded = pevalPreparedSeqFoldWith
              checked
              (underlyingTerm environment)
              (underlyingTerm initial)
              (underlyingTerm sequence)
         in folded `seq` wrapTerm folded
  checked `seq` return (PreparedSeqFoldWith apply)
{-# NOINLINE prepareFoldWithHost #-}

-- | Apply a prepared environment-bearing step.
applyPreparedFoldWith ::
  PreparedSeqFoldWith environment state element ->
  environment ->
  state ->
  SymSeq element ->
  state
applyPreparedFoldWith (PreparedSeqFoldWith apply) = apply

freshFocusedCaptures
  :: SymbolicFocusedCaptures captures
  -> IO
      ( FocusedSeqFoldBinderSymbols (FocusedConTypes captures),
        SymbolicFocusedCaptures captures
      )
freshFocusedCaptures FocusedNoCaptures =
  pure (NoFocusedSeqFoldBinderSymbols, FocusedNoCaptures)
freshFocusedCaptures (FocusedCapture (_ :: value) rest) = do
  symbol <- typedConstantSymbol <$> freshBoundSymbol "focusedFold.capture"
  (symbols, symbolicRest) <- freshFocusedCaptures rest
  pure
    ( FocusedSeqFoldBinderSymbol symbol symbols,
      FocusedCapture (wrapTerm (symTerm symbol) :: value) symbolicRest
    )

focusedOperands
  :: SymbolicFocusedCaptures captures
  -> FocusedSeqFoldOperands (FocusedConTypes captures)
focusedOperands FocusedNoCaptures = NoFocusedSeqFoldOperands
focusedOperands (FocusedCapture value rest) =
  FocusedSeqFoldOperand (underlyingTerm value) (focusedOperands rest)

-- | Prepare a multi-lane scalar-driver fold exactly once.
--
-- The callback is evaluated once against private typed placeholders and fresh
-- state/index binders.  Preparation rejects every free solver value except the
-- declared captures.  Applying the result substitutes current primitive lanes
-- into the retained function term; it neither calls the callback nor allocates
-- a binder.  This is the column-major alternative to a pair-valued row
-- environment.
prepareFocusedFoldHost ::
  forall captures state element.
  ( SupportedNonFuncPrim (ConType state),
    SupportedNonFuncPrim (ConType element),
    SupportedPrim (ConType element --> ConType state),
    SupportedPrim (ConType state --> ConType element --> ConType state),
    LinkedRep (ConType state) state,
    LinkedRep (ConType element) element
  ) =>
  SymbolicFocusedCaptures captures ->
  (SymbolicFocusedCaptures captures -> state -> element -> state) ->
  PreparedFocusedSeqFold captures state element
prepareFocusedFoldHost template step = unsafePerformIO $ do
  (captureSymbols, symbolicCaptures) <- freshFocusedCaptures template
  stateSymbol <- typedConstantSymbol <$> freshBoundSymbol "focusedFold.state"
  elementSymbol <- typedConstantSymbol <$> freshBoundSymbol "focusedFold.index"
  let body = underlyingTerm
        (step symbolicCaptures
          (wrapTerm (symTerm stateSymbol))
          (wrapTerm (symTerm elementSymbol)))
      callback = buildFocusedGeneralFun
        captureSymbols stateSymbol elementSymbol body
      validated = validateClosedFocusedSeqFold callback
      apply captures initial sequence =
        let folded = pevalPreparedFocusedSeqFold
              validated
              (focusedOperands captures)
              (underlyingTerm initial)
              (underlyingTerm sequence)
         in folded `seq` wrapTerm folded
  validated `seq` pure (PreparedFocusedSeqFold apply)
{-# NOINLINE prepareFocusedFoldHost #-}

-- | Apply a retained focused fold.  The host callback is not reachable here.
applyPreparedFocusedFold ::
  PreparedFocusedSeqFold captures state element ->
  SymbolicFocusedCaptures captures ->
  state ->
  SymSeq element ->
  state
applyPreparedFocusedFold (PreparedFocusedSeqFold apply) = apply

-- | One-shot environment-bearing host fold.
foldWithHost ::
  forall environment state element.
  ( SupportedNonFuncPrim (ConType environment),
    SupportedNonFuncPrim (ConType state),
    SupportedNonFuncPrim (ConType element),
    SupportedPrim (ConType element --> ConType state),
    SupportedPrim (ConType state --> ConType element --> ConType state),
    SupportedPrim
      (ConType environment --> ConType state --> ConType element --> ConType state),
    LinkedRep (ConType environment) environment,
    LinkedRep (ConType state) state,
    LinkedRep (ConType element) element
  ) =>
  (environment -> state -> element -> state) ->
  environment ->
  state ->
  SymSeq element ->
  state
foldWithHost step = applyPreparedFoldWith (prepareFoldWithHost step)
{-# NOINLINE foldWithHost #-}
