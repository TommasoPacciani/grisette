{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE Trustworthy #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

-- {-# OPTIONS_GHC -ddump-splices -ddump-to-file -ddump-file-prefix=mergeable1 #-}

-- |
-- Module      :   Grisette.Internal.Internal.Impl.Core.Data.Class.Mergeable
-- Copyright   :   (c) Sirui Lu 2021-2024
-- License     :   BSD-3-Clause (see the LICENSE file)
--
-- Maintainer  :   siruilu@cs.washington.edu
-- Stability   :   Experimental
-- Portability :   GHC only
module Grisette.Internal.Internal.Impl.Core.Data.Class.Mergeable
  ( -- * Internal structural law witnesses (not re-exported by the public facade)
    NominalWrapper (NominalWrapper),
    ReaderTWrapper (ReaderTWrapper),
    IdentityTWrapper (IdentityTWrapper),
    ContTWrapper (ContTWrapper),
    LazyRWSTWrapper (LazyRWSTWrapper),
    StrictRWSTWrapper (StrictRWSTWrapper),
    ComposeWrapper (ComposeWrapper),
    EndoWrapper (EndoWrapper),
    ListFamily (..),
    EitherFamily (..),
    MaybeFamily (..),
  )
where

import Control.Exception (ArithException)
import Control.Monad.Cont (ContT (ContT))
import Control.Monad.Except (ExceptT)
import Control.Monad.Identity
  ( Identity,
    IdentityT (IdentityT, runIdentityT),
  )
import qualified Control.Monad.RWS.Lazy as RWSLazy
import qualified Control.Monad.RWS.Strict as RWSStrict
import Control.Monad.Reader (ReaderT (ReaderT, runReaderT))
import qualified Control.Monad.State.Lazy as StateLazy
import qualified Control.Monad.State.Strict as StateStrict
import Control.Monad.Trans.Maybe (MaybeT)
import qualified Control.Monad.Writer.Lazy as WriterLazy
import qualified Control.Monad.Writer.Strict as WriterStrict
import qualified Data.ByteString as B
import Data.Functor.Compose (Compose (Compose, getCompose))
import Data.Functor.Const (Const)
import Data.Functor.Product (Product)
import Data.Functor.Sum (Sum)
import Data.Int (Int16, Int32, Int64, Int8)
import Data.Monoid (Alt, Ap, Endo (Endo, appEndo))
import qualified Data.Monoid as Monoid
import Data.Ord (Down)
import Data.Ratio (Ratio)
import qualified Data.Text as T
import Data.Typeable (Proxy, Typeable)
import Data.Word (Word16, Word32, Word64, Word8)
import GHC.TypeNats (KnownNat, type (+), type (<=))
import Numeric.Natural (Natural)
import Generics.Deriving
  ( Default (Default),
    Default1 (Default1),
    K1,
    M1,
    Par1,
    Rec1,
    U1,
    V1,
    type (:.:),
    type (:*:),
    type (:+:),
  )
import Grisette.Internal.Core.Control.Exception
  ( AssertionError,
    VerificationConditions,
  )
import Grisette.Internal.Core.Data.Class.BitCast (bitCastOrCanonical)
import Grisette.Internal.Core.Data.Class.ITEOp (ITEOp (symIte))
import Grisette.Internal.Internal.Decl.Core.Data.Class.Mergeable
  ( Mergeable (rootStrategy),
    Mergeable1 (liftRootStrategy),
    Mergeable2 (liftRootStrategy2),
    Mergeable3 (liftRootStrategy3),
    MergingStrategy (NoStrategy, SimpleStrategy, SortedStrategy, StructuralStrategy),
    StructuralCase (StructuralCase),
    StructuralFamily (compareStructural, compareStructuralShape),
    StructuralOrdering (StructuralEQ, StructuralGT, StructuralLT),
    StructuralWrapper (unwrapValue, wrapValue),
    pairStrategy,
    rootStrategy1,
    wrapStrategy,
  )
import Grisette.Internal.SymPrim.AlgReal (AlgReal, AlgRealPoly, RealPoint)
import Grisette.Internal.SymPrim.Array (Array)
import Grisette.Internal.SymPrim.BV
  ( IntN,
    WordN,
  )
import Grisette.Internal.SymPrim.FP
  ( FP,
    FPRoundingMode,
    NotRepresentableFPError,
    ValidFP,
    withValidFPProofs,
  )
import Grisette.Internal.SymPrim.GeneralFun (type (-->))
import Grisette.Internal.SymPrim.SymAlgReal (SymAlgReal)
import Grisette.Internal.SymPrim.SymArray (SymArray)
import Grisette.Internal.SymPrim.SymPair (SymPair)
import Grisette.Internal.SymPrim.SymSeq (SymSeq)
import Grisette.Internal.SymPrim.Nominal
  ( KnownNominalDomain,
    Nominal (Nominal, unNominal),
  )
import Grisette.Internal.SymPrim.Prim.Term
  ( LinkedRep,
    SupportedNonFuncPrim,
  )
import Grisette.Internal.SymPrim.SymNominal (SymNominal)
import Grisette.Internal.SymPrim.SymUninterp (SymUninterp)
import GHC.TypeLits (KnownSymbol)
import Grisette.Internal.SymPrim.SymBV (SymIntN, SymWordN)
import Grisette.Internal.SymPrim.SymFP (SymFP, SymFPRoundingMode)
import Grisette.Internal.SymPrim.SymGeneralFun (type (-~>))
import Grisette.Internal.SymPrim.SymInteger (SymInteger)
import Grisette.Internal.SymPrim.SymTabularFun (type (=~>))
import Grisette.Internal.SymPrim.TabularFun (type (=->))
import Grisette.Internal.TH.Derivation.Derive (derive)

data NominalWrapper target source where
  NominalWrapper :: NominalWrapper (Nominal domain value) value

instance StructuralFamily NominalWrapper where
  compareStructural NominalWrapper NominalWrapper = StructuralEQ
  compareStructuralShape NominalWrapper NominalWrapper = EQ

instance StructuralWrapper NominalWrapper where
  wrapValue NominalWrapper = Nominal
  unwrapValue NominalWrapper = unNominal

data ReaderTWrapper target source where
  ReaderTWrapper ::
    ReaderTWrapper (ReaderT environment monad value) (environment -> monad value)

instance StructuralFamily ReaderTWrapper where
  compareStructural ReaderTWrapper ReaderTWrapper = StructuralEQ
  compareStructuralShape ReaderTWrapper ReaderTWrapper = EQ

instance StructuralWrapper ReaderTWrapper where
  wrapValue ReaderTWrapper = ReaderT
  unwrapValue ReaderTWrapper = runReaderT

data IdentityTWrapper target source where
  IdentityTWrapper :: IdentityTWrapper (IdentityT monad value) (monad value)

instance StructuralFamily IdentityTWrapper where
  compareStructural IdentityTWrapper IdentityTWrapper = StructuralEQ
  compareStructuralShape IdentityTWrapper IdentityTWrapper = EQ

instance StructuralWrapper IdentityTWrapper where
  wrapValue IdentityTWrapper = IdentityT
  unwrapValue IdentityTWrapper = runIdentityT

data ContTWrapper target source where
  ContTWrapper ::
    ContTWrapper
      (ContT result monad value)
      ((value -> monad result) -> monad result)

instance StructuralFamily ContTWrapper where
  compareStructural ContTWrapper ContTWrapper = StructuralEQ
  compareStructuralShape ContTWrapper ContTWrapper = EQ

instance StructuralWrapper ContTWrapper where
  wrapValue ContTWrapper = ContT
  unwrapValue ContTWrapper (ContT value) = value

data LazyRWSTWrapper target source where
  LazyRWSTWrapper ::
    LazyRWSTWrapper
      (RWSLazy.RWST environment writer state monad value)
      (environment -> state -> monad (value, state, writer))

instance StructuralFamily LazyRWSTWrapper where
  compareStructural LazyRWSTWrapper LazyRWSTWrapper = StructuralEQ
  compareStructuralShape LazyRWSTWrapper LazyRWSTWrapper = EQ

instance StructuralWrapper LazyRWSTWrapper where
  wrapValue LazyRWSTWrapper = RWSLazy.RWST
  unwrapValue LazyRWSTWrapper (RWSLazy.RWST value) = value

data StrictRWSTWrapper target source where
  StrictRWSTWrapper ::
    StrictRWSTWrapper
      (RWSStrict.RWST environment writer state monad value)
      (environment -> state -> monad (value, state, writer))

instance StructuralFamily StrictRWSTWrapper where
  compareStructural StrictRWSTWrapper StrictRWSTWrapper = StructuralEQ
  compareStructuralShape StrictRWSTWrapper StrictRWSTWrapper = EQ

instance StructuralWrapper StrictRWSTWrapper where
  wrapValue StrictRWSTWrapper = RWSStrict.RWST
  unwrapValue StrictRWSTWrapper (RWSStrict.RWST value) = value

data ComposeWrapper target source where
  ComposeWrapper :: ComposeWrapper (Compose outer inner value) (outer (inner value))

instance StructuralFamily ComposeWrapper where
  compareStructural ComposeWrapper ComposeWrapper = StructuralEQ
  compareStructuralShape ComposeWrapper ComposeWrapper = EQ

instance StructuralWrapper ComposeWrapper where
  wrapValue ComposeWrapper = Compose
  unwrapValue ComposeWrapper = getCompose

data EndoWrapper target source where
  EndoWrapper :: EndoWrapper (Endo value) (value -> value)

instance StructuralFamily EndoWrapper where
  compareStructural EndoWrapper EndoWrapper = StructuralEQ
  compareStructuralShape EndoWrapper EndoWrapper = EQ

instance StructuralWrapper EndoWrapper where
  wrapValue EndoWrapper = Endo
  unwrapValue EndoWrapper = appEndo

#define CONCRETE_ORD_MERGEABLE(type) \
instance Mergeable type where \
  rootStrategy = \
    let sub = SimpleStrategy $ \_ t _ -> t \
     in SortedStrategy id $ const sub

#define CONCRETE_ORD_MERGEABLE_BV(type) \
instance (KnownNat n, 1 <= n) => Mergeable (type n) where \
  rootStrategy = \
    let sub = SimpleStrategy $ \_ t _ -> t \
     in SortedStrategy id $ const sub

#if 1
CONCRETE_ORD_MERGEABLE(Bool)
CONCRETE_ORD_MERGEABLE(Integer)
CONCRETE_ORD_MERGEABLE(Natural)
CONCRETE_ORD_MERGEABLE(Char)
CONCRETE_ORD_MERGEABLE(Int)
CONCRETE_ORD_MERGEABLE(Int8)
CONCRETE_ORD_MERGEABLE(Int16)
CONCRETE_ORD_MERGEABLE(Int32)
CONCRETE_ORD_MERGEABLE(Int64)
CONCRETE_ORD_MERGEABLE(Word)
CONCRETE_ORD_MERGEABLE(Word8)
CONCRETE_ORD_MERGEABLE(Word16)
CONCRETE_ORD_MERGEABLE(Word32)
CONCRETE_ORD_MERGEABLE(Word64)
CONCRETE_ORD_MERGEABLE(Float)
CONCRETE_ORD_MERGEABLE(Double)
CONCRETE_ORD_MERGEABLE(B.ByteString)
CONCRETE_ORD_MERGEABLE(T.Text)
CONCRETE_ORD_MERGEABLE(FPRoundingMode)
CONCRETE_ORD_MERGEABLE(Monoid.All)
CONCRETE_ORD_MERGEABLE(Monoid.Any)
CONCRETE_ORD_MERGEABLE_BV(WordN)
CONCRETE_ORD_MERGEABLE_BV(IntN)
#endif

instance Mergeable (Proxy a) where
  rootStrategy = SimpleStrategy $ \_ t _ -> t

instance Mergeable1 Proxy where
  liftRootStrategy _ = SimpleStrategy $ \_ t _ -> t
  {-# INLINE liftRootStrategy #-}

instance (Integral a, Typeable a) => Mergeable (Ratio a) where
  rootStrategy =
    let sub = SimpleStrategy $ \_ t _ -> t
     in SortedStrategy id $ const sub

instance (ValidFP eb sb) => Mergeable (FP eb sb) where
  rootStrategy =
    let sub = SimpleStrategy $ \_ t _ -> t
     in withValidFPProofs @eb @sb
          $ SortedStrategy
            (\fp -> (bitCastOrCanonical fp :: WordN (eb + sb)))
          $ const sub

instance Mergeable (a =-> b) where
  rootStrategy = NoStrategy

instance Mergeable (a --> b) where
  rootStrategy = SimpleStrategy symIte

instance Mergeable (Array k v) where
  rootStrategy = NoStrategy

#define MERGEABLE_SIMPLE(symtype) \
instance Mergeable symtype where \
  rootStrategy = SimpleStrategy symIte

#define MERGEABLE_BV(symtype) \
instance (KnownNat n, 1 <= n) => Mergeable (symtype n) where \
  rootStrategy = SimpleStrategy symIte

#define MERGEABLE_FUN(cop, op, consop) \
instance Mergeable (op sa sb) where \
  rootStrategy = SimpleStrategy symIte

#if 1
MERGEABLE_SIMPLE(SymInteger)
MERGEABLE_SIMPLE(SymFPRoundingMode)
MERGEABLE_SIMPLE(SymAlgReal)
MERGEABLE_BV(SymIntN)
MERGEABLE_BV(SymWordN)
MERGEABLE_FUN((=->), (=~>), SymTabularFun)
MERGEABLE_FUN((-->), (-~>), SymGeneralFun)
#endif

instance
  ( SupportedNonFuncPrim ck,
    SupportedNonFuncPrim cv,
    LinkedRep ck sk,
    LinkedRep cv sv
  ) =>
  Mergeable (SymArray sk sv) where
  rootStrategy = SimpleStrategy $ symIte

instance
  (SupportedNonFuncPrim ca, LinkedRep ca sa) =>
  Mergeable (SymSeq sa)
  where
  rootStrategy = SimpleStrategy symIte

instance (Mergeable value) => Mergeable (Nominal domain value) where
  rootStrategy = wrapStrategy NominalWrapper (rootStrategy @value)

instance
  ( SupportedNonFuncPrim ca,
    SupportedNonFuncPrim cb,
    LinkedRep ca sa,
    LinkedRep cb sb
  ) =>
  Mergeable (SymPair sa sb)
  where
  rootStrategy = SimpleStrategy symIte

instance (KnownSymbol n) => Mergeable (SymUninterp n) where
  rootStrategy = SimpleStrategy symIte

instance
  (KnownNominalDomain domain, SupportedNonFuncPrim value) =>
  Mergeable (SymNominal domain value)
  where
  rootStrategy = SimpleStrategy symIte

instance (ValidFP eb sb) => Mergeable (SymFP eb sb) where
  rootStrategy = SimpleStrategy symIte

-- function
instance (Mergeable b) => Mergeable (a -> b) where
  rootStrategy = case rootStrategy @b of
    SimpleStrategy m -> SimpleStrategy $ \cond t f v -> m cond (t v) (f v)
    _ -> NoStrategy
  {-# INLINE rootStrategy #-}

instance Mergeable1 ((->) a) where
  liftRootStrategy ms = case ms of
    SimpleStrategy m -> SimpleStrategy $ \cond t f v -> m cond (t v) (f v)
    _ -> NoStrategy
  {-# INLINE liftRootStrategy #-}

instance Mergeable2 ((->)) where
  liftRootStrategy2 _ ms = case ms of
    SimpleStrategy m -> SimpleStrategy $ \cond t f v -> m cond (t v) (f v)
    _ -> NoStrategy
  {-# INLINE liftRootStrategy2 #-}

data ListFamily value payload where
  EmptyListFamily :: ListFamily [a] ()
  ConsListFamily :: ListFamily [a] (a, [a])

instance StructuralFamily ListFamily where
  compareStructural EmptyListFamily EmptyListFamily = StructuralEQ
  compareStructural EmptyListFamily ConsListFamily = StructuralLT
  compareStructural ConsListFamily EmptyListFamily = StructuralGT
  compareStructural ConsListFamily ConsListFamily = StructuralEQ

  compareStructuralShape EmptyListFamily EmptyListFamily = EQ
  compareStructuralShape EmptyListFamily ConsListFamily = LT
  compareStructuralShape ConsListFamily EmptyListFamily = GT
  compareStructuralShape ConsListFamily ConsListFamily = EQ

listStrategy :: forall a. MergingStrategy a -> MergingStrategy [a]
listStrategy elementStrategy =
  StructuralStrategy splitList payloadStrategy injectList
  where
    splitList :: [a] -> StructuralCase ListFamily [a]
    splitList [] = StructuralCase EmptyListFamily ()
    splitList (value : values) =
      StructuralCase ConsListFamily (value, values)

    payloadStrategy ::
      forall payload. ListFamily [a] payload -> MergingStrategy payload
    payloadStrategy EmptyListFamily =
      SimpleStrategy $ \_ selected _ -> selected
    payloadStrategy ConsListFamily =
      pairStrategy elementStrategy (listStrategy elementStrategy)

    injectList :: forall payload. ListFamily [a] payload -> payload -> [a]
    injectList EmptyListFamily () = []
    injectList ConsListFamily (value, values) = value : values
{-# INLINE listStrategy #-}

instance (Mergeable a) => Mergeable [a] where
  rootStrategy = listStrategy rootStrategy
  {-# INLINE rootStrategy #-}

instance Mergeable1 [] where
  liftRootStrategy = listStrategy
  {-# INLINE liftRootStrategy #-}

instance Mergeable () where
  rootStrategy = SimpleStrategy $ \_ t _ -> t

data EitherFamily value payload where
  LeftEitherFamily :: EitherFamily (Either a b) a
  RightEitherFamily :: EitherFamily (Either a b) b

instance StructuralFamily EitherFamily where
  compareStructural LeftEitherFamily LeftEitherFamily = StructuralEQ
  compareStructural LeftEitherFamily RightEitherFamily = StructuralLT
  compareStructural RightEitherFamily LeftEitherFamily = StructuralGT
  compareStructural RightEitherFamily RightEitherFamily = StructuralEQ

  compareStructuralShape LeftEitherFamily LeftEitherFamily = EQ
  compareStructuralShape LeftEitherFamily RightEitherFamily = LT
  compareStructuralShape RightEitherFamily LeftEitherFamily = GT
  compareStructuralShape RightEitherFamily RightEitherFamily = EQ

eitherStrategy ::
  forall a b.
  MergingStrategy a ->
  MergingStrategy b ->
  MergingStrategy (Either a b)
eitherStrategy leftStrategy rightStrategy =
  StructuralStrategy splitEither payloadStrategy injectEither
  where
    splitEither :: Either a b -> StructuralCase EitherFamily (Either a b)
    splitEither (Left value) = StructuralCase LeftEitherFamily value
    splitEither (Right value) = StructuralCase RightEitherFamily value

    payloadStrategy ::
      forall payload.
      EitherFamily (Either a b) payload -> MergingStrategy payload
    payloadStrategy LeftEitherFamily = leftStrategy
    payloadStrategy RightEitherFamily = rightStrategy

    injectEither ::
      forall payload. EitherFamily (Either a b) payload -> payload -> Either a b
    injectEither LeftEitherFamily = Left
    injectEither RightEitherFamily = Right
{-# INLINE eitherStrategy #-}

instance (Mergeable a, Mergeable b) => Mergeable (Either a b) where
  rootStrategy = eitherStrategy rootStrategy rootStrategy
  {-# INLINE rootStrategy #-}

instance (Mergeable a) => Mergeable1 (Either a) where
  liftRootStrategy = eitherStrategy rootStrategy
  {-# INLINE liftRootStrategy #-}

instance Mergeable2 Either where
  liftRootStrategy2 = eitherStrategy
  {-# INLINE liftRootStrategy2 #-}

data MaybeFamily value payload where
  NothingMaybeFamily :: MaybeFamily (Maybe a) ()
  JustMaybeFamily :: MaybeFamily (Maybe a) a

instance StructuralFamily MaybeFamily where
  compareStructural NothingMaybeFamily NothingMaybeFamily = StructuralEQ
  compareStructural NothingMaybeFamily JustMaybeFamily = StructuralLT
  compareStructural JustMaybeFamily NothingMaybeFamily = StructuralGT
  compareStructural JustMaybeFamily JustMaybeFamily = StructuralEQ

  compareStructuralShape NothingMaybeFamily NothingMaybeFamily = EQ
  compareStructuralShape NothingMaybeFamily JustMaybeFamily = LT
  compareStructuralShape JustMaybeFamily NothingMaybeFamily = GT
  compareStructuralShape JustMaybeFamily JustMaybeFamily = EQ

maybeStrategy :: forall a. MergingStrategy a -> MergingStrategy (Maybe a)
maybeStrategy valueStrategy =
  StructuralStrategy splitMaybe payloadStrategy injectMaybe
  where
    splitMaybe :: Maybe a -> StructuralCase MaybeFamily (Maybe a)
    splitMaybe Nothing = StructuralCase NothingMaybeFamily ()
    splitMaybe (Just value) = StructuralCase JustMaybeFamily value

    payloadStrategy ::
      forall payload. MaybeFamily (Maybe a) payload -> MergingStrategy payload
    payloadStrategy NothingMaybeFamily =
      SimpleStrategy $ \_ selected _ -> selected
    payloadStrategy JustMaybeFamily = valueStrategy

    injectMaybe ::
      forall payload. MaybeFamily (Maybe a) payload -> payload -> Maybe a
    injectMaybe NothingMaybeFamily () = Nothing
    injectMaybe JustMaybeFamily value = Just value
{-# INLINE maybeStrategy #-}

instance (Mergeable a) => Mergeable (Maybe a) where
  rootStrategy = maybeStrategy rootStrategy
  {-# INLINE rootStrategy #-}

instance Mergeable1 Maybe where
  liftRootStrategy = maybeStrategy
  {-# INLINE liftRootStrategy #-}

instance (Mergeable a, Mergeable b) => Mergeable (a, b) where
  rootStrategy = pairStrategy rootStrategy rootStrategy
  {-# INLINE rootStrategy #-}

instance (Mergeable a) => Mergeable1 ((,) a) where
  liftRootStrategy = pairStrategy rootStrategy
  {-# INLINE liftRootStrategy #-}

instance Mergeable2 (,) where
  liftRootStrategy2 = pairStrategy
  {-# INLINE liftRootStrategy2 #-}

derive
  [ ''(,,),
    ''(,,,),
    ''(,,,,),
    ''(,,,,,),
    ''(,,,,,,),
    ''(,,,,,,,),
    ''(,,,,,,,,),
    ''(,,,,,,,,,),
    ''(,,,,,,,,,,),
    ''(,,,,,,,,,,,),
    ''(,,,,,,,,,,,,),
    ''(,,,,,,,,,,,,,),
    ''(,,,,,,,,,,,,,,)
  ]
  [''Mergeable, ''Mergeable1, ''Mergeable2, ''Mergeable3]

derive
  [ ''Identity,
    ''Monoid.Dual,
    ''Monoid.Sum,
    ''Monoid.Product,
    ''Monoid.First,
    ''Monoid.Last,
    ''Down,
    ''MaybeT,
    ''ExceptT,
    ''WriterLazy.WriterT,
    ''WriterStrict.WriterT,
    ''StateLazy.StateT,
    ''StateStrict.StateT
  ]
  [''Mergeable, ''Mergeable1]

derive
  [ ''AssertionError,
    ''VerificationConditions,
    ''ArithException,
    ''NotRepresentableFPError,
    ''AlgRealPoly,
    ''RealPoint,
    ''AlgReal
  ]
  [''Mergeable]

-- Reader -- separately implemented as we don't need Mergeable s
instance
  (Mergeable a, Mergeable1 m) =>
  Mergeable (ReaderT s m a)
  where
  rootStrategy = rootStrategy1
  {-# INLINE rootStrategy #-}

instance (Mergeable1 m) => Mergeable1 (ReaderT s m) where
  liftRootStrategy m =
    wrapStrategy ReaderTWrapper (liftRootStrategy (liftRootStrategy m))
  {-# INLINE liftRootStrategy #-}

-- IdentityT
instance (Mergeable1 m, Mergeable a) => Mergeable (IdentityT m a) where
  rootStrategy = rootStrategy1
  {-# INLINE rootStrategy #-}

instance (Mergeable1 m) => Mergeable1 (IdentityT m) where
  liftRootStrategy m = wrapStrategy IdentityTWrapper (liftRootStrategy m)
  {-# INLINE liftRootStrategy #-}

-- ContT -- separately implemented as we don't need Mergeable a
instance (Mergeable1 m, Mergeable r) => Mergeable (ContT r m a) where
  rootStrategy =
    wrapStrategy ContTWrapper (liftRootStrategy rootStrategy1)
  {-# INLINE rootStrategy #-}

instance (Mergeable1 m, Mergeable r) => Mergeable1 (ContT r m) where
  liftRootStrategy _ =
    wrapStrategy ContTWrapper (liftRootStrategy rootStrategy1)
  {-# INLINE liftRootStrategy #-}

-- RWS -- separately implemented as we don't need Mergeable r
instance
  (Mergeable s, Mergeable w, Mergeable a, Mergeable1 m) =>
  Mergeable (RWSLazy.RWST r w s m a)
  where
  rootStrategy = rootStrategy1
  {-# INLINE rootStrategy #-}

instance
  (Mergeable s, Mergeable w, Mergeable1 m) =>
  Mergeable1 (RWSLazy.RWST r w s m)
  where
  liftRootStrategy m =
    wrapStrategy
      LazyRWSTWrapper
      ( liftRootStrategy . liftRootStrategy . liftRootStrategy $
          liftRootStrategy3 m rootStrategy rootStrategy
      )
  {-# INLINE liftRootStrategy #-}

instance
  (Mergeable s, Mergeable w, Mergeable a, Mergeable1 m) =>
  Mergeable (RWSStrict.RWST r w s m a)
  where
  rootStrategy = rootStrategy1
  {-# INLINE rootStrategy #-}

instance
  (Mergeable s, Mergeable w, Mergeable1 m) =>
  Mergeable1 (RWSStrict.RWST r w s m)
  where
  liftRootStrategy m =
    wrapStrategy
      StrictRWSTWrapper
      ( liftRootStrategy . liftRootStrategy . liftRootStrategy $
          liftRootStrategy3 m rootStrategy rootStrategy
      )
  {-# INLINE liftRootStrategy #-}

-- Product
deriving via
  (Default (Product l r a))
  instance
    (Mergeable (l a), Mergeable (r a)) => Mergeable (Product l r a)

deriving via
  (Default1 (Product l r))
  instance
    (Mergeable1 l, Mergeable1 r) => Mergeable1 (Product l r)

-- Sum
deriving via
  (Default (Sum l r a))
  instance
    (Mergeable (l a), Mergeable (r a)) => Mergeable (Sum l r a)

deriving via
  (Default1 (Sum l r))
  instance
    (Mergeable1 l, Mergeable1 r) => Mergeable1 (Sum l r)

-- Compose
deriving via
  (Default (Compose f g a))
  instance
    (Mergeable (f (g a))) => Mergeable (Compose f g a)

instance (Mergeable1 f, Mergeable1 g) => Mergeable1 (Compose f g) where
  liftRootStrategy s =
    wrapStrategy ComposeWrapper (liftRootStrategy (liftRootStrategy s))
  {-# INLINE liftRootStrategy #-}

-- Const
deriving via
  (Default (Const a b))
  instance
    (Mergeable a) => Mergeable (Const a b)

deriving via
  (Default1 (Const a))
  instance
    (Mergeable a) => Mergeable1 (Const a)

-- Alt
deriving via
  (Default (Alt f a))
  instance
    (Mergeable (f a)) => Mergeable (Alt f a)

deriving via
  (Default1 (Alt f))
  instance
    (Mergeable1 f) => Mergeable1 (Alt f)

-- Ap
deriving via
  (Default (Ap f a))
  instance
    (Mergeable (f a)) => Mergeable (Ap f a)

deriving via
  (Default1 (Ap f))
  instance
    (Mergeable1 f) => Mergeable1 (Ap f)

-- Endo
instance (Mergeable a) => Mergeable (Endo a) where
  rootStrategy = rootStrategy1
  {-# INLINE rootStrategy #-}

instance Mergeable1 Endo where
  liftRootStrategy strategy =
    wrapStrategy EndoWrapper (liftRootStrategy strategy)

-- Generic
deriving via (Default (U1 p)) instance Mergeable (U1 p)

deriving via (Default (V1 p)) instance Mergeable (V1 p)

deriving via
  (Default (K1 i c p))
  instance
    (Mergeable c) => Mergeable (K1 i c p)

deriving via
  (Default (M1 i c f p))
  instance
    (Mergeable (f p)) => Mergeable (M1 i c f p)

deriving via
  (Default ((f :+: g) p))
  instance
    (Mergeable (f p), Mergeable (g p)) => Mergeable ((f :+: g) p)

deriving via
  (Default ((f :*: g) p))
  instance
    (Mergeable (f p), Mergeable (g p)) => Mergeable ((f :*: g) p)

deriving via
  (Default (Par1 p))
  instance
    (Mergeable p) => Mergeable (Par1 p)

deriving via
  (Default (Rec1 f p))
  instance
    (Mergeable (f p)) => Mergeable (Rec1 f p)

deriving via
  (Default ((f :.: g) p))
  instance
    (Mergeable (f (g p))) => Mergeable ((f :.: g) p)
