{-# LANGUAGE CPP #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskellQuotes #-}
{-# LANGUAGE Trustworthy #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

-- |
-- Module      :   Grisette.Internal.Internal.Impl.Core.Data.UnionBase
-- Copyright   :   (c) Sirui Lu 2021-2024
-- License     :   BSD-3-Clause (see the LICENSE file)
--
-- Maintainer  :   siruilu@cs.washington.edu
-- Stability   :   Experimental
-- Portability :   GHC only
module Grisette.Internal.Internal.Impl.Core.Data.UnionBase
  (
  )
where

#if MIN_VERSION_prettyprinter(1,7,0)
import Prettyprinter (align, group, nest, vsep)
#else
import Data.Text.Prettyprint.Doc (align, group, nest, vsep)
#endif

import Control.DeepSeq (NFData (rnf), NFData1 (liftRnf), rnf1)
import qualified Data.Binary as Binary
import Data.Bytes.Get (MonadGet (getWord8))
import Data.Bytes.Put (MonadPut (putWord8))
import Data.Bytes.Serial (Serial (deserialize, serialize))
import Data.Functor.Classes
  ( Eq1 (liftEq),
    Show1 (liftShowsPrec),
    showsPrec1,
    showsUnaryWith,
  )
import Data.Hashable (Hashable (hashWithSalt))
import Data.Kind (Type)
import qualified Data.Serialize as Cereal
import qualified GHC.Generics as G
import Grisette.Internal.Core.Data.Class.AsKey
  ( KeyHashable (keyHashWithSalt),
    KeyHashable1 (liftKeyHashWithSalt),
  )
import Grisette.Internal.Core.Data.Class.Mergeable
  ( Mergeable (rootStrategy),
  )
import Grisette.Internal.Core.Data.Class.PPrint
  ( PPrint (pformatPrec),
    PPrint1 (liftPFormatPrec),
    condEnclose,
    pformatPrec1,
  )
import Grisette.Internal.Internal.Decl.Core.Data.UnionBase
  ( UnionBase,
    eraseUnionGroups,
    ifWithStrategy,
  )
import qualified Grisette.Internal.Internal.Decl.Core.Data.UnionBase as Decl
import Grisette.Internal.SymPrim.AllSyms
  ( AllSyms (allSymsS),
    AllSyms1 (liftAllSymsS),
    SomeSym (SomeSym),
  )
import Grisette.Internal.SymPrim.SymBool (SymBool)
import Language.Haskell.TH.Syntax (Lift (lift, liftTyped))
import Language.Haskell.TH.Syntax.Compat (unTypeSplice)

data PlainUnionBase a
  = UnionSingle a
  | UnionIf a !Bool !SymBool (UnionBase a) (UnionBase a)
  deriving (G.Generic, G.Generic1)

toPlainUnionBase :: UnionBase a -> PlainUnionBase a
toPlainUnionBase (Decl.UnionSingle value) = UnionSingle value
toPlainUnionBase (Decl.UnionIf cached merged guard ifTrue ifFalse) =
  UnionIf cached merged guard ifTrue ifFalse
toPlainUnionBase group@Decl.UnionGroup {} =
  toPlainUnionBase (eraseUnionGroups group)
{-# INLINE toPlainUnionBase #-}

fromPlainUnionBase :: PlainUnionBase a -> UnionBase a
fromPlainUnionBase (UnionSingle value) = Decl.UnionSingle value
fromPlainUnionBase (UnionIf cached merged guard ifTrue ifFalse) =
  Decl.UnionIf cached merged guard ifTrue ifFalse
{-# INLINE fromPlainUnionBase #-}

type family StripDatatypeMetadata (representation :: Type -> Type) :: Type -> Type where
  StripDatatypeMetadata (G.M1 G.D _metadata body) = body

type UnionBaseRepresentation a =
  G.M1
    G.D
    ( 'G.MetaData
        "UnionBase"
        "Grisette.Internal.Internal.Decl.Core.Data.UnionBase"
        "grisette"
        'False
    )
    (StripDatatypeMetadata (G.Rep (PlainUnionBase a)))

type UnionBaseRepresentation1 =
  G.M1
    G.D
    ( 'G.MetaData
        "UnionBase"
        "Grisette.Internal.Internal.Decl.Core.Data.UnionBase"
        "grisette"
        'False
    )
    (StripDatatypeMetadata (G.Rep1 PlainUnionBase))

instance G.Generic (UnionBase a) where
  type Rep (UnionBase a) = UnionBaseRepresentation a
  from value = case G.from (toPlainUnionBase value) of
    G.M1 body -> G.M1 body
  to (G.M1 body) = fromPlainUnionBase (G.to (G.M1 body))

instance G.Generic1 UnionBase where
  type Rep1 UnionBase = UnionBaseRepresentation1
  from1 value = case G.from1 (toPlainUnionBase value) of
    G.M1 body -> G.M1 body
  to1 (G.M1 body) = fromPlainUnionBase (G.to1 (G.M1 body))

instance (Lift a) => Lift (UnionBase a) where
  liftTyped (Decl.UnionSingle value) = [||Decl.UnionSingle value||]
  liftTyped (Decl.UnionIf cached merged guard ifTrue ifFalse) =
    [||Decl.UnionIf cached merged guard ifTrue ifFalse||]
  liftTyped group@Decl.UnionGroup {} = liftTyped (eraseUnionGroups group)
  lift = unTypeSplice . liftTyped

instance Eq1 UnionBase where
  liftEq e (Decl.UnionSingle a) (Decl.UnionSingle b) = e a b
  liftEq e (Decl.UnionIf l1 i1 c1 t1 f1) (Decl.UnionIf l2 i2 c2 t2 f2) =
    e l1 l2 && i1 == i2 && c1 == c2 && liftEq e t1 t2 && liftEq e f1 f2
  liftEq e left@Decl.UnionGroup {} right =
    liftEq e (eraseUnionGroups left) (eraseUnionGroups right)
  liftEq e left right@Decl.UnionGroup {} =
    liftEq e (eraseUnionGroups left) (eraseUnionGroups right)
  liftEq _ _ _ = False

instance (NFData a) => NFData (UnionBase a) where
  rnf = rnf1

instance NFData1 UnionBase where
  liftRnf _a (Decl.UnionSingle a) = _a a
  liftRnf _a (Decl.UnionIf a bo b l r) =
    _a a `seq`
      rnf bo `seq`
        rnf b `seq`
          liftRnf _a l `seq`
            liftRnf _a r
  liftRnf force (Decl.UnionGroup _ _ inject payloads) =
    liftRnf (force . inject) payloads

instance (Mergeable a, Serial a) => Serial (UnionBase a) where
  serialize (Decl.UnionSingle a) = putWord8 0 >> serialize a
  serialize (Decl.UnionIf _ _ c a b) =
    putWord8 1 >> serialize c >> serialize a >> serialize b
  serialize group@Decl.UnionGroup {} = serialize (eraseUnionGroups group)
  deserialize = do
    tag <- getWord8
    case tag of
      0 -> Decl.UnionSingle <$> deserialize
      1 ->
        ifWithStrategy rootStrategy
          <$> deserialize
          <*> deserialize
          <*> deserialize
      _ -> fail "Invalid tag"

instance (Mergeable a, Serial a) => Cereal.Serialize (UnionBase a) where
  put = serialize
  get = deserialize

instance (Mergeable a, Serial a) => Binary.Binary (UnionBase a) where
  put = serialize
  get = deserialize

instance Show1 UnionBase where
  liftShowsPrec sp _ i (Decl.UnionSingle a) = showsUnaryWith sp "Single" i a
  liftShowsPrec sp sl i (Decl.UnionIf _ _ cond t f) =
    showParen (i > 10) $
      showString "If"
        . showChar ' '
        . showsPrec 11 cond
        . showChar ' '
        . sp1 11 t
        . showChar ' '
        . sp1 11 f
    where
      sp1 = liftShowsPrec sp sl
  liftShowsPrec sp sl i group@Decl.UnionGroup {} =
    liftShowsPrec sp sl i (eraseUnionGroups group)

instance (Show a) => Show (UnionBase a) where
  showsPrec = showsPrec1

instance (PPrint a) => PPrint (UnionBase a) where
  pformatPrec = pformatPrec1

instance PPrint1 UnionBase where
  liftPFormatPrec fa _ n (Decl.UnionSingle a) = fa n a
  liftPFormatPrec fa fl n (Decl.UnionIf _ _ cond t f) =
    group $
      condEnclose (n > 10) "(" ")" $
        align $
          nest 2 $
            vsep
              [ "If",
                pformatPrec 11 cond,
                liftPFormatPrec fa fl 11 t,
                liftPFormatPrec fa fl 11 f
              ]
  liftPFormatPrec fa fl n group@Decl.UnionGroup {} =
    liftPFormatPrec fa fl n (eraseUnionGroups group)

instance (Eq a, Hashable a) => KeyHashable (UnionBase a) where
  keyHashWithSalt = liftKeyHashWithSalt hashWithSalt
  {-# INLINE keyHashWithSalt #-}

instance KeyHashable1 UnionBase where
  liftKeyHashWithSalt f s (Decl.UnionSingle a) = s `hashWithSalt` (0 :: Int) `f` a
  liftKeyHashWithSalt f s (Decl.UnionIf _ _ c l r) =
    let g = liftKeyHashWithSalt f
     in ( s
            `hashWithSalt` (1 :: Int)
              `keyHashWithSalt` c
        )
          `g` l
          `g` r
  liftKeyHashWithSalt f s group@Decl.UnionGroup {} =
    liftKeyHashWithSalt f s (eraseUnionGroups group)

instance (AllSyms a) => AllSyms (UnionBase a) where
  allSymsS (Decl.UnionSingle v) = allSymsS v
  allSymsS (Decl.UnionIf _ _ c t f) = \l -> SomeSym c : (allSymsS t . allSymsS f $ l)
  allSymsS (Decl.UnionGroup _ _ inject payloads) =
    liftAllSymsS (allSymsS . inject) payloads

instance AllSyms1 UnionBase where
  liftAllSymsS fa (Decl.UnionSingle v) = fa v
  liftAllSymsS fa (Decl.UnionIf _ _ c t f) =
    \l -> SomeSym c : (liftAllSymsS fa t . liftAllSymsS fa f $ l)
  liftAllSymsS fa (Decl.UnionGroup _ _ inject payloads) =
    liftAllSymsS (fa . inject) payloads
