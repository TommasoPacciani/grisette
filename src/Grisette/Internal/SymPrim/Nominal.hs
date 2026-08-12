{-# LANGUAGE GHC2024 #-}
{-# LANGUAGE DeriveAnyClass #-}

-- |
-- Module      :   Grisette.Internal.SymPrim.Nominal
-- Copyright   :   (c) Sirui Lu 2021-2024
-- License     :   BSD-3-Clause (see the LICENSE file)
--
-- Solver-erased nominal domains and their concrete carrier.
module Grisette.Internal.SymPrim.Nominal
  ( NominalDomain (..),
    SNominalDomain (..),
    SNominalDomains (..),
    KnownNominalDomain (..),
    KnownNominalDomains (..),
    NominalDomainRep (..),
    SomeSNominalDomain (..),
    SomeSNominalDomains (..),
    nominalDomainRep,
    someSNominalDomain,
    Nominal (..),
  )
where

import Control.DeepSeq (NFData)
import Data.Binary qualified as Binary
import Data.Bytes.Serial (Serial (deserialize, serialize))
import Data.Hashable (Hashable)
import Data.Proxy (Proxy (Proxy))
import Data.Serialize qualified as Cereal
import GHC.Generics (Generic)
import GHC.TypeLits
  ( KnownSymbol,
    SomeSymbol (SomeSymbol),
    Symbol,
    someSymbolVal,
    symbolVal,
  )
import Grisette.Internal.Core.Data.Class.BitCast (BitCast (bitCast))
import Language.Haskell.TH.Syntax (Lift)
import Type.Reflection (Typeable)

-- | A nominal domain is a structural path, not a flattened string namespace.
data NominalDomain = Domain Symbol [NominalDomain]

-- | Singleton for a nominal domain.
data SNominalDomain (domain :: NominalDomain) where
  SDomain ::
    (KnownSymbol label) =>
    Proxy label ->
    SNominalDomains children ->
    SNominalDomain ('Domain label children)

-- | Singleton telescope for child domains.
data SNominalDomains (domains :: [NominalDomain]) where
  SNilDomains :: SNominalDomains '[]
  SConsDomain ::
    SNominalDomain domain ->
    SNominalDomains domains ->
    SNominalDomains (domain ': domains)

-- | Reify a structural nominal domain.
class (Typeable domain) => KnownNominalDomain (domain :: NominalDomain) where
  nominalDomainSing :: SNominalDomain domain

-- | Reify a telescope of structural nominal domains.
class (Typeable domains) => KnownNominalDomains (domains :: [NominalDomain]) where
  nominalDomainsSing :: SNominalDomains domains

instance
  (KnownSymbol label, KnownNominalDomains children) =>
  KnownNominalDomain ('Domain label children)
  where
  nominalDomainSing = SDomain Proxy nominalDomainsSing

instance KnownNominalDomains '[] where
  nominalDomainsSing = SNilDomains

instance
  (KnownNominalDomain domain, KnownNominalDomains domains) =>
  KnownNominalDomains (domain ': domains)
  where
  nominalDomainsSing = SConsDomain nominalDomainSing nominalDomainsSing

-- | First-order representation used by the type serializer.
data NominalDomainRep = NominalDomainRep !String ![NominalDomainRep]
  deriving stock (Eq, Ord, Show, Generic)
  deriving anyclass (NFData, Hashable)

instance Serial NominalDomainRep where
  serialize (NominalDomainRep label children) =
    serialize label >> serialize children
  deserialize = NominalDomainRep <$> deserialize <*> deserialize

instance Cereal.Serialize NominalDomainRep where
  put = serialize
  get = deserialize

instance Binary.Binary NominalDomainRep where
  put = serialize
  get = deserialize

-- | Existential reification result for one domain.
data SomeSNominalDomain where
  SomeSNominalDomain ::
    (KnownNominalDomain domain) =>
    SNominalDomain domain ->
    SomeSNominalDomain

-- | Existential reification result for a domain telescope.
data SomeSNominalDomains where
  SomeSNominalDomains ::
    (KnownNominalDomains domains) =>
    SNominalDomains domains ->
    SomeSNominalDomains

-- | Forget a singleton into its serializable structural representation.
nominalDomainRep :: SNominalDomain domain -> NominalDomainRep
nominalDomainRep (SDomain label children) =
  NominalDomainRep (symbolVal label) (nominalDomainsRep children)
  where
    nominalDomainsRep :: SNominalDomains domains -> [NominalDomainRep]
    nominalDomainsRep SNilDomains = []
    nominalDomainsRep (SConsDomain domain domains) =
      nominalDomainRep domain : nominalDomainsRep domains

-- | Rebuild the exact type-level tree from serialized labels.
someSNominalDomain :: NominalDomainRep -> SomeSNominalDomain
someSNominalDomain (NominalDomainRep label children) =
  case someSymbolVal label of
    SomeSymbol labelProxy ->
      case someSNominalDomains children of
        SomeSNominalDomains childDomains ->
          SomeSNominalDomain (SDomain labelProxy childDomains)
  where
    someSNominalDomains :: [NominalDomainRep] -> SomeSNominalDomains
    someSNominalDomains [] = SomeSNominalDomains SNilDomains
    someSNominalDomains (domain : domains) =
      case someSNominalDomain domain of
        SomeSNominalDomain domainSing ->
          case someSNominalDomains domains of
            SomeSNominalDomains domainsSing ->
              SomeSNominalDomains (SConsDomain domainSing domainsSing)

-- | Concrete nominal carrier. The domain exists only in the Haskell type.
newtype Nominal (domain :: NominalDomain) value = Nominal
  { unNominal :: value
  }
  deriving stock (Eq, Ord, Show, Generic, Lift)
  deriving newtype (NFData, Hashable)

type role Nominal nominal nominal

instance (Serial value) => Serial (Nominal domain value) where
  serialize (Nominal value) = serialize value
  deserialize = Nominal <$> deserialize

instance (Cereal.Serialize value) => Cereal.Serialize (Nominal domain value) where
  put (Nominal value) = Cereal.put value
  get = Nominal <$> Cereal.get

instance (Binary.Binary value) => Binary.Binary (Nominal domain value) where
  put (Nominal value) = Binary.put value
  get = Nominal <$> Binary.get

instance BitCast value (Nominal domain value) where
  bitCast = Nominal

instance BitCast (Nominal domain value) value where
  bitCast = unNominal
