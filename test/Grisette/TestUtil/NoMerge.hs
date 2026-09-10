{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE OverloadedStrings #-}

module Grisette.TestUtil.NoMerge
  ( NoMerge (..),
    MergingOnly (..),
    MergingTryOnly (..),
    oneNotMerged,
    noMergeNotMerged,
  )
where

import GHC.Generics (Generic)
import Grisette
  ( AsKey1,
    Mergeable (rootStrategy),
    MergingBranching (mrgIfWithStrategy),
    MergingStrategy (NoStrategy),
    SimpleMergeable (mrgIte),
    SimpleMergeable1 (liftMrgIte),
    SymBranching (mrgIfPropagatedStrategy),
    TryMerge (tryMergeWithStrategy),
    Union,
  )

data NoMerge = NoMerge
  deriving (Show, Eq, Generic)

instance Mergeable NoMerge where
  rootStrategy = NoStrategy

-- | A test carrier with explicit-strategy branching but no cached-strategy
-- propagation or independent normalization capability.
newtype MergingOnly a = MergingOnly {runMergingOnly :: Union a}
  deriving newtype (Functor, Applicative, Monad)

instance (Mergeable a) => SimpleMergeable (MergingOnly a) where
  mrgIte cond (MergingOnly left) (MergingOnly right) =
    MergingOnly $ mrgIte cond left right

instance SimpleMergeable1 MergingOnly where
  liftMrgIte merge cond (MergingOnly left) (MergingOnly right) =
    MergingOnly $ liftMrgIte merge cond left right

instance MergingBranching MergingOnly where
  mrgIfWithStrategy strategy cond (MergingOnly left) (MergingOnly right) =
    MergingOnly $ mrgIfWithStrategy strategy cond left right

-- | A test carrier with explicit-strategy branching and normalization, but no
-- propagated-strategy branching.
newtype MergingTryOnly a = MergingTryOnly {runMergingTryOnly :: Union a}
  deriving newtype (Functor, Applicative, Monad)

instance (Mergeable a) => SimpleMergeable (MergingTryOnly a) where
  mrgIte cond (MergingTryOnly left) (MergingTryOnly right) =
    MergingTryOnly $ mrgIte cond left right

instance SimpleMergeable1 MergingTryOnly where
  liftMrgIte merge cond (MergingTryOnly left) (MergingTryOnly right) =
    MergingTryOnly $ liftMrgIte merge cond left right

instance MergingBranching MergingTryOnly where
  mrgIfWithStrategy strategy cond (MergingTryOnly left) (MergingTryOnly right) =
    MergingTryOnly $ mrgIfWithStrategy strategy cond left right

instance TryMerge MergingTryOnly where
  tryMergeWithStrategy strategy (MergingTryOnly value) =
    MergingTryOnly $ tryMergeWithStrategy strategy value

oneNotMerged :: AsKey1 Union Int
oneNotMerged = mrgIfPropagatedStrategy "a" (return 1) (return 1)

noMergeNotMerged :: AsKey1 Union NoMerge
noMergeNotMerged = mrgIfPropagatedStrategy "a" (return NoMerge) (return NoMerge)
