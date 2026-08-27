{-# OPTIONS_GHC -Wno-missing-import-lists #-}

-- |
-- Module      :   Grisette.Internal.Core.Data.Class.Mergeable
-- Copyright   :   (c) Sirui Lu 2021-2023
-- License     :   BSD-3-Clause (see the LICENSE file)
--
-- Maintainer  :   siruilu@cs.washington.edu
-- Stability   :   Experimental
-- Portability :   GHC only
module Grisette.Internal.Core.Data.Class.Mergeable
  ( -- * Merging strategy
    MergingStrategy (..),
    StructuralOrdering (..),
    StructuralFamily (..),
    StructuralWrapper (..),
    StructuralCase (..),
    structuralStrategy,

    -- * Mergeable
    Mergeable (..),
    Mergeable1 (..),
    rootStrategy1,
    Mergeable2 (..),
    rootStrategy2,
    Mergeable3 (..),
    rootStrategy3,

    -- * Generic 'Mergeable'
    MergeableArgs (..),
    GMergeable (..),
    genericRootStrategy,
    genericLiftRootStrategy,

    -- * Combinators for manually building merging strategies
    wrapStrategy,
    pairStrategy,
    product2Strategy,
    DynamicSortedIdx (..),
    ResolvedStrategy (..),
    resolveStrategy,
    resolveStrategy',
    resolveMergeable1,

    -- * Internal structural law witnesses
    GenericProductWrapper (GenericProductWrapper),
    M1Wrapper (M1Wrapper),
    K1Wrapper (K1Wrapper),
    Par1Wrapper (Par1Wrapper),
    Rec1Wrapper (Rec1Wrapper),
    Comp1Wrapper (Comp1Wrapper),
    DefaultWrapper (DefaultWrapper),
    GenericWrapper (GenericWrapper),
    Default1Wrapper (Default1Wrapper),
    Generic1Wrapper (Generic1Wrapper),
    AsKeyWrapper (AsKeyWrapper),
    AsKey1Wrapper (AsKey1Wrapper),
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

import Grisette.Internal.Internal.Decl.Core.Data.Class.Mergeable
import Grisette.Internal.Internal.Impl.Core.Data.Class.Mergeable
  ( ComposeWrapper (ComposeWrapper),
    ContTWrapper (ContTWrapper),
    EitherFamily (..),
    EndoWrapper (EndoWrapper),
    IdentityTWrapper (IdentityTWrapper),
    LazyRWSTWrapper (LazyRWSTWrapper),
    ListFamily (..),
    MaybeFamily (..),
    NominalWrapper (NominalWrapper),
    ReaderTWrapper (ReaderTWrapper),
    StrictRWSTWrapper (StrictRWSTWrapper),
  )
