{-# LANGUAGE NoImplicitPrelude #-}

-- |
-- Module      :   Grisette.SymPrim.SymArray
-- Copyright   :   (c) Sirui Lu 2021-2024
-- License     :   BSD-3-Clause (see the LICENSE file)
--
-- Maintainer  :   siruilu@cs.washington.edu
-- Stability   :   Experimental
-- Portability :   GHC only
--
-- Public interface to symbolic arrays (the SMT theory of arrays). The
-- operations 'const', 'select', and 'store' have generic names that collide
-- with 'Prelude' and other modules, so this module is designed to be imported
-- qualified, e.g.
--
-- > import qualified Grisette.SymPrim.SymArray as SymArray
--
-- The 'SymArray' type itself is also re-exported unqualified from
-- "Grisette.SymPrim" for use in type signatures.
module Grisette.SymPrim.SymArray
  ( SymArray (..),
    const,
    select,
    store,
  )
where

import Grisette.Internal.SymPrim.SymArray
  ( SymArray (..),
    const,
    select,
    store,
  )
