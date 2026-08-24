{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE Strict #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# OPTIONS_GHC -fno-cse #-}

-- |
-- Module      :   Grisette.Internal.SymPrim.Prim.Internal.Caches
-- Copyright   :   (c) Sirui Lu 2021-2024
-- License     :   BSD-3-Clause (see the LICENSE file)
--
-- Maintainer  :   siruilu@cs.washington.edu
-- Stability   :   Experimental
-- Portability :   GHC only
module Grisette.Internal.SymPrim.Prim.Internal.Caches
  ( SomeStableName (..),
    Id,
    StableIdent,
    Digest,
    CachedInfo (..),
    Interned (..),
    intern,
    haveCache,
    threadCacheSize,
    -- dumpThreadCache,
    threadCacheLiveSize,
  )
where

import Control.Concurrent
  ( MVar,
    ThreadId,
    myThreadId,
    newMVar,
    withMVar,
  )
import Control.Monad (replicateM)
import qualified Data.Array as A
import Data.Atomics (atomicModifyIORefCAS, atomicModifyIORefCAS_)
import Data.Data (Proxy (Proxy), Typeable, typeRepFingerprint)
import Data.Foldable (traverse_)
import qualified Data.HashMap.Strict as HM
import qualified Data.HashTable.IO as HT
import Data.Hashable (Hashable)
import Data.IORef (IORef, newIORef, readIORef, writeIORef)
import qualified Data.Vector.Unboxed.Mutable as M
import Data.Word (Word32)
import GHC.Base (Any)
import GHC.Fingerprint (Fingerprint)
import GHC.IO (unsafePerformIO)
import GHC.StableName (makeStableName)
import GHC.Weak (Weak, deRefWeak, finalize)
import Grisette.Internal.SymPrim.Prim.Internal.Utils
  ( SomeStableName (SomeStableName),
    WeakThreadId,
    WeakThreadIdRef,
    mkWeakStableNameValueWithFinalizer,
    mkWeakThreadIdRefWithFinalizer,
    myWeakThreadId,
    weakThreadId,
  )
import System.Mem.StableName (StableName)
import Type.Reflection (someTypeRep)
import Unsafe.Coerce (unsafeCoerce)

-- | A unique identifier for a term.
type Id = Word32

-- | The identity of a term.
type StableIdent = StableName Any

-- | A digest of a term.
type Digest = Word32

-- | Information about a cached term.
data CachedInfo = CachedInfo
  { cachedThreadId :: {-# UNPACK #-} !WeakThreadId,
    cachedDigest :: {-# UNPACK #-} !Digest,
    cachedId :: {-# UNPACK #-} !Id,
    cachedStableIdent :: {-# UNPACK #-} !StableIdent
  }

data Cache t = Cache
  { getCache :: A.Array Int (CacheState t),
    nextId :: M.IOVector Id
  }

type HashTable k v = HT.CuckooHashTable k v

data CacheState t where
  CacheState ::
    { _sem :: MVar (),
      _currentThread :: HashTable (Description t) (Weak t)
    } ->
    CacheState t

finalizeCacheState :: CacheState t -> IO ()
finalizeCacheState (CacheState sem s) = do
  refs <-
    withMVar sem $ const $
      HT.foldM (\acc (_, termRef) -> return $ termRef : acc) [] s
  traverse_ finalize refs

finalizeCache :: Cache t -> IO ()
finalizeCache (Cache a _) = mapM_ finalizeCacheState (A.elems a)

-- | A class for interning terms.
class Interned t where
  data Description t
  type Uninterned t
  describe :: Uninterned t -> Description t
  identify :: CachedInfo -> Uninterned t -> t
  threadId :: t -> WeakThreadId
  descriptionDigest :: Description t -> Digest

{-# NOINLINE termCacheCell #-}
termCacheCell ::
  IORef
    ( HM.HashMap
        WeakThreadId
        ( WeakThreadIdRef,
          IORef (HM.HashMap Fingerprint (Cache Any))
        )
    )
termCacheCell = unsafePerformIO $ newIORef HM.empty

cacheWidth :: Word32
cacheWidth = 10
{-# INLINE cacheWidth #-}

mkCache :: forall t. (Interned t) => IO (Cache t)
mkCache = result
  where
    element =
      CacheState
        <$> newMVar ()
        <*> HT.new
    result = do
      elements <- replicateM (fromIntegral cacheWidth) element
      nextId <- M.replicate 1 0
      return $
        Cache (A.listArray (0, fromIntegral cacheWidth - 1) elements) nextId

-- | Internal cache for memoization of term construction. Different types have
-- different caches and they may share names, ids, or representations, but they
-- are not the same term.
typeMemoizedCache ::
  forall a. (Interned a) => ThreadId -> Fingerprint -> IO (Cache a)
typeMemoizedCache tid tyFingerprint = do
  caches <- readIORef termCacheCell
  let wtid = weakThreadId tid
  case HM.lookup wtid caches of
    Just (_, cref) -> do
      cache <- readIORef cref
      case HM.lookup tyFingerprint cache of
        Just d -> return $ unsafeCoerce d
        Nothing -> do
          r1 <- mkCache
          writeIORef cref $!
            HM.insert tyFingerprint (unsafeCoerce r1) cache
          return r1
    Nothing -> do
      r1 <- mkCache
      r <- newIORef $ HM.singleton tyFingerprint (unsafeCoerce r1)
      wtidRef <-
        mkWeakThreadIdRefWithFinalizer tid $ do
          typeCaches <- readIORef r
          traverse_ finalizeCache (HM.elems typeCaches)
          atomicModifyIORefCAS_ termCacheCell (HM.delete wtid)
      atomicModifyIORefCAS termCacheCell $
        \m -> (HM.insert wtid (wtidRef, r) m, r1)

reclaimTerm ::
  forall t.
  (Interned t, Hashable (Description t), Eq (Description t)) =>
  WeakThreadId ->
  Fingerprint ->
  Int ->
  Description t ->
  IO ()
reclaimTerm wtid tyFingerprint grp dt = do
  caches <- readIORef termCacheCell
  case HM.lookup wtid caches of
    Just (_, cref) -> do
      cache <- readIORef cref
      case HM.lookup tyFingerprint cache of
        Just c -> do
          let Cache a _ = unsafeCoerce c :: Cache t
          let CacheState sem s = a A.! grp
          withMVar sem $ const $ do
            result <- HT.lookup s dt
            case result of
              Nothing -> return ()
              Just wr -> do
                maybeTerm <- deRefWeak wr
                case maybeTerm of
                  Nothing -> HT.delete s dt
                  Just _ -> return ()
        Nothing -> return ()
    Nothing -> return ()

-- | Internalize a term.
intern ::
  forall t.
  (Interned t, Typeable t, Hashable (Description t), Eq (Description t)) =>
  Uninterned t ->
  IO t
intern !bt = do
  tid <- myThreadId
  let wtid = weakThreadId tid
  let fingerprint = typeRepFingerprint $ someTypeRep (Proxy @t)
  cache <- typeMemoizedCache tid fingerprint
  let !dt = describe bt :: Description t
      !hdt = descriptionDigest dt
      !r = hdt `mod` cacheWidth
      CacheState sem s = getCache cache A.! (fromIntegral r)
  withMVar sem $ const $ do
    let newTerm = do
          newId0 <- M.unsafeRead (nextId cache) 0
          M.unsafeWrite (nextId cache) 0 (newId0 + 1)
          let newId = newId0 * cacheWidth + r
          newIdent <- makeStableName dt
          let anyNewIdent = unsafeCoerce newIdent :: StableIdent
          let !t = identify (CachedInfo wtid hdt newId anyNewIdent) bt
          termRef <-
            mkWeakStableNameValueWithFinalizer anyNewIdent t $
              reclaimTerm wtid fingerprint (fromIntegral r) dt
          HT.insert s dt termRef
          return t
    cached <- HT.lookup s dt
    case cached of
      Nothing -> newTerm
      Just oldTermRef -> do
        maybeTerm <- deRefWeak oldTermRef
        case maybeTerm of
          Nothing -> newTerm
          Just term -> return term
{-# NOINLINE intern #-}

-- | Check if the current thread has a cache.
haveCache :: IO Bool
haveCache = do
  caches <- readIORef termCacheCell
  tid <- myWeakThreadId
  return $ HM.member tid caches

cacheStateSize :: CacheState t -> IO Int
cacheStateSize (CacheState sem s) =
  withMVar sem $ const $ HT.foldM (\size _ -> return $ size + 1) 0 s

cacheStateLiveSize :: CacheState t -> IO Int
cacheStateLiveSize (CacheState sem s) =
  withMVar sem $ const $
    HT.foldM
      ( \live (_, termRef) -> do
          maybeTerm <- deRefWeak termRef
          case maybeTerm of
            Nothing -> return live
            Just _ -> return $ live + 1
      )
      0
      s

cacheSize :: Cache t -> IO Int
cacheSize (Cache a _) = sum <$> mapM cacheStateSize (A.elems a)

cacheLiveSize :: Cache t -> IO Int
cacheLiveSize (Cache a _) = sum <$> mapM cacheStateLiveSize (A.elems a)

-- | Get the size of the current thread's cache.
threadCacheSize :: WeakThreadId -> IO Int
threadCacheSize tid = do
  caches <- readIORef termCacheCell
  case HM.lookup tid caches of
    Just (_, cref) -> do
      cache <- readIORef cref
      sum <$> mapM cacheSize (HM.elems cache)
    Nothing -> return 0

-- | Get the live size of the current thread's cache.
threadCacheLiveSize :: WeakThreadId -> IO Int
threadCacheLiveSize tid = do
  caches <- readIORef termCacheCell
  case HM.lookup tid caches of
    Just (_, cref) -> do
      cache <- readIORef cref
      sum <$> mapM cacheLiveSize (HM.elems cache)
    Nothing -> return 0
