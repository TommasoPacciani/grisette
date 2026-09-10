{-# LANGUAGE GHC2024 #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE Strict #-}
{-# LANGUAGE TypeFamilies #-}
-- The solver transformer instances expand backend constraint families whose
-- decrease is not syntactically visible to GHC.
{-# LANGUAGE UndecidableInstances #-}

-- |
-- Module      :   Grisette.Internal.Backend.Solving
-- Copyright   :   (c) Sirui Lu 2021-2024
-- License     :   BSD-3-Clause (see the LICENSE file)
--
-- Maintainer  :   siruilu@cs.washington.edu
-- Stability   :   Experimental
-- Portability :   GHC only
module Grisette.Internal.Backend.Solving
  ( -- * SBV backend configuration
    GrisetteSMTConfig (..),
    boolector,
    bitwuzla,
    cvc4,
    cvc5,
    yices,
    dReal,
    z3,
    mathSAT,
    abc,

    -- * Changing the extra configurations
    ExtraConfig (..),
    withTimeout,
    clearTimeout,

    -- * SBV monadic solver interface
    SBVIncrementalT,
    SBVIncremental,
    runSBVIncrementalT,
    runSBVIncremental,

    -- * SBV solver handle
    SBVSolverHandle,

    -- * Internal lowering functions
    lowerSinglePrimCached,
    lowerSinglePrim,
    parseModel,
  )
where

import Control.Concurrent.Async (Async (asyncThreadId), asyncWithUnmask, wait)
import Control.Concurrent.STM
  ( TMVar,
    atomically,
    newTMVarIO,
    putTMVar,
    takeTMVar,
    tryReadTMVar,
    tryTakeTMVar,
  )
import Control.Concurrent.STM.TChan (TChan, newTChan, readTChan, writeTChan)
import Control.DeepSeq (force)
import Control.Exception
  ( Exception (displayException),
    SomeException,
    evaluate,
    handle,
    mask,
    mask_,
    onException,
    throwTo,
  )
import Control.Monad (when)
import Control.Monad.IO.Class (MonadIO, liftIO)
import Control.Monad.Reader
  ( MonadReader (ask),
    MonadTrans (lift),
    ReaderT (runReaderT),
    ask,
  )
import Control.Monad.STM (STM)
import Control.Monad.State.Strict
  ( MonadState (get, put),
    StateT,
    evalStateT,
  )
import Data.Dynamic (Dynamic, fromDyn, fromDynamic, toDyn)
import qualified Data.HashMap.Strict as HM
import qualified Data.HashSet as HS
import Data.IORef (IORef, modifyIORef', newIORef, readIORef, writeIORef)
import qualified Data.List as L
import Data.Maybe (catMaybes)
import Data.List.NonEmpty (NonEmpty)
import Grisette.Internal.SymPrim.Uninterp (uninterpConSBVPrefix)
import Data.Proxy (Proxy (Proxy))
import qualified Data.SBV as SBV
import qualified Data.SBV.Control as SBVC
import qualified Data.SBV.Dynamic as SBVD
import qualified Data.SBV.Internals as SBVI
import qualified Data.SBV.List as SBVL
import qualified Data.SBV.Trans as SBVT
import qualified Data.SBV.Trans.Control as SBVTC
import qualified Data.SBV.Tuple as SBVTuple
import qualified Data.Text as T
import GHC.IO.Exception (ExitCode (ExitSuccess))
import GHC.Stack (HasCallStack)
import Grisette.Internal.Backend.QuantifiedStack
  ( QuantifiedStack,
    QuantifiedSymbols,
    addQuantified,
    addQuantifiedSymbol,
    emptyQuantifiedStack,
    emptyQuantifiedSymbols,
    isQuantifiedSymbol,
    lookupQuantified,
    nullQuantifiedSymbols,
  )
import Grisette.Internal.Backend.SymBiMap
  ( SymBiMap,
    addBiMap,
    addBiMapIntermediate,
    attachNextQuantifiedSymbolInfo,
    emptySymBiMap,
    findStringToSymbol,
    findSymbolToString,
    lookupTerm,
    sizeBiMap,
  )
import Grisette.Internal.Core.Data.Class.ModelOps
  ( ModelOps (emptyModel, insertValue),
  )
import Grisette.Internal.Core.Data.Class.Solver
  ( ConfigurableSolver (newSolver),
    ModelProjection (AllModelSymbols, OnlyModelSymbols),
    MonadicSolver
      ( monadicSolverAssert,
        monadicSolverCheckSat,
        monadicSolverPop,
        monadicSolverPush,
        monadicSolverResetAssertions
      ),
    Solver
      ( solverCheckSat,
        solverForceTerminate,
        solverRunCommand,
        solverTerminate
      ),
    SolverCommand
      ( SolverAssert,
        SolverCheckSat,
        SolverPop,
        SolverPush,
        SolverResetAssertions,
        SolverTerminate
      ),
    SolvingFailure (SolvingError, Terminated, Unk, Unsat),
  )
import Grisette.Internal.Core.Data.MemoUtils (weakStableMemo)
import Grisette.Internal.SymPrim.GeneralFun
  ( substTerm,
    type (-->) (GeneralFun),
  )
import Grisette.Internal.SymPrim.Prim.Model as PM
  ( Model,
    SymbolSet (SymbolSet),
  )
import Grisette.Internal.SymPrim.Prim.SomeTerm (SomeTerm (SomeTerm))
import Grisette.Internal.SymPrim.Prim.Term
  ( PEvalApplyTerm (sbvApplyTerm),
    PEvalBVTerm (sbvBVConcatTerm, sbvBVExtendTerm, sbvBVSelectTerm),
    PEvalBitCastOrTerm (sbvBitCastOr),
    PEvalBitCastTerm (sbvBitCast),
    PEvalBitwiseTerm
      ( sbvAndBitsTerm,
        sbvComplementBitsTerm,
        sbvOrBitsTerm,
        sbvXorBitsTerm
      ),
    PEvalDivModIntegralTerm
      ( sbvDivIntegralTerm,
        sbvModIntegralTerm,
        sbvQuotIntegralTerm,
        sbvRemIntegralTerm
      ),
    PEvalFPTerm
      ( sbvFPBinaryTerm,
        sbvFPFMATerm,
        sbvFPRoundingBinaryTerm,
        sbvFPRoundingUnaryTerm,
        sbvFPTraitTerm,
        sbvFPUnaryTerm
      ),
    PEvalFloatingTerm (sbvFloatingUnaryTerm, sbvPowerTerm),
    PEvalFractionalTerm (sbvFdivTerm, sbvRecipTerm),
    PEvalFromIntegralTerm (sbvFromIntegralTerm),
    PEvalIEEEFPConvertibleTerm (sbvFromFPOrTerm, sbvToFPTerm),
    PEvalNumTerm
      ( sbvAbsNumTerm,
        sbvAddNumTerm,
        sbvMulNumTerm,
        sbvNegNumTerm,
        sbvSignumNumTerm
      ),
    PEvalOrdTerm (sbvLeOrdTerm, sbvLtOrdTerm),
    PEvalRotateTerm (sbvRotateLeftTerm, sbvRotateRightTerm),
    PEvalShiftTerm (sbvShiftLeftTerm, sbvShiftRightTerm),
    SBVFreshMonad,
    SBVRep (SBVType),
    SomeTypedAnySymbol,
    SomeTypedSymbol (SomeTypedSymbol),
    SupportedNonFuncPrim (conNonFuncSBVTerm, withNonFuncPrim),
    SupportedPrim
      ( conSBVTerm,
        castTypedSymbol,
        funcDummyConstraint,
        parseSMTModelResult,
        sbvDistinct,
        sbvEq,
        sbvIte,
        symSBVName,
        symSBVTerm,
        withPrim
      ),
    SymbolKind (AnyKind),
    Term,
    FocusedSeqFoldCallback
      ( FocusedSeqFoldCallbackBind,
        FocusedSeqFoldCallbackBody
      ),
    FocusedSeqFoldOperands
      ( FocusedSeqFoldOperand,
        NoFocusedSeqFoldOperands
      ),
    TypedConstantSymbol,
    TypedSymbol (TypedSymbol),
    someTypedSymbol,
    symTerm,
    pattern AbsNumTerm,
    pattern AddNumTerm,
    pattern AndBitsTerm,
    pattern AndTerm,
    pattern ApplyTerm,
    pattern BVConcatTerm,
    pattern BVExtendTerm,
    pattern BVSelectTerm,
    pattern BitCastOrTerm,
    pattern BitCastTerm,
    pattern ComplementBitsTerm,
    pattern ConTerm,
    pattern DistinctTerm,
    pattern DivIntegralTerm,
    pattern EqTerm,
    pattern ExistsTerm,
    pattern FPBinaryTerm,
    pattern FPFMATerm,
    pattern FPRoundingBinaryTerm,
    pattern FPRoundingUnaryTerm,
    pattern FPTraitTerm,
    pattern FPUnaryTerm,
    pattern FdivTerm,
    pattern FloatingUnaryTerm,
    pattern ForallTerm,
    pattern FromFPOrTerm,
    pattern FromIntegralTerm,
    pattern ITETerm,
    pattern LeOrdTerm,
    pattern LtOrdTerm,
    pattern ModIntegralTerm,
    pattern MulNumTerm,
    pattern NegNumTerm,
    pattern NotTerm,
    pattern OrBitsTerm,
    pattern OrTerm,
    pattern PowerTerm,
    pattern QuotIntegralTerm,
    pattern RecipTerm,
    pattern RemIntegralTerm,
    pattern RotateLeftTerm,
    pattern RotateRightTerm,
    pattern ShiftLeftTerm,
    pattern ShiftRightTerm,
    pattern SignumNumTerm,
    pattern SupportedTerm,
    pattern SymTerm,
    pattern ToFPTerm,
    pattern XorBitsTerm,
    pattern SelectTerm,
    pattern StoreTerm,
    pattern ConstArrayTerm,
    pattern SeqConsTerm,
    pattern SeqAppendTerm,
    pattern SeqZipTerm,
    pattern SeqLengthTerm,
    pattern SeqRangeTerm,
    pattern SeqTailTerm,
    pattern SeqResizeTerm,
    pattern SeqUpdateTerm,
    pattern SeqLookupTerm,
    pattern SeqLookupValueTerm,
    pattern SeqFoldTerm,
    pattern FocusedSeqFoldTerm,
    pattern SeqFoldWithTerm,
    pattern PairTerm,
    pattern FirstTerm,
    pattern SecondTerm,
  )
import Grisette.Internal.SymPrim.SymBool (SymBool (SymBool))

-- $setup
-- >>> import Grisette.Core
-- >>> import Grisette.SymPrim
-- >>> import Grisette.Backend
-- >>> import Data.Proxy

-- | Grisette specific extra configurations for the SBV backend.
newtype ExtraConfig = ExtraConfig
  { -- | Timeout in microseconds for each solver call. CEGIS may call the
    -- solver multiple times and each call has its own timeout.
    timeout :: Maybe Int
  }

-- | Solver configuration for the Grisette SBV backend.
--
-- A Grisette solver configuration consists of a SBV solver configuration and
-- some extra configurations.
--
-- You should start with the predefined configurations.
data GrisetteSMTConfig = GrisetteSMTConfig
  { sbvConfig :: SBV.SMTConfig,
    extraConfig :: ExtraConfig
  }

preciseExtraConfig :: ExtraConfig
preciseExtraConfig = ExtraConfig {timeout = Nothing}

-- | Solver configuration for Boolector. <https://boolector.github.io/>
boolector :: GrisetteSMTConfig
boolector = GrisetteSMTConfig SBV.boolector preciseExtraConfig

-- | Solver configuration for Bitwuzla. <https://bitwuzla.github.io/>
bitwuzla :: GrisetteSMTConfig
bitwuzla = GrisetteSMTConfig SBV.bitwuzla preciseExtraConfig

-- | Solver configuration for CVC4. <https://cvc4.github.io/>
cvc4 :: GrisetteSMTConfig
cvc4 = GrisetteSMTConfig SBV.cvc4 preciseExtraConfig

-- | Solver configuration for CVC5. <https://cvc5.github.io/>
cvc5 :: GrisetteSMTConfig
cvc5 = GrisetteSMTConfig SBV.cvc5 preciseExtraConfig

-- | Solver configuration for Yices. <https://yices.csl.sri.com/>
yices :: GrisetteSMTConfig
yices = GrisetteSMTConfig SBV.yices preciseExtraConfig

-- | Solver configuration for DReal. <http://dreal.github.io/>
dReal :: GrisetteSMTConfig
dReal = GrisetteSMTConfig SBV.dReal preciseExtraConfig

-- | Solver configuration for Z3. <https://github.com/Z3Prover/z3/>
z3 :: GrisetteSMTConfig
z3 = GrisetteSMTConfig SBV.z3 preciseExtraConfig

-- | Solver configuration for MathSAT. <http://mathsat.fbk.eu/>
mathSAT :: GrisetteSMTConfig
mathSAT = GrisetteSMTConfig SBV.mathSAT preciseExtraConfig

-- | Solver configuration for ABC. <http://www.eecs.berkeley.edu/~alanmi/abc/>
abc :: GrisetteSMTConfig
abc = GrisetteSMTConfig SBV.abc preciseExtraConfig

-- | Set the timeout for the solver configuration.
--
-- The timeout is in microseconds (1e-6 seconds). The timeout is applied to each
-- individual solver query.
withTimeout :: Int -> GrisetteSMTConfig -> GrisetteSMTConfig
withTimeout t config =
  config {extraConfig = (extraConfig config) {timeout = Just t}}

-- | Clear the timeout for the solver configuration.
clearTimeout :: GrisetteSMTConfig -> GrisetteSMTConfig
clearTimeout config =
  config {extraConfig = (extraConfig config) {timeout = Nothing}}

sbvCheckSatResult :: SBVC.CheckSatResult -> SolvingFailure
sbvCheckSatResult SBVC.Sat = error "Should not happen"
sbvCheckSatResult (SBVC.DSat _) = error "DSat is currently not supported"
sbvCheckSatResult SBVC.Unsat = Unsat
sbvCheckSatResult SBVC.Unk = Unk

-- | Apply the timeout to the configuration.
applyTimeout ::
  (MonadIO m, SBVTC.MonadQuery m) => GrisetteSMTConfig -> m a -> m a
applyTimeout config q = case timeout (extraConfig config) of
  Nothing -> q
  Just t -> SBVTC.timeout t q

-- | Incremental solver monad transformer with the SBV backend.
type SBVIncrementalT m =
  ReaderT GrisetteSMTConfig (StateT SymBiMap (SBVTC.QueryT m))

-- | Incremental solver monad with the SBV backend.
type SBVIncremental = SBVIncrementalT IO

-- | Run the incremental solver monad with a given configuration.
runSBVIncremental :: GrisetteSMTConfig -> SBVIncremental a -> IO a
runSBVIncremental = runSBVIncrementalT

-- | Run the incremental solver monad transformer with a given configuration.
runSBVIncrementalT ::
  (SBVTC.ExtractIO m) =>
  GrisetteSMTConfig ->
  SBVIncrementalT m a ->
  m a
runSBVIncrementalT config sbvIncrementalT =
  SBVT.runSMTWith (sbvConfig config) $
    SBVTC.query $
      applyTimeout config $
        flip evalStateT emptySymBiMap $
          runReaderT sbvIncrementalT config

instance (MonadIO m) => MonadicSolver (SBVIncrementalT m) where
  monadicSolverAssert (SymBool formula) = do
    symBiMap <- get
    (newSymBiMap, lowered, dummyConstraint) <-
      lowerSinglePrimCached formula symBiMap
    lift $ lift $ SBV.constrain dummyConstraint
    lift $ lift $ SBV.constrain (lowered emptyQuantifiedStack)
    put newSymBiMap
  monadicSolverCheckSat projection = do
    config <- ask
    symBiMap <- get
    requested <- case projection of
      AllModelSymbols -> pure Nothing
      OnlyModelSymbols (SymbolSet symbols) ->
        Just . catMaybes <$> traverse (prepareModelQuery symBiMap)
          (HS.toList symbols)
    checkSatResult <- SBVTC.checkSat
    case checkSatResult of
      SBVC.Sat -> do
        sbvModel <- case requested of
          Nothing -> SBVTC.getModel
          Just queries -> SBVI.getModelFor queries
        -- CV/function decoders may fail lazily. Finish conversion inside this
        -- command, before the worker publishes a result or releases ownership.
        model <- liftIO $ evaluate $ force $ parseModel config sbvModel symBiMap
        return $ Right model
      r -> return $ Left $ sbvCheckSatResult r
  monadicSolverResetAssertions = SBVTC.resetAssertions
  monadicSolverPush = SBVTC.push
  monadicSolverPop = SBVTC.pop

-- Only the free-symbol registration index can authorize readback. In QueryT,
-- every primitive symSBVTerm is freshVar, which synchronizes its declaration
-- before returning a cached free-variable SVal. Extracting that existing SV
-- here cannot create an expression or declaration, and happens before checkSat.
-- Functions use their exact registered name, without saturating opaque domains.
prepareModelQuery ::
  forall m. (MonadIO m) =>
  SymBiMap ->
  SomeTypedAnySymbol ->
  SBVIncrementalT m (Maybe SBVI.ModelQuery)
prepareModelQuery symBiMap symbol@(SomeTypedSymbol (typed@TypedSymbol {} :: TypedSymbol 'AnyKind value)) =
  case findSymbolToString symbol symBiMap of
    Nothing -> pure Nothing
    Just name -> case castTypedSymbol typed :: Maybe (TypedConstantSymbol value) of
      Nothing -> pure $ Just $ SBVI.ModelFunction name
      Just TypedSymbol {} -> withNonFuncPrim @value $
        case lookupTerm (SomeTerm $ symTerm typed) symBiMap of
          Nothing -> inconsistent name
          Just lowered -> case fromDynamic (lowered emptyQuantifiedStack) :: Maybe (SBVType value) of
            Nothing -> inconsistent name
            Just variable -> do
              state <- SBVTC.queryState
              sv <- liftIO $ SBVI.sbvToSV state variable
              pure $ Just $ SBVI.ModelInput name sv
  where
    inconsistent :: forall result. String -> SBVIncrementalT m result
    inconsistent name = liftIO $ ioError $ userError $
      "Grisette projected model: registered free symbol has no matching lowered value: " ++ name

data SBVSolverStatus = SBVSolverNormal | SBVSolverTerminated

-- | The handle type for the SBV solver.
--
-- See 'ConfigurableSolver' and 'Solver' for the interfaces.
data SBVSolverHandle = SBVSolverHandle
  { sbvSolverHandleMonad :: Async (),
    sbvSolverHandleStatus :: TMVar SBVSolverStatus,
    sbvSolverHandleInChan :: TChan SolverCommand,
    sbvSolverHandleOutChan :: TChan (Either SolvingFailure Model)
  }

setTerminated :: TMVar SBVSolverStatus -> STM ()
setTerminated status = do
  _ <- tryTakeTMVar status
  putTMVar status SBVSolverTerminated

instance ConfigurableSolver GrisetteSMTConfig SBVSolverHandle where
  newSolver config = mask_ $ do
    sbvSolverHandleInChan <- atomically newTChan
    sbvSolverHandleOutChan <- atomically newTChan
    sbvSolverHandleStatus <- newTMVarIO SBVSolverNormal
    sbvSolverHandleMonad <- asyncWithUnmask $ \unmask -> do
      let handler (e :: SomeException) =
            liftIO $
              atomically $ do
                setTerminated sbvSolverHandleStatus
                writeTChan
                  sbvSolverHandleOutChan
                  (Left (SolvingError $ T.pack $ displayException e))
      -- withSolver acquires this worker under mask. Restore true unmasked
      -- execution, not the inherited MaskedInterruptible state: lowering can
      -- allocate for a long time without reaching an interruptible IO action.
      handle handler $ unmask $ runSBVIncremental config $ do
        let loop = do
              nextFormula <-
                liftIO $ atomically $ readTChan sbvSolverHandleInChan
              case nextFormula of
                SolverPush n -> monadicSolverPush n >> loop
                SolverPop n -> monadicSolverPop n >> loop
                SolverTerminate -> return ()
                SolverResetAssertions -> monadicSolverResetAssertions >> loop
                SolverAssert formula -> do
                  monadicSolverAssert formula
                  loop
                SolverCheckSat projection -> do
                  r <- monadicSolverCheckSat projection
                  liftIO $ atomically $ writeTChan sbvSolverHandleOutChan r
                  loop
        loop
        liftIO $ atomically $ do
          setTerminated sbvSolverHandleStatus
          writeTChan sbvSolverHandleOutChan $ Left Terminated
    return $ SBVSolverHandle {..}

instance Solver SBVSolverHandle where
  solverRunCommand f handle@(SBVSolverHandle _ status inChan _) !command = mask $ \restore -> do
    st <- liftIO $ atomically $ takeTMVar status
    case st of
      SBVSolverNormal -> do
        liftIO $ atomically $ writeTChan inChan command
        -- Once dispatched, a cancelled reply consumer must not release this
        -- handle for reuse: its orphaned CheckSat response could be mistaken
        -- for the next command's result. Terminate the session instead.
        r <- restore (f handle) `onException` solverForceTerminate handle
        liftIO $ atomically $ do
          currStatus <- tryReadTMVar status
          case currStatus of
            Nothing -> putTMVar status SBVSolverNormal
            Just _ -> return ()
        return r
      SBVSolverTerminated -> do
        liftIO $ atomically $ setTerminated status
        return $ Left Terminated
  solverCheckSat handle projection =
    solverRunCommand
      ( \(SBVSolverHandle _ _ _ outChan) ->
          liftIO $ atomically $ readTChan outChan
      )
      handle
      (SolverCheckSat projection)
  solverTerminate (SBVSolverHandle thread status inChan _) = do
    liftIO $ atomically $ do
      setTerminated status
      writeTChan inChan SolverTerminate
    wait thread
  solverForceTerminate (SBVSolverHandle thread status _ outChan) = do
    liftIO $ atomically $ do
      setTerminated status
      writeTChan outChan (Left Terminated)
    throwTo (asyncThreadId thread) ExitSuccess
    wait thread

sbvForall,
  sbvExists ::
    forall t.
    (SupportedNonFuncPrim t) =>
    TypedConstantSymbol t ->
    (QuantifiedStack -> SBV.SBool) ->
    QuantifiedStack ->
    SBV.SBool
#if MIN_VERSION_sbv(10,1,0)
sbvForall sb r qst = withNonFuncPrim @t $
  SBV.quantifiedBool $
    \(SBV.Forall (a :: SBVType t)) ->
      r $ addQuantified sb (toDyn a) qst
sbvExists sb r qst = withNonFuncPrim @t $
  SBV.quantifiedBool $
    \(SBV.Exists (a :: SBVType t)) ->
      r $ addQuantified sb (toDyn a) qst
#else
sbvForall =
  error "Quantifiers are only available when you build with SBV 10.1.0 or later"
sbvExists =
  error "Quantifiers are only available when you build with SBV 10.1.0 or later"
#endif

-- | Exactly specialize a complete small literal driver at lowering time.
-- Inspect the Grisette term before realizing an SBV range: even asking whether
-- an SBV range is literal can first construct its entire host list. The budget
-- is an optimization policy, never a supported-population limit. Larger or
-- symbolic drivers keep the original native recursive fold.
trySmallLiteralFoldl
  :: forall element acc. SupportedNonFuncPrim element
  => Term [element]
  -> (acc -> SBVType element -> acc)
  -> acc
  -> Maybe acc
trySmallLiteralFoldl driver step initial = withNonFuncPrim @element $
  case literalValues of
    Nothing -> Nothing
    Just values -> Just $
      L.foldl' (\acc value -> step acc (conNonFuncSBVTerm @element value))
        initial values
  where
    literalValues :: Maybe [element]
    literalValues = case driver of
      ConTerm values | withinBudget 32 values -> Just values
      SeqRangeTerm (ConTerm count) | 0 <= count && count <= 32 ->
        Just [0 .. count - 1]
      _ -> Nothing

    -- Check the whole bounded spine before invoking the callback; never fold
    -- a prefix and then fall back. At most 33 spine cells are inspected.
    withinBudget :: Int -> [value] -> Bool
    withinBudget _ [] = True
    withinBudget 0 (_ : _) = False
    withinBudget remaining (_ : rest) = withinBudget (remaining - 1) rest

-- | SBV recursive functions cannot close over solver values. Keep focused
-- operands explicit in a typed closure environment at the lowering boundary;
-- the prepared Grisette callback and its heterogeneous operands stay separate.
data LoweredFocusedCallback state element where
  LoweredFocusedCallback ::
    SBV.SymVal environment =>
    (QuantifiedStack -> SBV.SBV environment) ->
    (QuantifiedStack -> SBV.SBV environment -> SBVType (state --> element --> state)) ->
    LoweredFocusedCallback state element

-- A lowered closure is reusable throughout one lexical scope, even when its
-- term mentions bound symbols. Its evaluated SBV value is reusable only for
-- the same immutable argument stack, not merely the same set of binder names.
-- Keep this cache separate from the solver-wide free-symbol/model registry.
data LoweringScope = LoweringScope
  !QuantifiedSymbols
  !(IORef (HM.HashMap SomeTerm (QuantifiedStack -> Dynamic)))

newLoweringScope :: MonadIO m => QuantifiedSymbols -> m LoweringScope
newLoweringScope symbols =
  LoweringScope symbols <$> liftIO (newIORef HM.empty)

extendLoweringScope
  :: MonadIO m
  => TypedConstantSymbol a -> LoweringScope -> m LoweringScope
extendLoweringScope symbol (LoweringScope symbols _) =
  newLoweringScope (addQuantifiedSymbol symbol symbols)

-- | Lower a single primitive term to SBV. With an explicitly provided
-- 'SymBiMap' cache.
lowerSinglePrimCached ::
  forall t m.
  (HasCallStack, SBVFreshMonad m) =>
  Term t ->
  SymBiMap ->
  m (SymBiMap, QuantifiedStack -> SBVType t, SBV.SBool)
lowerSinglePrimCached t' m' = do
  mapState <- liftIO $ newIORef m'
  accumulatedDummyConstraints <- liftIO $ newIORef SBV.sTrue
  let goCached ::
        forall x.
        LoweringScope ->
        Term x ->
        m (QuantifiedStack -> SBVType x)
      goCached scope@(LoweringScope symbols cache) t@SupportedTerm
        | nullQuantifiedSymbols symbols = goGlobal scope t
        | otherwise = do
            cached <- HM.lookup (SomeTerm t) <$> liftIO (readIORef cache)
            case cached of
              Just lowered -> pure $ \stack -> withPrim @x $
                fromDyn (lowered stack)
                  (error "BUG: Scoped lowering cache has an inconsistent term type")
              Nothing -> withPrim @x $ do
                lowered <- case t of
                  SymTerm symbol | not (isQuantifiedSymbol symbol symbols) ->
                    goGlobal scope t
                  _ -> goCachedImpl scope t
                let memoed = weakStableMemo lowered
                    {-# NOINLINE memoed #-}
                liftIO $ modifyIORef' cache $
                  HM.insert (SomeTerm t) (toDyn . memoed)
                pure memoed
      goGlobal ::
        forall x.
        LoweringScope ->
        Term x ->
        m (QuantifiedStack -> SBVType x)
      goGlobal scope t@SupportedTerm = do
        mp <- liftIO $ readIORef mapState
        case lookupTerm (SomeTerm t) mp of
          Just lowered -> pure $ \stack -> withPrim @x $
            fromDyn (lowered stack)
              (error "BUG: Global lowering cache has an inconsistent term type")
          Nothing -> goCachedImpl scope t
      goCachedImpl ::
        forall a.
        (SupportedPrim a) =>
        LoweringScope ->
        Term a ->
        m (QuantifiedStack -> SBVType a)
      goCachedImpl _ (ConTerm v) =
        return $ const $ conSBVTerm v
      goCachedImpl (LoweringScope symbols _) t@(SymTerm ts) = do
        if isQuantifiedSymbol ts symbols
          then withPrim @a $ do
            let retDyn qst =
                  case lookupQuantified (someTypedSymbol ts) qst of
                    Just v -> v
                    Nothing ->
                      error "BUG: Symbol not found in the quantified stack"
            return $
              \x ->
                fromDyn
                  (retDyn x)
                  (error "BUG: Symbol not found in the quantified stack")
          else withPrim @a $ do
            m <- liftIO $ readIORef mapState
            let ordinal = sizeBiMap m
                name =
                  "grisette.symbol."
                    <> show ordinal
                    <> "."
                    <> symSBVName ts ordinal
            g <- symSBVTerm @a name
            liftIO $
              modifyIORef' accumulatedDummyConstraints $
                \c -> c SBV..&& funcDummyConstraint @a g
            liftIO $
              modifyIORef' mapState $
                addBiMap (SomeTerm t) (toDyn g) name (someTypedSymbol ts)
            return $ const g
      goCachedImpl scope@(LoweringScope symbols _)
          t@(ForallTerm (ts :: TypedConstantSymbol t1) v) =
        withNonFuncPrim @t1 $ do
          do
            m <- liftIO $ readIORef mapState
            let (newm, sb) =
                  attachNextQuantifiedSymbolInfo m ts
            liftIO $ writeIORef mapState newm
            let substedTerm = substTerm ts (symTerm sb) HS.empty v
            nested <- extendLoweringScope sb scope
            r <- goCached nested substedTerm
            let ret = weakStableMemo (sbvForall sb r)
                {-# NOINLINE ret #-}
            when (nullQuantifiedSymbols symbols) $
              liftIO $
                modifyIORef' mapState $
                  addBiMapIntermediate (SomeTerm t) (toDyn . ret)
            return ret
      goCachedImpl scope@(LoweringScope symbols _)
          t@(ExistsTerm (ts :: TypedConstantSymbol t1) v) =
        withNonFuncPrim @t1 $ do
          do
            m <- liftIO $ readIORef mapState
            let (newm, sb) =
                  attachNextQuantifiedSymbolInfo m ts
            liftIO $ writeIORef mapState newm
            let substedTerm = substTerm ts (symTerm sb) HS.empty v
            nested <- extendLoweringScope sb scope
            r <- goCached nested substedTerm
            let ret = weakStableMemo (sbvExists sb r)
                {-# NOINLINE ret #-}
            when (nullQuantifiedSymbols symbols) $
              liftIO $
                modifyIORef' mapState $
                  addBiMapIntermediate (SomeTerm t) (toDyn . ret)
            return ret
      goCachedImpl scope@(LoweringScope symbols _) t =
        withPrim @a $ do
          r <- goCachedIntermediate scope t
          if nullQuantifiedSymbols symbols
            then do
              let memoed = weakStableMemo r
                  {-# NOINLINE memoed #-}
              liftIO $
                modifyIORef' mapState $
                  addBiMapIntermediate (SomeTerm t) (toDyn . memoed)
              return memoed
            else return r
      goGeneralFunBinder ::
        forall argument result.
        SupportedNonFuncPrim argument =>
        ( LoweringScope ->
          Term result ->
          m (QuantifiedStack -> SBVType result)
        ) ->
        LoweringScope ->
        Term (argument --> result) ->
        m (QuantifiedStack -> SBVType (argument --> result))
      goGeneralFunBinder lowerResult qs function@SupportedTerm = case function of
        ConTerm (GeneralFun binder (body@SupportedTerm)) ->
          withNonFuncPrim @argument $ do
            currentMap <- liftIO $ readIORef mapState
            let (nextMap, scopedBinder) =
                  attachNextQuantifiedSymbolInfo currentMap binder
                scopedBody = substTerm binder (symTerm scopedBinder) HS.empty body
            liftIO $ writeIORef mapState nextMap
            nested <- extendLoweringScope scopedBinder qs
            loweredBody <- lowerResult nested scopedBody
            pure $ \stack argument ->
              loweredBody (addQuantified scopedBinder (toDyn argument) stack)
        _ -> goCached qs function
      goCachedIntermediate ::
        forall a.
        (SupportedPrim a) =>
        LoweringScope ->
        Term a ->
        m (QuantifiedStack -> SBVType a)
      goCachedIntermediate qs (NotTerm t) = do
        r <- goCached qs t
        return $ \qst -> SBV.sNot (r qst)
      goCachedIntermediate qs (OrTerm a b) = do
        a' <- goCached qs a
        b' <- goCached qs b
        return $ \qst -> a' qst SBV..|| b' qst
      goCachedIntermediate qs (AndTerm a b) = do
        a' <- goCached qs a
        b' <- goCached qs b
        return $ \qst -> a' qst SBV..&& b' qst
      goCachedIntermediate qs (EqTerm (a :: Term v) b) = do
        a' <- goCached qs a
        b' <- goCached qs b
        return $
          \qst -> sbvEq @v (a' qst) (b' qst)
      goCachedIntermediate
        qs
        (DistinctTerm (args :: NonEmpty (Term t0))) = do
          args' <- traverse (goCached qs) args
          return $ \qst -> sbvDistinct @t0 (fmap ($ qst) args')
      goCachedIntermediate qs (ITETerm c a b) = do
        c' <- goCached qs c
        a' <- goCached qs a
        b' <- goCached qs b
        return $ \qst -> sbvIte @a (c' qst) (a' qst) (b' qst)
      goCachedIntermediate qs (AddNumTerm a b) = do
        a' <- goCached qs a
        b' <- goCached qs b
        return $ \qst -> sbvAddNumTerm @a (a' qst) (b' qst)
      goCachedIntermediate qs (NegNumTerm a) = do
        a' <- goCached qs a
        return $ sbvNegNumTerm @a . a'
      goCachedIntermediate qs (MulNumTerm a b) = do
        a' <- goCached qs a
        b' <- goCached qs b
        return $ \qst -> sbvMulNumTerm @a (a' qst) (b' qst)
      goCachedIntermediate qs (AbsNumTerm a) = do
        a' <- goCached qs a
        return $ sbvAbsNumTerm @a . a'
      goCachedIntermediate qs (SignumNumTerm a) = do
        a' <- goCached qs a
        return $ sbvSignumNumTerm @a . a'
      goCachedIntermediate qs (LtOrdTerm (a :: Term v) b) = do
        a' <- goCached qs a
        b' <- goCached qs b
        return $ \qst -> sbvLtOrdTerm @v (a' qst) (b' qst)
      goCachedIntermediate qs (LeOrdTerm (a :: Term v) b) = do
        a' <- goCached qs a
        b' <- goCached qs b
        return $ \qst -> sbvLeOrdTerm @v (a' qst) (b' qst)
      goCachedIntermediate qs (AndBitsTerm a b) = do
        a' <- goCached qs a
        b' <- goCached qs b
        return $ \qst -> sbvAndBitsTerm @a (a' qst) (b' qst)
      goCachedIntermediate qs (OrBitsTerm a b) = do
        a' <- goCached qs a
        b' <- goCached qs b
        return $ \qst -> sbvOrBitsTerm @a (a' qst) (b' qst)
      goCachedIntermediate qs (XorBitsTerm a b) = do
        a' <- goCached qs a
        b' <- goCached qs b
        return $ \qst -> sbvXorBitsTerm @a (a' qst) (b' qst)
      goCachedIntermediate qs (ComplementBitsTerm a) = do
        a' <- goCached qs a
        return $ sbvComplementBitsTerm @a . a'
      goCachedIntermediate qs (ShiftLeftTerm a b) = do
        a' <- goCached qs a
        b' <- goCached qs b
        return $ \qst -> sbvShiftLeftTerm @a (a' qst) (b' qst)
      goCachedIntermediate qs (ShiftRightTerm a b) = do
        a' <- goCached qs a
        b' <- goCached qs b
        return $ \qst -> sbvShiftRightTerm @a (a' qst) (b' qst)
      goCachedIntermediate qs (RotateLeftTerm a b) = do
        a' <- goCached qs a
        b' <- goCached qs b
        return $ \qst -> sbvRotateLeftTerm @a (a' qst) (b' qst)
      goCachedIntermediate qs (RotateRightTerm a b) = do
        a' <- goCached qs a
        b' <- goCached qs b
        return $ \qst -> sbvRotateRightTerm @a (a' qst) (b' qst)
      goCachedIntermediate qs (ApplyTerm (f :: Term f) a) = do
        l1 <- goCached qs f
        l2 <- goCached qs a
        return $ \qst -> sbvApplyTerm @f (l1 qst) (l2 qst)
      goCachedIntermediate qs (BitCastTerm (a :: Term x)) = do
        a' <- goCached qs a
        return $ sbvBitCast @x @a . a'
      goCachedIntermediate
        qs
        (BitCastOrTerm (d :: Term a) (a :: Term x)) = do
          d' <- goCached qs d
          a' <- goCached qs a
          return $ \qst -> sbvBitCastOr @x @a (d' qst) (a' qst)
      goCachedIntermediate
        qs
        (BVConcatTerm (a :: Term (bv l)) (b :: Term (bv r))) =
          do
            a' <- goCached qs a
            b' <- goCached qs b
            return $
              \qst ->
                sbvBVConcatTerm @bv (Proxy @l) (Proxy @r) (a' qst) (b' qst)
      goCachedIntermediate
        qs
        (BVExtendTerm signed (pr :: p r) (a :: Term (bv l))) =
          do
            a' <- goCached qs a
            return $ sbvBVExtendTerm @bv (Proxy @l) pr signed . a'
      goCachedIntermediate
        qs
        (BVSelectTerm (pix :: p ix) (pw :: q w) (a :: Term (bv n))) =
          do
            a' <- goCached qs a
            return $ sbvBVSelectTerm @bv pix pw (Proxy @n) . a'
      goCachedIntermediate qs (DivIntegralTerm a b) = do
        a' <- goCached qs a
        b' <- goCached qs b
        return $ \qst -> sbvDivIntegralTerm @a (a' qst) (b' qst)
      goCachedIntermediate qs (ModIntegralTerm a b) = do
        a' <- goCached qs a
        b' <- goCached qs b
        return $ \qst -> sbvModIntegralTerm @a (a' qst) (b' qst)
      goCachedIntermediate qs (QuotIntegralTerm a b) = do
        a' <- goCached qs a
        b' <- goCached qs b
        return $ \qst -> sbvQuotIntegralTerm @a (a' qst) (b' qst)
      goCachedIntermediate qs (RemIntegralTerm a b) = do
        a' <- goCached qs a
        b' <- goCached qs b
        return $ \qst -> sbvRemIntegralTerm @a (a' qst) (b' qst)
      goCachedIntermediate qs (FPTraitTerm trait (a :: Term (fp eb sb))) = do
        a' <- goCached qs a
        return $ sbvFPTraitTerm @fp @eb @sb trait . a'
      goCachedIntermediate qs (FdivTerm a b) = do
        a <- goCached qs a
        b <- goCached qs b
        return $ \qst -> sbvFdivTerm @a (a qst) (b qst)
      goCachedIntermediate qs (RecipTerm a) = do
        a <- goCached qs a
        return $ sbvRecipTerm @a . a
      goCachedIntermediate qs (FloatingUnaryTerm op a) = do
        a <- goCached qs a
        return $ sbvFloatingUnaryTerm @a op . a
      goCachedIntermediate qs (PowerTerm a b) = do
        a <- goCached qs a
        b <- goCached qs b
        return $ \qst -> sbvPowerTerm @a (a qst) (b qst)
      goCachedIntermediate qs (FPUnaryTerm op (a :: Term (fp eb sb))) = do
        a <- goCached qs a
        return $ sbvFPUnaryTerm @fp @eb @sb op . a
      goCachedIntermediate qs (FPBinaryTerm op (a :: Term (fp eb sb)) b) = do
        a <- goCached qs a
        b <- goCached qs b
        return $ \qst -> sbvFPBinaryTerm @fp @eb @sb op (a qst) (b qst)
      goCachedIntermediate qs (FPRoundingUnaryTerm op round (a :: Term (fp eb sb))) = do
        round <- goCached qs round
        a <- goCached qs a
        return $ \qst -> sbvFPRoundingUnaryTerm @fp @eb @sb op (round qst) (a qst)
      goCachedIntermediate qs (FPRoundingBinaryTerm op round (a :: Term (fp eb sb)) b) = do
        round <- goCached qs round
        a <- goCached qs a
        b <- goCached qs b
        return $ \qst -> sbvFPRoundingBinaryTerm @fp @eb @sb op (round qst) (a qst) (b qst)
      goCachedIntermediate qs (FPFMATerm round (a :: Term (fp eb sb)) b c) = do
        round <- goCached qs round
        a <- goCached qs a
        b <- goCached qs b
        c <- goCached qs c
        return $ \qst -> sbvFPFMATerm @fp @eb @sb (round qst) (a qst) (b qst) (c qst)
      goCachedIntermediate qs (FromIntegralTerm (b :: Term b)) = do
        b <- goCached qs b
        return $ sbvFromIntegralTerm @b @a . b
      goCachedIntermediate qs (FromFPOrTerm d mode arg) = do
        d <- goCached qs d
        mode <- goCached qs mode
        arg <- goCached qs arg
        return $ \qst -> sbvFromFPOrTerm @a (d qst) (mode qst) (arg qst)
      goCachedIntermediate qs (ToFPTerm mode (arg :: Term b) _ _) = do
        mode <- goCached qs mode
        arg <- goCached qs arg
        return $ \qst -> sbvToFPTerm @b (mode qst) (arg qst)
      goCachedIntermediate qs (SelectTerm (arr :: Term arr) key) = withPrim @arr $ do
        arr' <- goCached qs arr
        key' <- goCached qs key
        pure $ \qst -> SBV.readArray (arr' qst) (key' qst)
      goCachedIntermediate qs (StoreTerm arr key val) = withPrim @a $ do
        arr' <- goCached qs arr
        key' <- goCached qs key
        val' <- goCached qs val
        pure $ \qst -> SBV.writeArray (arr' qst) (key' qst) (val' qst)
      goCachedIntermediate qs (ConstArrayTerm _ val) = withPrim @a $ do
        val' <- goCached qs val
        pure $ \qst -> SBV.constArray $ val' qst
      goCachedIntermediate
        qs
        (SeqConsTerm (element :: Term element) sequence) =
          withNonFuncPrim @element $ do
            element' <- goCached qs element
            sequence' <- goCached qs sequence
            pure $ \qst -> element' qst SBVL..: sequence' qst
      goCachedIntermediate
        qs
        (SeqAppendTerm (left :: Term [element]) right) =
          withNonFuncPrim @element $ do
            left' <- goCached qs left
            right' <- goCached qs right
            pure $ \qst -> left' qst SBVL.++ right' qst
      goCachedIntermediate
        qs
        ( SeqZipTerm
            (left :: Term [leftElement])
            (right :: Term [rightElement])
          ) =
          withNonFuncPrim @leftElement $ withNonFuncPrim @rightElement $ do
            left' <- goCached qs left
            right' <- goCached qs right
            pure $ \qst -> SBVL.zip (left' qst) (right' qst)
      goCachedIntermediate qs (SeqLengthTerm (sequence :: Term [element])) =
        withNonFuncPrim @element $ do
          sequence' <- goCached qs sequence
          pure $ SBVL.length . sequence'
      goCachedIntermediate qs (SeqRangeTerm extent) = do
        extent' <- goCached qs extent
        pure $ \qst -> SBVL.enumFromTo @Integer 0 (extent' qst - 1)
      goCachedIntermediate qs (SeqTailTerm (sequence :: Term [element])) =
        withNonFuncPrim @element $ do
          sequence' <- goCached qs sequence
          pure $ SBVL.drop 1 . sequence'
      goCachedIntermediate qs
        (SeqResizeTerm seed count (sequence :: Term [element])) =
          withNonFuncPrim @element $ do
            seed' <- goCached qs seed
            count' <- goCached qs count
            sequence' <- goCached qs sequence
            pure $ \qst ->
              let source = sequence' qst
                  size = SBV.ite (count' qst SBV..<= 0) 0 (count' qst)
                  sourceLength = SBVL.length source
               in SBV.ite (size SBV..<= sourceLength)
                    (SBVL.take size source)
                    (source SBVL.++ SBVL.replicate (size - sourceLength) (seed' qst))
      goCachedIntermediate qs
        (SeqUpdateTerm index replacement (sequence :: Term [element])) =
          withNonFuncPrim @element $ do
            index' <- goCached qs index
            replacement' <- goCached qs replacement
            sequence' <- goCached qs sequence
            pure $ \qst ->
              let source = sequence' qst
                  position = index' qst
                  present = (0 SBV..<= position)
                    SBV..&& (position SBV..< SBVL.length source)
               in SBV.ite present
                    (SBVL.take position source SBVL.++
                      (replacement' qst SBVL..: SBVL.drop (position + 1) source))
                    source
      goCachedIntermediate
        qs
        (SeqLookupTerm seed (sequence :: Term [element]) index) =
          withNonFuncPrim @element $ do
            seed' <- goCached qs seed
            sequence' <- goCached qs sequence
            index' <- goCached qs index
            pure $ \qst ->
              let seedValue = seed' qst
                  sequenceValue = sequence' qst
                  indexValue = index' qst
                  present =
                    (0 SBV..<= indexValue)
                      SBV..&& (indexValue SBV..< SBVL.length sequenceValue)
                  selected =
                    SBV.ite
                      present
                      (SBVL.elemAt sequenceValue indexValue)
                      seedValue
               in SBVTuple.tuple (present, selected)
      goCachedIntermediate
        qs
        (SeqLookupValueTerm seed (sequence :: Term [element]) index) =
          withNonFuncPrim @element $ do
            seed' <- goCached qs seed
            sequence' <- goCached qs sequence
            index' <- goCached qs index
            pure $ \qst ->
              let seedValue = seed' qst
                  sequenceValue = sequence' qst
                  indexValue = index' qst
                  present =
                    (0 SBV..<= indexValue)
                      SBV..&& (indexValue SBV..< SBVL.length sequenceValue)
               in SBV.ite
                    present
                    (SBVL.elemAt sequenceValue indexValue)
                    seedValue
      goCachedIntermediate
        qs
        (SeqFoldTerm (step :: Term (state --> element --> state)) initial sequence) =
          withNonFuncPrim @state $ withNonFuncPrim @element $ do
            step' <-
              goGeneralFunBinder @state @(element --> state)
                ( goGeneralFunBinder @element @state $
                    \symbols term@SupportedTerm -> goCached symbols term
                )
                qs
                step
            initial' <- goCached qs initial
            sequence' <- goCached qs sequence
            pure $ \qst ->
              case trySmallLiteralFoldl sequence (step' qst) (initial' qst) of
                Just result -> result
                Nothing -> SBVL.foldl (step' qst) (initial' qst) (sequence' qst)
      goCachedIntermediate
        qs
        ( FocusedSeqFoldTerm
            callback
            operands
            (initial :: Term state)
            (sequence :: Term [element])
          ) =
          withNonFuncPrim @state $ withNonFuncPrim @element $ do
            LoweredFocusedCallback environment' step' <-
              lowerFocusedCallback qs qs callback operands
            initial' <- goCached qs initial
            sequence' <- goCached qs sequence
            pure $ \qst ->
              case trySmallLiteralFoldl sequence
                  (step' qst (environment' qst)) (initial' qst) of
                Just result -> result
                Nothing -> SBVL.foldl
                  SBV.Closure
                    { SBV.closureEnv = environment' qst,
                      SBV.closureFun = step' qst
                    }
                  (initial' qst) (sequence' qst)
          where
            lowerFocusedCallback
              :: forall captures state element.
                 LoweringScope
              -> LoweringScope
              -> FocusedSeqFoldCallback captures state element
              -> FocusedSeqFoldOperands captures
              -> m (LoweredFocusedCallback state element)
            lowerFocusedCallback _ callbackSymbols
                (FocusedSeqFoldCallbackBody step)
                NoFocusedSeqFoldOperands = do
              lowered <- goGeneralFunBinder @state @(element --> state)
                (goGeneralFunBinder @element @state $ \symbols term@SupportedTerm ->
                  goCached symbols term)
                callbackSymbols
                step
              pure $ LoweredFocusedCallback
                (const (SBV.literal ())) (\qst _ -> lowered qst)
            lowerFocusedCallback operandSymbols callbackSymbols
                (FocusedSeqFoldCallbackBind symbol rest)
                (FocusedSeqFoldOperand (operand :: Term capture) restOperands) =
              withNonFuncPrim @capture $ do
                operand' <- goCached operandSymbols operand
                nested <- extendLoweringScope symbol callbackSymbols
                LoweredFocusedCallback restEnvironment lowered <-
                  lowerFocusedCallback operandSymbols nested rest restOperands
                pure $ LoweredFocusedCallback
                  (\qst -> SBVTuple.tuple (operand' qst, restEnvironment qst))
                  (\qst environment ->
                    lowered
                      (addQuantified symbol (toDyn (SBVTuple.fst environment)) qst)
                      (SBVTuple.snd environment))
      goCachedIntermediate
        qs
        ( SeqFoldWithTerm
            (step :: Term (environment --> state --> element --> state))
            environment
            initial
            sequence
          ) =
          withNonFuncPrim @environment $
            withNonFuncPrim @state $
              withNonFuncPrim @element $ do
                step' <-
                  goGeneralFunBinder @environment @(state --> element --> state)
                    ( goGeneralFunBinder @state @(element --> state)
                        ( goGeneralFunBinder @element @state $
                            \symbols term@SupportedTerm -> goCached symbols term
                        )
                    )
                    qs
                    step
                environment' <- goCached qs environment
                initial' <- goCached qs initial
                sequence' <- goCached qs sequence
                pure $ \qst ->
                  case trySmallLiteralFoldl sequence
                      (step' qst (environment' qst)) (initial' qst) of
                    Just result -> result
                    Nothing -> SBVL.foldl
                      SBV.Closure
                        { SBV.closureEnv = environment' qst,
                          SBV.closureFun = step' qst
                        }
                      (initial' qst)
                      (sequence' qst)
      goCachedIntermediate
        qs
        (PairTerm (firstValue :: Term firstType) (secondValue :: Term secondType)) =
          withNonFuncPrim @firstType $ withNonFuncPrim @secondType $ do
            firstValue' <- goCached qs firstValue
            secondValue' <- goCached qs secondValue
            pure $ \qst -> SBVTuple.tuple (firstValue' qst, secondValue' qst)
      goCachedIntermediate
        qs
        (FirstTerm (pairValue :: Term (firstType, secondType))) =
          withNonFuncPrim @firstType $ withNonFuncPrim @secondType $ do
            pairValue' <- goCached qs pairValue
            pure $ SBVTuple.fst . pairValue'
      goCachedIntermediate
        qs
        (SecondTerm (pairValue :: Term (firstType, secondType))) =
          withNonFuncPrim @firstType $ withNonFuncPrim @secondType $ do
            pairValue' <- goCached qs pairValue
            pure $ SBVTuple.snd . pairValue'
      goCachedIntermediate _ ConTerm {} = error "Should not happen"
      goCachedIntermediate _ SymTerm {} = error "Should not happen"
      goCachedIntermediate _ ForallTerm {} = error "Should not happen"
      goCachedIntermediate _ ExistsTerm {} = error "Should not happen"
  initialScope <- newLoweringScope emptyQuantifiedSymbols
  r <- goCached initialScope t'
  m <- liftIO $ readIORef mapState
  constraint <- liftIO $ readIORef accumulatedDummyConstraints
  return (m, r, constraint)

-- | Lower a single primitive term to SBV.
lowerSinglePrim ::
  forall a m.
  (HasCallStack, SBVFreshMonad m) =>
  Term a ->
  m (SymBiMap, QuantifiedStack -> SBVType a, SBV.SBool)
lowerSinglePrim t =
  lowerSinglePrimCached t emptySymBiMap

#if MIN_VERSION_sbv(10,3,0)
preprocessUIFuncs ::
  [(String, (Bool, ty, Either String ([([SBVD.CV], SBVD.CV)], SBVD.CV)))] ->
  Maybe [(String, ([([SBVD.CV], SBVD.CV)], SBVD.CV))]
preprocessUIFuncs =
  traverse
    (\v -> case v of
      (a, (_, _, Right c)) -> Just (a, c)
      _ -> Nothing)
#elif MIN_VERSION_sbv(10,0,0)
preprocessUIFuncs ::
  [(String, (ty, Either String ([([SBVD.CV], SBVD.CV)], SBVD.CV)))] ->
  Maybe [(String, ([([SBVD.CV], SBVD.CV)], SBVD.CV))]
preprocessUIFuncs =
  traverse
    (\v -> case v of
      (a, (_, Right c)) -> Just (a, c)
      _ -> Nothing)
#else
preprocessUIFuncs ::
  [(String, (ty, ([([SBVD.CV], SBVD.CV)], SBVD.CV)))] ->
  Maybe [(String, ([([SBVD.CV], SBVD.CV)], SBVD.CV))]
preprocessUIFuncs = Just . fmap (\(a, (_, c)) -> (a, c))
#endif

-- | Parse an SBV model to a Grisette model.
parseModel ::
  GrisetteSMTConfig ->
  SBVI.SMTModel ->
  SymBiMap ->
  PM.Model
parseModel _ model@(SBVI.SMTModel _ _ assoc origFuncs) mp =
  case preprocessUIFuncs origFuncs of
    Just funcs ->
      foldr goSingle emptyModel $
        filter (not . isInternalDummy . fst) $
          funcs ++ assocFuncs
    _ -> error "SBV Failed to parse model"
  where
    assocFuncs = (\(s, v) -> (s, ([], v))) <$> assoc
    -- Internal nullary constants of an uninterpreted sort (introduced e.g. by
    -- 'funcDummyConstraint' pinning a UF over the sort) leak into the SBV model
    -- but are not Grisette symbols; they denote an arbitrary element, so drop
    -- them rather than failing the model-consistency check below.
    isInternalDummy = L.isPrefixOf uninterpConSBVPrefix
    goSingle :: (String, ([([SBVD.CV], SBVD.CV)], SBVD.CV)) -> PM.Model -> PM.Model
    goSingle (name, cv) m = case findStringToSymbol name mp of
      Just (SomeTypedSymbol (s@TypedSymbol {} :: TypedSymbol 'AnyKind r)) ->
        insertValue
          s
          (parseSMTModelResult 0 cv :: r)
          m
      Nothing ->
        error $
          "BUG: Please send a bug report. The model is not consistent with the "
            <> "list of symbols that have been defined. The map is "
            <> show mp
            <> ". The model is "
            <> show model
