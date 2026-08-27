{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}

-- |
-- Module      :   Grisette.Internal.TH.Derivation.DeriveMergeable
-- Copyright   :   (c) Sirui Lu 2024
-- License     :   BSD-3-Clause (see the LICENSE file)
--
-- Maintainer  :   siruilu@cs.washington.edu
-- Stability   :   Experimental
-- Portability :   GHC only
module Grisette.Internal.TH.Derivation.DeriveMergeable
  ( deriveMergeable,
    deriveMergeable1,
    deriveMergeable2,
    deriveMergeable3,
    genMergeableAndGetMergingInfoResult,
    genMergeable,
    genMergeable',
    genMergeableNoExistential,
    genMergeableNoStrategy,
    genMergeableList,
  )
where

import Control.Monad (foldM, replicateM, zipWithM)
import qualified Data.Map as M
import Data.Maybe (catMaybes, mapMaybe)
import qualified Data.Set as S
import Grisette.Internal.Internal.Decl.Core.Data.Class.Mergeable
  ( Mergeable (rootStrategy),
    Mergeable1 (liftRootStrategy),
    Mergeable2 (liftRootStrategy2),
    Mergeable3 (liftRootStrategy3),
    MergingStrategy (NoStrategy, SimpleStrategy, StructuralStrategy),
    StructuralCase (StructuralCase),
    StructuralFamily (compareStructural, compareStructuralShape),
    StructuralOrdering (StructuralEQ, StructuralGT, StructuralLT),
    pairStrategy,
  )
import Grisette.Internal.TH.Derivation.Common
  ( CheckArgsResult
      ( CheckArgsResult,
        argVars,
        constructors,
        keptVars
      ),
    DeriveConfig (unconstrainedPositions, useNoStrategy),
    checkArgs,
    evalModeSpecializeList,
    extraConstraint,
    isVarUsedInFields,
    specializeResult,
    wrapEvalModeConstraintBody,
  )
import Grisette.Internal.TH.Util (mangleName)
import Language.Haskell.TH
  ( Bang (Bang),
    Body (NormalB),
    Clause (Clause),
    Con (ForallC, GadtC),
    Dec (DataD, FunD, InstanceD, PragmaD, SigD),
    Exp (AppE, ConE, VarE),
    Inline (Inline),
    Kind,
    Name,
    Pat (SigP, VarP, WildP),
    Phases (AllPhases),
    Pragma (InlineP),
    Pred,
    Q,
    RuleMatch (FunLike),
    SourceStrictness (NoSourceStrictness),
    SourceUnpackedness (NoSourceUnpackedness),
    Type (AppT, ArrowT, ConT, ForallT, StarT, TupleT, VarT),
    appE,
    conE,
    lookupTypeName,
    mkName,
    nameBase,
    newName,
    normalB,
    tupP,
    varE,
    varP,
    varT,
    wildP,
  )
import Language.Haskell.TH.Datatype
  ( ConstructorInfo
      ( constructorContext,
        constructorFields,
        constructorName,
        constructorVars
      ),
    DatatypeInfo (datatypeCons, datatypeName, datatypeVars),
    TypeSubstitution (applySubstitution, freeVariables),
    reifyDatatype,
    resolveTypeSynonyms,
    tvName,
  )
import Language.Haskell.TH.Datatype.TyVarBndr
  ( TyVarBndrUnit,
    kindedTVSpecified,
    plainTVFlag,
    plainTVReq,
    specifiedSpec,
  )
import Language.Haskell.TH.Lib (clause, conP)
import Type.Reflection
  ( SomeTypeRep (SomeTypeRep),
    TypeRep,
    eqTypeRep,
    typeRep,
    type (:~~:) (HRefl),
  )

payloadType :: [Type] -> Type
payloadType [] = ConT ''()
payloadType [field] = field
payloadType (field : fields) =
  AppT (AppT (TupleT 2) field) (payloadType fields)

payloadExp :: [Exp] -> Q Exp
payloadExp [] = conE '()
payloadExp [field] = pure field
payloadExp (field : fields) = [|($(pure field), $(payloadExp fields))|]

payloadPat :: [Name] -> Q Pat
payloadPat [] = conP '() []
payloadPat [field] = varP field
payloadPat (field : fields) = tupP [varP field, payloadPat fields]

payloadStrategyExp :: [Exp] -> Q Exp
payloadStrategyExp [] = [|SimpleStrategy $ \_ selected _ -> selected|]
payloadStrategyExp [strategy] = pure strategy
payloadStrategyExp (strategy : strategies) =
  [|pairStrategy $(pure strategy) $(payloadStrategyExp strategies)|]

compareTypeRepsExp :: [(Exp, Exp)] -> Q Exp
compareTypeRepsExp [] = conE 'StructuralEQ
compareTypeRepsExp ((leftRep, rightRep) : remaining) =
  [|
    case eqTypeRep $(pure leftRep) $(pure rightRep) of
      Just HRefl -> $(compareTypeRepsExp remaining)
      Nothing ->
        if SomeTypeRep $(pure leftRep) < SomeTypeRep $(pure rightRep)
          then StructuralLT
          else StructuralGT
    |]

compareTypeRepShapesExp :: [(Exp, Exp)] -> Q Exp
compareTypeRepShapesExp [] = conE 'EQ
compareTypeRepShapesExp ((leftRep, rightRep) : remaining) =
  [|
    case compare
      (SomeTypeRep $(pure leftRep))
      (SomeTypeRep $(pure rightRep)) of
      LT -> LT
      EQ -> $(compareTypeRepShapesExp remaining)
      GT -> GT
    |]

genMergingInfoCon ::
  [TyVarBndrUnit] ->
  Name ->
  Name ->
  Bool ->
  ConstructorInfo ->
  Q (Con, Name, [Clause], [Clause])
genMergingInfoCon dataTypeVars dataTypeName infoName isLast con = do
  let conName = mangleName $ constructorName con
  let newConName = mkName $ conName <> "MergingInfo"
  let originalVars = dataTypeVars ++ constructorVars con
  newDataTypeVars <- traverse (newName . nameBase . tvName) dataTypeVars
  newConstructorVars <-
    traverse (newName . nameBase . tvName) $ constructorVars con
  let newVars = VarT <$> newDataTypeVars ++ newConstructorVars
  let substMap = M.fromList $ zip (tvName <$> originalVars) newVars
  let fields = applySubstitution substMap $ constructorFields con
  let constructorVarTypes =
        applySubstitution
          substMap
          ((VarT . tvName) <$> constructorVars con)
  let typeRepFields = AppT (ConT ''TypeRep) <$> constructorVarTypes
  let targetType = foldl AppT (ConT dataTypeName) (VarT <$> newDataTypeVars)
  let resultType =
        AppT
          (AppT (ConT infoName) targetType)
          (payloadType fields)
  leftRepNames <- traverse (const $ newName "leftRep") typeRepFields
  rightRepNames <- traverse (const $ newName "rightRep") typeRepFields
  let leftPats = varP <$> leftRepNames
  let rightPats = varP <$> rightRepNames
  let allWildcards = replicate (length typeRepFields) wildP
  sameCompareClause <-
    clause
      [conP newConName leftPats, conP newConName rightPats]
      ( normalB $
          compareTypeRepsExp $
            zip (VarE <$> leftRepNames) (VarE <$> rightRepNames)
      )
      []
  earlierCompareClause <-
    clause
      [conP newConName allWildcards, wildP]
      (normalB $ conE 'StructuralLT)
      []
  laterCompareClause <-
    clause
      [wildP, conP newConName allWildcards]
      (normalB $ conE 'StructuralGT)
      []
  sameShapeClause <-
    clause
      [conP newConName leftPats, conP newConName rightPats]
      ( normalB $
          compareTypeRepShapesExp $
            zip (VarE <$> leftRepNames) (VarE <$> rightRepNames)
      )
      []
  earlierShapeClause <-
    clause
      [conP newConName allWildcards, wildP]
      (normalB $ conE 'LT)
      []
  laterShapeClause <-
    clause
      [wildP, conP newConName allWildcards]
      (normalB $ conE 'GT)
      []
  let structuralClauses =
        if isLast
          then [sameCompareClause]
          else [sameCompareClause, earlierCompareClause, laterCompareClause]
  let shapeClauses =
        if isLast
          then [sameShapeClause]
          else [sameShapeClause, earlierShapeClause, laterShapeClause]
  let context = applySubstitution substMap $ constructorContext con
  pure
    ( ForallC
        ( (`plainTVFlag` specifiedSpec)
            <$> newDataTypeVars ++ newConstructorVars
        )
        context
        $ GadtC
          [newConName]
          ( (Bang NoSourceUnpackedness NoSourceStrictness,)
              <$> typeRepFields
          )
          resultType,
      newConName,
      structuralClauses,
      shapeClauses
    )

data MergingInfoResult = MergingInfoResult
  { _infoName :: Name,
    _conInfoNames :: [Name]
  }

genMergingInfo :: Name -> Q (MergingInfoResult, [Dec])
genMergingInfo typName = do
  d <- reifyDatatype typName
  let originalName = mangleName $ datatypeName d
  let mergingInfoTypeName = originalName <> "MergingInfo"
  found <- lookupTypeName mergingInfoTypeName
  let constructors = datatypeCons d
  let name = mkName mergingInfoTypeName
  let generateConstructors [] = pure []
      generateConstructors [constructor] =
        (: [])
          <$> genMergingInfoCon
            (datatypeVars d)
            typName
            name
            True
            constructor
      generateConstructors (constructor : remaining) =
        (:)
          <$> genMergingInfoCon
            (datatypeVars d)
            typName
            name
            False
            constructor
          <*> generateConstructors remaining
  r <- generateConstructors constructors
  let cons = fmap (\(constructor, _, _, _) -> constructor) r
  let structuralClauses = concatMap (\(_, _, clauses, _) -> clauses) r
  let shapeClauses = concatMap (\(_, _, _, clauses) -> clauses) r
  valueName <- newName "value"
  payloadName <- newName "payload"
  return
    ( MergingInfoResult
        name
        (fmap (\(_, constructorName, _, _) -> constructorName) r),
      if maybe False (const True) found
        then []
        else
          [ DataD
              []
              name
              [plainTVReq valueName, plainTVReq payloadName]
              Nothing
              cons
              [],
            InstanceD
              Nothing
              []
              (ConT ''StructuralFamily `AppT` ConT name)
              [ FunD 'compareStructural structuralClauses,
                FunD 'compareStructuralShape shapeClauses
              ]
          ]
    )

-- | Generate 'Mergeable' instance and merging information for a data type.
genMergeableAndGetMergingInfoResult ::
  DeriveConfig -> Name -> Int -> Q (MergingInfoResult, [Dec])
genMergeableAndGetMergingInfoResult deriveConfig typName n = do
  (infoResult, infoDec) <- genMergingInfo typName
  (_, decs) <- genMergeable' deriveConfig infoResult typName n
  return (infoResult, infoDec ++ decs)

fieldStrategyExps ::
  [(Type, Kind)] ->
  ConstructorInfo ->
  Q ([Pat], [Exp])
fieldStrategyExps argTypes con = do
  fields <- traverse resolveTypeSynonyms $ constructorFields con
  let usedArgs = S.fromList $ freeVariables fields
  strategyNames <-
    traverse
      ( \(ty, _) -> case ty of
          VarT name
            | S.member name usedArgs -> Just <$> newName "strategy"
          _ -> pure Nothing
      )
      argTypes
  let strategyPats = fmap (maybe WildP VarP) strategyNames
  let argToStrategy =
        mapMaybe
          ( \((ty, _), maybeStrategy) -> case (ty, maybeStrategy) of
              (VarT name, Just strategyName) -> Just (name, strategyName)
              _ -> Nothing
          )
          (zip argTypes strategyNames)
  let argNameSet =
        S.fromList $
          mapMaybe
            ( \(ty, _) -> case ty of
                VarT name -> Just name
                _ -> Nothing
            )
            argTypes
  let containsArg ty =
        S.intersection argNameSet (S.fromList (freeVariables [ty])) /= S.empty
  let typeHasNoArg = not . containsArg
  let fieldStrategyExp ty
        | not (containsArg ty) = [|rootStrategy|]
        | otherwise = case ty of
            AppT constructor argument
              | typeHasNoArg constructor ->
                  [|liftRootStrategy $(fieldStrategyExp argument)|]
            AppT (AppT constructor first) second
              | typeHasNoArg constructor ->
                  [|
                    liftRootStrategy2
                      $(fieldStrategyExp first)
                      $(fieldStrategyExp second)
                    |]
            AppT (AppT (AppT constructor first) second) third
              | typeHasNoArg constructor ->
                  [|
                    liftRootStrategy3
                      $(fieldStrategyExp first)
                      $(fieldStrategyExp second)
                      $(fieldStrategyExp third)
                    |]
            VarT name -> case lookup name argToStrategy of
              Just strategyName -> varE strategyName
              Nothing -> fail "BUG: fieldStrategyExp"
            _ -> fail $ "fieldStrategyExp: unsupported type: " <> show ty
  strategies <- traverse fieldStrategyExp fields
  pure (strategyPats, strategies)

genPayloadStrategyClause ::
  (Q Exp -> Q Exp) ->
  [(Type, Kind)] ->
  Name ->
  ConstructorInfo ->
  Q Clause
genPayloadStrategyClause wrapBody argTypes conInfoName con = do
  let typeRepWildcards = replicate (length $ constructorVars con) wildP
  (strategyPats, strategies) <- fieldStrategyExps argTypes con
  strategy <- wrapBody $ payloadStrategyExp strategies
  clause
    ((pure <$> strategyPats) ++ [conP conInfoName typeRepWildcards])
    (normalB $ pure strategy)
    []

genInjectClause :: Name -> ConstructorInfo -> Q Clause
genInjectClause conInfoName con = do
  let keyFieldCount = length (constructorVars con)
  fieldNames <- replicateM (length $ constructorFields con) $ newName "field"
  clause
    [ conP conInfoName (replicate keyFieldCount wildP),
      payloadPat fieldNames
    ]
    ( normalB . pure $
        foldl AppE (ConE $ constructorName con) (VarE <$> fieldNames)
    )
    []

genMergingInfoFunClause' ::
  Name -> ConstructorInfo -> Q Clause
genMergingInfoFunClause' conInfoName con = do
  let conVars = constructorVars con
  capturedVarTyReps <-
    traverse (\bndr -> [|typeRep @($(varT $ tvName bndr))|]) conVars
  fieldNames <- replicateM (length $ constructorFields con) $ newName "field"
  let fieldPats =
        zipWith
          (\name fieldType -> pure $ SigP (VarP name) fieldType)
          fieldNames
          (constructorFields con)
  constructorPat <- conP (constructorName con) fieldPats
  let infoExpWithTypeReps = foldl AppE (ConE conInfoName) capturedVarTyReps
  let infoExp = infoExpWithTypeReps
  payload <- payloadExp $ VarE <$> fieldNames
  let structuralCaseExp =
        AppE
          (AppE (ConE 'StructuralCase) infoExp)
          payload
  pure $ Clause [constructorPat] (NormalB structuralCaseExp) []

mergeableNames :: Int -> Q (Name, Name)
mergeableNames 0 = pure (''Mergeable, 'rootStrategy)
mergeableNames 1 = pure (''Mergeable1, 'liftRootStrategy)
mergeableNames 2 = pure (''Mergeable2, 'liftRootStrategy2)
mergeableNames 3 = pure (''Mergeable3, 'liftRootStrategy3)
mergeableNames arity =
  fail $ "Mergeable derivation supports arities 0 through 3, not " <> show arity

-- | Generate 'Mergeable' instance for a data type, using a given merging info
-- result.
genMergeable' ::
  DeriveConfig -> MergingInfoResult -> Name -> Int -> Q (Name, [Dec])
genMergeable' deriveConfig (MergingInfoResult infoName conInfoNames) typName n = do
  result@CheckArgsResult {..} <-
    specializeResult (evalModeSpecializeList deriveConfig)
      =<< checkArgs "Mergeable" 3 typName True n

  d <- reifyDatatype typName
  let ctxForVar :: (Type, Kind) -> Q (Maybe Pred)
      ctxForVar (ty, kind) = case kind of
        StarT -> Just <$> [t|Mergeable $(return ty)|]
        AppT (AppT ArrowT StarT) StarT ->
          Just <$> [t|Mergeable1 $(return ty)|]
        AppT (AppT (AppT ArrowT StarT) StarT) StarT ->
          Just <$> [t|Mergeable2 $(return ty)|]
        AppT (AppT (AppT (AppT ArrowT StarT) StarT) StarT) StarT ->
          Just <$> [t|Mergeable3 $(return ty)|]
        AppT (AppT (AppT (AppT ArrowT StarT) StarT) StarT) _ ->
          fail $ "Unsupported kind: " <> show kind
        _ -> return Nothing
  let isTypeUsedInFields (VarT nm) = isVarUsedInFields result nm
      isTypeUsedInFields _ = False
  mergeableContexts <-
    traverse ctxForVar $
      filter (isTypeUsedInFields . fst) $
        fmap snd $
          filter (not . (`elem` unconstrainedPositions deriveConfig) . fst) $
            zip [0 ..] keptVars

  (instanceName, mergeInstanceFunName) <- mergeableNames n
  let instanceHead = ConT instanceName
  extraPreds <-
    extraConstraint
      deriveConfig
      typName
      instanceName
      []
      keptVars
      constructors

  let targetType =
        foldl
          (\ty (var, _) -> AppT ty var)
          (ConT typName)
          (keptVars ++ argVars)
  let infoType = ConT infoName
  let structuralCaseType =
        AppT (AppT (ConT ''StructuralCase) infoType) targetType
  let mergingInfoFunFinalType =
        AppT (AppT ArrowT targetType) structuralCaseType

  let mergingInfoFunType =
        ForallT
          ( mapMaybe
              ( \(ty, knd) -> case ty of
                  VarT nm -> Just $ kindedTVSpecified nm knd
                  _ -> Nothing
              )
              $ keptVars ++ argVars
          )
          []
          mergingInfoFunFinalType
  let mangledName = mangleName (datatypeName d)
  let mergingInfoFunName =
        mkName $
          "mergingInfo"
            <> (if n /= 0 then show n else "")
            <> mangledName
  let mergingInfoFunSigD = SigD mergingInfoFunName mergingInfoFunType
  clauses <-
    zipWithM genMergingInfoFunClause' conInfoNames constructors
  let mergingInfoFunDec = FunD mergingInfoFunName clauses

  let wrapBody = wrapEvalModeConstraintBody deriveConfig keptVars
  payloadTypeName <- newName "payload"
  valueTypeName <- newName "value"
  let payloadIndexedInfoType =
        AppT (AppT infoType targetType) (VarT payloadTypeName)
  let payloadStrategyFinalType =
        AppT
          (AppT ArrowT payloadIndexedInfoType)
          (AppT (ConT ''MergingStrategy) (VarT payloadTypeName))
  let payloadStrategyTypeWithoutContext =
        foldr
          (((AppT . AppT ArrowT) . AppT (ConT ''MergingStrategy)) . fst)
          payloadStrategyFinalType
          argVars
  let payloadStrategyFunType =
        ForallT
          ( mapMaybe
              ( \(ty, kind) -> case ty of
                  VarT name -> Just $ kindedTVSpecified name kind
                  _ -> Nothing
              )
              (keptVars ++ argVars)
              ++ [kindedTVSpecified payloadTypeName StarT]
          )
          (extraPreds ++ catMaybes mergeableContexts)
          payloadStrategyTypeWithoutContext
  let payloadStrategyFunName =
        mkName $
          "payloadStrategy"
            <> (if n /= 0 then show n else "")
            <> mangledName
  let payloadStrategyFunSigD =
        SigD payloadStrategyFunName payloadStrategyFunType
  payloadStrategyFunClauses <-
    zipWithM
      (genPayloadStrategyClause wrapBody argVars)
      conInfoNames
      constructors
  let payloadStrategyFunDec =
        FunD payloadStrategyFunName payloadStrategyFunClauses

  let injectFunType =
        let indexedInfoType =
              AppT (AppT infoType (VarT valueTypeName)) (VarT payloadTypeName)
         in ForallT
              [ kindedTVSpecified valueTypeName StarT,
                kindedTVSpecified payloadTypeName StarT
              ]
              []
              ( AppT
                  (AppT ArrowT indexedInfoType)
                  ( AppT
                      (AppT ArrowT (VarT payloadTypeName))
                      (VarT valueTypeName)
                  )
              )
  let injectFunName =
        mkName $
          "inject"
            <> (if n /= 0 then show n else "")
            <> mangledName
  let injectFunSigD = SigD injectFunName injectFunType
  injectFunClauses <- zipWithM genInjectClause conInfoNames constructors
  let injectFunDec = FunD injectFunName injectFunClauses

  let instanceType =
        AppT
          instanceHead
          (foldl AppT (ConT typName) $ fmap fst keptVars)

  mergeInstanceFunPatNames <- replicateM n $ newName "rootStrategy"
  let mergeInstanceFunPats = VarP <$> mergeInstanceFunPatNames

  mergeInstanceFunBody <-
    [|
      StructuralStrategy
        $(varE mergingInfoFunName)
        $( foldM
             (\exp name -> appE (return exp) $ varE name)
             (VarE payloadStrategyFunName)
             mergeInstanceFunPatNames
         )
        $(varE injectFunName)
      |]

  let mergeInstanceFunClause =
        Clause mergeInstanceFunPats (NormalB mergeInstanceFunBody) []

  return
    ( mergingInfoFunName,
      [ PragmaD (InlineP mergingInfoFunName Inline FunLike AllPhases),
        mergingInfoFunSigD,
        mergingInfoFunDec,
        PragmaD (InlineP payloadStrategyFunName Inline FunLike AllPhases),
        payloadStrategyFunSigD,
        payloadStrategyFunDec,
        PragmaD (InlineP injectFunName Inline FunLike AllPhases),
        injectFunSigD,
        injectFunDec,
        InstanceD
          Nothing
          (extraPreds ++ catMaybes mergeableContexts)
          instanceType
          [FunD mergeInstanceFunName [mergeInstanceFunClause]]
      ]
    )

-- | Generate 'Mergeable' instance for a data type without existential variables.
genMergeableNoExistential :: DeriveConfig -> Name -> Int -> Q [Dec]
genMergeableNoExistential deriveConfig typName n = do
  (infoResult, infoDec) <- genMergingInfo typName
  (_, decs) <- genMergeable' deriveConfig infoResult typName n
  pure $ infoDec ++ decs

-- | Generate 'Mergeable' instance for a data type, using 'NoStrategy'.
genMergeableNoStrategy :: DeriveConfig -> Name -> Int -> Q [Dec]
genMergeableNoStrategy deriveConfig typName n = do
  CheckArgsResult {..} <-
    specializeResult (evalModeSpecializeList deriveConfig)
      =<< checkArgs "Mergeable" 3 typName True n
  (instanceName, mergeInstanceFunName) <- mergeableNames n
  let instanceHead = ConT instanceName
  let instanceType =
        AppT
          instanceHead
          (foldl AppT (ConT typName) $ fmap fst keptVars)
  let mergeInstanceFunClause =
        Clause (replicate n WildP) (NormalB (ConE 'NoStrategy)) []
  return
    [ InstanceD
        Nothing
        []
        instanceType
        [FunD mergeInstanceFunName [mergeInstanceFunClause]]
    ]

-- | Generate 'Mergeable' instance for a data type.
genMergeable :: DeriveConfig -> Name -> Int -> Q [Dec]
genMergeable deriveConfig typName n = do
  datatype <- reifyDatatype typName
  if
    | useNoStrategy deriveConfig ->
        genMergeableNoStrategy deriveConfig typName n
    | null (datatypeCons datatype) ->
        genMergeableNoStrategy deriveConfig typName n
    | otherwise -> do
        (infoResult, infoDec) <- genMergingInfo typName
        (_, decs) <- genMergeable' deriveConfig infoResult typName n
        return $ infoDec ++ decs

-- | Generate multiple 'Mergeable' instances for a data type.
genMergeableList :: DeriveConfig -> Name -> [Int] -> Q [Dec]
genMergeableList _ _ [] = return []
genMergeableList deriveConfig typName [n] = genMergeable deriveConfig typName n
genMergeableList deriveConfig typName l@(n : ns) = do
  datatype <- reifyDatatype typName
  if
    | useNoStrategy deriveConfig ->
        concat <$> traverse (genMergeableNoStrategy deriveConfig typName) l
    | null (datatypeCons datatype) ->
        concat <$> traverse (genMergeableNoStrategy deriveConfig typName) l
    | otherwise -> do
        (info, dn) <-
          genMergeableAndGetMergingInfoResult
            deriveConfig
            typName
            n
        dns <-
          traverse (genMergeable' deriveConfig info typName) ns
        return $ dn ++ concatMap snd dns

-- | Derive 'Mergeable' instance for GADT.
deriveMergeable :: DeriveConfig -> Name -> Q [Dec]
deriveMergeable deriveConfig nm = genMergeable deriveConfig nm 0

-- | Derive 'Mergeable1' instance for GADT.
deriveMergeable1 :: DeriveConfig -> Name -> Q [Dec]
deriveMergeable1 deriveConfig nm = genMergeable deriveConfig nm 1

-- | Derive 'Mergeable2' instance for GADT.
deriveMergeable2 :: DeriveConfig -> Name -> Q [Dec]
deriveMergeable2 deriveConfig nm = genMergeable deriveConfig nm 2

-- | Derive 'Mergeable3' instance for GADT.
deriveMergeable3 :: DeriveConfig -> Name -> Q [Dec]
deriveMergeable3 deriveConfig nm = genMergeable deriveConfig nm 3
