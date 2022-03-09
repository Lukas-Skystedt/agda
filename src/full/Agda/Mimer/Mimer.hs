module Agda.Mimer.Mimer
  ( MimerResult(..)
  , mimer
  )
  where

import Data.Maybe (maybeToList, fromMaybe, maybe)
import Control.Monad (forM, zipWithM, (>=>), filterM, (<=<))
import Control.Monad.Except (catchError)
import Control.Monad.State (StateT, gets)
import qualified Data.Map as Map
import Data.List (sortOn, isSuffixOf, intercalate)
import Data.Maybe (isJust)
import Data.Function (on)
import qualified Data.IntSet as IntSet

import Agda.Auto.Convert (findClauseDeep)
import Agda.Compiler.Backend (getMetaContextArgs, TCState(..), PostScopeState(..), Open(..), isOpenMeta, getContextTerms)
import Agda.Interaction.Base
import Agda.Interaction.Base (Rewrite(..))
import Agda.Interaction.BasicOps (typeOfMetaMI, contextOfMeta )
import Agda.Interaction.Response (ResponseContextEntry(..))
import Agda.Syntax.Abstract (Expr)
import Agda.Syntax.Abstract.Name (QName(..))
import Agda.Syntax.Common (InteractionId, MetaId(..), Arg(..), ArgInfo(..), defaultArgInfo, Origin(..),Induction(..), ConOrigin(..), Hiding(..), setOrigin)
import Agda.Syntax.Internal (MetaId, Type, Type''(..), Term(..), Dom'(..), Abs(..), Elim, Elim'(..), arity
                            , ConHead(..), DataOrRecord(..), Args, argFromDom, Level'(..), PlusLevel'(..))
import Agda.Syntax.Position (Range)
import Agda.Syntax.Translation.InternalToAbstract (reify)
import Agda.TypeChecking.CheckInternal (infer)
import Agda.TypeChecking.Constraints (noConstraints)
import Agda.TypeChecking.Conversion (equalType)
import Agda.TypeChecking.Datatypes (isDataOrRecordType)
import Agda.TypeChecking.MetaVars (checkSubtypeIsEqual, newValueMeta)
import Agda.TypeChecking.Monad.MetaVars (LocalMetaStores(..))
import Agda.TypeChecking.Monad -- (MonadTCM, lookupInteractionId, getConstInfo, liftTCM, clScope, getMetaInfo, lookupMeta, MetaVariable(..), metaType, typeOfConst, getMetaType, MetaInfo(..), getMetaTypeInContext)
import Agda.TypeChecking.Monad.Base (TCM)
import Agda.TypeChecking.Pretty (prettyTCM, PrettyTCM(..))
import Agda.TypeChecking.Records (isRecord, getRecordFieldNames)
import Agda.TypeChecking.Reduce (normalise, reduce)
import Agda.TypeChecking.Rules.Term (lambdaAddContext)
import Agda.TypeChecking.Substitute (piApply, raise)
import Agda.TypeChecking.Substitute.Class (apply)
import Agda.TypeChecking.Telescope (piApplyM, flattenTel)
import Agda.Utils.Impossible (__IMPOSSIBLE__)
import Agda.Utils.Maybe (catMaybes)
import Agda.Utils.Permutation (idP)
import Agda.Utils.Pretty (prettyShow, render, pretty)
import Agda.Utils.Tuple (mapSnd)
import Agda.Utils.Monad (unlessM)
import Agda.Utils.Pretty (text)
import qualified Agda.Syntax.Scope.Base as Scope
import qualified Agda.TypeChecking.Monad.Base as TCM

import Debug.Trace
import System.IO.Unsafe (unsafePerformIO)
import Control.Monad.IO.Class (liftIO)

newtype MimerResult = MimerResult String


mimer :: MonadTCM tcm
  => InteractionId
  -> Range
  -> String
  -> tcm MimerResult
mimer ii range hint = liftTCM $ do
    oldState <- getTC
    runBfs ii
    putTC oldState
    -- The meta variable to solve
    -- metaI <- lookupInteractionId ii
    -- s <- runDfs ii >>= \case
    --   Just expr -> showTCM $ expr
    --   Nothing -> return ""
    let s = "?"


    openMetas <- getOpenMetas
    mlog $ "Remaining open metas: " ++ prettyShow openMetas
    putTC oldState
    return $ MimerResult $ s


-- Order to try things in:
-- 1. Local variables (including let-bound)
-- 2. Data constructors
-- 3. Where clauses
-- 4. Lambda abstract
-- Other: Equality, empty type, record projections
-- - If we only use constructors if the target type is a data type, we might
--   generate η-reducible expressions, e.g. λ xs → _∷_ 0 xs


type TypedTerm = (Term, Type)


-- TODO: withInteractionId to get the right context
runDfs :: InteractionId -> TCM (Maybe Expr)
runDfs ii = withInteractionId ii $ do
  theFunctionQName <- ipcQName . ipClause <$> lookupInteractionPoint ii
  mlog $ "Interaction point inside: " ++ prettyShow theFunctionQName
  -- TODO: What normalization should we use here?
  -- TODO: The problem with `contextOfMeta` is that it gives `Expr`. However, it does include let-bindings.
  context <- contextOfMeta ii AsIs
  strs <- mapM (\entry -> showTCM (respType entry) >>= \s -> return $ prettyShow (respOrigName entry) ++ " : " ++ s) context
  mlog $ "contextOfMeta: " ++ intercalate ", " strs

  context' <- getContext
  mlog $ "getContext: " ++ prettyShow context'

  localVars <- getLocalVars
  mlog $ "getLocalVars: " ++ prettyShow localVars

  -- TODO: Handle the `Open` stuff
  letVars <- asksTC envLetBindings >>= mapM (fmap (mapSnd unDom) . getOpen . snd) . Map.toAscList
  mlog $ "let-bound vars: " ++ prettyShow letVars


  metaId <- lookupInteractionId ii
  metaVar <- lookupLocalMeta metaId
  metaArgs <- getMetaContextArgs metaVar
  mlog $ "getMetaContextArgs: " ++ prettyShow metaArgs


  -- We remove the name of the function the interaction point occurs in to prevent
  -- arbitrary recursive calls
  hintNames1 <- filter (/= theFunctionQName) <$> getEverythingInScope metaVar
  records <- filterM (fmap isJust . isRecord) hintNames1
  recordProjs <- concat  <$> mapM getRecordFields records
  let hintNames = hintNames1 ++ recordProjs
  hints <- sortOn (arity . snd) . catMaybes <$> mapM qnameToTerm hintNames
  let hints' = filter (\(d,_) -> case d of Def{} -> True; _ -> False) hints
  mlog $ "Using hints: " ++ prettyShow (map fst hints')
  -- TODO: Remove @letVars ++@
  resTerm <- dfs (letVars ++ hints') 4 metaId

  mlog $ "dfs result term: " ++ prettyShow resTerm

  metaVar' <- lookupLocalMeta metaId
  case mvInstantiation metaVar' of
    InstV inst -> do
      termStr <- showTCM (instBody inst)
      mlog $ "instantiated to (showTCM):  " ++ termStr
      termStrNorm <- showTCM =<< normalise (instBody inst)
      mlog $ "instantiated (nf):  " ++ termStrNorm
      debugRecord (instBody inst)
      Just <$> reify (instBody inst)
    _ -> return Nothing
  where
    debugRecord = \case
      Con ch ci es -> do
        mlog $ "instantiation is a con: " ++ prettyShow ch ++ " " ++ show ci ++ " " ++ prettyShow es
        let s e = case e of
                    Apply arg -> case unArg arg of
                      MetaV m _ -> do
                        mv <- lookupLocalMeta m
                        case mvInstantiation mv of
                          InstV inst' -> ((prettyShow m ++ "=") ++) <$> showTCM (instBody inst')
                          _ -> return ""
                      _ -> return ""
                    _ -> return ""
        mapM s es >>= \str -> mlog $ "  where " ++ unwords str

      _ -> return ()

getRecordFields :: QName -> TCM [QName]
getRecordFields = fmap (map unDom . recFields . theDef) . getConstInfo

qnameToTerm :: QName -> TCM (Maybe (Term, Type))
qnameToTerm qname = do
  info <- getConstInfo qname
  typ <- typeOfConst qname
  let mTerm = case theDef info of
        Axiom{} -> Just $ Def qname []
        DataOrRecSig{} -> Nothing -- TODO
        GeneralizableVar -> Just $ Def qname []
        AbstractDefn{} -> Nothing -- TODO
        Function{} -> Just $ Def qname []
        Datatype{} -> Just $ Def qname []
        Record{} -> Just $ Def qname []
        c@Constructor{} -> Just $ Con (conSrcCon c) ConOCon []
        Primitive{} -> Just $ Def qname [] -- TODO
        PrimitiveSort{} -> Just $ Def qname [] -- TODO

  return ((,typ) <$> mTerm)


-- TODO: Check how giveExpr (intercation basic ops) -- v' <- instantiate $ MetaV mi $ map Apply ctx
dfs :: [(Term, Type)] -> Int -> MetaId -> TCM (Maybe Term)
dfs hints depth metaId = do
  metaVar <- lookupLocalMeta metaId
  -- Check if meta is already instantiated
  case mvInstantiation metaVar of
    InstV inst -> do
      mlog $ "dfs: meta " ++ prettyShow metaId ++ " already instantiated to " ++ prettyShow (instBody inst)
      return $ Just $ instBody inst
    -- Meta not instantiated, check if max depth is reached
    _ | depth <= 0 -> return Nothing
      -- Max depth not reached, continue search
      | otherwise -> do
          metaType <- reduce =<< getMetaTypeInContext metaId
          localVars <- getLocalVars
          go localVars
            `elseTry` tryDataCon hints depth metaId
            `elseTry` go hints
            `elseTry` tryLambda hints depth metaId
  where
    go [] = return Nothing
    go ((hintTerm, hintType):hs) = do
      mTerm <- tryRefine hints depth metaId hintTerm hintType
      case mTerm of
        Just term -> return $ Just term
        Nothing -> go hs

tryDataCon :: [(Term, Type)] -> Int -> MetaId -> TCM (Maybe Term)
tryDataCon hints depth metaId = do
  nonReducedMetaType <- getMetaTypeInContext metaId
  metaType <- reduce nonReducedMetaType
  case unEl metaType of
    Def qname elims -> isDataOrRecordType qname >>= \case
      Just IsData -> do
        info <- getConstInfo qname
        case theDef info of
          dataDefn@Datatype{} -> (fmap sequence $ mapM qnameToTerm $ dataCons dataDefn) >>= \case
            Nothing -> error ""
            Just cs ->
              let go [] = return Nothing
                  go ((term,typ):cs') = tryRefine hints depth metaId term typ `elseTry` go cs'
              in go (sortOn (arity . snd) cs) -- Try the constructors with few arguments first
          _ -> __IMPOSSIBLE__ -- return Nothing
      -- TODO: pattern/copattern
      Just IsRecord{} -> do
        info <- getConstInfo qname
        case theDef info of
          -- TODO: is ConORec appropriate?
          -- TODO: There is a `getRecordConstructor` function
          -- TODO: instantiate the hint term with meta variables for the fields
          recordDefn@Record{} -> do
            let cHead = recConHead recordDefn
                cName = conName cHead
                hintTerm = Con cHead ConORec []
            typ <- typeOfConst cName
            tryRefine hints depth metaId hintTerm typ
          _ -> __IMPOSSIBLE__ -- return Nothing
      _ -> return Nothing
    _ -> return Nothing


-- TODO: for adding binders: addToContext
-- TODO: Break out the part where we lookup the meta type etc.
tryRefine :: [(Term, Type)] -> Int -> MetaId -> Term -> Type -> TCM (Maybe Term)
tryRefine hints depth metaId hintTerm hintTyp = do
  metaVar <- lookupLocalMeta metaId
  metaType <- getMetaTypeInContext metaId
  metaArgs <- getMetaContextArgs metaVar
  go metaType metaArgs hintTerm hintTyp
  where
    go :: Type -> Args -> Term -> Type -> TCM (Maybe Term)
    go metaType metaArgs term nonreducedTyp = do
      typ <- reduce nonreducedTyp
      mlog $ "Trying " ++ prettyShow term ++ " : " ++ prettyShow typ ++ " to solve meta of type " ++ prettyShow metaType
      oldState <- getTC -- TODO: Backtracking state
      metasCreatedBy (dumbUnifier typ metaType) >>= \case
        -- The hint is applicable
        (True, newMetaStore) -> do
          let newMetaIds = Map.keys (openMetas newMetaStore)
          mlog $ "unifier succeeded, creating new metas: " ++ prettyShow newMetaIds ++ ".  Assigning " ++ prettyShow term ++ " to " ++ prettyShow metaId
          -- Solve any metas created during unification
          sequence <$> mapM (dfs hints (depth - 1)) newMetaIds >>= \case
            Just terms -> do
              assignV DirLeq metaId metaArgs term (AsTermsOf metaType)
              return $ Just term
            Nothing -> do
              putTC oldState
              return Nothing
        (False, _) -> case unEl typ of
          -- The hint may be applicable if we apply it to more metas
          Pi dom abs -> do
              putTC oldState
              let domainType = unDom dom
              -- TODO: What exactly does the occur check do?
              (metaId', metaTerm) <- newValueMeta DontRunMetaOccursCheck CmpLeq domainType
              mlog $ "Created new meta: " ++ prettyShow metaId'
              let arg = setOrigin Inserted $ metaTerm <$ argFromDom dom
              newType <- piApplyM typ metaTerm
              let newTerm = apply term [arg]
              go metaType metaArgs newTerm newType >>= \case
                Nothing -> do
                  putTC oldState
                  return Nothing
                -- Refinement success using the new meta as an argument
                Just resTerm -> do
                  mlog $ "Succeeded to find a matching term, solving remaining sub-meta: " ++ prettyShow metaId'
                  mSub <- dfs hints (depth - 1) metaId'
                  case mSub of
                    Just subTerm -> return $ Just resTerm
                    Nothing -> do
                      putTC oldState
                      return Nothing
          -- The hint is not applicable
          _ -> return Nothing
-- Termination checking:
-- Build call graph
-- Every cycle must have a "shrinking" arg

tryLambda :: [(Term, Type)] -> Int -> MetaId -> TCM (Maybe Term)
tryLambda hints depth metaId = do
  oldState <- getTC
  metaVar <- lookupLocalMeta metaId
  metaArgs <- getMetaContextArgs metaVar
  nonReducedMetaType <- getMetaTypeInContext metaId
  metaType <- reduce nonReducedMetaType
  -- TODO: check out `ifPi` or `ifPiType`
  case unEl metaType of
    Pi dom abs -> do
      -- TODO: look at `suggests`
      let bindName = absName abs
      newName <- freshName_ bindName
      mlog $ "Trying lambda with bindName " ++ prettyShow newName ++ " (generated from absName " ++ prettyShow (absName abs) ++ ")"
      -- TODO: `lambdaAddContext` vs `addContext`
      mSub <- lambdaAddContext newName bindName dom $ do
        context <- getContext
        mlog $ "  context inside lambda: " ++ prettyShow context

        -- TODO: due to problem with shifting indices, we lookup the type of the meta again in the extended context
        metaType' <- getMetaTypeInContext metaId
        bodyTyp <- piApplyM metaType' (Var 0 [])
        mlog $ "  body type inside lambda: " ++ prettyShow bodyTyp
        (metaId', metaTerm) <- newValueMeta DontRunMetaOccursCheck CmpLeq bodyTyp
        dfs hints (depth - 1) metaId'
      case mSub of
        Just body -> do
          let argInf = domInfo dom -- TODO: is this the correct arg info?
              newAbs = Abs{absName = bindName, unAbs = body}
              term = (Lam argInf newAbs)
          mlog $ "Lambda succeeded. Assigning " ++ prettyShow term ++ " to " ++ prettyShow metaId
          assignV DirLeq metaId metaArgs term (AsTermsOf metaType)
          return $ Just term
        Nothing -> do
          mlog "Lambda failed."
          putTC oldState
          return Nothing
    _ -> do
      putTC oldState
      return Nothing


data SearchBranch = SearchBranch
  { sbTCState :: TCState
  , sbUnsolvedMetas :: [MetaId]
  }

data Components = Components
  { topMeta :: MetaId
  , hintLocalVar :: [TypedTerm]
  -- ^ Variables from LHS of function definition or lambda abstraction
  , hintLet :: [TypedTerm]
  -- ^ Variables bound in let
  , hintFn :: [TypedTerm]
  -- ^ A function
  , hintWhere :: [TypedTerm]
  -- ^ A definition in a where clause
  }

-- | Search Monad
-- type SM a = TCMT (StateT Components IO) a
type SM a = TCM a

data SearchStepResult
  = ResultExpr Expr
  | OpenBranch SearchBranch
  | NoSolution

runBfs :: InteractionId -> SM ()
runBfs ii = withInteractionId ii $ do
  theFunctionQName <- ipcQName . ipClause <$> lookupInteractionPoint ii
  -- context <- contextOfMeta ii AsIs
  -- context' <- getContext
  letVars <- asksTC envLetBindings >>= mapM (fmap (mapSnd unDom) . getOpen . snd) . Map.toAscList
  metaId <- lookupInteractionId ii
  metaVar <- lookupLocalMeta metaId
  metaArgs <- getMetaContextArgs metaVar
  -- We remove the name of the function the interaction point occurs in to prevent
  -- arbitrary recursive calls
  hintNames1 <- filter (/= theFunctionQName) <$> getEverythingInScope metaVar
  records <- filterM (fmap isJust . isRecord) hintNames1
  recordProjs <- concat  <$> mapM getRecordFields records
  let hintNames = hintNames1 ++ recordProjs
  hints <- sortOn (arity . snd) . catMaybes <$> mapM qnameToTerm hintNames
  let hints' = filter (\(d,_) -> case d of Def{} -> True; _ -> False) hints

  state <- getTC
  let components = Components
        { topMeta = metaId
        , hintLocalVar = []
        , hintLet = []
        , hintFn = []
        , hintWhere = []
        }
      startBranch = SearchBranch { sbTCState = state, sbUnsolvedMetas = [metaId] }
  mlog =<< ("startBranch=" ++) <$> prettyBranch components startBranch
  oneStep <- bfsRefine components startBranch

  let go n branches
        | n <= 0 = return []
        | otherwise = do
          (branches', sols) <- partitionStepResult <$> concatMapM (bfsRefine components) branches
          mlog $ replicate 30 '#' ++ show n ++ replicate 30 '#'
          mapM_ (mlog <=< showTCM) sols
          mlog =<< (unlines <$> mapM (prettyBranch components) branches')
          mlog (replicate 61 '#')
          (sols ++) <$> go (n-1) branches'
  _ <- go 4 [startBranch]
  return ()
  where
    partitionStepResult :: [SearchStepResult] -> ([SearchBranch], [Expr])
    partitionStepResult [] = ([],[])
    partitionStepResult (x:xs) = case x of
      NoSolution -> rest
      OpenBranch br -> (br:brs,exps)
      ResultExpr exp -> (brs, exp:exps)
      where rest@(brs,exps) = partitionStepResult xs



bfsRefine :: Components -> SearchBranch -> SM [SearchStepResult]
bfsRefine s branch = do
  useBranchState branch
  (metaId, branch') <- nextBranchMeta' branch
  -- We reduce the meta type to WHNF(?) immediately to avoid refining it
  -- multiple times later (required e.g. to check if it is a Pi type)
  metaType <- reduce =<< getMetaTypeInContext metaId
  bfsLocals s metaId metaType branch'

-- | NOTE: the MetaId should already be removed from the SearchBranch when this function is called
bfsLocals :: Components -> MetaId -> Type -> SearchBranch -> SM [SearchStepResult]
bfsLocals s metaId metaType branch = do
  localVars <- getLocalVars
  newBranches <- concatMapM (uncurry $ bfsTryRefineAddMetas s metaId metaType branch) localVars
  mapM (checkSolved s) newBranches

checkSolved :: Components -> SearchBranch -> SM SearchStepResult
checkSolved s branch = do
  useBranchState branch
  openMetas <- getOpenMetas
  case filter (`elem` openMetas) (sbUnsolvedMetas branch) of
    [] -> do
      let metaId = topMeta s
      maybe NoSolution ResultExpr <$> getMetaInstantiation metaId
    remainingMetas -> return $ OpenBranch branch{sbUnsolvedMetas = remainingMetas}

-- | Type should already be reduced here
-- NOTE: Does not reset the state!
-- TODO: Make sure the type is always reduced
bfsTryRefineWith :: Components -> MetaId -> Type -> SearchBranch -> Term -> Type -> SM (Maybe SearchBranch)
bfsTryRefineWith s metaId metaType branch hintTerm hintType = do
  useBranchState branch
  metasCreatedBy (dumbUnifier hintType metaType) >>= \case
    (True, newMetaStore) -> do
      assignMeta metaId hintTerm metaType
      -- TODO: check if everything is solved?
      let newMetaIds = Map.keys (openMetas newMetaStore)
      Just <$> updateBranch newMetaIds branch
    (False, _) -> return Nothing

-- TODO: Make policy for when state should be put
bfsTryRefineAddMetas :: Components -> MetaId -> Type -> SearchBranch -> Term -> Type -> SM [SearchBranch]
bfsTryRefineAddMetas s metaId metaType branch hintTerm hintType = do
  -- Apply the hint to new metas (generating @c@, @c ?@, @c ? ?@, etc.)
  versions <- applyToMetas hintTerm hintType
  mlog $ "Refinements being tried: " ++ prettyShow (map (\(a,b,c,d) -> (a,b)) versions)
  res <- catMaybes <$> mapM doRefine versions
  mlog =<< (" ...successful: " ++) . unlines <$> mapM (prettyBranch s) res
  return res
  where
    doRefine :: (Term, Type, [MetaId], TCState) -> SM (Maybe SearchBranch)
    doRefine (term, typ, metaIds, state) = do
      let branch' = branch{sbTCState = state}
      fmap (addBranchMetas metaIds) <$> bfsTryRefineWith s metaId metaType branch' term typ

    -- TODO: Make sure the type is reduced the first time this is called
    applyToMetas :: Term -> Type -> SM [(Term, Type, [MetaId], TCState)]
    applyToMetas term typ = do
      state <- getTC
      ((term, typ, [], state) :) <$>
        case unEl typ of
          Pi dom abs -> do
            let domainType = unDom dom
            -- TODO: What exactly does the occur check do?
            (metaId', metaTerm) <- newValueMeta DontRunMetaOccursCheck CmpLeq domainType
            let arg = setOrigin Inserted $ metaTerm <$ argFromDom dom
            newType <- reduce =<< piApplyM typ metaTerm -- TODO: Is this the best place to reduce?
            let newTerm = apply term [arg]
            state <- getTC
            rest <- applyToMetas newTerm newType
            return $ map (\(term', typ', metas, state') -> (term', typ', metas ++ [metaId'], state')) rest
          _ -> return []

updateBranch :: [MetaId] -> SearchBranch -> SM SearchBranch
updateBranch newMetaIds branch = do
  state <- getTC
  return branch{ sbTCState = state
               , sbUnsolvedMetas = newMetaIds ++ sbUnsolvedMetas branch}

assignMeta :: MetaId -> Term -> Type -> SM ()
assignMeta metaId term metaType = do
  metaVar <- lookupLocalMeta metaId
  metaArgs <- getMetaContextArgs metaVar
  assignV DirLeq metaId metaArgs term (AsTermsOf metaType)

addBranchMetas :: [MetaId] -> SearchBranch -> SearchBranch
addBranchMetas newMetas branch = branch{sbUnsolvedMetas=newMetas ++ sbUnsolvedMetas branch}

useBranchState :: SearchBranch -> SM ()
useBranchState = putTC . sbTCState

nextBranchMeta' :: SearchBranch -> SM (MetaId, SearchBranch)
nextBranchMeta' = fmap (fromMaybe __IMPOSSIBLE__) . nextBranchMeta

nextBranchMeta :: SearchBranch -> SM (Maybe (MetaId, SearchBranch))
nextBranchMeta branch = case sbUnsolvedMetas branch of
  [] -> return Nothing
  (metaId : metaIds) ->
    return $ Just (metaId, branch{sbUnsolvedMetas=metaIds})


-- TODO: documentation for invariants
checkBranchInvariants :: SearchBranch -> SM ()
checkBranchInvariants branch = withLocalTCState (sbTCState branch) $
  case sbUnsolvedMetas branch of
    [] -> error "checkBranchInvariants: no metas in list"
    (metaId:_) -> unlessM (isMetaOpen metaId)
      (error "checkBranchInvariants: the head meta is not open")

isMetaOpen :: MetaId -> SM Bool
isMetaOpen metaId = (metaId `elem`) <$> getOpenMetas



getMetaInstantiation :: MetaId -> TCM (Maybe Expr)
getMetaInstantiation metaId = do
  metaVar <- lookupLocalMeta metaId
  case mvInstantiation metaVar of
    InstV inst -> Just <$> reify (instBody inst)
    _ -> return Nothing

getEverythingInScope :: MetaVariable -> TCM [QName]
getEverythingInScope metaVar = do
  let scope = clScope $ getMetaInfo metaVar
  let nameSpace = Scope.everythingInScope scope
      names = Scope.nsNames nameSpace
      qnames = map (Scope.anameName . head) $ Map.elems names
  mlog $ "getEverythingInScope, scope = " ++ prettyShow scope
  return qnames

  -- TODO: Look at getContextVars, locallyTC, getMetaScope

dumbUnifier :: Type -> Type -> TCM Bool
dumbUnifier t1 t2 =
  (noConstraints $ equalType t2 t1 >> return True) `catchError` \_err -> return False

getDomainType :: Type -> Type
getDomainType typ = case unEl typ of
  Pi dom _ -> unDom dom
  _ -> undefined

-- Duplicate of a local definition in Agda.Interaction.BasicOps
showTCM :: PrettyTCM a => a -> TCM String
showTCM v = render <$> prettyTCM v


concatUnzip :: [([a], [b])] -> ([a], [b])
concatUnzip xs = let (as, bs) = unzip xs in (concat as, concat bs)

-- partitionEithers :: [Either a b] -> ([a], [b])
-- partitionEithers [] = ([], [])
-- partitionEithers (e : es) = let (as, bs) = partitionEithers es in
--   case e of
--     Left a -> (a : as, bs)
--     Right b -> (as, b : bs)


mlog :: String -> TCM ()
mlog str = doLog str $ return ()

doLog :: String -> a -> a
doLog str e = unsafePerformIO $ do
  appendFile "/home/lukas/mimer.log" (str ++ "\n")
  return e

-- TODO: There is probably a standard way of doing this
elseTry :: Monad m => m (Maybe a) -> m (Maybe a) -> m (Maybe a)
elseTry ma ma1 = ma >>= \case
  Nothing -> ma1
  a@Just{} -> return a


metasInTerm :: Term -> [MetaId]
metasInTerm = \case
  Var _ es -> concatMap metasInElim es
  Lam _ abs -> metasInTerm $ unAbs abs
  Lit{} -> []
  Def _ es -> concatMap metasInElim es
  Con _ _ es -> concatMap metasInElim es
  Pi dom abs -> metasInType (unDom dom) ++ metasInType (unAbs abs)
  Sort{} -> []
  Level (Max _ pls) -> concatMap (\(Plus _ t) -> metasInTerm t) pls
  MetaV metaId es -> metaId : concatMap metasInElim es
  -- TODO: What are don't care and dummy term?
  DontCare _t -> []
  Dummy _ _es -> []

metasInType :: Type -> [MetaId]
metasInType = metasInTerm . unEl

metasInElim :: Elim -> [MetaId]
metasInElim = \case
  Apply arg -> metasInTerm $ unArg arg
  Proj{} -> []
  IApply t1 t2 t3 -> metasInTerm t1 ++ metasInTerm t2 ++ metasInTerm t3

isMetaIdOpen :: (MonadDebug m, ReadTCState m) => MetaId -> m Bool
isMetaIdOpen metaId = isOpenMeta . mvInstantiation <$> lookupLocalMeta metaId

openMetasInTerm :: Term -> TCM [MetaId]
openMetasInTerm = filterM isMetaIdOpen . metasInTerm

-- Local variables:
-- getContext :: MonadTCEnv m => m [Dom (Name, Type)]
-- getContextArgs :: (Applicative m, MonadTCEnv m) => m Args
-- getContextTelescope :: (Applicative m, MonadTCEnv m) => m Telescope
-- getContextTerms :: (Applicative m, MonadTCEnv m) => m [Term]
getLocalVars :: TCM [(Term, Type)]
getLocalVars = do
  contextTerms <- getContextTerms
  contextTypes <- map unDom . flattenTel <$> getContextTelescope
  return $ zip contextTerms contextTypes

prettyBranch :: Components -> SearchBranch -> SM String
prettyBranch s branch = do
    metas <- prettyTCM (sbUnsolvedMetas branch)
    let metaId = topMeta s
    inst <- getMetaInstantiation metaId
    return $ render $ text "Branch{metas: " <> metas <> text " , instantiation: " <> pretty metaId <> text "}"

prettySearchStepResult :: Components -> SearchStepResult -> SM String
prettySearchStepResult s = \case
  NoSolution -> return "No solution"
  OpenBranch branch -> ("Open branch: " ++) <$> prettyBranch s branch
  ResultExpr expr -> ("Result expression: " ++) <$> showTCM expr

concatMapM :: Monad m => (a -> m [b]) -> [a] -> m [b]
concatMapM f = fmap concat . mapM f

withLocalTCState :: MonadTCState m => TCState -> m a -> m a
withLocalTCState state ma = do
  state' <- getTC
  putTC state
  res <- ma
  putTC state'
  return res
