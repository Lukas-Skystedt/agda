module Agda.Mimer.Mimer
  ( MimerResult(..)
  , mimer
  )
  where

import Data.Maybe (maybeToList, fromMaybe, maybe)
import Data.Functor ((<&>))
import Control.Monad (forM, zipWithM, (>=>), filterM, (<=<), unless, foldM)
import Control.Monad.Except (catchError)
import Control.Monad.State (StateT, gets)
import Control.Monad.Reader (ReaderT(..), runReaderT, mapReaderT, ask, asks)
import qualified Data.Map as Map
import Data.Map (Map)
import Data.List (sortOn, isSuffixOf, intercalate, intersect)
import Data.Maybe (isJust)
import Data.Function (on)
import qualified Data.IntSet as IntSet
import Data.Function (on)

import Data.Time.Clock (diffUTCTime, getCurrentTime, secondsToNominalDiffTime)
import qualified Data.PQueue.Min as Q
import Data.PQueue.Min (MinQueue)

import Agda.Compiler.Backend (getMetaContextArgs, TCState(..), PostScopeState(..), Open(..), isOpenMeta, getContextTerms)
import Agda.Interaction.Base
import Agda.Interaction.Base (Rewrite(..))
import Agda.Interaction.BasicOps (typeOfMetaMI, contextOfMeta, parseExprIn)
import Agda.Interaction.Response (ResponseContextEntry(..))
import Agda.Syntax.Abstract (Expr(AbsurdLam))
import Agda.Syntax.Abstract.Name (QName(..), Name(..))
import Agda.Syntax.Common (InteractionId, MetaId(..), Arg(..), ArgInfo(..), defaultArgInfo, Origin(..),Induction(..), ConOrigin(..), Hiding(..), setOrigin, NameId, ProblemId, Nat)
import Agda.Syntax.Info (exprNoRange)
import Agda.Syntax.Internal (MetaId, Type, Type''(..), Term(..), Dom'(..), Abs(..), Elim, Elim'(..), arity , ConHead(..), DataOrRecord(..), Args, Sort'(..), Sort, Level, argFromDom, Level'(..), PlusLevel'(..), absurdBody, Dom)
import Agda.Syntax.Internal.MetaVars (AllMetas(..))
import Agda.Syntax.Internal.Generic (TermLike, traverseTermM)
import Agda.Syntax.Position (Range)
import Agda.Syntax.Translation.InternalToAbstract (reify)
import Agda.TypeChecking.CheckInternal (infer)
import Agda.TypeChecking.Constraints (noConstraints)
import Agda.TypeChecking.Conversion (equalType)
import Agda.TypeChecking.Datatypes (isDataOrRecordType)
import Agda.TypeChecking.EtaContract (etaContract, etaLam)
import Agda.TypeChecking.MetaVars (checkSubtypeIsEqual, newValueMeta, ReduceAndEtaContract(..))
import Agda.TypeChecking.Monad -- (MonadTCM, lookupInteractionId, getConstInfo, liftTCM, clScope, getMetaInfo, lookupMeta, MetaVariable(..), metaType, typeOfConst, getMetaType, MetaInfo(..), getMetaTypeInContext)
import Agda.TypeChecking.Monad.Base (TCM)
import Agda.TypeChecking.Monad.MetaVars (LocalMetaStores(..))
import Agda.TypeChecking.Pretty (MonadPretty, prettyTCM, PrettyTCM(..))
import Agda.TypeChecking.Records (isRecord, getRecordFieldNames)
import Agda.TypeChecking.Reduce (normalise, reduce, instantiateFull, instantiate)
import Agda.TypeChecking.Rules.Term  (lambdaAddContext)
import Agda.TypeChecking.Substitute (piApply, raise)
import Agda.TypeChecking.Substitute.Class (apply)
import Agda.TypeChecking.Telescope (piApplyM, flattenTel)
import Agda.TypeChecking.Warnings (MonadWarning)
import qualified Agda.TypeChecking.Empty as Empty -- (isEmptyType)
import Agda.Utils.Impossible (__IMPOSSIBLE__)
import Agda.Utils.Maybe (catMaybes)
import Agda.Utils.Permutation (idP, permute, takeP)
import Agda.Utils.Pretty (Pretty, prettyShow, render, pretty, braces, prettyList_)
import Agda.Utils.Tuple (mapFst, mapSnd)
import Agda.Utils.Monad (unlessM)
import Agda.Utils.Pretty (text)
import qualified Agda.Syntax.Scope.Base as Scope
import qualified Agda.TypeChecking.Monad.Base as TCM

import Debug.Trace
import System.IO.Unsafe (unsafePerformIO)
import Control.Monad.IO.Class (liftIO)
import qualified Agda.Auto.Options as Opt
import qualified Agda.Auto.Auto as Auto
import Agda.Mimer.Options
newtype MimerResult = MimerResult String


mimer :: MonadTCM tcm
  => InteractionId
  -> Range
  -> String
  -> tcm MimerResult
mimer ii range argStr = liftTCM $  do
    opts <- parseOptions ii range argStr
    mlog $ show opts

    oldState <- getTC
    sols <- runBfs opts True ii
    putTC oldState
    -- The meta variable to solve
    -- metaI <- lookupInteractionId ii
    -- s <- runDfs ii >>= \case
    --   Just expr -> showTCM $ expr
    --   Nothing -> return ""
    let s = case sols of
          [] -> "?"
          (sol:_) -> sol

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

getRecordFields :: (HasConstInfo tcm, MonadTCM tcm) => QName -> tcm [QName]
getRecordFields = fmap (map unDom . recFields . theDef) . getConstInfo

qnameToTerm :: (MonadTCM tcm, HasConstInfo tcm, ReadTCState tcm) => QName -> tcm (Maybe (Term, Type))
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


qnameToComp :: (MonadTCM tcm, HasConstInfo tcm, ReadTCState tcm) => QName -> tcm (Maybe Component)
qnameToComp qname = fmap (uncurry $ mkComponentQ qname) <$> qnameToTerm qname

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
          localVars <- map (\c -> (compTerm c, compType c)) <$> getLocalVars
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
  -- , sbTCEnv :: TCEnv
  , sbGoals :: [Goal]
  , sbCost :: Int
  , sbComponentsUsed :: Map Name Int -- ^ Number of times each component has been used
  }

-- | NOTE: Equality is only on the field `sbCost`
instance Eq SearchBranch where
  sb1 == sb2 = sbCost sb1 == sbCost sb2 && sbGoals sb1 == sbGoals sb2


instance Ord SearchBranch where
  compare = compare `on` sbCost

data Goal = Goal
  { goalMeta :: MetaId
  , goalLetVars :: Maybe [Component]
  , goalLocalVars :: Maybe [Component]
  , goalEnv :: TCEnv
  }

-- TODO: Is this a reasonable Eq instance?
instance Eq Goal where
  g1 == g2 = goalMeta g1 == goalMeta g2

-- | Create a goal in the current environment
mkGoal :: MonadTCEnv m => MetaId -> m Goal
mkGoal metaId = do
  env <- askTC
  return Goal
    { goalMeta = metaId
    , goalLetVars = Nothing
    , goalLocalVars = Nothing
    , goalEnv = env
    }

mkGoalPreserveLocalsAndEnv :: Goal -> MetaId -> Goal
mkGoalPreserveLocalsAndEnv goalLocalSource metaId = Goal
  { goalMeta = metaId
  , goalLetVars = goalLetVars goalLocalSource
  , goalLocalVars = goalLocalVars goalLocalSource
  , goalEnv = goalEnv goalLocalSource
  }

-- | Components that are not changed during search. Components that do change
-- (local variables and let bindings) are stored in each 'SearchBranch'.
data Components = Components
  { hintFns :: [Component]
  , hintDataTypes :: [Component]
  , hintRecordTypes :: [Component]
  , hintAxioms :: [Component]
  -- ^ Excluding those producing Level
  , hintLevel :: [Component]
  -- ^ A function
  , hintWhere :: [Component]
  -- ^ A definition in a where clause
  , hintProjections :: [Component]
  }

data Component = Component {compTerm :: Term, compType :: Type, compName :: Maybe Name}
  deriving Eq

mkComponent :: Maybe Name -> Term -> Type -> Component
mkComponent name term typ = Component { compTerm = term, compType = typ, compName = name}

mkComponentN :: Name -> Term -> Type -> Component
mkComponentN = mkComponent . Just

mkComponentQ :: QName -> Term -> Type -> Component
mkComponentQ = mkComponentN . qnameName


data SearchStepResult
  = ResultExpr Expr
  | OpenBranch SearchBranch
  | NoSolution

runBfs :: Options -> Bool -> InteractionId -> TCM [String]
runBfs options stopAfterFirst ii = withInteractionId ii $ do
  mTheFunctionQName <- fmap ipClause (lookupInteractionPoint ii) <&> \case
    clause@IPClause{} -> Just $ ipcQName clause
    IPNoClause -> Nothing
  metaId <- lookupInteractionId ii
  metaVar <- lookupLocalMeta metaId

  -- We remove the name of the function the interaction point occurs in to prevent
  -- arbitrary recursive calls
  -- hintNames1 <- filter (/= theFunctionQName) <$> getEverythingInScope metaVar
  -- records <- filterM (fmap isJust . isRecord) hintNames1
  -- recordProjs <- concat  <$> mapM getRecordFields records
  -- let hintNames = {- hintNames1 ++ -} recordProjs
  -- hints <- sortOn (arity . snd) . catMaybes <$> mapM qnameToTerm hintNames
  -- let hints' = filter (\(d,_) -> case d of Def{} -> True; _ -> False) hints

  state <- getTC
  env <- askTC
  components <- collectComponents options mTheFunctionQName metaId


  -- TODO: What if metaIds is empty? (The whole thing was solved by unification)
  metaIds <- case mvInstantiation metaVar of
    InstV inst -> do
      metaIds <- allOpenMetas (instBody inst)
      mlog $ "Instantiation already present at top-level: " ++  prettyShow (instBody inst) ++ " remaining metas: " ++ prettyShow metaIds ++ " all occurring metas: " ++ prettyShow (allMetas (:[]) (instBody inst))
      return metaIds
    Open -> do
      mlog $ "No insantiation present at top-level."
      return [metaId]
    _ -> __IMPOSSIBLE__

  -- Check if there are any meta variables to be solved
  case metaIds of
    -- No variables to solve, return the instantiation given
    [] -> (:[]) <$> (showTCM =<< fromMaybe __IMPOSSIBLE__ <$> getMetaInstantiation metaId)
    _ -> do
      startGoals <- mapM mkGoal metaIds
      let startBranch = SearchBranch
            { sbTCState = state
            , sbGoals = startGoals
            , sbCost = 0
            , sbComponentsUsed = Map.empty
            }

      let searchOptions = SearchOptions
            { searchComponents = components
            , searchHintMode = optHintMode options
            , searchTimeout = optTimeout options
            , searchTopMeta = metaId
            , searchTopEnv = env
            , searchCosts = defaultCosts
            }
      flip runReaderT searchOptions $ do
        mlog $ "Components: " ++ prettyShow components
        -- mlog =<< ("startBranch: " ++) <$> prettyBranch startBranch
        timeout <- secondsToNominalDiffTime . (/1000) . fromIntegral <$> asks searchTimeout
        mlog' $ "Timeout: " ++ show timeout
        startTime <- liftIO $ getCurrentTime
        let go n allBranches = case Q.minView allBranches of
              Nothing -> return ([], n)
              Just (branch, branches) -> do
                time <- liftIO $ getCurrentTime

                if diffUTCTime time startTime < timeout
                then do
                  (branches', sols) <- partitionStepResult branches <$> bfsRefine branch
                  -- mlog $ replicate 30 '#' ++ show n ++ replicate 30 '#'
                  -- mapM_ (mlog <=< showTCM) sols
                  -- mlog =<< (unlines <$> mapM prettyBranch (Q.toList branches'))
                  -- mlog (replicate 61 '#')
                  if stopAfterFirst
                  then case sols of [] -> go (n+1) branches'; _ -> return (sols, n)
                  else mapFst (sols ++) <$> go (n+1) branches'
                else do
                  mlog' $ "Time limit reached."
                  return ([], n)
        (sols, nrSteps) <- go 0 $ Q.singleton startBranch
        solStrs <- mapM showTCM sols
        mlog' $ "Final solution (after " ++ show nrSteps ++ " steps)\n: " ++ unlines solStrs
        return solStrs
  where
    partitionStepResult :: MinQueue SearchBranch -> [SearchStepResult] -> (MinQueue SearchBranch, [Expr])
    partitionStepResult brs [] = (brs,[])
    partitionStepResult brs (x:xs) = case x of
      NoSolution -> rest
      OpenBranch br -> (Q.insert br brs', exps)
      ResultExpr exp -> (brs', exp:exps)
      where rest@(brs',exps) = partitionStepResult brs xs

getLetVars :: MonadTCM tcm => tcm [Component]
getLetVars = asksTC envLetBindings >>= mapM bindingToComp . Map.toAscList
  where
    bindingToComp :: MonadTCM tcm => (Name, Open (Term, Dom Type)) -> tcm Component
    bindingToComp (name, is) = do
      (term, typ) <- getOpen is
      return $ mkComponentN name term (unDom typ)


collectComponents :: (MonadTCM tcm, ReadTCState tcm, HasConstInfo tcm, MonadFresh NameId tcm, MonadInteractionPoints tcm, MonadStConcreteNames tcm, PureTCM tcm)
  => Options -> Maybe QName -> MetaId -> tcm Components
collectComponents opts mDefName metaId = do
  let components = Components
        { hintFns = []
        , hintDataTypes = []
        , hintRecordTypes = []
        , hintProjections = []
        , hintAxioms = []
        , hintLevel = []
        , hintWhere = []
        }
  metaVar <- lookupLocalMeta metaId
  hintNames <- getEverythingInScope metaVar
  components' <- foldM go components hintNames
  return Components
    { hintFns = doSort $ hintFns components'
    , hintDataTypes = doSort $ hintDataTypes components'
    , hintRecordTypes = doSort $ hintRecordTypes components'
    , hintProjections = doSort $ hintProjections components'
    , hintAxioms = doSort $ hintAxioms components'
    , hintLevel = doSort $ hintLevel components'
    , hintWhere = doSort $ hintWhere components'
    }
  where
    hintMode = optHintMode opts
    explicitHints = optExplicitHints opts
    -- Sort by the arity of the type
    doSort = sortOn (arity . compType)

    isNotMutual qname f = case mDefName of
      Nothing -> True
      Just defName -> defName /= qname && fmap ((defName `elem`)) (funMutual f) /= Just True

    go comps qname = do
      info <- getConstInfo qname
      typ <- typeOfConst qname
      case theDef info of
        Axiom{} | isToLevel typ -> return comps{hintLevel = mkComponentQ qname (Def qname []) typ : hintLevel comps}
                | otherwise -> return comps{hintAxioms = mkComponentQ qname (Def qname []) typ : hintAxioms comps}
        -- TODO: Check if we want to use these
        DataOrRecSig{} -> return comps
        GeneralizableVar -> do
          mlog $ "Collect: GeneralizeableVar " ++ prettyShow (theDef info)
          return comps
        AbstractDefn{} -> do
          mlog $ "Collect: AbstractDefn " ++ prettyShow (theDef info)
          return comps
        -- If the function is in the same mutual block, do not include it.
        f@Function{}
          | isToLevel typ && isNotMutual qname f
            -> return comps{hintLevel = mkComponentQ qname (Def qname []) typ : hintLevel comps}
          | isNotMutual qname f && (hintMode /= NoHints || qname `elem` explicitHints) -- TODO: Check if local to module or not
            -> return comps{hintFns = mkComponentQ qname (Def qname []) typ : hintFns comps}
          | otherwise -> return comps
        Datatype{} -> return comps{hintDataTypes = mkComponentQ qname (Def qname []) typ : hintDataTypes comps}
        Record{} -> do
          -- TODO: remove dependency on qnameToTerm
          projections <- catMaybes <$> (mapM qnameToComp =<< getRecordFields qname)
          return comps{ hintRecordTypes = mkComponentQ qname (Def qname []) typ : hintRecordTypes comps
                      , hintProjections = projections ++ hintProjections comps}
        -- We look up constructors when we need them
        Constructor{} -> return comps
        -- TODO: special treatment for primitives?
        Primitive{} | isToLevel typ -> return comps{hintLevel = mkComponentQ qname (Def qname []) typ : hintLevel comps}
                    | otherwise -> return comps{hintFns = mkComponentQ qname (Def qname []) typ : hintFns comps}
        PrimitiveSort{} -> do
          mlog $ "Collect: Primitive " ++ prettyShow (theDef info)
          return comps

    -- NOTE: We do not reduce the type before checking, so some user definitions
    -- will not be included here.
    isToLevel :: Type -> Bool
    isToLevel typ = case unEl typ of
      Pi _ abs -> isToLevel (unAbs abs)
      Def qname _ -> prettyShow qname == builtinLevelName
      _ -> False

builtinLevelName :: String
builtinLevelName = "Agda.Primitive.Level"

bfsRefine :: SearchBranch -> SM [SearchStepResult]
bfsRefine branch = withBranchState branch $ do
  (goal, branch') <- nextBranchMeta' branch
  withBranchAndGoal branch' goal $ do
    goalType <- reduce =<< getMetaTypeInContext (goalMeta goal)
    -- Lambda-abstract as far as possible
    bfsLambdaAbstract goal goalType branch' >>= \case
      -- Abstracted with absurd pattern: solution found.
      Left expr -> return [ResultExpr expr]
      -- Normal abstraction
      Right (goal', goalType', branch'') ->
        withBranchAndGoal branch'' goal' $ do
          -- We reduce the meta type to WHNF(?) immediately to avoid refining it
          -- multiple times later (required e.g. to check if it is a Pi type)
          results1 <- bfsLocals goal' goalType' branch''
          results2 <- bfsDataRecord goal' goalType' branch''
          results3 <- bfsLet goal' goalType' branch''
          results4 <- bfsFnProjs goal' goalType' branch''
          return (results1 ++ results2 ++ results3 ++ results4)

bfsFnProjs :: Goal -> Type -> SearchBranch -> SM [SearchStepResult]
bfsFnProjs goal goalType branch = withBranchAndGoal branch goal $ do
  fns <- asks (hintFns . searchComponents)
  newBranches <- catMaybes <$> mapM (bfsTryRefineAddMetas costFn goal goalType branch) fns
  mapM checkSolved newBranches

bfsLet :: Goal -> Type -> SearchBranch -> SM [SearchStepResult]
bfsLet goal goalType branch = withBranchAndGoal branch goal $ do
  (goal', letVars) <- getLetVarsCached
  newBranches <- catMaybes <$> mapM (bfsTryRefineAddMetas costLet goal' goalType branch) letVars
  mapM checkSolved newBranches
  where getLetVarsCached =
          -- Does the goal already have computed let bindings?
          case goalLetVars goal of
            -- Yes. Use them.
            Just letVars -> return (goal, letVars)
            -- No. Find them.
            Nothing -> do
              letVars <- getLetVars
              return (goal {goalLetVars=Just letVars}, letVars)


-- | Returns @Right@ for normal lambda abstraction and @Left@ for absurd lambda.
bfsLambdaAbstract :: Goal -> Type -> SearchBranch -> SM (Either Expr (Goal, Type, SearchBranch))
bfsLambdaAbstract goal goalType branch =
  case unEl goalType of
    Pi dom abs -> do
     e <- isEmptyType (unDom dom); mlog $ "isEmptyType " ++ prettyShow (unDom dom) ++ " = " ++ show e
     isEmptyType (unDom dom) >>= \case -- TODO: Is this the correct way of checking if absurd lambda is applicable?
      True -> do
        let argInf = defaultArgInfo{argInfoOrigin = Inserted} -- domInfo dom
            term = Lam argInf absurdBody
        mlog $ show argInf
        newMetaIds <- assignMeta (goalMeta goal) term goalType
        unless (null newMetaIds) (__IMPOSSIBLE__)
        -- TODO: Represent absurd lambda as a Term instead of Expr.
        -- Left . fromMaybe __IMPOSSIBLE__ <$> getMetaInstantiation (goalMeta metaId)
        return $ Left $ AbsurdLam exprNoRange NotHidden
      False -> do
        let bindName = absName abs
        newName <- freshName_ bindName
        (metaId', bodyType, metaTerm, env) <- lambdaAddContext newName bindName dom $ do
          goalType' <- getMetaTypeInContext (goalMeta goal)
          bodyType <- reduce =<< piApplyM goalType' (Var 0 []) -- TODO: Good place to reduce?
          (metaId', metaTerm) <- newValueMeta DontRunMetaOccursCheck CmpLeq bodyType
          mlog $ "Created meta " ++ prettyShow metaId' ++ " in bfsLambdaAbstract"
          env <- askTC

          ctx <- getContextTelescope
          mlog $ prettyShow ctx
          return (metaId', bodyType, metaTerm, env)

        let argInf = domInfo dom -- TODO: is this the correct arg info?
            newAbs = Abs{absName = bindName, unAbs = metaTerm } --MetaV metaId' [] }
            -- look at mkLam
            term = Lam argInf newAbs

        newMetaIds <- assignMeta (goalMeta goal) term goalType

        withEnv env $ do
          branch' <- updateBranch newMetaIds branch
          goal' <- mkGoal metaId'
          bfsLambdaAbstract goal' bodyType branch'
    _ -> do
      branch' <- updateBranch [] branch
      return $ Right (goal, goalType, branch')

-- | NOTE: the MetaId should already be removed from the SearchBranch when this function is called
bfsLocals :: Goal -> Type -> SearchBranch -> SM [SearchStepResult]
bfsLocals goal goalType branch = withBranchAndGoal branch goal $ do
  metaVar <- lookupLocalMeta (goalMeta goal)
  localVars <- getLocalVars
  -- TODO: Explain permute
  let localVars' = localVars -- permute (takeP (length localVars) $ mvPermutation metaVar) localVars
  newBranches <- catMaybes <$> mapM (bfsTryRefineAddMetas costLocal goal goalType branch) localVars'
  mapM checkSolved newBranches

-- TODO: Factor out `checkSolved`
bfsDataRecord :: Goal -> Type -> SearchBranch -> SM [SearchStepResult]
bfsDataRecord goal goalType branch = withBranchAndGoal branch goal $ do
  -- TODO: There is a `isRecord` function, which performs a similar case
  -- analysis as here, but it does not work for data types.
  case unEl goalType of
    Def qname elims -> theDef <$> getConstInfo qname >>= \case
      recordDefn@Record{} -> do
        -- mlog $ "Found a Record: " ++ prettyShow recordDefn
        bfsRecord recordDefn
      dataDefn@Datatype{} -> do
        -- mlog $ "Found a Datatype: " ++ prettyShow dataDefn
        bfsData dataDefn
      primitive@Primitive{} -> do
        mlog $ "Found a Primitive: " ++ prettyShow primitive
        return []
      -- TODO: Better way of checking that type is Level
      d@Axiom{}
        | prettyShow qname == "Agda.Primitive.Level" -> do
            bfsLevel
        | otherwise -> do
        mlog $ "Found an Axiom: " ++ prettyShow d ++ " qname=" ++ prettyShow qname
        return []
      d@DataOrRecSig{} -> do
        mlog $ "Found a DataOrRecSig: " ++ prettyShow d
        return []
      d@GeneralizableVar -> do
        mlog $ "Found a GeneralizableVar: " ++ prettyShow d
        return []
      d@AbstractDefn{} -> do
        mlog $ "Found an AbstractDefn: " ++ prettyShow d
        return []
      d@Function{} -> do
        mlog $ "Found a Function: " ++ prettyShow d
        return []
      d@Constructor{} -> do
        mlog $ "Found a Constructor: " ++ prettyShow d
        return []
      d@PrimitiveSort{} -> do
        mlog $ "Found a PrimitiveSort: " ++ prettyShow d
        return []
    sort@(Sort (Type level)) -> do
      mlog $ "Found a Type: " ++ prettyShow sort
      bfsSet level
    Sort sort -> do
      mlog $ "Found an sort that is not yet handled: " ++ prettyShow sort
      return []
    _ -> return []
  where
      -- TODO: Alternatively, the constructor can be accessed via `getRecordConstructor`
      -- TODO: There might be a neater way of applying the constructor to new metas
    bfsRecord :: Defn -> SM [SearchStepResult]
    bfsRecord recordDefn = do
      let cHead = recConHead recordDefn
          cName = conName cHead
          cTerm = Con cHead ConOSystem []
      cType <- typeOfConst cName
      let comp = mkComponentQ (conName cHead) cTerm cType
      -- -- NOTE: at most 1
      newBranches <- maybeToList <$> bfsTryRefineAddMetasSkip costRecordCon (recPars recordDefn) goal goalType branch comp
      mapM checkSolved newBranches

    bfsData :: Defn -> SM [SearchStepResult]
    bfsData dataDefn = do
      -- Get the constructors as [(Term, Type)]
      -- TODO: prioritize constructors with few arguments. E.g. @sortOn (artity . snd)@
      comps <- mapM (fmap (fromMaybe __IMPOSSIBLE__) . qnameToComp) (dataCons dataDefn)
      newBranches <- mapM (bfsTryRefineAddMetas costDataCon goal goalType branch) comps
      -- TODO: Reduce overlap between e.g. bfsLocals, this and bfsRecord
      mapM checkSolved (catMaybes newBranches)

    bfsLevel :: SM [SearchStepResult]
    bfsLevel = do
      levelHints <- asks (hintLevel . searchComponents)
      newBranches <- catMaybes <$> mapM (bfsTryRefineAddMetas costLevel goal goalType branch) levelHints
      mapM checkSolved newBranches

    -- TODO: Add an extra filtering on the sort
    bfsSet :: Level -> SM [SearchStepResult]
    bfsSet level = do
      setTerm <- reduce level >>= \case
        reducedLevel@(Max i [])
          | i > 0 -> return [mkComponent Nothing (Sort $ Type $ Max (i-1) []) goalType]
          | otherwise -> do
              mlog $ "bfsSet: don't know what to do with level " ++ prettyShow reducedLevel
              return []
        reducedLevel -> do
          mlog $ "bfsSet: don't know what to do with " ++ prettyShow reducedLevel
          return []
      components <- asks searchComponents
      newBranches <- catMaybes <$> mapM (bfsTryRefineAddMetas costSet goal goalType branch)
                      (setTerm ++ concatMap ($ components)
                       [ hintDataTypes
                       , hintRecordTypes
                       , hintAxioms])
      mapM checkSolved newBranches

checkSolved :: SearchBranch -> SM SearchStepResult
checkSolved branch = {-# SCC "custom-checkSolved" #-} do
  env <- asks searchTopEnv
  withBranchState branch $ withEnv env $ do
    openMetas <- getOpenMetas
    case filter ((`elem` openMetas) . goalMeta) (sbGoals branch) of
      [] -> do
        metaId <- asks searchTopMeta
        mlog =<< ("checkSolved: context=" ++) . prettyShow <$> getContext
        -- r <- maybe NoSolution ResultExpr <$> (getMetaInstantiation metaId)
        getMetaInstantiation metaId >>= \case
          Nothing -> return NoSolution
          Just e -> do
            mlog =<< ("checkSolved: result=" ++) <$> showTCM e
            return (ResultExpr e)
      remainingGoals -> return $ OpenBranch branch{sbGoals = remainingGoals}

-- | Type should already be reduced here
-- NOTE: Does not reset the state!
-- TODO: Make sure the type is always reduced
bfsTryRefineWith :: (Costs -> Int) -> Goal -> Type -> SearchBranch -> Component -> SM (Maybe SearchBranch)
bfsTryRefineWith costFn goal goalType branch comp = withBranchAndGoal branch goal $ do
  mlog $ "Trying refine: " ++ prettyShow comp ++ " for " ++ prettyShow (goalMeta goal) ++ ":" ++ prettyShow goalType ++ ".."
  metasCreatedBy (dumbUnifier (compType comp) goalType) >>= \case
    (True, newMetaStore) -> do
      mlog $ "   ..succeeded."
      newMetaIds <- assignMeta (goalMeta goal) (compTerm comp) goalType
      -- TODO: check if everything is solved?
      let newMetaIds' = Map.keys (openMetas newMetaStore)
      mlog $ "  New metas (bfsTryRefineWith): " ++ prettyShow newMetaIds'
      Just <$> updateBranchCost costFn comp newMetaIds' branch
    (False, _) -> do
      mlog $ "   ..failed."
      return Nothing


-- TODO: Make policy for when state should be put
bfsTryRefineAddMetasSkip :: (Costs -> Int) -> Nat -> Goal -> Type -> SearchBranch -> Component -> SM (Maybe SearchBranch)
bfsTryRefineAddMetasSkip costFn skip goal goalType branch comp = withBranchAndGoal branch goal $ do
  -- Apply the hint to new metas (generating @c@, @c ?@, @c ? ?@, etc.)
  -- TODO: Where is the best pace to reduce the hint type?
  (hintTerm', hintType', newMetas) <- applyToMetas skip (compTerm comp) =<< reduce (compType comp)
  let comp' = mkComponent (compName comp) hintTerm' hintType'
  branch' <- updateBranch [] branch
  fmap (addBranchGoals $ map (mkGoalPreserveLocalsAndEnv goal) $ reverse newMetas) <$> bfsTryRefineWith costFn goal goalType branch' comp'

bfsTryRefineAddMetas :: (Costs -> Int) -> Goal -> Type -> SearchBranch -> Component -> SM (Maybe SearchBranch)
bfsTryRefineAddMetas costFn = bfsTryRefineAddMetasSkip costFn 0

-- TODO: Make sure the type is reduced the first time this is called
-- TODO: Rewrite with Component?
-- NOTE: The new metas are in left-to-right order -- the opposite of the
-- order they should be solved in.
applyToMetas :: Nat -> Term -> Type -> SM (Term, Type, [MetaId])
applyToMetas skip term typ = do
  ctx <- getContextTelescope
  mlog $ prettyShow ctx
  case unEl typ of
    Pi dom abs -> do
      let domainType = unDom dom
      -- TODO: What exactly does the occur check do?
      (metaId', metaTerm) <- newValueMeta DontRunMetaOccursCheck CmpLeq domainType
      mlog $ "Created meta " ++ prettyShow metaId' ++ " in applyToMetas"
      let arg = setOrigin Inserted $ metaTerm <$ argFromDom dom
      newType <- reduce =<< piApplyM typ metaTerm -- TODO: Is this the best place to reduce?
      -- For records, the parameters are not included in the term
      let newTerm = if skip > 0 then term else apply term [arg]
      (term', typ', metas) <- applyToMetas (predNat skip) newTerm newType
      return (term', typ', metaId' : metas)
    _ -> return (term, typ, [])


updateBranch' :: Maybe (Costs -> Int, Component) -> [MetaId] -> SearchBranch -> SM SearchBranch
updateBranch' costs newMetaIds branch = do
  state <- getTC
  env <- askTC
  let compsUsed = sbComponentsUsed branch
  (deltaCost, compsUsed') <- case costs of
        Nothing -> return (0, compsUsed)
        Just (costFn, comp) -> do
          cost1 <- asks (costFn . searchCosts)
          let p = cost1 :: Int
          case compName comp of
            Nothing -> return (cost1, compsUsed)
            Just name -> case compsUsed Map.!? name of
              Nothing -> return (cost1, Map.insert name 1 compsUsed)
              -- TODO: Currently using: uses^2+1 as cost. Make a parameter?
              Just uses -> return (cost1 + uses * uses + 2, Map.adjust succ name compsUsed)
  newGoals <- mapM mkGoal newMetaIds
  return branch{ sbTCState = state
               , sbGoals = newGoals ++ sbGoals branch
               , sbCost = sbCost branch + deltaCost
               , sbComponentsUsed = compsUsed'
               }

updateBranch :: [MetaId] -> SearchBranch -> SM SearchBranch
updateBranch = updateBranch' Nothing

updateBranchCost :: (Costs -> Int) -> Component -> [MetaId] -> SearchBranch -> SM SearchBranch
updateBranchCost costFn comp = updateBranch' $ Just (costFn, comp)

assignMeta :: MetaId -> Term -> Type -> SM [MetaId]
assignMeta metaId term metaType = {-# SCC "custom-assignMeta" #-}
  metasCreatedBy (do
    metaVar <- lookupLocalMeta metaId
    metaArgs <- getMetaContextArgs metaVar
    mlog $ "assignMeta: assigning " ++ prettyShow term ++ " to " ++ prettyShow metaId
    assignV DirLeq metaId metaArgs term (AsTermsOf metaType))
    >>= \case
    ((), newMetaStore) -> do
      let newMetaIds = Map.keys (openMetas newMetaStore)
      mlog $ "New metas created in assignMeta: " ++ prettyShow newMetaIds
      return newMetaIds

addBranchGoals :: [Goal] -> SearchBranch -> SearchBranch
addBranchGoals goals branch = branch {sbGoals = goals ++ sbGoals branch}

withBranchState :: SearchBranch -> SM a -> SM a
withBranchState br ma = {- withEnv (sbTCEnv br) $ -} do
  putTC (sbTCState br)
  ma

withBranchAndGoal :: SearchBranch -> Goal -> SM a -> SM a
withBranchAndGoal br goal ma = withEnv (goalEnv goal) $ withMetaId (goalMeta goal) $ withBranchState br ma

nextBranchMeta' :: SearchBranch -> SM (Goal, SearchBranch)
nextBranchMeta' = fmap (fromMaybe __IMPOSSIBLE__) . nextBranchMeta

nextBranchMeta :: SearchBranch -> SM (Maybe (Goal, SearchBranch))
nextBranchMeta branch = case sbGoals branch of
  [] -> return Nothing
  (goal : goals) ->
    return $ Just (goal, branch{sbGoals=goals})


-- TODO: documentation for invariants
checkBranchInvariants :: SearchBranch -> SM ()
checkBranchInvariants branch = withLocalTCState (sbTCState branch) $
  case sbGoals branch of
    [] -> error "checkBranchInvariants: no metas in list"
    (goal:_) -> unlessM (isMetaOpen $ goalMeta goal)
      (error "checkBranchInvariants: the head meta is not open")

isMetaOpen :: MetaId -> SM Bool
isMetaOpen metaId = (metaId `elem`) <$> getOpenMetas

getMetaInstantiation :: (MonadTCM tcm, PureTCM tcm, MonadDebug tcm, MonadInteractionPoints tcm, MonadFresh NameId tcm)
  => MetaId -> tcm (Maybe Expr)
getMetaInstantiation metaId = do
  metaVar <- lookupLocalMeta metaId
  case mvInstantiation metaVar of
    -- TODO: Change ReduceAndEtaContract class to avoid lift?
    InstV inst -> do
      mlog $ "Meta instantiation (non-contracted): " ++ prettyShow (instBody inst)
      -- NOTE: instantiateFull also does eta reduction
      res <- Just <$> (reify =<< {- etaContract' =<< -} instantiateFull (instBody inst))
      return res
    _ -> return Nothing


getEverythingInScope :: MonadTCM tcm => MetaVariable -> tcm [QName]
getEverythingInScope metaVar = do
  let scope = clScope $ getMetaInfo metaVar
  let nameSpace = Scope.everythingInScope scope
      names = Scope.nsNames nameSpace
      qnames = map (Scope.anameName . head) $ Map.elems names
  mlog $ "getEverythingInScope, scope = " ++ prettyShow scope
  return qnames

  -- TODO: Look at getContextVars, locallyTC, getMetaScope

dumbUnifier :: (MonadTCM tcm, PureTCM tcm, MonadWarning tcm, MonadStatistics tcm, MonadMetaSolver tcm, MonadFresh Int tcm, MonadFresh ProblemId tcm)
  => Type -> Type -> tcm Bool
dumbUnifier t1 t2 = {-# SCC "custom-dumbUnifier" #-}
  (noConstraints $ equalType t2 t1 >> return True) `catchError` \err -> do
--     str <- showTCM err
--     mlog $ "dumbUnifier error: " ++ str
    return False

getDomainType :: Type -> Type
getDomainType typ = case unEl typ of
  Pi dom _ -> unDom dom
  _ -> __IMPOSSIBLE__

-- Duplicate of a local definition in Agda.Interaction.BasicOps
showTCM :: (MonadPretty tcm, PrettyTCM a) => a -> tcm String
showTCM v = render <$> prettyTCM v


concatUnzip :: [([a], [b])] -> ([a], [b])
concatUnzip xs = let (as, bs) = unzip xs in (concat as, concat bs)

-- partitionEithers :: [Either a b] -> ([a], [b])
-- partitionEithers [] = ([], [])
-- partitionEithers (e : es) = let (as, bs) = partitionEithers es in
--   case e of
--     Left a -> (a : as, bs)
--     Right b -> (as, b : bs)


mlog :: Monad m => String -> m ()
mlog str = {- doLog str $ -} return ()

mlog' :: Monad m => String -> m ()
mlog' str = doLog str $ return ()

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
getLocalVars :: MonadTCM tcm => tcm [Component]
getLocalVars = do
  contextTerms <- getContextTerms
  contextTypes <- map unDom . flattenTel <$> getContextTelescope
  unless (length contextTerms == length contextTypes)
         (mlog $ "WARNING: length mismatch in getLocalVars: " ++ prettyShow contextTerms ++ "; " ++ prettyShow contextTypes)
  return $ zipWith (mkComponent Nothing) contextTerms contextTypes

prettyBranch :: SearchBranch -> SM String
prettyBranch branch = withBranchState branch $ do
    metas <- prettyTCM (map goalMeta $ sbGoals branch)
    metaId <- asks searchTopMeta
    inst <- getMetaInstantiation metaId
    instStr <- prettyTCM inst
    let compUses = pretty $ Map.toList $ sbComponentsUsed branch
    return $ render $ text "Branch{cost: " <> text (show $ sbCost branch) <> ", metas: " <> metas <> text " , instantiation: " <> pretty metaId <> text " = " <> instStr <> text ", used components: " <> compUses <> text "}"

prettySearchStepResult :: SearchStepResult -> SM String
prettySearchStepResult = \case
  NoSolution -> return "No solution"
  OpenBranch branch -> ("Open branch: " ++) <$> prettyBranch branch
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

instance Pretty Components where
  pretty comps =
    text "Components" <> braces (prettyList_
      [ text "hintFns=" <> pretty (hintFns comps)
      , text "hintDataTypes=" <> pretty (hintDataTypes comps)
      , text "hintRecordTypes=" <> pretty (hintRecordTypes comps)
      , text "hintAxioms=" <> pretty (hintAxioms comps)
      , text "hintLevel=" <> pretty (hintLevel comps)
      , text "hintWhere=" <> pretty (hintWhere comps)
      , text "hintProjections=" <> pretty (hintProjections comps)])

-- instance Pretty Goal where
--   pretty goal =
--     text "Goal" <> braces (prettyList_
--       [ text "goalMeta=" <> pretty (goalMeta goal)
--       , text "goalLocalVars=" <> pretty (goalLocalVars goal)
--       , text "goalLetVars=" <> pretty (goalLetVars goal)
--       ])

data SearchOptions = SearchOptions
  { searchComponents :: Components
  , searchHintMode :: HintMode
  , searchTimeout :: MilliSeconds
  , searchTopMeta :: MetaId
  , searchTopEnv :: TCEnv
  , searchCosts :: Costs
  }


data Costs = Costs
  { costLocal :: Int
  , costFn :: Int
  , costDataCon :: Int
  , costRecordCon :: Int
  , costSpeculateProj :: Int
  , costProj :: Int
  , costLet :: Int
  , costLevel :: Int
  , costSet :: Int -- Should probably be replaced with multiple different costs
  }

noCost :: Int
noCost = 0

defaultCosts :: Costs
defaultCosts = Costs
  { costLocal = 1
  , costFn = 3
  , costDataCon = 1
  , costRecordCon = 2
  , costSpeculateProj = 2
  , costProj = 2
  , costLet = 1
  , costLevel = 2
  , costSet = 2
  }



type SM a = ReaderT SearchOptions TCM a


-- TODO: Maybe there should be an instance @MonadTCM m => MonadMetaSolver m@?
instance MonadMetaSolver (ReaderT r TCM) where
  newMeta' a b c d e f = liftTCM $ newMeta' a b c d e f -- :: MetaInstantiation -> Frozen -> MetaInfo -> MetaPriority -> Permutation -> Judgement a -> m MetaId
  assignV a b c d e = liftTCM $ assignV a b c d e -- :: CompareDirection -> MetaId -> Args -> Term -> CompareAs -> m ()
  assignTerm' a b c = liftTCM $ assignTerm' a b c -- :: MonadMetaSolver m => MetaId -> [Arg ArgName] -> Term -> m ()
  etaExpandMeta a b = liftTCM $ etaExpandMeta a b -- :: [MetaKind] -> MetaId -> m ()
  updateMetaVar a b = liftTCM $ updateMetaVar a b -- :: MetaId -> (MetaVariable -> MetaVariable) -> m ()
  speculateMetas m1 m2 = ReaderT $ \r ->
    let tcm1 = runReaderT m1 r
        tcm2 = runReaderT m2 r
    in speculateMetas tcm1 tcm2 -- :: m () -> m KeepMetas -> m ()

-- TODO: Change the signature in original module instead.
isEmptyType :: Type -> SM Bool
isEmptyType = liftTCM . Empty.isEmptyType

predNat :: Nat -> Nat
predNat n | n > 0 = n - 1
          | n == 0 = 0
          | otherwise = error "predNat of negative value"

allOpenMetas :: (AllMetas t, ReadTCState tcm) => t -> tcm [MetaId]
allOpenMetas t = do
  openMetas <- getOpenMetas
  return $ allMetas (:[]) t `intersect` openMetas


instance Pretty Component where
  pretty comp =
    let name = case compName comp of Nothing -> text "NoName"; Just n -> pretty n
    in text "Component{compName=" <> name <> ", compTerm=" <> pretty (compTerm comp) <> ", compType=" <> pretty (compType comp)

