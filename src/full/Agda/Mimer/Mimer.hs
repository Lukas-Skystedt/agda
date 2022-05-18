module Agda.Mimer.Mimer
  ( MimerResult(..)
  , mimer
  )
  where

import Control.DeepSeq (force, NFData(..))
import Control.Monad ((>=>), (=<<), unless, foldM, when, zipWithM)
import Control.Monad.Except (catchError)
import Control.Monad.Error.Class (MonadError)
import Control.Monad.IO.Class (liftIO)
import Control.Monad.Reader (ReaderT(..), runReaderT, asks)
import Data.Function (on)
import Data.Functor ((<&>))
import Data.List (sortOn, intersect, transpose, (\\))
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Maybe (maybeToList, fromMaybe, maybe, isNothing)
import Data.PQueue.Min (MinQueue)
import qualified Data.PQueue.Min as Q
import Data.Time.Clock (diffUTCTime, getCurrentTime, secondsToNominalDiffTime)
import GHC.Generics (Generic)
import qualified Text.PrettyPrint.Boxes as Box


import qualified Agda.Benchmarking as Bench
import Agda.Syntax.Abstract (Expr(AbsurdLam))
import Agda.Syntax.Abstract.Name (QName(..), Name(..))
import Agda.Syntax.Common (InteractionId, MetaId(..), ArgInfo(..), defaultArgInfo, Origin(..), ConOrigin(..), Hiding(..), setOrigin, NameId, Nat, namedThing, Arg(..), setHiding, getHiding)
import Agda.Syntax.Info (exprNoRange)
import Agda.Syntax.Internal -- (Type, Type''(..), Term(..), Dom'(..), Abs(..), arity , ConHead(..), Sort'(..), Level, argFromDom, Level'(..), absurdBody, Dom, namedClausePats, Pattern'(..), dbPatVarIndex)
import Agda.Syntax.Internal.MetaVars (AllMetas(..))
import Agda.Syntax.Position (Range)
import qualified Agda.Syntax.Scope.Base as Scope
import Agda.Syntax.Translation.InternalToAbstract (reify)
import Agda.TypeChecking.Constraints (noConstraints)
import Agda.TypeChecking.Conversion (equalType)
import qualified Agda.TypeChecking.Empty as Empty -- (isEmptyType)
import Agda.TypeChecking.Free (flexRigOccurrenceIn)
import Agda.TypeChecking.MetaVars (newValueMeta)
import Agda.TypeChecking.Monad -- (MonadTCM, lookupInteractionId, getConstInfo, liftTCM, clScope, getMetaInfo, lookupMeta, MetaVariable(..), metaType, typeOfConst, getMetaType, MetaInfo(..), getMetaTypeInContext)
import Agda.TypeChecking.Pretty (MonadPretty, prettyTCM, PrettyTCM(..))
import Agda.TypeChecking.Records (isRecord)
import Agda.TypeChecking.Reduce (reduce, instantiateFull)
import Agda.TypeChecking.Rules.Term  (lambdaAddContext)
import Agda.TypeChecking.Substitute.Class (apply)
import Agda.TypeChecking.Telescope (piApplyM, flattenTel, teleArgs)
import Agda.Utils.Benchmark (billTo)
import Agda.Utils.Impossible (__IMPOSSIBLE__)
import Agda.Utils.Maybe (catMaybes)
-- import Agda.Utils.Permutation (idP, permute, takeP)
import Agda.Utils.Pretty (Pretty, Doc, prettyShow, prettyList, render, pretty, braces, prettyList_, text, (<+>), nest, lbrace, rbrace, comma, ($$), vcat, ($+$), align, cat, parens)
import Agda.Utils.Time (getCPUTime)
import Agda.Utils.Tuple (mapFst, mapSnd)

import Agda.Mimer.Options

import System.IO.Unsafe (unsafePerformIO)
import Data.IORef (IORef, writeIORef, readIORef, newIORef, modifyIORef')
import Agda.Mimer.Debug

newtype MimerResult = MimerResult String

mimer :: MonadTCM tcm
  => InteractionId
  -> Range
  -> String
  -> tcm MimerResult
mimer ii range argStr = liftTCM $ do
    reportDoc "mimer.top" 10 ("Running Mimer on interaction point" <+> pretty ii <+> "with argument string" <+> text (show argStr))
    verb <- hasVerbosity "mimer.all" 10
    liftIO $ writeIORef shouldLog verb
    mlog' $ "Mimer running verbose: " ++ show verb

    start <- liftIO $ getCPUTime
    mlog' $ "Start time: " ++ prettyShow start

    opts <- parseOptions ii range argStr
    reportS "mimer.top" 15 ("Mimer options: " ++ show opts)


    oldState <- getTC
    sols <- runSearch opts True ii
    putTC oldState

    s <- case sols of
          [] -> do
            reportSLn "mimer.top" 10 "No solution found"
            return "?"
          (sol:_) -> do
            reportSLn "mimer.top" 10 ("Solution: " ++ sol)
            return sol

    putTC oldState

    stop <- liftIO $ getCPUTime
    reportDoc "mimer.top" 10 ("Total elapsed time:" <+> pretty (stop - start))
    return $ MimerResult $ s


-- Order to try things in:
-- 1. Local variables (including let-bound)
-- 2. Data constructors
-- 3. Where clauses
-- 4. Lambda abstract
-- Other: Equality, empty type, record projections
-- - If we only use constructors if the target type is a data type, we might
--   generate η-reducible expressions, e.g. λ xs → _∷_ 0 xs


------------------------------------------------------------------------------
-- * Data types
------------------------------------------------------------------------------

type SM a = ReaderT SearchOptions TCM a

data SearchBranch = SearchBranch
  { sbTCState :: TCState
  , sbGoals :: [Goal]
  , sbCost :: Int
  , sbCache :: Map Telescope ComponentCache
  , sbComponentsUsed :: Map Name Int -- ^ Number of times each component has been used
  }
  deriving (Generic)
instance NFData SearchBranch

-- | NOTE: Equality is only on the fields `sbCost` and `sbGoals`
instance Eq SearchBranch where
  sb1 == sb2 = sbCost sb1 == sbCost sb2 && sbGoals sb1 == sbGoals sb2

-- TODO: Explain
instance Ord SearchBranch where
  compare = compare `on` sbCost

-- | List of names of projections used
type ComponentGen = [QName]
-- data ComponentGen = ComponentDone Component
--                   | NeedsArg Type (Term -> ComponentGen)
--   deriving (Generic)

-- instance NFData ComponentGen


-- | The @Open ()@ is for keeping track of the context in which the components are valid
type ComponentCache = (CheckpointId, Map CompId (Maybe Component, ComponentGen))

data Goal = Goal
  { goalMeta :: MetaId
  , goalEnv :: TCEnv
  }
  deriving (Generic)
instance NFData Goal

-- TODO: Is this a reasonable Eq instance?
instance Eq Goal where
  g1 == g2 = goalMeta g1 == goalMeta g2

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
  -- ^ Variables that are candidates for arguments to recursive calls
  , hintThisFn :: Maybe Component
  , hintLetVars :: [Open Component] -- ^ We *do* open these
  , hintRecVars :: Open [Term] -- ^ We *do* open these
  }
  deriving (Generic)

instance NFData Components

type CompId = Int
data Component = Component
  { compId :: CompId -- ^ Unique id for the component. Used for the cache.
  , compName :: Maybe Name -- ^ Used for keeping track of how many times a component has been used
  , compTerm :: Term
  , compType :: Type
  , compMetas :: [MetaId]
  , compCost :: Cost
  }
  deriving (Eq, Generic)

instance NFData Component

data SearchStepResult
  = ResultExpr Expr
  | OpenBranch SearchBranch
  | NoSolution
  deriving (Generic)
instance NFData SearchStepResult


-- NOTE: If you edit this, update the corr
data SearchOptions = SearchOptions
  { searchComponents :: Components
  , searchHintMode :: HintMode
  , searchTimeout :: MilliSeconds
  , searchTopMeta :: MetaId
  , searchTopEnv :: TCEnv
  , searchTopCheckpoint :: CheckpointId
  , searchCosts :: Costs
  , searchStats :: IORef MimerStats
  }

type Cost = Int
data Costs = Costs
  { costLocal :: Cost
  , costFn :: Cost
  , costDataCon :: Cost
  , costRecordCon :: Cost
  , costSpeculateProj :: Cost
  , costProj :: Cost
  , costAxiom :: Cost
  , costLet :: Cost
  , costLevel :: Cost
  , costSet :: Cost -- Should probably be replaced with multiple different costs
  , costRecCall :: Cost
  , costNewMeta :: Cost -- ^ Cost of a new meta-variable appearing in a non-implicit position
  , costNewHiddenMeta :: Cost -- ^ Cost of a new meta-variable appearing in an implicit position
  , costCompReuse :: Nat -> Cost -- ^ Cost of reusing a component @n@ times. Only counted when @n>1@.
  }

noCost :: Cost
noCost = 0

defaultCosts :: Costs
defaultCosts = Costs
  { costLocal = 10
  , costFn = 20
  , costDataCon = 10
  , costRecordCon = 10
  , costSpeculateProj = 30
  , costProj = 5
  , costAxiom = 20
  , costLet = 10
  , costLevel = 10
  , costSet = 30
  , costRecCall = 15
  , costNewMeta = 3
  , costNewHiddenMeta = 1
  , costCompReuse = \uses -> 2 * uses ^ 2
  }

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

------------------------------------------------------------------------------
-- * Helper functions
------------------------------------------------------------------------------

predNat :: Nat -> Nat
predNat n | n > 0 = n - 1
          | n == 0 = 0
          | otherwise = error "predNat of negative value"

getRecordFields :: (HasConstInfo tcm, MonadTCM tcm) => QName -> tcm [QName]
getRecordFields = fmap (map unDom . recFields . theDef) . getConstInfo


-- TODO: Change the signature in original module instead.
isEmptyType :: Type -> SM Bool
isEmptyType = liftTCM . Empty.isEmptyType

-- TODO: Currently not using this function. Is it useful anywhere?
getDomainType :: Type -> Type
getDomainType typ = case unEl typ of
  Pi dom _ -> unDom dom
  _ -> __IMPOSSIBLE__

allOpenMetas :: (AllMetas t, ReadTCState tcm) => t -> tcm [MetaId]
allOpenMetas t = do
  openMetas <- getOpenMetas
  return $ allMetas (:[]) t `intersect` openMetas

rmCache :: CompId -> ComponentCache -> ComponentCache
rmCache cId cache = mapSnd (Map.delete cId) cache

getOpenComponent :: Open Component -> SM Component
getOpenComponent openComp = do
  let comp = openThing openComp
  term <- getOpen $ compTerm <$> openComp
  typ <- getOpen $ compType <$> openComp
  when (not $ null $ compMetas comp) __IMPOSSIBLE__
  return Component
    { compId = compId comp
    , compName = compName comp
    , compTerm = term
    , compType = typ
    , compMetas = compMetas comp
    , compCost = compCost comp
    }

-- | Create a goal in the current environment
mkGoal :: MonadTCEnv m => MetaId -> m Goal
mkGoal metaId = do
  env <- askTC
  return Goal
    { goalMeta = metaId
    , goalEnv = env
    }

mkGoalPreserveEnv :: Goal -> MetaId -> Goal
mkGoalPreserveEnv goalLocalSource metaId = Goal
  { goalMeta = metaId
  , goalEnv = goalEnv goalLocalSource
  }

mkComponent :: CompId -> [MetaId] -> Cost -> Maybe Name -> Term -> Type -> Component
mkComponent cId metaIds cost mName term typ = Component
  { compId = cId, compName = mName, compTerm = term, compType = typ, compMetas = metaIds, compCost = cost }

mkComponentQ :: CompId -> Cost -> QName -> Term -> Type -> Component
mkComponentQ cId cost qname = mkComponent cId [] cost (Just $ qnameName qname)

noName :: Maybe Name
noName = Nothing

newComponent :: MonadFresh CompId m => [MetaId] -> Cost -> Maybe Name -> Term -> Type -> m Component
newComponent metaIds cost mName term typ = fresh <&> \cId -> mkComponent cId metaIds cost mName term typ

newComponentQ :: MonadFresh CompId m => [MetaId] -> Cost -> QName -> Term -> Type -> m Component
newComponentQ metaIds cost qname term typ = fresh <&> \cId -> mkComponent cId metaIds cost (Just $ qnameName qname) term typ

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

-- TODO: Rename (see metaInstantiation)
getMetaInstantiation :: (MonadTCM tcm, PureTCM tcm, MonadDebug tcm, MonadInteractionPoints tcm, MonadFresh NameId tcm)
  => MetaId -> tcm (Maybe Expr)
getMetaInstantiation = metaInstantiation >=> go
  where
    -- TODO: Cleaner way of juggling the maybes here?
    go Nothing = return Nothing
    go (Just term) = do
      mlog $ "Meta instantiation (non-contracted): " ++ prettyShow term
      expr <- instantiateFull term >>= reify
      return $ Just expr

metaInstantiation :: (MonadTCM tcm, MonadDebug tcm, ReadTCState tcm) => MetaId -> tcm (Maybe Term)
metaInstantiation metaId = lookupLocalMeta metaId <&> mvInstantiation >>= \case
  InstV inst -> return $ Just $ instBody inst
  _ -> return Nothing

------------------------------------------------------------------------------
-- * Components
------------------------------------------------------------------------------

-- ^ NOTE: Collects components from the *current* context, not the context of
-- the 'InteractionId'.
collectComponents :: ( MonadTCM tcm, ReadTCState tcm, HasConstInfo tcm, MonadFresh NameId tcm
                     , MonadInteractionPoints tcm, MonadStConcreteNames tcm, PureTCM tcm
                     , MonadError TCErr tcm, MonadFresh CompId tcm)
  => Options -> Costs -> InteractionId -> Maybe QName -> MetaId -> tcm Components
collectComponents opts costs ii mDefName metaId = do
  recVars <- collectRecVarCandidates ii
  letVars <- getLetVars (costLocal costs)
  let components = Components
        { hintFns = []
        , hintDataTypes = []
        , hintRecordTypes = []
        , hintProjections = []
        , hintAxioms = []
        , hintLevel = []
        , hintWhere = []
        , hintThisFn = Nothing
        , hintRecVars = recVars
        , hintLetVars = letVars
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
    , hintThisFn = hintThisFn components'
    , hintRecVars = recVars
    , hintLetVars = letVars
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
      cId <- fresh -- TODO: We generate this id even if it is not used
      case theDef info of
        Axiom{} | isToLevel typ -> return comps{hintLevel = mkComponentQ cId (costLevel costs) qname (Def qname []) typ : hintLevel comps}
                | shouldKeep -> return comps{hintAxioms = mkComponentQ cId (costAxiom costs) qname (Def qname []) typ : hintAxioms comps}
                | otherwise -> return comps
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
          | Just qname == mDefName -> return comps{hintThisFn = Just $ mkComponentQ cId noCost qname (Def qname []) typ}
          | isToLevel typ && isNotMutual qname f
            -> return comps{hintLevel = mkComponentQ cId (costLevel costs) qname (Def qname []) typ : hintLevel comps}
          | isNotMutual qname f && shouldKeep -- TODO: Check if local to module or not
            -> return comps{hintFns = mkComponentQ cId (costFn costs) qname (Def qname []) typ : hintFns comps}
          | otherwise -> return comps
        Datatype{} -> return comps{hintDataTypes = mkComponentQ cId (costSet costs) qname (Def qname []) typ : hintDataTypes comps}
        Record{} -> do
          projections <- mapM (qnameToComponent (costSpeculateProj costs)) =<< getRecordFields qname
          return comps{ hintRecordTypes = mkComponentQ cId (costSet costs) qname (Def qname []) typ : hintRecordTypes comps
                      , hintProjections = projections ++ hintProjections comps}
        -- We look up constructors when we need them
        Constructor{} -> return comps
        -- TODO: special treatment for primitives?
        Primitive{} | isToLevel typ -> return comps{hintLevel = mkComponentQ cId (costLevel costs) qname (Def qname []) typ : hintLevel comps}
                    | shouldKeep -> return comps{hintFns = mkComponentQ cId (costFn costs) qname (Def qname []) typ : hintFns comps}
                    | otherwise -> return comps
        PrimitiveSort{} -> do
          mlog $ "Collect: Primitive " ++ prettyShow (theDef info)
          return comps
      where
        shouldKeep = hintMode /= NoHints || qname `elem` explicitHints

    -- NOTE: We do not reduce the type before checking, so some user definitions
    -- will not be included here.
    isToLevel :: Type -> Bool
    isToLevel typ = case unEl typ of
      Pi _ abs -> isToLevel (unAbs abs)
      Def qname _ -> prettyShow qname == builtinLevelName
      _ -> False

qnameToComponent :: (HasConstInfo tcm, ReadTCState tcm, MonadFresh CompId tcm, MonadTCM tcm)
  => Cost -> QName -> tcm Component
qnameToComponent cost qname = do
  info <- getConstInfo qname
  typ <- typeOfConst qname
  let term = case theDef info of
        Axiom{} -> Def qname []
        DataOrRecSig{} -> __IMPOSSIBLE__
        GeneralizableVar -> Def qname []
        AbstractDefn{} -> __IMPOSSIBLE__
        Function{} -> Def qname []
        Datatype{} -> Def qname []
        Record{} -> Def qname []
        c@Constructor{} -> Con (conSrcCon c) ConOCon []
        Primitive{} -> Def qname []
        PrimitiveSort{} -> Def qname []
  newComponentQ [] cost qname term typ

getEverythingInScope :: MonadTCM tcm => MetaVariable -> tcm [QName]
getEverythingInScope metaVar = do
  let scope = clScope $ getMetaInfo metaVar
  let nameSpace = Scope.everythingInScope scope
      names = Scope.nsNames nameSpace
      qnames = map (Scope.anameName . head) $ Map.elems names
  mlog $ "getEverythingInScope, scope = " ++ prettyShow scope
  return qnames

getLetVars :: (MonadFresh CompId tcm, MonadTCM tcm, Monad tcm) => Cost -> tcm [Open Component]
getLetVars cost = do
  bindings <- asksTC envLetBindings
  mapM makeComp $ Map.toAscList bindings
  where
    -- makeComp :: (Name, Open (Term, Dom Type)) -> tcm (Open Component)
    makeComp (name, opn) = do
      cId <- fresh
      return $ (\(term, typ) -> mkComponent cId [] cost (Just name) term (unDom typ)) <$> opn

builtinLevelName :: String
builtinLevelName = "Agda.Primitive.Level"

collectRecVarCandidates :: (MonadFail tcm, ReadTCState tcm, MonadError TCErr tcm, MonadTCM tcm, HasConstInfo tcm)
  => InteractionId -> tcm (Open [Term])
collectRecVarCandidates ii = do
  ipc <- ipClause <$> lookupInteractionPoint ii
  let fnName = ipcQName ipc
      clauseNr = ipcClauseNo ipc

  info <- getConstInfo fnName
  typ <- typeOfConst fnName
  case theDef info of
    fnDef@Function{} -> do
      let clause = funClauses fnDef !! clauseNr
          naps = namedClausePats clause

      -- Telescope at interaction point
      iTel <- getContextTelescope
      -- Telescope for the body of the clause
      let cTel = clauseTel clause
      -- HACK: To get the correct indices, we shift by the difference in telescope lengths
      -- TODO: Difference between teleArgs and telToArgs?
      let shift = length (telToArgs iTel) - length (telToArgs cTel)

      reportSDoc "mimer" 60 $ do
        pITel <- prettyTCM iTel
        pCTel <- prettyTCM cTel
        return ("Tel:" $+$ nest 2 (pretty iTel $+$ pITel) $+$ "CTel:" $+$ nest 2 (pretty cTel $+$ pCTel))
      reportSDoc "mimer" 60 $ return $ "Shift:" <+> pretty shift
      -- makeOpen

      -- TODO: Names (we don't use flex)
      let flex = concatMap (go False . namedThing . unArg) naps
          terms = map (\n -> Var (n + shift) []) flex
      mlog $ "naps: " ++ prettyShow naps
      mlog $ "terms: " ++ show terms
      makeOpen terms
    _ -> do
      mlog $ "Did not get a function"
      makeOpen []
  where
    go isUnderCon = \case
      VarP patInf x | isUnderCon -> [{- var $ -} dbPatVarIndex x]
                    | otherwise -> []
      DotP patInf t -> [] -- Ignore dot patterns
      ConP conHead conPatInf namedArgs -> concatMap (go True . namedThing . unArg) namedArgs
      LitP{} -> []
      ProjP{} -> []
      IApplyP{} -> [] -- Only for Cubical?
      DefP{} -> [] -- Only for Cubical?

runComponentGen :: ComponentGen -> SM Component
runComponentGen = undefined
-- runComponentGen (ComponentDone comp) = return comp
-- runComponentGen (NeedsArg typ f) = do
--   let arg = undefined typ
--   runComponentGen (f arg)


------------------------------------------------------------------------------
-- * Measure performance
------------------------------------------------------------------------------
data MimerStats = MimerStats
  { statCompHit :: Nat -- ^ Could make use of an already generated component
  , statCompGen :: Nat -- ^ Could use a generator for a component
  , statCompRegen :: Nat -- ^ Had to regenerate the cache (new context)
  , statCompNoRegen :: Nat -- ^ Did not have to regenerate the cache
  , statMetasCreated :: Nat -- ^ Total number of meta-variables created explicitly (not through unification)
  , statTypeEqChecks :: Nat -- ^ Number of times type equality is tested (with unification)
  , statRefineSuccess :: Nat -- ^ Number of times a refinement has been successful
  , statRefineFail :: Nat -- ^ Number of times a refinement has failed
  } deriving (Show, Eq, Generic)
instance NFData MimerStats

emptyMimerStats :: MimerStats
emptyMimerStats = MimerStats
  { statCompHit = 0, statCompGen = 0, statCompRegen = 0 , statCompNoRegen = 0 , statMetasCreated = 0, statTypeEqChecks = 0, statRefineSuccess = 0 , statRefineFail = 0}

incCompHit, incCompGen, incCompRegen, incCompNoRegen, incMetasCreated, incTypeEqChecks, incRefineSuccess, incRefineFail :: MimerStats -> MimerStats
incCompHit       stats = stats {statCompHit       = succ $ statCompHit stats}
incCompGen       stats = stats {statCompGen       = succ $ statCompGen stats}
incCompRegen     stats = stats {statCompRegen     = succ $ statCompRegen stats}
incCompNoRegen   stats = stats {statCompNoRegen   = succ $ statCompNoRegen stats}
incMetasCreated  stats = stats {statMetasCreated  = succ $ statMetasCreated stats}
incTypeEqChecks  stats = stats {statTypeEqChecks  = succ $ statTypeEqChecks stats}
incRefineSuccess stats = stats {statRefineSuccess = succ $ statRefineSuccess stats}
incRefineFail    stats = stats {statRefineFail    = succ $ statRefineFail stats}

updateStat :: (MimerStats -> MimerStats) -> SM ()
updateStat f = verboseS "mimer.stats" 1 $ do
  ref <- asks searchStats
  liftIO $ modifyIORef' ref f

------------------------------------------------------------------------------
-- * Core algorithm
------------------------------------------------------------------------------

-- TODO: Integrate stopAfterFirst with Options (maybe optStopAfter Nat?)
runSearch :: Options -> Bool -> InteractionId -> TCM [String]
runSearch options stopAfterFirst ii = withInteractionId ii $ do
  mTheFunctionQName <- fmap ipClause (lookupInteractionPoint ii) <&> \case
    clause@IPClause{} -> Just $ ipcQName clause
    IPNoClause -> Nothing
  reportS "mimer.init" 15 (text "Interaction point in function: " <> pretty mTheFunctionQName)

  metaId <- lookupInteractionId ii
  metaVar <- lookupLocalMeta metaId

  state <- getTC
  env <- askTC

  metaIds <- case mvInstantiation metaVar of
    InstV inst -> do

      metaIds <- allOpenMetas (instBody inst)
      -- mlog $ "Instantiation already present at top-level: " ++ prettyShow (instBody inst) ++ " remaining metas: " ++ prettyShow metaIds ++ " all occurring metas: " ++ prettyShow (allMetas (:[]) (instBody inst))

      -- TODO: Make pretty instantiation for 'Instantiation'?
      reportSLn "mimer.init" 20 $ "Interaction point already instantiated: " ++ prettyShow (instBody inst) ++ " with args " ++ prettyShow (instTel inst)

      -- mlog $ "Extra arguments: " ++ prettyShow (instTel inst)
      -- ctx <- getContextTelescope
      -- mlog $ "The metaId: " ++ prettyShow metaId ++ " with context " ++ prettyShow ctx
      return metaIds
    Open -> do
      reportSLn "mimer.init" 20 "Interaction point not instantiated."
      mlog $ "No insantiation present at top-level."
      return [metaId]
    _ -> __IMPOSSIBLE__
  -- TODO: Print each meta-variable's full context telescope
  reportSDoc "mimer.init" 20 $ ("Remaining meta-variables to solve:" <+>) <$> prettyTCM metaIds

  -- Check if there are any meta-variables to be solved
  case metaIds of
    -- No variables to solve, return the instantiation given
    [] -> do
      -- old code:
      -- (:[]) <$> (showTCM =<< fromMaybe __IMPOSSIBLE__ <$> getMetaInstantiation metaId)
      -- TODO: HACK! ask for proper way (metaTel?)
      case mvInstantiation metaVar of
        InstV inst -> do
          cxtSize <- getContextSize
          -- mlog $ "getContextSize: " ++ show cxtSize
          body <- showTCM (instBody inst)
          let res = (if null (instTel inst)
                     then ""
                     else "λ " ++ (unwords $ map unArg $ drop cxtSize $ instTel inst) ++ " → ")
                    ++ body
          reportSLn "mimer.init" 15 $ "Hack-building already instantiated term: " ++ res
          return [res]
        _ -> __IMPOSSIBLE__
    _ -> do
      let costs = defaultCosts
      components <- collectComponents options costs ii mTheFunctionQName metaId
      startGoals <- mapM mkGoal metaIds
      let startBranch = SearchBranch
            { sbTCState = state
            , sbGoals = startGoals
            , sbCost = 0
            , sbCache = Map.empty
            , sbComponentsUsed = Map.empty
            }

      statsRef <- liftIO $ newIORef emptyMimerStats
      checkpoint <- viewTC eCurrentCheckpoint
      let searchOptions = SearchOptions
            { searchComponents = components
            , searchHintMode = optHintMode options
            , searchTimeout = optTimeout options
            , searchTopMeta = metaId
            , searchTopEnv = env
            , searchTopCheckpoint = checkpoint
            , searchCosts = costs
            , searchStats = statsRef
            }

      reportDoc "mimer.init" 20 ("Using search options:" $+$ nest 2 (pretty searchOptions))
      reportDoc "mimer.init" 20 ("Initial search branch:" $+$ nest 2 (pretty startBranch))

      flip runReaderT searchOptions $ bench [Bench.Deserialization] $ do
        -- mlog $ "Components: " ++ prettyShow components
        -- mlog =<< ("startBranch: " ++) <$> prettyBranch startBranch

        -- TODO: Check what timing stuff is used in Agda.Utils.Time
        timeout <- secondsToNominalDiffTime . (/1000) . fromIntegral <$> asks searchTimeout
        startTime <- liftIO $ getCurrentTime
        let go :: Int -> MinQueue SearchBranch -> SM ([Expr], Int)
            go n branchQueue = case Q.minView branchQueue of
              Nothing -> do
                reportSLn "mimer.search" 30 $ "No remaining search branches."
                return ([], n)
              Just (branch, branchQueue') -> do
                time <- liftIO $ getCurrentTime

                reportSMDoc "mimer.search" 40 $ do
                  inst <- branchInstantiationDocCost branch
                  metas <- prettyTCM $ map goalMeta $ sbGoals branch
                  return $
                    "Choosing branch with instantiation:" $+$ nest 2
                    (inst $+$ "..and remaining metas:" <+> pretty metas)
                reportDoc "mimer.search" 50 $ "Full branch:" <+> pretty branch
                reportSMDoc "mimer.search" 45 $ do
                  is <- mapM branchInstantiationDocCost $ Q.toAscList branchQueue
                  return $ "Instantiation of other branches:" <+> prettyList is

                let elapsed = diffUTCTime time startTime
                if elapsed < timeout
                then do
                  (newBranches, sols) <- partitionStepResult <$> refine branch
                  let branchQueue'' = foldr Q.insert branchQueue' newBranches
                  reportSLn "mimer.search" 40 $ show (length sols) ++ " solutions found during cycle " ++ show (n + 1)
                  reportSMDoc "mimer.search" 45 $ ("Solutions:" <+>) <$> prettyTCM sols
                  reportSMDoc "mimer.search" 45 $ do
                     is <- mapM branchInstantiationDocCost newBranches
                     return $ "New branch instantiations:" <+> prettyList is

                  if stopAfterFirst
                  then case sols of
                         [] -> do
                           reportSLn "mimer.search" 40 $ "Continuing search"
                           go (n+1) branchQueue''
                         _ -> do
                           reportSLn "mimer.search" 40 $ "Search done (stopping after first solution)"
                           return (sols, n)
                  else do
                    reportSLn "mimer.search" 40 $ "Continuing search"
                    mapFst (sols ++) <$> go (n+1) branchQueue''
                else do
                  reportSLn "mimer.search" 30 $ "Search time limit reached. Elapsed search time: " ++ show elapsed
                  return ([], n)
        (sols, nrSteps) <- go 0 $ Q.singleton startBranch
        reportSLn "mimer.search" 20 $ "Search ended after " ++ show (nrSteps + 1) ++ " cycles"
        solStrs <- mapM showTCM sols
        reportSLn "mimer.search" 15 $ "Solutions found: " ++ prettyShow solStrs
        let q = do
              ref <- asks searchStats
              stats <- liftIO $ readIORef ref
              return $ "Statistics:" <+> text (show stats)

        reportSMDoc "mimer.stats" 10 $ (q :: SM Doc)
        return solStrs

prepareComponents :: Goal -> SearchBranch -> SM (SearchBranch, [Component])
prepareComponents goal branch = withBranchAndGoal branch goal $ do
  cxtTel <- getContextTelescope
  case Map.lookup cxtTel (sbCache branch) of
    Nothing -> do
      updateStat incCompRegen
      reportDoc "mimer.components" 20 $ "No cache found for current context" <+> parens (pretty cxtTel) <+> ". Generating one."
      -- Generate components for this context
      componentsWithGen <- genComponents
      reportDoc "mimer.components" 20 $ "Generated cache with" <+> pretty (length componentsWithGen) <+> "components"
      checkpoint <- viewTC eCurrentCheckpoint
      let components = map fst componentsWithGen
          cache = (checkpoint, Map.fromList $ map (\(c,g) -> (compId c, (Just c, g))) componentsWithGen)
          newSbCache = Map.insert cxtTel cache (sbCache branch)
      -- Update the branch because state has new meta-variables
      branch' <- updateBranch [] branch{sbCache=newSbCache}
      return (branch', components)
    Just (checkpoint, cache) -> do
      updateStat incCompNoRegen
      reportDoc "mimer.components" 20 $ "Cache found for current context" <+> parens (pretty cxtTel)
      verboseS "mimer.sanity" 10 $ do
        subst <- checkpointSubstitution checkpoint
        unless (subst == IdS) $ reportDoc "mimer.sanity" 10 $
          "WARNING! Substitution should be identity, but was " <+> pretty subst
          <+> "when accessing cache for context" <+> pretty cxtTel
      -- TODO:
      -- Traverse the map, regenerating components as needed

      components <- mapM (\case
                             (Nothing, gen) -> runComponentGen gen
                             (Just comp, _) -> return comp) (Map.elems cache)
      -- Update the branch because state has new meta-variables
      branch' <- updateBranch [] branch
      return (branch', components)


genComponents :: SM [(Component, ComponentGen)]
genComponents = do
  cost <- asks (costLocal . searchCosts)
  localVars <- getLocalVars cost
  concatMapM (genComponentsFrom True) localVars

genComponentsFrom :: Bool -- ^ Apply record elimination
                  -> Component
                  -> SM [(Component, ComponentGen)]
genComponentsFrom False comp = do
  comp <- applyToMetasG 0 Nothing comp
  return [(comp,[])]
genComponentsFrom appRecElims origComp = go Set.empty origComp
  where
  -- We keep a set of recursive records that we have already "seen" to avoid looping
  go :: Set QName -> Component -> SM [(Component, ComponentGen)]
  go seenRecords comp = do
    comp' <- applyToMetasG 0 Nothing comp
    projComps <- case unEl (compType comp') of
      Def qname elims
        | Set.member qname seenRecords -> do
            reportDoc "mimer.components" 60 $
              "Skipping projection because recursive record already seen: " <+> pretty qname
            return []
        | otherwise -> isRecord qname >>= \case
          Nothing -> return [(comp', [])]
          Just defn -> do
            -- TODO: Is there a better way to check if a record is recursive? There is a recMutual field
            reportDoc "mimer.temp" 10 $ "Record recursive?" <+> pretty qname <+> ( if isNothing $ recInduction defn then "no" else "yes" )
            let seenRecords' =
                  if isNothing $ recInduction defn
                  then seenRecords
                  else Set.insert qname seenRecords
                -- Mark all the arguments as implicit
                recordArgs = map (setHiding Hidden) (argsFromElims elims)
            reportDoc "mimer.temp" 10 $ "Record args:" <+> pretty (map (\arg -> (pretty $ unArg arg, argInfoHiding $ argInfo arg)) recordArgs)
            cost <- asks (costProj . searchCosts)
            fields <- getRecordFields qname
            comps <- mapM (applyProj recordArgs comp' cost) fields
            compWGens <- mapM (go seenRecords') comps
            -- Add the projection name to generators
            let finishedComps =
                   concat (zipWith (\cgs f -> map (\(c,g) -> (c,f:g)) cgs) compWGens fields)
            return $ finishedComps

      _ -> do
        reportDoc "mimer.temp" 10 $ "Non-record type:" <+> pretty (compType comp')
        return []
    return $ (comp', []) : projComps
    where
      applyProj :: Args -> Component -> Cost -> QName -> SM Component
      applyProj recordArgs comp' cost qname = do
        -- Add meta-variables for the record parameters
        projNoArgs <- qnameToComponent cost qname
        let projTerm = apply (compTerm projNoArgs) recordArgs
        projType <- piApplyM (compType projNoArgs) recordArgs
        let dom = case unEl $ projType of Pi dom _ -> dom; _ -> __IMPOSSIBLE__
            arg = setOrigin Inserted $ compTerm comp' <$ argFromDom dom
            newTerm = apply projTerm [arg]
        newType <- piApplyM projType (compTerm comp')

        reportSDoc "mimer.temp" 10 $ do
          ter <- instantiateFull newTerm >>= prettyTCM
          typ <- instantiateFull newType >>= prettyTCM
          return $ "After projection:" <+> ter <+> typ
        newComponentQ (compMetas comp') (compCost comp' + cost) qname newTerm newType


applyToMetasG
  :: Nat -- ^ Arguments to skip applying term. Used for record parameters.
  -> Maybe Nat -- ^ Max number of arguments to apply.
  -> Component -> SM Component
applyToMetasG _ (Just m) comp | m <= 0 = return comp
applyToMetasG skip maxArgs comp = do
  ctx <- getContextTelescope
  case unEl (compType comp) of
    Pi dom abs -> do
      let domainType = unDom dom
      (metaId, metaTerm) <- createMeta domainType
      let arg = setOrigin Inserted $ metaTerm <$ argFromDom dom
      newType <- reduce =<< piApplyM (compType comp) metaTerm
      -- For records, the parameters are not included in the term
      let newTerm = if skip > 0 then compTerm comp else apply (compTerm comp) [arg]
      cost <- asks $ (if getHiding arg == Hidden then costNewHiddenMeta else costNewMeta) . searchCosts
      applyToMetasG (predNat skip) (predNat <$> maxArgs)
                    comp{ compTerm = newTerm
                        , compType = newType
                        , compMetas = metaId : compMetas comp
                        , compCost = cost + compCost comp
                        }
    _ -> return comp

createMeta :: Type -> SM (MetaId, Term)
createMeta typ = do
  (metaId, metaTerm) <- newValueMeta DontRunMetaOccursCheck CmpLeq typ
  verboseS "mimer.stats" 20 $ updateStat incMetasCreated
  reportSDoc "mimer.components" 80 $ do
    metaType <- getMetaTypeInContext metaId
    return $ "Created meta-variable (type in context):" <+> pretty metaTerm <+> ":" <+> pretty metaType
  return (metaId, metaTerm)


partitionStepResult :: [SearchStepResult] -> ([SearchBranch], [Expr])
partitionStepResult [] = ([],[])
partitionStepResult (x:xs) = case x of
  NoSolution -> rest
  OpenBranch br -> (br:brs', exps)
  ResultExpr exp -> (brs', exp:exps)
  where rest@(brs',exps) = partitionStepResult xs


topInstantiationDoc :: SM Doc
topInstantiationDoc = asks searchTopMeta >>= getMetaInstantiation >>= maybe (return "(nothing)") prettyTCM

branchInstantiationDocCost :: SearchBranch -> SM Doc
branchInstantiationDocCost branch = do
  inst <- branchInstantiationDoc branch
  return $ inst <+> parens ("cost =" <+> pretty (sbCost branch))

-- | For debug
branchInstantiationDoc :: SearchBranch -> SM Doc
branchInstantiationDoc branch = withBranchState branch topInstantiationDoc

refine :: SearchBranch -> SM [SearchStepResult]
refine branch = withBranchState branch $ do
  (goal, branch') <- nextBranchMeta' branch

  reportDoc "mimer.refine" 20 $ "Refining goal" <+> pretty goal

  withBranchAndGoal branch' goal $ do
    goalType <- bench [Bench.Deserialization, Bench.Reduce] $ reduce =<< getMetaTypeInContext (goalMeta goal)

    reportDoc "mimer.refine" 30 $ "Goal type:" <+> pretty goalType
    reportSDoc "mimer.refine" 30 $ ("Goal context:" <+>) . pretty <$> getContextTelescope

    -- Lambda-abstract as far as possible
    tryLamAbs goal goalType branch' >>= \case
      -- Abstracted with absurd pattern: solution found.
      Left expr -> do
        reportSDoc "mimer.refine" 30 $ ("Abstracted with absurd lambda. Result: " <+>) <$> prettyTCM expr
        return [ResultExpr expr]
      -- Normal abstraction
      Right (goal', goalType', branch'') -> do
        (branch''', components) <- prepareComponents goal' branch''
        withBranchAndGoal branch''' goal' $ do
          reportSMDoc "mimer.temp" 10 $ do
            subst <- checkpointSubstitution =<< asks searchTopCheckpoint
            return $ "Substitution after abstraction:" <+> pretty subst

          reportSDoc "mimer.refine" 40 $ getContextTelescope >>= \tel -> return $
            "After lambda abstract:" <+> nest 2 (vcat
                                                [ "Goal:" <+> pretty goal'
                                                , "Goal type:" <+> pretty goalType'
                                                , "Goal context:" <+> pretty tel])

          reportSDoc "mimer.components" 20 $ do
            comps <- mapM prettyTCM components
            return $ "Components:" $+$ nest 2 (vcat comps)

          results1 <- mapM checkSolved =<< catMaybes <$> mapM (tryRefineWith goal' goalType' branch''') components
          results2 <- tryDataRecord goal' goalType' branch'''
          return $ results1 ++ results2
          -- We reduce the meta type to WHNF(?) immediately to avoid refining it
          -- multiple times later (required e.g. to check if it is a Pi type)
          -- results1 <- tryLocals     goal' goalType' branch''
          -- results2 <- tryDataRecord goal' goalType' branch''
          -- results3 <- tryLet        goal' goalType' branch''
          -- results4 <- tryProjs      goal' goalType' branch''
          -- results5 <- tryRecCall    goal' goalType' branch''
          -- results6 <- tryFns        goal' goalType' branch''
          -- results7 <- tryAxioms     goal' goalType' branch''
          -- let results = results1 ++ results2 ++ results3 ++ results4 ++ results5 ++ results6 ++ results7
          -- return results

tryFns :: Goal -> Type -> SearchBranch -> SM [SearchStepResult]
tryFns goal goalType branch = withBranchAndGoal branch goal $ do
  reportDoc "mimer.refine.fn" 50 $ "Trying functions"
  fns <- asks (hintFns . searchComponents)
  newBranches <- catMaybes <$> mapM (tryRefineAddMetas goal goalType branch) fns
  mapM checkSolved newBranches

tryProjs :: Goal -> Type -> SearchBranch -> SM [SearchStepResult]
tryProjs goal goalType branch = withBranchAndGoal branch goal $ do
  projs <- asks (hintProjections . searchComponents)
  newBranches <- catMaybes <$> mapM (tryRefineAddMetas goal goalType branch) projs
  mapM checkSolved newBranches

tryAxioms :: Goal -> Type -> SearchBranch -> SM [SearchStepResult]
tryAxioms goal goalType branch = withBranchAndGoal branch goal $ do
  axioms <- asks (hintAxioms . searchComponents)
  newBranches <- catMaybes <$> mapM (tryRefineAddMetas goal goalType branch) axioms
  mapM checkSolved newBranches

tryLet :: Goal -> Type -> SearchBranch -> SM [SearchStepResult]
tryLet goal goalType branch = withBranchAndGoal branch goal $ do
  letVars <- asks (hintLetVars . searchComponents) >>= mapM getOpenComponent
  mlog $ "Let vars: " ++ prettyShow letVars
  newBranches <- catMaybes <$> mapM (tryRefineAddMetas goal goalType branch) letVars
  mapM checkSolved newBranches

-- | Returns @Right@ for normal lambda abstraction and @Left@ for absurd lambda.
tryLamAbs :: Goal -> Type -> SearchBranch -> SM (Either Expr (Goal, Type, SearchBranch))
tryLamAbs goal goalType branch =
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
          bodyType <- bench [Bench.Deserialization, Bench.Reduce] $ reduce =<< piApplyM goalType' (Var 0 []) -- TODO: Good place to reduce?
          (metaId', metaTerm) <- bench [Bench.Deserialization, Bench.Free] $ newValueMeta DontRunMetaOccursCheck CmpLeq bodyType
          mlog $ "Created meta " ++ prettyShow metaId' ++ " in tryLamAbs"
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
          tryLamAbs goal' bodyType branch'
    _ -> do
      branch' <- updateBranch [] branch -- TODO: Is this necessary?
      return $ Right (goal, goalType, branch')


tryRecCall :: Goal -> Type -> SearchBranch -> SM [SearchStepResult]
tryRecCall goal goalType branch = asks (hintThisFn . searchComponents) >>= \case
  Nothing -> return []
  Just thisFn -> withBranchAndGoal branch goal $ do
    localCost <- asks (costLocal . searchCosts)
    localVars <- bench [Bench.Deserialization, Bench.Level] $ getLocalVars localCost
    recCand <- asks (hintRecVars . searchComponents) >>= getOpen
    let recCandidates = filter (\t -> case compTerm t of v@Var{} -> v `elem` recCand; _ -> False) localVars
    reportSDoc "mimer.refine.rec" 60 $ ("Argument candidates for recursive call:" <+>) <$> prettyTCM recCandidates

    case recCandidates of
      -- If there are no argument candidates for recursive call, there is no reason to try one.
      [] -> return []
      _ -> do
        -- Disable occurs check for the variable to allow recursive call
        (goal', branch') <- ensureNoOccursCheck goal branch
        -- Apply the recursive call to new metas
        (thisFnTerm', thisFnType, newMetas) <- applyToMetas 0 (compTerm thisFn) (compType thisFn)
        -- TODO: Good idea to use noCost here? The actual cost is added later for now.
        thisFnComp <- newComponent newMetas noCost (compName thisFn) thisFnTerm' thisFnType
        -- Newly created metas must be stored in the branch state
        branch'' <- updateBranch [] branch'

        reportSDoc "mimer.refine.rec" 60 $ return ("Recursive call component:" <+> pretty thisFnComp)
        -- Try using the recursive call
        tryRefineWith goal' goalType branch'' thisFnComp >>= \case
          -- Recursive call failed
          Nothing -> do
            reportSMDoc "mimer.refine.rec" 60 $ "Assigning the recursive call failed"
            return []
          -- Recursive call succeeded
          Just branch''' -> do
            reportSMDoc "mimer.refine.rec" 60 $ "Assigning the recursive call succeeded"
            let argGoals = map (mkGoalPreserveEnv goal') newMetas
            let fillArg g = do
                  gType <- getMetaTypeInContext (goalMeta g)
                  reportSDoc "mimer.refine.rec" 60 $ return ("Arg " <+> pretty (goalMeta g) <+> ":" <+> pretty gType)
                  let remainingArgGoals = argGoals \\ [g]
                  r <- catMaybes <$> mapM (\recCandidate -> do
                     mbr <- tryRefineWith g gType branch''' recCandidate
                     return $ fmap (\br -> br{sbGoals = remainingArgGoals ++ sbGoals br}) mbr
                     ) recCandidates
                  reportSDoc "mimer.refine.rec" 60 $ return ("Possibilities: " <+> pretty (length r))
                  return r

            argBranches <- concatMapM fillArg argGoals
            reportSDoc "mimer.refine.rec" 60 $ return ("Number of argument branches" <+> pretty (length argBranches))
            mapM checkSolved argBranches
  where
  -- HACK: If the meta-variable is set to run occurs check, assigning a
  -- recursive call to it will cause an error. Therefore, we create a new
  -- meta-variable with the check disabled and assign it to the previous
  -- one.
  ensureNoOccursCheck :: Goal -> SearchBranch -> SM (Goal, SearchBranch)
  ensureNoOccursCheck goal branch = do
    metaVar <- lookupLocalMeta (goalMeta goal)
    if miMetaOccursCheck (mvInfo metaVar) == DontRunMetaOccursCheck
    then do
      reportDoc "mimer.refine.rec" 60 $ "Meta-variable already has DontRunMetaOccursCheck"
      return (goal, branch)
    else do
      metaArgs <- getMetaContextArgs metaVar
      (newMetaId, newMetaTerm) <- newValueMeta DontRunMetaOccursCheck CmpLeq goalType
      assignV DirLeq (goalMeta goal) metaArgs newMetaTerm (AsTermsOf goalType)
      reportDoc "mimer.refine.rec" 60 $ "Instantiating meta-variable (" <> pretty (goalMeta goal) <> ") with a new one with DontRunMetaOccursCheck (" <> pretty newMetaId <> ")"
      branch' <- updateBranch [] branch
      return (goal{goalMeta = newMetaId}, branch')


-- TODO: Factor out `checkSolved`
tryDataRecord :: Goal -> Type -> SearchBranch -> SM [SearchStepResult]
tryDataRecord goal goalType branch = withBranchAndGoal branch goal $ do
  -- TODO: There is a `isRecord` function, which performs a similar case
  -- analysis as here, but it does not work for data types.
  case unEl goalType of
    Def qname elims -> theDef <$> getConstInfo qname >>= \case
      recordDefn@Record{} -> do
        -- mlog $ "Found a Record: " ++ prettyShow recordDefn
        tryRecord recordDefn
      dataDefn@Datatype{} -> do
        -- mlog $ "Found a Datatype: " ++ prettyShow dataDefn
        tryData dataDefn
      primitive@Primitive{} -> do
        mlog $ "Found a Primitive: " ++ prettyShow primitive
        return []
      -- TODO: Better way of checking that type is Level
      d@Axiom{}
        | prettyShow qname == "Agda.Primitive.Level" -> do
            tryLevel
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
      trySet level
    Sort sort -> do
      mlog $ "Found an sort that is not yet handled: " ++ prettyShow sort
      return []
    _ -> return []
  where
      -- TODO: Alternatively, the constructor can be accessed via `getRecordConstructor`
      -- TODO: There might be a neater way of applying the constructor to new metas
    tryRecord :: Defn -> SM [SearchStepResult]
    tryRecord recordDefn = do
      let cHead = recConHead recordDefn
          cName = conName cHead
          cTerm = Con cHead ConOSystem []
      cType <- typeOfConst cName
      cost <- asks (costRecordCon . searchCosts) -- TODO: Use lenses for this?
      comp <- newComponentQ [] cost cName cTerm cType
      -- -- NOTE: at most 1
      newBranches <- maybeToList <$> tryRefineAddMetasSkip (recPars recordDefn) goal goalType branch comp
      mapM checkSolved newBranches

    tryData :: Defn -> SM [SearchStepResult]
    tryData dataDefn = do
      cost <- asks (costDataCon . searchCosts)
      comps <- mapM (qnameToComponent cost) $ dataCons dataDefn
      newBranches <- mapM (tryRefineAddMetas goal goalType branch) comps
      -- TODO: Reduce overlap between e.g. tryLocals, this and tryRecord
      mapM checkSolved (catMaybes newBranches)

    tryLevel :: SM [SearchStepResult]
    tryLevel = do
      levelHints <- asks (hintLevel . searchComponents)
      newBranches <- catMaybes <$> mapM (tryRefineAddMetas goal goalType branch) levelHints
      mapM checkSolved newBranches

    -- TODO: Add an extra filtering on the sort
    trySet :: Level -> SM [SearchStepResult]
    trySet level = do
      setTerm <- bench [Bench.Deserialization, Bench.Reduce] $ reduce level >>= \case
        reducedLevel@(Max i [])
          | i > 0 -> do
              cost <- asks (costSet . searchCosts)
              comp <- newComponent [] cost Nothing (Sort $ Type $ Max (i-1) []) goalType
              return [comp]
          | otherwise -> do
              mlog $ "trySet: don't know what to do with level " ++ prettyShow reducedLevel
              return []
        reducedLevel -> do
          mlog $ "trySet: don't know what to do with " ++ prettyShow reducedLevel
          return []
      components <- asks searchComponents
      newBranches <- catMaybes <$> mapM (tryRefineAddMetas goal goalType branch)
                      (setTerm ++ concatMap ($ components)
                       [ hintDataTypes
                       , hintRecordTypes
                       , hintAxioms])
      mapM checkSolved newBranches

-- | Type should already be reduced here
-- NOTE: Does not reset the state!
-- TODO: Make sure the type is always reduced
tryRefineWith :: Goal -> Type -> SearchBranch -> Component -> SM (Maybe SearchBranch)
tryRefineWith goal goalType branch comp = withBranchAndGoal branch goal $ do
  reportSMDoc "mimer.refine" 50 $ do
    cxt <- getContextTelescope >>= prettyTCM
    hi <- prettyTCM $ compTerm comp
    ht <- prettyTCM $ compType comp
    gm <- prettyTCM $ goalMeta goal
    gt <- prettyTCM goalType
    return $ "Trying refinement" <+> hi <+> ":" <+> ht $+$ nest 2 ("for" <+> gm <+> ":" <+> gt $+$ "in context" <+> cxt)

  metasCreatedBy (dumbUnifier (compType comp) goalType) >>= \case
    (True, newMetaStore) -> do
      updateStat incRefineSuccess
      -- TODO: Why is newMetaIds not used here?
      newMetaIds <- assignMeta (goalMeta goal) (compTerm comp) goalType
      -- TODO: check if everything is solved?
      let newMetaIds' = Map.keys (openMetas newMetaStore)
      mlog $ "  New metas (tryRefineWith): " ++ prettyShow newMetaIds'

      reportSMDoc "mimer.refine" 50 $ "Refinement succeeded"
      -- Take the metas stored in the component and add them as sub-goals
      Just <$> updateBranchCost comp (newMetaIds' ++ compMetas comp) branch
    (False, _) -> do
      updateStat incRefineFail
      reportSMDoc "mimer.refine" 50 $ "Refinement failed"
      return Nothing


-- TODO: Make policy for when state should be put
tryRefineAddMetasSkip :: Nat -> Goal -> Type -> SearchBranch -> Component -> SM (Maybe SearchBranch)
tryRefineAddMetasSkip skip goal goalType branch comp = withBranchAndGoal branch goal $ do
  -- Apply the hint to new metas (generating @c@, @c ?@, @c ? ?@, etc.)
  -- TODO: Where is the best place to reduce the hint type?
  comp' <- applyToMetasG skip Nothing comp
  branch' <- updateBranch [] branch
  tryRefineWith goal goalType branch' comp'

tryRefineAddMetas :: Goal -> Type -> SearchBranch -> Component -> SM (Maybe SearchBranch)
tryRefineAddMetas = tryRefineAddMetasSkip 0

-- TODO: Make sure the type is reduced the first time this is called
-- TODO: Rewrite with Component?
-- NOTE: The new metas are in left-to-right order -- the opposite of the
-- order they should be solved in.
applyToMetas' :: Nat -> Term -> Type -> SM (Term, Type, [MetaId])
applyToMetas' skip term typ = do
  ctx <- getContextTelescope
  mlog $ prettyShow ctx
  case unEl typ of
    Pi dom abs -> do
      let domainType = unDom dom
      -- TODO: What exactly does the occur check do?
      (metaId', metaTerm) <- bench [Bench.Deserialization, Bench.Free] $ newValueMeta DontRunMetaOccursCheck CmpLeq domainType
      mlog $ "Created meta " ++ prettyShow metaId' ++ " in applyToMetas"
      let arg = setOrigin Inserted $ metaTerm <$ argFromDom dom
      newType <- bench [Bench.Deserialization, Bench.Reduce] $ reduce =<< piApplyM typ metaTerm -- TODO: Is this the best place to reduce?
      -- For records, the parameters are not included in the term
      let newTerm = if skip > 0 then term else apply term [arg]
      (term', typ', metas) <- applyToMetas' (predNat skip) newTerm newType
      return (term', typ', metaId' : metas)
    _ -> return (term, typ, [])


-- TODO: Remove this version (it is just for bench-marking)
applyToMetas :: Nat -> Term -> Type -> SM (Term, Type, [MetaId])
applyToMetas skip term typ = bench [Bench.Deserialization, Bench.Generalize] $ applyToMetas' skip term typ

checkSolved :: SearchBranch -> SM SearchStepResult
checkSolved branch = {-# SCC "custom-checkSolved" #-} bench [Bench.Deserialization, Bench.Sort] $ do
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

updateBranch' :: Maybe Component -> [MetaId] -> SearchBranch -> SM SearchBranch
updateBranch' mComp newMetaIds branch = do
  state <- getTC
  let compsUsed = sbComponentsUsed branch
  (deltaCost, compsUsed') <- case mComp of
        Nothing -> return (0, compsUsed)
        Just comp -> do
          case compName comp of
            Nothing -> return (compCost comp, compsUsed)
            Just name -> case compsUsed Map.!? name of
              Nothing -> return (compCost comp, Map.insert name 1 compsUsed)
              -- TODO: Currently using: uses^2+1 as cost. Make a parameter?
              Just uses -> do
                reuseCost <- asks (costCompReuse . searchCosts)
                return (compCost comp + reuseCost uses, Map.adjust succ name compsUsed)
  newGoals <- mapM mkGoal newMetaIds
  return branch{ sbTCState = state
               , sbGoals = newGoals ++ sbGoals branch
               , sbCost = sbCost branch + deltaCost
               , sbComponentsUsed = compsUsed'
               }

updateBranch :: [MetaId] -> SearchBranch -> SM SearchBranch
updateBranch = updateBranch' Nothing

updateBranchCost :: Component -> [MetaId] -> SearchBranch -> SM SearchBranch
updateBranchCost comp = updateBranch' (Just comp)

assignMeta :: MetaId -> Term -> Type -> SM [MetaId]
assignMeta metaId term metaType = bench [Bench.Deserialization, Bench.CheckRHS] $ {-# SCC "custom-assignMeta" #-}
  metasCreatedBy (do
    metaVar <- lookupLocalMeta metaId
    metaArgs <- getMetaContextArgs metaVar

    -- reportSMDoc "mimer.assignMeta" 60 $ do
    --   hi <- prettyTCM term
    --   mt <- prettyTCM metaType
    --   mv <- prettyTCM metaId
    --   return $ "Assigning" <+> hi <+> "to meta variable" <+> mv <+> ":" <+> mt
    reportSMDoc "mimer.assignMeta" 60 $ do
      cxt <- getContextTelescope
      return $ "Assigning" <+> pretty term $+$ nest 2 ("to" <+> pretty metaId <+> ":" <+> pretty metaType $+$ "in context" <+> pretty cxt)

    (assignV DirLeq metaId metaArgs term (AsTermsOf metaType)) `catchError` \err -> do
      reportSMDoc "mimer.assignMeta" 30 $ do
        er <- prettyTCM err
        cxt <- getContextTelescope
        return $ "Got error from assignV:" <+> er $+$ nest 2 ("when trying to assign" <+> pretty term $+$ "to" <+> pretty metaId <+> ":" <+> pretty metaType $+$ "in context" <+> pretty cxt)) >>= \case
        ((), newMetaStore) -> do
          let newMetaIds = Map.keys (openMetas newMetaStore)
          mlog $ "New metas created in assignMeta: " ++ prettyShow newMetaIds
          return newMetaIds



-- dumbUnifier :: (MonadTCM tcm, PureTCM tcm, MonadWarning tcm, MonadStatistics tcm, MonadMetaSolver tcm, MonadFresh Int tcm, MonadFresh ProblemId tcm)
--   => Type -> Type -> tcm Bool
dumbUnifier :: Type -> Type -> SM Bool
dumbUnifier t1 t2 = bench [Bench.Deserialization, Bench.UnifyIndices] $ do
  updateStat incTypeEqChecks
  (noConstraints $ equalType t2 t1 >> return True) `catchError` \err -> do
--     str <- showTCM err
--     mlog $ "dumbUnifier error: " ++ str
    return False


-- Duplicate of a local definition in Agda.Interaction.BasicOps
showTCM :: (MonadPretty tcm, PrettyTCM a) => a -> tcm String
showTCM v = render <$> prettyTCM v

bench :: NFData a => [Bench.Phase] -> SM a -> SM a
bench k ma = billTo (Bench.Deserialization:k) ma
  -- r <- ma
  -- return $ force r

-- Local variables:
-- getContext :: MonadTCEnv m => m [Dom (Name, Type)]
-- getContextArgs :: (Applicative m, MonadTCEnv m) => m Args
-- getContextTelescope :: (Applicative m, MonadTCEnv m) => m Telescope
-- getContextTerms :: (Applicative m, MonadTCEnv m) => m [Term]
getLocalVars :: (MonadTCM tcm, MonadFresh CompId tcm)
  => Cost -> tcm [Component]
getLocalVars cost = do
  contextTerms <- getContextTerms
  contextTypes <- map unDom . flattenTel <$> getContextTelescope
  unless (length contextTerms == length contextTypes)
         (mlog $ "WARNING: length mismatch in getLocalVars: " ++ prettyShow contextTerms ++ "; " ++ prettyShow contextTypes)
  zipWithM (newComponent [] cost noName) contextTerms contextTypes

prettyBranch :: SearchBranch -> SM String
prettyBranch branch = withBranchState branch $ do
    metas <- prettyTCM $ map goalMeta (sbGoals branch)
    metaId <- asks searchTopMeta
    inst <- getMetaInstantiation metaId
    instStr <- prettyTCM inst
    let compUses = pretty $ Map.toList $ sbComponentsUsed branch
    return $ render $ text "Branch{cost: " <> text (show $ sbCost branch) <> ", metas: " <> metas <> text " , instantiation: " <> pretty metaId <> text " = " <> instStr <> text ", used components: " <> compUses <> text "}"

-- instance Pretty ComponentCache where
--   pretty cache = keyValueList
--     [ ("ccLocalVars",  pretty $ map fst . snd <$> ccLocalVars cache)
--     , ("ccComponents", pretty $ map (mapSnd fst) . Map.toList . snd <$> ccComponents cache)
--     ]

instance Pretty Goal where
  pretty goal = keyValueList
    [ ("goalMeta", pretty $ goalMeta goal)
    , ("goalEnv", "[...]")
    ]

instance Pretty SearchBranch where
  pretty branch = keyValueList
    [ ("sbTCState", "[...]")
    , ("sbGoals", pretty $ sbGoals branch)
    , ("sbCost", pretty $ sbCost branch)
    , ("sbComponentsUsed", pretty $ sbComponentsUsed branch)
    ]

prettySearchStepResult :: SearchStepResult -> SM String
prettySearchStepResult = \case
  NoSolution -> return "No solution"
  OpenBranch branch -> ("Open branch: " ++) <$> prettyBranch branch
  ResultExpr expr -> ("Result expression: " ++) <$> showTCM expr



-- TODO: Is it possible to derive the pretty instances?
instance Pretty Components where
  pretty comps = cat
      [ f "hintFns" (hintFns comps)
      , f "hintDataTypes" (hintDataTypes comps)
      , f "hintRecordTypes" (hintRecordTypes comps)
      , f "hintAxioms" (hintAxioms comps)
      , f "hintLevel" (hintLevel comps)
      , f "hintWhere" (hintWhere comps)
      , f "hintProjections" (hintProjections comps)
      ]
    where
      f n [] = n <> ": []"
      f n xs = (n <> ":") $+$ nest 2 (pretty xs)

instance Pretty SearchOptions where
  pretty opts =
    "searchComponents:" $+$ nest 2 (pretty $ searchComponents opts) $+$
    keyValueList
      [ ("searchHintMode", pretty $ searchHintMode opts)
      , ("searchTimeout", pretty $ searchTimeout opts)
      , ("searchTopMeta", pretty $ searchTopMeta opts)
      , ("searchTopEnv", "[...]")
      ] $+$
      "searchCosts:" $+$ nest 2 (pretty $ searchCosts opts)

-- instance Pretty Goal where
--   pretty goal =
--     text "Goal" <> braces (prettyList_
--       [ text "goalMeta=" <> pretty (goalMeta goal)
--       , text "goalLocalVars=" <> pretty (goalLocalVars goal)
--       , text "goalLetVars=" <> pretty (goalLetVars goal)
--       ])


instance Pretty Component where
  pretty comp = haskellRecord "Component"
    [ ("compId", pretty $ compId comp)
    , ("compTerm", pretty $ compTerm comp)
    , ("compType", pretty $ compType comp)
    , ("compMetas", pretty $ compMetas comp)
    , ("compCost", pretty $ compCost comp)
    ]


instance Pretty Costs where
  pretty costs = align 20 entries
    where
      entries =
        [ ("costLocal:"         , pretty $ costLocal costs)
        , ("costFn:"            , pretty $ costFn costs)
        , ("costDataCon:"       , pretty $ costDataCon costs)
        , ("costRecordCon:"     , pretty $ costRecordCon costs)
        , ("costSpeculateProj:" , pretty $ costSpeculateProj costs)
        , ("costProj:"          , pretty $ costProj costs)
        , ("costAxiom:"         , pretty $ costAxiom costs)
        , ("costLet:"           , pretty $ costLet costs)
        , ("costLevel:"         , pretty $ costLevel costs)
        , ("costSet:"           , pretty $ costSet costs)
        , ("costRecCall:"       , pretty $ costRecCall costs)
        , ("costNewMeta:"       , pretty $ costNewMeta costs)
        , ("costNewHiddenMeta:" , pretty $ costNewHiddenMeta costs)
        , ("costCompReuse:"     , text "{function}")
        ]

instance PrettyTCM Component where
  prettyTCM comp = do
    term <- prettyTCM $ compTerm comp
    typ <- prettyTCM $ compType comp
    metas <- prettyTCM $ compMetas comp
    return $ pretty (compId comp) <+> "=" <+> term <+> ":" <+> typ <+> "with meta-variables" <+> metas


-- TODO: Not used but keep it around for debug printing
concatMapM :: Monad m => (a -> m [b]) -> [a] -> m [b]
concatMapM f = fmap concat . mapM f

-- TODO: Ask how they typically do it
reportDoc :: MonadDebug m => VerboseKey -> VerboseLevel -> Doc -> m ()
reportDoc vk vl d = reportSDoc vk vl (return d)

reportSMDoc :: VerboseKey -> VerboseLevel -> SM Doc -> SM ()
reportSMDoc vk vl md = md >>= reportDoc vk vl

encloseSep
    :: Doc   -- ^ left delimiter
    -> Doc   -- ^ right delimiter
    -> Doc   -- ^ separator
    -> [Doc] -- ^ input documents
    -> Doc
encloseSep l r s ds = case ds of
    []  -> l <> r
    [d] -> l <> d <> r
    _   -> cat (zipWith (<>) (l : repeat s) ds) <> r

haskellList :: [Doc] -> Doc
haskellList = encloseSep "[ " " ]" ", "

haskellRecord :: Doc -> [(Doc, Doc)] -> Doc
haskellRecord name fields = name <+> sepList " = " fields

keyValueList :: [(Doc, Doc)] -> Doc
keyValueList = sepList ": "

sepList :: Doc -> [(Doc, Doc)] -> Doc
sepList s values = encloseSep "{ " " }" ", " $ map (\(n, v) -> n <> s <> v) values
