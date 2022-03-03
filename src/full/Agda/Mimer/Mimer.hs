module Agda.Mimer.Mimer
  ( MimerResult(..)
  , mimer
  )
  where

import Data.Maybe (maybeToList)
import Control.Monad (forM, zipWithM, (>=>), filterM)
import Control.Monad.Except (catchError)
import qualified Data.Map as Map
import Data.List (sortOn, isSuffixOf, intercalate)
import Data.Maybe (isJust)
import Data.Function (on)

import Agda.Auto.Convert (findClauseDeep)
import Agda.Compiler.Backend (getMetaContextArgs, TCState(..), PostScopeState(..), Open(..), isOpenMeta, getContextTerms)
import Agda.Interaction.Base
import Agda.Interaction.Base (Rewrite(..))
import Agda.Interaction.BasicOps (typeOfMetaMI, contextOfMeta )
import Agda.Interaction.Response (ResponseContextEntry(..))
import Agda.Syntax.Abstract (Expr)
import Agda.Syntax.Abstract.Name (QName(..))
import Agda.Syntax.Common (InteractionId, MetaId, Arg(..), ArgInfo(..), defaultArgInfo, Origin(..),Induction(..), ConOrigin(..), Hiding(..), setOrigin)
import Agda.Syntax.Internal (MetaId, Type, Type''(..), Term(..), Dom'(..), Abs(..), Elim, Elim'(..), arity
                            , ConHead(..), DataOrRecord(..), Args, argFromDom, Level'(..), PlusLevel'(..))
import Agda.Syntax.Position (Range)
import Agda.Syntax.Translation.InternalToAbstract (reify)
import Agda.TypeChecking.CheckInternal (infer)
import Agda.TypeChecking.Constraints (noConstraints)
import Agda.TypeChecking.Conversion (equalType)
import Agda.TypeChecking.Datatypes (isDataOrRecordType)
import Agda.TypeChecking.MetaVars (checkSubtypeIsEqual, newValueMeta)
import Agda.TypeChecking.Monad -- (MonadTCM, lookupInteractionId, getConstInfo, liftTCM, clScope, getMetaInfo, lookupMeta, MetaVariable(..), metaType, typeOfConst, getMetaType, MetaInfo(..), getMetaTypeInContext)
import Agda.TypeChecking.Monad.Base (TCM)
import Agda.TypeChecking.Pretty (prettyTCM, PrettyTCM(..))
import Agda.TypeChecking.Reduce (normalise, reduce)
import Agda.TypeChecking.Substitute (piApply, raise)
import Agda.TypeChecking.Substitute.Class (apply)
import Agda.TypeChecking.Telescope (piApplyM, flattenTel)
import Agda.Utils.Impossible (__IMPOSSIBLE__)
import Agda.Utils.Maybe (catMaybes)
import Agda.Utils.Permutation (idP)
import Agda.Utils.Pretty (prettyShow, render)
import qualified Agda.Syntax.Scope.Base as Scope
import qualified Agda.TypeChecking.Monad.Base as TCM

import Debug.Trace
import System.IO.Unsafe (unsafePerformIO)
import Control.Monad.IO.Class (liftIO)

newtype MimerResult = MimerResult String

data Hint = Hint { isConstructor :: Bool
                 , hintName :: QName }

instance Show Hint where
  show hint = "Hint { hintName: " ++ prettyShow (hintName hint) ++ ", isConstructor = " ++ show (isConstructor hint) ++ " }"


hintToTerm :: Hint -> Term
hintToTerm hint = undefined -- quoteName (hintName hint)

mimer :: MonadTCM tcm
  => InteractionId
  -> Range
  -> String
  -> tcm MimerResult
mimer ii range hint = liftTCM $ do
    oldState <- getTC
    -- The meta variable to solve
    -- metaI <- lookupInteractionId ii
    s <- runDfs ii >>= \case
      Just expr -> showTCM $ expr
      Nothing -> return ""

    openMetas <- getOpenMetas
    mlog $ "Remaining open metas: " ++ prettyShow openMetas
    putTC oldState
    return $ MimerResult $ s


-- ###################################################################### 
-- Next up: fix metas instantiated by unification. It is likely the cause of the
-- error in constant-data-with-Order


-- arg to try things in:
-- 1. Local variables (including let-bound)
-- 2. Data constructors
-- 3. Where clauses
-- 4. Lambda abstract
-- Other: Equality, empty type, record projections
-- - If we only use constructors if the target type is a data type, we might
--   generate η-reducible expressions, e.g. λ xs → _∷_ 0 xs


type TypedTerm = (Term, Type)
data Components = Component
  { hintLocalVar :: [TypedTerm]
  -- ^ Variables from LHS of function definition or lambda abstraction
  , hintLet :: [TypedTerm]
  -- ^ Variables bound in let
  , hintFn :: [TypedTerm]
  -- ^ A function
  , hintWhere :: [TypedTerm]
  -- ^ A definition in a where clause
  }


-- TODO: withInteractionId to get the right context
runDfs :: InteractionId -> TCM (Maybe Expr)
runDfs ii = withInteractionId ii $ do
  -- TODO: What normalization should we use here?
  -- TODO: The problem with `contextOfMeta` is that it gives `Expr`. However, it does include let-bindings.
  context <- contextOfMeta ii AsIs
  strs <- mapM (\entry -> showTCM (respType entry) >>= \s -> return $ prettyShow (respOrigName entry) ++ " : " ++ s) context
  mlog $ "contextOfMeta: " ++ intercalate ", " strs

  context' <- getContext
  mlog $ "getContext: " ++ prettyShow context'

  localVars <- getLocalVars
  mlog $ "getLocalVars: " ++ prettyShow localVars

  letVars <- Map.toAscList <$> asksTC envLetBindings
  mlog $ "let-bound vars: " ++ prettyShow letVars


  metaId <- lookupInteractionId ii
  metaVar <- lookupLocalMeta metaId
  metaArgs <- getMetaContextArgs metaVar
  mlog $ "getMetaContextArgs: " ++ prettyShow metaArgs


  hintNames <- filter (not . ("test" `isSuffixOf`) . prettyShow) . map hintName <$> getEverythingInScope metaVar
  hints <- sortOn (arity . snd) . catMaybes <$> mapM qnameToTerm hintNames
  let hints' = filter (\(d,_) -> case d of Def{} -> True; _ -> False) hints
  mlog $ "Using hints: " ++ prettyShow (map fst hints')
  resTerm <- dfs hints' 5 metaId

  mlog $ "dfs result term: " ++ prettyShow resTerm

  metaVar' <- lookupLocalMeta metaId
  case mvInstantiation metaVar' of
    InstV inst -> do
      termStr <- showTCM (instBody inst)
      mlog $ "instantiated to (showTCM):  " ++ termStr
      Just <$> reify (instBody inst)
    _ -> return Nothing

qnameToTerm :: QName -> TCM (Maybe (Term, Type))
qnameToTerm qname = do
  info <- getConstInfo qname
  typ <- typeOfConst qname
  let mTerm = case theDef info of
        Function{} -> Just $ Def qname []
        Datatype{} -> Just $ Def qname []
        Constructor{} -> Just $ Con ConHead{ conName = qname
                                    , conDataRecord = IsData
                                    , conInductive = Inductive
                                    , conFields = []}
                            ConOCon []
        _ -> Nothing

  return ((,typ) <$> mTerm)



-- TODO: Check how giveExpr (intercation basic ops) -- v' <- instantiate $ MetaV mi $ map Apply ctx
dfs :: [(Term, Type)] -> Int -> MetaId -> TCM (Maybe Term)
dfs hints depth metaId = do
  metaVar <- lookupLocalMeta metaId
  -- Check if meta is already instantiated
  case mvInstantiation metaVar of
    InstV inst -> do
      mlog $ "dfs: meta " ++ prettyShow metaId ++ " already instantiated to " ++ prettyShow (instBody inst)

      -- TODO: Sometimes unification generates new metas that we need to solve. What is a good way of finding them?
      openMetas <- getOpenMetas
      -- openMetas <- openMetasInTerm (instBody inst)
      case openMetas of
        -- No unsolved sub-metas
        [] -> return $ Just $ instBody inst
        (metaId':_) -> dfs hints depth metaId' >>= \case
          Nothing -> return Nothing
          Just{} -> dfs hints depth metaId
    -- Meta not instantiated, check if max depth is reached
    _ | depth <= 0 -> return Nothing
      -- Max depth not reached, continue search
      | otherwise -> do
          localVars <- getLocalVars
          go localVars
            `elseTry` tryDataCon hints depth metaId
            `elseTry` go hints
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
          _ -> return Nothing
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
      dumbUnifier typ metaType >>= \case
        -- The hint is applicable
        True -> do
          mlog $ "unifier succeeded. Assigning " ++ prettyShow term ++ " to " ++ prettyShow metaId
          assignV DirLeq metaId metaArgs term (AsTermsOf metaType)
          return $ Just term
        False -> case unEl typ of
          -- The hint may be applicable if we apply it to more metas
          Pi dom abs -> do
              putTC oldState -- TODO: Is this needed? (Reset the state in case dumbUnifier left some constraints.)
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

experiment :: MetaId -> TCM (Maybe Term)
experiment metaId = lookupMeta metaId >>= \case
  -- TODO: What are RemoteMetaVariables?
  Just (Right metaVar) -> do
    metaType <- getMetaTypeInContext metaId
    metaArgs <- getMetaContextArgs metaVar
    hints <- getEverythingInScope metaVar
    let qnames = map hintName hints
    mlog $ "getEverythingInScope: " ++ show hints
    mlog $ "  qnameNames: " ++ prettyShow (map qnameName qnames)
    let (ttName:_) = filter (("tt" `isSuffixOf`) . prettyShow) qnames
    let (topName:_) = filter (("⊤" `isSuffixOf`) . prettyShow) qnames
    let ttTerm = Con ConHead{conName=ttName,conDataRecord=IsData,conInductive=Inductive,conFields=[]} ConOCon [] -- quoteName ttName
    ttType <- typeOfConst ttName
    mlog $ "metaType: " ++ prettyShow metaType
    mlog $ "metaArgs: " ++ prettyShow metaArgs
    mlog $ "ttName: " ++ prettyShow ttName
    mlog $ "ttType: " ++ prettyShow ttType
    mlog $ "ttTerm: " ++ prettyShow ttTerm
    -- () <- equalType metaType ttType  `catchError` \err -> do
    --          errMsg <- showTCM err
    --          mlog $ "equalType gave error: " ++ errMsg
    -- mlog $ "equalType succeeded"
    let myArgInfo = defaultArgInfo{argInfoOrigin = Inserted}
    -- let arg = Arg {argInfo = myArgInfo, unArg = ttTerm}
    let compareAs = AsTermsOf metaType
    -- assignV DirLeq metaId metaArgs ttTerm compareAs



    let (idName:_) = filter (("id" `isSuffixOf`) . prettyShow) qnames
    meta2Inf <- createMetaInfo
    let permutation = idP 0
    let judgement = HasType () CmpLeq ttType
    meta2Id <- newMeta Instantiable meta2Inf lowMetaPriority permutation judgement
    let idTerm = Def idName [Apply Arg{argInfo=myArgInfo{argInfoHiding=Hidden}, unArg=MetaV meta2Id []}, Apply Arg{argInfo=myArgInfo, unArg=ttTerm}] -- id ? tt
    mlog $ "idTerm: " ++ prettyShow idTerm

    assignV DirLeq metaId metaArgs idTerm compareAs

    metaVar2 <- lookupMeta meta2Id
    case fmap mvInstantiation <$> metaVar2 of
      Just (Right (InstV inst)) -> do
        mlog $ "instantiated meta2 to: " ++ prettyShow (instTel inst) ++ " " ++ prettyShow (instBody inst)
      i -> do
        mlog $ "meta2 not instantiated: " ++ show i
        state <- stPostScopeState <$> getTC
        awakeStr <- unlines <$> mapM showTCM (stPostAwakeConstraints state)
        mlog $ "Awake constraints:" ++ awakeStr
        sleepStr <- unlines <$> mapM showTCM (stPostSleepingConstraints state)
        mlog $ "Sleeping constraints:" ++ sleepStr

    assignV DirLeq meta2Id metaArgs (Def topName []) compareAs

    metaVar' <- lookupMeta metaId
    case fmap mvInstantiation <$> metaVar' of
      Just (Right (InstV inst)) -> do
        let term = instBody inst
        mlog $ "instantiated to: " ++ prettyShow (instTel inst) ++ " " ++ prettyShow term
        return $ Just term
      _ -> return Nothing
  -- Meta variable lookup failed
  _ -> return Nothing

getEverythingInScope :: MetaVariable -> TCM [Hint]
getEverythingInScope metaVar = do
  let scope = clScope $ getMetaInfo metaVar
  let nameSpace = Scope.everythingInScope scope
      names = Scope.nsNames nameSpace
      qnames = map (Scope.anameName . head) $ Map.elems names
  mlog $ "getEverythingInScope, scope = " ++ prettyShow scope
  return $ map (\qname -> Hint {isConstructor = False, hintName = qname}) qnames

  -- TODO: Look at getContextVars, locallyTC, getMetaScope

dumbUnifier :: Type -> Type -> TCM Bool
dumbUnifier t1 t2 =
  (noConstraints $ equalType t2 t1 >> return True) `catchError` \err -> do
  str <- showTCM err
  mlog $ "dumbUnifier error: " ++ str
  return False

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
