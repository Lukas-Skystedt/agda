module Agda.Mimer.Mimer
  ( MimerResult(..)
  , mimer
  )
  where

import Data.Maybe (maybeToList)
import Control.Monad (forM, zipWithM, (>=>))
import Control.Monad.Except (catchError)
import qualified Data.Map as Map
import Data.List (sortOn, isSuffixOf)
import Data.Maybe (isJust)
import Data.Function (on)

import Agda.Auto.Convert (findClauseDeep)
import Agda.Interaction.Base
import Agda.Syntax.Common (InteractionId, MetaId, Arg(..), ArgInfo(..), defaultArgInfo, Origin(..),Induction(..), ConOrigin(..), Hiding(..))
import Agda.Syntax.Internal (MetaId, Type, Type''(..), Term(..), Dom'(..), Abs(..), Elim, Elim'(..), arity, ConHead(..), DataOrRecord(..), Args)
import Agda.Syntax.Position (Range)
import Agda.TypeChecking.Monad -- (MonadTCM, lookupInteractionId, getConstInfo, liftTCM, clScope, getMetaInfo, lookupMeta, MetaVariable(..), metaType, typeOfConst, getMetaType, MetaInfo(..), getMetaTypeInContext)
import Agda.Compiler.Backend (getMetaContextArgs, TCState(..), PostScopeState(..))
import Agda.TypeChecking.Monad.Base (TCM)
import Agda.TypeChecking.MetaVars (checkSubtypeIsEqual)
import Agda.TypeChecking.Conversion (equalType)
import Agda.TypeChecking.Pretty (prettyTCM, PrettyTCM(..))
import Agda.TypeChecking.Reduce (normalise)
import Agda.TypeChecking.CheckInternal (infer)
import Agda.TypeChecking.Substitute (piApply)
import Agda.TypeChecking.Substitute.Class (apply)
import Agda.TypeChecking.Telescope (piApplyM)
import Agda.TypeChecking.Constraints (noConstraints)
import Agda.Utils.Pretty (prettyShow, render)
import Agda.Utils.Permutation (idP)
import qualified Agda.Syntax.Scope.Base as Scope
import qualified Agda.TypeChecking.Monad.Base as TCM
import Agda.Syntax.Abstract.Name (QName(..))
import Agda.Interaction.BasicOps (typeOfMetaMI, contextOfMeta, )
import Agda.Interaction.Base (Rewrite(..))
import Agda.Utils.Impossible (__IMPOSSIBLE__)
import Agda.Utils.Maybe (catMaybes)

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
    -- The meta variable to solve
    metaI <- lookupInteractionId ii
    -- thisdefinfo <- findClauseDeep ii

    -- metaVar <- lookupMeta metaI
    -- metaTyp <- metaType metaI
    -- metaTyp'' <- getMetaType metaI
    -- outputConstraint <- typeOfMetaMI Normalised metaI
    -- let metaTyp' = case outputConstraint of
    --       OfType _namedMeta expr -> expr
    --       _ -> __IMPOSSIBLE__
    -- let metaInf = mvInfo metaVar
    -- let closure = miClosRange metaInf


    -- -- Lookup the type
    -- mrectyp <- do
    --   forM thisdefinfo $ \ (def, _, _) -> do
    --     normalise =<< do TCM.defType <$> getConstInfo def
    -- hints <- getEverythingInScope metaI
    -- let hintNames = map hintName hints
    -- hintTypes <- mapM typeOfConst hintNames

    -- -- unifiers <- map fst . filter snd . zip hintNames <$> mapM (unifyTypes metaTyp) hintTypes

    -- metaTyp''' <- getMetaTypeInContext metaI

    -- solutions <- map fst . filter snd . zip hintNames <$> mapM (dumbUnifier metaTyp''') hintTypes

    -- solutions' <- map fst . filter (isJust . snd) . zip hintNames <$> mapM (unifiesEq metaTyp''') hintTypes

    -- metaTypStr <- showTCM metaTyp'

    -- -- closureStr <- showTCM closure

    -- solutions'' <- search 2 metaI hints
    -- mlog $ show $ solutions''

    -- s <- experiment metaI >>= \case
    --     Just term -> showTCM term
    --     Nothing -> return "tt"
    s <- runDfs metaI >>= \case
      Just term -> showTCM term
      Nothing -> return "tt"

    -- runDfs metaI
    return $ MimerResult $ s
      -- "Result: " ++
      -- prettyShow unifiers ++
      -- "\n\nDef type: " ++
      -- prettyShow mrectyp ++
      -- "\n\nMeta type: " ++
      -- prettyShow metaTyp ++
      -- "\n\nMeta type': " ++
      -- metaTypStr ++
      -- "\n\nMeta type'': " ++
      -- prettyShow metaTyp'' ++
      -- "\n\nMeta type''': " ++
      -- prettyShow metaTyp''' ++
      -- "\n\nSolutions dumbUnifier: " ++ show (length solutions) ++ "/" ++ show (length hints) ++
      -- prettyShow solutions ++
      -- "\n\nSolutions unifiesEq: " ++ show (length solutions') ++ "/" ++ show (length hints) ++
      -- prettyShow solutions' ++
      -- -- "\n\nClosure: " ++
      -- -- closureStr ++
      -- "\n\n Components: " ++
      -- prettyShow (zip hintNames hintTypes)


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

-- TODO: withInteractionId to get the right context
runDfs :: MetaId -> TCM (Maybe Term)
runDfs metaId = lookupMeta metaId >>= \case
  Just (Right metaVar) -> do
    hintNames <- filter (not . ("test" `isSuffixOf`) . prettyShow) . map hintName <$> getEverythingInScope metaVar
    mlog $ "Using hints: " ++ prettyShow hintNames
    hints <- sortOn (arity . snd) . catMaybes <$> mapM qnameToTerm hintNames
    resTerm <- dfs hints 5 metaId

    metaVar' <- lookupMeta metaId
    case fmap mvInstantiation <$> metaVar' of
      Just (Right (InstV inst)) -> do
        mlog $ "instantiated to: " ++ prettyShow (instTel inst) ++ " " ++ prettyShow (instBody inst)
      _ -> return ()
    return resTerm
  -- Metavar lookup failed
  _ -> return Nothing

  where
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
-- TODO: Check if meta is already instantiated
dfs :: [(Term, Type)] -> Int -> MetaId -> TCM (Maybe Term)
dfs hints depth metaId
  | depth <= 0 = return Nothing
  | otherwise = go hints
  where
    go [] = return Nothing
    go ((hintTerm, hintType):hs) = do
      mTerm <- tryRefine hints depth metaId hintTerm hintType
      case mTerm of
        Just term -> return $ Just term
        Nothing -> go hs

tryRefine :: [(Term, Type)] -> Int -> MetaId -> Term -> Type -> TCM (Maybe Term)
tryRefine hints depth metaId hintTerm hintTyp = lookupMeta metaId >>= \case
  Just (Right metaVar) -> do
    metaType <- getMetaTypeInContext metaId
    metaArgs <- getMetaContextArgs metaVar
    go metaType metaArgs hintTerm hintTyp
  -- Metavar lookup failed
  _ -> return Nothing
  where
    go :: Type -> Args -> Term -> Type -> TCM (Maybe Term)
    go metaType metaArgs term typ = do
      mlog $ "Trying " ++ prettyShow term ++ " : " ++ prettyShow typ ++ " to solve meta of type " ++ prettyShow metaType
      dumbUnifier typ metaType >>= \case
        -- The hint is applicable
        True -> do
          assignV DirLeq metaId metaArgs term (AsTermsOf metaType)
          return $ Just term
        False -> case unEl typ of
          -- The hint may be applicable if we apply it to more metas
          -- TODO: Reduce the type
          Pi dom abs -> do
              oldState <- getTC -- TODO: Backtracking state
              -- TODO: check module Typechecking.Metavars
              let domainType = unDom dom
              let permutation = idP 0 -- length $ metaArgs
              -- TODO: for adding binders: addToContext
              metaInf' <- createMetaInfo
              let judgement = HasType () CmpLeq domainType
              metaId' <- newMeta Instantiable metaInf' lowMetaPriority permutation judgement
              -- TODO: This should be taken care of by some other function (newValueMeta)
              let metaTerm = MetaV metaId' [] -- TODO: apply to the context
              -- TODO: How should arg info be propagated?
              -- TODO: argFromDom
              -- setOrigin Inserted $ metaTerm <$ argFromDom dom
              let arg = Arg { argInfo = (domInfo dom){argInfoOrigin = Inserted}, unArg = metaTerm}
              newType <- piApplyM typ metaTerm
              let newTerm = apply term [arg]
              go metaType metaArgs newTerm newType >>= \case
                Nothing -> do
                  putTC oldState
                  return Nothing
                -- Refinement success using the new meta as an argument
                Just resTerm -> do
                  mSub <- dfs hints (depth - 1) metaId'
                  case mSub of
                    Just subTerm -> do
                      -- let newTerm' = apply term [ arg{unArg=subTerm} ]
                      -- assignV DirLeq metaId' metaArgs newTerm' (AsTermsOf metaType)
                      return $ Just resTerm
                    Nothing -> do
                      putTC oldState
                      return Nothing
          -- The hint is not applicable
          _ -> return Nothing
-- Termination checking:
-- Build call graph
-- Every cycle must have a "shrinking" arg


getEverythingInScope :: MetaVariable -> TCM [Hint]
getEverythingInScope metaVar = do
  let scope = clScope $ getMetaInfo metaVar
  let nameSpace = Scope.everythingInScope scope
      names = Scope.nsNames nameSpace
      qnames = map (Scope.anameName . head) $ Map.elems names
  return $ map (\qname -> Hint {isConstructor = False, hintName = qname}) qnames

  -- TODO: Look at getContextVars, locallyTC, getMetaScope


data SearchBranch = SearchBranch
  { sTCState   :: TCState
  , sOpenMetas :: [MetaId]
  , sHints     :: [Hint]
  }

data SearchSolution = SearchSolution { finalState :: TCState } deriving Show


search :: Int -> MetaId -> [Hint] -> TCM [SearchSolution]
search depth metaId hints = do
  mlog $ "Inital hints: " ++ show hints
  state <- getTC
  let startBranch = SearchBranch{sTCState = state, sOpenMetas = [metaId], sHints = hints}
  (_branches, solutions) <- stepN ([startBranch], [])
  putTC state
  return solutions
  where
    -- Perform 'stepSearch' depth number of times
    stepN :: ([SearchBranch], [SearchSolution]) -> TCM ([SearchBranch], [SearchSolution])
    stepN = foldl (>=>) return (replicate depth stepSearch)


stepSearch :: ([SearchBranch], [SearchSolution]) -> TCM ([SearchBranch], [SearchSolution])
stepSearch (branches, solutions) = do
  (branches', solutions') <- concatUnzip <$> mapM stepBranch branches
  return (branches', solutions ++ solutions')

stepBranch :: SearchBranch -> TCM ([SearchBranch], [SearchSolution])
stepBranch branch = do
  -- Save the state
  oldState <- getTC
  -- Load the state from the search branch
  putTC $ sTCState branch
  -- Take the first meta variable and refine it
  let (metaId:metaIds) = sOpenMetas branch
  let hints = sHints branch
  refined <- mapM (\hint -> refineWith hints hint metaId) hints
  -- Restore the old state
  putTC oldState
  let branches =  [br  | Branch br    <- refined]
  let solutions = [sol | Solution sol <- refined]
  -- Add the remaining meta variables back to the new branches
  let newBranches = map (\br -> br{sOpenMetas = sOpenMetas br ++ metaIds}) branches
  -- Are there remaining meta variables?
  case metaIds of
    -- No.
    [] -> return (newBranches, solutions)
    -- Yes. Construct search branches from the partial solutions
    _  -> do
      let moreBranches = map (\sol -> SearchBranch { sTCState = finalState sol, sOpenMetas = metaIds, sHints = hints}) solutions
      return (moreBranches ++ newBranches, [])


data RefineResult = Branch SearchBranch | Solution SearchSolution | BranchDead
-- For now, I always apply the maximum number of meta variables to a hint.
refineWith :: [Hint] -> Hint -> MetaId -> TCM RefineResult
refineWith hints hint metaId = do
    -- Backup the state
    oldState <- getTC
    -- Find the type a solution term should have to fill the hole.
    metaType <- getMetaTypeInContext metaId

    -- Get the type of the hint
    hintType <- typeOfConst (hintName hint)

    (hintTerm, newHintType, newMetaIds) <- applyToMetas (hintToTerm hint)  hintType

    dumbUnifier newHintType metaType >>= \case
      -- The types unify; the hint is applicable and a solution is found.
      True -> do
        -- Apply the meta variable to the hint
        -- applyMeta metaId hint
        -- TODO: What should the compare direction be here?
        let argInfo = defaultArgInfo{argInfoOrigin = Inserted} -- TODO: Arg info
        let arg = Arg {argInfo = argInfo, unArg = hintToTerm hint}
        -- TODO: CompareAs should probably be AsTermsOf instead of AsTypes
        let compareAs = AsTermsOf newHintType -- $ El { _getSort = undefined, unEl = newHintType }
        mlog $ "Before assignV:"
        mlog $ "  arg: " ++ prettyShow arg
        mlog $ "  arg: " ++ show arg
        mlog $ "  hintTerm: " ++ prettyShow hintTerm
        mlog $ "  newHintType: " ++ prettyShow newHintType
        assignV DirLeq metaId [arg] hintTerm compareAs
          `catchError` \err -> do
          mlog $ "  Caught error: " ++ show err
          return ()
        newState <- getTC
        -- Restore the old state
        putTC oldState
        case newMetaIds of
          [] -> return $ Solution $ SearchSolution { finalState = newState }
          _  -> return $ Branch   $ SearchBranch { sTCState = newState, sOpenMetas = newMetaIds, sHints = hints }
      -- The types do not unify; the hint is not applicable (without more arguments).
      False -> do
        -- Restore the old state
        putTC oldState
        return $ BranchDead

-- | Apply a 'Term' to new meta variables. For now, we give as many arguments as
-- possible.
applyToMetas :: Term -> Type -> TCM (Term, Type, [MetaId])
applyToMetas term termType = case arity termType of
  -- The term is already fully applied
  0 -> return (term, termType, [])
  -- The term can be applied to more arguments
  n -> do
    -- Create a new meta variable
    let domainType = getDomainType termType
    -- TODO: What is this permutation stuff?
    let permutation = idP 0
    let judgement = HasType () CmpLeq domainType
    metaInf <- createMetaInfo
    newMetaId <- newMeta Instantiable metaInf lowMetaPriority permutation judgement
    let meta = MetaV newMetaId []
    let argInfo = defaultArgInfo -- TODO: Arg info
    let arg = Arg {argInfo = argInfo, unArg = meta}
    -- Apply the term to the new meta variable. TODO: Is this the right application?
    let newTerm = apply term [arg]
    newTermType <- piApplyM termType meta
    -- Continue recursively
    (finalTerm, finalTermType, metas) <- applyToMetas newTerm newTermType
    return (finalTerm, finalTermType, metas ++ [newMetaId])




-- doSearch :: Int -> MetaId -> [Term] -> TCM [Term]
-- doSearch 0 _ _ = return []
-- doSearch depth metaId hints = do
--     -- Find the type a solution term should have to fill the hole.
--     metaType <- getMetaTypeInContext metaId

--     hintTypes <- mapM infer hints
--   -- TODO: there is also   typeArity :: Type -> TCM Nat
--     let hintArities = map arity hintTypes

--     -- Find applicable hints sorted by the number of arguments they require.
--     whichApply <- mapM (unifiesEq metaType) hintTypes
--     let applicableHints = sortOn snd $ [(hint, nrArgs) | (hint, Just nrArgs) <- zip hints whichApply]

--     solutions <- mapM (\(hint, nrArgs) -> refine (depth-1) nrArgs metaId hint hints) applicableHints

--     return $ concat solutions

-- refine :: Int  -- ^ Search depth
--        -> Int -- ^ Number of arguments left to apply
--        -> MetaId -- ^ The meta variable to refine
--        -> Term -- ^ The hint to use for refining
--        -> [Term] -- ^ All hints, used to continue search
--        -> TCM [Term]
-- refine depth nrArgs metaId hint hints = do
--   -- We mutate the state during search. When this search branch is done, the
--   -- state must be reset for the next search branch.
--   oldState <- getTC

--   metaType <- getMetaTypeInContext metaId

--   hintType <- infer hint

--   let hintDomainType = getDomainType hintType
--   -- TODO: What is this permutation stuff?
--   let permutation = idP 0
--   let judgement = HasType () CmpLeq hintDomainType
--   metaInf <- createMetaInfo
--   newMetaId <- newMeta Instantiable metaInf lowMetaPriority permutation judgement
--   piApply [Arg (error "No arg info available") (MetaV newMetaId [])]


--   isApplicable <- unifiesEq metaType hintType
--   if isApplicable
--     -- Hint is applicable
--     then undefined
--     -- Hint not applicable: Reset state and backtrack
--     else do
--       putTC oldState
--       return []

--   -- Is the refinement creating new meta variables?
--   case nrArgs of
--     -- No. Then we are done.
--     0 -> undefined -- Do the refining. Then done
--     -- Yes. Continue search recursively.
--     _ -> do
--       -- Apply the hint to a new meta variable
--       let newMetaId = undefined
--       -- Recursively find a solution to the new meta
--       solutions <- doSearch depth newMetaId hints
--       -- For each solution, continue search
--       solutions' <- mapM (\solution -> refine depth (nrArgs - 1) newMetaId solution hints) solutions

--       -- Restore the original state
--       putTC oldState
--       return $ concat solutions'


-- | @unifiesEq t1 t2@ gives @Just n$ if @t2@ applied to @n@ arguments equals
-- @t1$. During search, @t1@ is the target type and @t2@ the type of a
-- considered component.
-- TODO: use Agda.Utils.Functor.($>)
unifiesEq :: Type -> Type -> TCM (Maybe Int)
unifiesEq t1 t2 =
  -- If @t1@ and @t2@ are equal, return @Just 0@. Otherwise, we get an error
  -- which we catch..
  (equalType t2 t1 >> return (Just 0)) `catchError` \_ ->
  -- ..and continue:
  case unEl t2 of
    -- If @t2@ is a pi type, check its co-domain recursively, adding @1@ for the
    -- extra argument. Note that if the co-domain is dependent on the argument
    -- we will not find a solution since the argument will be a free variable (I
    -- think).
    Pi _dom abs -> fmap (+1) <$> unifiesEq t1 (unAbs abs)
    -- If @t2@ is not a pi type, we have no solution.
    _ -> return Nothing

dumbUnifier :: Type -> Type -> TCM Bool
dumbUnifier t1 t2 =
  (noConstraints $ equalType t2 t1 >> return True) `catchError` \_ -> return False


unifyTypes :: Type -> Type -> TCM Bool
unifyTypes typ1 typ2 = unifyTerms (unEl typ1) (unEl typ2) 


unifyTerms :: Term -> Term -> TCM Bool
unifyTerms l@(Var i1 elims1) (Var i2 elims2)
  = error $ "unimplemented: " ++ show l
unifyTerms l@(Lam argInfo1 abs1) (Lam argInfo2 abs2)
  = error $ "unimplemented: " ++ show l
unifyTerms l@(Lit lit1) (Lit lit2)
  = error $ "unimplemented: " ++ show l
unifyTerms l@(Def qname1 elims1) (Def qname2 elims2) = do
  elimsUnify <- and <$> zipWithM unifyElims elims1 elims2
  -- Obviously, we should not check names like this
  return $ qname1 == qname2 && elimsUnify
unifyTerms l@(Con conHead1 conInfo1 elims1) (Con conHead2 conInfo2 elims2)
  = error $ "unimplemented: " ++ show l
-- A pi type unifies if its domain and co-domain unify
unifyTerms l@(Pi dom1 abs1) (Pi dom2 abs2) = do
  domainsUnify <- unifyTypes (unDom dom1) (unDom dom2)
  absUnify <- unifyTypes (unAbs abs1) (unAbs abs2)
  return $ domainsUnify && absUnify
unifyTerms l@(Sort sort1) (Sort sort2)
  = return $ sort1 == sort2
unifyTerms l@(Level level1) (Level level2)
  = error $ "unimplemented: " ++ show l
unifyTerms l@(MetaV metaId1 elims1) (MetaV metaId2 elims2)
  = error $ "unimplemented: " ++ show l
unifyTerms l@(DontCare term1) (DontCare term2)
  = error $ "unimplemented: " ++ show l
unifyTerms l@(Dummy str1 elims1) (Dummy str2 elims2)
  = error $ "unimplemented: " ++ show l
unifyTerms _ _ = return False

unifyElims :: Elim -> Elim -> TCM Bool
unifyElims l@(Apply arg1) (Apply arg2) = unifyTerms (unArg arg1) (unArg arg2)
unifyElims l@(Proj projOrigin1 qname1) (Proj projOrigin qname) = error $ "unimplemented: " ++ show l
unifyElims l@(IApply x1 y1 r1) (IApply x2 y2 r2) = error $ "unimplemented: " ++ show l
unifyElims _ _ = return False

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
