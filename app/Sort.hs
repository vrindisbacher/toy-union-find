{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE BangPatterns #-}

module Sort where

import Expr (Expr (..))
import Data.HashMap.Strict
import Data.IORef
import Control.Monad.State
    ( MonadIO(liftIO), StateT, evalStateT, MonadState(put, get) )
import Union (UnifyKey (index, fromIndex), UnifyVal (unifyVals), UnificationTable, newKey, newUF, probe, unifyVarVar, unifyVarVal)

data Sort =
    SInt
    | SFloat
    | SFunc Sort Sort
    -- free type variable (e.g. one that must be unified)
    | SFVar Int
    deriving (Show, Eq)

-- hindley milner type checking

type TypeEnv = HashMap String Sort
type Subst = HashMap Int Sort

data CheckState = CheckState { checkCount :: IORef Int, env :: TypeEnv, subst :: Subst }

fresh :: CheckM Int
fresh = do
  state <- get
  let rn = checkCount state
  liftIO $ atomicModifyIORef' rn $ \n -> (n+1, n)

emptySubst :: Subst
emptySubst :: Subst = empty

type CheckM a = StateT CheckState IO a

typeCheckFun :: Sort -> CheckM (Sort, Sort)
typeCheckFun (SFunc t1 t2) = return (t1, t2)
typeCheckFun (SFVar i) = do
    x1 <- fresh
    x2 <- fresh
    let t1 = SFVar x1
    let t2 = SFVar x2
    state <- get
    put state { subst = insert i (SFunc t1 t2) (subst state) }
    return (t1, t2)
typeCheckFun _ = error "failed to check: not a function"

evalSort :: Sort -> CheckM Sort
evalSort (SFVar i) = do
    state <- get
    case Data.HashMap.Strict.lookup i (subst state) of
        Just s -> evalSort s
        Nothing -> return (SFVar i)
evalSort s = return s

apply :: Sort -> CheckM Sort
apply s = do
    state <- get
    case s of
        SFVar i -> case Data.HashMap.Strict.lookup i (subst state) of
            Just s' -> apply s'
            Nothing -> return s
        SFunc t1 t2 -> do
            t1' <- apply t1
            t2' <- apply t2
            return (SFunc t1' t2')
        _ -> return s

unifyVar :: Int -> Sort -> CheckM ()
unifyVar i t@(SFVar j) = do
    state <- get
    case Data.HashMap.Strict.lookup i (subst state) of
      Just t' -> if t == t' then return () else unifyVar j t'
      Nothing -> put state { subst = insert i t (subst state) }

unifyVar i t = do
    state <- get
    case Data.HashMap.Strict.lookup i (subst state) of
        Just (SFVar j) ->
            put state { subst = insert j t (insert i t (subst state)) }
        Just t'        -> if t == t' then return () else unify t t'
        Nothing        -> put state { subst = insert i t (subst state) }

unify :: Sort -> Sort -> CheckM ()
unify (SFVar i) t = unifyVar i t
unify t (SFVar i) = unifyVar i t
unify (SFunc sIn sOut) (SFunc sIn' sOut') = do
    unify sIn sIn'
    unify sOut sOut'
unify (SFunc sIn _) sArg = unify sIn sArg
unify s1 s2 = do
    state <- get
    s1' <- evalSort s1
    s2' <- evalSort s2
    case (s1', s2') of
        (SInt, SInt) -> return ()
        (SInt, SFVar i) -> put state { subst = insert i SInt (subst state) }
        (SFVar i, SInt) -> put state { subst = insert i SInt (subst state) }
        (SFloat, SFloat) -> return ()
        (SFVar i, SFloat) -> put state { subst = insert i SFloat (subst state) }
        (SFloat, SFVar i) -> put state { subst = insert i SFloat (subst state) }
        _ -> error ("Cannot unify " ++ show s1' ++ " and " ++ show s2')

typeCheckExpr :: Expr -> CheckM Sort
typeCheckExpr (EInt _) = return SInt
typeCheckExpr (EFloat _) = return SFloat
typeCheckExpr (EVar s) = do
    state <- get
    let env' = env state
    case Data.HashMap.Strict.lookup s env' of
        Just t -> return t
        Nothing -> error ("oops, var not found: " ++ show s)
typeCheckExpr (EBind s e1 e2) = do
    t <- typeCheckExpr e1
    state <- get
    put state { env = insert s t (env state) }
    typeCheckExpr e2
typeCheckExpr (ELam s body) = do
    xFun <- fresh
    let sFunc = SFVar xFun
    (sIn, sOut) <- typeCheckFun sFunc
    state <- get
    put state { env = insert s sIn (env state)}
    sBody <- typeCheckExpr body
    unify sBody sOut
    sIn' <- apply sIn
    sOut' <- apply sOut
    return (SFunc sIn' sOut')
typeCheckExpr (EApp f arg) = do
    sFunc <- typeCheckExpr f
    sArg <- typeCheckExpr arg
    case sFunc of
        SFunc sIn sOut -> do
            -- classic case
            unify sIn sArg
            apply sOut
        SFVar _ -> do
            -- the function is a variable and we need to figure out it's type
            (sIn, sOut) <- typeCheckFun sFunc
            unify sIn sArg
            apply sOut
        _ -> error ("Expected fun but got: " ++ show sFunc)
typeCheckExpr (EAdd e1 e2) = do
    s1 <- typeCheckExpr e1
    s2 <- typeCheckExpr e2
    unify s1 s2
    s1' <- apply s1
    s2' <- apply s2
    case (s1', s2') of
        (SInt, SInt) -> return SInt
        (SFloat, SFloat) -> return SFloat
        _ -> error ("Type error - expected int, int or float, float, get " ++ show s1' ++ ", " ++ show s2')

typeCheck :: Expr -> IO Sort
typeCheck e = do
    checkCountRef <- newIORef 0
    evalStateT (typeCheckExpr e) CheckState { checkCount = checkCountRef, env = empty, subst = emptySubst }

-- union find type checking

-- Sort that does not use free variables
data SortUF =
    SIntUF
    | SFloatUF
    | SFuncUF SortUF SortUF
    | SFVarUF SortVid
    deriving (Show, Eq)

-- define a type (SortVar ID) to use as keys in union find
newtype SortVid = SortVid Int deriving (Eq, Show)

instance UnifyKey SortVid where
    index (SortVid i) = i
    fromIndex = SortVid

-- define a type for Sorts to use as values in union find
newtype SortUFVal = SortUFVal (Maybe SortUF) deriving (Eq, Show)

instance UnifyVal SortUFVal where
    unifyVals :: SortUFVal -> SortUFVal -> SortUFVal
    unifyVals (SortUFVal Nothing) (SortUFVal Nothing) = SortUFVal Nothing
    unifyVals (SortUFVal Nothing) s@(SortUFVal (Just _)) = s
    unifyVals s@(SortUFVal (Just _)) (SortUFVal Nothing)  = s
    unifyVals s1@(SortUFVal (Just sLeft)) (SortUFVal (Just sRight)) = 
        if sLeft == sRight then s1 else error ("Failed to unify sorts: " ++ show sLeft ++ " and " ++ show sRight)

-- State for the checker
type TypeEnvUF = HashMap String SortUF

data CheckStateUF = CheckStateUF {
    envUF :: TypeEnvUF,
    sortUnif :: IORef (UnificationTable SortVid SortUFVal)
}

type CheckUFM a = StateT CheckStateUF IO a
type AppFTuple a b = UnificationTable a b -> (a, UnificationTable a b)
type AppFVal a b = UnificationTable a b -> b
type AppFTable a b = UnificationTable a b -> UnificationTable a b

applyUnionTuple :: (UnifyKey a, UnifyVal b) => AppFTuple a b -> IORef (UnificationTable a b) -> CheckUFM a
applyUnionTuple f rn = do
    let thing = atomicModifyIORef' rn (\u -> let (k, v) = f u in (v, k))
    liftIO thing

applyUnionVal :: (UnifyKey a, UnifyVal b) => AppFVal a b -> IORef (UnificationTable a b) -> CheckUFM b
applyUnionVal f rn = do
    let thing = atomicModifyIORef' rn (\u -> let v = f u in (u, v))
    liftIO thing

applyUnionTable :: (UnifyKey a, UnifyVal b) => AppFTable a b -> IORef (UnificationTable a b) -> CheckUFM ()
applyUnionTable f rn = do
    liftIO $ atomicModifyIORef' rn (\u -> let !v = f u in (v, ()))

resolveVars :: SortUF -> CheckUFM SortUF
resolveVars SIntUF = return SIntUF
resolveVars SFloatUF = return SFloatUF
resolveVars s@(SFVarUF k) = do
    state <- get
    let f = probe k
    currSort <- applyUnionVal f (sortUnif state)
    case currSort of
        SortUFVal (Just sort) -> resolveVars sort
        SortUFVal Nothing -> return s
resolveVars (SFuncUF s1 s2) = do
    s1' <- resolveVars s1
    s2' <- resolveVars s2
    return (SFuncUF s1' s2')

equate :: SortUF -> SortUF -> CheckUFM ()
equate (SFVarUF k1) (SFVarUF k2) = do
    state <- get
    let f = unifyVarVar k1 k2
    applyUnionTable f (sortUnif state)
equate s (SFVarUF k) = do
    state <- get
    s' <- resolveVars s
    let f = unifyVarVal k (SortUFVal (Just s'))
    applyUnionTable f (sortUnif state)
equate (SFVarUF k) s = do
    state <- get
    s' <- resolveVars s
    let f = unifyVarVal k (SortUFVal (Just s'))
    applyUnionTable f (sortUnif state)
equate SIntUF SIntUF = return ()
equate SFloatUF SFloatUF = return ()
equate (SFuncUF sIn1 sOut1) (SFuncUF sIn2 sOut2) = do
    sIn1' <- resolveVars sIn1
    sIn2' <- resolveVars sIn2
    equate sIn1' sIn2'
    sOut1' <- resolveVars sOut1
    sOut2' <- resolveVars sOut2
    equate sOut1' sOut2'
equate s1 s2 = error ("Type error. Cannot unify " ++ show s1 ++ " and " ++ show s2)



typeCheckExprUF :: Expr -> CheckUFM SortUF
typeCheckExprUF (EInt _) = return SIntUF
typeCheckExprUF (EFloat _) = return SFloatUF
typeCheckExprUF (EVar s) = do
    state <- get
    case Data.HashMap.Strict.lookup s (envUF state) of
        Just t -> resolveVars t
        Nothing -> error ("oops, var not found: " ++ show s)
typeCheckExprUF (EBind s e1 e2) = do
    s1 <- typeCheckExprUF e1
    state <- get
    put state { envUF = insert s s1 (envUF state) }
    s2 <- typeCheckExprUF e2 
    !_ <- resolveVars s1
    resolveVars s2
typeCheckExprUF (EAdd e1 e2) = do
    !s1 <- typeCheckExprUF e1
    !s2 <- typeCheckExprUF e2
    () <- equate s1 s2
    resolveVars s1
typeCheckExprUF (ELam s body) = do
    -- the function is a variable and we need to figure out it's type
    state <- get
    let f = newKey (SortUFVal Nothing) :: AppFTuple SortVid SortUFVal
    -- create input sort and bind it in the env
    sInArgExpected <- SFVarUF <$> applyUnionTuple f (sortUnif state)
    put state { envUF = insert s sInArgExpected (envUF state)}
    -- check the body
    sOutFound <- typeCheckExprUF body
    -- resolve vars for the the input
    sInFound <- resolveVars sInArgExpected
    return (SFuncUF sInFound sOutFound)
typeCheckExprUF (EApp func arg) = do
    sFunc <- typeCheckExprUF func 
    sArg <- typeCheckExprUF arg
    case sFunc of 
        SFuncUF sIn sOut -> do
            -- make sure sIn and sArg match
            () <- equate sIn sArg
            resolveVars sOut
        SFVarUF _ -> do
            -- the function is a var and we need to deduce it's type
            state <- get
            let f = newKey (SortUFVal Nothing) :: AppFTuple SortVid SortUFVal
            -- create input and output types
            sInExpected <- SFVarUF <$> applyUnionTuple f (sortUnif state) 
            sOutExpected <- SFVarUF <$> applyUnionTuple f (sortUnif state) 
            -- create a function type and try to equate it with the free variable
            let sFuncExpected = SFuncUF sInExpected sOutExpected
            () <- equate sFuncExpected sFunc

            () <- equate sInExpected sArg

            resolveVars sOutExpected
        _ -> error ("Expected function but got: " ++ show sFunc)

typeCheckUF :: Expr -> IO SortUF
typeCheckUF e = do
    ref <- newIORef newUF
    evalStateT (do typeCheckExprUF e) CheckStateUF { envUF = empty, sortUnif = ref }
    