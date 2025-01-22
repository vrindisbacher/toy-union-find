{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE InstanceSigs #-}

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
    unifyVals s1 s2 =
        case (s1, s2) of 
            (SortUFVal Nothing, SortUFVal Nothing) -> SortUFVal Nothing
            (SortUFVal (Just s), SortUFVal Nothing) -> SortUFVal (Just s)
            (SortUFVal Nothing, SortUFVal (Just s)) -> SortUFVal (Just s)
            (s1', s2') -> if s1' == s2' then
                    s1'
                else
                error ("Failed to equate sorts: " ++ show s1 ++ " and " ++ show s2)

-- State for the checker
type TypeEnvUF = HashMap String SortUF
-- type SubstUF = HashMap Int SortUF

data CheckStateUF = CheckStateUF {
    envUF :: TypeEnvUF,
    -- substUF :: Subst,
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
    let thing = atomicModifyIORef' rn (\u -> let v = f u in (v, ()))
    liftIO thing

resolveVars :: SortUF -> CheckUFM SortUF
resolveVars SIntUF = return SIntUF
resolveVars SFloatUF = return SFloatUF
-- ??
resolveVars (SFVarUF k) = do
    state <- get
    let f = probe k
    currSort <- applyUnionVal f (sortUnif state)
    case currSort of
        SortUFVal (Just sort) -> resolveVars sort
        SortUFVal Nothing ->  return (SFVarUF k)
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



typeCheckExprUF :: Expr -> SortUF -> CheckUFM SortUF
typeCheckExprUF (EInt _) expected = do
    expected' <- resolveVars expected
    () <- equate expected' SIntUF
    return SIntUF
    -- if expected' == SIntUF then
        -- return SIntUF
    -- else
        -- error ("Type error. Expected int but got: " ++ show expected')
typeCheckExprUF (EFloat _) expected = do
    expected' <- resolveVars expected
    () <- equate expected' SFloatUF
    return SFloatUF
    -- if expected' == SFloatUF then
    --     return SFloatUF
    -- else
    --     error ("Type error. Expected float but got: " ++ show expected')
typeCheckExprUF (EVar s) expected = do
    state <- get
    case Data.HashMap.Strict.lookup s (envUF state) of
        Just t -> do
            expected' <- resolveVars expected
            t' <- resolveVars t
            () <- equate expected' t'
            return expected'
            -- if expected' == t' then
                -- return expected'
            -- else
                -- error ("Type error. Expected " ++ show expected' ++ " but got " ++ show t')
        Nothing -> error ("oops, var not found: " ++ show s)
typeCheckExprUF (EBind s e1 e2) expected = do
    t <- typeCheckExprUF e1 expected
    state <- get
    put state { envUF = insert s t (envUF state) }
    found <- typeCheckExprUF e2 expected
    found' <- resolveVars found
    expected' <- resolveVars expected
    () <- equate found' expected'
    return expected'
    -- if found' == expected' then
        -- return expected'
    -- else
        -- error ("Type error. Expected " ++ show expected' ++ " but got " ++ show found')
typeCheckExprUF (EAdd e1 e2) expected = do
    state <- get
    -- new var
    let f = newKey (SortUFVal Nothing) :: UnificationTable SortVid SortUFVal -> (SortVid, UnificationTable SortVid SortUFVal)
    found <- SFVarUF <$> applyUnionTuple f (sortUnif state)
    -- type check e1 & e2
    s1 <- typeCheckExprUF e1 found
    s2 <- typeCheckExprUF e2 found
    s1' <- resolveVars s1
    s2' <- resolveVars s2
    expected' <- resolveVars expected
    found' <- resolveVars found
    () <- equate s1' s2'
    () <- equate s1' expected'
    () <- equate expected' found'
    return expected'
    -- if expected' == found' then
    --     return expected'
    -- else
    --     error ("Type error. Expected " ++ show expected' ++ " but got " ++ show found')
typeCheckExprUF (ELam s body) expected = do
    case expected of
        SFuncUF sIn sOut -> do
            state <- get
            put state { envUF = insert s sIn (envUF state)}
            found <- typeCheckExprUF body sOut
            found' <- resolveVars (SFuncUF sIn found)
            expected' <- resolveVars expected
            equate expected' found'
            return expected'
            -- if found' == expected' then
            --     return expected'
            -- else 
            --   error ("Type Error. Expected " ++ show expected' ++ " but got " ++ show found)
        s' -> error ("Type error. Expected function but got: " ++ show s')
typeCheckExprUF (EApp func arg) expected = do
    state <- get
    let f = newKey (SortUFVal Nothing) :: AppFTuple SortVid SortUFVal
    -- create input & ouput sort vars for the function
    sInArgExpected <- SFVarUF <$> applyUnionTuple f (sortUnif state)
    sOutBodyExpected <- SFVarUF <$> applyUnionTuple f (sortUnif state)
    -- type check func and arg
    sFuncExpected <- typeCheckExprUF func (SFuncUF sInArgExpected sOutBodyExpected)
    sArg <- typeCheckExprUF arg sInArgExpected
    -- resolve all type variables
    sFuncExpected' <- resolveVars sFuncExpected
    case sFuncExpected' of
        SFuncUF sIn sOut -> do
            -- sIn & sOut wshould be resolved by resolving the func type above
            sArg' <- resolveVars sArg
            expected' <- resolveVars expected
            () <- equate sIn sArg'
            () <- equate sOut expected'
            return expected'
            -- if sIn == sArg' then
            --     if sOut == expected' then
            --         return expected'
            --     else
            --         error ("Type error. Expected Func to have type " ++  show sFuncExpected' ++ " but got: " ++ show (SFuncUF sArg' expected'))
            -- else
            --     error ("Type error. Expected " ++ show expected' ++ " but got: " ++ show sArg)
        s' -> error ("Type error. Expected function but got: " ++ show s')

typeCheckUF :: Expr -> IO SortUF
typeCheckUF e = do
    let f = newKey (SortUFVal Nothing) :: AppFTuple SortVid SortUFVal
    ref <- newIORef newUF
    evalStateT (do
        state <- get
        expected <- SFVarUF <$> applyUnionTuple f (sortUnif state)
        typeCheckExprUF e expected) CheckStateUF { envUF = empty, sortUnif = ref }