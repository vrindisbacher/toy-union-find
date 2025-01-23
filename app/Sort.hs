{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE BangPatterns #-}

module Sort where

import Expr (Expr (..))
import Data.HashMap.Strict
import Data.IORef
import Control.Monad.State
    ( MonadIO(liftIO), StateT, evalStateT, MonadState(put, get) )
import Union 

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
    | SFVarUF Int
    deriving (Show, Eq)

-- define a type (SortVar ID) to use as keys in union find
-- newtype SortVid = SortVid Int deriving (Eq, Show)

-- instance UnifyKey SortVid where
--     index (SortVid i) = i
--     fromIndex = SortVid

-- define a type for Sorts to use as values in union find
-- newtype SortUFVal = SortUFVal (Maybe SortUF) deriving (Eq, Show)

-- instance UnifyVal SortUFVal where
--     unifyVals :: SortUFVal -> SortUFVal -> SortUFVal
--     unifyVals (SortUFVal Nothing) (SortUFVal Nothing) = SortUFVal Nothing
--     unifyVals (SortUFVal Nothing) s@(SortUFVal (Just _)) = s
--     unifyVals s@(SortUFVal (Just _)) (SortUFVal Nothing)  = s
--     unifyVals s1@(SortUFVal (Just sLeft)) (SortUFVal (Just sRight)) = 
--         if sLeft == sRight then s1 else error ("Failed to unify sorts: " ++ show sLeft ++ " and " ++ show sRight)


instance UFVal SortUF where 
    -- unifyUF :: b -> b -> b 
    unionVals SIntUF SIntUF = SIntUF
    unionVals SFloatUF SFloatUF = SFloatUF
    -- unifyUF (SFVarUF _) (SFVarUF j) = SFVarUF j
    unionVals (SFVarUF _) s = s
    unionVals s (SFVarUF _) = s
    unionVals (SFuncUF s1 s2) (SFuncUF s1' s2') = SFuncUF (unionVals s1 s1') (unionVals s2 s2')
    unionVals s1 s2 = error ("Cannot unify " ++ show s1 ++ " " ++ show s2)
    next s = case s of 
        SFVarUF i -> Just i 
        _ -> Nothing 

-- State for the checker
type TypeEnvUF = HashMap String SortUF

data CheckStateUF = CheckStateUF {
    chCount :: IORef Int,
    envUF :: TypeEnvUF,
    uf :: IORef (UF SortUF)
}

type CheckUFM a = StateT CheckStateUF IO a

freshSFVar :: CheckUFM Int
freshSFVar = do
  state <- get 
  let rn = chCount state
  liftIO $ atomicModifyIORef' rn $ \n -> (n+1, n)

unifyUF :: SortUF -> SortUF -> CheckUFM ()
unifyUF SIntUF SIntUF = return ()
unifyUF SFloatUF SFloatUF = return ()
unifyUF (SFVarUF _) (SFVarUF _) = return ()
unifyUF (SFVarUF i) s = do
    state <- get
    let ufRef = uf state
    _ <- liftIO $ atomicModifyIORef' ufRef $ \ufM -> (Union.union ufM i s, ())
    return ()
unifyUF s (SFVarUF i) = do
    state <- get
    let ufRef = uf state
    _ <- liftIO $ atomicModifyIORef' ufRef $ \ufM -> (Union.union ufM i s, ())
    return ()
unifyUF (SFuncUF s1 s2) (SFuncUF s1' s2') = do
    unifyUF s1 s1'
    unifyUF s2 s2'
    return ()
unifyUF s1 s2 = error ("Cannot unify " ++ show s1 ++ " " ++ show s2)


typeCheckExprUF :: Expr -> CheckUFM SortUF
typeCheckExprUF (EInt _) = return SIntUF
typeCheckExprUF (EFloat _) = return SFloatUF
typeCheckExprUF (EVar s) = do
    state <- get
    case Data.HashMap.Strict.lookup s (envUF state) of
        Just t -> return t
        Nothing -> error ("oops, var not found: " ++ show s)
typeCheckExprUF (EBind s e1 e2) = do
    s1 <- typeCheckExprUF e1
    state <- get
    put state { envUF = insert s s1 (envUF state) }
    typeCheckExprUF e2
typeCheckExprUF (EAdd e1 e2) = do
    !s1 <- typeCheckExprUF e1
    !s2 <- typeCheckExprUF e2
    unifyUF s1 s2
    return s2
typeCheckExprUF (ELam s body) = do
    state <- get
    -- create an input var
    svid <- freshSFVar
    let sIn = SFVarUF svid
    -- bind it in the state
    put state { envUF = insert s sIn (envUF state)}
    -- check the body
    sOut <- typeCheckExprUF body
    return (SFuncUF sIn sOut)
typeCheckExprUF (EApp func arg) = do
    sFunc <- typeCheckExprUF func 
    sArg <- typeCheckExprUF arg
    case sFunc of 
        SFuncUF sIn sOut -> do
            -- make sure sIn and sArg match
            unifyUF sIn sArg
            return sOut
        SFVarUF _ -> do
            -- the function is a var and we need to deduce it's type
            xIn <- freshSFVar
            xOut <- freshSFVar
            let sIn = SFVarUF xIn
            let sOut = SFVarUF xOut
            let sFuncFresh = SFuncUF sIn sOut
            unifyUF sFunc sFuncFresh
            unifyUF sIn sArg
            return sOut
        _ -> error ("Expected function but got: " ++ show sFunc)

resolveUF :: UF SortUF -> SortUF -> SortUF
resolveUF ufM (SFVarUF i) = case find ufM i of 
    Nothing -> error ("Fvar " ++ show i ++ " not in uf")
    Just (_, s) -> s
resolveUF ufM (SFuncUF s1 s2) = SFuncUF (resolveUF ufM s1) (resolveUF ufM s2)
resolveUF _ SIntUF = SIntUF
resolveUF _ SFloatUF = SFloatUF

typeCheckUF :: Expr -> IO SortUF
typeCheckUF e = do
    chCountRef <- newIORef 0
    ufRef <- newIORef new
    res <- evalStateT (do
        result <- typeCheckExprUF e
        state <- get
        return (result, state)
        ) CheckStateUF { envUF = empty, uf = ufRef, chCount = chCountRef }
    let (result, state) = res
    finalUF <- readIORef (uf state)
    return (resolveUF finalUF result)