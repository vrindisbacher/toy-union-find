{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE InstanceSigs #-}

module Sort where

import Expr (Expr (..))
import Data.HashMap.Strict
import Data.IORef
import Control.Monad.State
    ( MonadIO(liftIO), StateT, evalStateT, MonadState(put, get) )
import Union (UF (MkUF), union, find, UFVal (unionVals, next))
import qualified Union

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
        Just (SFVar j) -> put state { subst = insert j t (insert i t (subst state)) }
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

unionFuncArgs :: UF Sort -> Int -> Sort -> Sort -> UF Sort 
unionFuncArgs u i s1 s2 = case (s1 , s2) of 
    (SFVar i1, _) -> Union.union u i1 s2
    (_, SFVar i2) -> Union.union u i2 s1
    (_, _) -> unionVals u i s1 s2

instance UFVal Sort where
    unionVals :: UF Sort -> Int -> Sort -> Sort -> UF Sort
    unionVals ufM _ SInt SInt = ufM
    unionVals ufM _ SFloat SFloat = ufM
    unionVals (MkUF ufM) i (SFVar _) s = MkUF (insert i s ufM)
    unionVals (MkUF ufM) i s (SFVar _) = MkUF (insert i s ufM)
    unionVals u i (SFunc s1 s2) (SFunc s1' s2') = 
        let u' = unionFuncArgs u i s1 s1' in 
            unionFuncArgs u' i s2 s2'
    unionVals _ _ s1 s2 = error ("Cannot unify " ++ show s1 ++ " " ++ show s2)
    next s = case s of
        SFVar i -> Just i
        _ -> Nothing

-- State for the checker
type TypeEnvUF = HashMap String Sort

data CheckStateUF = CheckStateUF {
    chCount :: IORef Int,
    envUF :: TypeEnvUF,
    uf :: IORef (UF Sort)
}

type CheckUFM a = StateT CheckStateUF IO a

freshSFVar :: CheckUFM Int
freshSFVar = do
  state <- get
  let rn = chCount state
  liftIO $ atomicModifyIORef' rn $ \n -> (n+1, n)

unifyUF :: Sort -> Sort -> CheckUFM ()
unifyUF SInt SInt = return ()
unifyUF SFloat SFloat = return ()
unifyUF (SFVar i) (SFVar j) = do
    state <- get
    let ufRef = uf state
    liftIO $ atomicModifyIORef' ufRef $ \ufM -> (Union.union ufM i (SFVar j), ())
    return ()
unifyUF (SFVar i) s = do
    state <- get
    let ufRef = uf state
    liftIO $ atomicModifyIORef' ufRef $ \ufM -> (Union.union ufM i s, ())
    return ()
unifyUF s (SFVar i) = do
    state <- get
    let ufRef = uf state
    liftIO $ atomicModifyIORef' ufRef $ \ufM -> (Union.union ufM i s, ())
    return ()
unifyUF (SFunc s1 s2) (SFunc s1' s2') = do
    unifyUF s1 s1'
    unifyUF s2 s2'
    return ()
unifyUF s1 s2 = error ("Cannot unify " ++ show s1 ++ " " ++ show s2)


typeCheckExprUF :: Expr -> CheckUFM Sort
typeCheckExprUF (EInt _) = return SInt
typeCheckExprUF (EFloat _) = return SFloat
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
    let sIn = SFVar svid
    -- bind it in the state
    put state { envUF = insert s sIn (envUF state)}
    -- check the body
    sOut <- typeCheckExprUF body
    return (SFunc sIn sOut)
typeCheckExprUF (EApp func arg) = do
    sFunc <- typeCheckExprUF func
    sArg <- typeCheckExprUF arg
    case sFunc of
        SFunc sIn sOut -> do
            -- make sure sIn and sArg match
            unifyUF sIn sArg
            return sOut
        SFVar _ -> do
            -- the function is a var and we need to infer its type
            xIn <- freshSFVar
            xOut <- freshSFVar
            let sIn = SFVar xIn
            let sOut = SFVar xOut
            let sFuncFresh = SFunc sIn sOut
            unifyUF sFunc sFuncFresh
            unifyUF sIn sArg
            return sOut
        _ -> error ("Expected function but got: " ++ show sFunc)

resolveUF :: UF Sort -> Sort -> Sort
resolveUF ufM ty@(SFVar i) = case find ufM i of
    Nothing -> ty
    Just (_, s) -> resolveUF ufM s
resolveUF ufM (SFunc s1 s2) = SFunc (resolveUF ufM s1) (resolveUF ufM s2)
resolveUF _ SInt = SInt
resolveUF _ SFloat = SFloat

typeCheckUF :: Expr -> IO Sort
typeCheckUF e = do
    chCountRef <- newIORef 0
    ufRef <- newIORef Union.new
    res <- evalStateT (do
        result <- typeCheckExprUF e
        state <- get
        return (result, state)
        ) CheckStateUF { envUF = empty, uf = ufRef, chCount = chCountRef }
    let (result, state) = res
    finalUF <- readIORef (uf state)
    return (resolveUF finalUF result)