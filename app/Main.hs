{-# LANGUAGE ScopedTypeVariables #-}
module Main where

import Data.HashMap.Strict
import Control.Monad.State hiding (state)
import Data.IORef

-- sorts
data Sort =
    SInt
    | SFloat
    | SFunc Sort Sort
    -- free type variable (e.g. one that must be unified)
    | SFVar Int
    deriving (Show, Eq)

-- expressions
data Expr =
    EInt Int
    | EFloat Float
    | EVar String
    | EBind String Expr Expr
    | EApp Expr Expr
    | ELam String Expr
    | EAdd Expr Expr
    deriving (Show)

-- type checking expressions - hindley milner

type TypeEnv = HashMap String Sort
type Subst = HashMap Int Sort

data CheckState = CheckState { checkCount :: IORef Int, env :: TypeEnv, subst :: Subst }

fresh :: CheckM Int
fresh = do
  state' <- get
  let rn = checkCount state'
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
    state' <- get
    let env' = env state'
    case Data.HashMap.Strict.lookup s env' of
        Just t -> return t
        Nothing -> error ("oops, var not found: " ++ show s)
typeCheckExpr (EBind s e1 e2) = do
    t <- typeCheckExpr e1
    state' <- get
    put state' { env = insert s t (env state') }
    typeCheckExpr e2
typeCheckExpr (ELam s body) = do
    xFun <- fresh 
    let sFunc = SFVar xFun
    (sIn, sOut) <- typeCheckFun sFunc
    state' <- get 
    put state' { env = insert s sIn (env state')}
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

-- type checking - union find

-- eval expr

type EvalEnv = HashMap String Expr
type ExprM = StateT EvalEnv IO Expr

evalExpr :: Expr -> ExprM
evalExpr e@(EInt _) = return e
evalExpr e@(EFloat _) = return e
evalExpr (EVar s) = do
    env' <- get
    case Data.HashMap.Strict.lookup s env' of
        Just e -> return e
        Nothing -> error "Oops that's a bad var"
evalExpr (EBind s e1 e2) = do
    eb' <- evalExpr e1
    env' <- get
    put $ insert s eb' env'
    evalExpr e2
evalExpr (ELam s e) = return (ELam s e)
evalExpr (EApp e1 e2) = do
    env' <- get
    arg' <- evalExpr e2
    case e1 of
        ELam s e1' -> do
            put $ insert s arg' env'
            evalExpr e1'
        EVar s ->
            case Data.HashMap.Strict.lookup s env' of
                Just (ELam s' e1') -> do
                    put $ insert s' arg' env'
                    evalExpr e1'
                _ -> error "Oops that's a bad app"
        _ -> error "Oops that's a bad app"
evalExpr (EAdd e1 e2) = do
    e1' <- evalExpr e1
    e2' <- evalExpr e2
    case (e1', e2') of
        (EInt i1, EInt i2) -> return (EInt (i1 + i2))
        (EFloat i1, EFloat i2) -> return (EFloat (i1 + i2))
        _ -> error ("Oops that's a bad add: " ++ show e1' ++ ", " ++ show e2')

main :: IO ()
main = do
    let f1 = ELam "x" (EAdd (EVar "x") (EInt 3))
    let f2 = ELam "f" (EApp (EVar "f") (EInt 3))
    let e = EBind "f2" f2 (EApp (EVar "f2") f1) 
    -- let body = EAdd (EVar "x") (EFloat 3)
    -- let e = EApp (ELam "x" body) (EAdd (EInt 1) (EInt 2))
    checkCountRef <- newIORef 0
    ty <- evalStateT (typeCheckExpr e) CheckState { checkCount = checkCountRef, env = empty, subst = emptySubst }
    print ty
    expr <- evalStateT (evalExpr e) empty
    print expr
