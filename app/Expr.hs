module Expr where
import Data.HashMap.Strict
import Control.Monad.State

data Expr =
    EInt Int
    | EFloat Float
    | EVar String
    | EBind String Expr Expr
    | EApp Expr Expr
    | ELam String Expr
    | EAdd Expr Expr
    deriving (Show)

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

eval :: Expr -> IO Expr
eval e = evalStateT (evalExpr e) empty 