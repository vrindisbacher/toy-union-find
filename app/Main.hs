module Main where

import Elab (testElab)
import Expr (Expr (..))
import Sort (typeCheck, typeCheckUF, Sort)

check :: Expr -> IO (Sort, Sort)
check e = do
    s <- typeCheck e 
    s' <- typeCheckUF e
    return (s, s')

main :: IO ()
main = do
    testElab
    -- let f1 = ELam "x" (EAdd (EVar "x") (EInt 3))
    -- let f2 = ELam "f" (EApp (EVar "f") (EInt 3))
    -- let e1 = EBind "f2" f2 (EApp (EVar "f2") f1)
    -- res1 <- check e1
    -- print res1

    let body = EAdd (EVar "x") (EInt 3)
    let e2 = EApp (ELam "x" body) (EAdd (EInt 1) (EInt 2))
    res2 <- check e2
    print res2

    let e3 = EBind "x" (EInt 3) (EAdd (EVar "x") (EInt 3))
    res3 <- check e3
    print res3

    let body' = EAdd (EVar "x") (EFloat 3)
    let e4 = EApp (ELam "x" body') (EAdd (EFloat 1) (EFloat 2))
    res4 <- check e4
    print res4