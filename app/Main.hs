module Main where

import Expr (Expr (..), eval)
import Sort (typeCheck, typeCheckUF)

main :: IO ()
main = do
    -- let f1 = ELam "x" (EAdd (EVar "x") (EInt 3))
    -- let f2 = ELam "f" (EApp (EVar "f") (EInt 3))
    -- let e = EBind "f2" f2 (EApp (EVar "f2") f1)

    -- let body = EAdd (EVar "x") (EInt 3)
    -- let e = EApp (ELam "x" body) (EAdd (EInt 1) (EInt 2))

    let e = EAdd (EInt 2) (EInt 3)
    ty <- typeCheck e 
    print ("Hindley Milner: " ++ show ty)
    ty' <- typeCheckUF e
    print ("Union Find: " ++ show ty')
    expr <- eval e
    print expr
