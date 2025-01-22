{-# LANGUAGE BangPatterns #-}
module Main where

import Expr (Expr (..), eval)
import Union (testUnionFind)
import Sort (typeCheck)

main :: IO ()
main = do
    let !_ = testUnionFind 
    let f1 = ELam "x" (EAdd (EVar "x") (EInt 3))
    let f2 = ELam "f" (EApp (EVar "f") (EInt 3))
    let e = EBind "f2" f2 (EApp (EVar "f2") f1)
    -- let body = EAdd (EVar "x") (EFloat 3)
    -- let e = EApp (ELam "x" body) (EAdd (EInt 1) (EInt 2))
    ty <- typeCheck e 
    print ty
    expr <- eval e
    print expr
