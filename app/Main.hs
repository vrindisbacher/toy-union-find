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
    let f1 = ELam "x" (EAdd (EVar "x") (EInt 3))
    let f2 = ELam "f" (EApp (EVar "f") (EInt 3))
    let e1 = EApp f2 f1
    res1 <- check e1
    print res1

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

    let f1' = ELam "x" (EAdd (EVar "x") (EInt 1))
    let f2' = ELam "f" (ELam "x" (EApp (EVar "f") (EVar "x")))
    let e1' = EApp f2' f1'
    res5 <- check e1'
    print res5

    let nestedLambdaTest = EApp 
            (ELam "f" 
                (ELam "x" 
                    (EAdd 
                        (EApp (EVar "f") (EFloat 1.0))
                        (EVar "x"))))
            (ELam "y" (EAdd (EVar "y") (EFloat 2.0)))

    let bindChainTest = EBind "x" (EFloat 1.0)
            (EBind "y" (EAdd (EVar "x") (EFloat 2.0))
                (EBind "z" (EAdd (EVar "y") (EFloat 3.0))
                    (EAdd (EVar "x") (EVar "z"))))

    let higherOrderTest = EApp
            (ELam "f"
                (EApp 
                    (EVar "f")
                    (EAdd (EFloat 1.0) (EFloat 2.0))))
            (ELam "x" 
                (EAdd (EVar "x") (EFloat 3.0)))

    let lambdaChainTest = EApp
            (EApp
                (ELam "f"
                    (ELam "g"
                        (ELam "x"
                            (EAdd
                                (EApp (EVar "f") (EVar "x"))
                                (EApp (EVar "g") (EVar "x"))))))
                (ELam "y" (EAdd (EVar "y") (EFloat 1.0))))
            (ELam "z" (EAdd (EVar "z") (EFloat 2.0)))

    let mixedTypesTest = EBind "x" (EInt 5)
            (EBind "y" (EFloat 2.5)
                (EApp
                    (ELam "z" 
                        (EAdd 
                            (EAdd (EVar "z") (EVar "x"))
                            (EVar "y")))
                    (EFloat 1.5)))

    -- Test expressions
    res6 <- check nestedLambdaTest
    print res6
    res7 <- check bindChainTest
    print res7
    res8 <- check higherOrderTest
    print res8
    res9 <- check lambdaChainTest
    print res9
    res10 <- check mixedTypesTest
    print res10

    -- (
    --     SFunc 
    --         (SFunc SInt (SFunc (SFVar 4) (SFVar 5)))
    --         (SFunc (SFVar 4) (SFVar 5))
    --     SFunc 
    --         (SFunc SInt (SFunc (SFVar 4) (SFVar 5)))
    --         (SFunc (SFVar 1) (SFVar 5))
    -- )