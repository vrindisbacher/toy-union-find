{-# LANGUAGE BangPatterns #-}
module Elab (testElab) where
import Data.HashMap.Strict (lookup, insert, HashMap, empty)
import Prelude hiding (lookup)
import Control.Monad.Reader (ReaderT (runReaderT), asks, MonadIO (liftIO))
import Data.IORef (IORef, atomicModifyIORef', readIORef)
import GHC.IORef (newIORef)
import GHC.IO (unsafePerformIO)

data Expr = EInt Int
          | EReal Float
          | EAdd Expr Expr
          | EVar String
          | ECst !Expr !Sort
          | ELam (String, Sort) Expr
          | EApp !Expr !Expr
          deriving (Show)

data Sort = FInt
          | FReal
          | FFunc Sort Sort
          | FVar Int
          | FApp  !Sort !Sort 
            deriving (Show)


testElab :: IO () 
testElab = do
    let e = EApp (ELam ("x", FVar 0) (EVar "x")) (EInt 1)
    chState <- ChS <$> newIORef 1 <*> newIORef new
    (e', s) <- runReaderT (elab empty e) chState
    finalUF <- readIORef (uf chState)
    let sFin = resolveTyVarSort finalUF s
    let eFin = resolveTyVarExpr finalUF e'
    print ("Elaboration. e is now: " ++ show eFin ++ " with type: " ++ show sFin)
    return ()

resolveTyVarSort :: UF -> Sort -> Sort 
resolveTyVarSort ufM (FVar i) = case find ufM i of
    Nothing -> error "TyVar not in uf"
    Just (_, s) -> s
resolveTyVarSort ufM (FFunc s1 s2) = FFunc (resolveTyVarSort ufM s1) (resolveTyVarSort ufM s2)
resolveTyVarSort ufM (FApp s1 s2) = FApp (resolveTyVarSort ufM s1) (resolveTyVarSort ufM s2)
resolveTyVarSort _ FInt = FInt
resolveTyVarSort _ FReal = FInt

resolveTyVarExpr :: UF -> Expr -> Expr 
resolveTyVarExpr _ e@(EInt _) = e
resolveTyVarExpr _ e@(EReal _) = e
resolveTyVarExpr ufM (EAdd e1 e2) = EAdd (resolveTyVarExpr ufM e1) (resolveTyVarExpr ufM e2)
resolveTyVarExpr _ e@(EVar _) = e
resolveTyVarExpr ufM (ECst e s) = ECst (resolveTyVarExpr ufM e) (resolveTyVarSort ufM s)
resolveTyVarExpr ufM (ELam (x, s) e) = ELam (x, resolveTyVarSort ufM s) (resolveTyVarExpr ufM e)
resolveTyVarExpr ufM (EApp e1 e2) = EApp (resolveTyVarExpr ufM e1) (resolveTyVarExpr ufM e2)

type ElabEnv = HashMap String Sort
data ChState = ChS { chCount :: IORef Int, uf :: IORef UF }
type CheckM = ReaderT ChState IO

fresh :: CheckM Int
fresh = do
  rn <- asks chCount
  liftIO $ atomicModifyIORef' rn $ \n -> (n+1, n)


checkFunSort :: Sort -> CheckM (Sort, Sort)
checkFunSort (FFunc t1 t2) = return (t1, t2)
checkFunSort (FVar i)      = do j <- fresh
                                k <- fresh
                                ufRef <- asks uf
                                _ <- liftIO $ atomicModifyIORef' ufRef $ \ufM -> (union ufM i (FFunc (FVar j) (FVar k)), ())
                                return (FVar j, FVar k)
checkFunSort _             = error "not a function"

elabAppSort :: ElabEnv -> Expr -> Expr -> Sort -> Sort -> CheckM (Expr, Expr, Sort, Sort, Sort)
elabAppSort _ e1 e2 s1 s2 = do
    (sIn, sOut) <- checkFunSort s1
    unify sIn s2
    return (e1, e2, s1, s2, sOut)

elabEApp  :: ElabEnv -> Expr -> Expr -> CheckM (Expr, Sort, Expr, Sort, Sort)
elabEApp f e1 e2 = do
  (e1', s1) <- elab f e1
  (e2', s2) <- elab f e2
  let !_ = unsafePerformIO $ print ("e1' " ++ show e1' ++ " s1: " ++ show s1 ++ " s2: " ++ show s2)
  (e1'', e2'', s1', s2', s) <- elabAppSort f e1' e2' s1 s2
  return (e1'', s1', e2'', s2', s)

dropECst :: Expr -> Expr
dropECst e = case e of
  ECst e' _ -> dropECst e'
  _         -> e

eCst :: Expr -> Sort -> Expr
eCst e = ECst (dropECst e)

eAppC :: Sort -> Expr -> Expr -> Expr
eAppC s e1 e2 = eCst (EApp e1 e2) s

elab :: ElabEnv -> Expr -> CheckM (Expr, Sort)
elab f (EApp e1 e2) = do
    (e1', s1, e2', s2, s) <- elabEApp f e1 e2
    let e = eAppC s (eCst e1' s1) (eCst e2' s2)
    return (e, s)

elab f (ECst e t) = do
  (e', _) <- elab f e
  return (eCst e' t, t)

elab _ e@(EInt _) = return (e, FInt)
elab _ e@(EReal _) = return (e, FReal)
elab f e@(EVar x) = do 
    case lookup x f of 
        Nothing -> error "Var doesn't exist"
        Just s -> return (e, s)
elab f (ELam (x, s) e) = do 
    (e', sOut) <- elab (insert x s f) e
    return (ELam (x, s) (eCst e' s), FFunc s sOut)
elab f (EAdd e1 e2)  = do 
    (e1', s1) <- elab f e1
    (e2', s2) <- elab f e2
    unify s1 s2
    return (EAdd (eCst e1' s1) (eCst e2' s2), s2)

unify :: Sort -> Sort -> CheckM ()
unify FInt FInt = return ()
unify FReal FReal = return ()
unify (FVar _) (FVar _) = return ()
unify (FVar i) s = do
    ufRef <- asks uf
    _ <- liftIO $ atomicModifyIORef' ufRef $ \ufM -> (union ufM i s, ())
    return ()
unify s (FVar i) = do
    ufRef <- asks uf
    _ <- liftIO $ atomicModifyIORef' ufRef $ \ufM -> (union ufM i s, ())
    return ()
unify (FApp s1 s2) (FApp s1' s2') = do
    unify s1 s1'
    unify s2 s2'
    return ()
unify _ _ = error "Cannot unify"

-- all the union find stuff

unifyUF :: Sort -> Sort -> Sort
unifyUF FInt FInt = FInt
unifyUF FReal FReal = FReal
unifyUF (FVar _) (FVar j) = FVar j
unifyUF (FVar _) s = s
unifyUF s (FVar _) = s
unifyUF (FApp s1 s2) (FApp s1' s2') = FApp (unifyUF s1 s1') (unifyUF s2 s2')
unifyUF _ _ = error "Cannot unify"

newtype UF = MkUF (HashMap Int Sort)

new :: UF
new = MkUF empty

union :: UF -> Int -> Sort -> UF -- one of the things being union-ed is a ty-var
union (MkUF ufM) tyv s =
    -- find the root for tyv 
    let tyv_root = find (MkUF ufM) tyv in
    case tyv_root of
            -- if tyv not in union find, insert
            Nothing -> MkUF (insert tyv s ufM)
            -- otherwise, unify the current sort with 
            -- the new one and insert that
            Just (i, s') ->
                let unified = unifyUF s s' in
                MkUF (insert i unified ufM)

find  :: UF -> Int -> Maybe (Int, Sort)
find (MkUF ufM) k = case lookup k ufM of
    Nothing -> Nothing
    Just s -> case s of
        FVar i -> case find (MkUF ufM) i of
            Nothing -> Just (k, FVar i)
            Just s' -> Just s'
        _ -> Just (k, s)



