{-# LANGUAGE EmptyCase #-}
module SimplerUnion (UF, new, union, find) where
import Data.HashMap.Strict (lookup, insert, HashMap, empty)
import Prelude hiding (lookup)
import Control.Monad.Reader (ReaderT, asks, MonadIO (liftIO))
import Data.IORef (IORef, atomicModifyIORef')

data Expr = EInt
          | EReal
          | EVar String
          | EApp !Expr !Expr
          | ECst !Expr !Sort

data Sort = FInt
          | FReal
          | FVar  !Int           -- type variable
          | FFunc !Sort !Sort    -- function type
          | FApp  !Sort !Sort    -- constructed type


type ElabEnv = String -> Sort
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

elab _ EInt = return (EInt, FInt)
elab _ EReal = return (EReal, FReal)
elab f e@(EVar s) = return (e, f s)


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
unify (FFunc s1 s2) (FFunc s1' s2') = do
    unify s1 s1'
    unify s2 s2'
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
unifyUF (FVar i) (FVar j) = FVar j
unifyUF (FVar i) s = s
unifyUF s (FVar i) = s
unifyUF (FFunc s1 s2) (FFunc s1' s2') = FFunc (unifyUF s1 s1') (unifyUF s2 s2')
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
    Nothing -> error "key not in UnionFind"
    Just s -> case s of
        FVar i -> case find (MkUF ufM) i of
            Nothing -> Just (k, FVar i)
            Just s' -> Just s'
        _ -> Just (k, s)



