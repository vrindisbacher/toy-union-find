{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE AllowAmbiguousTypes #-}

module Union where

class (Eq a, Show a) => UnifyKey a where 
    index :: a -> Int
    fromIndex :: Int -> a

class (Eq b, Show b) => UnifyVal b where 
    unifyVals :: b -> b -> b

data (UnifyKey a, UnifyVal b) => VarValue a b = VarValue { parent :: a, value :: b, rank :: Int} deriving Show

newtype UnificationTable a b = UnificationTable { values :: [VarValue a b] } deriving Show

newUF :: (UnifyKey a, UnifyVal b) => UnificationTable a b
newUF = UnificationTable { values = [] }

newKey :: (UnifyKey a, UnifyVal b) => b -> UnificationTable a b -> (a, UnificationTable a b)
newKey val table =
    let key = fromIndex $ length (values table) in
    let var = VarValue { parent = key, value = val, rank = 0 } in
    (key, UnificationTable { values = values table ++ [var] })

find :: (UnifyKey a, UnifyVal b) => a -> UnificationTable a b -> VarValue a b
find x table = let rep = (values table !! index x) in 
        if parent rep == x then rep else find (parent rep) table

redirectRep :: (UnifyKey a, UnifyVal b) => 
    Int -> a -> a -> b -> UnificationTable a b -> UnificationTable a b
redirectRep newRank oldRootKey newRootKey newVal table = 
    -- update value for old root key parent to new root key
    let (hd, tl) = splitAt (index oldRootKey) (values table) in
    let old = head tl in 
    let newOld = VarValue { parent = newRootKey, value = value old, rank = rank old } in
    let vals = hd ++ (newOld : tail tl) in 
    let (hd', tl') = splitAt (index newRootKey) vals in 
    let valNew = head tl' in 
    let newNew = VarValue { parent = parent valNew, value = newVal, rank = newRank } in 
    UnificationTable { values = hd' ++ (newNew : tail tl') }

unifyReps :: (UnifyKey a, UnifyVal b) => 
    VarValue a b -> VarValue a b -> b -> UnificationTable a b -> UnificationTable a b
unifyReps x y newVal table = 
    let rank_x = rank x in
    let rank_y = rank y in 
    if rank_x > rank_y then 
        -- point b to a and set a to new
        redirectRep rank_x (parent x) (parent y) newVal table
    else if rank_x < rank_y then 
        redirectRep rank_y (parent x) (parent y) newVal table
    else 
        redirectRep (rank_x + 1) (parent x) (parent y) newVal table

unifyVarVar :: (UnifyKey a, UnifyVal b) => a -> a -> UnificationTable a b -> UnificationTable a b
unifyVarVar x y table = 
    let y_rep = find y table in 
    let x_rep = find x table in
    let combined = unifyVals (value y_rep) (value x_rep) in 
    unifyReps x_rep y_rep combined table

unifyVarVal :: (UnifyKey a, UnifyVal b) => a -> b -> UnificationTable a b -> UnificationTable a b
unifyVarVal k v table = 
    let k_rep = find k table in 
    let v' = unifyVals (value k_rep) v in 
    let (hd, tl) = splitAt (index (parent k_rep)) (values table) in
    let old = head tl in 
    let newVal = VarValue { parent = parent old, value = v', rank = rank old } in
    UnificationTable { values = hd ++ (newVal : tail tl) } 

probe :: (UnifyKey a, UnifyVal b) => a -> UnificationTable a b -> b
probe k table = 
    let k_rep = find k table in 
    value k_rep