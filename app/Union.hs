{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE AllowAmbiguousTypes #-}

module Union (UF(MkUF), new, find, union, UFVal(next, unionVals)) where
import Data.HashMap.Strict (lookup, insert, HashMap, empty)
import Prelude hiding (lookup)

newtype UF b = MkUF (HashMap Int b) deriving (Show)

class (Show b) => UFVal b where 
    unionVals :: UF b -> Int -> b -> b -> UF b
    next :: b -> Maybe Int

new :: UF b
new = MkUF empty

union :: (UFVal b) => UF b -> Int -> b -> UF b 
union u@(MkUF ufM) tyv s =
    -- find the root for tyv 
    let tyv_root = find (MkUF ufM) tyv in
    case tyv_root of
            -- if tyv not in union find, insert
            Nothing -> MkUF (insert tyv s ufM)
            -- otherwise, unify the current sort with 
            -- the new one and insert that
            Just (i, s') -> unionVals u i s s'

find  :: (UFVal b) => UF b -> Int -> Maybe (Int, b)
find (MkUF ufM) k = do
    s <- lookup k ufM
    case next s of 
        Nothing -> Just (k, s)
        Just i -> find (MkUF ufM) i