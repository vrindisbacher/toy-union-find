{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE BangPatterns #-}

module Union (UF, new, find, union, UFVal(next, unionVals)) where
import Data.HashMap.Strict (lookup, insert, HashMap, empty)
import Prelude hiding (lookup)
import GHC.IO (unsafePerformIO)

newtype UF b = MkUF (HashMap Int b) deriving (Show)

class (Show b) => UFVal b where 
    unionVals :: b -> b -> b 
    next :: b -> Maybe Int

new :: UF b
new = MkUF empty

union :: (UFVal b) => UF b -> Int -> b -> UF b 
union (MkUF ufM) tyv s =
    -- find the root for tyv 
    let tyv_root = find (MkUF ufM) tyv in
    case tyv_root of
            -- if tyv not in union find, insert
            Nothing -> MkUF (insert tyv s ufM)
            -- otherwise, unify the current sort with 
            -- the new one and insert that
            Just (i, s') ->
                let unified = unionVals s s' in
                let !_ = unsafePerformIO $ print ("Unified for " ++ show i ++ ": " ++ show s ++ " and " ++ show s' ++ " is " ++ show unified) in
                MkUF (insert i unified ufM)

find  :: (UFVal b) => UF b -> Int -> Maybe (Int, b)
find (MkUF ufM) k = case lookup k ufM of
    Nothing -> Nothing
    Just s -> 
        case next s of 
            Nothing -> Just (k, s)
            Just i -> case find (MkUF ufM) i of 
                Nothing -> Just (k, s)
                s' -> s'