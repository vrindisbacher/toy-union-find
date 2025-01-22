module Union where

import qualified Control.Monad
import Data.HashMap.Strict hiding (union)
import Prelude hiding (lookup)

data UnificationTable a = UnificationTable { values :: [a], unifToIdxMap :: HashMap a Int }

class UnifyKey a where
    eq :: a -> a -> Bool
    unify :: a -> a -> a
    rank :: a -> Int

getIdx :: a -> HashMap a Int -> Int
getIdx val map = case lookup val map of 
    Nothing -> error ("Could not find val in idx map " ++ show val)
    Just idx -> idx

new :: UnifyKey a => UnificationTable a
new = UnificationTable { values = [], unifToIdxMap = empty }

newKey :: UnifyKey a => a -> UnificationTable a -> UnificationTable a
newKey value table =
    let idx = length (values table) in
    UnificationTable { values = values table ++ [value], unifToIdxMap = insert value idx (unifToIdxMap table) }

find :: UnifyKey a => a -> UnificationTable a -> a
find x table = let rep = values table !! (getIdx x (unifToIdxMap table))  in 
        if eq rep x then x else find rep table

union :: UnifyKey a  => a -> a -> UnificationTable a -> UnificationTable a
union x y table =
    let x_rep = find x table in
    let y_rep = find y table in
    if eq x_rep y_rep then table else
    let combined = unify x_rep y_rep in
    let x_rank = rank x_rep in
    let y_rank = rank y_rep in
    if x_rank > y_rank then
        -- y should point to x - and x should be combined
        let y_idx = getIdx y_rep (unifToIdxMap table) in
        let (first, scd) = splitAt y_idx (values table) in
        let new_values = first ++ (x_rep : tail scd) in
        let x_idx = getIdx x_rep (unifToIdxMap table) in
        let (first_x, scd_x) = splitAt x_idx new_values in
        UnificationTable { values = first_x ++ (combined : tail scd_x), unifToIdxMap = unifToIdxMap table }
    else
        -- x should point to y and y should be combined
        let x_idx = getIdx x_rep (unifToIdxMap table) in
        let (first, scd) = splitAt x_idx (values table) in
        let new_values = first ++ (y_rep : tail scd) in
        let y_idx = getIdx y_rep (unifToIdxMap table) in
        let (first_y, scd_y) = splitAt y_idx new_values in
        UnificationTable { values = first_x ++ (combined : tail scd_x), unifToIdxMap = unifToIdxMap table }

newtype TestKey = TestKey Int deriving (Eq, Show)

instance UnifyKey TestKey where
    eq (TestKey i) (TestKey j) = i == j
    unify (TestKey i) (TestKey j) = TestKey (min i j)
    rank (TestKey i) = i

testUnionFind :: IO ()
testUnionFind = do
    -- Test creating a new unification table
    let table = new :: UnificationTable TestKey
    Control.Monad.when (values table /= []) $ error "Test failed: new unification table should be empty"

    -- Test adding a new key to the table
    let table1 = newKey (TestKey 0) new
    Control.Monad.when (values table1 /= [TestKey 0]) $ error "Test failed: new key should be added to the table"

    -- Test finding the representative of a key
    let table2 = newKey (TestKey 0) new
    Control.Monad.when (find (TestKey 0) table2 /= TestKey 0) $ error "Test failed: should find the representative of the key"

    -- Test union of two keys
    let table3 = newKey (TestKey 0) $ newKey (TestKey 1) new
    let table4 = union (TestKey 0) (TestKey 1) table3
    Control.Monad.when (find (TestKey 0) table4 /= TestKey 0 || find (TestKey 1) table4 /= TestKey 0) $ error "Test failed: keys should be unioned"