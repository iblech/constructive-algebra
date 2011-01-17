module Smith where

import Matrix
import Data.Array
import TypeLevel
import Prelude hiding (gcd, (!!))
import NumericHelper

makeZeroInFirstRow :: (N n, N m, Euclidean a) => Nat -> Matrix n m a -> Matrix n m a
makeZeroInFirstRow j mtx@(MkMatrix arr) = MkMatrix (arr // updates) `asTypeOf` mtx
    where
    (u,v,s,t) = gcd (arr ! (0,0)) (arr ! (0,j))
    updates   = do
	i <- [0..n]
	let (x,y) = (arr ! (i,0), arr ! (i,j))
	[ ((i,0), u*x + v*y), ((i,j), -t*x + s*y) ]
    ((0,0),(n,m)) = bounds arr

makeZeroInFirstCol :: (N n, N m, Euclidean a) => Nat -> Matrix n m a -> Matrix n m a
makeZeroInFirstCol i = transpose . makeZeroInFirstRow i . transpose

smith :: (N n, N m, Euclidean a) => Matrix n m a -> [a]
smith mtx
    | numRows mtx == 0 || numCols mtx == 0
    = []
    | not (null badCols)
    = smith $ makeZeroInFirstRow (head badCols) mtx
    | not (null badRows)
    = smith $ makeZeroInFirstCol (head badRows) mtx
    | otherwise
    = unsafeNonTrivialDim mtx (\mtx' -> (mtx !! (0,0)) : smith (deleteRow 0 . deleteColumn 0 $ mtx'))
    where
    badCols = [j | j <- [1..numCols mtx - 1], mtx !! (0,j) /= 0]
    badRows = [i | i <- [1..numRows mtx - 1], mtx !! (i,0) /= 0]
    deleteTopLeft = deleteRow 0 . deleteColumn 0

exMatrix :: Matrix N4 N4 Integer
exMatrix = MkMatrix $ listArray ((0,0), (3,3)) [18, 12, 24, 42,  7, 9, 7, 3,  10, 12, 7, 10, 4, -6, 9, 10]
