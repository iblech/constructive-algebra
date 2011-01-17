module Smith where

import Matrix
import Data.Array
import TypeLevel
import Prelude hiding (gcd, (!!))
import NumericHelper
import Polynomial
import Debug.Trace

makeZeroInFirstRow :: (Euclidean a) => Nat -> Matrix a -> Matrix a
makeZeroInFirstRow j mtx@(MkMatrix arr) = MkMatrix (arr // updates) `asTypeOf` mtx
    where
    (u,v,s,t) = gcd (arr ! (0,0)) (arr ! (0,j))
    updates   = do
	i <- [0..n]
	let (x,y) = (arr ! (i,0), arr ! (i,j))
	[ ((i,0), u*x + v*y), ((i,j), -t*x + s*y) ]
    ((0,0),(n,m)) = bounds arr

makeZeroInFirstCol :: (Euclidean a) => Nat -> Matrix a -> Matrix a
makeZeroInFirstCol i = transpose . makeZeroInFirstRow i . transpose

diagonalForm :: (Euclidean a) => Matrix a -> [a]
diagonalForm mtx = dia mtx --trace (show $ elems . unMatrix $ mtx) $ dia mtx

dia mtx
    | numRows mtx == 0 || numCols mtx == 0
    = []
    | not (null badCols)
    = diagonalForm $ makeZeroInFirstRow (head badCols) mtx
    | not (null badRows)
    = diagonalForm $ makeZeroInFirstCol (head badRows) mtx
    | otherwise
    = mtx !! (0,0) : diagonalForm mtx'
    where
    badCols = [j | j <- [1..numCols mtx - 1], mtx !! (0,j) /= 0]
    badRows = [i | i <- [1..numRows mtx - 1], mtx !! (i,0) /= 0]
    mtx'    = deleteRow 0 . deleteColumn 0 $ mtx

{-
elementaryDivisors :: (Euclidean a) => Matrix a -> [a]
elementaryDivisors = fixDivisibility . diagonalForm
    where
    fixDivisibility as = go as
        where
        go []       = as
        go [a]      = as
        go (a:b:bs)
    fixDivisibility (a:as) =
        where
        d = foldl gcd' a as
        gcd' x y = let (u,v,s,t) = gcd x y in u*x + v*y

smith' :: (Fractional a) => SqMatrix a -> [Poly a]
smith' (MkMatrix arr) = elementaryDivisors (fromArray arr')
    where
    arr' = accum (+) (fmap (negate . constant) arr) [((i,i), iX) | i <- [0..fst (snd (bounds arr))]]
-}

determinant :: (Euclidean a) => SqMatrix a -> a
determinant = product . diagonalForm

-- XXX: Vor. abschwächen!
charPoly :: (Fractional a) => SqMatrix a -> Poly a
charPoly (MkMatrix arr) = determinant (fromArray arr')
    where
    arr' = accum (+) (fmap (negate . constant) arr) [((i,i), iX) | i <- [0..fst (snd (bounds arr))]]

exMatrix :: Matrix Rational
exMatrix = MkMatrix $ listArray ((0,0), (3,3)) [18, 12, 24, 42,  7, 9, 7, 3,  10, 12, 7, 10, 4, -6, 9, 10]

exMatrix2 :: Matrix Rational
exMatrix2 = MkMatrix $ listArray ((0,0), (3,3)) $ repeat 1 -- [1,1,1, 1,1,1, 1,1,1]
