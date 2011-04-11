{-# LANGUAGE FlexibleContexts #-}
module Smith where

import Matrix
import Data.Array
import Prelude hiding (gcd, (!!), (+), (*), (-), (/), negate)
import NumericHelper
import Polynomial
import Ring
import Field
import Euclidean
import Debug.Trace

makeZeroInFirstRow :: (EuclideanRing a, Eq a, TestableAssociatedness a) => Nat -> Matrix a -> Matrix a
makeZeroInFirstRow j mtx@(MkMatrix arr) = MkMatrix (arr // updates) `asTypeOf` mtx
    where
    (u,v,s,t) = gcd' (arr ! (0,0)) (arr ! (0,j))
    updates   = do
	i <- [0..n]
	let (x,y) = (arr ! (i,0), arr ! (i,j))
	[ ((i,0), u*x + v*y), ((i,j), s*y - t*x) ]
    ((0,0),(n,m)) = bounds arr

makeZeroInFirstCol :: (EuclideanRing a, Eq a, TestableAssociatedness a) => Nat -> Matrix a -> Matrix a
makeZeroInFirstCol i = transpose . makeZeroInFirstRow i . transpose

diagonalForm :: (EuclideanRing a, Eq a, TestableAssociatedness a) => Matrix a -> [a]
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
    badCols = [j | j <- [1..numCols mtx - 1], mtx !! (0,j) /= zero]
    badRows = [i | i <- [1..numRows mtx - 1], mtx !! (i,0) /= zero]
    mtx'    = deleteRow 0 . deleteColumn 0 $ mtx

{-
elementaryDivisors :: (EuclideanRing a) => Matrix a -> [a]
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

class (Ring a) => Determinantable a where
    determinant :: SqMatrix a -> a

instance (EuclideanRing a, Eq a, TestableAssociatedness a) => Determinantable (ER a) where
    determinant = detER

instance (Field a, Eq a, IntegralDomain a) => Determinantable (Poly a) where
    determinant = unER . determinant . fmap ER

detER :: (EuclideanRing a, Eq a, TestableAssociatedness a) => SqMatrix a -> a
detER mtx
    | numRows mtx == 0 = unit
    | null badCols     = (mtx !! (0,0)) * detER mtx'
    | otherwise        = detER $ makeZeroInFirstRow (head badCols) mtx
    where
    badCols = [j | j <- [1..numCols mtx - 1], mtx !! (0,j) /= zero]
    mtx'    = deleteRow 0 . deleteColumn 0 $ mtx

-- ist normiert.
charPoly :: (Ring a, Determinantable (Poly a)) => SqMatrix a -> Poly a
charPoly (MkMatrix arr) = determinant (fromArray arr')
    where
    arr' = accum (+) (fmap (negate . constant) arr) [((i,i), iX) | i <- [0..fst (snd (bounds arr))]]

exMatrix :: Matrix Rational
exMatrix = MkMatrix $ listArray ((0,0), (3,3)) [18, 12, 24, 42,  7, 9, 7, 3,  10, 12, 7, 10, 4, -6, 9, 10]

exMatrix2 :: Matrix Rational
exMatrix2 = MkMatrix $ listArray ((0,0), (3,3)) $ repeat 1 -- [1,1,1, 1,1,1, 1,1,1]

exMatrix3 :: Matrix Integer
exMatrix3 = MkMatrix $ listArray ((0,0), (3,3)) [18, 12, 24, 42,  7, 9, 7, 3,  10, 12, 7, 10, 4, -6, 9, 10]
