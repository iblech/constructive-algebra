module Algebraic where

import Complex hiding (goldenRatio, sqrt2)
import qualified Complex

import Polynomial hiding (constant)
import Matrix hiding ((!!))
import Data.Array

data Algebraic = MkAlgebraic { number :: Complex, polynomial :: Poly Rational }

instance Eq   Algebraic where (==) = undefined

instance Show Algebraic where show = undefined

instance Num Algebraic where
    MkAlgebraic x p + MkAlgebraic x' p' =
	MkAlgebraic (x + x') (sumPolynomial p p')
    MkAlgebraic x p * MkAlgebraic x' p' =
	MkAlgebraic (x * x') (prodPolynomial p p')


    fromInteger i = MkAlgebraic (fromInteger i) (iX - fromInteger i)

    abs = undefined
    signum = undefined

-- müssen normiert sein
sumPolynomial :: (Num a) => Poly a -> Poly a -> Poly a
sumPolynomial f g = fromArray (charPoly . unsafeSquare) $ listArray ((0,0), (length indices - 1, length indices - 1)) elems
    where
    elems = [arr ij kl | ij <- indices, kl <- indices ]
    arr (i,j) (k,l) = arr1 (i,j) (k,l) + arr2 (i,j) (k,l)
    arr1 (i,j) (k,l)
	| i < n - 1 = if (k,l) == (i+1,j) then 1 else 0
	| otherwise = if l == j then -xs !! k else 0
    arr2 (i,j) (k,l)
	| j < m - 1 = if (k,l) == (i,j+1) then 1 else 0
	| otherwise = if k == i then -(ys !! l) else 0
    indices = [ (i,j) | i <- [0..n-1], j <- [0..m-1] ]
    (n,m)   = (length xs - 1, length ys - 1)
    (xs,ys) = (coeffs f, coeffs g)

-- müssen normiert sein
prodPolynomial :: (Num a) => Poly a -> Poly a -> Poly a
prodPolynomial f g = fromArray (charPoly . unsafeSquare) $ listArray ((0,0), (length indices - 1, length indices - 1)) elems
    where
    elems = [arr ij kl | ij <- indices, kl <- indices ]
    arr (i,j) (k,l)
	| i < n - 1  && j < m - 1
	= if (k,l) == (i+1,j+1) then 1 else 0
	| i == n - 1 && j < m - 1
	= if l == j + 1 then -xs !! k else 0
	| i < n - 1  && j == m - 1
	= if k == i + 1 then -ys !! l else 0
	| i == n - 1 && j == m - 1
	= xs !! k * ys !! l
    indices = [ (i,j) | i <- [0..n-1], j <- [0..m-1] ]
    (n,m)   = (length xs - 1, length ys - 1)
    (xs,ys) = (coeffs f, coeffs g)

goldenRatio :: Algebraic
goldenRatio = MkAlgebraic Complex.goldenRatio (iX^2 - iX - 1)

sqrt2 :: Algebraic
sqrt2 = MkAlgebraic Complex.sqrt2 (iX^2 - 2)

checkZero :: Algebraic -> Complex
checkZero (MkAlgebraic x f) = eval x $ fmap (constant . fromRational) f
