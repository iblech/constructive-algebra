module Algebraic where

import Debug.Trace

import Complex hiding (goldenRatio, sqrt2)
import qualified Complex
import NumericHelper
import Polynomial hiding (constant)
import Matrix hiding ((!!))
import Smith

import Data.Array

data Algebraic = MkAlgebraic { number :: Complex, polynomial :: Poly Rational }

instance Eq   Algebraic where x == y = unsafeRunR (isZero (x-y))

instance Show Algebraic where show = undefined

instance Num Algebraic where
    MkAlgebraic x p + MkAlgebraic x' p' = MkAlgebraic (x + x') (sumPolynomial p p')
    MkAlgebraic x p * MkAlgebraic x' p' = MkAlgebraic (x * x') (prodPolynomial p p')

    negate (MkAlgebraic x p) = MkAlgebraic (negate x) (MkPoly as)
	where
	as = reverse $ zipWith (*) (reverse $ coeffs p) (cycle [1,-1])

    fromInteger i = MkAlgebraic (fromInteger i) (iX - fromInteger i)

    abs = undefined
    signum = undefined

rec :: Algebraic -> Algebraic
rec (MkAlgebraic z p) = MkAlgebraic (recip z) (norm . MkPoly . reverse . coeffs $ p)
    where
    norm q = recip (leadingCoeff q) .* q

--instance Fractional Algebraic where
--    fromRational r = MkAlgebraic (constant $ fromRational r) (iX - fromRational r)
--    recip = error "recip"

-- müssen normiert sein
sumPolynomial :: (Fractional a) => Poly a -> Poly a -> Poly a
sumPolynomial f g = charPoly . fromArray $ listArray ((0,0), (length indices - 1, length indices - 1)) elems
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

prodPolynomial :: (Fractional a) => Poly a -> Poly a -> Poly a
prodPolynomial f g = charPoly . fromArray $ listArray ((0,0), (length indices - 1, length indices - 1)) elems
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

isZero :: Algebraic -> R Bool
isZero (MkAlgebraic x p) =
    if null bounds
	then return True
	else magnitudeZero (roundDownToRecipN (minimum bounds)) x
    where
    as     = coeffs p
    bs     = dropWhile (== 0) as
    k      = length bs
    bounds = zipWith f (tail bs) [1..]
	where
	f b j
	    | b == 0    = 17  --FIXME
	    | otherwise
	    = approxRoot j $ abs (head bs) / (fromIntegral k * abs b)
	approxRoot q a = rootSeq' q a 4

t x = trace (show x) x

verifyPolynomial :: Algebraic -> Complex
verifyPolynomial (MkAlgebraic x f) = eval x $ fmap (constant . fromRational) f

goldenRatio :: Algebraic
goldenRatio = MkAlgebraic Complex.goldenRatio (iX^2 - iX - 1)

sqrt2 :: Algebraic
sqrt2 = MkAlgebraic Complex.sqrt2 (iX^2 - 2)

exCheckZero i x = runR $ unComplex (verifyPolynomial x) i
