module IntegralClosure where

import Debug.Trace

import Prelude hiding (fromInteger, (+), (*), (-), (^), negate)
import Complex hiding (goldenRatio, sqrt2)
import qualified Complex
import NumericHelper
import Polynomial hiding (constant)
import Matrix hiding ((!!))
import Ring
import Field
import Smith

import Data.Array

data IC a b = MkIC { number :: b, polynomial :: Poly a }

instance (Field a, Eq a, IntegralDomain a, Ring b) => Ring (IC a b) where
    MkIC x p + MkIC x' p' = MkIC (x + x') (sumPolynomial p p')
    MkIC x p * MkIC x' p' = MkIC (x * x') (prodPolynomial p p')

    negate (MkIC x p) = MkIC (negate x) (MkPoly as)
	where
	as = reverse $ zipWith (*) (reverse $ coeffs p) (cycle [unit,negate unit])

    fromInteger i = MkIC (fromInteger i) (iX - fromInteger i)

    zero = fromInteger zero
    unit = fromInteger unit

-- Voraussetzung: Polynome müssen normiert sein
sumPolynomial :: (IntegralDomain a, Field a, Eq a) => Poly a -> Poly a -> Poly a
sumPolynomial f g = charPoly . fromArray $ listArray ((0,0), (length indices - 1, length indices - 1)) elems
    where
    elems = [arr ij kl | ij <- indices, kl <- indices ]
    arr (i,j) (k,l) = arr1 (i,j) (k,l) + arr2 (i,j) (k,l)
    arr1 (i,j) (k,l)
	| i < n - 1 = if (k,l) == (i+1,j) then unit else zero
	| otherwise = if l == j then negate (xs !! k) else zero
    arr2 (i,j) (k,l)
	| j < m - 1 = if (k,l) == (i,j+1) then unit else zero
	| otherwise = if k == i then negate (ys !! l) else zero
    indices = [ (i,j) | i <- [0..n-1], j <- [0..m-1] ]
    (n,m)   = (length xs - 1, length ys - 1)
    (xs,ys) = (coeffs f, coeffs g)

-- Voraussetzung: Polynome müssen normiert sein
prodPolynomial :: (IntegralDomain a, Field a, Eq a) => Poly a -> Poly a -> Poly a
prodPolynomial f g = charPoly . fromArray $ listArray ((0,0), (length indices - 1, length indices - 1)) elems
    where
    elems = [arr ij kl | ij <- indices, kl <- indices ]
    arr (i,j) (k,l)
	| i < n - 1  && j < m - 1
	= if (k,l) == (i+1,j+1) then unit else zero
	| i == n - 1 && j < m - 1
	= if l == j + 1 then negate (xs !! k) else zero
	| i < n - 1  && j == m - 1
	= if k == i + 1 then negate (ys !! l) else zero
	| i == n - 1 && j == m - 1
	= xs !! k * ys !! l
    indices = [ (i,j) | i <- [0..n-1], j <- [0..m-1] ]
    (n,m)   = (length xs - 1, length ys - 1)
    (xs,ys) = (coeffs f, coeffs g)


goldenRatio :: IC Rational Complex
goldenRatio = MkIC Complex.goldenRatio (iX^2 - iX - unit)

sqrt2 :: IC Rational Complex
sqrt2 = MkIC Complex.sqrt2 (iX^2 - fromInteger 2)
{-

isZero :: IC -> R Bool
isZero (MkIC x p) =
    if null bounds
	then return True
	else trace ((":: " ++) . show $ roundDownToRecipN (minimum bounds)) $ magnitudeZero (roundDownToRecipN (minimum bounds)) x
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

verifyPolynomial :: IC -> Complex
verifyPolynomial (MkIC x f) = eval x $ fmap (constant . fromRational) f

exCheckZero i x = runR $ unComplex (verifyPolynomial x) i



rec :: IC -> IC
rec (MkIC z p) = MkIC (recip z) (norm . MkPoly . reverse . coeffs $ p)
    where
    norm q = recip (leadingCoeff q) .* q
-- XXX mit X kürzen

--instance Fractional IC where
--    fromRational r = MkIC (constant $ fromRational r) (iX - fromRational r)
--    recip = error "recip"
-}
