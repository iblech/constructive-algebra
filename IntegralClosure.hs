module IntegralClosure where

import Debug.Trace

import Prelude hiding (fromInteger, (+), (*), negate)
import Complex hiding (goldenRatio, sqrt2)
import qualified Complex
import NumericHelper
import Polynomial hiding (constant)
import Matrix hiding ((!!))
import Ring
--import Smith

import Data.Array

data IC a b = MkIC { number :: b, polynomial :: Poly a }

instance Eq   (IC a b) where (==) = error "== on IC"

instance Show (IC a b) where show = error "show on IC"

instance (Ring a, Ring b) => Ring (IC a b) where
    MkIC x p + MkIC x' p' = MkIC (x + x') (sumPolynomial p p')
    MkIC x p * MkIC x' p' = MkIC (x * x') (prodPolynomial p p')

    negate (MkIC x p) = MkIC (negate x) (MkPoly as)
	where
	as = reverse $ zipWith (*) (reverse $ coeffs p) (cycle [1,-1])

    fromInteger i = MkIC (fromInteger i) (iX - fromInteger i)

    zero = fromInteger zero
    unit = fromInteger unit

-- Voraussetzung: Polynome müssen normiert sein
sumPolynomial :: (Ring a) => Poly a -> Poly a -> Poly a
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

{-

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

goldenRatio :: IC
goldenRatio = MkIC Complex.goldenRatio (iX^2 - iX - 1)

sqrt2 :: IC
sqrt2 = MkIC Complex.sqrt2 (iX^2 - 2)

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
