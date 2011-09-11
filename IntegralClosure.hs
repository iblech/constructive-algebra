{-# LANGUAGE FlexibleContexts, UndecidableInstances, FlexibleInstances #-}
module IntegralClosure where

import Debug.Trace

import Prelude hiding (fromInteger, fromRational, (+), (*), (-), (^), negate)
import Complex hiding (goldenRatio, sqrt2)
import qualified Complex
import qualified Prelude as P
import NumericHelper
import qualified Polynomial as P
import Polynomial hiding (constant)
import Matrix hiding ((!!))
import Ring
import RingMorphism
import Field
import Smith
import ComplexRational

import Data.Array

-- Polynom soll normiert sein
data (RingMorphism m) => IC m =
    MkIC { number :: Codomain m, polynomial :: Poly (Domain m) }

-- FIXME: Besserer Name
fromBase :: (RingMorphism m) => Domain m -> IC m
fromBase x = r
    where
    r    = MkIC (mor' x) (iX - P.constant x)
    mor' = mor ((undefined :: IC m -> m) r)

instance (RingMorphism m, HaveAnnihilatingPolynomial (Domain m)) => Ring (IC m) where
    MkIC x p + MkIC x' p' = MkIC (x + x') (sumPolynomial p p')
    MkIC x p * MkIC x' p'
        | couldBeNotX p  == False = zero
        | couldBeNotX p' == False = zero
        | otherwise               = MkIC (x * x') (prodPolynomial p p')

    negate (MkIC x p) = MkIC (negate x) (MkPoly as)
	where
	as = reverse $ zipWith (*) (reverse $ coeffs p) (cycle [unit,negate unit])

    fromInteger i = MkIC (fromInteger i) (iX - fromInteger i)

    zero = fromInteger zero
    unit = fromInteger unit

{-
instance Show (IC m) where show = error "show on IC"
instance Eq   (IC m) where (==) = error "== on IC"
instance (RingMorphism m, Determinantable (Poly (Domain m))) => P.Num (IC m) where
    (+) = (+)
    (*) = (*)
    negate      = negate
    abs         = error "abs on IC"
    signum      = error "signum on IC"
    fromInteger = fromInteger
-}

instance (RingMorphism m, IntegralDomain (Codomain m), HaveAnnihilatingPolynomial (Domain m)) =>
    IntegralDomain (IC m)

instance (RingMorphism m, HaveAnnihilatingPolynomial (Domain m), AllowsRationalEmbedding (Domain m)) =>
    AllowsRationalEmbedding (IC m) where
    fromRational r = z
        where
        mor' = mor ((undefined :: IC m -> m) z)
        z    = MkIC (mor' (fromRational r)) (iX - fromRational r)

instance (RingMorphism m, ApproxFloating (Codomain m)) =>
    ApproxFloating (IC m) where
    approx = approx . number

-- Voraussetzung: Polynome müssen normiert sein
sumPolynomial :: (Ring a, HaveAnnihilatingPolynomial a) => Poly a -> Poly a -> Poly a
sumPolynomial f g = annihilatingPolynomial . fromArray $ listArray ((0,0), (length indices - 1, length indices - 1)) elems
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
prodPolynomial :: (Ring a, HaveAnnihilatingPolynomial a) => Poly a -> Poly a -> Poly a
prodPolynomial f g = annihilatingPolynomial . fromArray $ listArray ((0,0), (length indices - 1, length indices - 1)) elems
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

-- Voraussetzung: Polynome müssen normiert sein
{-
solPolynomial :: (Ring a, Determinantable (Poly a)) => Poly a -> [Poly a] -> Poly a
solPolynomial p gs = charPoly . fromArray $ listArray ((0,0), (length indices - 1, length indices - 1)) elems
    where
    indices = [ (i,
-}

goldenRatio :: IC QinC
goldenRatio = MkIC Complex.goldenRatio (iX^2 - iX - unit)

sqrt2 :: IC QinC
sqrt2 = MkIC Complex.sqrt2 (iX^2 - unit - unit)

instance AllowsConjugation (IC QinC) where
    conjugate (MkIC z p) = MkIC (conjugate z) p
    imagUnit             = MkIC (constant imagUnit) (iX^2 + unit)

verifyPolynomial :: (RingMorphism m) => IC m -> Codomain m
verifyPolynomial z@(MkIC x f) = eval x $ fmap mor' f
    where mor' = mor ((undefined :: IC m -> m) z)
