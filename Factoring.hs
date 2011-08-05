module Factoring where

import Prelude hiding ((+), (*), (/), (-), (^), negate, fromInteger, fromRational, recip, signum, sum, product, quotRem, gcd)
import Ring
import Polynomial
import ZeroRational
import Data.Maybe
import Data.List hiding (product)
import Euclidean
import Algebraic
import Control.Monad
import Complex hiding (constant)
import IntegralClosure
import Field

-- soll mind. Grad 1 haben
isIrreducible :: Poly Rational -> Maybe (Poly Rational,Poly Rational)
isIrreducible f
    | degree f <  1 = error "isirreducible"
    | degree f == 1 = Nothing
    | otherwise
    = listToMaybe $ do
	xs <- subsequences zeros
	guard $ not $ null xs
	guard $ length xs /= length zeros
	let p = product $ map ((iX -) . constant) xs
	Just p' <- [isRationalPoly p]
	let q = fst $ f `quotRem` p'  -- ist das ineffizient?
	return (p',q)
    where
    zeros  = rootsA f

-- soll mind. Grad 1 haben
irreducibleFactors :: Poly Rational -> [Poly Rational]
irreducibleFactors f
    | Nothing <- test
    = [f]
    | Just (p,q) <- test
    = irreducibleFactors p ++ irreducibleFactors q
    where
    test = isIrreducible f

-- sollte dann in allen Vorkommen von z das MP liefern (überschreiben)
minimalPolynomial :: Alg QinC -> Poly Rational
minimalPolynomial z = go (fmap unF . polynomial . unAlg $ z)
    where
    go f
	| degree f <= 1 = f
	| otherwise     = case isIrreducible f of
	    Nothing    -> f
	    Just (p,q) -> if eval z (fmap fromRational p) == zero then go p else go q
