module Zero where

import Prelude hiding ((+), (*), (/), (-), (^), negate, fromInteger, fromRational, recip, signum, sum)
import Polynomial
import Ring
import Field
import NumericHelper
import Complex hiding (constant)
import Algebraic
import Polynomial
import Control.Monad
import Euclidean
import ComplexRational
import Real
import IntegralClosure
import Debug.Trace

-- Zählt die Anzahl von Vorzeichenänderungen, Wechsel von/auf 0 zählen 1/2
signChanges :: (Ring a, Ord a) => [a] -> Rational
signChanges xs = sum $ map f (pairs xs)
    where
    pairs []       = []
    pairs [x]      = []
    pairs (x:y:zs) = (x,y) : pairs (y:zs)
    f (x,y)
        | signum (x*y) == N      = 1
        | x == zero && y /= zero = 1/2
        | x /= zero && y == zero = 1/2
        | otherwise              = 0

signChanges' :: (Ring a, Ord a) => a -> a -> [Poly a] -> Rational
signChanges' a b ps = signChanges (map (eval a) ps) - signChanges (map (eval b) ps)

sturmChain :: (Field a, Eq a, IntegralDomain a) => Poly a -> Poly a -> [Poly a]
sturmChain r s
    | degree r > degree s = error "sturmChain"
    | otherwise           = euclidChain s r

index :: (Field a, Eq a, IntegralDomain a, Ord a) => a -> a -> Poly a -> Poly a -> Rational
index a b r s
    | degree r <= degree s = signChanges' a b (sturmChain r s)
    | otherwise            = signChanges' a b [r,s] - index a b s r

windingNumber :: ComplexRational -> ComplexRational -> Poly (Alg QinC) -> Rational
windingNumber z z' p
    = index zero unit (toReal $ realPart gamma) (toReal $ imagPart gamma) / 2
    where
    gamma = compose p alpha
    alpha = constant (fromBase' z) + iX * constant (fromBase' (z' - z))
    toReal :: Poly (Alg QinC) -> Poly (Alg QinR)
    toReal = fmap (\(MkAlg (MkIC z p)) -> MkAlg (MkIC (realComponent z) p))
    fromBase' (u :+: v)
        | v == 0    = fromRational u
        | otherwise = MkAlg $ fromRational u + imagUnit * fromRational v

--windingNumber :: ComplexRational -> ComplexRational -> Poly (Alg QinC) -> Rational
windingNumber' z z' p
    = index zero unit (fmap toReal $ realPart gamma) (fmap toReal $ imagPart gamma) / 2
    where
    gamma = compose p alpha
    alpha = constant (fromBase' z) + iX * constant (fromBase' (z' - z))
    fromBase' (u :+: v)
        | v == 0    = fromRational u
        | otherwise = fromRational u + imagUnit * fromRational v
    toReal (x :+: y) = x

ex :: Poly (Alg QinC)
ex = (iX + negate (fromInteger 3)) * (iX + negate (fromInteger 3))  -- + fromInteger 4 * Polynomial.constant imagUnit))

ex' :: Poly ComplexRational
ex' = (iX + negate (fromInteger 3)) * (iX + negate (fromInteger 3))  -- + fromInteger 4 * Polynomial.constant imagUnit))
