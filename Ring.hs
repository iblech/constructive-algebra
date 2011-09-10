{-# LANGUAGE FlexibleInstances #-}
module Ring where

import qualified Prelude as P
import Prelude (Maybe, (&&), (||), (==), (/=), abs, otherwise)
import Data.Ratio
import qualified Data.Complex as C

class Ring a where
    (+) :: a -> a -> a
    (-) :: a -> a -> a
    (*) :: a -> a -> a
    zero   :: a
    unit   :: a
    negate :: a -> a
    fromInteger :: P.Integer -> a
    x - y = x + negate y
    infixl 6 +
    infixl 6 -
    infixl 7 *

    -- Zur Effizienzsteigerung, damit Null-Koeffizienten bei Polynomen
    -- gestrichen werden können.
    -- Es muss gelten: couldBeNonZero x == False  ==>  x == zero.
    couldBeNonZero :: a -> P.Bool
    couldBeNonZero = P.const P.True

class (Ring a) => IntegralDomain a

data Sign = N | Z | P deriving (P.Show,P.Eq,P.Ord)
signum :: (Ring a, P.Ord a) => a -> Sign
signum x
    | x P.> zero = P
    | x ==  zero = Z
    | x P.< zero = N
    | otherwise  = P.error "signum"

-- x ~ y :<=> ex. u inv'bar: y = u x
class (Ring a) => TestableAssociatedness a where
    areAssociated :: a -> a -> Maybe a
    -- Nothing, oder Just u (mit y = u x, in der Reihenfolge)

class (Ring a) => AllowsRationalEmbedding a where
    fromRational :: Rational -> a

class (Ring a) => AllowsConjugation a where
    conjugate :: a -> a
    imagUnit  :: a

absSq :: (AllowsConjugation a) => a -> a
absSq z = z * conjugate z

realPart :: (AllowsConjugation a, AllowsRationalEmbedding a) => a -> a
realPart z = fromRational (1 P./ 2) * (z + conjugate z)

imagPart :: (AllowsConjugation a, AllowsRationalEmbedding a) => a -> a
imagPart z = negate imagUnit * fromRational (1 P./ 2) * (z - conjugate z)

-- unsafePerformIO zugelassen
class ApproxFloating a where
    approx :: a -> C.Complex P.Double

-- direkt ausm Prelude kopiert
(^) :: (Ring a) => a -> P.Integer -> a
x ^ 0           = unit
x ^ n | n P.> 0 = f x (n-1) x
    where f _ 0 y = y
          f x n y = g x n  where
                    g x n | P.even n  = g (x*x) (n `P.quot` 2)
                          | P.otherwise = f x (n-1) (x*y)
_ ^ _           = P.error "Prelude.^: negative exponent"
infixr 8 ^

instance Ring P.Int where
    (+)    = (P.+)
    (*)    = (P.*)
    zero   = 0
    unit   = 1
    negate = P.negate
    fromInteger = P.fromInteger
    couldBeNonZero = (/= 0)
instance ApproxFloating P.Int where
    approx = P.fromIntegral

instance Ring P.Integer where
    (+)    = (P.+)
    (*)    = (P.*)
    zero   = 0
    unit   = 1
    negate = P.negate
    fromInteger = P.fromInteger
    couldBeNonZero = (/= 0)
instance IntegralDomain P.Integer
instance TestableAssociatedness P.Integer where
    areAssociated x y
        | abs x == abs y = P.Just (P.signum x * P.signum y)
        | otherwise      = P.Nothing
instance ApproxFloating P.Integer where
    approx = P.fromIntegral

instance (IntegralDomain a, P.Integral a) => Ring (Ratio a) where
    (+)    = (P.+)
    (*)    = (P.*)
    zero   = 0
    unit   = 1
    negate = P.negate
    fromInteger = P.fromInteger
    couldBeNonZero = (/= 0)
instance (IntegralDomain a, P.Integral a) => IntegralDomain (Ratio a)
instance (IntegralDomain a, P.Integral a) => TestableAssociatedness (Ratio a) where
    areAssociated x y
        | x == zero && y == zero = P.Just 1
        | x /= zero && y /= zero = P.Just (y * P.recip x)
        | otherwise              = P.Nothing
instance AllowsRationalEmbedding (Ratio P.Integer) where
    fromRational = P.fromRational
instance (IntegralDomain a, P.Integral a, ApproxFloating a) => ApproxFloating (Ratio a) where
    approx x =
        let (p,q) = (numerator x,denominator x)
        in  approx p P./ approx q

sum :: (Ring a) => [a] -> a
sum = sum' zero
    where
    sum' acc []     = acc
    sum' acc (x:xs) = sum' (acc + x) xs

product :: (Ring a) => [a] -> a
product = product' unit
    where
    product' acc []     = acc
    product' acc (x:xs) = product' (acc * x) xs
