{-# LANGUAGE ScopedTypeVariables #-}
module NumericHelper where

import Prelude hiding (gcd)
import Test.QuickCheck
import Data.List
import Debug.Trace

-- Hat Eigenschaft: Für a rational, a > 0 konvergiert rootSeq streng monoto
-- von oben gegen die positive p-te Wurzel von a.
rootSeq :: (Fractional a) => Int -> a -> Integer -> a
rootSeq p a n = xs `genericIndex` n
    where
    xs = iterate (\x -> ((p'-1)*x + a/x^(p-1)) / p') a
    p' = fromIntegral p

-- konvergiert von unten, FIXME!
rootSeq' :: (Fractional a) => Int -> a -> Integer -> a
rootSeq' = rootSeq
{-p a n = xs `genericIndex` n
    where
    xs = iterate (\x -> x - x/p' + (-1)^p * a / (p' * x^(p-1))) (a)
    p' = fromIntegral p-}

-- Für x > 0 größtes n mit 1/n < x
roundDownToRecipN :: Rational -> Integer
roundDownToRecipN = ceiling . recip

-- ilog b n == Abrundung von log_b n
ilogb :: Integer -> Integer -> Integer
ilogb b n | n < 0      = ilogb b (- n)
          | n < b      = 0
          | otherwise  = (up b n 1) - 1
  where up b n a = if n < (b ^ a)
                      then bin b (quot a 2) a
                      else up b n (2*a)
        bin b lo hi = if (hi - lo) <= 1
                         then hi
                         else let av = quot (lo + hi) 2
                              in if n < (b ^ av)
                                    then bin b lo av
                                    else bin b av hi

class (Num a) => Euclidean a where
    gcd :: a -> a -> (a,a,a,a)

instance Euclidean Integer where
    gcd a b
        | b == 0
        = (1, 0, 1, 0)
        | a < 0
        = let (u,v,s,t) = gcd (-a) b
          in  (-u,v,-s,t)
        | otherwise
        = (u,v,s,t)
            where
            (u',v',s',t') = gcd b r
            (q,r)         = a `quotRem` b
            u             = v'
            v             = u' - q * v'
            s             = t' + q * s'
            t             = s'

ggTCheck :: Integer -> Integer -> (Integer,Integer,Integer,Integer) -> (Integer,Integer,Integer)
ggTCheck a b (u,v,s,t) = (d, d*s, d*t) where d = u*a + v*b

prop_gcd :: Property
prop_gcd = forAll arbitrary $ \(a :: Integer) -> forAll arbitrary $ \b ->
    let (u,v,s,t) = gcd a b
	d         = u*a + v*b
    in  trace (show (a,b,d)) $ d*s == a && d*t == b
