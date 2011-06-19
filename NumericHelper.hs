{-# LANGUAGE ScopedTypeVariables #-}
module NumericHelper where

import Prelude hiding (gcd)
import Data.List
import Debug.Trace
import Data.Ratio

{-
-- Hat Eigenschaft: Für a rational, a > 0 konvergiert rootSeq streng
-- monoton von oben gegen die positive p-te Wurzel von a.
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
-}

-- Für x > 0 kleinstes n mit 1/n < x und n > 0
roundDownToRecipN :: Rational -> Integer
roundDownToRecipN x = if recip (fromInteger n) == x then n + 1 else n where n = ceiling . recip $ x

roundUp :: Rational -> Integer
roundUp z
    | x `mod` y == 0 = x `div` y
    | otherwise      = x `div` y + 1
  where (x,y) = (numerator z, denominator z)

-- ilog b n == Abrundung von log_b n
-- XXX Quelle?
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

-- Liefert alle positiven Teiler, auch 1 und die Zahl selbst.
-- XXX: Naiv implementiert!
positiveDivisors :: Integer -> [Integer]
positiveDivisors n
    | n == 0    = error "divisors 0"
    | otherwise = [x | x <- [1..abs n], n `mod` x == 0]
