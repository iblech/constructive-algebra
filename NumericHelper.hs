{-# LANGUAGE ScopedTypeVariables, PatternGuards #-}
-- | Dieses Modul stellt numerische Hilfsfunktionen bereit.
module NumericHelper where

import Prelude hiding (gcd)
import Data.List
import Debug.Trace
import Data.Ratio
import Primes
import Testing

-- | Findet zu einer gegebenen rationalen Zahl /x > 0/ die kleinste positive
-- Zahl /n/ mit /1\/n < x/.
roundDownToRecipN :: Rational -> Integer
roundDownToRecipN x = if recip (fromInteger n) == x then n + 1 else n where n = ceiling . recip $ x

props_roundDownToRecipN =
    [ forAll positive $ \x ->
        let n = roundDownToRecipN x
        in  recip (fromInteger n) < x
    , forAll positive $ \x -> forAll positive $ \n' ->
        recip (fromInteger n') < x ==> n' >= roundDownToRecipN x
    ]

-- | Rundet eine gegebene rationale Zahl /x/ zur nächsten ganzen Zahl auf
-- (also Richtung /+∞/).
roundUp :: Rational -> Integer
roundUp z
    | x `mod` y == 0 = x `div` y
    | otherwise      = x `div` y + 1
  where (x,y) = (numerator z, denominator z)

props_roundUp =
    [ property $ \x ->
        x <= fromInteger (roundUp x)  &&  fromInteger (roundUp x) - x < 1
    ]

-- ilog b n == Abrundung von log_b n
-- XXX Quelle?
-- http://www.haskell.org/pipermail/haskell-cafe/2009-August/065854.html
-- XXX Bessere Version nehmen!
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

props_ilogb = (:[]) $ forAll positive $ \b -> forAll positive $ \n ->
    b > 1 ==>
    let k = ilogb b n
    in  b^k <= n && b^(k+1) > n

-- | Bestimmt zu einer gegebenen ganzen Zahl /n ≠ 0/ ihre Primfaktorzerlegung
-- (in positive Primzahlen). Die Vielfachheiten sind jeweils die zweiten
-- Komponenten der Paare. Jeder Primfaktor kommt genau einmal in der
-- Rückgabeliste vor.
primeFactors :: Integer -> [(Integer,Integer)]
primeFactors = multiplicities . group . go primes
    where
    go (p:ps) n
        | abs n == 1           = []
        | (q,0) <- quotRem n p = p : go (p:ps) q
        | otherwise            = go ps n
    multiplicities = map (\xs -> (head xs, genericLength xs))

props_primeFactors = (:[]) $ forAll arbitrary $ \n -> n /= 0 ==> and
    [ abs n == product (map (uncurry (^)) . primeFactors $ n)
    , all (`elem` primes) . map fst $ primeFactors n
    ]

-- | Liefert alle positiven Teiler einer gegebenen ganzen Zahl /n ≠ 0/, auch
-- /1/ und den (Betrag der) Zahl selbst. Erfüllt folgende Spezifikation:
--
-- > positiveDivisors n = [x | x <- [1..abs n], n `mod` x == 0]
positiveDivisors :: Integer -> [Integer]
positiveDivisors = sort . go . primeFactors
    where
    go []         = [1]
    go ((p,n):ps) = do
        i <- [0..n]
        q <- go ps
        return $ p^i * q

props_positiveDivisors = (:[]) $ forAll arbitrary $ \n -> n /= 0 ==>
    positiveDivisors n == [x | x <- [1..abs n], n `mod` x == 0]

-- | Bestimmt zu einer gegebenen nichtnegativen ganzen Zahl /n/ die Abrundung
-- ihrer nichtnegativen Quadratwurzel.
--
-- Quelle: <http://www.haskell.org/haskellwiki/Generic_number_type#squareRoot>
squareRoot :: Integer -> Integer
squareRoot 0 = 0
squareRoot 1 = 1
squareRoot n =
   let twopows = iterate (^2) 2
       (lowerRoot, lowerN) =
          last $ takeWhile ((n>=) . snd) $ zip (1:twopows) twopows
       newtonStep x = div (x + div n x) 2
       iters = iterate newtonStep (squareRoot (div n lowerN) * lowerRoot)
       isRoot r  =  r^2 <= n && n < (r+1)^2
   in  head $ dropWhile (not . isRoot) iters

props_squareRoot = (:[]) $ forAll arbitrary $ \n -> n >= 0 ==>
    let s = squareRoot n
    in  s >= 0 && s^2 <= n && (s+1)^2 > n

prop_NumericHelper = concat
    [ props_roundDownToRecipN
    , props_roundUp
    , props_primeFactors
    , props_positiveDivisors
    , props_squareRoot
    ]
