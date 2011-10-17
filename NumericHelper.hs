-- | Dieses Modul stellt numerische Hilfsfunktionen bereit.
{-# LANGUAGE ScopedTypeVariables, PatternGuards #-}
module NumericHelper where

import Prelude hiding (gcd)
import Data.List
import Data.Ratio
import Primes
import Nat
import Testing

-- | Approximation an den Typ nichtnegativer rationaler Zahlen.
type NonnegativeRational = Rational

-- | Findet zu einer gegebenen rationalen Zahl /x > 0/ die kleinste positive
-- Zahl /n/ mit /1\/n < x/.
roundDownToRecipN :: Rational -> PositiveNat
roundDownToRecipN x = if recip (fromInteger n) == x then n + 1 else n where n = ceiling . recip $ x

props_roundDownToRecipN :: [Property]
props_roundDownToRecipN =
    [ forAll positive $ \x ->
        let n = roundDownToRecipN x
        in  n > 0 && recip (fromInteger n) < x
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

props_roundUp :: [Property]
props_roundUp =
    [ property $ \x ->
        x <= fromInteger (roundUp x)  &&  fromInteger (roundUp x) - x < 1
    ]

-- ilog b n == Abrundung von log_b n
-- XXX Quelle?
-- http://www.haskell.org/pipermail/haskell-cafe/2009-August/065854.html
-- XXX Bessere Version nehmen!
ilogb :: PositiveNat -> Nat -> Integer
ilogb b n | n < 0      = error "ilogb: Negatives Argument!"
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

props_ilogb :: [Property]
props_ilogb = (:[]) $ forAll positive $ \b -> forAll positive $ \n ->
    b > 1 ==>
    let k = ilogb b n
    in  b^k <= n && b^(k+1) > n

ilogbUp :: PositiveNat -> Nat -> Integer
ilogbUp b n =
    let l = ilogb b n
    in  if b^l == n then l else l + 1

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
    go [] _ = undefined  -- kann nicht eintreten
    multiplicities = map (\xs -> (head xs, genericLength xs))

props_primeFactors :: [Property]
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

props_positiveDivisors :: [Property]
props_positiveDivisors = (:[]) $ forAll arbitrary $ \n -> n /= 0 ==>
    positiveDivisors n == [x | x <- [1..abs n], n `mod` x == 0]

-- | Bestimmt zu einer gegebenen nichtnegativen ganzen Zahl /n/ die Abrundung
-- ihrer nichtnegativen Quadratwurzel.
--
-- Quelle: <http://www.haskell.org/haskellwiki/Generic_number_type#squareRoot>
squareRoot :: Nat -> Nat
squareRoot 0 = 0
squareRoot 1 = 1
squareRoot n =
   let twopows = iterate (^(2::Integer)) 2
       (lowerRoot, lowerN) =
          last $ takeWhile ((n>=) . snd) $ zip (1:twopows) twopows
       newtonStep x = div (x + div n x) 2
       iters = iterate newtonStep (squareRoot (div n lowerN) * lowerRoot)
       isRoot r  =  r*r <= n && n < (r+1)*(r+1)
   in  head $ dropWhile (not . isRoot) iters

props_squareRoot :: [Property]
props_squareRoot = (:[]) $ forAll arbitrary $ \n -> n >= 0 ==>
    let s = squareRoot n
    in  s >= 0 && s*s <= n && (s+1)*(s+1) > n

-- | Bestimmt zu einer gegebenen nichtnegativen rationalen Zahl untere und obere
-- Schranken für ihre Quadratwurzel.
squareRootBounds :: NonnegativeRational -> (NonnegativeRational, NonnegativeRational)
squareRootBounds x = (squareRoot p % squareRootUp q, squareRootUp p % squareRoot q)
    where
    (p,q) = (numerator x, denominator x)
    squareRootUp n =
        let n' = squareRoot n
        in  if n'*n' == n then n' else n' + 1

props_squareRootBounds :: [Property]
props_squareRootBounds =
    [ property $ \x -> x >= 0 ==>
        let (u,v) = squareRootBounds x
        in  u >= 0 && v >= 0 && u*u <= x && x <= v*v
    ]

-- | Ist eine rationale Zahl /x/ sogar eine ganze Zahl, so liefert
-- /unsafeFromRational x/ diese ganze Zahl. Sonst wirft sie eine
-- Laufzeitausnahme.
unsafeFromRational :: Rational -> Integer
unsafeFromRational x
    | r == 0    = q
    | otherwise = error $ "unsafeFromRational: " ++ show x
    where
    (q,r) = numerator x `quotRem` denominator x

-- | Liefert Approximationen an den goldenen Schnitt. Erfüllt folgende
-- Spezifikation:
--
-- > |goldenRatioSeq n - φ| < 1/n für alle n >= 1.
goldenRatioSeq :: Integer -> Rational
goldenRatioSeq n = xs `genericIndex` (ilogb 2 n)
    where xs = iterate ((1 +) . recip) 1
-- a_1 = 1, a_(n+1) = 1 + 1/a_n
-- erfüllt |a_n - a| < (4/9)^n für alle n >= 2.
-- Diese Folge hier wird künstlich verlangsamt, sie erfüllt |x_n - x| < 1/n für
-- alle n >= 1.
-- XXX: Bestimmt kann man die Folge noch viel weiter verlangsamen!

-- | Liefert Approximationen an /√2/. Erfüllt folgende Spezifikation:
--
-- > |sqrt2Seq n - √2| < 1/n für alle n >= 1.
sqrt2Seq :: Integer -> Rational
sqrt2Seq n = xs `genericIndex` ((1 + ilogb 2 n) `div` 2)
    where xs = map (+ 1) $ iterate (\x -> 1 / (fromInteger 2 + x)) 0
-- Die Folge mit
--   a_1 = 0, a_(n+1) = 1/(2+a_n)
-- erfüllt |a_n - (sqrt(2) - 1)| <= gamma^n * c für alle n >= 1
-- mit gamma = 1 / (2 (1 + sqrt(2))) <= 0.2072 und c = 2.
-- Die Folge hier wird daher entsprechend künstlich verlangsamt.
-- XXX: Bestimmt kann man die Folge noch viel weiter verlangsamen!

props_Approximation :: (Integer -> Rational) -> Double -> [Property]
props_Approximation f x = (:[]) $ forAll positive $ \n ->
    abs (fromRational (f n) - x) < recip (fromInteger n)

props_NumericHelper :: [Property]
props_NumericHelper = concat
    [ props_roundDownToRecipN
    , props_roundUp
    , props_primeFactors
    , props_positiveDivisors
    , props_squareRoot
    , props_squareRootBounds
    , props_Approximation goldenRatioSeq ((1 + sqrt 5) / 2)
    , props_Approximation sqrt2Seq       (sqrt 2)
    ]
