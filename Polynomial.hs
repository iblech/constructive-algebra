{-# LANGUAGE GeneralizedNewtypeDeriving, PatternGuards #-}
module Polynomial where

import Prelude hiding (gcd, (+), (-), (*), (/), (^), negate, recip, fromInteger, fromRational, quotRem, sum)
import qualified Prelude as P
import Test.QuickCheck
import Data.List (intersperse, genericLength, foldl')
import NumericHelper
import Ring
import Field
import Euclidean
import Control.DeepSeq

newtype Poly a = MkPoly { unPoly :: [a] }
  deriving (Functor,NFData)

mkPoly :: (Ring a, Eq a) => [a] -> Poly a
mkPoly = canonForm . MkPoly

canonForm :: (Ring a, Eq a) => Poly a -> Poly a
canonForm = MkPoly . reverse . dropWhile (== zero) . reverse . unPoly

simplify :: (Ring a) => Poly a -> Poly a
simplify = MkPoly . reverse . dropWhile (not . couldBeNonZero) . reverse . unPoly

eval :: (Ring a) => a -> Poly a -> a
eval x = foldr (\c val -> c + x*val) zero . unPoly
--eval x = foldl' ((+) . (* x)) zero . reverse . unPoly
-- was ist besser?

-- Evaluiert in 0, semantisch gleich eval zero.
eval0 :: (Ring a) => Poly a -> a
eval0 (MkPoly [])     = zero
eval0 (MkPoly (a:as)) = a

instance (Ring a, Eq a, Show a) => Show (Poly a) where
  show f = addZero $ concat . intersperse " + " $ filter (not . null) $ zipWith join (unPoly $ canonForm f) vars
      where
      vars = "" : "X" : map (("X^" ++) . show) [2..]
      join x v
        | x == zero = ""
	| x == unit = if null v then "1" else v
	| otherwise = show x ++ (if null v then "" else "*" ++ v)
      addZero s
	| null s    = "0"
	| otherwise = s

instance (Ring a, Eq a) => Eq (Poly a) where
    p == q = unPoly (canonForm p) == unPoly (canonForm q)
    
instance (Ring a) => Ring (Poly a) where
    MkPoly xs + MkPoly ys = simplify $ MkPoly (zipWithDefault (+) zero xs ys)
    MkPoly xs * MkPoly ys = simplify . MkPoly $ go xs ys
	where
	go []     ys = []
	go (x:xs) ys = zipWithDefault (+) zero (map (x *) ys) (zero:go xs ys)
    negate (MkPoly xs) = MkPoly $ map negate xs
    fromInteger = MkPoly . (:[]) . fromInteger
    zero = fromInteger zero
    unit = fromInteger unit

instance (AllowsConjugation a) => AllowsConjugation (Poly a) where
    conjugate (MkPoly xs) = MkPoly (map conjugate xs)
    imagUnit              = constant imagUnit

instance (IntegralDomain a) => IntegralDomain (Poly a)

instance (AllowsRationalEmbedding a) => AllowsRationalEmbedding (Poly a) where
    fromRational = constant . fromRational

instance (Field a, Eq a, IntegralDomain a) => EuclideanRing (Poly a) where
    degree = pred . genericLength . unPoly . canonForm
    quotRem f g
        | degree f < degree g = (MkPoly [], f)
        | otherwise
        = let (q,r) = quotRem (f - q' * g) g
              q'    = leadingCoeff f / leadingCoeff g .* (iX^(degree f - degree g))
          in  (q + q', r)

instance (Field a, Eq a) => TestableAssociatedness (Poly a) where
    areAssociated p q
        | p == zero && q == zero = Just unit
        | p /= zero && q /= zero =
            let x = leadingCoeff q / leadingCoeff p
            in  if x .* p == q then Just (constant x) else Nothing
        | otherwise        = Nothing

infixl 7 .*
(.*) :: (Ring a) => a -> Poly a -> Poly a
x .* f = MkPoly $ map (x *) $ unPoly f

iX :: (Ring a) => Poly a
iX = MkPoly [zero, unit]

constant :: a -> Poly a
constant x = MkPoly [x]

norm :: (Field a, Eq a) => Poly a -> Poly a
norm p = recip (leadingCoeff p) .* p

zipWithDefault :: (a -> a -> b) -> a -> [a] -> [a] -> [b]
zipWithDefault (#) zero = go
    where
    go []     ys     = map (zero #) ys
    go (x:xs) []     = map (# zero) (x:xs)
    go (x:xs) (y:ys) = (x#y) : go xs ys

-- bottom fürs Nullpolynom
leadingCoeff :: (Ring a, Eq a) => Poly a -> a
leadingCoeff = last . unPoly . canonForm

-- nach aufsteigender Potenz geordnet, Nuller möglich
coeffs :: Poly a -> [a]
coeffs = unPoly

derivative :: (Ring a) => Poly a -> Poly a
derivative (MkPoly xs) 
    | null xs   = MkPoly []
    | otherwise = simplify . MkPoly $ zipWith (*) (tail xs) $ map fromInteger [1..]

-- compose f g = "f . g"
compose :: (Ring a) => Poly a -> Poly a -> Poly a
compose (MkPoly as) g = sum $ zipWith (\a i -> a .* g^i) as (map fromInteger [0..])

multiplicity :: (Ring a, Eq a) => a -> Poly a -> Int
multiplicity x f
    | eval x f == zero = 1 + multiplicity x (derivative f)
    | otherwise        = 0

-- Zur Effizienzsteigerung.
-- Es muss gelten: couldBeNotX p == False  ==>  p == iX.
couldBeNotX :: (Ring a) => Poly a -> P.Bool
couldBeNotX (MkPoly [a0,a1])
    | couldBeNonZero a0 == False && couldBeNonZero (a1 - unit) == False = False
couldBeNotX _ = True
