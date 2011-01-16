{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Polynomial where

import Test.QuickCheck
import Data.List (intersperse)

newtype Poly a = MkPoly { unPoly :: [a] }
  deriving (Functor)

mkPoly :: (Num a) => [a] -> Poly a
mkPoly = canonForm . MkPoly

canonForm :: (Num a) => Poly a -> Poly a
canonForm = MkPoly . reverse . dropWhile (== 0) . reverse . unPoly

eval :: (Num a) => a -> Poly a -> a
eval x = foldr (\c val -> c + x*val) 0 . unPoly

instance (Num a, Show a) => Show (Poly a) where
  show f = addZero $ concat . intersperse " + " $ filter (not . null) $ zipWith join (unPoly $ canonForm f) vars
      where
      vars = "" : "X" : map (("X^" ++) . show) [2..]
      join x v
	| x == 0    = ""
	| x == 1    = if null v then "1" else v
	| otherwise = show x ++ (if null v then "" else "*" ++ v)
      addZero s
	| null s    = "0"
	| otherwise = s

instance (Num a) => Eq (Poly a) where
    p == q = unPoly (canonForm p) == unPoly (canonForm q)
    
instance (Num a) => Num (Poly a) where
    MkPoly xs + MkPoly ys = MkPoly (zipWithDefault (+) 0 xs ys)
    MkPoly xs * MkPoly ys = MkPoly $ go xs ys
	where
	go []     ys = []
	go (x:xs) ys = zipWithDefault (+) 0 (map (x *) ys) (0:go xs ys)
    negate (MkPoly xs) = MkPoly $ map negate xs
    abs    = error "abs on Poly a"
    signum = error "signum on Poly a"
    fromInteger = MkPoly . (:[]) . fromInteger

infixl 7 .*
(.*) :: (Num a) => a -> Poly a -> Poly a
x .* f = MkPoly $ map (x *) $ unPoly f

iX :: (Num a) => Poly a
iX = MkPoly [0,1]

constant :: a -> Poly a
constant x = MkPoly [x]

zipWithDefault :: (a -> a -> b) -> a -> [a] -> [a] -> [b]
zipWithDefault (#) zero = go
    where
    go []     ys     = map (zero #) ys
    go (x:xs) []     = map (# zero) (x:xs)
    go (x:xs) (y:ys) = (x#y) : go xs ys

degree :: (Num a) => Poly a -> Int
degree = pred . length . unPoly . canonForm

-- bottom fürs Nullpolynom
leadingCoeff :: (Num a) => Poly a -> a
leadingCoeff = last . unPoly . canonForm

-- nach aufsteigender Potenz geordnet
coeffs :: (Num a) => Poly a -> [a]
coeffs = unPoly . canonForm

quotrem :: (Fractional a) => Poly a -> Poly a -> (Poly a, Poly a)
quotrem f g
  | degree f < degree g = (MkPoly [], f)
  | otherwise
  = let (q,r) = quotrem (f - q' * g) g
	q'    = leadingCoeff f / leadingCoeff g .* (iX^(degree f - degree g))
    in  (q + q', r)
