module Polynomial where

newtype Poly a = MkPoly { unPoly :: [a] }
    deriving (Show)

mkPoly :: (Num a) => [a] -> Poly a
mkPoly = canonForm . MkPoly

canonForm :: (Num a) => Poly a -> Poly a
canonForm = MkPoly . reverse . dropWhile (== 0) . reverse . unPoly

instance (Num a) => Eq (Poly a) where
    p == q = unPoly (canonForm p) == unPoly (canonForm q)
    
instance (Num a) => Num (Poly a) where
    MkPoly xs + MkPoly ys = mkPoly (zipWithDefault (+) 0 xs ys)
    MkPoly xs * MkPoly ys = mkPoly $ go xs ys
	where
	go []     ys = []
	go (x:xs) ys = zipWithDefault (+) 0 (map (x *) ys) (0:go xs ys)
    abs    = error "abs on Poly a"
    signum = error "signum on Poly a"
    fromInteger = mkPoly . (:[]) . fromInteger

iX :: (Num a) => Poly a
iX = MkPoly [0,1]

zipWithDefault :: (a -> a -> b) -> a -> [a] -> [a] -> [b]
zipWithDefault (#) zero = go
    where
    go []     ys     = map (zero #) ys
    go (x:xs) []     = map (# zero) (x:xs)
    go (x:xs) (y:ys) = (x#y) : go xs ys
