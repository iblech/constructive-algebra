{-# LANGUAGE FlexibleContexts, FlexibleInstances #-}
module Smith where

import Matrix
import Data.Array
import Prelude hiding (gcd, (!!), (+), (*), (-), (/), negate, quotRem)
import qualified Prelude as P
import NumericHelper
import Polynomial
import Ring
import Field
import Euclidean
import Debug.Trace
import Data.Ratio

makeZeroInFirstRow :: (EuclideanRing a, Eq a, TestableAssociatedness a) => Nat -> Matrix a -> Matrix a
makeZeroInFirstRow j mtx@(MkMatrix arr) = MkMatrix (arr // updates) `asTypeOf` mtx
    where
    (u,v,s,t) = gcd' (arr ! (0,0)) (arr ! (0,j))
    updates   = do
	i <- [0..n]
	let (x,y) = (arr ! (i,0), arr ! (i,j))
	[ ((i,0), u*x + v*y), ((i,j), s*y - t*x) ]
    ((0,0),(n,m)) = bounds arr

makeZeroInFirstCol :: (EuclideanRing a, Eq a, TestableAssociatedness a) => Nat -> Matrix a -> Matrix a
makeZeroInFirstCol i = transpose . makeZeroInFirstRow i . transpose

diagonalForm :: (EuclideanRing a, Eq a, TestableAssociatedness a) => Matrix a -> [a]
diagonalForm mtx = dia mtx  --trace (show $ elems . unMatrix $ mtx) $ dia mtx

dia mtx
    | numRows mtx == 0 || numCols mtx == 0
    = []
    | not (null badCols)
    = diagonalForm $ makeZeroInFirstRow (head badCols) mtx
    | not (null badRows)
    = diagonalForm $ makeZeroInFirstCol (head badRows) mtx
    | otherwise
    = mtx !! (0,0) : diagonalForm mtx'
    where
    badCols = [j | j <- [1..numCols mtx - 1], mtx !! (0,j) /= zero]
    badRows = [i | i <- [1..numRows mtx - 1], mtx !! (i,0) /= zero]
    mtx'    = deleteRow 0 . deleteColumn 0 $ mtx

elementaryDivisors :: (EuclideanRing a, Eq a, TestableAssociatedness a) => Matrix a -> [a]
elementaryDivisors = divisors . diagonalForm

divisors :: (EuclideanRing a, Eq a, TestableAssociatedness a) => [a] -> [a]
divisors [] = []
divisors as = go (length as - 1) as
    where
    go i as
	| i == 0    = head as : divisors (tail as)
	| otherwise = go (i-1) $ d : splice (i-1) p (tail as)
	where
	(u,v,s,t) = gcd (head as) (as P.!! i)
	d         = u*head as + v*as P.!! i
	p         = d*s*t

splice :: Int -> a -> [a] -> [a]
splice 0 x (y:ys) = x : ys
splice n x (y:ys) = y : splice (n-1) x ys

{-
smith' :: (Fractional a) => SqMatrix a -> [Poly a]
smith' (MkMatrix arr) = elementaryDivisors (fromArray arr')
    where
    arr' = accum (+) (fmap (negate . constant) arr) [((i,i), iX) | i <- [0..fst (snd (bounds arr))]]
-}

-- annihilatingPolynomial m soll ein normiertes (!) Polynom sein, welches m annihiliert.
class (Ring a) => HaveAnnihilatingPolynomial a where
    annihilatingPolynomial :: SqMatrix a -> Poly a

{-
 - XXX: noch verbessern: Sollte für jeden IntBer. funktionieren. Hat mit ER nichts zu tun!
instance (EuclideanRing a, Integral a, IntegralDomain a, TestableAssociatedness a, Eq a) => HaveAnnihilatingPolynomial (ER a) where
    annihilatingPolynomial = fmap unsafeFromRatio . charPoly . fmap toRatio
	where
	toRatio = (% unit)
	unsafeFromRatio z =
	    let (p,q) = (numerator z, denominator z)
		(r,s) = p `quotRem` q
	    in  if s == 0 then r else error $ "unsafeFromRatio"
-}

instance (Field a, IntegralDomain a, Eq a) => HaveAnnihilatingPolynomial (F a) where
    annihilatingPolynomial = minPoly

t x = trace (show x) $ x
t' x = trace (pretty $ fmap (/= zero) $ unMatrix x) $ x
    where
    pretty = map f . elems
    f True  = '*'
    f False = ' '
t'' s m = trace (s ++ prettyMatrix m) $ m

determinant :: (EuclideanRing a, Eq a, TestableAssociatedness a) => SqMatrix a -> a
determinant mtx
    | numRows mtx == 0 = unit
    | null badCols     = (mtx !! (0,0)) * determinant mtx'
    | otherwise        = determinant $ makeZeroInFirstRow (head badCols) mtx
    where
    badCols = [j | j <- [1..numCols mtx - 1], mtx !! (0,j) /= zero]
    mtx'    = deleteRow 0 . deleteColumn 0 $ mtx

-- ist normiert.
charPoly :: (Field a, IntegralDomain a, Eq a) => SqMatrix a -> Poly a
charPoly = unER . determinant . fmap ER . lambdaMatrix

-- ist normiert.
minPoly :: (Field a, IntegralDomain a, Eq a) => SqMatrix a -> Poly a
minPoly = norm . last . map unER . elementaryDivisors . fmap ER . lambdaMatrix

lambdaMatrix :: (Ring a) => SqMatrix a -> SqMatrix (Poly a)
lambdaMatrix (MkMatrix arr) =
    fromArray $ accum (+) (fmap (negate . constant) arr) [((i,i), iX) | i <- [0..fst (snd (bounds arr))]]

exMatrix :: Matrix Rational
exMatrix = MkMatrix $ listArray ((0,0), (3,3)) [18, 12, 24, 42,  7, 9, 7, 3,  10, 12, 7, 10, 4, -6, 9, 10]

exMatrix2 :: Matrix Rational
exMatrix2 = MkMatrix $ listArray ((0,0), (3,3)) $ repeat 1  -- [1,1,1, 1,1,1, 1,1,1]

exMatrix3 :: Matrix Integer
exMatrix3 = MkMatrix $ listArray ((0,0), (3,3)) [18, 12, 24, 42,  7, 9, 7, 3,  10, 12, 7, 10, 4, -6, 9, 10]

exMatrix4 :: Matrix Integer
exMatrix4 = MkMatrix $ listArray ((0,0), (2,2)) [5,0,0, 0,3,0, 0,0,7]

exMatrix5 :: Matrix Rational
exMatrix5 = MkMatrix $ listArray ((0,0), (3,3)) [5,0,0,0, 0,5,1,0, 0,0,5,0, 0,0,0,4]
