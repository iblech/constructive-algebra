{-# LANGUAGE GeneralizedNewtypeDeriving, RankNTypes, MultiParamTypeClasses #-}
module Matrix where

import Prelude hiding ((!!))

import TypeLevel
import Polynomial

import Data.Array
import Control.Arrow ((***))

newtype Matrix a = MkMatrix { unMatrix :: Array (Nat,Nat) a }
    deriving (Show,Eq,Functor)

type SqMatrix a = Matrix a

(!!) :: Matrix a -> (Nat,Nat) -> a
(!!) m ij = unMatrix m ! ij

emptySqMatrix :: SqMatrix a
emptySqMatrix = MkMatrix $ array ((0,0),(-1,-1)) []

fromArray :: Array (Nat,Nat) a -> Matrix a
fromArray = MkMatrix

numRows :: Matrix a -> Int
numRows = succ . fst . snd . bounds . unMatrix

numCols :: Matrix a -> Int
numCols = succ . snd . snd . bounds . unMatrix

deleteRow :: Nat -> Matrix a -> Matrix a
deleteRow a (MkMatrix matrix)
    | a <= n    = MkMatrix $ ixmap ((0,0), (n-1,m)) f matrix
    | otherwise = error "deleteRow"
    where
    ((0,0), (n,m)) = bounds matrix
    f (i,j)
	| i  < a = (i,j)
	| i >= a = (i+1,j)

deleteColumn :: Nat -> Matrix a -> Matrix a
deleteColumn a = transpose . deleteRow a . transpose

transpose :: Matrix a -> Matrix a
transpose (MkMatrix m) = MkMatrix $ ixmap ((id *** swap) (bounds m)) swap m
    where swap (i,j) = (j,i)

ex :: Matrix Double
ex = MkMatrix $ listArray ((0,0), (2,1)) [1..]

ex2 :: Matrix Double
ex2 = MkMatrix $ listArray ((0,0), (2,2)) [1,2,3, 4,5,6, 1,1,10]

{-
determinant :: (Num a) => SqMatrix a -> a
determinant m
    | numRows m /= numCols m = error "determinant on non-square matrix>"
    | numRows m == 0         = 1
    | otherwise              = sum $ map f [0..numRows m - 1]
    where
    f i = (-1)^i * (m !! (0,i)) * determinant (deleteColumn i m')
    m'  = deleteRow 0 m

charPoly :: (Num a) => SqMatrix a -> Poly a
charPoly m@(MkMatrix arr) = determinant (MkMatrix arr' `asTypeOf` fmap constant m)
    where
    arr' = accum (+) (fmap (negate . constant) arr) [((i,i), iX) | i <- [0..fst (snd (bounds arr))]]
-}
