{-# LANGUAGE GeneralizedNewtypeDeriving, RankNTypes, MultiParamTypeClasses #-}
module Matrix where

import Prelude hiding ((!!))

import TypeLevel
import Polynomial

import Data.Array
import Control.Arrow ((***))

newtype Matrix n m a = MkMatrix { unMatrix :: Array (Nat,Nat) a }
    deriving (Show,Eq,Functor)

type SqMatrix n a = Matrix n n a

(!!) :: Matrix n m a -> (Nat,Nat) -> a
(!!) m ij = unMatrix m ! ij

emptySqMatrix :: SqMatrix Z a
emptySqMatrix = MkMatrix $ array ((0,0),(-1,-1)) []

fromArray :: (forall n m. (Determinantable n, Determinantable m) => Matrix n m a -> r) -> Array (Nat,Nat) a -> r
fromArray cc arr = reflect' (n+1) $ \n' -> reflect' (m+1) $ \m' -> cc (MkMatrix arr `asTypeOf` dummy n' m')
    where
    dummy = undefined :: n -> m -> Matrix n m a
    ((0,0), (n,m)) = bounds arr
    reflect' :: Nat -> (forall n. (Determinantable n) => n -> r) -> r
    reflect' 0 cc         = cc (undefined :: Z)
    reflect' n cc | n > 0 = reflect' (pred n) $ cc . (undefined :: m -> S m)

unsafeSquare :: Matrix n m a -> Matrix n n a
unsafeSquare (MkMatrix arr)
    | n == m    = MkMatrix arr
    | otherwise = error "unsafeSquare on non-square matrix!"
    where
    ((0,0), (n,m)) = bounds arr

numRows :: (N n, N m) => Matrix n m a -> Int
numRows = reify . (undefined :: Matrix n m a -> n)

deleteRow :: (N n, N m) => Nat -> Matrix (S n) m a -> Matrix n m a
deleteRow a (MkMatrix matrix)
    | a <= n    = MkMatrix $ ixmap ((0,0), (n-1,m)) f matrix
    | otherwise = error "deleteRow"
    where
    ((0,0), (n,m)) = bounds matrix
    f (i,j)
	| i  < a = (i,j)
	| i >= a = (i+1,j)

deleteColumn :: (N n, N m) => Nat -> Matrix n (S m) a -> Matrix n m a
deleteColumn a = transpose . deleteRow a . transpose

transpose :: (N n, N m) => Matrix n m a -> Matrix m n a
transpose (MkMatrix m) = MkMatrix $ ixmap ((id *** swap) (bounds m)) swap m
    where swap (i,j) = (j,i)

ex :: Matrix N3 N2 Double
ex = MkMatrix $ listArray ((0,0), (2,1)) [1..]

ex2 :: Matrix N3 N3 Double
ex2 = MkMatrix $ listArray ((0,0), (2,2)) [1,2,3, 4,5,6, 1,1,10]

class (N n) => Determinantable n where
    determinant :: (Num a) => SqMatrix n a -> a

instance Determinantable Z where
    determinant _ = 1

instance (Determinantable n) => Determinantable (S n) where
    determinant m = sum $ map f [0..numRows m - 1]
	where
	f i = (-1)^i * (m !! (0,i)) * determinant (deleteColumn i m')
	m'  = deleteRow 0 m

charPoly :: (Determinantable n, Num a) => SqMatrix n a -> Poly a
charPoly m@(MkMatrix arr) = determinant (MkMatrix arr' `asTypeOf` fmap constant m)
    where
    arr' = accum (+) (fmap (negate . constant) arr) [((i,i), iX) | i <- [0..fst (snd (bounds arr))]]
