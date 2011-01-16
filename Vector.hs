{-# LANGUAGE RankNTypes #-}
module Vector where

import TypeLevel

newtype Vector n a = MkVector { unVector :: [a] }
    deriving (Show,Eq)

emptyVector :: Vector Z a
emptyVector = MkVector []

cons :: (N n) => a -> Vector n a -> Vector (S n) a
cons x (MkVector xs) = MkVector (x:xs)

fromList :: (forall n. (N n) => Vector n a -> r) -> [a] -> r
fromList cc []     = cc emptyVector
fromList cc (x:xs) = flip fromList xs $ cc . cons x
