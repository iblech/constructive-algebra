module Smith where

import Matrix
import Data.Array
import TypeLevel

makeZero :: (N n, N m, Num a) => (a -> a -> (a,a,a,a)) -> Nat -> Matrix n m a -> Matrix n m a
makeZero ggT j mtx@(MkMatrix arr) = MkMatrix (arr // updates) `asTypeOf` mtx
    where
    (u,v,s,t) = ggT (arr ! (0,0)) (arr ! (0,j))
    updates   = do
	i <- [0..n-1]
	let (x,y) = (arr ! (i,0), arr ! (i,j))
	[ ((i,0), u*x + v*y), ((i,j), -t*x + s*y) ]
    ((0,0),(n,m)) = bounds arr

exMatrix :: Matrix N4 N4 Integer
exMatrix = MkMatrix $ listArray ((0,0), (3,3)) [18, 12, 24, 42,  7, 9, 7, 3,  10, 12, 7, 10, 4, -6, 9, 10]
