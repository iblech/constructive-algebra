module Algebraic where

import Complex
import Polynomial

data Algebraic = MkAlgebraic { number :: Complex, polynomial :: NormedPoly Rational }

instance Eq   Algebraic where (==) = undefined
instance Show Algebraic where show = undefined

instance Num Algebraic where
    MkAlgebraic x p + MkAlgebraic x' p' =
	MkAlgebraic (x + x') (sumPolynomial p p')

    fromInteger i = MkAlgebraic (fromInteger i) $ MkPoly [-fromInteger i]

sumPolynomial :: (Num a) => NormedPoly a -> NormedPoly a -> NormedPoly a
sumPolynomial (MkPoly xs) (MkPoly ys) = undefined
    where
    indices = [ (i,j) | i <- [0..length xs], j <- [0..length ys] ]
