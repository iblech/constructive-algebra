module Main where

import Prelude (print, ($), (.), flip, tail)
import Data.List hiding (sum)
import IntegralClosure
import Ring
import Complex hiding (goldenRatio)
import Algebraic as A
import Control.Monad
import ZeroRational
import Factoring
import Galois
import Data.List (map)
import Polynomial
import System.IO.Unsafe
import System.IO
import Field

--main = print =<< runR (ex exPoly)
--main = mapM_ print $ map (map approx) $ galoisGroup $ rootsA $ iX^4 - fromRational 10*iX^2 + unit
--main = mapM_ print $ map (map approx) $ galoisGroup $ rootsA $ iX^2 - unit - unit
--main = mapM_ print $ (map approx) $ rootsA $ iX^2 - unit - unit

--main = print $ minimalPolynomial' $ A.eval u (iX^4)
--    where u = A.sqrt2 + A.goldenRatio

--main = print $ irreducibleFactors $ iX^9 - fromInteger 243 * iX^3
--main = mapM_ print $ map (unsafePerformIO . runR . flip unComplex 10000 . number . unAlg) $ rootsA $ iX^3 - fromRational 2

--main = print (approx z) >> print (polynomial . unAlg $ z) where z = foldl1 primitiveElement $ tail $ rootsA $ iX^3 - unit - unit
--main = print $ approx $ foldl1 primitiveElement $ tail $ rootsA $ iX^4 + unit

main = do
    let [a,b,c] = rootsA $ iX^3 + unit
        (as,t)  = pseudoResolvent [a,b]
    print $ approx t
    print $ polynomial . unAlg $ t
    putStrLn ""
    print $ as

main' = do
    print $ sum
        [ windingNumber (-4*imagUnit) (5-4*imagUnit) ex
        , windingNumber (5-4*imagUnit) (5 + 4*imagUnit) ex
        , windingNumber (5 + 4*imagUnit) (4*imagUnit) ex
        , windingNumber (4*imagUnit) (-4*imagUnit) ex
        ]
    print $ minimalPolynomial $ imagUnit^6

main'' = do
    let z1 = IntegralClosure.sqrt2
	z2 = z1 * z1
	z3 = z2 * z1
	z4 = z2 * z2
	z5 = z3 * z2
	z6 = z3 * z3
    print $ polynomial z1
    print $ polynomial z2
    print $ polynomial z3
    print $ polynomial z4
    print $ polynomial z5
    print $ polynomial z6
    print $ polynomial $ IntegralClosure.sqrt2^3 + IntegralClosure.goldenRatio
    print $ polynomial $ IntegralClosure.sqrt2^3 - IntegralClosure.goldenRatio*fromRational 3
    let z = (A.sqrt2 + A.goldenRatio)^2 - A.goldenRatio^2 - fromRational 2 * A.sqrt2 * A.goldenRatio
    print $ polynomial $ unAlg $ z
    print $ isRational z
