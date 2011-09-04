module Main where

import Prelude (print, ($))
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

--main = print =<< runR (ex exPoly)
--main = mapM_ print $ map (map approx) $ galoisGroup $ rootsA $ iX^4 - fromRational 10*iX^2 + unit
--main = mapM_ print $ map (map approx) $ galoisGroup $ rootsA $ iX^3 + unit

main = print $ irreducibleFactors $ iX^6 - (unit+unit+unit)


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
