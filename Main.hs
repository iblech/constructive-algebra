module Main where

import Prelude (print, ($))
import IntegralClosure
import Ring
import Complex hiding (goldenRatio)

main = do
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
    print $ polynomial $ IntegralClosure.sqrt2^3 - IntegralClosure.goldenRatio*3
