module Main where

import Algebraic
import Complex hiding (goldenRatio)

main = do
    let z = Algebraic.sqrt2^4
    print $ polynomial z
    print $ z == 4
