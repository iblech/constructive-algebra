module Main where

import Prelude (print, ($), (.), flip, tail, fst, snd)
import qualified Prelude as P
import IntegralClosure
import Ring
import Algebraic as A
import Control.Monad
import Factoring
import Galois
import Data.List (map)
import Polynomial
import System.IO

--main = print =<< runR (ex exPoly)
--main = mapM_ print $ map (map unsafeApprox) $ galoisGroup $ rootsA $ iX^4 - fromRational 10*iX^2 + unit
--main = mapM_ print $ map (map unsafeApprox) $ galoisGroup $ rootsA $ iX^2 - unit - unit
--main = mapM_ print $ (map unsafeApprox) $ rootsA $ iX^2 - unit - unit

--main = print $ minimalPolynomial' $ A.eval u (iX^4)
--    where u = A.sqrt2 + A.goldenRatio

--main = print $ irreducibleFactors $ iX^9 - fromInteger 243 * iX^3
--main = mapM_ print $ map (unsafePerformIO . runR . flip unComplex 10000 . number . unAlg) $ rootsA $ iX^3 - fromRational 2

--main = print (unsafeApprox z) >> print (polynomial . unAlg $ z) where z = foldl1 primitiveElement $ tail $ rootsA $ iX^3 - unit - unit
--main = print $ unsafeApprox $ foldl1 primitiveElement $ tail $ rootsA $ iX^4 + unit

{-
main = do
    let [a,b,c] = rootsA $ iX^3 + unit
        (as,t)  = pseudoResolvent [a,b]
    print $ unsafeApprox t
    print $ polynomial . unAlg $ t
    putStrLn ""
    print $ as
-}

main = Galois.demo

{-
main' = do
    print $ sum
        [ windingNumber (-4*imagUnit) (5-4*imagUnit) ex
        , windingNumber (5-4*imagUnit) (5 + 4*imagUnit) ex
        , windingNumber (5 + 4*imagUnit) (4*imagUnit) ex
        , windingNumber (4*imagUnit) (-4*imagUnit) ex
        ]
    print $ minimalPolynomial $ imagUnit^6
-}
