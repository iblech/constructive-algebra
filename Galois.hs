module Galois where

import Prelude hiding ((+), (*), (/), (-), (^), negate, fromInteger, fromRational, recip, signum, sum, product, quotRem, gcd)
import Ring
import Field
import Polynomial
import Factoring
import Data.List hiding (sum)
import Complex
import IntegralClosure
import ZeroRational
import Algebraic

linearResolvent :: (Ring a, Eq a) => [a] -> [Integer]
linearResolvent xs = head $ filter isResolvent candidates
    where
    isResolvent cs = arePairwiseDistinct $ map (evalResolvent cs) $ permutations xs
    candidates  = crossN $ replicate (length xs) allIntegers
    allIntegers = 0 : go 1 where go n = n : (-n) : go (n + 1)
    arePairwiseDistinct [] = True
    arePairwiseDistinct (x:xs) = all (x /=) xs && arePairwiseDistinct xs

evalResolvent :: (Ring a) => [Integer] -> [a] -> a
evalResolvent cs ys = sum $ zipWith (*) (map fromInteger cs) ys

-- müssen genau die Nst. eines normierten sep. Polynoms sein
primitiveElement' :: (Ring a, Eq a) => [a] -> a
primitiveElement' xs = evalResolvent (linearResolvent xs) xs

primitiveElement :: Alg QinC -> Alg QinC -> Alg QinC
primitiveElement x y = x + fromInteger lambda * y
    where
    -- Nst. der Minimalpolynome würden genügen
    exceptions :: [Rational]
    exceptions = do
        x' <- rootsA . polynomial . unAlg $ x
        y' <- rootsA . polynomial . unAlg $ y
        let z = (x' - x) / (y - y')
        -- Test unnötig, da wir eh nur rat. Zahlen nehmen [Just q] <- [isRational
        -- XXX: doch, test besser? oder lieber isEqualToRational?
        return q
    lambda = head $ filter ((`notElem` exceptions) . fromInteger) [(0::Integer)..]

merge :: [a] -> [a] -> [a]
merge []     ys = ys
merge (x:xs) ys = x : merge ys xs

cross :: (a -> b -> r) -> [a] -> [b] -> [r]
cross (#) []     _  = []
cross (#) (x:xs) ys = map (x #) ys `merge` cross (#) xs ys

crossN :: [[a]] -> [[a]]
crossN []       = [[]]
crossN (xs:xss) = cross (:) xs (crossN xss)
