module Galois where

import Prelude hiding ((+), (*), (/), (-), (^), negate, fromInteger, fromRational, recip, signum, sum, product, quotRem, gcd)
import Ring
import Field
import Polynomial
import Factoring
import Data.List hiding (sum,product)
import Complex hiding (constant)
import IntegralClosure
import ZeroRational
import Algebraic
import Control.Monad
import Data.Maybe

linearResolvent :: (Ring a, Eq a) => [a] -> [Integer]
linearResolvent xs = head $ filter isResolvent candidates
    where
    isResolvent cs = arePairwiseDistinct $ map (evalResolvent cs) $ permutations xs
    candidates  = crossN $ replicate (length xs) allIntegers
    allIntegers = 0 : go 1 where go n = n : (-n) : go (n + 1)
    -- XXX ab 1, zur Effizienzsteigerung?
    arePairwiseDistinct [] = True
    arePairwiseDistinct (x:xs) = all (x /=) xs && arePairwiseDistinct xs

evalResolvent :: (Ring a) => [Integer] -> [a] -> a
evalResolvent cs ys = sum $ zipWith (*) (map fromInteger cs) ys

-- müssen genau die Nst. eines normierten sep. Polynoms sein
primitiveElement' :: (Ring a, Eq a) => [a] -> a
primitiveElement' xs = evalResolvent (linearResolvent xs) xs

-- Eingabe müssen genau die Nst. eines normierten sep. Polynoms sein
galoisGroup :: [Alg QinC] -> [[Alg QinC]]
galoisGroup xs = fst . head $ filter (isJust . isRationalPoly . poly . snd) (zip cands vss)
    where
    res     = linearResolvent xs
    cands   = tail . subsequences . permutations $ xs
    vss     = tail . subsequences . map (simplify' . evalResolvent res) . permutations $ xs
    poly vs = product $ map ((iX -) . constant) vs

primitiveElement :: Alg QinC -> Alg QinC -> Alg QinC
primitiveElement x y = x + fromInteger lambda * y
    where
    -- Nst. der Minimalpolynome würden genügen
    -- kann man hier optimieren? gar nicht x',y' ausrechnen, sondern
    -- nur das Polynom (von z = (x'-x) / (y-y'))?
    exceptions :: [Alg QinC]
    exceptions = do
        x' <- rootsA . fmap unF . polynomial . unAlg $ x
        y' <- rootsA . fmap unF . polynomial . unAlg $ y
	guard $ y /= y'
        return $ (x' - x) / (y - y')
    lambda = head $ filter (\q -> all (necessarilyNotEquals (fromInteger q)) exceptions) [(5::Integer)..]
    -- necessarilyNotEquals p z == True ==> p != z,
    -- Rückrichtung gilt nicht.
    necessarilyNotEquals :: Rational -> Alg QinC -> Bool
    --necessarilyNotEquals p z = eval p (fmap unF $ polynomial (unAlg z)) /= 0
    necessarilyNotEquals p z = fromRational p /= z

merge :: [a] -> [a] -> [a]
merge []     ys = ys
merge (x:xs) ys = x : merge ys xs

cross :: (a -> b -> r) -> [a] -> [b] -> [r]
cross (#) []     _  = []
cross (#) (x:xs) ys = map (x #) ys `merge` cross (#) xs ys

crossN :: [[a]] -> [[a]]
crossN []       = [[]]
crossN (xs:xss) = cross (:) xs (crossN xss)
