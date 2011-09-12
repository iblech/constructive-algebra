{-# LANGUAGE TupleSections #-}
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
import Algebraic as A
import Control.Monad
import Data.Maybe
import Debug.Trace
import NumericHelper

-- Vor.: f normiert, separabel
linearResolvent :: Poly Rational -> R [Integer]
linearResolvent f = do
    bounds' <- sequence bounds
    let csq = foldl' max 1 bounds'
        c   = fromIntegral n * (squareRoot csq + 1)
    return $ take n $ let as = 1 : map (c*) as in as
    where
    xs     = map (number . unAlg) $ rootsA f
    n      = length xs
    bounds = do
        (a,b) <- pairs xs
        (u,v) <- pairs xs
        let q = magnitudeUpperBound $ absSq ((a - b) * recip' (u - v))
        return $ liftM roundUp q

galoisGroup :: Poly Rational -> [[Int]]
galoisGroup f = map (map fst . fst) . filter (isRoot . snd) $ vs
    where
    xs       = rootsA f
    (res,t)  = pseudoResolvent (tail xs)
    res'     = 0:res
    m        = fmap unF . polynomial . unAlg $ t  -- Minimalpolynom von t
    ps       = permutations $ zip [0..] xs
    vs       = flip map ps $ \sigma -> (sigma, evalResolvent res' (map snd sigma))
    isRoot v = trace ("versuche wurzel: " ++ show (approx v)) $ A.eval v m == zero

{-

galoisGroup :: Poly Rational -> [[Int]]
galoisGroup f =
    res <- linearResolvent f
    let cands = tail . subsequences . permutations $ [0..length as-1]
        vss   = tail . subsequences . map (evalResolvent res) . permutations
galoisGroup xs = fst . head $ filter (isJust . isRationalPoly . poly . snd) (zip cands vss)
    where
    cands   = tail . subsequences . permutations $ xs
    vss     = tail . subsequences . map (simplify' . evalResolvent res) . permutations $ xs
    poly vs = product $ map ((iX -) . constant) vs
-}   

pairs :: [a] -> [(a,a)]
pairs []       = []
pairs (x:xs)   = map (x,) xs ++ pairs xs


{-
head $ filter isResolvent candidates
    where
    isResolvent cs = arePairwiseDistinct $ map (evalResolvent cs) $ permutations xs
    candidates  = filter arePairwiseDistinct' $ crossN $ replicate (length xs) allIntegers
    -- XXX ab 1, zur Effizienzsteigerung?
    arePairwiseDistinct xs = arePairwiseDistinct' xs
    arePairwiseDistinct' [] = True
    arePairwiseDistinct' (x:xs) = all (x /=) xs && arePairwiseDistinct' xs
-}

allIntegers :: [Integer]
allIntegers = 0 : go 1 where go n = n : (-n) : go (n + 1)

evalResolvent :: (Ring a) => [Integer] -> [a] -> a
evalResolvent cs ys = sum $ zipWith (*) (map fromInteger cs) ys
{-

-- müssen genau die Nst. eines normierten sep. Polynoms sein
primitiveElement' :: (ApproxFloating a, Ring a, Eq a) => [a] -> a
primitiveElement' xs = evalResolvent (linearResolvent xs) xs

-- Eingabe müssen genau die Nst. eines normierten sep. Polynoms sein
galoisGroup :: [Alg QinC] -> [[Alg QinC]]
galoisGroup xs = fst . head $ filter (isJust . isRationalPoly . poly . snd) (zip cands vss)
    where
    res     = linearResolvent xs
    cands   = tail . subsequences . permutations $ xs
    vss     = tail . subsequences . map (simplify' . evalResolvent res) . permutations $ xs
    poly vs = product $ map ((iX -) . constant) vs
-}


-- für Effizienz sollte y kleineren Grad haben.
primitiveElement :: Alg QinC -> Alg QinC -> (Integer, Alg QinC)
primitiveElement x y = (lambda, x + fromInteger lambda * y)
    where
    -- Nst. der Minimalpolynome würden genügen
    exceptions :: [Integer]
    exceptions = do
        x' <- rootsA . fmap unF . polynomial . unAlg $ x
        y' <- rootsA . fmap unF . polynomial . unAlg $ y
        r  <- maybeToList $ unsafeRunR $ invert (y - y')
        maybeToList $ isApproxInteger $ (x' - x) * r
    lambda = head $ filter (\q -> all (/= q) exceptions) allIntegers

pseudoResolvent :: [Alg QinC] -> ([Integer], Alg QinC)
pseudoResolvent []       = ([],  zero)
pseudoResolvent [x]      = ([1], x)
pseudoResolvent (x:y:zs) =
    let (lambda, u) = primitiveElement x y
        u'          = simplify' $ trace ("vor simplify: " ++ show (polynomial .  unAlg $ u)) $ u
        (as, t)     = pseudoResolvent (u':zs)
        -- zipWith (*) as (u':zs) = t
    in  (1 : lambda : tail as, t)

merge :: [a] -> [a] -> [a]
merge []     ys = ys
merge (x:xs) ys = x : merge ys xs

cross :: (a -> b -> r) -> [a] -> [b] -> [r]
cross (#) []     _  = []
cross (#) (x:xs) ys = map (x #) ys `merge` cross (#) xs ys

crossN :: [[a]] -> [[a]]
crossN []       = [[]]
crossN (xs:xss) = cross (:) xs (crossN xss)
