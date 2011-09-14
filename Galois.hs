{-# LANGUAGE TupleSections, PatternGuards #-}
module Galois where

import Prelude hiding ((+), (*), (/), (-), (^), negate, fromInteger, fromRational, recip, signum, sum, product, quotRem, gcd)
import Ring
import Field
import Polynomial as Poly
import Factoring
import Data.List hiding (sum,product)
import Complex
import IntegralClosure
import ZeroRational
import Algebraic as A
import Control.Monad
import Data.Maybe
import Debug.Trace
import NumericHelper
import IdealExtension as I
import IdealEuclidean
import Euclidean

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

-- normiert, separabel
galoisGroup :: Poly Rational -> ([Alg QinC], [[Int]])
galoisGroup f
    | Just (g,h) <- isIrreducible f
    = let (xs,gs) = galoisGroup g
          (ys,hs) = galoisGroup h
          n       = length (head gs)  -- Anzahl Nullstellen von f
      in  (xs ++ ys, [ sigma ++ map (n +) tau | sigma <- gs, tau <- hs ])
    | otherwise
    = galoisGroup' f

-- normiert, separabel
galoisGroup' :: Poly Rational -> ([Alg QinC], [[Int]])
galoisGroup' f = trace debugMsg $ (xs, sigmas)
    where
    xs         = map simplify' $ rootsA f
    (res,t,hs) = pseudoResolvent (tail xs)
    res'       = 0:res
    hs'        = negate (sum hs + Poly.fromBase a) : hs where a = (!! 1) . reverse . canonCoeffs $ f
    t'         = t  -- simplify' unnötig
    m          = unNormedPoly . fmap unF . polynomial . unAlg $ t'  -- Minimalpolynom von t
    conjs      = rootsA m
    inds       = [0..length xs - 1]
    sigmas     =
        flip map conjs $ \t0 ->
            flip map inds $ \i ->
                head [ j | j <- inds, xs !! j == A.eval t0 (hs' !! i) ]
    debugMsg = concat $ intersperse "\n"
        [ "Zur Galoisgruppe von: " ++ show f
        , "Nullstellen:          " ++ show (map approx xs)
        , "Prim. Element:        " ++ show res' ++ " * xs ~~ " ++ show (approx t')
        , "Min. Polynom:         " ++ show m
        , "Gal. Konjugierte:     " ++ show (map approx conjs)
        ]

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

-- für Effizienz sollte y kleineren Grad haben.
primitiveElement :: Alg QinC -> Alg QinC -> (Integer, Alg QinC, Poly Rational, Poly Rational)
primitiveElement x y = (lambda, t, hX, hY)
    where
    f = unNormedPoly . fmap unF . polynomial . unAlg $ x
    g = squarefreePart . unNormedPoly . fmap unF . polynomial . unAlg $ y
    -- Nst. der Minimalpolynome würden genügen
    exceptions :: [Integer]
    exceptions = do
        x' <- rootsA f
        y' <- rootsA g
        r  <- maybeToList $ unsafeRunR $ invert (y - y')
        maybeToList $ isApproxInteger $ (x' - x) * r
    lambda = head $ filter (\q -> all (/= q) exceptions) allIntegers
    t = x + fromInteger lambda * y
    hY = runISEwithAlgebraic t $ do
        let h = fmap I.fromBase f `compose` (Poly.fromBase adjointedRoot - fromInteger lambda * iX)
        d <- idealNormedGCD (fmap I.fromBase g) h
        liftM negate . canonISE . head . unsafeCoeffs $ d
    hX = iX - fromInteger lambda * hY

-- garantiert, dass das zurückgegebene prim. Element bereits simplify'-ed wurde.
pseudoResolvent :: [Alg QinC] -> ([Integer], Alg QinC, [Poly Rational])
pseudoResolvent []       = ([],  zero,        [])
pseudoResolvent [x]      = ([1], simplify' x, [iX])
pseudoResolvent (x:y:zs) =
    let (lambda, u, hX, hY) = primitiveElement x y
        u'                  = trace ("vor simplify: " ++ show (polynomial .  unAlg $ u)) $ simplify' u
        (as, t, hU:hs)      = pseudoResolvent (u':zs)
        -- zipWith (*) as (u':zs) = t,  (hs !! i)(t) = (u':zs) !! i
        reduce p = snd (p `quotRem` unNormedPoly (fmap unF (polynomial . unAlg $ t)))
    in  (1 : lambda : tail as, t, reduce (hX `compose` hU) : reduce (hY `compose` hU) : hs)

merge :: [a] -> [a] -> [a]
merge []     ys = ys
merge (x:xs) ys = x : merge ys xs

cross :: (a -> b -> r) -> [a] -> [b] -> [r]
cross (#) []     _  = []
cross (#) (x:xs) ys = map (x #) ys `merge` cross (#) xs ys

crossN :: [[a]] -> [[a]]
crossN []       = [[]]
crossN (xs:xss) = cross (:) xs (crossN xss)
