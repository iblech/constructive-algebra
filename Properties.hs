{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Properties where

import Prelude hiding (gcd, quotRem, (+), (*), (^), (/), (-), fromInteger, negate, recip)
import NumericHelper
import ComplexRational
import Euclidean
import Ring
import Field
import Polynomial
import Complex hiding (goldenRatio, sqrt2)
import IntegralClosure

import Control.Monad
import Test.QuickCheck
import Debug.Trace

positive :: (Num a, Ord a, Arbitrary a) => Gen a
positive = do
    x <- arbitrary
    if x == 0
        then return 1
        else return $ abs x

instance Arbitrary ComplexRational where
    arbitrary = liftM (uncurry (:+:)) arbitrary
    shrink    = map   (uncurry (:+:)) . shrink . (\(x :+: y) -> (x,y))

instance (Arbitrary a) => Arbitrary (Poly a) where
    arbitrary = liftM MkPoly arbitrary

newtype RejectZero a = MkRejectZero a
    deriving (Show,Eq,Num,Fractional,Ring,IntegralDomain,Field)

instance (Ring a, Eq a, Arbitrary a) => Arbitrary (RejectZero a) where
    arbitrary = do
        x <- arbitrary
        return $ if x == zero
            then MkRejectZero unit
            else MkRejectZero x
    shrink (MkRejectZero x) = map MkRejectZero . shrink $ x


-- NumerNumicHelper


-- XXX: fehlt: magnitudeSq, magnitudeUpperBound


-- Ring


-- Euclidean


-- IntegralClosure


main = do
    mapM_ check  prop_roundDownToRecipN
    mapM_ check  prop_ilogb
    mapM_ check  $ prop_field (undefined :: ComplexRational)
    mapM_ check  $ prop_testableAssociatedness (undefined :: Integer)
    mapM_ check  $ prop_testableAssociatedness (undefined :: Rational)
    mapM_ check  prop_euclideanRingInteger
    mapM_ check' $ prop_euclideanRing (undefined :: Poly Rational)
    mapM_ check' $ prop_integralClosure
    where
    check  = quickCheckWith (stdArgs { maxSuccess = 1000, maxSize = 10000 })
    check' = quickCheckWith (stdArgs { maxSuccess = 100,  maxSize = 20 })
