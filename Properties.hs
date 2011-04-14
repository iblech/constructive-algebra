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
import RootFinding

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
prop_roundDownToRecipN =
    [ forAll positive $ \x ->
        let n = roundDownToRecipN x
        in  recip (fromInteger n) < x
    , forAll positive $ \x -> forAll positive $ \n' ->
        recip (fromInteger n') < x ==> n' >= roundDownToRecipN x
    ]

prop_ilogb = (:[]) $ forAll positive $ \b -> forAll positive $ \n ->
    b > 1 ==>
    let k = ilogb b n
    in  b^k <= n && b^(k+1) > n

prop_roundUp =
    [ property $ \x ->
        x <= fromInteger (roundUp x)  &&  fromInteger (roundUp x) - x <= 1
    ]

-- XXX: rootSeq NICHT geprüft!


-- ComplexRational
prop_field :: (Field a, Eq a, Show a, Arbitrary a) => a -> [Property]
prop_field a =
    prop_commutativeGroup (+) (zero `asTypeOf` a) negate ++
    prop_commutativeGroup (*) (unit `asTypeOf` (MkRejectZero a)) recip ++
    [ property $ \x y z -> x * (y + z) == x * y + x * (z `asTypeOf` a) ]

prop_commutativeGroup :: (Eq a, Show a, Arbitrary a) => (a -> a -> a) -> a -> (a -> a) -> [Property]
prop_commutativeGroup (+) zero negate =
    [ property $ \x y z -> x + (y + z)    == (x + y) + z
    , property $ \x     -> x + zero       == x
    , property $ \x     -> x + (negate x) == zero
    , property $ \x y   -> x + y          == y + x
    ]

-- XXX: fehlt: magnitudeSq, magnitudeUpperBound


-- Ring
prop_testableAssociatedness :: (TestableAssociatedness a, Eq a, Show a, Arbitrary a) => a -> [Property]
prop_testableAssociatedness a =
    [ property $ \x y ->
        case areAssociated x y of
            Nothing -> True  -- ungenau
            Just u  -> y == u * x
                where _ = x `asTypeOf` a
    ]


-- Euclidean
prop_euclideanRing :: (EuclideanRing a, Eq a, Show a, Arbitrary a) => a -> [Property]
prop_euclideanRing x =
    [ property $ \a b -> b /= zero ==>
          let (q,r) = a `quotRem` b
              _     = a `asTypeOf` x
          in   a == b * q + r  &&  (r == zero || degree r < degree b)
    , property $ \a b ->
          let (u,v,s,t) = gcd a b
              d         = u*a + v*b
              _         = a `asTypeOf` x
          in  d*s == a && d*t == b
    ]

prop_euclideanRingInteger :: [Property]
prop_euclideanRingInteger = prop_euclideanRing (0 :: Integer) ++
    [ property $ \a b ->
          let (u,v,s,t) = gcd a b
              d         = u*a + v*b
              _         = a `asTypeOf` (0 :: Integer)
          in flip all [1..min a b] $ \d' ->
          not (a `mod` d' == 0 && b `mod` d' == 0) || d `mod` d' == 0
    ]


-- IntegralClosure
prop_integralClosure :: [Property]
prop_integralClosure =
    map complexNumberTest [sqrt2, goldenRatio, sqrt2 + goldenRatio]
    where
    complexNumberTest z = property $
        let approx = unsafeRunR $ unComplex (verifyPolynomial z) n
        in  magnitudeSq approx < recip (fromInteger (n^2))
    n = 1000


-- RootFinding
prop_mesh :: [Property]
prop_mesh =
    [ forAll positive $ \r -> forAll positive $ \delta -> r / delta < 15 ==>
        let ps = mesh delta r
        in  property $ \z ->
            magnitudeSq z <= r^2  ==>  any (\p -> magnitudeSq (p - z) < delta^2) ps
    ]


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
