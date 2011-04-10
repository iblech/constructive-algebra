{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Properties where

import Prelude hiding (gcd)
import NumericHelper
import ComplexRational

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
    arbitrary = liftM2 (:+:) arbitrary arbitrary

newtype RejectZero a = MkRejectZero a
    deriving (Show,Eq,Num,Fractional)

instance (Num a, Arbitrary a) => Arbitrary (RejectZero a) where
    arbitrary = do
        x <- arbitrary
        return $ if x == 0
            then MkRejectZero 1
            else MkRejectZero x
    shrink (MkRejectZero x) = map MkRejectZero . shrink $ x

-- NumericHelper
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

prop_gcd = 
    [ forAll (arbitrary :: Gen Integer) $ \a -> forAll arbitrary $ \b ->
        let (u,v,s,t) = gcd a b
            d         = u*a + v*b
        in  d*s == a && d*t == b
    , forAll (arbitrary :: Gen Integer) $ \a -> forAll arbitrary $ \b ->
      let (u,v,s,t) = gcd a b
          d         = u*a + v*b
      in flip all [1..min a b] $ \d' ->
      not (a `mod` d' == 0 && b `mod` d' == 0) || d `mod` d' == 0
    ]

-- XXX: rootSeq NICHT geprüft!


-- ComplexRational
prop_field :: (Fractional a, Arbitrary a) => a -> [Property]
prop_field a =
  prop_commutativeGroup (+) (0 `asTypeOf` a) negate ++
  prop_commutativeGroup (*) (1 `asTypeOf` (MkRejectZero a)) recip ++
  [ property $ \x y z -> x * (y + z) == x * y + x * (z `asTypeOf` a) ]

prop_commutativeGroup :: (Eq a, Show a, Arbitrary a) => (a -> a -> a) -> a -> (a -> a) -> [Property]
prop_commutativeGroup (+) zero negate =
  [ property $ \x y z -> x + (y + z)    == (x + y) + z
  , property $ \x     -> x + zero       == x
  , property $ \x     -> x + (negate x) == zero
  , property $ \x y   -> x + y          == y + x
  ]

-- XXX: fehlt: magnitudeSq, magnitudeBound

main = do
    mapM_ check prop_roundDownToRecipN
    mapM_ check prop_ilogb
    mapM_ check prop_gcd
    mapM_ check $ prop_field (0 :: ComplexRational)
    where check = quickCheckWith (stdArgs { maxSuccess = 1000, maxSize = 10000 })
