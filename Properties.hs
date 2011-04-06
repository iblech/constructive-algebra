module Properties where

import Prelude hiding (gcd)
import NumericHelper

import Test.QuickCheck
import Debug.Trace

positive :: (Num a, Ord a, Arbitrary a) => Gen a
positive = do
    x <- arbitrary
    if x == 0
        then return 1
        else return $ abs x

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

main = do
    mapM_ check prop_roundDownToRecipN
    mapM_ check prop_ilogb
    mapM_ check prop_gcd
    where check = quickCheckWith (stdArgs { maxSuccess = 1000, maxSize = 10000 })
