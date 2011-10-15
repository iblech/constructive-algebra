module Testing
    ( module Test.QuickCheck
    , positive
    , simpleRational, simpleNonzeroRational
    ) where

import Test.QuickCheck
import Control.Monad
import Data.Ratio
import Data.List ((\\))

positive :: (Num a, Ord a, Arbitrary a) => Gen a
positive = do
    x <- arbitrary
    if x == 0
        then return 1
        else return $ abs x

simpleRational :: Gen Rational
simpleRational = liftM2 (%) (elements ps) (elements qs)
    where
    ps = [-10..10]
    qs = [-10..10] \\ [0]

simpleNonzeroRational :: Gen Rational
simpleNonzeroRational = liftM2 (%) (elements qs) (elements qs)
    where
    qs = [-10..10] \\ [0]
