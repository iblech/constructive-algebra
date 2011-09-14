module Testing
    ( module Test.QuickCheck
    , positive
    ) where

import Test.QuickCheck

positive :: (Num a, Ord a, Arbitrary a) => Gen a
positive = do
    x <- arbitrary
    if x == 0
        then return 1
        else return $ abs x
