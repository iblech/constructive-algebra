-- | Dieses Modul re-exportiert das QuickCheck-Modul zum Testen und stellt
-- häufig verwendete Testfallgeneratoren zur Verfügung.
module Testing
    ( module Test.QuickCheck
    , positive
    , simpleRational, simpleNonzeroRational
    ) where

import Control.Monad
import Data.List ((\\))
import Data.Ratio
import Test.QuickCheck

-- | Erzeugt positive Zahlen.
positive :: (Num a, Ord a, Arbitrary a) => Gen a
positive = do
    x <- arbitrary
    if x == 0
        then return 1
        else return $ abs x

-- | Erzeugt \"einfache\" rationale Zahlen, also solche, mit nicht zu
-- großen Zählern und Nennern.
--
-- Wird verwendet, um das Ausführen der Tests praktikabel zu halten.
simpleRational :: Gen Rational
simpleRational = liftM2 (%) (elements ps) (elements qs)
    where
    ps = [-10..10]
    qs = [-10..10] \\ [0]

-- | Erzeugt \"einfache\", von Null verschiedene rationale Zahlen.
simpleNonzeroRational :: Gen Rational
simpleNonzeroRational = liftM2 (%) (elements qs) (elements qs)
    where
    qs = [-10..10] \\ [0]
