{-# LANGUAGE FlexibleInstances #-}
module NormedRing
    ( NormedRing(..)
    , props_normUpperBound, check_NormedRing
    ) where

import Data.Ratio

import NumericHelper (PositiveRational)
import Proxy
import Ring
import Testing
import Nondet
import MetricSpace

-- | Klasse für Ringe mit Norm, wie beispielsweise 'Rational' und
-- 'ComplexRational'. Die Normstruktur soll mit der Metrikstruktur
-- verträglich sein, d.h. es soll gelten:
-- 
-- > norm(x) <= q  <==>  d(x,0) <= q.
class (Ring a, MetricSpace a) => NormedRing a where
    -- | Liefert nicht-deterministisch eine obere Schranke für die Norm einer
    -- Zahl, der monadische Ausdruck
    --
    -- > do { q <- normUpperBound x; return (norm x q); }
    --
    -- soll also stets zu /True/ evaluieren.
    normUpperBound :: a -> R NonnegativeRational
    normUpperBound = distUpperBound zero

class (NormedRing a, DecidableMetricSpace a) => DecidableNormedRing a where
    -- | /norm q x/ soll genau dann wahr sein, wenn die Norm von /x/
    -- kleinergleich /q/ ist.
    norm :: NonnegativeRational -> a -> Bool
    norm = flip dist zero

class (NormedRing a, LocatedMetricSpace a) => LocatedNormedRing a where
    

instance NormedRing (Ratio Integer)

props_normUpperBound :: (NormedRing a, Arbitrary a, Show a) => Proxy a -> [Property]
props_normUpperBound proxy = (:[]) $ forAll arbitrary $ \x ->
    let _ = x `asTypeOf` unProxy proxy
	d = unsafeRunR $ normUpperBound x
    in  d > 0 && norm x d

check_NormedRing :: IO ()
check_NormedRing = mapM_ quickCheck $ concat
    [ props_normUpperBound (undefined :: Proxy Rational)
    ]
