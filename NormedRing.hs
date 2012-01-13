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
-- > norm x = dist zero x
class (Ring a, MetricSpace a) => NormedRing a where
    -- | /norm x q/ ist genau dann wahr, wenn die Norm von /x/ kleinergleich
    -- /q/ ist.
    norm :: a -> PositiveRational -> Bool
    norm = dist zero

    -- | Liefert nicht-deterministisch eine obere Schranke für die Norm einer
    -- Zahl, der monadische Ausdruck
    --
    -- > do { q <- normUpperBound x; return (norm x q); }
    --
    -- soll also stets zu /True/ evaluieren.
    normUpperBound :: a -> R PositiveRational
    normUpperBound = distUpperBound zero

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
