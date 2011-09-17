{-# LANGUAGE FlexibleInstances #-}
module NormedRing where

import Ring
import Data.Ratio
import Proxy
import Testing

-- | Approximation an den Typ nichtnegativer rationaler Zahlen.
type NonnegativeRational = Rational

-- | Klasse für Ringe mit Norm, wie beispielsweise 'Rational' und
-- 'ComplexRational'.
class (Ring a) => NormedRing a where
    -- | Gewöhnlich erwartet man ja von einer Norm, dass sie jedem Element
    -- ihre Länge als reelle Zahl zuordnet.
    -- Diese Definition ist für unsere Zwecke aber nicht geeignet, da wir die
    -- reellen Zahlen erst durch einen geeigneten Vervollständigungsprozess aus
    -- den rationalen Zahlen erhalten wollen.
    --
    -- Die Anschauung hinter unserer Definition ist folgende: /norm x q/
    -- soll genau dann wahr sein, wenn die Länge von /x/ kleinergleich /q/ ist.
    norm :: a -> NonnegativeRational -> Bool

    -- | Liefert eine obere Schranke für die Norm einer Zahl, es soll also
    -- folgende Spezifikation erfüllt sein:
    --
    -- > norm x (normUpperBound x) == True.
    normUpperBound :: a -> NonnegativeRational

instance NormedRing (Ratio Integer) where
    norm x q = abs x <= q
    normUpperBound = abs

props_normUpperBound :: (NormedRing a, Arbitrary a, Show a) => Proxy a -> [Property]
props_normUpperBound proxy = (:[]) $ forAll arbitrary $ \x ->
    let _ = x `asTypeOf` unProxy proxy
    in  normUpperBound x >= 0 && norm x (normUpperBound x)

props_NormedRing :: [Property]
props_NormedRing = props_normUpperBound (undefined :: Proxy Rational)
