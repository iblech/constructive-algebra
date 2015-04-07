module ContinuedFractions where

import Prelude hiding ((+), (-), (*), (/), (^), negate, recip, fromRational, quotRem, fromInteger)
import Ring
import Field
import Algebraic
import IntegralClosure hiding (goldenRatio,sqrt2)
import Complex         hiding (goldenRatio,sqrt2)

-- | Berechnet die Abrundung einer reellen algebraischen Zahl. Terminiert
-- auf jeder Eingabe.
floor' :: Alg QinR -> Integer
floor' z = go y
    where
    x = unsafeRunR $ approx 1 $ number . unAlg $ z
    y = floor (x - 1/1) :: Integer
    -- y ist eine Ganzzahl mit y <= x.
    -- Statt "1" kann man auch jede andere Genauigkeit nehmen.

    -- Invariante: a ist eine ganzzahlige untere Schranke an z.
    -- Wir haben die größte solche Schranke zu ermitteln.
    go a
        | fromInteger (a + 1) <= z
        = go (a + 1)
        | otherwise
        = a

-- | Berechnet die unendliche Kettenbruchentwicklung einer reellen
-- algebraischen Zahl. Terminiert auf jeder Eingabe.
cf :: Alg QinR -> [Integer]
cf x = a : cf (unit / (x - fromInteger a))
    where a = floor' x
