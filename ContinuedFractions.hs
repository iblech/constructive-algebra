module ContinuedFractions where

import Prelude hiding ((+), (-), (*), (/), (^), negate, recip, fromRational, quotRem, fromInteger, Real)
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
    n = 100
    x = unsafeRunR $ approx n $ number . unAlg $ z
    y = floor (x - 1/fromInteger n) :: Integer
    -- y ist eine Ganzzahl mit y <= x.
    -- Für /n/ kann man auch jede andere Genauigkeit nehmen.

    -- Invariante: a ist eine ganzzahlige untere Schranke an z.
    -- Wir haben die größte solche Schranke zu ermitteln.
    go a
        | floor (x - 1 / fromInteger n) == floor (x + 1 / fromInteger n)
        = floor (x - 1 / fromInteger n)
        | fromInteger (a + 1) <= z
        = go (a + 1)
        | otherwise
        = a

-- | Berechnet die Abrundung einer reellen Zahl. Terminiert
-- auf ganzzahligen Eingaben *nicht*.
unsafeFloor :: Real -> Integer
unsafeFloor z = unsafeRunR $ go 3  -- Optimierung, man könnte auch bei 1 starten
    where
    go n = do
        x <- approx n z :: R Rational
        -- z liegt echt zwischen x-1/n und x+1/n.
        -- Liegt zwischen den Intervallgrenzen eine ganze Zahl?
        if floor (x - 1 / fromInteger n) == floor (x + 1 / fromInteger n)
            then return $ floor (x - 1 / fromInteger n)
            else go (2*n)

-- | Berechnet die unendliche Kettenbruchentwicklung einer reellen
-- algebraischen Zahl. Terminiert auf jeder Eingabe.
cf :: Alg QinR -> [Integer]
cf x = case recip (x - fromInteger a) of
    Just r  -> a : cf r
    Nothing -> [a]
    where a = floor' x

-- | Berechnet die unendliche Kettenbruchentwicklung einer reellen
-- Zahl. Terminiert auf rationalen Eingaben nicht, sonst aber schon.
unsafeCf :: Real -> [Integer]
unsafeCf x = a : unsafeCf (recip' (x - fromInteger a))
    where a = unsafeFloor x

demo :: IO ()
demo = do
    let zs =
            [ ("41",                  fromInteger 41)
            , ("zero",                zero)
            , ("sqrt2 - sqrt2",       sqrt2 - sqrt2)
            , ("goldenRatio * (sqrt2 - sqrt2)", goldenRatio * (sqrt2 - sqrt2))
            , ("goldenRatio",         goldenRatio)
            , ("sqrt2",               sqrt2)
            , ("sqrt2^2",             sqrt2^2)
            , ("sqrt2^5",             sqrt2^5)
            , ("goldenRatio + sqrt2", goldenRatio + sqrt2)
            ]
    mapM_ (uncurry printInfo) zs

    where
    printInfo name z =
        putStrLn $
            "Beginn der Kettenbruchentwicklung der Zahl " ++ name ++ ": " ++
                show (take 7 $ cf z)
