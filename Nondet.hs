{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Nondet where

import System.IO.Unsafe

-- | Monade für nicht-deterministische Rechnungen von
-- Approximationsalgorithmen.
--
-- Wir verwenden dazu einfach die 'IO'-Monade, weil wir beliebige externe
-- Kommunikation (beispielsweise Nutzereingaben oder Zufallszahlen) erlauben
-- wollen.
--
-- Operationen, die den Kontrollfluss beeinflussen (wie beispielsweise
-- 'forkIO'), verbieten wir. (Denn was würde so ein Algorithmus bedeuten?)
newtype R a = R { runR :: IO a }
    deriving (Functor,Monad)

-- | /unsafeRunR m/ lässt die nicht-deterministische Operation /m/ laufen
-- und gibt ihr Ergebnis zurück.
--
-- Das ist im Allgemeinen gefährlich, denn jedes Mal, wenn das Ergebnis dann
-- ausgewertet wird, kann jeweils ein anderer Wert resultieren, da /m/ ja nicht
-- als deterministisch vorausgesetzt wird. Außerdem werden die Nebeneffekte in /m/
-- möglicherweise mehrmals ausgeführt.
--
-- Verwendet man 'unsafeRunR' in einer Funktion, muss man daher darauf achten,
-- dass der Rückgabewert nicht von den verschiedenen Ergebnissen von
-- 'unsafeRunR' abhängt -- sonst verletzt man das Prinzip der referentiellen
-- Transparenz.
unsafeRunR :: R a -> a
unsafeRunR = unsafePerformIO . runR
