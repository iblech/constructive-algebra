module Apartness where

import Nat

-- Der Zahltyp a sei so, dass für alle x : a gilt:
--     |x| > 0  oder  |x| < 1/n.
-- magnitudeZeroTest soll im ersten Fall False, im zwei True zurückgeben.
class Apartness a where
    magnitudeZeroTest :: Nat -> a -> Bool
