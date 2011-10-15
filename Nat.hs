-- | Dieses Modul stellt die Typen 'Nat' und 'PositiveNat' bereit,
-- die Typen der natürlichen Zahlen mit bzw. ohne Null.
module Nat where

-- | Der Typ 'Nat' soll eine Approximation an den Typ der natürlichen Zahlen
-- mit Null sein.
type Nat = Integer

-- | Der Typ 'PositiveNat' soll eine Approximation an den Typ der natürlichen
-- Zahlen ab Eins sein.
type PositiveNat = Integer
