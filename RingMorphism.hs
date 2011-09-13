-- | Stellt die Typklasse 'RingMorphism' für Ringhomomorphismen bereit,
-- beispielsweise um Ganzheitsringe (deren Datum eben ein Ringhomomorphismus
-- ist) statisch typisieren zu können.
{-# LANGUAGE TypeFamilies, EmptyDataDecls, FlexibleContexts #-}
module RingMorphism where

import Prelude hiding (fromInteger)
import Ring

-- | Dummytyp ohne Elemente (abgesehen von 'undefined'), um bei der
-- Typerschließung zu helfen.
data Proxy s

-- | Klasse für Ringhomomorphismen.
class (Ring (Domain m), Ring (Codomain m)) => RingMorphism m where
    -- | Der Quellring des Ringmorphismus.
    type Domain   m :: *
    -- | Der Zielring des Ringmorphismus.
    type Codomain m :: *
    -- | Der eigentliche Morphismus.
    mor :: Proxy m -> Domain m -> Codomain m


-- | Bezeichnung für den eindeutigen Ringhomomorphismus vom Ring
-- der ganzen Zahlen in einen beliebigen Ring /a/ (nur zu
-- Demonstrationszwecken).
data Zin a

instance (Ring a) => RingMorphism (Zin a) where
    type Domain   (Zin a) = Integer
    type Codomain (Zin a) = a
    mor _ = fromInteger
