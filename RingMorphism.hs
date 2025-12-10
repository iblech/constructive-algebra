-- | Stellt die Typklasse 'RingMorphism' für Ringhomomorphismen bereit,
-- beispielsweise um Ganzheitsringe (deren Datum eben ein Ringhomomorphismus
-- ist) statisch typisieren zu können.
{-# LANGUAGE TypeFamilies, EmptyDataDecls, FlexibleContexts #-}
module RingMorphism where

import Prelude hiding (fromInteger)
import Data.Kind

import Proxy
import Ring

-- | Klasse für Ringhomomorphismen.
class (Ring (Domain m), Ring (Codomain m)) => RingMorphism m where
    -- | Der Quellring des Ringmorphismus.
    type Domain   m :: Type
    -- | Der Zielring des Ringmorphismus.
    type Codomain m :: Type
    -- | Der eigentliche Morphismus.
    mor :: Proxy m -> Domain m -> Codomain m

-- | Bezeichnung für den eindeutigen Ringhomomorphismus vom Ring
-- der ganzen Zahlen in einen beliebigen Ring /a/ (nur zu
-- Demonstrationszwecken).
--
-- Zentral nutzen wir 'Complex.QinC' für die algebraischen Zahlen.
data Zin a

instance (Ring a) => RingMorphism (Zin a) where
    type Domain   (Zin a) = Integer
    type Codomain (Zin a) = a
    mor _ = fromInteger
