-- | Stellt den Dummytyp 'Proxy' ohne Elemente bereit. Wird in "RingMorphism",
-- "TypeLevelNat" und einigen anderen Stellen verwendet, um den Code besser
-- lesbar zu gestalten.
{-# LANGUAGE EmptyDataDecls #-}
module Proxy where

-- | Dummytyp ohne Elemente (abgesehen von /undefined :: Proxy s/), um bei der
-- Typerschließung zu helfen.
--
-- Man könnte auch einfach /undefined :: s/ schreiben; wir verwenden den
-- expliziten /Proxy/-Typ, um im Code andeuten zu können, dass es nur auf
-- das Typgeschehen ankommt. Auch wird so verhindert, dass wir aus Versehen
-- einen solchen /undefined/-Wert vom Typ /s/ in einer Rechnung nutzen.
data Proxy s
-- deriving (Functor) führt bei GHC 6.12.1 zu einer Panik.

instance Functor Proxy where
    fmap _ _ = undefined

toProxy :: s -> Proxy s
toProxy = undefined

unProxy :: Proxy s -> s
unProxy = undefined

asTypeOfProxy :: s -> Proxy s -> s
asTypeOfProxy x _ = x
