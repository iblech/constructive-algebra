-- | Stellt den Dummytyp 'Proxy' bereit. Wird in "RingMorphism" und
-- "TypeLevelNat" verwendet.
{-# LANGUAGE EmptyDataDecls #-}
module Proxy where

-- | Dummytyp ohne Elemente (abgesehen von /undefined :: Proxy s/), um bei der
-- Typerschließung zu helfen.
--
-- Man könnte auch einfach /undefined :: s/ schreiben; man verwendet den
-- /Proxy/-Typ daher, um im Code aus Dokumentationszwecken explizit darauf
-- hinzuweisen, dass es nur auf das Typgeschehen ankommt.
data Proxy s
-- deriving (Functor) führt bei GHC 6.12.1 zu einer Panik.

instance Functor Proxy where
    fmap f _ = undefined

unProxy :: Proxy s -> s
unProxy = undefined
