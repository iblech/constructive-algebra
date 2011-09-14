-- | Stellt den Dummytyp 'Proxy' bereit. Wird in "RingMorphism" und
-- "TypeLevelNat" verwendet.
{-# LANGUAGE EmptyDataDecls #-}
module Proxy where

-- | Dummytyp ohne Elemente (abgesehen von 'undefined'), um bei der
-- Typerschließung zu helfen.
data Proxy s
-- deriving (Functor) führt bei GHC 6.12.1 zu einer Panik.

instance Functor Proxy where
    fmap f _ = undefined
