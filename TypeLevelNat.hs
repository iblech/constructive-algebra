{-# LANGUAGE EmptyDataDecls, RankNTypes #-}
module TypeLevelNat
    ( Z, S
    , ReifyNat(..), reflectNat, reflectPositiveNat
    , module Proxy
    ) where

import Prelude hiding (pred,succ)
import Proxy

data Z
data S n

-- | Approximation an den Typ für natürliche Zahlen.
type Nat = Integer

class ReifyNat n where
    reifyNat :: Proxy n -> Nat

instance ReifyNat Z where reifyNat _ = 0

instance (ReifyNat n) => ReifyNat (S n) where
    reifyNat = (+ 1) . reifyNat . fmap pred

reflectNat :: Nat -> (forall n. (ReifyNat n) => Proxy n -> r) -> r
reflectNat n k
    | n == 0    = k (undefined :: Proxy Z)
    | n  < 0    = error "reflectNat einer negativen Zahl!"
    | otherwise = reflectNat (n - 1) $ k . fmap succ

reflectPositiveNat :: Nat -> (forall n. (ReifyNat n) => Proxy (S n) -> r) -> r
reflectPositiveNat n k
    | n  < 1    = error "reflectPositiveNat einer nicht-positiven Zahl!"
    | n == 1    = k (undefined :: Proxy (S Z))
    | otherwise = reflectPositiveNat (n - 1) $ k . fmap succ

zero :: Z
zero = undefined

pred :: S n -> n
pred = undefined

succ :: n -> S n
succ = undefined
