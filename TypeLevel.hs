{-# LANGUAGE EmptyDataDecls, RankNTypes #-}
module TypeLevel where

data Z
data S a

type N0 = Z
type N1 = S N0
type N2 = S N1
type N3 = S N2
type N4 = S N3

type Nat = Int

class N a where reify :: a -> Nat

instance N Z where reify _ = 0

instance (N n) => N (S n) where
    reify = succ . reify . pred
	where pred = undefined :: S m -> m

reflect :: Nat -> (forall n. (N n) => n -> r) -> r
reflect 0 cc         = cc (undefined :: Z)
reflect n cc | n > 0 = reflect (pred n) $ cc . (undefined :: m -> S m)
