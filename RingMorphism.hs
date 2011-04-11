{-# LANGUAGE TypeFamilies, EmptyDataDecls, FlexibleContexts #-}
module RingMorphism where

import Ring

class (Ring (Domain m), Ring (Codomain m)) => RingMorphism m where
    type Domain   m :: *
    type Codomain m :: *
    mor :: m -> Domain m -> Codomain m


data ZinQ

instance RingMorphism ZinQ where
    type Domain   ZinQ = Integer
    type Codomain ZinQ = Rational
    mor _ = Ring.fromInteger
