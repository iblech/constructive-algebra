{-# LANGUAGE TypeFamilies, FlexibleContexts, UndecidableInstances #-}
module SimpleExtension where

import Prelude hiding ((+), (*), (/), (-), (^), negate, fromInteger, fromRational, recip, signum, sum, product, quotRem, gcd)
import Ring
import Field
import Polynomial
import Factoring
import Data.List hiding (sum)
import Complex
import Algebraic
import Control.Monad
import RingMorphism

class (RingMorphism (Mor m), Field (Codomain (Mor m))) => SimpleExtension m where
    type Mor m :: *
    generator :: m -> Codomain (Mor m)

data (SimpleExtension m) => SE m = MkSE (Poly (Domain (Mor m))) (Poly (Domain (Mor m)))

instance (SimpleExtension m) => Ring (SE m) where
    MkSE p q + MkSE p' q' = MkSE (p*q' + p'*q)   (q*q')
    MkSE p q * MkSE p' q' = MkSE (p*p')          (q*q')
    negate (MkSE p q)     = MkSE (negate p)      q
    zero                  = MkSE zero            unit
    unit                  = MkSE unit            unit
    fromInteger n         = MkSE (fromInteger n) unit

instance (SimpleExtension m) => Field (SE m) where
    recip (MkSE p q) = MkSE q p

instance (SimpleExtension m, Eq (Codomain (Mor m))) => Eq (SE m) where
    u@(MkSE p q) == MkSE p' q' = evalg p * evalg q' == evalg p' * evalg q
	where evalg = eval (generator . (undefined :: SE m -> m) $ u) . fmap (mor . (undefined :: SE m -> Mor m) $ u)

data Qsqrt2

instance SimpleExtension Qsqrt2	where
    type Mor Qsqrt2 = QinQalg
    generator _ = Algebraic.sqrt2
