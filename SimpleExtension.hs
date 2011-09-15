{-# LANGUAGE TypeFamilies, FlexibleContexts, UndecidableInstances, GeneralizedNewtypeDeriving, EmptyDataDecls, StandaloneDeriving #-}
module SimpleExtension where

import Prelude hiding ((+), (*), (/), (-), (^), negate, fromInteger, fromRational, recip, signum, sum, product, quotRem, gcd)
import Ring
import Field
import Polynomial as Poly
import Factoring
import Data.List hiding (sum)
import Complex
import Control.Monad
import RingMorphism
import Proxy
import Euclidean
import Data.Maybe
import Algebraic
import IntegralClosure

class (Ring (BaseRing p)) => ReifyPoly p where
    type BaseRing p :: *
    reifyPoly :: Proxy p -> Poly (BaseRing p)

class (ReifyPoly p) => ReifyIrreduciblePoly p

newtype (ReifyPoly p) => SE p = MkSE (Poly (BaseRing p))

deriving instance (ReifyPoly p) => Ring (SE p)

instance (ReifyPoly p, Field (BaseRing p), Show (BaseRing p)) => Show (SE p) where
    show z = "[" ++ show (canonRep z) ++ "]"

modulus :: (ReifyPoly p) => Proxy (SE p) -> Poly (BaseRing p)
modulus = reifyPoly . (undefined :: Proxy (SE p) -> Proxy p)

canonRep :: (ReifyPoly p, Field (BaseRing p)) => SE p -> Poly (BaseRing p)
canonRep z@(MkSE f) = snd $ f `quotRem` modulus (toProxy z)

adjointedRoot :: (ReifyPoly p) => SE p
adjointedRoot = MkSE iX

fromBase :: (ReifyPoly p) => BaseRing p -> SE p
fromBase = MkSE . Poly.fromBase

instance (ReifyPoly p, Field (BaseRing p)) => Eq (SE p) where
   z == w = canonRep z == canonRep w

instance (ReifyIrreduciblePoly p, Field (BaseRing p)) => IntegralDomain (SE p) where

instance (ReifyIrreduciblePoly p, Field (BaseRing p)) => Field (SE p) where
    recip z@(MkSE p)
        | degree d == 0        = Just . MkSE $ fromJust (recip (leadingCoeff d)) .* v
        | degree d == degree f = Nothing
        | otherwise            =
            error "SimpleExtension.recip: Echten Faktor des angeblich irreduziblen Modulus gefunden!"
        where
        f = modulus (toProxy z)
        (u,v,s,t) = gcd f p
        d = u*f + v*p

data MinPolySqrt2
instance ReifyPoly MinPolySqrt2 where
    type BaseRing MinPolySqrt2 = Rational
    reifyPoly _ = iX^2 - fromInteger 2
instance ReifyIrreduciblePoly MinPolySqrt2

data Qsqrt2inC
instance RingMorphism Qsqrt2inC where
    type Domain   Qsqrt2inC = SE MinPolySqrt2
    type Codomain Qsqrt2inC = Complex
    mor _ = Poly.eval Complex.sqrt2 . fmap fromRational . canonRep

ex :: Alg Qsqrt2inC
ex = MkAlg $ MkIC Complex.sqrt2 $ mkNormedPoly (iX - Poly.fromBase adjointedRoot)
