{-# LANGUAGE TypeFamilies, FlexibleContexts, GeneralizedNewtypeDeriving, RankNTypes, FlexibleInstances #-}
module IdealExtension where

import Prelude hiding (gcd, quotRem, (+), (*), (-), (/), (^), negate, recip, fromInteger)
import Ring
import Field
import Polynomial
import Euclidean
import Control.Monad.Reader
import Control.Monad.Error
import Debug.Trace
import Algebraic as A
import IntegralClosure
import Complex
import ZeroRational
import Data.Maybe

type Ideal k k' = ReaderT k (Either k')

restart :: k' -> Ideal k k' a
restart x = ReaderT (const $ Left x)

runIdeal :: Ideal k k' a -> k -> (k' -> k) -> a
runIdeal m x0 f = case runReaderT m x0 of
    Left  y -> runIdeal m (f y) f
    Right a -> a

class (Ring a, Monad (Nondet a)) => IdealField a where
    type Nondet a :: * -> *
    idealRecip :: a -> (Nondet a) (Maybe a)

idealEquals :: (IdealField a) => a -> a -> Nondet a Bool
idealEquals x y = liftM isNothing $ idealRecip (x - y)

-- IdealSimpleExtension
newtype ISE k s = S (Poly k)
    deriving (Show,Ring,AllowsRationalEmbedding)

fromBase :: k -> ISE k s
fromBase = S . Polynomial.constant

adjointedRoot :: (Field k) => ISE k s
adjointedRoot = S iX

-- Vor.: f nicht null.
instance Error (Poly k, Poly k) where
    strMsg msg = error $ "Error (Poly k): " ++ show msg

instance (Field k, IntegralDomain k, Eq k) => IdealField (ISE k s) where
    type Nondet (ISE k s) = Ideal (Poly k) (Poly k, Poly k)
    idealRecip (S g) = do
        f <- ask
        let (u,v,s,t) = gcd f g; d = u*f + v*g
        if degree d == 0        then return . Just . S $ recip (leadingCoeff d) .* v else do
        if degree d == degree f then return Nothing else do
        trace ("restart!") $ do
        restart (d,s)

canonISE :: (Field k, IntegralDomain k, Eq k) => ISE k s -> Nondet (ISE k s) (Poly k)
canonISE (S g) = do
    f <- ask
    let (q,r) = quotRem g f
    return r

runISE
    :: (Field k)
    => Poly k -> (Poly k -> Bool)
    -> (forall s. Nondet (ISE k s) a)
    -> a
runISE f phi m =
    case runReaderT m f of
        Right x     -> x
        Left  (d,s) ->
            if phi d
                then runISE d phi m
                else runISE s phi m

ex :: Nondet (ISE Rational s) (Maybe (ISE Rational s))
ex = do
    Just x <- idealRecip $ adjointedRoot - unit
    let z = adjointedRoot^2 - unit - unit
    let y = (x * (adjointedRoot - unit) - unit) * z
    idealRecip z

exF :: Poly Rational
exF = iX^3 - fromInteger 2

runISEwithAlgebraic :: Alg QinC -> (forall s. Nondet (ISE Rational s) a) -> a
runISEwithAlgebraic z = runISE f phi
    where
    f     = fmap unF . polynomial . unAlg $ z
    phi g = zero == A.eval z g

--exRun' = exRun (head $ rootsA $ iX^3 - fromInteger 1)
