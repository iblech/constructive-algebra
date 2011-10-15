{-# LANGUAGE FlexibleInstances #-}
module AlgebraicTesting where

import Prelude hiding ((+), (-), (*), (/), (^), negate, recip, fromRational, quotRem, fromInteger)
import Ring
import Complex
import ComplexRational
import Algebraic
import qualified Algebraic as A
import Testing
import ZeroRational
import Polynomial
import qualified Polynomial as Poly
import IntegralClosure
import Field
import Debug.Trace
import Data.Ratio
import NumericHelper

instance Arbitrary (Alg QinC) where
    arbitrary = elements . roots =<< simpleNonconstantRationalPoly

props_maybeInvert :: [Property]
props_maybeInvert =
    [ forAll arbitrary $ \(Blind z) ->
        case maybeInvert z of
            Nothing -> z == zero
            Just z' -> z * z' == unit
    ]

props_isRational :: [Property]
props_isRational =
    [ forAll simpleRational $ \r -> forAll simpleNonconstantRationalPoly $ \f ->
        let z = MkAlg $ MkIC (fromRational r) . normalize' $ fmap F f * (iX - fromRational r)
        in  isRational z == Just r && isRational (z + A.sqrt2) == Nothing
        -- Natürlich ist dieser Test nur als Minimalanforderung zu verstehen,
        -- besser wäre es, eine Funktion nonRationalAlgebraicNumber :: Gen (Alg QinC)
        -- zu schreiben. Aber die offensichtliche Implementation würde ja
        -- isRational verwenden, sodass der Test keine Aussagekraft hätte.
    ]

props_isComplexRational :: [Property]
props_isComplexRational =
    [ forAll simpleRational $ \r -> forAll simpleRational $ \s -> forAll simpleNonconstantRationalPoly $ \f ->
        let u = fromComplexRational (r :+: s) :: IC QinC
            z = MkAlg $ MkIC (number u) . normalize' $ fmap F f * unNormedPoly (polynomial u)
        in  isComplexRational z == Just (r :+: s) && isComplexRational (z + A.sqrt2) == Nothing
    ]

props_isInteger :: [Property]
props_isInteger =
    [ forAll arbitrary $ \(Blind z) ->
        case isRational z of
            Just q | numerator q `mod` denominator q == 0 ->
                isInteger z == Just (unsafeFromRational q)
            otherwise -> isInteger z == Nothing
    ]

props_eval :: [Property]
props_eval =
    [ forAll arbitrary $ \(Blind x) -> forAll simpleNonconstantRationalPoly $ \f ->
        A.eval x f == Poly.eval x (fmap (A.fromBase . F) f)
    ]

props_Algebraic :: [Property]
props_Algebraic =
    props_maybeInvert ++
    props_isRational ++ props_isComplexRational ++ props_isInteger ++
    props_eval
