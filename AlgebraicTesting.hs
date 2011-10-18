-- | Dieses Modul stellt QuickCheck-Eigenschaften für "Algebraic" bereit.
{-# LANGUAGE FlexibleInstances, FlexibleContexts, TypeFamilies #-}
module AlgebraicTesting (check_Algebraic) where

import Prelude hiding ((+), (-), (*), (/), (^), negate, recip, fromRational, quotRem, fromInteger)
import Data.Ratio

import Algebraic
import qualified Algebraic as A
import Complex
import ComplexRational
import Field
import IntegralClosure
import NumericHelper
import Polynomial
import qualified Polynomial as Poly
import Ring
import Testing
import ZeroRational

instance Arbitrary (Alg QinC) where
    arbitrary = elements . roots =<< simpleNonconstantRationalPoly

props_maybeInvert :: [Property]
props_maybeInvert =
    [ forAll arbitrary $ \(Blind z) ->
        case recip (z :: Alg QinC) of
            Nothing -> z == zero
            Just z' -> z * z' == unit
    ]

props_isRational :: [Property]
props_isRational =
    [ forAll simpleRational $ \r -> forAll simpleNonconstantRationalPoly $ \f ->
        let z = MkAlg $ MkIC (fromRational r) . normalize' $ fmap F f * (iX - fromRational r)
        in  isRational z == Just r && isRational (z + irrationalNumber) == Nothing
        -- Natürlich ist dieser Test nur als Minimalanforderung zu verstehen,
        -- besser wäre es, eine Funktion nonRationalAlgebraicNumber :: Gen (Alg QinC)
        -- zu schreiben. Aber die offensichtliche Implementation würde ja
        -- isRational verwenden, sodass der Test keine Aussagekraft hätte.
    ]
    where irrationalNumber = fromRealAlg A.sqrt2

props_isComplexRational :: [Property]
props_isComplexRational =
    [ forAll simpleRational $ \r -> forAll simpleRational $ \s -> forAll simpleNonconstantRationalPoly $ \f ->
        let u = fromComplexRational (r :+: s) :: IC QinC
            z = MkAlg $ MkIC (number u) . normalize' $ fmap F f * unNormedPoly (polynomial u)
        in  isComplexRational z == Just (r :+: s) && isComplexRational (z + irrationalNumber) == Nothing
    ]
    where irrationalNumber = fromRealAlg A.sqrt2

props_isInteger :: [Property]
props_isInteger =
    [ forAll arbitrary $ \(Blind z) ->
        case isRational z of
            Just q | numerator q `mod` denominator q == 0 ->
                isInteger z == Just (unsafeFromRational q)
            _ -> isInteger z == Nothing
    ]

props_eval :: [Property]
props_eval =
    [ forAll arbitrary $ \(Blind x) -> forAll simpleNonconstantRationalPoly $ \f ->
        A.eval (x :: Alg QinC) (fmap F f) == Poly.eval x (fmap (A.fromBase . F) f)
    ]

check_Algebraic :: IO ()
check_Algebraic = mapM_ (quickCheckWith stdArgs{ maxSize = 1 }) $ concat
    [ props_maybeInvert
    , props_isRational, props_isComplexRational, props_isInteger
    , props_eval
    ]
