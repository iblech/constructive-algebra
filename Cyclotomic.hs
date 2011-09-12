module Cyclotomic where

import Prelude hiding ((+), (*), (/), (-), (^), negate, fromInteger, fromRational, recip, signum, sum, product, quotRem, gcd)
import Ring
import Polynomial
import NumericHelper
import Euclidean
import Data.List hiding (product)

cyclotomicPolynomials :: [Poly Integer]
cyclotomicPolynomials
    = map go [1..]
    where
    go n = fst $ (iX^fromInteger n - fromInteger 1) `normedQuotRem`
        product (map (cyclotomicPolynomials `genericIndex`) . map pred . init $ positiveDivisors n)
