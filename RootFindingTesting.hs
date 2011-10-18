-- | Dieses Modul stellt QuickCheck-Eigenschaften für "RootFinding" bereit.
--
-- Die Eigenschaften sind hierhin deswegen ausgelagert, um die sonst
-- entstehende zyklische Abhängigkeit von "RootFinding" und "Algebraic"
-- zu verhindern.
module RootFindingTesting where

import Prelude hiding ((+), (*), (/), (-), (^), negate, fromInteger, fromRational, recip, signum, sum, product, quotRem, gcd)
import Ring
import Algebraic as A
import Polynomial
import qualified Polynomial as Poly
import RootFinding
import Galois
import Testing
import Field

props_roots :: [Property]
props_roots =
    [ forAll simpleNonconstantRationalPoly $ \f ->
        let g  = unNormedPoly $ squarefreePart f

            -- g' sollte das Produkt über die Linearfaktoren X-x_i sein,
            -- also idealerweise wie folgt definiert:
            --     g' = product $ map ((iX -) . Poly.fromBase) $ roots g
            -- Das ist allerdings zu ineffizient in der Berechnung der
            -- Ganzheitsgleichungen der Koeffizienten von g'. Daher folgender
            -- Trick:
            g' = MkPoly . map (A.eval t . fmap F) . canonCoeffs . product . map ((iX -) . Poly.fromBase) $ hs
            (_,t,hs) = pseudoResolvent (roots g)
            -- Wir berechnen also ein primitives Element zusammen mit Polynomen
            -- hs (die hs_i(t) = x_i erfüllen)
        in  isRationalPoly g' == Just g
    ]

check_RootFinding :: IO ()
check_RootFinding = mapM_ (quickCheckWith stdArgs{ maxSize = 1, maxSuccess = 5 }) props_roots
