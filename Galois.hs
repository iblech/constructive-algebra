-- | Dieses Modul stellt die Funktionalität zur Berechnung von Galoisgruppen.
-- Dazu bestimmen wir zu einem gegebenen normierten separablen Polynom /f/ zunächst
-- die Nullstellen, bestimmen dann ein primitives Element und nutzen
-- schließlich die Bijektion der galoissch Konjugierten des primitiven Elements
-- mit den Elementen der Galoisgruppe aus.
{-# LANGUAGE TupleSections, PatternGuards #-}
module Galois
    ( linearResolvent, galoisGroup, primitiveElement, pseudoResolvent, Galois.demo )
    where

import Prelude hiding ((+), (*), (/), (-), (^), negate, fromInteger, fromRational, recip, signum, sum, product, quotRem, gcd)
import Ring
import Field
import Polynomial as Poly
import Factoring
import Data.List hiding (sum,product)
import Complex
import IntegralClosure
import ZeroRational
import Algebraic as A
import Control.Monad
import Data.Maybe
import NumericHelper
import IdealExtension as I
import IdealEuclidean
import Euclidean
import Text.Printf
import Testing

-- | Berechnet eine lineare galoissche Resolvente eines normierten separablen
-- Polynoms über eine Abschätzung, in der die Nullstellen des Polynoms
-- eingehen.
--
-- Wird von den anderen Funktionen dieses Moduls nicht benutzt.
--
-- Siehe: Algebra I, Übungsblatt 11, Aufgabe 12
linearResolvent :: Poly Rational -> R [Integer]
linearResolvent f = do
    bounds' <- sequence bounds
    let csq = foldl' max 1 bounds'
        c   = fromIntegral n * (squareRoot csq + 1)
    return $ take n $ let as = 1 : map (c*) as in as
    where
    xs     = map (number . unAlg) $ roots f
    n      = length xs
    bounds = do
        (a,b) <- pairs xs
        (u,v) <- pairs xs
        let q = normUpperBoundR $ absSq ((a - b) * recip' (u - v))
        return $ liftM roundUp q

pairs :: [a] -> [(a,a)]
pairs []       = []
pairs (x:xs)   = map (x,) xs ++ pairs xs

-- | Eine Liste aller ganzen Zahlen.
allIntegers :: [Integer]
allIntegers = 0 : go 1 where go n = n : (-n) : go (n + 1)

-- | Datentyp für Ergebnisse von Galoisgruppenberechnungen von Polynomen
-- mit Koeffizienten in /r/ und Nullstellen in /a/.
data GaloisInfo r a = MkGaloisInfo
    { zeros             :: [a]        -- ^ die Nullstellen des betrachteten Polynoms
    , primitiveElt      :: a          -- ^ ein primitives Element der Nullstellen
    , primitiveMinpoly  :: Poly r     -- ^ Minimalpolynom des primitiven Elements
    , primitiveCombo    :: [Integer]  -- ^ Zahlen /lambda_i/ wie bei 'pseudoResolvent'
    , rationalExprs     :: [Poly r]   -- ^ Zeugen der Rationalität der Nullstellen
                                    -- im primitiven Element
    , primitiveConjs    :: [a]        -- ^ die galoisch Konjugierten des primitiven Elements
    , groupElts         :: [[Int]]    -- ^ die Element der Galoisgruppe
    } deriving (Show)

-- | Bestimmt die Galoisgruppe eines normierten separablen Polynoms.
galoisGroup :: Poly Rational -> GaloisInfo Rational (Alg QinC)
galoisGroup f = MkGaloisInfo xs t m res' hs' conjs sigmas
    where
    -- Die Nullstellen von f. Hier schon mit simplifyAlg die entsprechenden
    -- Minimalpolynome zu finden, bringt einiges an Effizienz.
    xs         = map simplifyAlg $ roots f

    -- t ist ein primitives Element der Nullstellen, wobei die Darstellungen
    --   zipWith (*) (map fromInteger res') xs == t
    -- und
    --   eval t (hs'!!i) == xs!!i
    -- gelten.
    -- Bezeichnet n den Grad von f, so genügt es, nur nach einem primitiven
    -- Element der letzten (n-1) Nullstellen zu suchen. Denn die fehlende erste
    -- Nullstelle lässt sich (Satz von Vieta) sowieso über die anderen ausdrücken.
    (res,t,hs) = pseudoResolvent (tail xs)
    res'       = 0:res
    hs'        = negate (sum hs + Poly.fromBase a) : hs where a = (!! 1) . reverse . canonCoeffs $ f

    -- Minimalpolynom und galoissch Konjugierte von t.
    -- pseudoResolvent garantiert, dass das zum zurückgegebenen primitiven Element
    -- gehörende Polynom schon das Minimalpolynom ist.
    m          = unNormedPoly . fmap unF . polynomial . unAlg $ t
    conjs      = roots m

    -- Schließlich die Elemente der Galoisgruppe. Diese stehen in Bijektion mit
    -- den galoissch Konjugierten von t: Ist t' ein galoissch Konjugiertes von
    -- t (wobei t selbst auch erlaubt ist), so ist für jedes i die Zahl h_i(t')
    -- gleich einem gewissen x_j, womit eine Permutation sigma: i |-> j
    -- definiert wird.
    inds       = [0..length xs - 1]
    sigmas     =
        flip map conjs $ \t' ->
            flip map inds $ \i ->
                head [ j | j <- inds, xs !! j == A.eval t' (fmap F $ hs' !! i) ]
                -- aus der Theorie wissen wir, dass diese Liste aus genau einem
                -- Element besteht.

-- | Berechnet zu zwei gegebenen algebraischen Zahlen /x/ und /y/ ein
-- primitives Element /t/ in der Form /t = x + lambda*y/ für eine
-- ganze Zahl /lambda/.
primitiveElement
    :: Alg QinC  -- ^ /x/
    -> Alg QinC  -- ^ /y/
    -> (Integer, Alg QinC, Poly Rational, Poly Rational)
                 -- ^ /(lambda, t, hX, hY)/, mit
                 -- t = x + lambda*y, hX(t) = x und hY(t) = y.
primitiveElement x y = (lambda, t, hX, hY)
    where
    -- Wir nutzen das Verfahren des Skripts. Dort hat man f und g als die
    -- Minimalpolynome von x bzw. y bestimmt; das ist aber nicht nötig.
    -- Es genügt, wenn f irgendein normiertes Polynom mit f(x) = 0 und
    -- g ein normiertes separables Polynom mit g(y) = 0 ist.
    f = unNormedPoly . fmap unF . polynomial . unAlg $ x
    g = unNormedPoly . squarefreePart . unNormedPoly . fmap unF . polynomial . unAlg $ y

    -- Ausnahmewerte von lambda, die wir nicht verwenden dürfen, wenn
    -- x + lambda*y garantiert ein primitives Element zu x und y sein soll.
    exceptions :: [Integer]
    exceptions = do
        x' <- roots f
        y' <- roots g
        r  <- maybeToList $ recip (y - y')
        maybeToList $ isApproxInteger $ (x' - x) * r

    -- lambda soll die erste Zahl in unser Aufzählung aller ganzen Zahlen sein,
    -- die nicht in der Ausnahmemenge enthalten ist.
    lambda = head $ filter (\q -> all (/= q) exceptions) allIntegers

    t = x + fromInteger lambda * y

    -- Da wir später (beispielsweise in der Bestimmung der Galoisgruppe) eh das
    -- Minimalpolynom von t benötigen, könnten wir eigentlich auch in der
    -- richtigen Erweiterung Q[X]/(m_t) statt der ideellen Erweiterung rechnen.
    -- Dazu müssten wir aber das Minimalpolynom von t auf Typniveau heben, und
    -- das ist wohl die Mühe nicht wert.
    hY = fmap unF $ execISEwithAlgebraic t $ do
        -- h = f(t - lambda X)
        let h = fmap I.fromBase (fmap F f) `compose` (Poly.fromBase adjointedRoot - fromInteger lambda * iX)
        d <- idealNormedGCD (fmap I.fromBase (fmap F g)) h
        -- Im Skript ist bewiesen, dass d von der Form X-y ist, daher erhalten
        -- wir y (als in t polynomiellen Ausdruck) als die Negation des ersten
        -- Koeffizienten von d.
        liftM negate . canonRep . head . unsafeCoeffs $ d

    -- Der Zeuge, dass x in t rational ist, ist einfacher:
    hX = iX - fromInteger lambda * hY

props_primitiveElement :: [Property]
props_primitiveElement =
    [ property $ \x y ->
        let (lambda,t,hX,hY) = primitiveElement x y
        in  and
            [ t == x + fromInteger lambda * y
            , A.eval t (fmap F hX) == x
            , A.eval t (fmap F hY) == y
            ]
    ]

-- | Berechnet zu einer gegebenen Liste von algebraischen Zahlen /x_1,...,x_n/ ein primitives
-- Element /t/ in der Form /t = lambda_1 x_1 + ... + lambda_n x_n/ und gibt
-- außerdem Zeugen der Rationalität der /x_i/ in /t/ zurück, also Polynome /hs/
-- mit /eval t (hs!!i) == x_i/.
--
-- Es wird garantiert, dass auf das zurückgegebene primitive Element schon
-- 'Factoring.simplifyAlg' aufgerufen wurde.
--
-- Der Name /pseudoResolvent/ erklärt sich dadurch, als dass im Spezifall, dass
-- die /x_i/ die Nullstellen eines separablen Polynoms sind, zumindest die Zahlen
-- /sigma * t/, wobei /sigma/ die entsprechende Galoisgruppe durchläuft,
-- paarweise verschieden sind.
pseudoResolvent
    :: [Alg QinC]                              -- ^ /x_1, ..., x_n/
    -> ([Integer], Alg QinC, [Poly Rational])  -- ^ /(lambdas,t,hs)/
pseudoResolvent []       = ([],  zero,        [])
pseudoResolvent [x]      = ([1], simplifyAlg x, [iX])
pseudoResolvent (x:y:zs) =
    -- Wir berechnen ein primitives Element u der ersten beiden Zahlen x und y,
    -- und bestimmen dann rekursiv ein primitives Element zu u und den
    -- restlichen Zahlen zs.
    let (lambda, u, hX, hY) = primitiveElement x y
        u'                  = simplifyAlg u
        -- u = x + lambda y
        (as, t, hU:hs)      = pseudoResolvent (u':zs)
        -- Es gilt:
        --   t = zipWith (*) as (u':zs)
        --   (hs !! i)(t) = (u':zs) !! i

        -- Reduktionsoperation modulo des Minimalpolynoms von t
        reduce :: Poly Rational -> Poly Rational
        reduce = snd . (`quotRem` unNormedPoly (fmap unF . polynomial . unAlg $ t))

    -- Wir können die Zeugen der Rationalität,
    --     x = hX(u) = hX(hU(t)) = (hX . hU)(t)
    --     y = hY(u) = hY(hU(t)) = (hY . hU)(t)
    -- modulo dem Minimalpolynom von t betrachten, denn es ist je nur relevant,
    -- dass die Einsetzung von t zu x bzw. y führt. Das führt zu kleineren
    -- Polynomen, ist also im Hinblick auf spätere Verwendung effizienter.
    in (1 : lambda : tail as, t, reduce (hX `compose` hU) : reduce (hY `compose` hU) : hs)

props_pseudoResolvent :: [Property]
props_pseudoResolvent =
    [ property $ \xs ->
        let (lambdas,t,hs) = pseudoResolvent xs
        in  t == sum (zipWith (*) (map fromInteger lambdas) xs) &&
            all (\(p,x) -> A.eval t (fmap F p) == x) (zip hs xs)
    ]

demo :: IO ()
demo = do
    flip mapM_ [iX^4 - unit, iX^5 - unit, iX^6 - unit] $ \f -> do
        putStrLn $ "Zur Galoisgruppe von " ++ show f ++ ":"
        putStrLn $ formatGaloisInfo $ galoisGroup f
        putStrLn ""

formatGaloisInfo
    :: (Eq r, Show r, Ring r, HasFloatingApprox a)
    => GaloisInfo r a -> String
formatGaloisInfo gal = concat $ intersperse "\n" $
    [ "` Nullstellen:        " ++ show (map unsafeApprox (zeros gal))
    , "` Prim. Element t:    " ++ show (primitiveCombo gal) ++ " * xs ~~ "
                               ++ show (unsafeApprox (primitiveElt gal))
    , "  ` Min. Polynom:     " ++ show (primitiveMinpoly gal)
    , "  ` Gal. Konjugierte: " ++ show (map unsafeApprox (primitiveConjs gal))
    , concat . intersperse "\n" $ zipWith (\i p -> printf "  ` Nst. #%d in t:     %s" i (show p))
        [(0::Integer)..] (rationalExprs gal)
    , "` Galoisgruppe:       " ++ show (groupElts gal)
    ]
