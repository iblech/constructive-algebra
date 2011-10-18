module Main where

import System.Environment

import Algebraic
import AlgebraicTesting
import Complex
import ComplexRational
import Euclidean
import Factoring
import Field
import Galois
import IdealExtension
import IntegralClosure
import NormedRing
import NumericHelper
import Polynomial
import Ring
import SimpleExtension
import Smith
import TypeLevelNat
import RootFinding
import RootFindingTesting

demos :: [(String, IO ())]
demos =
    [ ("SimpleExtension", SimpleExtension.demo)
    , ("Smith",           Smith.demo)
    , ("Complex",         Complex.demo)
    , ("Algebraic",       Algebraic.demo)
    , ("RootFinding",    RootFinding.demo)
    , ("Factoring",       Factoring.demo)
    , ("IdealExtension",  IdealExtension.demo)
    , ("Galois",          Galois.demo)
    ]

tests :: [(String, IO ())]
tests =
    [ ("Algebraic",       check_Algebraic)
    , ("ComplexRational", check_ComplexRational)
    , ("Euclidean",       check_Euclidean)
    , ("Factoring",       check_Factoring)
    , ("Field",           check_Field)
    , ("IntegralClosure", check_IntegralClosure)
    , ("NormedRing",      check_NormedRing)
    , ("NumericHelper",   check_NumericHelper)
    , ("Polynomial",      check_Polynomial)
    , ("Ring",            check_Ring)
    , ("SimpleExtension", check_SimpleExtension)
    , ("Smith",           check_Smith)
    , ("TypeLevelNat",    check_TypeLevelNat)
    , ("RootFinding",     check_RootFinding)
    ]

main :: IO ()
main = do
    args <- getArgs
    case args of
        "demos":_ -> mapM_ (uncurry runProc) demos
        "tests":_ -> mapM_ (uncurry runProc) tests
        _         -> error "Rufe mich mit 'demos' oder 'tests' als Argument auf!"

runProc :: String -> IO () -> IO ()
runProc name m = do
    putStrLn $ ">> " ++ name
    m
    putStrLn ""
