module Main where

import Algebraic
import Complex
import Factoring
import Galois
import IdealExtension
import SimpleExtension
import Smith
import ZeroRational

main = mapM_ (uncurry runDemo)
    [ ("SimpleExtension", SimpleExtension.demo)
    , ("Smith",           Smith.demo)
    , ("Complex",         Complex.demo)
    , ("Algebraic",       Algebraic.demo)
    , ("ZeroRational",    ZeroRational.demo)
    , ("Factoring",       Factoring.demo)
    , ("IdealExtension",  IdealExtension.demo)
    , ("Galois",          Galois.demo)
    ]

    where
    runDemo name m = do
        putStrLn $ ">> " ++ name
        m
        putStrLn ""
