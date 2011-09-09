{-# OPTIONS_GHC -O2 -fno-cse #-}
module Primes (primes) where

primes :: [Integer]
primes = primesTMWE ()

-- http://www.haskell.org/haskellwiki/Prime_numbers, Tree merging with Wheel
primesTMWE :: () -> [Integer]
primesTMWE () = 2:3:5:7: gaps 11 wheel (join $ roll 11 wheel primes')
  where
    primes' = 11: gaps 13 (tail wheel) (join $ roll 11 wheel primes')
    join ((x:xs): ~(ys:zs:t))  = x : union xs (union ys zs)    
                                       `union` join (pairs t)  
    pairs ((x:xs):ys:t)        = (x : union xs ys) : pairs t
    gaps k ws@(w:t) cs@(c:u) | k==c  = gaps (k+w) t u 
                             | True  = k : gaps (k+w) t cs  
    roll k ws@(w:t) ps@(p:u) | k==p  = scanl (\c d->c+p*d) (p*p) ws 
                                         : roll (k+w) t u 
                             | True  = roll (k+w) t ps    
    wheel = 2:4:2:4:6:2:6:4:2:4:6:6:2:6:4:2:6:4:6:8:4:2:4:2:
            4:8:6:4:6:2:4:6:2:6:6:4:2:4:6:2:6:4:2:4:2:10:2:10:wheel

union (x:xs) (y:ys) = case (compare x y) of 
           LT -> x : union  xs  (y:ys)
           EQ -> x : union  xs     ys 
           GT -> y : union (x:xs)  ys
union  xs     ys    = xs ++ ys
