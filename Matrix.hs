module Matrix where

determinant :: (Num a) => [[a]] -> a
determinant [] = 1
determinant [[
