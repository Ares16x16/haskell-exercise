module First where

double :: Int -> Int
double x = x + x

triple :: Num a => a -> a
triple x = x + x + x

quadruple :: Int -> Int
quadruple x = double (double x)

factorial :: (Num a, Enum a) => a -> a
factorial n = product [1..n]

average :: Foldable t => t Int -> Int
average ns  = sum ns `div` length ns
