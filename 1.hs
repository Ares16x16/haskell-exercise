module A1 where 
import Data.Bits


--Q1 pentanacci
pentanacci :: Int -> Int
pentanacci(1) = 0
pentanacci(2) = 0
pentanacci(3) = 0
pentanacci(4) = 0
pentanacci(5) = 1
pentanacci n = pentanacci(n-5) + pentanacci(n-4) + pentanacci(n-3) + pentanacci(n-2) + pentanacci(n-1)

--Q2 divide mooncake
solve :: Int -> Int -> [Int]
solve 0 0 = []
solve n m =  (n `quot` m) : solve (n - n `quot` m) (m - 1)

--Q3 lookup name
isPrefixOf :: (Eq a) => [a] -> [a] -> Bool
isPrefixOf [] _ = True
isPrefixOf _ [] = False
isPrefixOf (x:xs) (y:ys) = x == y && isPrefixOf xs ys

--cutHyphen :: [[Char]] -> [[Char]]
--cutHyphen (x:xs) = (filter (\xs -> (xs /='-')) x) : xs

replace :: String -> String
replace ('-':xs) = ' ' : replace xs
replace (x:xs)       = x : replace xs
replace ""           = ""

lookupName :: [String] -> String -> [String]
lookupName (x:xs) y
    | isPrefixOf y x = [replace x]
    | otherwise = []
        

--Q4 sorting
sortp :: [a] -> (a -> a -> Bool) -> [a]
g :: Bool -> Bool -> Bool
g True True = True
g True False = True
g False True = False
g False False = False
parti :: (a -> Bool) -> [a] -> ([a], [a])
parti p xs = (filter p xs, filter (not . p) xs)
sortp [] _ = []
sortp (x:xs) pf = re (snd pt) ++ [x] ++ re (fst pt) 
    where p = pf x
          pt = parti p xs
          re s = sortp s pf

--Q5 foldl with predicate
--foldlp :: (b -> Bool) -> (b -> a -> b) -> b -> [a] -> b
--foldlp a f y (x:xs) = foldlp a f (f y x) xs

--Q6 twin pair
isTwinPaired :: [Int] -> Bool

checkAsc :: (Ord a) => [a] -> Bool
checkAsc [] = True
checkAsc [x] = True
checkAsc (x:y:xs) = x <= y && checkAsc (y:xs)

checkDes :: (Ord a) => [a] -> Bool
checkDes [] = True
checkDes [x] = True
checkDes (x:y:xs) = x >= y && checkDes (y:xs)

isTwinPaired xs =  checkAsc (filter even (xs)) && checkDes (filter odd (xs))

--Q7 Reverse Polish Notation
solveRPN :: String -> Int
dup :: Int -> Int
dup x = x
solveRPN = head.foldl fold [].words  
    where   fold (x:y:ys) "+" = (x + y):ys  
            fold (x:y:ys) "-" = (x - y):ys  
            fold (x:y:ys) "*" = (y * x):ys 
            fold (x:y:ys) "/" = (y `div` x):ys  
            fold (x:y:ys) "&" = (y .&. x):ys
            fold (x:y:ys) "|" = (y .|. x):ys
            fold (y:ys) "inc" = (y + 1):ys
            fold (y:ys) "dec" = (y - 1):ys
            fold (y:ys) "dup" = (y:y:ys)
            fold (y:ys) "clear" = (0):ys
            fold xs n = read n:xs  