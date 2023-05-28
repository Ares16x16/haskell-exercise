{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE BlockArguments #-}
{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use camelCase" #-}
{-# HLINT ignore "Avoid lambda" #-}
{-# HLINT ignore "Use isJust" #-}
{-# HLINT ignore "Use lambda-case" #-}
{-# HLINT ignore "Use tuple-section" #-}

module Template where

import Parsing
import Control.Monad.Trans.State ( get, put, State, evalState, modify )
import Control.Monad ( ap, liftM, liftM2 )
import GHC.Base (liftA)
import Data.Char
import Data.List
import Data.Ord
import Data.Bits ( Bits((.|.), (.&.)) )

---------------------------------
-- IO Interaction
---------------------------------
-- Problem 1
initBoard :: Int -> [Int]
initBoard i = take i [1,2..]

next :: Int -> Int
next 1 = 2
next 2 = 1

counter:: Int -> Int
counter c = c + 1

move :: [Int] -> Int -> Int -> [Int]
move board row num = [refresh ro nu | (ro,nu) <- zip [1..] board]
   where refresh ro nu = if ro == row then nu-num else nu

print_board :: [Int] -> Int -> IO ()
print_board board i = putStr $ unlines [replicate star '*' ++ replicate (i - star) ' ' ++  " | "  ++ show row | (star, row) <- zip board [1..length board]]

getDigit :: String -> IO Int
getDigit msg =  do putStr msg
                   x <- getChar
                   if isDigit x then
                        do return (digitToInt x)
                   else getDigit ""

maingame :: [Int] -> Int -> Int -> IO ()
maingame board i player =
   do print_board board i
      if all (== 0) board then
         do putStr "\nPlayer "
            putStr (show (next player))
            putStrLn " wins!"
      else
         do putStr "\nPlayer "
            print player
            row <- getDigit "Enter a row number: "
            num <- getDigit "Stars to remove: "
            putStr "\n"

            if row <= i && board !! (row-1) >= num then
                  maingame (move board row num) i (next player)
            else if row > i then
                  do  putStr "Warning: There are only "
                      putStr (show i)
                      putStrLn " rows in the game. Try again.\n"
                      maingame board i player
            else
                  do  putStr "Warning: There are only "
                      putStr (show (board !! (row-1)))
                      putStr " stars in the row "
                      putStr (show row)
                      putStrLn ". Try again.\n"
                      maingame board i player

nim :: Int -> IO ()
nim i = maingame (initBoard i) i 1

-- Problem 2
nextAI :: String -> String
nextAI "Player" = "AI"
nextAI "AI" = "Player"

reverseList :: [Int] -> [Int]
reverseList = foldl (\acc x -> x : acc) []

findMaxRow :: Ord a => [a] -> Int
findMaxRow xs = head $ filter ((== maximum xs) . (xs !!)) [0..]

maingameAI :: [Int] -> Int -> String -> IO ()
maingameAI board i player =
   do print_board board i
      if all (== 0) board then
         do putStr "\n"
            putStr (nextAI player)
            putStrLn " wins!"
      else if player == "Player" then
         do putStrLn "\nPlayer "
            row <- getDigit "Enter a row number: "
            num <- getDigit "Stars to remove: "
            putStr "\n"
            if row <= i && board !! (row-1) >= num then
                  maingameAI (move board row num) i (nextAI player)
            else if row > i then
                  do  putStrLn ""
                      putStr "Warning: There are only "
                      putStr (show i)
                      putStrLn " rows in the game. Try again.\n"
                      maingameAI board i player
            else
                  do  putStrLn ""
                      putStr "Warning: There are only "
                      putStr (show (board !! (row-1)))
                      putStr " stars in the row "
                      putStr (show row)
                      putStrLn ". Try again.\n"
                      maingameAI board i player

        else do putStrLn "\nAI "
                let row = findMaxRow board + 1
                let num = board !! (row - 1)
                --print board
                putStr "Enter a row number: "
                print row
                putStr "Stars to move: "
                print num
                putStr "\n"
                maingameAI (move board row num) i (nextAI player)

nimAI :: Int -> IO ()
nimAI i = maingameAI (initBoard i) i "Player"

---------------------------------
-- Functional Parsing
---------------------------------

data Binop = Add | Sub | Mul | Div | Mod deriving (Eq, Show)

data Expr = Bin Binop Expr Expr
          | Val Int
          | Var String deriving (Eq, Show)

type Env = [(String, Int)]

add :: Maybe Int -> Maybe Int -> Maybe Int
add Nothing _ = Nothing
add _ Nothing = Nothing
add (Just x) (Just y) = Just (x + y)

divide :: Maybe Int -> Maybe Int -> Maybe Int
divide Nothing _ = Nothing
divide _ Nothing = Nothing
divide (Just x) (Just y) = Just (div x y)

mult :: Maybe Int -> Maybe Int -> Maybe Int
mult Nothing _ =Nothing
mult _ Nothing =Nothing
mult (Just x ) (Just y) =Just (x * y)

sub :: Maybe Int -> Maybe Int -> Maybe Int
sub Nothing _ =Nothing
sub _ Nothing = Nothing
sub (Just x) (Just y) = Just (x - y)

modulus :: Maybe Int -> Maybe Int -> Maybe Int
modulus Nothing _ =Nothing
modulus _ Nothing =Nothing
modulus (Just x) (Just y)= Just (mod x y)

envToVal :: (a, b) -> b
envToVal  (x,y) = y

envToStr :: (a, b) -> a
envToStr (x,y) = x

envout :: Env -> String -> Maybe Int
envout [] y   = Nothing
envout (x:xs) y = if envToStr x == y then Just (envToVal x) else envout xs y

-- Problem 3

eval :: Env -> Expr -> Maybe Int
eval xs (Val x)       = Just x
eval xs (Var x)       = if envout xs x /= Nothing then envout xs x else Nothing
eval xs (Bin Add a b) = add (eval xs a) (eval xs b)
eval xs (Bin Sub a b) = sub (eval xs a) (eval xs b)
eval xs (Bin Mul a b) = mult (eval xs a) (eval xs b)
eval xs (Bin Div a b) = if eval xs b == Just 0 then Nothing
                          else divide (eval xs a) (eval xs b)
eval xs (Bin Mod a b) = if eval xs b == Just 0  then Nothing
                          else modulus (eval xs a) (eval xs b)

-- Problem 4

--expr := term op_term
pExpr_opterm :: Expr -> Parsing.Parser Expr
pExpr_opterm x = do parse_op_term x
pExpr :: Parsing.Parser Expr
pExpr = do x <- parse_term
           pExpr_opterm x +++ return x

--op_term := ('+' | '-') term op_term | ''
pOpfactor_add :: Expr -> Expr -> Parsing.Parser Expr
pOpfactor_add ex y = return (Bin Add ex y)
pOpfactor_Padd :: Expr -> Expr -> Parsing.Parser Expr
pOpfactor_Padd ex y = do parse_op_term (Bin Add ex y)
pOpfactor_plus :: Expr -> Parsing.Parser Expr
pOpfactor_plus ex = do char '+'
                       y <- parse_term
                       pOpfactor_Padd ex y +++ pOpfactor_add ex y

pOpfactor_sub :: Expr -> Expr -> Parsing.Parser Expr
pOpfactor_sub ex y = do parse_op_term (Bin Sub ex y)
pOpfactor_hyphen :: Expr -> Parsing.Parser Expr
pOpfactor_hyphen ex = do char '-'
                         y <- parse_term
                         pOpfactor_sub ex y +++ return (Bin Sub ex y)

parse_op_term :: Expr -> Parser Expr
parse_op_term ex = pOpfactor_plus ex +++ pOpfactor_hyphen ex

--term := factor op_factor
ptermOpFactor :: Expr -> Parsing.Parser Expr
ptermOpFactor x = do parse_op_factor x
parse_term :: Parsing.Parser Expr
parse_term = do x <- parseFactor
                ptermOpFactor x +++ return x


--op_factor := ('*' | '/' | '%') factor op_factor | ''
pOpfactor_mult :: Expr -> Expr -> Parsing.Parser Expr
pOpfactor_mult ex y = do parse_op_factor (Bin Mul ex y)
pOpfactor_ast :: Expr -> Parsing.Parser Expr
pOpfactor_ast ex = do char '*'
                      y <- parseFactor
                      pOpfactor_mult ex y +++ return (Bin Mul ex y)

pOpfactor_div :: Expr -> Expr -> Parsing.Parser Expr
pOpfactor_div ex y = do parse_op_factor (Bin Div ex y)
pOpfactor_slash :: Expr -> Parsing.Parser Expr
pOpfactor_slash ex = do char '/'
                        y <- parseFactor
                        pOpfactor_div ex y +++ return (Bin Div ex y)

pOpfactor_mod :: Expr -> Expr -> Parsing.Parser Expr
pOpfactor_mod ex y = do parse_op_factor(Bin Mod ex y)
pOpfactor_pa :: Expr -> Parsing.Parser Expr
pOpfactor_pa ex = do char '%'
                     y <- parseFactor
                     pOpfactor_mod ex y +++ return (Bin Mod ex y)

parse_op_factor :: Expr -> Parsing.Parser Expr
parse_op_factor ex =  pOpfactor_ast ex +++ pOpfactor_slash ex +++ pOpfactor_pa ex

--factor := '(' expr ')' | integer | identifier
pFactor_expr :: Parsing.Parser Expr
pFactor_expr = do char '('
                  expr <- pExpr
                  char ')'
                  return expr
pFactor_int :: Parsing.Parser Expr
pFactor_int = do Val <$> integer

pFactor_identifier :: Parsing.Parser Expr
pFactor_identifier = do Var <$> identifier

parseFactor :: Parsing.Parser Expr
parseFactor =  pFactor_expr +++ pFactor_int +++ pFactor_identifier


-- Problem 5
exprType :: Num p => Maybe Expr -> p
exprType (Just (Val a)) = 1
exprType (Just (Var a)) = 2
exprType _ = 3

compute :: Expr -> Int
compute (Val a) = a
compute (Var a) = 0
compute (Bin Add x y) = compute x + compute y
compute (Bin Sub x y) = compute x - compute y
compute (Bin Mul x y) = compute x * compute y
compute (Bin Div x y) = div (compute x)  (compute y)
compute (Bin Mod x y) = mod (compute x) (compute y)

optimize :: Expr -> Maybe Expr
optimize (Val x) = Just (Val x)
optimize (Var x) = Just (Var x)
optimize (Bin Add x (Val 0)) = optimize x
optimize (Bin Add (Val 0) x) = optimize x
optimize (Bin Add x y)
  | exprType (optimize x) == 1 && exprType (optimize y)== 1 = Just (Val(compute x + compute y))
  | exprType (optimize x) == 1 && exprType (optimize y) == 2 && (compute x /= 0) = Just (Bin Add (Val (compute x)) y)
  | exprType (optimize x) == 1 && exprType (optimize y) == 2 && (compute x == 0) = optimize y
  | exprType (optimize x) == 2 && exprType (optimize y)== 1  && (compute y /= 0) = Just (Bin Add x (Val (compute y)))
  | exprType (optimize x) == 2 && exprType (optimize y)== 1  && (compute y == 0) = optimize x
  | otherwise = Nothing

optimize (Bin Sub x (Val 0)) = optimize x
optimize (Bin Sub (Val 0) x ) = optimize x
optimize (Bin Sub x y)
  | exprType (optimize x) == 1 && exprType (optimize y) == 1 = Just (Val(compute x - compute y))
  | exprType (optimize x) == 1 && exprType (optimize y) == 2 = Just (Bin Sub (Val (compute x)) y)
  | exprType (optimize x) == 2 && exprType (optimize y) == 1 && compute y /= 0 = Just (Bin Sub x (Val (compute y)))
  | exprType (optimize x) == 2 && exprType (optimize y) == 1 && compute y == 0 = optimize x
  | otherwise = Nothing

optimize (Bin Mul (Val 0) _) = Just (Val 0)
optimize (Bin Mul _ (Val 0)) = Just (Val 0)
optimize (Bin Mul x y)
  | exprType (optimize x) == 1 && exprType (optimize y) == 1 = Just (Val(compute x + compute y))
  | exprType (optimize x) == 1 && exprType (optimize y) == 2 && (compute x /= 0) = Just (Bin Mul (Val (compute x)) y)
  | exprType (optimize x) == 1 && exprType (optimize y) == 2 && (compute x == 0) = Just (Val 0)
  | exprType (optimize x) == 2 && exprType (optimize y) == 1 && (compute y /= 0) = Just (Bin Mul x (Val (compute y)))
  | exprType (optimize x) == 2 && exprType (optimize y) == 1 && (compute y == 0) = Just (Val 0)
  | otherwise = Nothing

optimize (Bin Div x y)
  | exprType (optimize y) == 1 && compute y == 0 = Nothing
  | exprType (optimize x) == 1 && exprType (optimize y) == 1 = Just (Val (compute x + compute y))
  | exprType (optimize x) == 1 && exprType (optimize y) == 2 = Just (Bin Div (Val(compute x)) y)
  | exprType (optimize x) == 2 && exprType (optimize y) == 1 = Just (Bin Div x (Val(compute y)))
  | otherwise = Nothing

optimize (Bin Mod x y)
  | exprType (optimize y) == 1 && compute y == 0 = Nothing
  | exprType (optimize x) == 1 && exprType (optimize y) == 1 = Just (Val (compute x + compute y))
  | exprType (optimize x) == 1 && exprType (optimize y) == 2 = Just (Bin Mod (Val(compute x)) y)
  | exprType (optimize x) == 2 && exprType (optimize y) == 1 = Just (Bin Mod x (Val(compute y)))
  | otherwise = Nothing

---------------------------------
-- Programming with Monads
---------------------------------

-- Problem 6

type EvalState = [Int]
type EvalValue = Int

push6 x = modify (x:)
pop6 = do xs <- get
          put (tail xs)
          if not $ null xs then
            return (head xs)
          else
            return 0

evalL :: [String] -> State EvalState EvalValue
evalL ("inc":s) = do x <- pop6
                     push6 $ x + 1
                     evalL s
evalL ("dec":s) = do x <- pop6
                     push6 $ x - 1
                     evalL s
evalL ("+":s) = do y <- pop6
                   x <- pop6
                   push6 $ x + y
                   evalL s
evalL ("-":s) = do y <- pop6
                   x <- pop6
                   push6 $ x - y
                   evalL s
evalL ("*":s) = do y <- pop6
                   x <- pop6
                   push6 $ x * y
                   evalL s
evalL ("/":s) = do y <- pop6
                   x <- pop6
                   push6 $ x `div` y
                   evalL s
evalL ("&":s) = do y <- pop6
                   x <- pop6
                   push6 $ x .&. y
                   evalL s
evalL ("|":s) = do y <- pop6
                   x <- pop6
                   push6 $ x .|. y
                   evalL s
evalL ("clear":s) = do x <- pop6
                       push6 0
                       evalL s
evalL ("dup":s) = do   x <- pop6
                       push6 x
                       push6 x
                       evalL s
evalL (x:s) = do push6 $ read x
                 evalL s

evalL [] = pop6

solveRPN :: String -> Int
solveRPN xs = evalState (evalL . words $ xs) []

-- Problem 7

newtype Stack a = Stack {runStack :: [Int] -> ([Int], a)}

instance Functor Stack where
    fmap = liftM

instance Applicative Stack where
    pure x = Stack $ \s -> (s, x)
    (<*>) = ap

instance Monad Stack where
    return = pure
    m >>= k = Stack $ \s -> case runStack m s of
        (s', x) -> runStack (k x) s'

pop :: Stack Int
pop = Stack {runStack = \st -> case st of
                          (x:xs) -> (xs, x)
                          _ -> (st, 0)}

push :: Int -> Stack Int
push x = Stack {runStack = \st -> (x:st, x)}

evalStack :: Stack Int -> [Int] -> Int
evalStack m s = snd (runStack m s)

evalL' :: [String] -> Stack Int
evalL' ("inc":s) = do x <- pop
                      push $ x + 1
                      evalL' s
evalL' ("dec":s) = do x <- pop
                      push $ x - 1
                      evalL' s
evalL' ("+":s) = do y <- pop
                    x <- pop
                    push $ x + y
                    evalL' s
evalL' ("-":s) = do y <- pop
                    x <- pop
                    push $ x - y
                    evalL' s
evalL' ("*":s) = do y <- pop
                    x <- pop
                    push $ x * y
                    evalL' s
evalL' ("/":s) = do y <- pop
                    x <- pop
                    push $ x `div` y
                    evalL' s
evalL' ("&":s) = do y <- pop
                    x <- pop
                    push $ x .&. y
                    evalL' s
evalL' ("|":s) = do y <- pop
                    x <- pop
                    push $ x .|. y
                    evalL' s
evalL' ("clear":s) = do x <- pop
                        push 0
                        evalL' s
evalL' ("dup":s) = do  x <- pop
                       push x
                       push x
                       evalL' s

evalL' (x:s) = do push $ read x
                  evalL' s
evalL' [] = pop

-- Problem 8

(>=>) :: Monad m => (a -> m b) -> (b -> m c) -> a -> m c
f >=> g = \x -> f x >>= g

safeLog :: (Ord a, Floating a) => a -> Maybe a
safeLog x
  | x > 0 = Just (log x)
  | otherwise = Nothing

safeSqrt :: (Ord a, Floating a) => a -> Maybe a
safeSqrt x
  | x >= 0 = Just (sqrt x)
  | otherwise = Nothing

logSqrt :: Double -> Double
logSqrt = log . sqrt

safeLogSqrt :: (Ord a, Floating a) => a -> Maybe a
safeLogSqrt = safeSqrt >=> safeLog


-- Problem 9

zipL :: Monad m => m a -> m b -> m (a,b)
zipL = liftM2 (,)


-- Problem 10 (Advanced)

newtype LM a = LM { getLM :: [Maybe a] }
  deriving Functor

instance Applicative LM where
  pure = return
  (<*>) = liftM2 ($)

instance Monad LM where
  return :: a -> LM a
  return x = LM [Just x]

  (>>=) :: LM a -> (a -> LM b) -> LM b
  LM [Nothing] >>= f = LM [Nothing]
  LM [Just x] >>= f = f x
  LM [] >>= f = LM [Nothing]

---------- Monad Laws Reasoning ----------------
--1. Left Identity of return x >>= f = f x; return x >>= f = [Just x] >>= f = f x  
--2. Right Identity of return m >>= return = m; ([Nothing] >>= f_ >>= g = Nothing >>= g = Nothing); [Nothing] >>= (\x -> (f x >>= g)) = Nothing
--3. Associativity of (>>=) m >>= (\x -> f x >>= g) = (m >>= f) >>= g
--                          ([Nothing] >>= f ) >>= g = Nothing >>= g = Nothing == [Nothing] >>=  (\x -> (f x >>= g)) = Nothing;
--                          ([Just x] >>= f) >>= g = f x >>= g == [Just x] >>= (\c -> (f c >>= g)) = (\c -> (f c >>= g)) x = f x >>= g
-------------------------------------------------

newtype ML a = ML { getML :: Maybe [a] }
  deriving Functor

instance Applicative ML where
  pure = return
  (<*>) = liftM2 ($)

instance Monad ML where
  return :: a -> ML a
  return x = ML (Just[x])

  (>>=) :: ML a -> (a -> ML b) -> ML b
  ML Nothing >>= f = ML Nothing
  ML (Just[x]) >>= f = f x
  ML (Just []) >>= f = ML Nothing
---------- Monad Laws Reasoning ----------------
--1. Left Identity of return x >>= f = f x; return x >>= f = [Just x] >>= f = f x   
--2. Right Identity of return m >>= return = m; Nothing >>= f_ >>= g = Nothing >>= g = Nothing; Nothing >>= (\x -> (f x >>= g)) = Nothing
--3. Associativity of (>>=) m >>= (\x -> f x >>= g) = (m >>= f) >>= g
--                          Nothing >>= f  >>= g = Nothing >>= g = Nothing == Nothing >>=  (\x -> (f x >>= g)) = Nothing;
--                          (Just [x] >>= f) >>= g = f x >>= g == Just [x] >>= (\c -> (f c >>= g)) = (\c -> (f c >>= g)) x = f x >>= g
-------------------------------------------------