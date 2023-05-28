{-# OPTIONS_GHC -Wno-overlapping-patterns #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Redundant bracket" #-}
{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
{-# HLINT ignore "Redundant if" #-}
{-# HLINT ignore "Avoid lambda" #-}
{-# LANGUAGE RankNTypes #-}
module A2 where
--import Control.Monad.Trans.Accum (accum)
import Data.List(nub)
import Debug.Trace ()

------------------------------------------------------
-- Warm up 
------------------------------------------------------

data Tree a = Leaf | Branch a (Tree a) (Tree a) deriving (Show, Eq)

foldTree :: b -> (a -> b -> b -> b) -> Tree a -> b
foldTree e _ Leaf = e
foldTree e n (Branch a n1 n2) = n a (foldTree e n n1) (foldTree e n n2)

mapTree :: (a -> b) -> Tree a -> Tree b
mapTree f = foldTree Leaf (\x t1 t2 -> Branch (f x) t1 t2)

-- Problem 1 
tree1 :: Tree Integer
tree1 = Branch 1 (Branch 2 Leaf Leaf) (Branch 3 Leaf Leaf)
tree2 :: Tree Integer
tree2 = Branch 4 (Branch 2 Leaf Leaf) (Branch 3 Leaf Leaf)
takeWhileTree :: (a -> Bool) -> Tree a -> Tree a
takeWhileTree c = foldTree
    where foldTree Leaf = Leaf
          foldTree (Branch x l r) | c x = Branch  x (foldTree l) (foldTree r)
                            | otherwise = Leaf

-- Problem 2 
zipTree :: (a -> b -> c) -> Tree a -> Tree b -> Tree c
zipTree f = foldTree (const Leaf) go
    where
        go _ _ _ Leaf = Leaf
        go pl l1 r1 (Branch pr l2 r2) = Branch (f pl pr) (l1 l2) (r1 r2)

------------------------------------------------------
-- Propositional Logic 
------------------------------------------------------

type Name = String
data Prop = Var Name
          | F
          | T
          | Not Prop
          | Prop :|: Prop
          | Prop :&: Prop
          | Prop :->: Prop
          | Prop :<->: Prop
           deriving (Eq, Show)
type Env = [(Name, Bool)]

vars :: Prop -> [Name]
vars = nub . vars'
    where
        vars' F    = []
        vars' (Var v)   = [v]
        vars' (Not f)   = vars' f
        vars' (f :|: g) = vars' f ++ vars' g
        vars' (f :&: g) = vars' f ++ vars' g
        vars' (f :->: g) = vars' f ++ vars' g
        vars' (f :<->: g) = vars' f ++ vars' g

-- Problem 4 
eval :: Env -> Prop -> Bool
eval val F    = False
eval val T    = True
eval val (Var v)   = case (lookup v val) of
                       Nothing -> error ("Error")
                       Just t  -> t
eval val (Not f)  = not (eval val f)
eval val (f :|: g) = (eval val f) || (eval val g)
eval val (f :&: g) = (eval val f) && (eval val g)
eval val (f :->: g) = eval val ((Not f) :|: g)
eval val (f :<->: g) = eval val (f :->: g) && eval val (g :->: f)

props :: [Name] -> [Env]
props [] = [[]]
props (v:vs) = map ((v,True):) ds ++ map ((v,False):) ds
    where ds = props vs

models :: Prop -> [Env]  --incldue all True combination
models f = filter satisfies (props (vars f))
    where satisfies val = eval val f

modelsV :: Prop -> [Env]  --incldue all combination
modelsV f = props (vars f)

-- Problem 3 
--test = (Var "P") :&: (Not (Var "P"))
--Check some True
checkSomeBool :: [Env] -> Bool
checkSomeBool [] = False
checkSomeBool (x1:xs) = check x1
    where
        check [(y1,y2)]
            | y2 = True
            | otherwise = checkSomeBool xs

--check all true
checkAllBool :: [Env] -> Bool
checkAllBool [] = True
checkAllBool [] = True
checkAllBool (x1:xs) = check x1
    where
        check [(y1,y2)]
            | not y2 = False
            | otherwise = checkAllBool xs

satisfiable :: Prop -> Bool
satisfiable = not.null.models
unsatisfiable :: Prop -> Bool
unsatisfiable = not.satisfiable
valid :: Prop -> Bool
valid f = if models f == modelsV f then True else False


-- Problem 5 
dnf1 :: Prop
dnf1 = ((Var "A") :&: (Not (Var "B")) :&: (Not (Var "C"))) :|: ((Not (Var "D")) :&: (Var "E") :&: (Var "F"))
dnf2 :: Prop
dnf2 = ((Var "A") :&: (Var "B")) :|: (Var "C")
dnf3 :: Prop
dnf3 = (Var "A") :&: (Var "B")

findBool :: (Name, Bool) ->Bool
findBool (_,x) = x

findName :: (Name, Bool) -> Name
findName (x,_) = x

oneTerm :: (Name, Bool) -> Prop
oneTerm (x, True) = Var x
oneTerm (x, False) = Not (Var x)

minterm :: Env -> [Prop]
minterm [] = [Not F]
minterm [x] = [oneTerm x]
minterm (x : xs) =  oneTerm x : minterm xs

manyterm :: [Env] -> [[Prop]]
manyterm [] = [[Not F]]
manyterm [x] = [minterm x]
manyterm (x : xs) =  minterm x : manyterm xs

toDNF :: Prop -> [[Prop]]
toDNF f = manyterm (models f) --output DNF from all true values of truth table (~K-map)
                              --which is logically equivalent to the input 
------------------------------------------------------
-- Trie 
------------------------------------------------------

data Trie k v = Trie { value :: Maybe v
                     , subTrees :: [(k, Trie k v)]} deriving (Show)


trie1 :: Trie Integer Integer
trie1 = insertTrie emptyTrie [0] 0
trie2 :: Trie Integer Integer
trie2 = insertTrie trie1 [0, 2] 1
trie3 :: Trie Integer Integer
trie3 = insertTrie trie2 [1] 3
trie4 :: Trie Integer Integer
trie4 = insertTrie trie3 [1,2] 4

emptyTrie :: Trie k v
emptyTrie = Trie Nothing []

--insertTrie :: Eq k => Trie k v -> [k] -> v -> Trie k v
--insertTrie (Trie _ oldChildren) [] value = Trie (Just value) oldChildren
--insertTrie (Trie oldVal oldChild) (c:cs) value = Trie oldVal (newChildren)
--   where
--       newChildren = [(c,insertTrie (Trie (Just value) []) cs value)]

insertTrie :: Eq k => Trie k v -> [k] -> v -> Trie k v
insertTrie t [] x = Trie (Just x) (subTrees t)
insertTrie t (k:ks) x = Trie (value t) (ins (subTrees t) k ks x) 
    where
        ins [] k ks x = [(k, (insertTrie emptyTrie ks x))]
        ins (p:ps) k ks x = if fst p == k
                            then (k, insertTrie (snd p) ks x):ps
                            else p:(ins ps k ks x)

-- Problem 7
lookupTrie :: Eq k => [k] -> Trie k v -> Maybe v
lookupTrie [] t  = value t
lookupTrie (k:ks) t  = case lookup k (subTrees t) of
                        Nothing -> Nothing
                        Just t1 -> lookupTrie ks t1 

-- Problem 8
fromList :: Eq k => [([k], v)] -> Trie k v
fromList (x:xs) =  undefined
     
-- Problem 9 
fromString = undefined

------------------------------------------------------
-- Functional Data Structure
------------------------------------------------------

flatten :: Ord a => Tree a -> [a]
flatten Leaf = []
flatten (Branch x l r) = x : merge (flatten l) (flatten r)

merge :: Ord a => [a] -> [a] -> [a]
merge [] ys = ys
merge xs [] = xs
merge (x:xs) (y:ys) | x <= y = x : merge xs (y:ys)
                    | otherwise = y : merge (x:xs) ys

-- Problem 10 
heapSort :: Ord a => [a] -> [a]
heapSort = flatten . buildHeap

buildHeap :: Ord a => [a] -> Tree a
buildHeap = heapify . buildTree

buildTree ::Ord a => [a] -> Tree a
buildTree [] = Leaf
buildTree (x:xs) = Branch x (buildTree l) (buildTree r)
    where (l, r) = splitAt (length xs `div` 2) xs

heapify :: Ord a => Tree a -> Tree a
heapify Leaf = Leaf
heapify (Branch x l r) = siftDown x (heapify l) (heapify r)

siftDown :: Ord a => a -> Tree a -> Tree a -> Tree a
siftDown x Leaf Leaf = Branch x Leaf Leaf
siftDown x (Branch y l r) Leaf
    |x <= y = Branch x (Branch y l r) Leaf
    |otherwise = Branch y (siftDown x l r) Leaf
siftDown x Leaf (Branch y l r)
    |x <= y = Branch x Leaf (Branch y l r)
    |otherwise = Branch y Leaf (siftDown x l r)
siftDown x (Branch y l1 r1) (Branch z l2 r2)
    |x <= min y z = Branch x (Branch y l1 r1) (Branch z l2 r2)
    |y <= min x z = Branch y (siftDown x l1 r1) (Branch z l2 r2)
    |z <= min x y = Branch z (Branch y l1 r1) (siftDown x l2 r2)

-- Problem 11 
data PQueue a p = Null
                | Fork Order a p (PQueue a p) (PQueue a p) deriving (Show, Eq)
type Order = Int
sampleTree1 :: PQueue String Int
sampleTree1 = Fork 2 "A" 4 (Fork 1 "B" 5 (Fork 1 "C" 6 Null Null) Null) (Fork 1 "D" 8 Null Null)
sampleTree2 :: PQueue String Int
sampleTree2 = Fork 2 "A" 1 (Fork 2 "B" 3 (Fork 1 "C" 4 Null Null) (Fork 1 "D" 6 Null Null)) (Fork 1 "E" 10 (Fork 1 "F" 11 Null Null) Null)
sampleTree1' :: PQueue String Int
sampleTree1' = fork "A" 4 (fork "B" 5 (fork "C" 6 Null Null) Null) (fork "D" 8 Null Null)
sampleTree2' :: PQueue String Int
sampleTree2' = fork "A" 1 (fork "B" 3 (fork "C" 4 Null Null) (fork "D" 6 Null Null)) (fork "E" 10 (fork "F" 11 Null Null) Null)
foo1 :: PQueue [Char] Integer
foo1 = fork "A" 10 Null Null
foo2 :: PQueue [Char] Integer
foo2 = fork "B" 100 Null Null
foo3 :: PQueue [Char] Integer
foo3 = fork "C" 1 Null Null
bar1 :: PQueue [Char] Integer
bar1 = fork "A" 87 Null Null
bar2 :: PQueue [Char] Integer
bar2 = fork "B" 12 Null Null
bar3 :: PQueue [Char] Integer
bar3 = fork "C" 1 Null Null
bar4 :: PQueue [Char] Integer
bar4 = fork "D" 100 Null Null
bar5 :: PQueue [Char] Integer
bar5 = fork "E" 102 Null Null

merges ::Ord b => (a -> b) -> [a] -> [a] -> [a]
merges key xs []= xs
merges key [ ] ys = ys
merges key (x:xs) (y:ys)
    | key x <= key y = x : merges key xs (y : ys)
    | otherwise = y :merges key (x : xs) ys

flattenQ :: Ord p => PQueue a p -> [(a, p)]
flattenQ Null = []
flattenQ (Fork _ a p t1 t2) = (a,p) : merges snd (flattenQ t1) (flattenQ t2)

sval ::PQueue a p -> Order
sval Null = 0
sval (Fork r _ _ _ _) = r

fork :: a -> p -> PQueue a p -> PQueue a p -> PQueue a p
fork a p t1 t2
    | r1 <= r2 = Fork (r1 + 1) a p t1 t2
    | otherwise = Fork (r2 + 1) a p t2 t1
    where  r1 = sval t2
           r2 = sval t1


mergeQ :: Ord p => PQueue a p -> PQueue a p -> PQueue a p
mergeQ Null a = a
mergeQ a Null = a
mergeQ (Fork a1 b1 p1 l1 r1) (Fork a2 b2 p2 l2 r2)
    | p1 <= p2 = fork b1 p1 l1 (mergeQ r1 (Fork a2 b2 p2 l2 r2))
    | otherwise = fork b2 p2 l2 (mergeQ (Fork a1 b1 p1 l1 r1) r2)

insert :: Ord p => a -> p -> PQueue a p -> PQueue a p
insert a p = mergeQ (fork a p Null Null)

delete :: Ord p => PQueue a p -> ((a, p), PQueue a p)
delete (Fork _ a p t1 t2) = ((a,p), mergeQ t1 t2)