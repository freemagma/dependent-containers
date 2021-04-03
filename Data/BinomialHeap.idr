module Data.BinomialHeap

import Data.Binary

%access public export

namespace Tree
    mutual
        data Tree : Nat -> Type -> Type where
            Node : a -> Children n a -> Tree n a

        data Children : Nat -> Type -> Type where
            Nil  : Children Z a
            (::) : Tree n a -> Children n a -> Children (S n) a

mergeTrees : Ord a => Tree n a -> Tree n a -> Tree (S n) a
mergeTrees l@(Node a cl) r@(Node b cr) = 
    if a < b 
        then Node a (r :: cl) 
        else Node b (l :: cr) 

namespace Forest
    data Forest : Nat -> Bin -> Type -> Type where
        Nil  : Forest n MSEnd a
        F0   : Forest (S n) b a -> Forest n (B0 b) a
        F1   : Tree n a -> Forest (S n) b a -> Forest n (B1 b) a

insertTree : Ord a => Tree n a -> Forest n b a -> Forest n (succ b) a
insertTree s Nil      = F1 s Nil
insertTree s (F0 f)   = F1 s f
insertTree s (F1 t f) = F0 $ insertTree (mergeTrees s t) f

mergeForests : Ord a => Forest n b1 a -> Forest n b2 a -> Forest n (b1 + b2) a
mergeForests {b2} Nil f        = rewrite plusMSEndLeftIdentity b2 in f
mergeForests      f Nil        = f
mergeForests (F0 x)   (F0 y)   = F0 $ mergeForests x y
mergeForests (F1 t x) (F0 y)   = F1 t $ mergeForests x y
mergeForests (F0 x)   (F1 t y) = F1 t $ mergeForests x y
mergeForests (F1 s x) (F1 t y) = F0 $ insertTree (mergeTrees s t) (mergeForests x y)


data BinomialHeap : Bin -> Type -> Type where
    Heap : Forest Z b a -> BinomialHeap b a

empty : BinomialHeap MSEnd a
empty = Heap Nil

singleton : a -> BinomialHeap (B1 MSEnd) a
singleton x = Heap $ F1 (Node x Nil) Nil

merge : Ord a => BinomialHeap b1 a -> BinomialHeap b2 a -> BinomialHeap (b1 + b2) a
merge (Heap f1) (Heap f2) = Heap $ mergeForests f1 f2

push : Ord a => a -> BinomialHeap b a -> BinomialHeap (succ b) a
push {b} x f = rewrite (sym $ succIsOnePlus b) in
    merge (singleton x) f

infixr 6 :+>
(:+>) : Ord a => a -> BinomialHeap b a -> BinomialHeap (succ b) a
(:+>) = push

fromList : Ord a => (l : List a) -> BinomialHeap (fromNat $ length l) a
fromList [] = empty
fromList (x :: xs) = x :+> (fromList xs)

peek : Ord a => BinomialHeap (succ b) a -> a

pop : Ord a => BinomialHeap (succ b) a -> (a, BinomialHeap b a)





        