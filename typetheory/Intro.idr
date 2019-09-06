module Intro
import Data.Vect

-- a term (object) with its type
three : Nat
three = 3

next: Nat -> Nat -- the type is a function type
next n = n + 1

-- a recursive definition
fct: Nat -> Nat
fct Z = 1
fct (S k) = (S k) * (fct k) -- this is primitive recursion

loop: Nat -> Nat
loop Z = Z
loop (S k) = loop k + (loop (k + 2)) -- this is horrible

fibPair: Nat -> (Nat, Nat)
fibPair Z = (1, 1)
fibPair (S k) = case fibPair k of
                     (a, b) => (b, a + b)

fibo: Nat -> Nat
fibo n = fst (fibPair n)

-- types are terms, i.e., first class, so have types
Naturals : Type
Naturals = Nat

natToNat : Type
natToNat = Nat -> Nat

anotherThree : Naturals
anotherThree = 3

add : Nat -> Nat -> Nat -- Curryed type
add m n = m + n

data BinTree : Type where
  Leaf : BinTree
  Node : (left: BinTree) -> (right: BinTree) -> BinTree

egTree: BinTree
egTree = Node (Node Leaf (Node Leaf Leaf)) Leaf

numberVertices : BinTree -> Nat
numberVertices Leaf = 1
numberVertices (Node left right) =
  (numberVertices left) + (numberVertices right) + 1

-- a parametrized type (generic)
data LTree : Type -> Type where
  LLeaf : (a: Type) -> (label: a) -> LTree a
  LNode : (a : Type) -> (left : LTree a) -> (right : LTree a) -> LTree a

egLTree : LTree Nat
egLTree =
  LNode Nat (
  LNode Nat (LLeaf Nat 1) (LNode Nat (LLeaf Nat 3) (LLeaf Nat 4))
  ) (LLeaf Nat 7)

labels : (a: Type) -> LTree a -> List a
labels a (LLeaf a label) = [label]
labels a (LNode a left right) =
  (labels a left) ++ (labels a right)

Tuple: Nat -> Type -- tuples of Natural numbers
Tuple Z = Unit
Tuple (S k) = (Nat, Tuple k)

egTuple : Tuple 2
egTuple = (3, (4, ()))

countdown : (n: Nat) -> Tuple n -- this is a dependent function
countdown Z = ()
countdown (S k) = (S k, countdown k)

cntd : (n: Nat) -> Vect (S n) Nat
cntd Z = [0]
cntd (S k) = (S k) :: (cntd k)

zipNat : (n: Nat) -> Vect n Nat -> Vect n Nat -> Vect n (Nat, Nat)
zipNat Z [] [] = []
zipNat (S len) (x :: xs) (y :: ys) = (x , y) :: (zipNat len xs ys)

zip : (n: Nat) -> (a: Type) -> (b: Type) -> Vect n a -> Vect n b -> Vect n (a, b)
zip Z a b [] [] = []
zip (S len) a b (x :: xs) (y :: ys) =
  (x, y) :: (zip len a b xs ys)

append: (n: Nat) -> (a: Type) -> (x: a) -> Vect n a -> Vect (S n) a
append Z a x [] = [x]
append (S len) a x (y :: xs) =
  y :: (append len a x xs)

filter: (n: Nat) -> (a: Type) -> (p: a -> Bool) -> Vect n a -> (m: Nat ** Vect m a)
filter Z a p [] = (Z ** [])
filter (S len) a p (x :: xs) =
  (case p x of
        False => filter len a p xs
        True => (case filter len a p xs of
                      (m ** pf) =>
                        (S m ** x :: pf) ))




-- some space
