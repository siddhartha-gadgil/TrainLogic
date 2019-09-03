module Intro
import Data.Vect
-- a term with its type
three: Nat
three = 3

-- next is a term with type the function type `Nat -> Nat`
next: Nat -> Nat
next n = S n

fct: Nat -> Nat
fct Z = 1
fct (S k) = (S k) * (fct k)

fibPair: Nat -> (Nat, Nat)
fibPair Z = (1, 1)
fibPair (S k) = case (fibPair k) of
                     (a, b) => (b, a + b)

fibo: Nat -> Nat
fibo n = fst (fibPair n)

-- Nat is itself a term with type `Type`
naturals: Type
naturals = Nat

-- as is Nat -> Nat
natToNat: Type
natToNat = Nat -> Nat

-- functions of two variables can be viewed as iterated functions by Currying
add: Nat -> Nat -> Nat
add k j = k + j

-- we can define inductive types by listing all intro rules. `BinTree` is a type
data BinTree: Type where
  Leaf: BinTree
  Node : (left: BinTree) -> (right: BinTree) -> BinTree

vertices: BinTree -> Nat
vertices Leaf = 1
vertices (Node left right) = (vertices left) + (vertices right)

-- We have labelled trees, which depend on a type.
data LTree: Type -> Type where
  LLeaf : (a: Type) -> (label: a) -> LTree a
  LNode : (a: Type) -> (left: LTree a) -> (right: LTree a) -> LTree a

vertexList: (a: Type) -> LTree a -> List a
vertexList a (LLeaf a label) = [label]
vertexList a (LNode a left right) = (vertexList a left) ++ (vertexList a right)


-- a type family
Tuple: Nat -> Type
Tuple Z = Unit
Tuple (S k) = (Nat, Tuple k)

--- countdown is a dependent function, and its type is a Pi-Type
countdown: (n: Nat) -> Tuple n
countdown Z = ()
countdown (S k) = ((S k), countdown k)

cntd : (n: Nat) -> Vect (S n) Nat
cntd Z = [0]
cntd (S k) = (S k) :: (cntd k)

append: (n: Nat) -> (a: Type) -> Vect n a -> a -> Vect (S n) a
append Z a [] x = x :: []
append (S len) a (y :: xs) x = y :: (append len a xs x)

reverse: (n: Nat) -> (a: Type) -> Vect n a -> Vect n a
reverse Z a [] = []
reverse (S len) a (x :: xs) = append len a (reverse len a xs) x

zip : (n: Nat) -> (a: Type) -> (b: Type) -> Vect n a -> Vect n b -> Vect n (a, b)
zip Z a b [] [] = []
zip (S len) a b (x :: xs) (y :: ys) = (x, y) :: (zip _ _ _ xs ys)

filter : (n: Nat) -> (a: Type) -> (vec: Vect n a) -> (condition: a -> Bool) -> (m: Nat ** Vect m a) -- dependent pair
filter Z a [] condition = (Z ** [])
filter (S len) a (x :: xs) condition = case filter len a xs condition of
                                            (m ** pf) => if (condition x) then (S m ** x :: pf) else (m ** pf)
