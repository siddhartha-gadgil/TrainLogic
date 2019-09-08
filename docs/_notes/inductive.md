---
title: Inductive types and type families
date: 2019-09-08
---

Inductive types and type families are very important in Type Theory. Indeed in the flavour of type theory we consider, all types except universes and
(dependent) function types are inductive types. Here we take a more careful look at what these are.

First we consider an example, binary rooted trees. There are two ways of constructing a binary tree:

* we take the tree with a single _leaf_.
* we join two trees at a _node_.

We can model this as an inductive type. Namely, we simultaneously define

* the type we are going to introduce, here `BinTree : Type`.
* two terms which are _constructors_, corresponding to the ways of constructing a `BinTree`. These are described by giving them names and specifying their types.

The idris code is as below.

```idris
data BinTree : Type where
  Leaf : BinTree
  Node : (left: BinTree) -> (right: BinTree) -> BinTree
```

We have defined an inductive type by naming it and its constructors and specifying the types of the constructors. Once we do so, we have introduced three new terms with names  
and types specified - `BinTree`, `Leaf` and `Node`. We can use the constructor terms to construct terms of the type `BinTree` (this is why they are called constructors).

```idris
egTree: BinTree
egTree = Node (Node Leaf (Node Leaf Leaf)) Leaf
```

It is useful to have a second example. Below is the natural numbers as defined in the idris standard library.

```idris
Data type Prelude.Nat.Nat : Type
    Natural numbers: unbounded, unsigned integers which can be pattern matched.
    
Constructors:
    Z : Nat
        Zero
        
    S : Nat -> Nat
        Successor

```

What we have not described is what types can be the types of constructors. We won't describe this in full generality but describe the
permitted types in the basic cases. Recursively, a type `T` is can be the type of a constructor for an inductive type `W` if

1. `T = W`, as in the case of `Leaf : BinTree` and `Z : Nat`,
2. a type `A -> T` where `T` can be the type of a constructor and `A`  is a type that is previously defined,
3. a type `W -> T` where `T`  can be the type of a constructor.

For example the type of `S : Nat -> Nat` si allowed because `T = Nat` is allowed for a constructor for `Nat` by the first rule and hence `Nat -> T` is allowed by the third rule.
For the constructor `Node : BinTree -> BinTree -> BinTree`, we use the first rule once and the third rule twice.

### Recursive/inductive definitions

In addition to rules for constructing inductive types $W$, we have rules that allow us to define functions on these recursively by giving the definitions for all constructors of $W$,
in general recursively. We have seen several examples of these, two of which we recall.

```idris
numberVertices : BinTree -> Nat
numberVertices Leaf = 1
numberVertices (Node left right) =
  (numberVertices left) + (numberVertices right) + 1

fct: Nat -> Nat
fct Z = 1
fct (S k) = (S k) * (fct k)
```

We can similarly define dependent functions on an inductive type $W$. This is usually called _induction_ rather than recursion. We will see the relation to proofs by induction 
in another post.

## Inductive type families

More generally, rather than defining a single inductive type we can define an _inductive type family_. This is similar to the above, except that the final target of constructors
is some specific member of the type family. We have seen two examples - labelled trees and vectors.

```idris
data LTree : Type -> Type where
  LLeaf : (a: Type) -> (label: a) -> LTree a
  LNode : (a : Type) -> (left : LTree a) -> (right : LTree a) -> LTree a
```

```idris
*Intro> :doc Vect
Data type Data.Vect.Vect : (len : Nat) -> (elem : Type) -> Type
    Vectors: Generic lists with explicit length in the type
    Arguments:
        len : Nat  -- the length of the list

        elem : Type  -- the type of elements

Constructors:
    Nil : Vect 0 elem
        Empty vector

    (::) : (x : elem) -> (xs : Vect len elem) -> Vect (S len) elem
        A non-empty vector of length S len, consisting of a head element and the rest of the list, of length len.
        infixr 7
```
