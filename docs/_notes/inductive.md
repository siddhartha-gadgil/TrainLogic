---
title: Inductive types and type families
date: 2019-09-08
---

In the flavour of type theory we consider (Martin-L&ouml;f Type Theory), all types are of one of the following forms.

* Universes such as `Type` : these are predefined.
* Function types and dependent function types : we can form these using previously defined types.
* Inductive types : we define these, in general using previously defined types.

We have seen several examples of inductive types. Here we see a little more precisely how to define an inductive type.

### Defining and using inductive types

We begin with a high-level view of inductive types. All this will become clearer when we see examples.

When defining an inductive type (or later an inductive type family) $W$, we 

* name $W$ and specify its type : the type of an inductive types $W$ is always the universe `Type`, but for inductive type families we can have other types.
* define a list of _constructors_ for $W$ - these are terms which have types of an appropriate form (which we describe below) so that we can use them to construct terms with type $W$.

Once we define such an inductive type $W$, rules of type theory let us define functions and dependent functions on $W$ by recursion/induction.

### Example

We recall an example, binary rooted trees. There are two ways of constructing a binary tree:

* we take the tree with a single _leaf_.
* we join two trees at a _node_.

We can model this as an inductive type. Namely, we simultaneously define

* the type we are going to introduce, here `BinTree : Type`.
* two terms which are _constructors_, corresponding to the ways of constructing a `BinTree`. These are described by giving them names and specifying their types.

The idris code is as below.

```haskell
data BinTree : Type where
  Leaf : BinTree
  Node : (left: BinTree) -> (right: BinTree) -> BinTree
```

We have defined an inductive type by naming it and its constructors and specifying the types of the constructors. Once we do so, we have introduced three new terms with names and types specified - `BinTree`, `Leaf` and `Node`. We can use the constructor terms to construct terms of the type `BinTree` (this is why they are called constructors).

```haskell
egTree: BinTree
egTree = Node (Node Leaf (Node Leaf Leaf)) Leaf
```

It is useful to have a second example. Below is the natural numbers as defined in the idris standard library.

```haskell
Data type Prelude.Nat.Nat : Type
    Natural numbers: unbounded, unsigned integers which can be pattern matched.
    
Constructors:
    Z : Nat
        Zero
        
    S : Nat -> Nat
        Successor

```

We mentioned earlier that the types of constructors are such that the constructors can be used to form terms of type $W$. Let us call such types constructor-types for $W$. 
We won't describe constructor-types full generality but describe the basic cases. Recursively, a type $T$ is a constructor-type for an inductive type $W$ if

1. $T = W$, as in the case of `Leaf : BinTree` and `Z : Nat`,
2. a type `$A \to T$` where `$T$` is a constructor-type for `$W$` and `A`  is a type that is previously defined (i.e., without defining `$W$`),
3. a type `$W to T$` where `$T$`  can be the type of a constructor.

For example the type of `$S : Nat \to Nat$` is a constructor type because `$T = Nat$` is allowed for a constructor for `Nat` by the first rule and hence `Nat -> T` is allowed by the third rule.
For the constructor `Node : BinTree -> BinTree -> BinTree`, we use the first rule once and the third rule twice.

### Recursive/inductive definitions

In addition to rules for constructing inductive types $W$, we have rules that allow us to define functions on these recursively by giving the definitions for all constructors of $W$,
in general recursively. We have seen several examples of these, two of which we recall.

```haskell
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

```haskell
data LTree : Type -> Type where
  LLeaf : (a: Type) -> (label: a) -> LTree a
  LNode : (a : Type) -> (left : LTree a) -> (right : LTree a) -> LTree a
```

```haskell
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
