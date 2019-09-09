---
title: Inductive types and type families
date: 2019-09-08
---

__Type Theory__ is a language. We have taken an _immersion learning_ approach to it (as well as to the language of sets) - where we learn a language by listening to it being spoken, relating to known languages and eventually learning the specific idioms. In this note we take a more formal view, looking more explicitly at the rules of the grammar. Hopefully this will complement immersion learning.

## Inductive Types: a more formal view

In the flavour of type theory we consider, namely Martin-L&ouml;f Type Theory (MLTT), all types are of one of the following forms.

* Universes such as `Type` - these are predefined.
* Function types and dependent function types - we can form these using previously defined types.
* Inductive types - we define these, possibly using previously defined types.

We have seen several examples of inductive types. Here we see a little more precisely how to define an inductive type.

### Defining and using inductive types

We begin with a high-level view of inductive types. All this will become clearer when we see examples.

When defining an inductive type (or later an inductive type family) $W$, we 

* name $W$ and specify its type - the type of an inductive types $W$ is always the universe `Type`, but for inductive type families we can have other types.
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
We will not describe constructor-types full generality but describe the basic cases (we have omitted a slightly more complicated way to construct such types). Recursively, a type $T$ is a constructor-type for an inductive type $W$ if

1. $T = W$, as in the case of `Leaf : BinTree` and `Z : Nat`,
2. `$T = A \to T'$` where `$T'$` is a constructor-type for `$W$` and `A`  is a type that is previously defined (i.e., without defining `$W$`),
3. `$T = W \to T'$` where `$T'$` is a constructor-type for `$W$`.

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

Let us first consider the type family `LTree : Type -> Type`. This is defined as follows.

```haskell
data LTree : Type -> Type where
  LLeaf : (a: Type) -> (label: a) -> LTree a
  LNode : (a : Type) -> (left : LTree a) -> (right : LTree a) -> LTree a
```

For a fixed type, say `Nat`, `LTree Nat : Type` is an inductive type with constructors `LLeaf Nat` and `LNode Nat`. Such inductive type families are a simple generalization of inductive types, generally called _parametrized_ inductive type families (similar to _generics_ in many programming languages). Thus we have simply introduced a bunch of inductive types rather than
just one.

On the other hand, the case of _Vectors_ is more subtle. To see this, first look at the definition.

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

The _length_ of a vector is what is called an _index_, not a parameter. The key difference is that the constructor `(::)` for vectors of length, say, $7$ involves vectors of length $6$.
As a consequence we cannot make recursive definitions on vectors of a fixed length. Instead we need to simultaneously define a function on vectors of all lengths. For example, consider the append function.

```haskell
append: (n: Nat) -> (a: Type) -> (x: a) -> Vect n a -> Vect (S n) a
append Z a x [] = [x]
append (S len) a x (y :: xs) =
  y :: (append len a x xs)
```

The function is defined by specifying how to append to the empty vector, and then how to append to a vector of length $n + 1$ in terms of appending to a vector of length $n$. Note that `elem` for a vector is a parameter, as constructors (and hence recursion) for a fixed type `elem` (e.g. `elem = Nat`) are not related to those for vectors with any other element type.
