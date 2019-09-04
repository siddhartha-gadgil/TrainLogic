---
title: Dependent Type theory
date: Sept 4, 2019
---

We sketch an introduction to the concepts of _dependent type theory_ accompanied by `idris` code. This note does not include _propositions as types_, which will be in the sequel. This is an annotated version of the live code from the lecture but wih some reordering for a better flow.

### Terms and Types

Objects in type theory are called _terms_. Each _term_ has a type, generally unique. The notation `a: A` means `a` is a term of type `A`.
For example `Nat` is a type and we define a term `three` of type `Nat`. Note that in `idris` we __must__ specify the type of a term being defined
before defining it.

```
three : Nat
three = 3
```

### Functions and function types

The next term we define is a function. Observe that its type is the _function type_ `Nat -> Nat`. A function is just a term whose type is a
function type.

```
next : Nat -> Nat
next n = n + 1
```

We can _apply_ a function to a value in its domain. For example, we see:
```
*Intro> next 3
4 : Nat
```

#### Currying

Function types are central to functional programming. In mathematics and programming, one also considers functions of more that one variable.
However we can instead use a tricj called _Currying_ to define _iterated functions_.

```
add : Nat -> Nat -> Nat
add m n = m + n
```

This means, for example, that `add 3` is the function given by adding `3`. We see:
```
*Intro> add 2
add 2 : Nat -> Nat
*Intro> add 2 3
5 : Nat
```


### Recursive definitions

A very important way to define functions is _recursively_, i.e., a function `f` is defined by specifying `f(n)` in terms of other values `f(m)`.
A specific kind of recursion is _primitive recursion_. For functions on natural numbers this means that we define `f(0)` as a constant (i.e. without using `f` in the rhs) and define
`f(n + 1)` in terms of `f(n)` only.
```
fct: Nat -> Nat
fct Z = 1
fct (S k) = (S k) * (fct k)
```

We see:
```
*Intro> fct 5
120 : Nat
```

An important feature of _primitive recursion_ is that the definitions are guaranteed to terminate for all inputs, i.e. the functions are `total`.
Indeed this can be checked by idris.
```
*Intro> :total fct
Intro.fct is Total
```

For contrast, consider the following function. It is easy to see that trying to calculate `loop 1` runs forever.

```
loop: Nat -> Nat
loop Z = Z
loop (S k) = loop k + (loop (k + 2))
```

Naturally, idris is suspicious.

```
*Intro> :total loop
Intro.loop is possibly not total due to recursive path:
    Intro.loop, Intro.loop, Intro.loop
```

In our next example, we define _Fibonacci numbers_. The usual definition of these, `fib(n + 2) = fib(n + 1) + fib(n)` is not primitive recursive.
Instead we use a trick, giving a primitive recursive definition of `$n\mapsto (fib(n), fib(n+1))$` and define fibonacci numbers in terms of this.
Note that the codomain of `fibPair` is the _product type_ `(Nat, Nat) = Pair Nat Nat`.

```
fibPair: Nat -> (Nat, Nat)
fibPair Z = (1, 1)
fibPair (S k) = case fibPair k of
                     (a, b) => (b, a + b)

fibo: Nat -> Nat
fibo n = fst (fibPair n)
```

We see:
```
*Intro> map fibo [0..10]
[1, 1, 2, 3, 5, 8, 13, 21, 34, 55, 89] : List Nat
```

Before we move on, some remarks about recursion.

* Recursion is the _only_ form of looping in a functional language.
* We have defined _primitive recursion_ for integers, but this has analogues for all _inductive types_, as we see below.
* A primitive recursive definition is guaranteed to be total.
* It is common to make a recursive definition with more information than we finally need, as we did with fibonacci pairs above.

#### Inductive types and recursion

An _inductive type_ is a type defined by defining _introduction rules_ that are the ways a term of the type can be constructed.
For instance a _binary tree_ is either a _leaf_ or a _node_ where two binary trees are joined. This can be defined in idris
using a `data` definition (the name comes from datatype)

```
data BinTree : Type where
  Leaf : BinTree
  Node : (left: BinTree) -> (right: BinTree) -> BinTree
```

An example is as follows.
```
egTree: BinTree
egTree = Node (Node Leaf (Node Leaf Leaf)) Leaf
```

As we have mentioned before, we can define functions recursively on inductive types. The following counts the number of vertices.

```
numberVertices : BinTree -> Nat
numberVertices Leaf = 1
numberVertices (Node left right) =
  (numberVertices left) + (numberVertices right) + 1
```

We see:
```
*Intro> numberVertices egTree
7 : Nat
```

### First-class types: types are terms (objects)

The above was functional programming, not yet dependent type theory. In Dependent Type Theory, a type _is_ a term, i.e. an object. Specifically,

* types can be assigned to variables.
* types can be arguments to and results of functions.
* types themselves have types - the type of a type is called a universe (denoted `Type` in idris)

First let us assign some types to variables.

```
Naturals : Type
Naturals = Nat

natToNat : Type
natToNat = Nat -> Nat
```

Note that as `Naturals` and `Nat` are equal, `3` has type `Naturals`

```
anotherThree : Naturals
anotherThree = 3
```

#### A parametrized type (generic)

We can generalize inductive types to _inductive type families_. Rather than defining a single inductive type, we define a family of them.
A simple example of this is binary trees with leaves labelled. The labels can have any type `a`, but all labels should have the same type.
We view this as a _function_ that given a type has value a type. Functions with values that are types are called _type families_.

```
data LTree : Type -> Type where
  LLeaf : (a: Type) -> (label: a) -> LTree a
  LNode : (a : Type) -> (left : LTree a) -> (right : LTree a) -> LTree a
```

Here is an example
```
egLTree : LTree Nat
egLTree =
  LNode Nat (
  LNode Nat (LLeaf Nat 1) (LNode Nat (LLeaf Nat 3) (LLeaf Nat 4))
  ) (LLeaf Nat 7)
```

Here too we can define functions by recursion.

```
labels : (a: Type) -> LTree a -> List a
labels a (LLeaf a label) = [label]
labels a (LNode a left right) =
  (labels a left) ++ (labels a right)
```

We see:
```
*Intro> labels _ egLTree
[1, 3, 4, 7] : List Nat
```

__Remark:__ The type `LTree a` depended on the _type_ `a`, not say a natural number. Such dependence is possible, and indeed common,
even in languages where types are not objects. For example we have `List[A]` in scala or `List<A>` in java. We will soon see genuine dependent types.

### Type families, dependent functions and `$\Pi$`-types

We now define a type family with domain `Nat`, i.e. a function `Nat -> Type`. This is the type of _tuples_.
We can view tuples as given recursively. To do this we use the `Unit` type - this is a type with just one term, denoted `()`

* A $0$-tuple of natural numbers is the unique term with type `Unit`.
* An $(n + 1)$-tuple is a pair $(k, t)$ where $k$ is a natural number and $t$ an $n$-tuple.

We define the __type__ of $n$-tuples as a function of $n$ recursively. This is thus a type family.
```
Tuple: Nat -> Type -- tuples of Natural numbers
Tuple Z = Unit
Tuple (S k) = (Nat, Tuple k)
```

Now we can define concrete $n$-tuples and see that they have the expected type.
```
egTuple : Tuple 2
egTuple = (3, (4, ()))
```

Better still we can define a term `countdown` which associates to `n` the countdown to `1`, e.g. `countdown 3` is the $3$-tuple
`(3, (2, (1, ())))`. The definition is recursive.

```
countdown : (n: Nat) -> Tuple n
countdown Z = ()
countdown (S k) = (S k, countdown k)
```

We see:
```
*Intro> countdown 3
(3, 2, 1, ()) : (Nat, Nat, Nat, ())
```

While the above looked innocuous, note that the type of `countdown n` is `Tuple n`, which is not fixed. Thus countdown is __not__ a function
in the usual sense (like say Fibonacci numbers) with fixed domain and codomain. Instead, while the domain is indeed a fixed type `Nat`,
the type of the values depend on the arguments.

Such functions are called _dependent functions_. The type of such a functions is called a _dependent function type_ or a `$\Pi-type` (
the latter term is because they are in some sense products). For instance in more mathematical type theory notation,
`$$countdown : \Pi_{n\in \mathbb{N}} Tuple(n)$$`

#### Vectors : an (indexed) inductive type family

A much better way to define vectors is as an (indexed) inductive type, similar to how we defined `BinTree` and `LTree`
(we note a key difference later).

Here is the idris documentation for vectors.
```
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

We have a different version of countdown, giving vectors and counting down to $0$. Note the type involves `S n` to get the correct length.
```
cntd : (n: Nat) -> Vect (S n) Nat
cntd Z = [0]
cntd (S k) = (S k) :: (cntd k)
```

We see:
```
*Intro> cntd 4
[4, 3, 2, 1, 0] : Vect 5 Nat
```

Next, a more practically useful example. When we zip two lists, it is generally an error if they do not have the same length.
With dependent types, we can enforce this as part of the syntax.
```
zipNat : (n: Nat) -> Vect n Nat -> Vect n Nat -> Vect n (Nat, Nat)
zipNat Z [] [] = []
zipNat (S len) (x :: xs) (y :: ys) = (x , y) :: (zipNat len xs ys)
```

We see:
```
*Intro> zipNat _ [1, 3, 5] [10, 20, 30]
[(1, 10), (3, 20), (5, 30)] : Vect 3 (Nat, Nat)
```

### Rules for forming terms and types

In First-Order Logic we had very few rules for forming expressions: forming recursive terms, atomic formulas, combinations of formulas
and quantified formulas. It seems that in type theory, we have a lot of rules. But in fact there are _fewer_ rules than in the examples above,
since some of them (such as forming pairs) are special cases of others.

Indeed below is a full list of rules for forming types and terms (though some details of these rules are subtle).

* We have universes such as `Type`.
* We can form function types and dependent function types.
* We can form inductive types (including indexed ones like vectors) : we thus form both types and their constructor terms.
* We can define functions and dependent functions in two ways:
  - by an expression `f x = y` where `y` is an expression that can depend on `x` (this is a `$\lambda$` definition).
  - by primitive recursion (if the domain is an inductive type).
* If `f` is a (dependent) function with domain `A` and `a : A` we can form the term `f a`.
