---
title: Partial and Total orders
date: 2019-09-13
---

Recall that a _relation_ $R$ on a set $S$ is a subset of `$S\times S$`. We have defined reflexive, symmetric and transitive relations. Using these we defined _equivalence relations_. In this exercise we consider another important class of relations, [_partial orders_](https://en.wikipedia.org/wiki/Partially_ordered_set). We begin with some definitions. Fix a relation $R$ on a set $S$. In the following, it is helpful to think of 
`$(a, b)\in R$` as `$a \leq b$`.

* We say that a reflexive relation $R$ is _anti-symmetric_ if `$\forall x,y\in S\ ((x, y)\in R)\land((y, x)\in R)\implies x = y$`.
* We say that $R$ is a _partial-order_ if $R$ is reflexive, anti-symmetric and transitive.
* A partial-order $R$ is said to be a [_total order_](https://en.wikipedia.org/wiki/Total_order) if, in addition, `$\forall x,y\in S\ (x, y)\in R\lor (y, x)\in R$` (this means that every pair of elements is comparable).
* An element $a\in S$ is said to be a _minimum_ with respect to the partial order $R$ if `$\forall x\in S\ (a, x)\in R$`.
* __Fact:__ If $R$ is a total order on a finite set $S$, there is a _unique_ minimum.


Implement the following in a programming language of your choice. If you use `scala` you can use the code from the lectures (by copy-paste).

1. Define a function to check whether a relation $R$ is anti-symmetric.
2. Define a function to check whether a relation $R$ is a partial order.
3. Define a function to check whether a relation $R$ is a total order.
4. On the set `$S=\{2, 3, 4,\dots, 20\}$`, construct sets $R$ corresponding to the following relations:
   1. `$(a, b)\in R$` if and only if `$a - b$` is even.
   2. `$(a, b)\in R$` if and only if `$a \leq b$`.
   3. `$(a, b)\in R$` if and only if `$a | b$` (i.e., $a$ is a [divisor](https://en.wikipedia.org/wiki/Divisor) of $b$).
5. Using the functions you defined, check whether each of the above relations are partial orders.
6. Using the functions you defined, check whether each of the above relations are total orders.
7. Define a function that given a relation $R$ that is a total order, finds that the (unique) minimum with respect to $R$.
8. Use this function to find the minimum for the total order among the relations you defined above.
9. Define a function that given a relation $R$ on a set $S$ such that $R$ is a partial order, finds __all__  elements `$a\in S$` such that `$a$` is a minimum with respect to $R$.
10. Use this function to find __all__ the minima for the partial orders among the three relations you defined above.