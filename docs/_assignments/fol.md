---
title: Formulas for Sets
date: 2019-8-20
---

Write a function/program in any programming language to list all the _closed formulas_ in the _language of sets_. Recall that this is the _first-order language_ with a single constant $\phi$ and a relation $\in$ of degree $2$ (plus the equality relation). A _closed formula_ means a formula with no free variables.

The solution can be either a function that we can import and interact with in a REPL/console/notebook or a program to which we give appropriate input (as below) and get output as desired. Concretely:

1. Fix representations in some data structures for _terms_ and _formulas_ in the language of sets.
2. Have a function/method giving an output string for each formula (any unambiguous and readable representation is fine. One way is to use unicode for mathematical symbols).
3. Define a function (or write a program) to list `n` closed formulas given an integer `n` (as an argument to a function or input to a program). Listing the first `n` functions in any order is fine, but any given formula should appear for large enough `n`. For example if `n` is large enough  the formula $\forall A \forall B\exists C(\forall x\ (x\in C \iff (x\in A \lor x\in B )))$ should be output (in your chosen string representation).

__Remark:__ It may be useful to recursively define a function giving _all_ formulas (including those that are not closed) involving a given finite set of variables and with complexity at most `k` for some appropriate definition of complexity.
