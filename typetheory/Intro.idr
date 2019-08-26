module Intro

fct: Nat -> Nat
fct Z = 1
fct (S k) = (S k) * (fct k)
