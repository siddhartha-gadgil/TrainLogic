module Evens

-- The type `IsEven(n)`  has terms (objects) that are proofs that `n` is even.
data IsEven : Nat -> Type where
  ZeroEven : IsEven 0
  SSEven : (n: Nat) -> IsEven n -> IsEven (S (S n))
