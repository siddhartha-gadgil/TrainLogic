module Evens

-- The type `IsEven(n)`  has terms (objects) that are proofs that `n` is even.
data IsEven : Nat -> Type where
  ZeroEven : IsEven 0
  SSEven : (n: Nat) -> IsEven n -> IsEven (S (S n))

twoEven: IsEven 2
twoEven = SSEven 0 ZeroEven

half : (n : Nat) -> IsEven(n) ->  Nat
half Z ZeroEven = Z
half (S (S k)) (SSEven k pf) = S(half k pf)

fourEven: IsEven 4
fourEven = SSEven 2 twoEven
