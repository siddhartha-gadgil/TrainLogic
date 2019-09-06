module Evens

-- The type `IsEven(n)`  has terms (objects) that are proofs that `n` is even.
data IsEven : Nat -> Type where
  ZeroEven : IsEven 0
  SSEven : (n: Nat) -> (pf: IsEven n) -> IsEven (S (S n))

twoEven : IsEven 2
twoEven = SSEven Z ZeroEven

fourEven : IsEven 4
fourEven = SSEven _ twoEven

half : (n: Nat) -> IsEven n -> Nat
half Z ZeroEven = 0
half (S (S k)) (SSEven k pf) =
  S (half k pf)

double: Nat -> Nat
double Z = Z
double (S k) = S (S (double k))

doubleEven: (n: Nat) -> IsEven (double n)
doubleEven Z = ZeroEven
doubleEven (S k) =
  SSEven (double k) (doubleEven k)

halfDouble : Nat -> Nat
halfDouble n = half (double n) (doubleEven n)
