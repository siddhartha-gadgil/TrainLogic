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

double: Nat -> Nat
double Z = Z
double (S n) = S (S (double n))

doubleEven: (n: Nat) -> IsEven (double n)
doubleEven Z = ZeroEven
doubleEven (S k) = SSEven (double k) (doubleEven k)

oneOdd : IsEven 1 -> Void
oneOdd ZeroEven impossible
oneOdd (SSEven _ _) impossible

threeOdd : IsEven 3 -> Void
threeOdd (SSEven (S Z) ZeroEven) impossible
threeOdd (SSEven (S Z) (SSEven _ _)) impossible

nOrSnEven : (n: Nat) -> Either (IsEven n) (IsEven (S n))
nOrSnEven Z = Left ZeroEven
nOrSnEven (S k) = case nOrSnEven k of
                       (Left l) => Right (SSEven k l)
                       (Right r) => Left r

IsOdd: Nat -> Type
IsOdd m = (IsEven m) -> Void

succOdd: (n: Nat) -> IsEven n -> IsOdd (S n)
succOdd Z ZeroEven = oneOdd
succOdd (S (S k)) (SSEven k x) = \pf => (case pf of
                                              (SSEven (S k) y) => succOdd k x y)
