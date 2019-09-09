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

notBothEven : (n: Nat) -> IsEven n -> IsEven (S n) -> Void
notBothEven Z ZeroEven ZeroEven impossible
notBothEven Z ZeroEven (SSEven _ _) impossible
notBothEven (S (S k)) (SSEven k x) (SSEven (S k) y) = notBothEven k x y

nOddThenSnEven : (n: Nat) -> (IsEven n -> Void) -> IsEven (S n)
nOddThenSnEven n contra = case (nOrSnEven n) of
                               (Left l) => void (contra l)
                               (Right r) => r

apNat : (f: Nat -> Nat) -> (n: Nat) -> (m: Nat) -> n = m -> f n = f m
apNat f m m Refl = Refl


byTwo : (n: Nat) -> IsEven n -> (k: Nat ** double k = n)
byTwo Z ZeroEven = (0 ** Refl)
byTwo (S (S k)) (SSEven k x) = case (byTwo k x) of
          (m ** pf) => ((S m) ** apNat (\l => S (S l)) (double m) k pf)

isDouble: Nat -> Type
isDouble n = (m : Nat ** (double m) = n)

evenIsDouble: (n: Nat) -> IsEven n -> (isDouble n)
evenIsDouble Z ZeroEven = (Z ** Refl)
evenIsDouble (S (S k)) (SSEven k x) =
  (case evenIsDouble k x of
        (m ** pf) => (S m ** apNat (\l => S (S l)) (double m) k pf)
        )

transport : (a : Type) -> (P : a -> Type) ->  (x : a) -> (y : a) -> (x = y) -> P(x) -> P(y)
transport a P y y Refl z = z

doubleIsEven: (n: Nat) -> isDouble n -> IsEven n
doubleIsEven n pair =
  case pair of
        (k ** pf) =>
          transport Nat IsEven (double k) n pf (doubleEven k)

-- The Peano axioms

sInj : (x: Nat) -> (y: Nat) -> (S x = S y) -> (x = y)
sInj Z Z Refl = Refl
sInj (S k) (S k) Refl = Refl

sNotZ : (x: Nat) -> (S x = Z) -> Void
sNotZ _ Refl impossible

symmEq : (x: Nat) -> (y: Nat) -> (x = y) -> (y = x)
symmEq y y Refl = Refl

transEq: (x: Nat) -> (y: Nat) -> (z: Nat) -> (x = y) -> (y = z) -> (x = z)
transEq y y y Refl Refl = Refl

data InRange : Nat -> Nat -> Type where
  MkInRange : (x : Nat) -> (y : Nat) -> (n : Nat) -> LTE x n -> LTE n y -> InRange x y 
