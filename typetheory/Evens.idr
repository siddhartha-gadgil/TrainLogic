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

nOrSnEven : (n : Nat) -> Either (IsEven n) (IsEven (S n))
nOrSnEven Z = Left ZeroEven
nOrSnEven (S k) = case nOrSnEven k of
                       (Left l) => Right (SSEven k l)
                       (Right r) => Left r

oneOdd : IsEven 1 -> Void
oneOdd ZeroEven impossible
oneOdd (SSEven _ _) impossible

threeOdd : IsEven 3 -> Void
threeOdd (SSEven (S Z) ZeroEven) impossible
threeOdd (SSEven (S Z) (SSEven _ _)) impossible

nAndSnNotBothEven : (n: Nat) -> IsEven n -> IsEven (S n) -> Void
nAndSnNotBothEven Z ZeroEven ZeroEven impossible
nAndSnNotBothEven Z ZeroEven (SSEven _ _) impossible
nAndSnNotBothEven (S (S k)) (SSEven k pf) (SSEven (S k) x) =
  nAndSnNotBothEven k pf x

nOddThenSnEven : (n: Nat) -> (IsEven n -> Void) -> IsEven (S n)
nOddThenSnEven n contra =
  (case (nOrSnEven n) of
        (Left l) => void (contra l)
        (Right r) => r
        )

halfSucc : (n : Nat) -> ((IsEven n) -> Void) -> Nat
halfSucc n contra = half (S n) (nOddThenSnEven n contra)

apNat : (f: Nat -> Nat) -> (n: Nat) -> (m: Nat) -> n = m -> f n = f m
apNat f m m Refl = Refl


byTwo : (n: Nat) -> IsEven n -> (k: Nat ** double k = n)
byTwo Z ZeroEven = (Z ** Refl)
byTwo (S (S k)) (SSEven k pf) =
  (case byTwo k pf of
        (x ** pf) => (S x ** (apNat (\m => (S (S m))) (double x) k pf)))

isDouble: Nat -> Type
isDouble n = (m : Nat ** (double m) = n)

evenIsDouble: (n: Nat) -> IsEven n -> (isDouble n)
evenIsDouble = byTwo

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

--- Less than or equal and subtraction

sub : (n: Nat) -> (m : Nat) -> (LTE m n) -> Nat
sub n Z LTEZero = n
sub (S right) (S left) (LTESucc x) = sub right left x

superSub : (n: Nat) -> (m : Nat) -> (LTE m n) -> (diff: Nat ** LTE diff n)
superSub n Z LTEZero = (n ** lteRefl)
superSub (S n) (S m) (LTESucc x) = case (superSub n m x) of
                                               (diff ** pf) => (diff ** lteSuccRight pf)

oneLTEFour : LTE 1 4
oneLTEFour = LTESucc LTEZero

fourMinusOne : Nat
fourMinusOne = sub 4 1 oneLTEFour


-- Range type

data InRange : Nat -> Nat -> Type where
  MkInRange : (l : Nat) -> (u : Nat) -> (n : Nat) -> LTE l n -> LTE n u -> InRange l u

oneBetween0And4 : InRange 0 4
oneBetween0And4 = MkInRange 0 4 1 LTEZero oneLTEFour

Cast (InRange n m) Nat where -- cast is an interface (typeclass in scala)
  cast (MkInRange n m k x y) = k

one: Nat
one = cast oneBetween0And4



--- space
