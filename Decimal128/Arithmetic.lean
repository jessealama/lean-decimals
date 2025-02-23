import Mathlib
import Decimal128.Basic

def absoluteValue (x : Decimal128Value) : Decimal128Value :=
  match x with
  | Decimal128Value.NaN => Decimal128Value.NaN
  | Decimal128Value.NegInfinity => Decimal128Value.PosInfinity
  | Decimal128Value.PosInfinity => Decimal128Value.PosInfinity
  | Decimal128Value.PosZero => Decimal128Value.PosZero
  | Decimal128Value.NegZero => Decimal128Value.PosZero
  | Decimal128Value.Rational x => Decimal128Value.Rational ⟨|x.val|, sorry⟩

def negate (x : Decimal128Value) : Decimal128Value :=
  match x with
  | Decimal128Value.NaN => Decimal128Value.NaN
  | Decimal128Value.NegInfinity => Decimal128Value.PosInfinity
  | Decimal128Value.PosInfinity => Decimal128Value.PosInfinity
  | Decimal128Value.PosZero => Decimal128Value.NegZero
  | Decimal128Value.NegZero => Decimal128Value.PosZero
  | Decimal128Value.Rational x => Decimal128Value.Rational (-x)

instance : Neg Decimal128Value where
  neg x := negate x

def add (x : Decimal128Value) (y : Decimal128Value) : Decimal128Value :=
  match x, y with
  | Decimal128Value.NaN, _ => Decimal128Value.NaN
  | _, Decimal128Value.NaN => Decimal128Value.NaN
  | Decimal128Value.NegInfinity, Decimal128Value.PosInfinity => Decimal128Value.NaN
  | Decimal128Value.PosInfinity, Decimal128Value.NegInfinity => Decimal128Value.NaN
  | Decimal128Value.NegInfinity, _ => Decimal128Value.NegInfinity
  | _, Decimal128Value.NegInfinity => Decimal128Value.NegInfinity
  | Decimal128Value.PosInfinity, _ => Decimal128Value.PosInfinity
  | _, Decimal128Value.PosInfinity => Decimal128Value.PosInfinity
  | Decimal128Value.PosZero, Decimal128Value.NegZero => Decimal128Value.PosZero
  | Decimal128Value.NegZero, Decimal128Value.PosZero => Decimal128Value.PosZero
  | Decimal128Value.PosZero, _ => y
  | _, Decimal128Value.PosZero => x
  | Decimal128Value.NegZero, _ => y
  | _, Decimal128Value.NegZero => x
  | Decimal128Value.Rational ⟨p, _⟩, Decimal128Value.Rational ⟨q, _⟩ => RoundToDecimal128Domain (x.val + y.val) RoundingMode.halfEven

  instance : HAdd Decimal128Value Decimal128Value Decimal128Value where
    hAdd := add

def sub (x : Decimal128Value) (y : Decimal128Value) : Decimal128Value :=
  match x, y with
  | Decimal128Value.NaN, _ => Decimal128Value.NaN
  | _, Decimal128Value.NaN => Decimal128Value.NaN
  | Decimal128Value.NegInfinity, Decimal128Value.NegInfinity => Decimal128Value.NaN
  | Decimal128Value.PosInfinity, Decimal128Value.PosInfinity => Decimal128Value.NaN
  | Decimal128Value.NegInfinity, _ => Decimal128Value.NegInfinity
  | _, Decimal128Value.NegInfinity => Decimal128Value.PosInfinity
  | Decimal128Value.PosInfinity, _ => Decimal128Value.PosInfinity
  | _, Decimal128Value.PosInfinity => Decimal128Value.NegInfinity
  | Decimal128Value.PosZero, Decimal128Value.PosZero => Decimal128Value.PosZero
  | Decimal128Value.NegZero, Decimal128Value.NegZero => Decimal128Value.PosZero
  | Decimal128Value.PosZero, Decimal128Value.NegZero => Decimal128Value.PosZero
  | Decimal128Value.NegZero, Decimal128Value.PosZero => Decimal128Value.NegZero
  | Decimal128Value.PosZero, _ => y
  | _, Decimal128Value.PosZero => x
  | Decimal128Value.NegZero, _ => y
  | _, Decimal128Value.NegZero => x
  | Decimal128Value.Rational x, Decimal128Value.Rational y => RoundToDecimal128Domain (x.val - y.val) RoundingMode.halfEven

instance : HSub Decimal128Value Decimal128Value Decimal128Value where
  hSub := sub

def multiply (x : Decimal128Value) (y : Decimal128Value) : Decimal128Value :=
  match x, y with
  | Decimal128Value.NaN, _ => Decimal128Value.NaN
  | _, Decimal128Value.NaN => Decimal128Value.NaN
  | Decimal128Value.NegInfinity, _ => if isZero y then Decimal128Value.NaN else Decimal128Value.NegInfinity
  | _, Decimal128Value.NegInfinity => if isZero x then Decimal128Value.NaN else Decimal128Value.NegInfinity
  | Decimal128Value.PosInfinity, _ => if isZero y then Decimal128Value.NaN else Decimal128Value.PosInfinity
  | _, Decimal128Value.PosInfinity => if isZero x then Decimal128Value.NaN else Decimal128Value.PosInfinity
  | Decimal128Value.PosZero, _ => Decimal128Value.PosZero
  | _, Decimal128Value.PosZero => Decimal128Value.PosZero
  | Decimal128Value.NegZero, Decimal128Value.NegZero => Decimal128Value.PosZero
  | Decimal128Value.NegZero, Decimal128Value.Rational _ => Decimal128Value.PosZero
  | Decimal128Value.Rational _, Decimal128Value.NegZero => Decimal128Value.PosZero
  | Decimal128Value.Rational x, Decimal128Value.Rational y => RoundToDecimal128Domain (x.val * y.val) RoundingMode.halfEven

instance : HMul Decimal128Value Decimal128Value Decimal128Value where
  hMul := multiply

def divide (x : Decimal128Value) (y : Decimal128Value) : Decimal128Value :=
  match x, y with
  | Decimal128Value.NaN, _ => Decimal128Value.NaN
  | _, Decimal128Value.NaN => Decimal128Value.NaN
  | Decimal128Value.PosInfinity, Decimal128Value.PosInfinity => Decimal128Value.NaN
  | Decimal128Value.PosInfinity, Decimal128Value.NegInfinity => Decimal128Value.NaN
  | Decimal128Value.PosInfinity, _ => if isNegative y then Decimal128Value.NegInfinity else Decimal128Value.PosInfinity
  | Decimal128Value.NegInfinity, Decimal128Value.NegInfinity => Decimal128Value.NaN
  | Decimal128Value.NegInfinity, Decimal128Value.PosInfinity => Decimal128Value.NaN
  | Decimal128Value.NegInfinity, _ => if isNegative y then Decimal128Value.PosInfinity else Decimal128Value.NegInfinity
  | _, Decimal128Value.PosInfinity => if isNegative x then Decimal128Value.NegZero else Decimal128Value.PosZero
  | _, Decimal128Value.NegInfinity => if isNegative x then Decimal128Value.PosZero else Decimal128Value.NegZero
  | Decimal128Value.PosZero, Decimal128Value.PosZero => Decimal128Value.NaN
  | Decimal128Value.NegZero, Decimal128Value.PosZero => Decimal128Value.NaN
  | _, Decimal128Value.PosZero => if isNegative x then Decimal128Value.NegInfinity else if isNegative x then Decimal128Value.NegInfinity else Decimal128Value.PosInfinity
  | Decimal128Value.PosZero, Decimal128Value.NegZero => Decimal128Value.NaN
  | Decimal128Value.NegZero, Decimal128Value.NegZero => Decimal128Value.NaN
  | _, Decimal128Value.NegZero => if isNegative x then Decimal128Value.PosInfinity else Decimal128Value.NegInfinity
  | Decimal128Value.PosZero, _ => if isNegative y then Decimal128Value.NegZero else Decimal128Value.PosZero
  | Decimal128Value.NegZero, _ => if isNegative y then Decimal128Value.PosZero else Decimal128Value.NegZero
  | Decimal128Value.Rational x, Decimal128Value.Rational y => RoundToDecimal128Domain (x.val / y.val) RoundingMode.halfEven

instance : HDiv Decimal128Value Decimal128Value Decimal128Value where
  hDiv := divide

-- it should be possible for n to be positive or negative infinity, or even NaN
def scale10 (x : Decimal128Value) (n : Int) : Decimal128Value :=
  match x with
  | Decimal128Value.NaN => Decimal128Value.NaN
  | Decimal128Value.NegInfinity => Decimal128Value.NegInfinity
  | Decimal128Value.PosInfinity => Decimal128Value.PosInfinity
  | Decimal128Value.PosZero => Decimal128Value.PosZero
  | Decimal128Value.NegZero => Decimal128Value.NegZero
  | Decimal128Value.Rational x => RoundToDecimal128Domain (x.val * (10 ^ n)) RoundingMode.halfEven

private def truncate (x : Rat) : Rat :=
  if x < 0
  then 0 - Rat.floor (0 - x)
  else Rat.floor x

def remainder (x : Decimal128Value) (y : Decimal128Value) : Decimal128Value :=
  match x, y with
  | Decimal128Value.NaN, _ => Decimal128Value.NaN
  | _, Decimal128Value.NaN => Decimal128Value.NaN
  | Decimal128Value.PosInfinity, _ => Decimal128Value.NaN
  | Decimal128Value.NegInfinity, _ => Decimal128Value.NaN
  | _, Decimal128Value.PosInfinity => x
  | _, Decimal128Value.NegInfinity => x
  | _, Decimal128Value.PosZero => Decimal128Value.NaN
  | _, Decimal128Value.NegZero => Decimal128Value.NaN
  | Decimal128Value.PosZero, x => x
  | Decimal128Value.NegZero, x => x
  | Decimal128Value.Rational x, Decimal128Value.Rational y =>
    let q : Rat := truncate (x.val / y.val)
    let r : Rat := x.val - (y.val * q)
    if r == 0 && x.val < 0
    then Decimal128Value.NegZero
    else RoundToDecimal128Domain r RoundingMode.halfEven

instance : HMod Decimal128Value Decimal128Value Decimal128Value where
  hMod := remainder

def exponent (x : Decimal128Value) : Decimal128Value :=
  match x with
  | Decimal128Value.NaN => Decimal128Value.NaN
  | Decimal128Value.NegInfinity => Decimal128Value.PosInfinity
  | Decimal128Value.PosInfinity => Decimal128Value.PosInfinity
  | Decimal128Value.PosZero => Decimal128Value.NegInfinity
  | Decimal128Value.NegZero => Decimal128Value.NegInfinity
  | Decimal128Value.Rational x =>
    let e := rationalExponent x.val
    have suitable : isRationalSuitable e := by sorry
    Decimal128Value.Rational ⟨e, suitable⟩

def rationalSignificand (q : Rat) : Rat :=
  let re : Int := rationalExponent q
  let e : Nat := Int.natAbs re
  q / (10 ^ e)

#eval rationalSignificand 10.4

lemma significandPreservesSuitability (q : Rat) :
  isRationalSuitable q → isRationalSuitable (rationalSignificand q)
  := by
  sorry

lemma mantissaRepresentation (q : Rat) :
  q = (rationalSignificand q) * (10 ^ (rationalExponent q)) := by
  sorry

def mantissa (x : Decimal128Value) : Decimal128Value :=
  match x with
  | Decimal128Value.NaN => Decimal128Value.NaN
  | Decimal128Value.NegInfinity => Decimal128Value.PosInfinity
  | Decimal128Value.PosInfinity => Decimal128Value.PosInfinity
  | Decimal128Value.PosZero => Decimal128Value.PosZero
  | Decimal128Value.NegZero => Decimal128Value.NegZero
  | Decimal128Value.Rational ⟨q, p⟩ =>
    let s : Rat := rationalSignificand q
    have suitable : isRationalSuitable s := by
      apply significandPreservesSuitability q p
    Decimal128Value.Rational ⟨s, suitable⟩
