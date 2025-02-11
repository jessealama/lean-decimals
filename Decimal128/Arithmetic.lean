import Mathlib
import Decimal128.Basic
import Decimal128.Round
import Decimal128.Predicates

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
  | Decimal128Value.Rational x, Decimal128Value.Rational y => RoundToDecimal128Domain (x.val + y.val) RoundingMode.halfEven

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
