import Mathlib
import Decimal128.Basic

def equals (x : Decimal128Value) (y : Decimal128Value) : Bool :=
  match x, y with
  | Decimal128Value.NaN, _ => false
  | _, Decimal128Value.NaN => false
  | Decimal128Value.PosInfinity, Decimal128Value.PosInfinity => true
  | Decimal128Value.PosInfinity, _ => false
  | Decimal128Value.NegInfinity, Decimal128Value.NegInfinity => true
  | Decimal128Value.NegInfinity, _ => false
  | Decimal128Value.PosZero, Decimal128Value.PosZero => true
  | Decimal128Value.NegZero, Decimal128Value.NegZero => true
  | Decimal128Value.Rational x, Decimal128Value.Rational y => x.val = y.val
  | _, _ => false
