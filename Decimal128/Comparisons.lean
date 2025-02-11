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

def notEquals (x : Decimal128Value) (y : Decimal128Value) : Bool :=
  | Decimal128Value.NaN, _ => false
  | _, Decimal128Value.NaN => false
  | Decimal128Value.PosInfinity, Decimal128Value.PosInfinity => false
  | Decimal128Value.PosInfinity, _ => true
  | Decimal128Value.NegInfinity, Decimal128Value.NegInfinity => false
  | Decimal128Value.NegInfinity, _ => true
  | Decimal128Value.PosZero, Decimal128Value.PosZero => false
  | Decimal128Value.NegZero, Decimal128Value.NegZero => true
  | Decimal128Value.Rational x, Decimal128Value.Rational y => !(x.val = y.val)
  | _, _ => false

def lessThan (x : Decimal128Value) (y : Decimal128Value) : Bool :=
  match x, y with
  | Decimal128Value.NaN, _ => false
  | _, Decimal128Value.NaN => false
  | Decimal128Value.PosInfinity, Decimal128Value.PosInfinity => false
  | Decimal128Value.PosInfinity, _ => false
  | Decimal128Value.NegInfinity, Decimal128Value.NegInfinity => false
  | Decimal128Value.NegInfinity, _ => true
  | Decimal128Value.PosZero, Decimal128Value.PosZero => false
  | Decimal128Value.PosZero, Decimal128Value.NegZero => false
  | Decimal128Value.NegZero, Decimal128Value.NegZero => false
  | Decimal128Value.NegZero, Decimal128Value.PosZero => true
  | Decimal128Value.Rational x, Decimal128Value.Rational y => x.val < y.val

def greaterThan (x : Decimal128Value) (y : Decimal128Value) : Bool :=
  match x, y with
  | Decimal128Value.NaN, _ => false
  | _, Decimal128Value.NaN => false
  | Decimal128Value.PosInfinity, Decimal128Value.PosInfinity => false
  | Decimal128Value.PosInfinity, _ => true
  | Decimal128Value.NegInfinity, _ => false
  | Decimal128Value.PosZero, Decimal128Value.PosZero => false
  | Decimal128Value.PosZero, Decimal128Value.NegZero => true
  | Decimal128Value.PosZero, Decimal128Value.Rational z => z.val > 0
  | Decimal128Value.NegZero, Decimal128Value.NegZero => false
  | Decimal128Value.NegZero, Decimal128Value.PosZero => false
  | Decimal128Value.NegZero, Decimal128Value.Rational z => z.val < 0
  | Decimal128Value.Rational x, Decimal128Value.Rational y => x.val > y.val
