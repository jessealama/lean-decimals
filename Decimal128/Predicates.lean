import Mathlib
import Decimal128.Basic

def isZero (x : Decimal128Value) : Bool :=
  match x with
  | Decimal128Value.PosZero => true
  | Decimal128Value.NegZero => true
  | _ => false

def isNegative (x : Decimal128Value) : Bool :=
  match x with
  | Decimal128Value.NegInfinity => true
  | Decimal128Value.NegZero => true
  | Decimal128Value.Rational ⟨q, _⟩ => q < 0
  | _ => false

def isFinite (x : Decimal128Value) : Bool :=
  match x with
  | Decimal128Value.NaN => false
  | Decimal128Value.NegInfinity => false
  | Decimal128Value.PosInfinity => false
  | _ => true

def isNaN (x : Decimal128Value) : Bool :=
  match x with
  | Decimal128Value.NaN => true
  | _ => false
