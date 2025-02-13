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

instance : BEq Decimal128Value where
  beq := equals

def notEquals (x : Decimal128Value) (y : Decimal128Value) : Bool :=
  match x, y with
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
  | Decimal128Value.PosZero, Decimal128Value.NegInfinity => false
  | Decimal128Value.PosZero, Decimal128Value.PosInfinity => true
  | Decimal128Value.PosZero, Decimal128Value.PosZero => false
  | Decimal128Value.PosZero, Decimal128Value.NegZero => false
  | Decimal128Value.PosZero, Decimal128Value.Rational x => x.val > 0
  | Decimal128Value.NegZero, Decimal128Value.NegInfinity => false
  | Decimal128Value.NegZero, Decimal128Value.PosInfinity => true
  | Decimal128Value.NegZero, Decimal128Value.NegZero => false
  | Decimal128Value.NegZero, Decimal128Value.PosZero => true
  | Decimal128Value.NegZero, Decimal128Value.Rational x => x.val < 0
  | Decimal128Value.Rational _, Decimal128Value.PosInfinity => true
  | Decimal128Value.Rational _, Decimal128Value.NegInfinity => false
  | Decimal128Value.Rational x, Decimal128Value.PosZero => x.val < 0
  | Decimal128Value.Rational x, Decimal128Value.NegZero => x.val < 0
  | Decimal128Value.Rational x, Decimal128Value.Rational y => x.val < y.val

instance : LT Decimal128Value where
  lt x y := lessThan x y

def lessThanOrEqual (x : Decimal128Value) (y : Decimal128Value) : Bool :=
  match x, y with
  | Decimal128Value.NaN, _ => false
  | _, Decimal128Value.NaN => false
  | Decimal128Value.PosInfinity, Decimal128Value.PosInfinity => true
  | Decimal128Value.PosInfinity, _ => false
  | Decimal128Value.NegInfinity, _ => true
  | Decimal128Value.PosZero, Decimal128Value.NegInfinity => false
  | Decimal128Value.PosZero, Decimal128Value.PosInfinity => true
  | Decimal128Value.PosZero, Decimal128Value.PosZero => true
  | Decimal128Value.PosZero, Decimal128Value.NegZero => true
  | Decimal128Value.PosZero, Decimal128Value.Rational x => x.val ≥ 0
  | Decimal128Value.NegZero, Decimal128Value.NegInfinity => false
  | Decimal128Value.NegZero, Decimal128Value.PosInfinity => true
  | Decimal128Value.NegZero, Decimal128Value.NegZero => true
  | Decimal128Value.NegZero, Decimal128Value.PosZero => true
  | Decimal128Value.NegZero, Decimal128Value.Rational x => x.val ≤ 0
  | Decimal128Value.Rational _, Decimal128Value.PosInfinity => true
  | Decimal128Value.Rational _, Decimal128Value.NegInfinity => false
  | Decimal128Value.Rational x, Decimal128Value.PosZero => x.val ≤ 0
  | Decimal128Value.Rational x, Decimal128Value.NegZero => x.val ≤ 0
  | Decimal128Value.Rational x, Decimal128Value.Rational y => x.val ≤ y.val

  instance : LE Decimal128Value where
    le x y := lessThanOrEqual x y

def greaterThan (x : Decimal128Value) (y : Decimal128Value) : Bool :=
  match x, y with
  | Decimal128Value.NaN, _ => false
  | _, Decimal128Value.NaN => false
  | Decimal128Value.PosInfinity, Decimal128Value.PosInfinity => false
  | Decimal128Value.PosInfinity, _ => false
  | Decimal128Value.NegInfinity, _ => true
  | Decimal128Value.PosZero, Decimal128Value.NegInfinity => true
  | Decimal128Value.PosZero, Decimal128Value.PosInfinity => false
  | Decimal128Value.PosZero, Decimal128Value.PosZero => false
  | Decimal128Value.PosZero, Decimal128Value.NegZero => true
  | Decimal128Value.PosZero, Decimal128Value.Rational x => x.val < 0
  | Decimal128Value.NegZero, Decimal128Value.NegInfinity => true
  | Decimal128Value.NegZero, Decimal128Value.PosInfinity => false
  | Decimal128Value.NegZero, Decimal128Value.NegZero => false
  | Decimal128Value.NegZero, Decimal128Value.PosZero => false
  | Decimal128Value.NegZero, Decimal128Value.Rational x => x.val > 0
  | Decimal128Value.Rational _, Decimal128Value.PosInfinity => false
  | Decimal128Value.Rational _, Decimal128Value.NegInfinity => true
  | Decimal128Value.Rational x, Decimal128Value.PosZero => x.val > 0
  | Decimal128Value.Rational x, Decimal128Value.NegZero => x.val > 0
  | Decimal128Value.Rational x, Decimal128Value.Rational y => x.val > y.val

def greaterThanOrEqual (x : Decimal128Value) (y : Decimal128Value) : Bool :=
  match x, y with
  | Decimal128Value.NaN, _ => false
  | _, Decimal128Value.NaN => false
  | Decimal128Value.PosInfinity, _ => true
  | Decimal128Value.NegInfinity, Decimal128Value.NegInfinity => true
  | Decimal128Value.NegInfinity, _ => false
  | Decimal128Value.PosZero, Decimal128Value.NegInfinity => true
  | Decimal128Value.PosZero, Decimal128Value.PosInfinity => false
  | Decimal128Value.PosZero, Decimal128Value.PosZero => true
  | Decimal128Value.PosZero, Decimal128Value.NegZero => true
  | Decimal128Value.PosZero, Decimal128Value.Rational x => x.val ≤ 0
  | Decimal128Value.NegZero, Decimal128Value.NegInfinity => true
  | Decimal128Value.NegZero, Decimal128Value.PosInfinity => false
  | Decimal128Value.NegZero, Decimal128Value.NegZero => true
  | Decimal128Value.NegZero, Decimal128Value.PosZero => true
  | Decimal128Value.NegZero, Decimal128Value.Rational x => x.val ≤ 0
  | Decimal128Value.Rational _, Decimal128Value.PosInfinity => false
  | Decimal128Value.Rational _, Decimal128Value.NegInfinity => true
  | Decimal128Value.Rational x, Decimal128Value.PosZero => x.val ≥ 0
  | Decimal128Value.Rational x, Decimal128Value.NegZero => x.val ≥ 0
  | Decimal128Value.Rational x, Decimal128Value.Rational y => x.val ≥ y.val

inductive CmpResult where
  | NaN : CmpResult
  | lessThan : CmpResult
  | equal : CmpResult
  | greaterThan : CmpResult

  def compare (x : Decimal128Value) (y : Decimal128Value) : CmpResult :=
    match x, y with
    | Decimal128Value.NaN, _ => CmpResult.NaN
    | _, Decimal128Value.NaN => CmpResult.NaN
    | _, _ => if equals x y then CmpResult.equal
              else if lessThan x y then CmpResult.lessThan
              else CmpResult.greaterThan
