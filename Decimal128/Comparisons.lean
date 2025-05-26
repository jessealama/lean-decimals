import Mathlib
import Decimal128.Basic

def equals (x : DecimalValue) (y : DecimalValue) : Bool :=
  match x, y with
  | DecimalValue.NaN, _ => false
  | _, DecimalValue.NaN => false
  | DecimalValue.PosInfinity, DecimalValue.PosInfinity => true
  | DecimalValue.PosInfinity, _ => false
  | DecimalValue.NegInfinity, DecimalValue.NegInfinity => true
  | DecimalValue.NegInfinity, _ => false
  | DecimalValue.PosZero, DecimalValue.PosZero => true
  | DecimalValue.NegZero, DecimalValue.NegZero => true
  | DecimalValue.Rational x, DecimalValue.Rational y => x.val = y.val
  | _, _ => false

instance : BEq DecimalValue where
  beq := equals

def notEquals (x : DecimalValue) (y : DecimalValue) : Bool :=
  match x, y with
  | DecimalValue.NaN, _ => false
  | _, DecimalValue.NaN => false
  | DecimalValue.PosInfinity, DecimalValue.PosInfinity => false
  | DecimalValue.PosInfinity, _ => true
  | DecimalValue.NegInfinity, DecimalValue.NegInfinity => false
  | DecimalValue.NegInfinity, _ => true
  | DecimalValue.PosZero, DecimalValue.PosZero => false
  | DecimalValue.NegZero, DecimalValue.NegZero => true
  | DecimalValue.Rational x, DecimalValue.Rational y => !(x.val = y.val)
  | _, _ => false

def lessThan (x : DecimalValue) (y : DecimalValue) : Bool :=
  match x, y with
  | DecimalValue.NaN, _ => false
  | _, DecimalValue.NaN => false
  | DecimalValue.PosInfinity, DecimalValue.PosInfinity => false
  | DecimalValue.PosInfinity, _ => false
  | DecimalValue.NegInfinity, DecimalValue.NegInfinity => false
  | DecimalValue.NegInfinity, _ => true
  | DecimalValue.PosZero, DecimalValue.NegInfinity => false
  | DecimalValue.PosZero, DecimalValue.PosInfinity => true
  | DecimalValue.PosZero, DecimalValue.PosZero => false
  | DecimalValue.PosZero, DecimalValue.NegZero => false
  | DecimalValue.PosZero, DecimalValue.Rational x => x.val > 0
  | DecimalValue.NegZero, DecimalValue.NegInfinity => false
  | DecimalValue.NegZero, DecimalValue.PosInfinity => true
  | DecimalValue.NegZero, DecimalValue.NegZero => false
  | DecimalValue.NegZero, DecimalValue.PosZero => true
  | DecimalValue.NegZero, DecimalValue.Rational x => x.val < 0
  | DecimalValue.Rational _, DecimalValue.PosInfinity => true
  | DecimalValue.Rational _, DecimalValue.NegInfinity => false
  | DecimalValue.Rational x, DecimalValue.PosZero => x.val < 0
  | DecimalValue.Rational x, DecimalValue.NegZero => x.val < 0
  | DecimalValue.Rational x, DecimalValue.Rational y => x.val < y.val

instance : LT DecimalValue where
  lt x y := lessThan x y

def lessThanOrEqual (x : DecimalValue) (y : DecimalValue) : Bool :=
  match x, y with
  | DecimalValue.NaN, _ => false
  | _, DecimalValue.NaN => false
  | DecimalValue.PosInfinity, DecimalValue.PosInfinity => true
  | DecimalValue.PosInfinity, _ => false
  | DecimalValue.NegInfinity, _ => true
  | DecimalValue.PosZero, DecimalValue.NegInfinity => false
  | DecimalValue.PosZero, DecimalValue.PosInfinity => true
  | DecimalValue.PosZero, DecimalValue.PosZero => true
  | DecimalValue.PosZero, DecimalValue.NegZero => true
  | DecimalValue.PosZero, DecimalValue.Rational x => x.val ≥ 0
  | DecimalValue.NegZero, DecimalValue.NegInfinity => false
  | DecimalValue.NegZero, DecimalValue.PosInfinity => true
  | DecimalValue.NegZero, DecimalValue.NegZero => true
  | DecimalValue.NegZero, DecimalValue.PosZero => true
  | DecimalValue.NegZero, DecimalValue.Rational x => x.val ≤ 0
  | DecimalValue.Rational _, DecimalValue.PosInfinity => true
  | DecimalValue.Rational _, DecimalValue.NegInfinity => false
  | DecimalValue.Rational x, DecimalValue.PosZero => x.val ≤ 0
  | DecimalValue.Rational x, DecimalValue.NegZero => x.val ≤ 0
  | DecimalValue.Rational x, DecimalValue.Rational y => x.val ≤ y.val

  instance : LE DecimalValue where
    le x y := lessThanOrEqual x y

def greaterThan (x : DecimalValue) (y : DecimalValue) : Bool :=
  match x, y with
  | DecimalValue.NaN, _ => false
  | _, DecimalValue.NaN => false
  | DecimalValue.PosInfinity, DecimalValue.PosInfinity => false
  | DecimalValue.PosInfinity, _ => false
  | DecimalValue.NegInfinity, _ => true
  | DecimalValue.PosZero, DecimalValue.NegInfinity => true
  | DecimalValue.PosZero, DecimalValue.PosInfinity => false
  | DecimalValue.PosZero, DecimalValue.PosZero => false
  | DecimalValue.PosZero, DecimalValue.NegZero => true
  | DecimalValue.PosZero, DecimalValue.Rational x => x.val < 0
  | DecimalValue.NegZero, DecimalValue.NegInfinity => true
  | DecimalValue.NegZero, DecimalValue.PosInfinity => false
  | DecimalValue.NegZero, DecimalValue.NegZero => false
  | DecimalValue.NegZero, DecimalValue.PosZero => false
  | DecimalValue.NegZero, DecimalValue.Rational x => x.val > 0
  | DecimalValue.Rational _, DecimalValue.PosInfinity => false
  | DecimalValue.Rational _, DecimalValue.NegInfinity => true
  | DecimalValue.Rational x, DecimalValue.PosZero => x.val > 0
  | DecimalValue.Rational x, DecimalValue.NegZero => x.val > 0
  | DecimalValue.Rational x, DecimalValue.Rational y => x.val > y.val

def greaterThanOrEqual (x : DecimalValue) (y : DecimalValue) : Bool :=
  match x, y with
  | DecimalValue.NaN, _ => false
  | _, DecimalValue.NaN => false
  | DecimalValue.PosInfinity, _ => true
  | DecimalValue.NegInfinity, DecimalValue.NegInfinity => true
  | DecimalValue.NegInfinity, _ => false
  | DecimalValue.PosZero, DecimalValue.NegInfinity => true
  | DecimalValue.PosZero, DecimalValue.PosInfinity => false
  | DecimalValue.PosZero, DecimalValue.PosZero => true
  | DecimalValue.PosZero, DecimalValue.NegZero => true
  | DecimalValue.PosZero, DecimalValue.Rational x => x.val ≤ 0
  | DecimalValue.NegZero, DecimalValue.NegInfinity => true
  | DecimalValue.NegZero, DecimalValue.PosInfinity => false
  | DecimalValue.NegZero, DecimalValue.NegZero => true
  | DecimalValue.NegZero, DecimalValue.PosZero => true
  | DecimalValue.NegZero, DecimalValue.Rational x => x.val ≤ 0
  | DecimalValue.Rational _, DecimalValue.PosInfinity => false
  | DecimalValue.Rational _, DecimalValue.NegInfinity => true
  | DecimalValue.Rational x, DecimalValue.PosZero => x.val ≥ 0
  | DecimalValue.Rational x, DecimalValue.NegZero => x.val ≥ 0
  | DecimalValue.Rational x, DecimalValue.Rational y => x.val ≥ y.val

inductive CmpResult where
  | NaN : CmpResult
  | lessThan : CmpResult
  | equal : CmpResult
  | greaterThan : CmpResult

  def compare (x : DecimalValue) (y : DecimalValue) : CmpResult :=
    match x, y with
    | DecimalValue.NaN, _ => CmpResult.NaN
    | _, DecimalValue.NaN => CmpResult.NaN
    | _, _ => if equals x y then CmpResult.equal
              else if lessThan x y then CmpResult.lessThan
              else CmpResult.greaterThan
