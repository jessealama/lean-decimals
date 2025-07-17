import Mathlib
import Decimal128.Basic

-- Proves that the exponent of a suitable rational is itself suitable
lemma exponentSuitable (p : Rat) :
  isRationalSuitable p → isRationalSuitable (rationalExponent p : Rat)
:= by sorry

theorem absoluteValuePreservesSuitability (v : Rat) :
  isRationalSuitable v → isRationalSuitable |v|
  := by
  intro h
  obtain ⟨q, h⟩ := h
  obtain ⟨isInt, absPos, absNotTooBig⟩ := h
  exists q
  constructor
  · rw [abs_abs, isInt]
  · constructor
    · simp [abs_abs, absPos]
    · simp [abs_abs, absNotTooBig]

def absoluteValue (x : DecimalValue) : DecimalValue :=
  match x with
  | DecimalValue.NaN => DecimalValue.NaN
  | DecimalValue.NegInfinity => DecimalValue.PosInfinity
  | DecimalValue.PosInfinity => DecimalValue.PosInfinity
  | DecimalValue.PosZero => DecimalValue.PosZero
  | DecimalValue.NegZero => DecimalValue.PosZero
  | DecimalValue.Rational ⟨q, s'⟩ =>
    have s : isRationalSuitable |q| := by
      apply absoluteValuePreservesSuitability q s'
    DecimalValue.Rational ⟨|q|, s⟩

def negate (x : DecimalValue) : DecimalValue :=
  match x with
  | DecimalValue.NaN => DecimalValue.NaN
  | DecimalValue.NegInfinity => DecimalValue.PosInfinity
  | DecimalValue.PosInfinity => DecimalValue.NegInfinity
  | DecimalValue.PosZero => DecimalValue.NegZero
  | DecimalValue.NegZero => DecimalValue.PosZero
  | DecimalValue.Rational ⟨q, s'⟩ =>
    have s : isRationalSuitable (-q) := by
      apply negationPreservesSuitability q s'
    DecimalValue.Rational ⟨-q, s⟩

instance : Neg DecimalValue where
  neg x := negate x

def add (x : DecimalValue) (y : DecimalValue) : DecimalValue :=
  match x, y with
  | DecimalValue.NaN, _ => DecimalValue.NaN
  | _, DecimalValue.NaN => DecimalValue.NaN
  | DecimalValue.NegInfinity, DecimalValue.PosInfinity => DecimalValue.NaN
  | DecimalValue.PosInfinity, DecimalValue.NegInfinity => DecimalValue.NaN
  | DecimalValue.NegInfinity, _ => DecimalValue.NegInfinity
  | _, DecimalValue.NegInfinity => DecimalValue.NegInfinity
  | DecimalValue.PosInfinity, _ => DecimalValue.PosInfinity
  | _, DecimalValue.PosInfinity => DecimalValue.PosInfinity
  | DecimalValue.PosZero, DecimalValue.NegZero => DecimalValue.PosZero
  | DecimalValue.NegZero, DecimalValue.PosZero => DecimalValue.PosZero
  | DecimalValue.PosZero, _ => y
  | _, DecimalValue.PosZero => x
  | DecimalValue.NegZero, _ => y
  | _, DecimalValue.NegZero => x
  | DecimalValue.Rational ⟨p, _⟩, DecimalValue.Rational ⟨q, _⟩ =>
    RoundToDecimal128Domain (p + q) RoundingMode.halfEven

  instance : HAdd DecimalValue DecimalValue DecimalValue where
    hAdd := add

def sub (x : DecimalValue) (y : DecimalValue) : DecimalValue :=
  match x, y with
  | DecimalValue.NaN, _ => DecimalValue.NaN
  | _, DecimalValue.NaN => DecimalValue.NaN
  | DecimalValue.NegInfinity, DecimalValue.NegInfinity => DecimalValue.NaN
  | DecimalValue.PosInfinity, DecimalValue.PosInfinity => DecimalValue.NaN
  | DecimalValue.NegInfinity, _ => DecimalValue.NegInfinity
  | _, DecimalValue.NegInfinity => DecimalValue.PosInfinity
  | DecimalValue.PosInfinity, _ => DecimalValue.PosInfinity
  | _, DecimalValue.PosInfinity => DecimalValue.NegInfinity
  | DecimalValue.PosZero, DecimalValue.PosZero => DecimalValue.PosZero
  | DecimalValue.NegZero, DecimalValue.NegZero => DecimalValue.PosZero
  | DecimalValue.PosZero, DecimalValue.NegZero => DecimalValue.PosZero
  | DecimalValue.NegZero, DecimalValue.PosZero => DecimalValue.NegZero
  | DecimalValue.PosZero, _ => y
  | _, DecimalValue.PosZero => x
  | DecimalValue.NegZero, _ => y
  | _, DecimalValue.NegZero => x
  | DecimalValue.Rational ⟨p, _⟩, DecimalValue.Rational ⟨q, _⟩ =>
    RoundToDecimal128Domain (p - q) RoundingMode.halfEven

instance : HSub DecimalValue DecimalValue DecimalValue where
  hSub := sub

def multiply (x : DecimalValue) (y : DecimalValue) : DecimalValue :=
  match x, y with
  | DecimalValue.NaN, _ => DecimalValue.NaN
  | _, DecimalValue.NaN => DecimalValue.NaN
  | DecimalValue.NegInfinity, _ => if isZero y then DecimalValue.NaN else DecimalValue.NegInfinity
  | _, DecimalValue.NegInfinity => if isZero x then DecimalValue.NaN else DecimalValue.NegInfinity
  | DecimalValue.PosInfinity, _ => if isZero y then DecimalValue.NaN else DecimalValue.PosInfinity
  | _, DecimalValue.PosInfinity => if isZero x then DecimalValue.NaN else DecimalValue.PosInfinity
  | DecimalValue.PosZero, _ => DecimalValue.PosZero
  | _, DecimalValue.PosZero => DecimalValue.PosZero
  | DecimalValue.NegZero, DecimalValue.NegZero => DecimalValue.PosZero
  | DecimalValue.NegZero, DecimalValue.Rational _ => DecimalValue.PosZero
  | DecimalValue.Rational _, DecimalValue.NegZero => DecimalValue.PosZero
  | DecimalValue.Rational ⟨p, _⟩, DecimalValue.Rational ⟨q, _⟩ =>
    RoundToDecimal128Domain (p * q) RoundingMode.halfEven

instance : HMul DecimalValue DecimalValue DecimalValue where
  hMul := multiply

def divide (x : DecimalValue) (y : DecimalValue) : DecimalValue :=
  match x, y with
  | DecimalValue.NaN, _ => DecimalValue.NaN
  | _, DecimalValue.NaN => DecimalValue.NaN
  | DecimalValue.PosInfinity, DecimalValue.PosInfinity => DecimalValue.NaN
  | DecimalValue.PosInfinity, DecimalValue.NegInfinity => DecimalValue.NaN
  | DecimalValue.PosInfinity, _ => if isNegative y then DecimalValue.NegInfinity else DecimalValue.PosInfinity
  | DecimalValue.NegInfinity, DecimalValue.NegInfinity => DecimalValue.NaN
  | DecimalValue.NegInfinity, DecimalValue.PosInfinity => DecimalValue.NaN
  | DecimalValue.NegInfinity, _ => if isNegative y then DecimalValue.PosInfinity else DecimalValue.NegInfinity
  | _, DecimalValue.PosInfinity => if isNegative x then DecimalValue.NegZero else DecimalValue.PosZero
  | _, DecimalValue.NegInfinity => if isNegative x then DecimalValue.PosZero else DecimalValue.NegZero
  | DecimalValue.PosZero, DecimalValue.PosZero => DecimalValue.NaN
  | DecimalValue.NegZero, DecimalValue.PosZero => DecimalValue.NaN
  | _, DecimalValue.PosZero => if isNegative x then DecimalValue.NegInfinity else if isNegative x then DecimalValue.NegInfinity else DecimalValue.PosInfinity
  | DecimalValue.PosZero, DecimalValue.NegZero => DecimalValue.NaN
  | DecimalValue.NegZero, DecimalValue.NegZero => DecimalValue.NaN
  | _, DecimalValue.NegZero => if isNegative x then DecimalValue.PosInfinity else DecimalValue.NegInfinity
  | DecimalValue.PosZero, _ => if isNegative y then DecimalValue.NegZero else DecimalValue.PosZero
  | DecimalValue.NegZero, _ => if isNegative y then DecimalValue.PosZero else DecimalValue.NegZero
  | DecimalValue.Rational ⟨p, _⟩, DecimalValue.Rational ⟨q, _⟩ =>
    RoundToDecimal128Domain (p / q) RoundingMode.halfEven

instance : HDiv DecimalValue DecimalValue DecimalValue where
  hDiv := divide

-- it should be possible for n to be positive or negative infinity, or even NaN
def scale10 (x : DecimalValue) (n : Int) : DecimalValue :=
  match x with
  | DecimalValue.NaN => DecimalValue.NaN
  | DecimalValue.NegInfinity => DecimalValue.NegInfinity
  | DecimalValue.PosInfinity => DecimalValue.PosInfinity
  | DecimalValue.PosZero => DecimalValue.PosZero
  | DecimalValue.NegZero => DecimalValue.NegZero
  | DecimalValue.Rational ⟨p, _⟩ => RoundToDecimal128Domain (p * (10 ^ n)) RoundingMode.halfEven

def truncate (x : Rat) : Rat :=
  if x < 0
  then 0 - Rat.floor (0 - x)
  else Rat.floor x

-- JavaScript remainder operator (%) behavior:
-- The remainder operation returns the remainder left over when one operand is divided
-- by a second operand. It always takes the sign of the dividend.
-- Formula: dividend % divisor = dividend - Math.trunc(dividend/divisor) * divisor
--
-- Examples from JavaScript:
--   7 % 3 = 1          (positive dividend, positive divisor)
--   -7 % 3 = -1        (negative dividend, positive divisor → negative result)
--   7 % -3 = 1         (positive dividend, negative divisor → positive result)
--   -7 % -3 = -1       (negative dividend, negative divisor → negative result)
--   7.5 % 2 = 1.5      (works with decimals)
--   -7.5 % 2 = -1.5    (decimal with negative dividend)
--
-- Special cases:
--   ±Infinity % n = NaN
--   n % ±Infinity = n (returns dividend unchanged)
--   n % 0 = NaN
--   0 % n = 0 (with appropriate sign handling for -0)

def remainder (x : DecimalValue) (y : DecimalValue) : DecimalValue :=
  match x, y with
  | DecimalValue.NaN, _ => DecimalValue.NaN
  | _, DecimalValue.NaN => DecimalValue.NaN
  | DecimalValue.PosInfinity, _ => DecimalValue.NaN
  | DecimalValue.NegInfinity, _ => DecimalValue.NaN
  | _, DecimalValue.PosInfinity => x
  | _, DecimalValue.NegInfinity => x
  | _, DecimalValue.PosZero => DecimalValue.NaN
  | _, DecimalValue.NegZero => DecimalValue.NaN
  | DecimalValue.PosZero, _ => DecimalValue.PosZero
  | DecimalValue.NegZero, _ => DecimalValue.NegZero
  | DecimalValue.Rational ⟨p, _⟩, DecimalValue.Rational ⟨q, _⟩ =>
    let quotient : Rat := truncate (p / q)
    let r : Rat := p - (q * quotient)
    if r == 0 && p < 0
    then DecimalValue.NegZero
    else RoundToDecimal128Domain r RoundingMode.halfEven

instance : HMod DecimalValue DecimalValue DecimalValue where
  hMod := remainder

def exponent (x : DecimalValue) : DecimalValue :=
  match x with
  | DecimalValue.NaN => DecimalValue.NaN
  | DecimalValue.NegInfinity => DecimalValue.PosInfinity
  | DecimalValue.PosInfinity => DecimalValue.PosInfinity
  | DecimalValue.PosZero => DecimalValue.NegInfinity
  | DecimalValue.NegZero => DecimalValue.NegInfinity
  | DecimalValue.Rational x =>
    let e : Rat := rationalExponent x.val
    -- Proves that the exponent of a rational is suitable
    have suitable : isRationalSuitable e := by
      apply exponentSuitable x.val x.property
    DecimalValue.Rational ⟨e, suitable⟩

def rationalSignificand (q : Rat) : Rat :=
  let re : Int := rationalExponent q
  let e : Nat := Int.natAbs re
  q / (10 ^ e)

#eval rationalSignificand 10.4

-- Proves that extracting significand preserves suitability
lemma significandPreservesSuitability (q : Rat) :
  isRationalSuitable q → isRationalSuitable (rationalSignificand q)
  := by
  sorry

-- Proves that a rational equals its significand times 10 to its exponent
lemma mantissaRepresentation (q : Rat) :
  q = (rationalSignificand q) * (10 ^ (rationalExponent q)) := by
  sorry

def mantissa (x : DecimalValue) : DecimalValue :=
  match x with
  | DecimalValue.NaN => DecimalValue.NaN
  | DecimalValue.NegInfinity => DecimalValue.PosInfinity
  | DecimalValue.PosInfinity => DecimalValue.PosInfinity
  | DecimalValue.PosZero => DecimalValue.PosZero
  | DecimalValue.NegZero => DecimalValue.NegZero
  | DecimalValue.Rational ⟨q, p⟩ =>
    let s : Rat := rationalSignificand q
    have suitable : isRationalSuitable s := by
      apply significandPreservesSuitability q p
    DecimalValue.Rational ⟨s, suitable⟩
