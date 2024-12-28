import Mathlib
import Decimal128.Constants
import Decimal128.Util

def maxCohortValue : Rat := scale10 34

def isRationalSuitable (v : Rat) : Prop :=
  ∃ q : Int,
  Rat.isInt (|v| * (scale10 (0 - q)))
  ∧ |v| > 0
  ∧ |v| < maxCohortValue

-- lemma absNeg (v : Rat) : abs (-v) = |v| := by sorry

theorem negationPreservesSuitability (v : Rat) :
  isRationalSuitable v → isRationalSuitable (-v)
  := by
  intro h
  obtain ⟨q, h⟩ := h
  obtain ⟨isInt, absPos, absNotTooBig⟩ := h
  exists q
  constructor
  · rw [abs_neg, isInt]
  · constructor
    · simp [abs_neg, absPos]
    · simp [abs_neg, absNotTooBig]

def SuitableRationals : Type := { q : Rat // isRationalSuitable q }

inductive Decimal128Value where
  | NaN : Decimal128Value
  | NegInfinity : Decimal128Value
  | PosInfinity : Decimal128Value
  | PosZero : Decimal128Value
  | NegZero : Decimal128Value
  | Rational : SuitableRationals → Decimal128Value

def isZero (x : Decimal128Value) : Bool :=
  match x with
  | Decimal128Value.PosZero => true
  | Decimal128Value.NegZero => true
  | _ => false

def isFinite (x : Decimal128Value) : Bool :=
  match x with
  | Decimal128Value.NaN => false
  | Decimal128Value.NegInfinity => false
  | Decimal128Value.PosInfinity => false
  | _ => true

def FiniteDecimal128 : Type := { x : Decimal128Value // isFinite x }

def mathematicalValue (x : FiniteDecimal128) : Rat :=
  match x with
  | ⟨Decimal128Value.Rational ⟨q, _⟩, _⟩ => q
  | _ => 0

def PositiveRational : Type := { x : Rat // x > 0 }
def NonZeroRational : Type := { x : Rat // x ≠ 0 }

def rationalExponentAndSignificand (x : Rat) : Option (Int × Rat) :=
  some (0, Rat.mk' 0 1)

def rationalExponent (x : Rat) : Option Int :=
  match rationalExponentAndSignificand x with
  | none => none
  | some (e, _) => some e

def rationalSignificand (x : Rat) : Option Rat :=
  match rationalExponentAndSignificand x with
  | none => none
  | some (_, s) => some s

inductive RoundingMode where
  | ceil : RoundingMode
  | floor : RoundingMode
  | trunc : RoundingMode
  | halfExpand : RoundingMode
  | halfEven : RoundingMode

def ApplyRoundingModeToPositive (m : PositiveRational) (r : RoundingMode) : Int :=
  let mLow := Rat.floor m.1
  let fraction := m.1 - mLow
  let mHigh := mLow + 1
  match fraction with
  | 0 => mLow
  | _ => match r with
    | RoundingMode.floor => mLow
    | RoundingMode.trunc => mLow
    | RoundingMode.ceil => mHigh
    | _ => if fraction < 0.5
           then mLow
           else (if fraction > 0.5
                 then mHigh
                 else (match r with
                       | RoundingMode.halfEven => if mLow % 2 == 0
                                                  then mLow
                                                  else mHigh
                       | _ => (if mLow % 2 == 0
                                 then mLow
                                 else mHigh)))

def ReverseRoundingMode (r : RoundingMode) : RoundingMode :=
  match r with
  | RoundingMode.ceil => RoundingMode.floor
  | RoundingMode.floor => RoundingMode.ceil
  | _ => r

instance : Neg SuitableRationals where
  neg x := ⟨-x.val, negationPreservesSuitability x.val x.property⟩

def Decimal128Negate (x : Decimal128Value) : Decimal128Value :=
  match x with
  | Decimal128Value.NaN => Decimal128Value.NaN
  | Decimal128Value.NegInfinity => Decimal128Value.PosInfinity
  | Decimal128Value.PosInfinity => Decimal128Value.PosInfinity
  | Decimal128Value.PosZero => Decimal128Value.NegZero
  | Decimal128Value.NegZero => Decimal128Value.PosZero
  | Decimal128Value.Rational x => Decimal128Value.Rational (-x)

#eval (Rat.mk' 1 2) ^ 4

def RoundToDecimal128Domain (v : Rat) (r : RoundingMode) : Decimal128Value :=
  if z: v == 0
  then Decimal128Value.PosZero
  else if n: v < 0
  then
    let reverseRoundingMode := ReverseRoundingMode r
    let d := RoundToDecimal128Domain (-v) reverseRoundingMode
    match d with
    | Decimal128Value.PosInfinity => Decimal128Value.NegInfinity
    | Decimal128Value.PosZero => Decimal128Value.NegZero
    | Decimal128Value.Rational q => Decimal128Value.Rational (-q)
    | _ => Decimal128Value.NaN
  else
    have positive : v > 0 := by sorry
    match rationalExponent v with
    | none => Decimal128Value.NaN
    | some e =>
      let te : Int := max (e - 33) (0 - 6176)
      let m : Rat := v * (rat10 ^ (0 - te))
      let rounded := ApplyRoundingModeToPositive v r
      if rounded = 0
      then Decimal128Value.PosZero
      else if rounded = 10 ^ 34
      then Decimal128Value.PosInfinity
      else Decimal128Value.Rational ⟨rounded * (10 ^ te), sorry⟩

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
