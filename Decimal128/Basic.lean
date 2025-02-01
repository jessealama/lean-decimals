import Mathlib
import Decimal128.Constants
import Decimal128.Util
import Decimal128.Round

def maxCohortValue : Rat := scale10 34

def isRationalSuitable (v : Rat) : Prop :=
  ∃ q : Int,
  Rat.isInt (|v| * (scale10 (0 - q)))
  ∧ |v| > 0
  ∧ |v| < maxCohortValue

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

def FiniteDecimal128 : Type := { x : Decimal128Value // isFinite x }

def mathematicalValue (x : FiniteDecimal128) : Rat :=
  match x with
  | ⟨Decimal128Value.Rational ⟨q, _⟩, _⟩ => q
  | _ => 0

def rationalExponentAndSignificand (x : Rat) : Option (Int × Rat) :=
  some (0, Rat.mk' 0 1)

def rationalExponent (x : Rat) : Option Int :=
  match rationalExponentAndSignificand x with
  | none => none
  | some (e, _) => e

def rationalSignificand (x : Rat) : Option Rat :=
  match rationalExponentAndSignificand x with
  | none => none
  | some (_, s) => s

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

theorem ratTrichotomy (x : Rat) : x < 0 ∨ x = 0 ∨ x > 0 := by
  have h := le_total x 0
  cases h with
  | inl h1 => have h2 := lt_or_eq_of_le h1
              cases h2 with
              | inl h3 => exact Or.inl h3
              | inr h4 => exact Or.inr (Or.inl h4)
  | inr h1 => have h2 := lt_or_eq_of_le h1
              cases h2 with
              | inl h3 => exact Or.inr (Or.inr h3)
              | inr h4 => have h5: x = 0 := by simp [h4]
                          exact Or.inr (Or.inl h5)

theorem ne_nlt_gt (x : Rat) : x ≠ 0 ∧ ¬(x < 0) → x > 0 :=
  by
  intro h
  obtain ⟨nonZero, nonNegative⟩ := h
  cases ratTrichotomy x with
  | inl h1 => contradiction
  | inr h2 => cases h2 with
    | inl h3 => contradiction
    | inr h4 => assumption

theorem abs_neg_pos (x : Rat) : x < 0 → |x| > 0 := by
  intro h
  have h1 := abs_pos_of_neg h
  exact h1

def RoundPositiveToDecimal128Domain (v : PositiveRational) (r : RoundingMode) : Decimal128Value :=
    let v' : Rat := v.1
    match rationalExponent v' with
    | some e =>
        let te : Int := max (e - (maxSignificantDigits - 1)) minDenomalizedExponent
        let m : Rat := v' * (rat10 ^ (0 - te))
        let rounded := ApplyRoundingModeToPositive v r
        if rounded = 0
        then Decimal128Value.PosZero
        else if rounded = 10 ^ maxSignificantDigits
        then Decimal128Value.PosInfinity
        else
          let x : Rat := rounded * (10 ^ te)
          have suitable: isRationalSuitable x := by sorry
          let y : SuitableRationals := ⟨x, suitable⟩
          Decimal128Value.Rational y
    | _ => Decimal128Value.NaN

def RoundToDecimal128Domain (v : Rat) (r : RoundingMode) : Decimal128Value :=
  if z: v = 0
  then Decimal128Value.PosZero
  else if n: v < 0
  then
    let reverseRoundingMode := ReverseRoundingMode r
    let v' := |v|
    have positive: v' > 0 := by
      apply abs_neg_pos v n
    let vPos : PositiveRational := ⟨v', positive⟩
    let d := RoundPositiveToDecimal128Domain vPos reverseRoundingMode
    match d with
    | Decimal128Value.PosInfinity => Decimal128Value.NegInfinity
    | Decimal128Value.PosZero => Decimal128Value.NegZero
    | Decimal128Value.Rational q => Decimal128Value.Rational (-q)
    | _ => Decimal128Value.NaN
  else
    have positive: v > 0 := by
      apply ne_nlt_gt v ⟨z, n⟩
    let vPos : PositiveRational := ⟨v, positive⟩
    RoundPositiveToDecimal128Domain vPos r

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
