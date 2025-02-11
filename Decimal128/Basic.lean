import Mathlib
import Decimal128.Constants
import Decimal128.Util
import Decimal128.Round

def maxCohortValue : Rat := scale10 maxSignificantDigits

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

instance : Neg SuitableRationals where
  neg x := ⟨-x.val, negationPreservesSuitability x.val x.property⟩

inductive Decimal128Value where
  | NaN : Decimal128Value
  | NegInfinity : Decimal128Value
  | PosInfinity : Decimal128Value
  | PosZero : Decimal128Value
  | NegZero : Decimal128Value
  | Rational : SuitableRationals → Decimal128Value

def mathematicalValue (x : Decimal128Value) : Option Rat :=
  match x with
  | Decimal128Value.PosZero => some 0
  | Decimal128Value.NegZero => some 0
  | Decimal128Value.Rational ⟨q, _⟩ => some q
  | _ => none

def rationalExponentAndSignificand (x : Rat) : Option (Int × Rat) :=
  some (0, x)

def rationalExponent (x : Rat) : Option Int :=
  match rationalExponentAndSignificand x with
  | none => none
  | some (e, _) => e

def rationalSignificand (x : Rat) : Option Rat :=
  match rationalExponentAndSignificand x with
  | none => none
  | some (_, s) => s

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

def sign (x : Decimal128Value) : Option Int :=
  match x with
  | Decimal128Value.NaN => none
  | Decimal128Value.NegInfinity => some (-1)
  | Decimal128Value.PosInfinity => some 1
  | Decimal128Value.PosZero => some 1
  | Decimal128Value.NegZero => some (-1)
  | Decimal128Value.Rational ⟨q, _⟩ => some (if q > 0 then 1 else -1)
