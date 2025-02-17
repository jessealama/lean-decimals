import Mathlib
import Decimal128.Constants

def maxCohortValue : Rat := 10 ^ maxSignificantDigits

def isRationalSuitable (v : Rat) : Prop :=
  ∃ q : Int,
  Rat.isInt (|v| * (10 ^ (0 - q)))
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

def rationalExponent (q : Rat) : Int :=
  if q < 0
  then Int.log 10 (-q)
  else Int.log 10 q

#eval rationalExponent 0.03

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

def isNormalized (x : Decimal128Value) : Option Bool :=
  match x with
  | Decimal128Value.Rational ⟨q, _⟩ =>
    let e := rationalExponent q
    e ≤ maxNormalizedExponent && minNormalizedExponent ≤ e
  | _ => none

def isDenormalized (x : Decimal128Value) : Option Bool :=
  match x with
  | Decimal128Value.Rational ⟨q, _⟩ =>
    let e := rationalExponent q
    e ≤ minDenomalizedExponent && maxDenomalizedExponent ≤ e
  | _ => none

def RoundPositiveToDecimal128Domain (v : PositiveRational) (r : RoundingMode) : Decimal128Value :=
    let v' : Rat := v.1
    let rounded := ApplyRoundingModeToPositive v r
    let e := rationalExponent v'
    let te : Int := max (e - (maxSignificantDigits - 1)) minDenomalizedExponent
    let m : Rat := v' * (rat10 ^ (0 - te))
    if rounded = 0
    then Decimal128Value.PosZero
    else if rounded = 10 ^ maxSignificantDigits
    then Decimal128Value.PosInfinity
    else
      let x : Rat := rounded * (10 ^ te)
      have suitable: isRationalSuitable x := by sorry
      let y : SuitableRationals := ⟨x, suitable⟩
      Decimal128Value.Rational y

def ReverseRoundingMode (r : RoundingMode) : RoundingMode :=
  match r with
  | RoundingMode.ceil => RoundingMode.floor
  | RoundingMode.floor => RoundingMode.ceil
  | _ => r

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
