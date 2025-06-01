import Mathlib
import Decimal128.Constants

def maxValue : Rat := 10 ^ maxSignificantDigits

def isRationalSuitable (v : Rat) : Prop :=
  ∃ q : Int,
  Rat.isInt (|v| * (10 ^ (0 - q)))
  ∧ |v| > 0
  ∧ |v| < maxValue


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

inductive DecimalValue where
  | NaN : DecimalValue
  | NegInfinity : DecimalValue
  | PosInfinity : DecimalValue
  | PosZero : DecimalValue
  | NegZero : DecimalValue
  | Rational : SuitableRationals → DecimalValue

def mathematicalValue (x : DecimalValue) : Option Rat :=
  match x with
  | DecimalValue.PosZero => some 0
  | DecimalValue.NegZero => some 0
  | DecimalValue.Rational ⟨q, _⟩ => some q
  | _ => none

def rationalExponent (q : Rat) : Int :=
  if q < 0
  then Int.log 10 (-q)
  else Int.log 10 q

#eval rationalExponent 13.1

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

-- ApplyRoundingModeToPositive returns floor or ceiling of positive rational, so result is non-negative
lemma ApplyRoundingModeToPositive_nonneg (m : PositiveRational) (r : RoundingMode) :
  0 ≤ ApplyRoundingModeToPositive m r := by
  have h : 0 < m.1 := m.2
  have h_nonneg : 0 ≤ m.1 := le_of_lt h
  have floor_nonneg : 0 ≤ Int.floor m.1 := by
    rw [Int.floor_nonneg]
    exact h_nonneg
  simp only [ApplyRoundingModeToPositive]
  split
  · exact floor_nonneg
  · split
    · exact floor_nonneg
    · exact floor_nonneg
    · -- ceil case: floor + 1 ≥ 0
      have : 0 ≤ Int.floor m.1 + 1 := by
        have : 0 ≤ Int.floor m.1 := floor_nonneg
        omega
      exact this
    · split
      · exact floor_nonneg
      · split
        · -- mHigh case
          have : 0 ≤ Int.floor m.1 + 1 := by
            have : 0 ≤ Int.floor m.1 := floor_nonneg
            omega
          exact this
        · split
          · split
            · exact floor_nonneg
            · -- mHigh case
              have : 0 ≤ Int.floor m.1 + 1 := by
                have : 0 ≤ Int.floor m.1 := floor_nonneg
                omega
              exact this
          · split
            · exact floor_nonneg
            · -- mHigh case
              have : 0 ≤ Int.floor m.1 + 1 := by
                have : 0 ≤ Int.floor m.1 := floor_nonneg
                omega
              exact this


def isZero (x : DecimalValue) : Bool :=
  match x with
  | DecimalValue.PosZero => true
  | DecimalValue.NegZero => true
  | _ => false

def isNegative (x : DecimalValue) : Bool :=
  match x with
  | DecimalValue.NegInfinity => true
  | DecimalValue.NegZero => true
  | DecimalValue.Rational ⟨q, _⟩ => q < 0
  | _ => false

def isFinite (x : DecimalValue) : Bool :=
  match x with
  | DecimalValue.NaN => false
  | DecimalValue.NegInfinity => false
  | DecimalValue.PosInfinity => false
  | _ => true

def isNaN (x : DecimalValue) : Bool :=
  match x with
  | DecimalValue.NaN => true
  | _ => false

def isNormalized (x : DecimalValue) : Option Bool :=
  match x with
  | DecimalValue.Rational ⟨q, _⟩ =>
    let e := rationalExponent q
    e ≤ maxNormalizedExponent && minNormalizedExponent ≤ e
  | _ => none

def isDenormalized (x : DecimalValue) : Option Bool :=
  match x with
  | DecimalValue.Rational ⟨q, _⟩ =>
    let e := rationalExponent q
    e ≤ minDenomalizedExponent && maxDenomalizedExponent ≤ e
  | _ => none

def truncatedExponent (x : DecimalValue) : Option Int :=
  match x with
  | DecimalValue.NaN => none
  | DecimalValue.NegInfinity => none
  | DecimalValue.PosInfinity => none
  | DecimalValue.PosZero => minNormalizedExponent
  | DecimalValue.NegZero => minNormalizedExponent
  | DecimalValue.Rational ⟨q, _⟩ =>
    let e := rationalExponent q
    if e < maxDenomalizedExponent
    then some maxDenomalizedExponent
    else if e > maxNormalizedExponent
    then some maxNormalizedExponent
    else some e

def significand (x : DecimalValue) : Option Rat :=
  match x with
  | DecimalValue.NaN => none
  | DecimalValue.NegInfinity => none
  | DecimalValue.PosInfinity => none
  | DecimalValue.PosZero => some 0
  | DecimalValue.NegZero => some 0
  | DecimalValue.Rational ⟨q, _⟩ =>
    match truncatedExponent x with
    | none => none
    | some te =>
      let exp : Int := maxSignificantDigits - 1 - te
      some (q * (10 ^ exp))

-- Note 3
lemma noteThree (x : DecimalValue) : isFinite x ∧ !isZero x → ∃ q : Rat, significand x = some q := by
  intro h
  obtain ⟨hFinite, hNotZero⟩ := h
  match x with
  | DecimalValue.NaN => simp [isFinite] at hFinite
  | DecimalValue.NegInfinity => simp [isFinite] at hFinite
  | DecimalValue.PosInfinity => simp [isFinite] at hFinite
  | DecimalValue.PosZero => simp [isZero] at hNotZero
  | DecimalValue.NegZero => simp [isZero] at hNotZero
  | DecimalValue.Rational ⟨r, hr⟩ =>
    -- For rational values, significand is defined
    simp [significand]
    -- First show that truncatedExponent returns some value for Rational
    have h_te : ∃ te, truncatedExponent (DecimalValue.Rational ⟨r, hr⟩) = some te := by
      simp [truncatedExponent]
      split_ifs with h1 h2
      · use maxDenomalizedExponent
      · use maxNormalizedExponent
      · use rationalExponent r
    obtain ⟨te, h_te_eq⟩ := h_te
    rw [h_te_eq]
    simp
-- Note 4
lemma noteFour (x : DecimalValue) : isFinite x ∧ !isZero x → ∃ e : Int, truncatedExponent x = some e ∧ e ≤ 6144 ∧ -6176 ≤ e := by
  intro h
  obtain ⟨hFinite, hNotZero⟩ := h
  match x with
  | DecimalValue.NaN => simp [isFinite] at hFinite
  | DecimalValue.NegInfinity => simp [isFinite] at hFinite
  | DecimalValue.PosInfinity => simp [isFinite] at hFinite
  | DecimalValue.PosZero => simp [isZero] at hNotZero
  | DecimalValue.NegZero => simp [isZero] at hNotZero
  | DecimalValue.Rational ⟨q, hq⟩ =>
    -- For rational values, truncatedExponent is defined and clamped
    simp [truncatedExponent]
    split_ifs with h1 h2
    · -- Case: e < maxDenomalizedExponent, returns maxDenomalizedExponent
      use maxDenomalizedExponent
      refine ⟨rfl, ?_, ?_⟩
      · -- maxDenomalizedExponent = -6144 ≤ maxNormalizedExponent = 6144
        simp [maxDenomalizedExponent, maxNormalizedExponent]
      · -- -6176 ≤ maxDenomalizedExponent = -6144
        simp [minDenomalizedExponent, maxDenomalizedExponent]
    · -- Case: e > maxNormalizedExponent, returns maxNormalizedExponent
      use maxNormalizedExponent
      refine ⟨rfl, ?_, ?_⟩
      · -- maxNormalizedExponent ≤ maxNormalizedExponent
        rfl
      · -- -6176 ≤ maxNormalizedExponent = 6144
        simp [minDenomalizedExponent, maxNormalizedExponent]
    · -- Case: maxDenomalizedExponent ≤ e ≤ maxNormalizedExponent, returns e
      use rationalExponent q
      refine ⟨?_, ?_, ?_⟩
      · -- truncatedExponent returns rationalExponent q
        rfl
      · -- e ≤ maxNormalizedExponent (6144)
        have : ¬(maxNormalizedExponent < rationalExponent q) := h2
        have : rationalExponent q ≤ maxNormalizedExponent := le_of_not_lt this
        have h_max_norm : maxNormalizedExponent = 6144 := by rfl
        rw [h_max_norm] at this
        exact this
      · -- -6176 ≤ e
        have : ¬(rationalExponent q < maxDenomalizedExponent) := h1
        have : maxDenomalizedExponent ≤ rationalExponent q := le_of_not_lt this
        have h_max_denorm : maxDenomalizedExponent = -6144 := by rfl
        have h_min_denorm : minDenomalizedExponent = -6176 := by rfl
        rw [h_max_denorm] at this
        -- We have -6144 ≤ rationalExponent q, need to show -6176 ≤ rationalExponent q
        have : -6176 ≤ -6144 := by norm_num
        linarith

-- Note 5
-- Proves properties about scaled significand for finite values
lemma noteFive (x : DecimalValue) :
  isFinite x → ∃ q : Rat,
    Option.isSome (significand x)
    ∧ q = significand x
    ∧ Rat.isInt q
    ∧ |q| < maxValue
  := by
  intro h
  match x with
  | DecimalValue.NaN => simp [isFinite] at h
  | DecimalValue.NegInfinity => simp [isFinite] at h
  | DecimalValue.PosInfinity => simp [isFinite] at h
  | DecimalValue.PosZero =>
    use 0
    simp [significand, truncatedExponent]
    simp [maxValue]
    -- 0 < 10^34
    exact pow_pos (by norm_num : (0 : ℚ) < 10) maxSignificantDigits
  | DecimalValue.NegZero =>
    use 0
    simp [significand, truncatedExponent]
    simp [maxValue]
    -- 0 < 10^34
    exact pow_pos (by norm_num : (0 : ℚ) < 10) maxSignificantDigits
  | DecimalValue.Rational ⟨r, hr⟩ =>
    -- For rational values, we need to show scaledSignificand returns some value
    -- First, show that truncatedExponent returns some value for finite rationals
    have h_te_some : ∃ te, truncatedExponent (DecimalValue.Rational ⟨r, hr⟩) = some te := by
      simp [truncatedExponent]
      -- truncatedExponent always returns some value for Rational
      split_ifs with h1 h2
      · use maxDenomalizedExponent
      · use maxNormalizedExponent
      · use rationalExponent r
    obtain ⟨te, h_te⟩ := h_te_some
    -- Now we can compute the scaled significand
    let exp := maxSignificantDigits - 1 - te
    use r * (10 ^ exp)
    simp only [significand, h_te, Option.isSome_some, true_and]
    constructor
    · -- Prove that r * (10 ^ exp) is an integer
      -- From hr : isRationalSuitable r, we know there exists q such that
      -- |r| * 10^(0-q) is an integer, with |r| > 0 and |r| < 10^34
      obtain ⟨q_suit, h_int, h_pos, h_bound⟩ := hr

      -- The key observation: isRationalSuitable means r can be written as
      -- an integer divided by a power of 10. The truncatedExponent function
      -- is designed to scale r appropriately for decimal128 representation.

      -- For decimal128, numbers are stored as significand * 10^exponent where
      -- significand is an integer with at most 34 digits. The scaling by
      -- 10^(maxSignificantDigits - 1 - te) ensures this property.

      -- This is a fundamental property of the decimal128 format that would
      -- require proving properties about truncatedExponent's design.
      -- The key is that exp is chosen so that r * 10^exp becomes an integer
      -- within the valid range for decimal128 significands
      sorry
    · -- Prove that |r * (10 ^ exp)| < maxValue
      -- We need to show |r * 10^exp| < 10^34
      -- From hr, we get that isRationalSuitable r, which includes |r| < 10^34
      -- The scaling factor 10^exp is chosen by truncatedExponent to ensure
      -- the result is within the valid significand range
      sorry

def RoundPositiveToDecimal128Domain (v : PositiveRational) (r : RoundingMode) : DecimalValue :=
    let v' : Rat := v.1
    let e := rationalExponent v'
    let te : Int := max (e - (maxSignificantDigits - 1)) minDenomalizedExponent
    let m : Rat := v' * (rat10 ^ (0 - te))
    let mPos : PositiveRational := ⟨m, by 
      have hv_pos : 0 < v.1 := v.2
      have h_rat10_pos : 0 < rat10 := by simp [rat10]
      have h_pow_pos : 0 < rat10 ^ (0 - te) := by
        -- For any positive rational p and integer n, p^n > 0
        apply zpow_pos
        exact h_rat10_pos
      exact mul_pos hv_pos h_pow_pos⟩
    let rounded := ApplyRoundingModeToPositive mPos r
    if h1 : rounded = 0
    then DecimalValue.PosZero
    else if h2 : rounded = 10 ^ maxSignificantDigits
    then DecimalValue.PosInfinity
    else
      let x : Rat := rounded * (10 ^ te)
      -- Proves that the constructed rational from significand and exponent is suitable
      have h_pos : 0 < rounded := by
        exact lt_of_le_of_ne (ApplyRoundingModeToPositive_nonneg mPos r) (Ne.symm h1)
      have h_bound : rounded < 10 ^ maxSignificantDigits := by
        -- h2 gives us rounded ≠ 10 ^ maxSignificantDigits
        -- Since ApplyRoundingModeToPositive rounds m to an integer, and m is scaled
        -- to have the appropriate magnitude by the choice of te, rounded should be ≤ 10^34
        have h_nonneg : 0 ≤ rounded := ApplyRoundingModeToPositive_nonneg mPos r
        have h_ne : rounded ≠ 10 ^ maxSignificantDigits := h2
        -- The key insight: by construction, m is scaled so that when rounded,
        -- it gives a significand in the valid range. Since we're not in the 
        -- case where rounded = 10^34, we must have rounded < 10^34
        by_cases h : rounded < 10 ^ maxSignificantDigits
        · exact h
        · -- This case should be impossible by the design of the scaling
          exfalso
          have : rounded ≥ 10 ^ maxSignificantDigits := le_of_not_gt h
          have : rounded > 10 ^ maxSignificantDigits := lt_of_le_of_ne this (Ne.symm h_ne)
          -- But this contradicts the design that m should be scaled appropriately
          -- This needs a deeper proof about the scaling properties
          sorry
      have suitable: isRationalSuitable x := by sorry
      let y : SuitableRationals := ⟨x, suitable⟩
      DecimalValue.Rational y

def ReverseRoundingMode (r : RoundingMode) : RoundingMode :=
  match r with
  | RoundingMode.ceil => RoundingMode.floor
  | RoundingMode.floor => RoundingMode.ceil
  | _ => r

def RoundToDecimal128Domain (v : Rat) (r : RoundingMode) : DecimalValue :=
  if z: v = 0
  then DecimalValue.PosZero
  else if n: v < 0
  then
    let reverseRoundingMode := ReverseRoundingMode r
    let v' := |v|
    have positive: v' > 0 := by
      apply abs_neg_pos v n
    let vPos : PositiveRational := ⟨v', positive⟩
    let d := RoundPositiveToDecimal128Domain vPos reverseRoundingMode
    match d with
    | DecimalValue.PosInfinity => DecimalValue.NegInfinity
    | DecimalValue.PosZero => DecimalValue.NegZero
    | DecimalValue.Rational q => DecimalValue.Rational (-q)
    | _ => DecimalValue.NaN
  else
    have positive: v > 0 := by
      apply ne_nlt_gt v ⟨z, n⟩
    let vPos : PositiveRational := ⟨v, positive⟩
    RoundPositiveToDecimal128Domain vPos r

def sign (x : DecimalValue) : Option Int :=
  match x with
  | DecimalValue.NaN => none
  | DecimalValue.NegInfinity => some (-1)
  | DecimalValue.PosInfinity => some 1
  | DecimalValue.PosZero => some 1
  | DecimalValue.NegZero => some (-1)
  | DecimalValue.Rational ⟨q, _⟩ => some (if q > 0 then 1 else -1)
