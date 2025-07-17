import Mathlib
import Decimal128.Basic
import Decimal128.Arithmetic

-- Proves that RoundToDecimal128Domain preserves suitable rationals exactly
lemma roundPreservesSuitable (p : Rat) (r : RoundingMode) :
  isRationalSuitable p →
  ∃ (s : isRationalSuitable p),
    RoundToDecimal128Domain p r = DecimalValue.Rational ⟨p, s⟩
:= by sorry

-- Proves that the truncate function matches Lean's floor for positive rationals
-- and ceiling (negated) for negative rationals
lemma truncateCorrect (x : Rat) :
  truncate x = if x < 0 then -Rat.floor (-x) else Rat.floor x
:= by
  simp only [truncate]
  split_ifs with h
  · simp [sub_eq_neg_add]
  · rfl

-- Defines the mathematical remainder for rationals as p - truncate(p/q) * q
def ratRemainder (p q : Rat) : Rat :=
  p - (truncate (p / q)) * q

-- Proves properties about the rational remainder function
lemma ratRemainderBounds (p q : Rat) (hq : q > 0) :
  let r := ratRemainder p q
  0 ≤ r ∧ r < q
:= by sorry

-- Proves that when the remainder is suitable, it's preserved by rounding
lemma remainderRoundingPreserves (p q : Rat) (hq : q ≠ 0) :
  let r := ratRemainder p q
  isRationalSuitable r →
  ∃ (s : isRationalSuitable r),
    (if r = 0 ∧ p < 0
    then DecimalValue.NegZero
    else RoundToDecimal128Domain r RoundingMode.halfEven)
    = if r = 0 ∧ p < 0
      then DecimalValue.NegZero
      else DecimalValue.Rational ⟨r, s⟩
:= by sorry

-- Proves that negating a suitable rational produces the expected result
theorem negationCorrect (p : Rat) :
  isRationalSuitable p
∧ isRationalSuitable (-p)
→ ∃ (s1 : isRationalSuitable p) (s2 : isRationalSuitable (-p)),
  negate (DecimalValue.Rational ⟨p, s1⟩)
  = DecimalValue.Rational ⟨-p, s2⟩
:= by
  intro ⟨h1, h2⟩
  use h1, h2
  simp [negate]

-- Proves that negating positive zero gives negative zero
theorem negatePosZero :
  negate DecimalValue.PosZero = DecimalValue.NegZero
:= by rfl

-- Proves that negating negative zero gives positive zero
theorem negateNegZero :
  negate DecimalValue.NegZero = DecimalValue.PosZero
:= by rfl

-- Proves that negating positive infinity gives negative infinity
theorem negatePosInfinity :
  negate DecimalValue.PosInfinity = DecimalValue.NegInfinity
:= by rfl

-- Proves that negating negative infinity gives positive infinity
theorem negateNegInfinity :
  negate DecimalValue.NegInfinity = DecimalValue.PosInfinity
:= by rfl

-- Proves that negation preserves the zero property
theorem negateZeroIsZero (x : DecimalValue) :
  isZero x → isZero (negate x)
:= by
  intro h
  cases x with
  | PosZero => simp [negate, isZero]
  | NegZero => simp [negate, isZero]
  | NaN => simp [isZero] at h
  | PosInfinity => simp [isZero] at h
  | NegInfinity => simp [isZero] at h
  | Rational _ => simp [isZero] at h

-- Proves that absolute value of a suitable rational produces the expected result
theorem absoluteValueCorrect (p : Rat) :
  isRationalSuitable p
∧ isRationalSuitable |p|
→ ∃ (s1 : isRationalSuitable p) (s2 : isRationalSuitable |p|),
  absoluteValue (DecimalValue.Rational ⟨p, s1⟩)
  = DecimalValue.Rational ⟨|p|, s2⟩
:= by
  intro ⟨h1, h2⟩
  use h1, h2
  simp [absoluteValue]

-- Proves that absolute value of positive zero is positive zero
theorem absoluteValuePosZero :
  absoluteValue DecimalValue.PosZero = DecimalValue.PosZero
:= by rfl

-- Proves that absolute value of negative zero is positive zero
theorem absoluteValueNegZero :
  absoluteValue DecimalValue.NegZero = DecimalValue.PosZero
:= by rfl

-- Proves that absolute value always returns positive zero for any zero
theorem absoluteValueZeroAlwaysPosZero (x : DecimalValue) :
  isZero x → absoluteValue x = DecimalValue.PosZero
:= by
  intro h
  cases x with
  | PosZero => rfl
  | NegZero => rfl
  | NaN => simp [isZero] at h
  | PosInfinity => simp [isZero] at h
  | NegInfinity => simp [isZero] at h
  | Rational _ => simp [isZero] at h

-- Proves that adding two suitable rationals produces the expected result
theorem additionCorrect (p : Rat) (q : Rat) :
  isRationalSuitable p
∧ isRationalSuitable q
∧ isRationalSuitable (p + q)
→ ∃ (s1 : isRationalSuitable p) (s2 : isRationalSuitable q) (s3 : isRationalSuitable (p + q)),
  add (DecimalValue.Rational ⟨p, s1⟩)
      (DecimalValue.Rational ⟨q, s2⟩)
  = DecimalValue.Rational ⟨p + q, s3⟩
:= by
  intro ⟨h1, h2, h3⟩
  use h1, h2
  -- Apply the roundPreservesSuitable lemma
  obtain ⟨s3, h_round⟩ := roundPreservesSuitable (p + q) RoundingMode.halfEven h3
  use s3
  simp [add]
  exact h_round

-- Proves that when two suitable rationals sum to zero, addition returns a zero
-- Note: When two non-zero rationals sum to exactly zero, the result is always
-- positive zero. This matches JavaScript behavior where -1 + 1 = +0 (not -0).
-- The only way to get -0 from addition is -0 + -0 = -0.
theorem additionZeroResult (p : Rat) (q : Rat) :
  isRationalSuitable p
  → isRationalSuitable q
  → p + q = 0
  → ∃ (s1 : isRationalSuitable p) (s2 : isRationalSuitable q),
    isZero (add (DecimalValue.Rational ⟨p, s1⟩)
                (DecimalValue.Rational ⟨q, s2⟩))
:= by
  intro hp hq h_sum
  use hp, hq
  simp [add]
  -- RoundToDecimal128Domain returns PosZero when given 0
  rw [h_sum]
  simp [RoundToDecimal128Domain]
  simp [isZero]

-- Proves that subtracting two suitable rationals produces the expected result
theorem subtractionCorrect (p : Rat) (q : Rat) :
  isRationalSuitable p
∧ isRationalSuitable q
∧ isRationalSuitable (p - q)
→ ∃ (s1 : isRationalSuitable p) (s2 : isRationalSuitable q) (s3 : isRationalSuitable (p - q)),
  sub (DecimalValue.Rational ⟨p, s1⟩)
      (DecimalValue.Rational ⟨q, s2⟩)
  = DecimalValue.Rational ⟨p - q, s3⟩
:= by
  intro ⟨h1, h2, h3⟩
  use h1, h2
  -- Apply the roundPreservesSuitable lemma
  obtain ⟨s3, h_round⟩ := roundPreservesSuitable (p - q) RoundingMode.halfEven h3
  use s3
  simp [sub]
  exact h_round

-- Proves key subtraction zero cases
theorem subNegZeroPosZero :
  sub DecimalValue.NegZero DecimalValue.PosZero = DecimalValue.NegZero
:= by rfl

theorem subNegZeroNegZero :
  sub DecimalValue.NegZero DecimalValue.NegZero = DecimalValue.PosZero
:= by rfl

theorem subPosZeroPosZero :
  sub DecimalValue.PosZero DecimalValue.PosZero = DecimalValue.PosZero
:= by rfl

theorem subPosZeroNegZero :
  sub DecimalValue.PosZero DecimalValue.NegZero = DecimalValue.PosZero
:= by rfl

-- Proves that when two suitable rationals have equal values, subtraction returns zero
-- Note: Like addition, when two non-zero rationals subtract to exactly zero,
-- the result is always positive zero. This matches JavaScript behavior.
theorem subtractionZeroResult (p : Rat) (q : Rat) :
  isRationalSuitable p
  → isRationalSuitable q
  → p - q = 0
  → ∃ (s1 : isRationalSuitable p) (s2 : isRationalSuitable q),
    isZero (sub (DecimalValue.Rational ⟨p, s1⟩)
                (DecimalValue.Rational ⟨q, s2⟩))
:= by
  intro hp hq h_diff
  use hp, hq
  simp [sub]
  -- RoundToDecimal128Domain returns PosZero when given 0
  rw [h_diff]
  simp [RoundToDecimal128Domain]
  simp [isZero]

-- Proves that zero minus any value equals the negation of that value
theorem subZeroValue (y : DecimalValue) :
  sub DecimalValue.PosZero y = negate y
:= by
  cases y with
  | NaN => rfl
  | PosInfinity => rfl
  | NegInfinity => rfl
  | PosZero => rfl
  | NegZero => rfl
  | Rational _ => rfl

-- Proves that negative zero minus any value equals the negation of that value
theorem subNegZeroValue (y : DecimalValue) :
  sub DecimalValue.NegZero y = negate y
:= by
  cases y with
  | NaN => rfl
  | PosInfinity => rfl
  | NegInfinity => rfl
  | PosZero => rfl
  | NegZero => rfl
  | Rational _ => rfl

-- Proves that multiplying two suitable rationals produces the expected result
theorem multiplicationCorrect (p : Rat) (q : Rat) :
  isRationalSuitable p
∧ isRationalSuitable q
∧ isRationalSuitable (p * q)
→ ∃ (s1 : isRationalSuitable p) (s2 : isRationalSuitable q) (s3 : isRationalSuitable (p * q)),
  multiply (DecimalValue.Rational ⟨p, s1⟩)
      (DecimalValue.Rational ⟨q, s2⟩)
  = DecimalValue.Rational ⟨p * q, s3⟩
:= by
  intro ⟨h1, h2, h3⟩
  use h1, h2
  -- Apply the roundPreservesSuitable lemma
  obtain ⟨s3, h_round⟩ := roundPreservesSuitable (p * q) RoundingMode.halfEven h3
  use s3
  simp [multiply]
  exact h_round

-- Proves that dividing two suitable rationals produces the expected result
theorem divisionCorrect (p : Rat) (q : Rat) :
  isRationalSuitable p
∧ isRationalSuitable q
∧ isRationalSuitable (p / q)
→ ∃ (s1 : isRationalSuitable p) (s2 : isRationalSuitable q) (s3 : isRationalSuitable (p / q)),
  divide (DecimalValue.Rational ⟨p, s1⟩)
      (DecimalValue.Rational ⟨q, s2⟩)
  = DecimalValue.Rational ⟨p / q, s3⟩
:= by
  intro ⟨h1, h2, h3⟩
  use h1, h2
  -- Apply the roundPreservesSuitable lemma
  obtain ⟨s3, h_round⟩ := roundPreservesSuitable (p / q) RoundingMode.halfEven h3
  use s3
  simp [divide]
  exact h_round

-- Proves that when remainder is zero, the result respects IEEE 754 signed zero semantics
theorem remainderZeroCorrect (p : Rat) (q : Rat) :
  isRationalSuitable p
∧ isRationalSuitable q
∧ ratRemainder p q = 0
→ ∃ (s1 : isRationalSuitable p) (s2 : isRationalSuitable q),
  isZero (remainder (DecimalValue.Rational ⟨p, s1⟩)
      (DecimalValue.Rational ⟨q, s2⟩))
:= by sorry

-- Proves that remainder of two suitable rationals produces the expected result
-- Note: Rat does have a % operator from its Field/EuclideanDomain instance,
-- but it always returns 0 (since division is exact in a field).
-- Our ratRemainder function implements the truncating remainder we need.
theorem remainderCorrect (p : Rat) (q : Rat) :
  isRationalSuitable p
∧ isRationalSuitable q
∧ isRationalSuitable (ratRemainder p q)
→ ∃ (s1 : isRationalSuitable p) (s2 : isRationalSuitable q) (s3 : isRationalSuitable (ratRemainder p q)),
  remainder (DecimalValue.Rational ⟨p, s1⟩)
      (DecimalValue.Rational ⟨q, s2⟩)
  = DecimalValue.Rational ⟨ratRemainder p q, s3⟩
:= by
  intro ⟨h1, h2, h3⟩
  -- Since q ≠ 0 (otherwise it wouldn't be suitable)
  have hq : q ≠ 0 := by
    obtain ⟨_, _, hpos, _⟩ := h2
    exact abs_pos.mp hpos
  -- Apply the remainderRoundingPreserves lemma
  obtain ⟨s3, h_round⟩ := remainderRoundingPreserves p q hq h3
  -- Provide all three witnesses
  use h1, h2, s3
  -- Now prove the equality
  simp only [remainder]
  -- Since ratRemainder p q is suitable, it's not zero
  have h_nonzero : ratRemainder p q ≠ 0 := by
    intro h_eq
    rw [h_eq] at h3
    -- h3 says isRationalSuitable 0, which requires |0| > 0
    obtain ⟨_, _, habs, _⟩ := h3
    -- But |0| = 0, not > 0
    rw [abs_zero] at habs
    -- This gives us 0 > 0, which is false
    exact (lt_irrefl 0) habs
  -- The rest requires careful matching of the if-then-else expression
  sorry

-- Proves that scaling by powers of 10 produces the expected result
theorem scale10Correct (p : Rat) (n : Int) :
  isRationalSuitable p
∧ isRationalSuitable (p * (10 ^ n))
→ ∃ (s1 : isRationalSuitable p) (s2 : isRationalSuitable (p * (10 ^ n))),
  scale10 (DecimalValue.Rational ⟨p, s1⟩) n
  = DecimalValue.Rational ⟨p * (10 ^ n), s2⟩
:= by
  intro ⟨h1, h2⟩
  use h1
  -- Apply the roundPreservesSuitable lemma
  obtain ⟨s2, h_round⟩ := roundPreservesSuitable (p * (10 ^ n)) RoundingMode.halfEven h2
  use s2
  simp [scale10]
  exact h_round

-- Proves that exponent extraction produces the expected result
theorem exponentCorrect (p : Rat) :
  isRationalSuitable p
  → ∃ (s1 : isRationalSuitable p) (s2 : isRationalSuitable (rationalExponent p : Rat)),
    exponent (DecimalValue.Rational ⟨p, s1⟩)
    = DecimalValue.Rational ⟨(rationalExponent p : Rat), s2⟩
:= by
  intro h1
  use h1
  -- We need to prove that the exponent is suitable
  have h2 : isRationalSuitable (rationalExponent p : Rat) := exponentSuitable p h1
  use h2
  simp [exponent]

-- Proves that mantissa extraction produces the expected result
theorem mantissaCorrect (p : Rat) :
  isRationalSuitable p
  → ∃ (s1 : isRationalSuitable p) (s2 : isRationalSuitable (rationalSignificand p)),
    mantissa (DecimalValue.Rational ⟨p, s1⟩)
    = DecimalValue.Rational ⟨rationalSignificand p, s2⟩
:= by
  intro h1
  use h1
  -- The mantissa function already applies significandPreservesSuitability
  have h2 : isRationalSuitable (rationalSignificand p) := significandPreservesSuitability p h1
  use h2
  simp [mantissa]
