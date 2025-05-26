import Mathlib
import Decimal128.Basic
import Decimal128.Arithmetic

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
  rfl

-- Proves that absolute value of a suitable rational produces the expected result
theorem absoluteValueCorrect (p : Rat) (q : Rat) :
  isRationalSuitable p
∧ isRationalSuitable |p|
→ ∃ (s1 : isRationalSuitable p) (s2 : isRationalSuitable |p|),
  absoluteValue (DecimalValue.Rational ⟨p, s1⟩)
  = DecimalValue.Rational ⟨|p|, s2⟩
:= by sorry

-- Proves that adding two suitable rationals produces the expected result
theorem additionCorrect (p : Rat) (q : Rat) :
  isRationalSuitable p
∧ isRationalSuitable q
∧ isRationalSuitable (p + q)
→ ∃ (s1 : isRationalSuitable p) (s2 : isRationalSuitable q) (s3 : isRationalSuitable (p + q)),
  add (DecimalValue.Rational ⟨p, s1⟩)
      (DecimalValue.Rational ⟨q, s2⟩)
  = DecimalValue.Rational ⟨p + q, s3⟩
:= by sorry

-- Proves that subtracting two suitable rationals produces the expected result
theorem subtractionCorrect (p : Rat) (q : Rat) :
  isRationalSuitable p
∧ isRationalSuitable q
∧ isRationalSuitable (p - q)
→ ∃ (s1 : isRationalSuitable p) (s2 : isRationalSuitable q) (s3 : isRationalSuitable (p - q)),
  add (DecimalValue.Rational ⟨p, s1⟩)
      (DecimalValue.Rational ⟨q, s2⟩)
  = DecimalValue.Rational ⟨p - q, s3⟩
:= by sorry

-- Proves that multiplying two suitable rationals produces the expected result
theorem multiplicationCorrect (p : Rat) (q : Rat) :
  isRationalSuitable p
∧ isRationalSuitable q
∧ isRationalSuitable (p * q)
→ ∃ (s1 : isRationalSuitable p) (s2 : isRationalSuitable q) (s3 : isRationalSuitable (p * q)),
  add (DecimalValue.Rational ⟨p, s1⟩)
      (DecimalValue.Rational ⟨q, s2⟩)
  = DecimalValue.Rational ⟨p * q, s3⟩
:= by sorry

-- Proves that dividing two suitable rationals produces the expected result
theorem divisionCorrect (p : Rat) (q : Rat) :
  isRationalSuitable p
∧ isRationalSuitable q
∧ isRationalSuitable (p / q)
→ ∃ (s1 : isRationalSuitable p) (s2 : isRationalSuitable q) (s3 : isRationalSuitable (p / q)),
  add (DecimalValue.Rational ⟨p, s1⟩)
      (DecimalValue.Rational ⟨q, s2⟩)
  = DecimalValue.Rational ⟨p / q, s3⟩
:= by sorry

-- Proves that remainder of two suitable rationals produces the expected result
theorem remainderCorrect (p : Rat) (q : Rat) :
  isRationalSuitable p
∧ isRationalSuitable q
∧ isRationalSuitable (p % q)
→ ∃ (s1 : isRationalSuitable p) (s2 : isRationalSuitable q) (s3 : isRationalSuitable (p % q)),
  add (DecimalValue.Rational ⟨p, s1⟩)
      (DecimalValue.Rational ⟨q, s2⟩)
  = DecimalValue.Rational ⟨p % q, s3⟩
:= by sorry

-- Proves that scaling by powers of 10 produces the expected result
theorem scale10Correct (p : Rat) (n : Nat) :
  isRationalSuitable p
∧ isRationalSuitable (p ^ (10 * n))
→ ∃ (s1 : isRationalSuitable p) (s2 : isRationalSuitable (p ^ (10 * n))),
  scale10 (DecimalValue.Rational ⟨p, s1⟩)
          n
  = DecimalValue.Rational ⟨p ^ (10 * n), s2⟩
:= by sorry

-- Proves that exponent extraction produces the expected result
theorem exponentCorrect (p : Rat) :
  isRationalSuitable p
  → ∃ (s1 : isRationalSuitable p) (s2 : isRationalSuitable (rationalExponent p)),
    exponent (DecimalValue.Rational ⟨p, s1⟩)
    = DecimalValue.Rational ⟨rationalExponent p, s2⟩
:= by sorry

-- Proves that mantissa extraction produces the expected result
theorem mantissaCorrect (p : Rat) :
  isRationalSuitable p
  → ∃ (s1 : isRationalSuitable p) (s2 : isRationalSuitable (rationalSignificand p)),
    exponent (DecimalValue.Rational ⟨p, s1⟩)
    = DecimalValue.Rational ⟨rationalSignificand p, s2⟩
:= by sorry
