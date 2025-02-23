import Mathlib
import Decimal128.Basic
import Decimal128.Arithmetic

theorem negationCorrect (p : Rat) (q : Rat) :
  isRationalSuitable p
∧ isRationalSuitable (-p)
→ ∃ (s1 : isRationalSuitable p) (s2 : isRationalSuitable (-p)),
  negate (Decimal128Value.Rational ⟨p, s1⟩)
  = Decimal128Value.Rational ⟨-p, s2⟩
:= by sorry

theorem absoluteValueCorrect (p : Rat) (q : Rat) :
  isRationalSuitable p
∧ isRationalSuitable |p|
→ ∃ (s1 : isRationalSuitable p) (s2 : isRationalSuitable |p|),
  absoluteValue (Decimal128Value.Rational ⟨p, s1⟩)
  = Decimal128Value.Rational ⟨|p|, s2⟩
:= by sorry

theorem additionCorrect (p : Rat) (q : Rat) :
  isRationalSuitable p
∧ isRationalSuitable q
∧ isRationalSuitable (p + q)
→ ∃ (s1 : isRationalSuitable p) (s2 : isRationalSuitable q) (s3 : isRationalSuitable (p + q)),
  add (Decimal128Value.Rational ⟨p, s1⟩)
      (Decimal128Value.Rational ⟨q, s2⟩)
  = Decimal128Value.Rational ⟨p + q, s3⟩
:= by sorry

theorem subtractionCorrect (p : Rat) (q : Rat) :
  isRationalSuitable p
∧ isRationalSuitable q
∧ isRationalSuitable (p - q)
→ ∃ (s1 : isRationalSuitable p) (s2 : isRationalSuitable q) (s3 : isRationalSuitable (p - q)),
  add (Decimal128Value.Rational ⟨p, s1⟩)
      (Decimal128Value.Rational ⟨q, s2⟩)
  = Decimal128Value.Rational ⟨p - q, s3⟩
:= by sorry

theorem multiplicationCorrect (p : Rat) (q : Rat) :
  isRationalSuitable p
∧ isRationalSuitable q
∧ isRationalSuitable (p * q)
→ ∃ (s1 : isRationalSuitable p) (s2 : isRationalSuitable q) (s3 : isRationalSuitable (p * q)),
  add (Decimal128Value.Rational ⟨p, s1⟩)
      (Decimal128Value.Rational ⟨q, s2⟩)
  = Decimal128Value.Rational ⟨p * q, s3⟩
:= by sorry

theorem divisionCorrect (p : Rat) (q : Rat) :
  isRationalSuitable p
∧ isRationalSuitable q
∧ isRationalSuitable (p / q)
→ ∃ (s1 : isRationalSuitable p) (s2 : isRationalSuitable q) (s3 : isRationalSuitable (p / q)),
  add (Decimal128Value.Rational ⟨p, s1⟩)
      (Decimal128Value.Rational ⟨q, s2⟩)
  = Decimal128Value.Rational ⟨p / q, s3⟩
:= by sorry

theorem remainderCorrect (p : Rat) (q : Rat) :
  isRationalSuitable p
∧ isRationalSuitable q
∧ isRationalSuitable (p % q)
→ ∃ (s1 : isRationalSuitable p) (s2 : isRationalSuitable q) (s3 : isRationalSuitable (p % q)),
  add (Decimal128Value.Rational ⟨p, s1⟩)
      (Decimal128Value.Rational ⟨q, s2⟩)
  = Decimal128Value.Rational ⟨p % q, s3⟩
:= by sorry

theorem scale10Correct (p : Rat) (n : Nat) :
  isRationalSuitable p
∧ isRationalSuitable (p ^ (10 * n))
→ ∃ (s1 : isRationalSuitable p) (s2 : isRationalSuitable (p ^ (10 * n))),
  scale10 (Decimal128Value.Rational ⟨p, s1⟩)
          n
  = Decimal128Value.Rational ⟨p ^ (10 * n), s2⟩
:= by sorry

theorem exponentCorrect (p : Rat) :
  isRationalSuitable p
  → ∃ (s1 : isRationalSuitable p) (s2 : isRationalSuitable (rationalExponent p)),
    exponent (Decimal128Value.Rational ⟨p, s1⟩)
    = Decimal128Value.Rational ⟨rationalExponent p, s2⟩
:= by sorry

theorem mantissaCorrect (p : Rat) :
  isRationalSuitable p
  → ∃ (s1 : isRationalSuitable p) (s2 : isRationalSuitable (rationalSignificand p)),
    exponent (Decimal128Value.Rational ⟨p, s1⟩)
    = Decimal128Value.Rational ⟨rationalSignificand p, s2⟩
:= by sorry
