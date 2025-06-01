-- File: test_rat_to_int.lean
-- Converting Rat to Int when we have proof it's an integer

-- ANSWER: Use q.num directly
-- 
-- For a rational number q : Rat with proof h : Rat.isInt q,
-- the correct and most direct conversion to Int is simply: q.num
-- 
-- This works because:
-- 1. Rat.isInt q means q.den = 1 (the denominator is 1)
-- 2. Therefore q = q.num / q.den = q.num / 1 = q.num
-- 3. So q.num is exactly the integer value of q

def ratToInt (q : Rat) (h : Rat.isInt q) : Int := q.num

-- Alternative ways (more verbose but equivalent):

-- Method 1: Using Int.floor (overkill since we know it's already an integer)
def ratToIntFloor (q : Rat) (h : Rat.isInt q) : Int := Int.floor q

-- Method 2: Explicitly using the fact that den = 1
def ratToIntExplicit (q : Rat) (h : Rat.isInt q) : Int := by
  -- Since q.den = 1, we can use q.num directly
  exact q.num

-- The simplest and most idiomatic way is just q.num