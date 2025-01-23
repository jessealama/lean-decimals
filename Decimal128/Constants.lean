import Mathlib

def maxSignificantDigits : Nat := 34
def minDenomalizedExponent : Int := -6176
def maxDenomalizedExponent : Int := -6144

def rat10 : Rat := Rat.mk' 10 1

def PositiveRational : Type := { x : Rat // x > 0 }
def NonZeroRational : Type := { x : Rat // x ≠ 0 }
