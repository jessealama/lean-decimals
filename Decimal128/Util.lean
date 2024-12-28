import Mathlib

def scale10Nat (n : Nat) : Nat :=
  10 ^ n

def scale10 (q : Int) : Rat :=
  match q with
  | Int.ofNat n => mkRat (scale10Nat n) 1
  | Int.negSucc n => mkRat (scale10Nat n) 1
