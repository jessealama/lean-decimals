import Mathlib

def scale10 (q : Int) : Rat :=
  match q with
  | Int.ofNat n => mkRat (10 ^ n) 1
  | Int.negSucc n => mkRat (10 ^ n) 1
