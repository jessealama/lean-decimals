import Std.Data.Rat

structure BigInt where
  isNegative: Bool
  significand: Nat
  exponent: Int
deriving Repr

def ratOne := Rat.mk' 1 1
def ratTen := Rat.mk' 10 1

def ratExp (x : Rat) (n : Nat) : Rat :=
  if n == 0 then ratOne
  else Rat.mul x (ratExp x (n - 1))

def tenToPower (n : Int) : Rat :=
    if n < 0 then Rat.div ratOne
                          (tenToPower (-n))
    else if n == 0 then (Rat.mk' 1 1)
    else Rat.mul ratTen
                 (tenToPower (n - 1))

def MathematicalValue (x: BigInt) : Rat =
  if x.isNegative then
    Rat.mul ratOne MathematicalValue { x with isNegative := False }
  else
    Rat.mul (Rat.mk' x.significand 1)
            (ratExp ratTen x.exponent)
