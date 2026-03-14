import Mathlib.Data.Rat.Defs
import Azurite.Nat.Compare

namespace Azurite.Rat

/-- Returns the floor of the base-2 logarithm of the absolute value of a rational number.
 -/
def floorLogBase2Abs (q : ℚ) : ℤ :=
  let exponent : ℤ := (Nat.size q.num.natAbs : ℤ) - (Nat.size q.den : ℤ)
  if Azurite.Nat.normalizedCompare q.num.natAbs q.den == Ordering.lt then
    exponent - 1
  else
    exponent

#guard floorLogBase2Abs 1 == 0
#guard floorLogBase2Abs 100 == 6
#guard floorLogBase2Abs 1000000000000 == 39
#guard floorLogBase2Abs 4294967295 == 31
#guard floorLogBase2Abs 4294967296 == 32
#guard floorLogBase2Abs 4294967297 == 32
#guard floorLogBase2Abs (22/7) == 1
#guard floorLogBase2Abs (936851431250/1397) == 29
#guard floorLogBase2Abs (1/1000000000000) == -40
#guard floorLogBase2Abs (1/4294967295) == -32
#guard floorLogBase2Abs (1/4294967296) == -32
#guard floorLogBase2Abs (1/4294967297) == -33
#guard floorLogBase2Abs (1/2) == -1
#guard floorLogBase2Abs (1/3) == -2
#guard floorLogBase2Abs (1/4) == -2
#guard floorLogBase2Abs (1/5) == -3
#guard floorLogBase2Abs (1/6) == -3
#guard floorLogBase2Abs (1/7) == -3
#guard floorLogBase2Abs (1/8) == -3
#guard floorLogBase2Abs (1/9) == -4

#guard floorLogBase2Abs (-1) == 0
#guard floorLogBase2Abs (-100) == 6
#guard floorLogBase2Abs (-1000000000000) == 39
#guard floorLogBase2Abs (-4294967295) == 31
#guard floorLogBase2Abs (-4294967296) == 32
#guard floorLogBase2Abs (-4294967297) == 32
#guard floorLogBase2Abs (-22/7) == 1
#guard floorLogBase2Abs (-936851431250/1397) == 29
#guard floorLogBase2Abs (-1/1000000000000) == -40
#guard floorLogBase2Abs (-1/4294967295) == -32
#guard floorLogBase2Abs (-1/4294967296) == -32
#guard floorLogBase2Abs (-1/4294967297) == -33
#guard floorLogBase2Abs (-1/2) == -1
#guard floorLogBase2Abs (-1/3) == -2
#guard floorLogBase2Abs (-1/4) == -2
#guard floorLogBase2Abs (-1/5) == -3
#guard floorLogBase2Abs (-1/6) == -3
#guard floorLogBase2Abs (-1/7) == -3
#guard floorLogBase2Abs (-1/8) == -3
#guard floorLogBase2Abs (-1/9) == -4

/-- Returns the ceiling of the base-2 logarithm of the absolute value of a rational number.
 -/
def ceilingLogBase2Abs (q : ℚ) : ℤ :=
  let exponent : ℤ := (Nat.size q.num.natAbs : ℤ) - (Nat.size q.den : ℤ)
  if Azurite.Nat.normalizedCompare q.num.natAbs q.den == Ordering.gt then
    exponent + 1
  else
    exponent

#guard ceilingLogBase2Abs 1 == 0
#guard ceilingLogBase2Abs 100 == 7
#guard ceilingLogBase2Abs 1000000000000 == 40
#guard ceilingLogBase2Abs 4294967295 == 32
#guard ceilingLogBase2Abs 4294967296 == 32
#guard ceilingLogBase2Abs 4294967297 == 33
#guard ceilingLogBase2Abs (22/7) == 2
#guard ceilingLogBase2Abs (936851431250/1397) == 30
#guard ceilingLogBase2Abs (1/1000000000000) == -39
#guard ceilingLogBase2Abs (1/4294967295) == -31
#guard ceilingLogBase2Abs (1/4294967296) == -32
#guard ceilingLogBase2Abs (1/4294967297) == -32
#guard ceilingLogBase2Abs (1/2) == -1
#guard ceilingLogBase2Abs (1/3) == -1
#guard ceilingLogBase2Abs (1/4) == -2
#guard ceilingLogBase2Abs (1/5) == -2
#guard ceilingLogBase2Abs (1/6) == -2
#guard ceilingLogBase2Abs (1/7) == -2
#guard ceilingLogBase2Abs (1/8) == -3
#guard ceilingLogBase2Abs (1/9) == -3

#guard ceilingLogBase2Abs (-1) == 0
#guard ceilingLogBase2Abs (-100) == 7
#guard ceilingLogBase2Abs (-1000000000000) == 40
#guard ceilingLogBase2Abs (-4294967295) == 32
#guard ceilingLogBase2Abs (-4294967296) == 32
#guard ceilingLogBase2Abs (-4294967297) == 33
#guard ceilingLogBase2Abs (-22/7) == 2
#guard ceilingLogBase2Abs (-936851431250/1397) == 30
#guard ceilingLogBase2Abs (-1/1000000000000) == -39
#guard ceilingLogBase2Abs (-1/4294967295) == -31
#guard ceilingLogBase2Abs (-1/4294967296) == -32
#guard ceilingLogBase2Abs (-1/4294967297) == -32
#guard ceilingLogBase2Abs (-1/2) == -1
#guard ceilingLogBase2Abs (-1/3) == -1
#guard ceilingLogBase2Abs (-1/4) == -2
#guard ceilingLogBase2Abs (-1/5) == -2
#guard ceilingLogBase2Abs (-1/6) == -2
#guard ceilingLogBase2Abs (-1/7) == -2
#guard ceilingLogBase2Abs (-1/8) == -3
#guard ceilingLogBase2Abs (-1/9) == -3

end Azurite.Rat
