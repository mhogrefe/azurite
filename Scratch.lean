import Azurite
import Mathlib
import Lean

open Lean
open Azurite

-- Create a concrete `DensePoly` directly: 1 + 2x + 3x^2
def p1 : DensePoly ℤ := ⟨[1, 2, 3], by decide⟩

#eval p1

#eval (0 : DensePoly ℤ)

#eval (1 : DensePoly ℤ)

-- Example with ZMod
def p2 : DensePoly (ZMod 5) := ⟨[6, 7, 8], by decide⟩

#eval p2

-- Example with Rat (ℚ)
def p3 : DensePoly ℚ := ⟨[1/2, 3/4, 5/8], by norm_num⟩

#eval p3

#eval -p1

#eval p1.natDegree
#eval p1.degree
#eval (0 : DensePoly ℤ).natDegree
#eval (0 : DensePoly ℤ).degree
