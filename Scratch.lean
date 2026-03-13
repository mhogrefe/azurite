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
