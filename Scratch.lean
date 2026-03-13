import Azurite
import Mathlib.Data.Int.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.NormNum
import Lean
import Azurite.DensePoly.Monomial

open Lean
open Azurite
open Azurite.DensePoly

-- Create a concrete `DensePoly` directly: 1 + 2x + 3x^2
def p1a : DensePoly ℤ := ⟨#[1, 2, 3], by decide⟩

def p1b : DensePoly ℤ := ⟨#[10, 11, 12], by decide⟩

#eval p1a

#eval (0 : DensePoly ℤ)

#eval (1 : DensePoly ℤ)

-- Example with ZMod
def p2 : DensePoly (ZMod 5) := ⟨#[6, 7, 8], by decide⟩

#eval p2

-- Example with Rat (ℚ)
def p3 : DensePoly ℚ := ⟨#[1/2, 3/4, 5/8], by norm_num⟩

#eval p3

#eval -p2

#eval (zero : DensePoly ℤ).degree

#eval (zero : DensePoly ℤ).natDegree

#eval p1a = p1b

#eval C (0: ℤ)

#eval C (5: ℤ)

#eval (X : DensePoly ℤ)
