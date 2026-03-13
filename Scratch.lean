import Azurite
import Mathlib.Data.Int.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.NormNum
import Lean
import Azurite.DensePoly.Basic
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

#eval monomial 10 (5: ℤ)

#eval p1a.erase 1
#eval p1a.erase 2
#eval (C 5).erase 0

#eval p1a.leadingCoeff

#eval p1a.Monic

-- 1. Lifting a DensePoly Z to DensePoly Q using mapAlgebraMap
def pZ : DensePoly ℤ := ⟨#[1, -2, 3], by decide⟩
#eval Azurite.DensePoly.mapAlgebraMap (S := ℚ) (by intro x y h; exact Int.cast_inj.mp h) pZ

-- 2. Lifting a DensePoly (ZMod 5) to a DensePoly (ZMod 10) using mapZeroInjective
-- (Note: ZMod 5 → ZMod 10 is not a ring homomorphism, so we use mapZeroInjective directly!)
def f5_10 (x : ZMod 5) : ZMod 10 := x.val * 2
lemma f5_10_inj (r : ZMod 5) : f5_10 r = 0 ↔ r = 0 := by
  revert r
  decide
def pZMod5 : DensePoly (ZMod 5) := ⟨#[1, 2, 3, 4], by decide⟩
#eval Azurite.DensePoly.mapZeroInjective f5_10 f5_10_inj pZMod5

-- 3. Mapping a DensePoly (ZMod 10) to a DensePoly (ZMod 5) using map
-- The polynomial ends in 5, which maps to 0 in ZMod 5, so `normalize` strips it.
def pZMod10 : DensePoly (ZMod 10) := ⟨#[1, 2, 3, 5], by decide⟩
#eval Azurite.DensePoly.map (ZMod.castHom (by decide) (ZMod 5)) pZMod10
