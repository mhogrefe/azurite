import Azurite
import Mathlib.Data.Int.Basic
import Lean
import Azurite.DensePoly.Basic
import Azurite.DensePoly.Monomial
import Azurite.DensePoly.Cast
import Azurite.DensePoly.ToString
import Azurite.DensePoly.String

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

-- 1. Lifting a DensePoly N to DensePoly Z using mapNatToInt
def pN : DensePoly ℕ := ⟨#[1, 2, 3], by decide⟩
#eval Azurite.DensePoly.mapNatToInt pN

-- 2. Lifting a DensePoly Z to DensePoly Q using mapIntToRat
def pZ : DensePoly ℤ := ⟨#[1, -2, 3], by decide⟩
#eval Azurite.DensePoly.mapIntToRat pZ

-- 3. Mapping a DensePoly (ZMod 5) to DensePoly N using mapZModToNat
def pZMod5 : DensePoly (ZMod 5) := ⟨#[1, 2, 3, 4], by decide⟩
#eval Azurite.DensePoly.mapZModToNat pZMod5

-- 4. Lifting a DensePoly (ZMod 5) to a DensePoly (ZMod 10) using mapZeroInjective
-- (Note: ZMod 5 → ZMod 10 is not a ring homomorphism, so we use mapZeroInjective directly!)
def f5_10 (x : ZMod 5) : ZMod 10 := x.val * 2
lemma f5_10_inj (r : ZMod 5) : f5_10 r = 0 ↔ r = 0 := by
  revert r
  decide
#eval Azurite.DensePoly.mapZeroInjective f5_10 f5_10_inj pZMod5

-- 5. Mapping a DensePoly N to a DensePoly (ZMod 5) using mapNatToZMod
def pN_large : DensePoly ℕ := ⟨#[1, 2, 3, 5], by decide⟩
#eval Azurite.DensePoly.mapNatToZMod (n := 5) pN_large

-- 6. Mapping a DensePoly Z to a DensePoly (ZMod 5) using mapIntToZMod
def pZ_large : DensePoly ℤ := ⟨#[1, -2, 3, 10], by decide⟩
#eval Azurite.DensePoly.mapIntToZMod (n := 5) pZ_large

-- The polynomial ends in 5, which maps to 0 in ZMod 5, so `normalize` strips it.
def pZMod10 : DensePoly (ZMod 10) := ⟨#[1, 2, 3, 5], by decide⟩
#eval Azurite.DensePoly.map (ZMod.castHom (by decide) (ZMod 5)) pZMod10

section ToCharsEval

#eval (String.ofList (monomialToChars 0 (5:ℤ)))
#eval (String.ofList (monomialToChars 1 (5:ℤ)))
#eval (String.ofList (monomialToChars 2 (5:ℤ)))

#eval (String.ofList (monomialToChars 0 (1:ℤ)))
#eval (String.ofList (monomialToChars 1 (1:ℤ)))
#eval (String.ofList (monomialToChars 2 (1:ℤ)))

#eval (String.ofList (monomialToChars 0 (-1:ℤ)))
#eval (String.ofList (monomialToChars 1 (-1:ℤ)))
#eval (String.ofList (monomialToChars 2 (-1:ℤ)))

#eval (String.ofList (monomialToChars 0 (0:ℤ)))
#eval (String.ofList (monomialToChars 1 (0:ℤ)))
#eval (String.ofList (monomialToChars 2 (0:ℤ)))

end ToCharsEval

section ParseEval

#eval parseMonomial (R := ℤ) "5".toList
#eval parseMonomial (R := ℤ) "5*x".toList
#eval parseMonomial (R := ℤ) "5*x^2".toList

#eval parseMonomial (R := ℤ) "1".toList
#eval parseMonomial (R := ℤ) "x".toList
#eval parseMonomial (R := ℤ) "x^2".toList

#eval parseMonomial (R := ℤ) "-1".toList
#eval parseMonomial (R := ℤ) "-x".toList
#eval parseMonomial (R := ℤ) "-x^2".toList

#eval parseMonomial (R := ℤ) "0".toList

#eval parseMonomial (R := ℚ) "22/7".toList
#eval parseMonomial (R := ℚ) "22/7*x".toList
#eval parseMonomial (R := ℚ) "22/7*x^2".toList

#eval parseMonomial (R := ℚ) "1".toList
#eval parseMonomial (R := ℚ) "x".toList
#eval parseMonomial (R := ℚ) "x^2".toList

#eval parseMonomial (R := ℚ) "-1".toList
#eval parseMonomial (R := ℚ) "-x".toList
#eval parseMonomial (R := ℚ) "-x^2".toList

#eval parseMonomial (R := ℚ) "0".toList

end ParseEval

#eval toString (0 : DensePoly ℤ)
#eval toString (monomial 2 (5:ℤ))
#eval toString p1a

#eval parseDensePoly (R := ℤ) "3*x^4-x^2+1"
#eval parseDensePoly (R := ℤ) "-x^2+1"
#eval parseDensePoly (R := ℚ) "-2/3*x^2-1/2"
#eval parseDensePoly (R := ℤ) "-2/3*x^2-1/2"
#eval parseDensePoly (R := (ZMod 5)) "3*x^2-1"
#eval parseDensePoly (R := (ZMod 5)) "3*x^2+x^2-1"
