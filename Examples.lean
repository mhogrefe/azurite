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

#guard toString p1a == "3*x^2+2*x+1"

#guard toString (0 : DensePoly ℤ) == "0"

#guard toString (1 : DensePoly ℤ) == "1"

-- Example with ZMod
def p2 : DensePoly (ZMod 5) := ⟨#[6, 7, 8], by decide⟩

#guard toString p2 == "3*x^2+2*x+1"

-- Example with Rat (ℚ)
def p3 : DensePoly ℚ := ⟨#[1/2, 3/4, 5/8], by norm_num⟩

#guard toString p3 == "5/8*x^2+3/4*x+1/2"

#guard toString (-p2) == "2*x^2+3*x+4"

#guard (zero : DensePoly ℤ).degree == none

#guard (zero : DensePoly ℤ).natDegree == 0

#guard p1a != p1b

#guard toString (C (0: ℤ)) == "0"

#guard toString (C (5: ℤ)) == "5"

#guard toString (X : DensePoly ℤ) == "x"

#guard toString (monomial 10 (5: ℤ)) == "5*x^10"

#guard toString (p1a.erase 1) == "3*x^2+1"
#guard toString (p1a.erase 2) == "2*x+1"
#guard toString ((C 5).erase 0) == "0"

#guard p1a.leadingCoeff = 3

#guard !p1a.Monic

-- 1. Lifting a DensePoly N to DensePoly Z using mapNatToInt
def pN : DensePoly ℕ := ⟨#[1, 2, 3], by decide⟩
#guard toString (Azurite.DensePoly.mapNatToInt pN) == "3*x^2+2*x+1"

-- 2. Lifting a DensePoly Z to DensePoly Q using mapIntToRat
def pZ : DensePoly ℤ := ⟨#[1, -2, 3], by decide⟩
#guard toString (Azurite.DensePoly.mapIntToRat pZ) == "3*x^2-2*x+1"

-- 3. Mapping a DensePoly (ZMod 5) to DensePoly N using mapZModToNat
def pZMod5 : DensePoly (ZMod 5) := ⟨#[1, 2, 3, 4], by decide⟩
#guard toString (Azurite.DensePoly.mapZModToNat pZMod5) == "4*x^3+3*x^2+2*x+1"

-- 4. Lifting a DensePoly (ZMod 5) to a DensePoly (ZMod 10) using mapZeroInjective
-- (Note: ZMod 5 → ZMod 10 is not a ring homomorphism, so we use mapZeroInjective directly!)
def f5_10 (x : ZMod 5) : ZMod 10 := x.val * 2
lemma f5_10_inj (r : ZMod 5) : f5_10 r = 0 ↔ r = 0 := by
  revert r
  decide
#guard toString (Azurite.DensePoly.mapZeroInjective f5_10 f5_10_inj pZMod5) == "8*x^3+6*x^2+4*x+2"

-- 5. Mapping a DensePoly N to a DensePoly (ZMod 5) using mapNatToZMod
def pN_large : DensePoly ℕ := ⟨#[1, 2, 3, 5], by decide⟩
#guard toString (Azurite.DensePoly.mapNatToZMod (n := 5) pN_large) == "3*x^2+2*x+1"

-- 6. Mapping a DensePoly Z to a DensePoly (ZMod 5) using mapIntToZMod
def pZ_large : DensePoly ℤ := ⟨#[1, -2, 3, 10], by decide⟩
#guard toString (Azurite.DensePoly.mapIntToZMod (n := 5) pZ_large) == "3*x^2+3*x+1"

-- The polynomial ends in 5, which maps to 0 in ZMod 5, so `normalize` strips it.
def pZMod10 : DensePoly (ZMod 10) := ⟨#[1, 2, 3, 5], by decide⟩
#guard toString (Azurite.DensePoly.map (ZMod.castHom (by decide) (ZMod 5)) pZMod10) == "3*x^2+2*x+1"

section ToCharsEval

#guard (String.ofList (monomialToChars 0 (5:ℤ))) == "5"
#guard (String.ofList (monomialToChars 1 (5:ℤ))) == "5*x"
#guard (String.ofList (monomialToChars 2 (5:ℤ))) == "5*x^2"

#guard (String.ofList (monomialToChars 0 (1:ℤ))) == "1"
#guard (String.ofList (monomialToChars 1 (1:ℤ))) == "x"
#guard (String.ofList (monomialToChars 2 (1:ℤ))) == "x^2"

#guard (String.ofList (monomialToChars 0 (-1:ℤ))) == "-1"
#guard (String.ofList (monomialToChars 1 (-1:ℤ))) == "-x"
#guard (String.ofList (monomialToChars 2 (-1:ℤ))) == "-x^2"

#guard (String.ofList (monomialToChars 0 (0:ℤ))) == "0"
#guard (String.ofList (monomialToChars 1 (0:ℤ))) == "0"
#guard (String.ofList (monomialToChars 2 (0:ℤ))) == "0"

end ToCharsEval

section ParseEval

#guard parseMonomial (R := ℤ) "5".toList == some (0, 5)
#guard parseMonomial (R := ℤ) "5*x".toList == some (1, 5)
#guard parseMonomial (R := ℤ) "5*x^2".toList == some (2, 5)

#guard parseMonomial (R := ℤ) "1".toList == some (0, 1)
#guard parseMonomial (R := ℤ) "x".toList == some (1, 1)
#guard parseMonomial (R := ℤ) "x^2".toList == some (2, 1)

#guard parseMonomial (R := ℤ) "-1".toList == some (0, -1)
#guard parseMonomial (R := ℤ) "-x".toList == some (1, -1)
#guard parseMonomial (R := ℤ) "-x^2".toList == some (2, -1)

#guard parseMonomial (R := ℤ) "0".toList == some (0, 0)

#guard parseMonomial (R := ℚ) "22/7".toList == some (0, 22/7)
#guard parseMonomial (R := ℚ) "22/7*x".toList == some (1, 22/7)
#guard parseMonomial (R := ℚ) "22/7*x^2".toList == some (2, 22/7)

#guard parseMonomial (R := ℚ) "1".toList == some (0, 1)
#guard parseMonomial (R := ℚ) "x".toList == some (1, 1)
#guard parseMonomial (R := ℚ) "x^2".toList == some (2, 1)

#guard parseMonomial (R := ℚ) "-1".toList == some (0, -1)
#guard parseMonomial (R := ℚ) "-x".toList == some (1, -1)
#guard parseMonomial (R := ℚ) "-x^2".toList == some (2, -1)

#guard parseMonomial (R := ℚ) "0".toList == some (0, 0)

end ParseEval

#guard toString (0 : DensePoly ℤ) == "0"
#guard toString (monomial 2 (5:ℤ)) == "5*x^2"
#guard toString p1a == "3*x^2+2*x+1"

#guard (parseDensePoly (R := ℤ) "3*x^4-x^2+1").map (·.coeffs) == some #[1, 0, -1, 0, 3]
#guard (parseDensePoly (R := ℤ) "-x^2+1").map (·.coeffs) == some #[1, 0, -1]
#guard (parseDensePoly (R := ℚ) "-2/3*x^2-1/2").map (·.coeffs) == some #[-1/2, 0, -2/3]
#guard (parseDensePoly (R := ℤ) "-2/3*x^2-1/2") == none
#guard (parseDensePoly (R := (ZMod 5)) "3*x^2-1").map (·.coeffs) == some #[4, 0, 3]
