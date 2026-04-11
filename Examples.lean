import Azurite
import Mathlib.Data.Int.Basic
import Lean
import Azurite.AzPolynomial.Basic
import Azurite.AzPolynomial.Monomial
import Azurite.AzPolynomial.Cast
import Azurite.AzPolynomial.ToString
import Azurite.AzPolynomial.Parse
import Azurite.AzPolynomial.StringLemmas
import Azurite.AzPolynomialQ.Parse

open Lean
open Azurite
open Azurite.AzPolynomial

instance : Fact (1 < 10) := ⟨by decide⟩

-- Create a concrete `AzPolynomial` directly: 1 + 2x + 3x^2
def p1a : AzPolynomial ℤ := ⟨#[1, 2, 3], by decide⟩

def p1b : AzPolynomial ℤ := ⟨#[10, 11, 12], by decide⟩

#guard toString p1a == "3*x^2+2*x+1"

#guard toString (0 : AzPolynomial ℤ) == "0"

#guard toString (1 : AzPolynomial ℤ) == "1"

-- Example with ZMod
def p2 : AzPolynomial (ZMod 5) := ⟨#[6, 7, 8], by decide⟩

#guard toString p2 == "3*x^2+2*x+1"

-- Example with Rat (ℚ)
def p3 : AzPolynomial ℚ := ⟨#[1/2, 3/4, 5/8], by norm_num⟩

#guard toString p3 == "5/8*x^2+3/4*x+1/2"

#guard toString (-p2) == "2*x^2+3*x+4"

#guard (zero : AzPolynomial ℤ).degree == none

#guard (zero : AzPolynomial ℤ).natDegree == 0

#guard p1a != p1b

#guard toString (C (0: ℤ)) == "0"

#guard toString (C (5: ℤ)) == "5"

#guard toString (X : AzPolynomial ℤ) == "x"

#guard toString (monomial 10 (5: ℤ)) == "5*x^10"

#guard toString (p1a.erase 1) == "3*x^2+1"
#guard toString (p1a.erase 2) == "2*x+1"
#guard toString ((C 5).erase 0) == "0"

#guard p1a.leadingCoeff = 3

#guard !p1a.Monic

-- 1. Lifting a AzPolynomial N to AzPolynomial Z using mapNatToInt
def pN : AzPolynomial ℕ := ⟨#[1, 2, 3], by decide⟩
#guard toString (Azurite.AzPolynomial.mapNatToInt pN) == "3*x^2+2*x+1"

-- 2. Lifting a AzPolynomial Z to AzPolynomial Q using mapIntToRat
def pZ : AzPolynomial ℤ := ⟨#[1, -2, 3], by decide⟩
#guard toString (Azurite.AzPolynomial.mapIntToRat pZ) == "3*x^2-2*x+1"

-- 3. Mapping a AzPolynomial (ZMod 5) to AzPolynomial N using mapZModToNat
def pZMod5 : AzPolynomial (ZMod 5) := ⟨#[1, 2, 3, 4], by decide⟩
#guard toString (Azurite.AzPolynomial.mapZModToNat pZMod5) == "4*x^3+3*x^2+2*x+1"

-- 4. Lifting a AzPolynomial (ZMod 5) to a AzPolynomial (ZMod 10) using mapZeroInjective
-- (Note: ZMod 5 → ZMod 10 is not a ring homomorphism, so we use mapZeroInjective directly!)
def f5_10 (x : ZMod 5) : ZMod 10 := x.val * 2
lemma f5_10_inj (r : ZMod 5) : f5_10 r = 0 ↔ r = 0 := by
  revert r
  decide
#guard toString (Azurite.AzPolynomial.mapZeroInjective f5_10 f5_10_inj pZMod5) == "8*x^3+6*x^2+4*x+2"

-- 5. Mapping a AzPolynomial N to a AzPolynomial (ZMod 5) using mapNatToZMod
def pN_large : AzPolynomial ℕ := ⟨#[1, 2, 3, 5], by decide⟩
#guard toString (Azurite.AzPolynomial.mapNatToZMod (n := 5) pN_large) == "3*x^2+2*x+1"

-- 6. Mapping a AzPolynomial Z to a AzPolynomial (ZMod 5) using mapIntToZMod
def pZ_large : AzPolynomial ℤ := ⟨#[1, -2, 3, 10], by decide⟩
#guard toString (Azurite.AzPolynomial.mapIntToZMod (n := 5) pZ_large) == "3*x^2+3*x+1"

-- The polynomial ends in 5, which maps to 0 in ZMod 5, so `normalize` strips it.
def pZMod10 : AzPolynomial (ZMod 10) := ⟨#[1, 2, 3, 5], by decide⟩
#guard toString (Azurite.AzPolynomial.map (ZMod.castHom (by decide) (ZMod 5)) pZMod10) == "3*x^2+2*x+1"

#guard toString (0 : AzPolynomial ℤ) == "0"
#guard toString (monomial 2 (5:ℤ)) == "5*x^2"
#guard toString p1a == "3*x^2+2*x+1"

#guard (parseAzPolynomial (R := ℤ) "3*x^4-x^2+1").map (·.coeffs) == some #[1, 0, -1, 0, 3]
#guard (parseAzPolynomial (R := ℤ) "-x^2+1").map (·.coeffs) == some #[1, 0, -1]
#guard (parseAzPolynomial (R := ℚ) "-2/3*x^2-1/2").map (·.coeffs) == some #[-1/2, 0, -2/3]
#guard (parseAzPolynomial (R := ℤ) "-2/3*x^2-1/2") == none
#guard (parseAzPolynomial (R := (ZMod 5)) "3*x^2-1").map (·.coeffs) == some #[4, 0, 3]

open Azurite.AzPolynomialQ in
#guard (parseAzPolynomialQ "3*x^2+2*x+1").map (·.numerators) == some #[1, 2, 3]
open Azurite.AzPolynomialQ in
#guard (parseAzPolynomialQ "3*x^2+2*x+1").map (·.denom) == some 1
open Azurite.AzPolynomialQ in
#guard (parseAzPolynomialQ "-2/3*x^2-1/2").map (·.numerators) == some #[-3, 0, -4]
open Azurite.AzPolynomialQ in
#guard (parseAzPolynomialQ "-2/3*x^2-1/2").map (·.denom) == some 6
open Azurite.AzPolynomialQ in
#guard (parseAzPolynomialQ "0").map (·.numerators) == some #[]
