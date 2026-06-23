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

/-! `AzPolynomial` over the Az coefficient types (`AzInt`, `AzRat`, `AzZMod`).
The GMP-backed `ℕ`/`ℤ`/`ℚ`/`ZMod` coefficient types are no longer supported as
`ParsableCoeff`/`ParsableElement`; use the Az types instead. -/

-- Create a concrete `AzPolynomial` directly: 1 + 2x + 3x^2
def p1a : AzPolynomial AzInt := ⟨#[1, 2, 3], by native_decide⟩

def p1b : AzPolynomial AzInt := ⟨#[10, 11, 12], by native_decide⟩

#guard toString p1a == "3*x^2+2*x+1"

#guard toString (0 : AzPolynomial AzInt) == "0"

#guard toString (1 : AzPolynomial AzInt) == "1"

-- Example with `AzZMod (ℤ/5)`
def p2 : AzPolynomial (AzZMod (AzNat.ofNat 5)) := ⟨#[6, 7, 8], by native_decide⟩

#guard toString p2 == "3*x^2+2*x+1"

-- Example with `AzRat`
def p3 : AzPolynomial AzRat := ⟨#[1/2, 3/4, 5/8], by native_decide⟩

#guard toString p3 == "5/8*x^2+3/4*x+1/2"

#guard toString (-p2) == "2*x^2+3*x+4"

#guard (zero : AzPolynomial AzInt).degree == none

#guard (zero : AzPolynomial AzInt).natDegree == 0

#guard p1a != p1b

#guard toString (C (0 : AzInt)) == "0"

#guard toString (C (5 : AzInt)) == "5"

#guard toString (X : AzPolynomial AzInt) == "x"

#guard toString (monomial 10 (5 : AzInt)) == "5*x^10"

#guard toString (p1a.erase 1) == "3*x^2+1"
#guard toString (p1a.erase 2) == "2*x+1"
#guard toString ((C (5 : AzInt)).erase 0) == "0"

#guard p1a.leadingCoeff = 3

#guard !p1a.Monic

/-! ## Coefficient-type casts (`AzPolynomial.Cast`)

These convert between the Az coefficient types. -/

-- 1. Lifting an `AzPolynomial AzNat` to `AzPolynomial AzInt` via `mapAzNatToAzInt`.
def pN : AzPolynomial AzNat := ⟨#[1, 2, 3], by native_decide⟩
#guard toString (Azurite.AzPolynomial.mapAzNatToAzInt pN) == "3*x^2+2*x+1"

-- 2. Lifting an `AzPolynomial AzInt` to `AzPolynomial AzRat` via `mapAzIntToAzRat`.
def pZ : AzPolynomial AzInt := ⟨#[1, -2, 3], by native_decide⟩
#guard toString (Azurite.AzPolynomial.mapAzIntToAzRat pZ) == "3*x^2-2*x+1"

-- 3. Mapping an `AzPolynomial (AzZMod 5)` to `AzPolynomial AzNat` via `mapAzZModToAzNat`.
def pZMod5 : AzPolynomial (AzZMod (AzNat.ofNat 5)) := ⟨#[1, 2, 3, 4], by native_decide⟩
#guard toString (Azurite.AzPolynomial.mapAzZModToAzNat pZMod5) == "4*x^3+3*x^2+2*x+1"

-- 4. Mapping an `AzPolynomial AzNat` to `AzPolynomial (AzZMod 5)` via `mapAzNatToAzZMod`.
--    The polynomial ends in 5, which maps to 0 in `AzZMod 5`, so `normalize` strips it.
def pN_large : AzPolynomial AzNat := ⟨#[1, 2, 3, 5], by native_decide⟩
#guard (Azurite.AzPolynomial.mapAzNatToAzZMod (m := AzNat.ofNat 5) pN_large).coeffs == #[1, 2, 3]

-- 5. Mapping an `AzPolynomial AzInt` to `AzPolynomial (AzZMod 5)` via `mapAzIntToAzZMod`.
--    `-2 ↦ 3` and the trailing `10 ↦ 0` is stripped by `normalize`.
def pZ_large : AzPolynomial AzInt := ⟨#[1, -2, 3, 10], by native_decide⟩
#guard (Azurite.AzPolynomial.mapAzIntToAzZMod (m := AzNat.ofNat 5) pZ_large).coeffs == #[1, 3, 3]

/-! ## Parsing (over Az coefficient types) -/

#guard (parseAzPolynomial (R := AzInt) "3*x^4-x^2+1").map (·.coeffs) == some #[1, 0, -1, 0, 3]
#guard (parseAzPolynomial (R := AzInt) "-x^2+1").map (·.coeffs) == some #[1, 0, -1]
#guard (parseAzPolynomial (R := AzRat) "-2/3*x^2-1/2").map (·.coeffs) == some #[-1/2, 0, -2/3]
#guard (parseAzPolynomial (R := AzInt) "-2/3*x^2-1/2") == none

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
