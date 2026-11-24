/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzPolynomial.FastMul
import Azurite.AzPolynomial.Equiv.Monomial
import Azurite.AzPolynomial.Equiv.Sub
import Azurite.AzPolynomial.Basic
import Azurite.AzPolynomial.Add
import Azurite.AzPolynomial.Sub
import Azurite.AzPolynomial.Mul
import Azurite.AzPolynomial.Monomial
import Azurite.AzPolynomial.Parse

import Mathlib.Algebra.Ring.Defs

/-!
# Division by a Monic Polynomial over an arbitrary `CommRing`

This module implements Euclidean division of a polynomial `P` by a **monic**
polynomial `f`, over any commutative ring `R` — **no field / inverse required**.

Because `f` is monic, subtracting `c • X^k * f` (where `c` is the leading
coefficient of the running remainder and `k` is the degree gap) cancels the
remainder's leading term exactly, without ever dividing a coefficient.  This is
the polynomial analogue of `AzNat.mod` used to build `AzZMod`, and it is the
reduction primitive underlying `AzPolyMod` (`R[x] / (f)`).

## Algorithm (`divModByMonicAux`)

Starting from `rem := P`, `quo := 0`, while `deg rem ≥ deg f` (and `rem ≠ 0`):
- `c := leadingCoeff rem`, `k := natDegree rem − natDegree f`;
- `rem := rem − c • (X^k * f)` (cancels the leading term since `f` is monic);
- `quo := quo + c • X^k`.

Termination is by an explicit fuel counter (`P.coeffs.size + 1` steps suffice for
monic `f`, since each step drops the degree by at least one).  On the fuel-out
branch the remainder is reset to `0` so that the returned remainder **always**
satisfies `deg < deg f` (`divModByMonicAux_rem_size`) for any `f`, monic or not —
this is what makes the `AzPolyMod` reduced invariant provable without a monic
hypothesis.  For monic `f` the fuel-out branch is never reached, so the result is
the genuine quotient/remainder pair.

Phase-2 correctness (`P = divByMonic P f * f + modByMonic P f` and monic-ness
assumptions) will mirror the `QuoRem` / `ExactDiv` equivalence proofs.
-/

namespace Azurite.AzPolynomial

variable {R : Type _} [CommRing R] [DecidableEq R]

/-- Fuel-driven core of division by a monic polynomial.

Returns `(quotient-so-far-contribution, remainder)`.  `rem` is the running
remainder; each recursive step shaves its leading term using the monic divisor
`f`.  The fuel-out branch (`0, rem` with `deg rem ≥ deg f`) resets the remainder
to `0`, guaranteeing `deg (result.2) < deg f` unconditionally (see
`divModByMonicAux_rem_size`). -/
def divModByMonicAux (f : AzPolynomial R) : ℕ → AzPolynomial R → AzPolynomial R × AzPolynomial R
  | 0, rem => (0, if rem.coeffs.size < f.coeffs.size then rem else 0)
  | fuel + 1, rem =>
    if rem.coeffs.size < f.coeffs.size then (0, rem)
    else
      let k := rem.natDegree - f.natDegree
      let c := rem.leadingCoeff
      let m := monomial k c          -- `c * X^k`
      let rem' := rem - mulBasecaseFold m f   -- subtract `c * X^k * f`
      let res := divModByMonicAux f fuel rem'
      (m + res.1, res.2)

/-- **Division by a monic polynomial.** Returns `(quotient, remainder)` with
`P = quotient * f + remainder` and `deg remainder < deg f` when `f` is monic. -/
def divModByMonic (P f : AzPolynomial R) : AzPolynomial R × AzPolynomial R :=
  divModByMonicAux f (P.coeffs.size + 1) P

/-- The remainder of `P` modulo the monic polynomial `f`. -/
def modByMonic (P f : AzPolynomial R) : AzPolynomial R := (divModByMonic P f).2

/-- The quotient of `P` divided by the monic polynomial `f`. -/
def divByMonic (P f : AzPolynomial R) : AzPolynomial R := (divModByMonic P f).1

/-! ### The remainder in place

`divModByMonicAux` builds, at every step, the polynomial `c · Xᵏ · f` and a new remainder.
`modByMonicFast` runs the same steps on the coefficient array of the remainder (one pass
`b[k + i] -= c · f[i]`, then the trailing zeros are dropped) and builds no quotient.  It is
equal to `modByMonic` for every `f`, monic or not (`modByMonic_eq_modByMonicFast`), and the
compiler uses it in place of `modByMonic` (`@[csimp]`), so that the theory keeps talking about
`modByMonic`. -/

/-- `b[k + i'] -= c · f[i']` for `i ≤ i' < i + n`. -/
def subScaledLoop (f : Array R) (c : R) (k : ℕ) : ℕ → ℕ → Array R → Array R
  | 0, _, b => b
  | n + 1, i, b =>
    subScaledLoop f c k n (i + 1) (b.modify (k + i) (· - c * (f[i]?).getD 0))

omit [DecidableEq R] in
theorem subScaledLoop_getElem? (f : Array R) (c : R) (k : ℕ) :
    ∀ (n i : ℕ) (b : Array R) (j : ℕ),
      ((subScaledLoop f c k n i b)[j]?).getD 0 =
        if k + i ≤ j ∧ j < k + i + n ∧ j < b.size then
          (b[j]?).getD 0 - c * (f[j - k]?).getD 0
        else (b[j]?).getD 0 := by
  intro n
  induction n with
  | zero =>
    intro i b j
    have : ¬(k + i ≤ j ∧ j < k + i + 0 ∧ j < b.size) := by omega
    simp only [subScaledLoop, this, ↓reduceIte]
  | succ n ih =>
    intro i b j
    rw [subScaledLoop, ih, Array.size_modify, Array.getElem?_modify]
    by_cases hj : k + i = j
    · subst hj
      have h1 : ¬(k + (i + 1) ≤ k + i ∧ k + i < k + (i + 1) + n ∧ k + i < b.size) := by omega
      simp only [h1, ↓reduceIte]
      by_cases hb : k + i < b.size
      · have h2 : k + i ≤ k + i ∧ k + i < k + i + (n + 1) ∧ k + i < b.size := by omega
        have hbs : b[k + i]? = some b[k + i] := Array.getElem?_eq_getElem hb
        simp only [h2, and_self, ↓reduceIte, hbs, Option.map_some, Option.getD_some,
          Nat.add_sub_cancel_left]
      · have h2 : ¬(k + i ≤ k + i ∧ k + i < k + i + (n + 1) ∧ k + i < b.size) := by omega
        have hbn : b[k + i]? = none := Array.getElem?_eq_none (by omega)
        simp only [h2, ↓reduceIte, hbn, Option.map_none]
    · have h1 : (k + (i + 1) ≤ j ∧ j < k + (i + 1) + n ∧ j < b.size) ↔
          (k + i ≤ j ∧ j < k + i + (n + 1) ∧ j < b.size) := by omega
      simp only [hj, ↓reduceIte, h1]

/-- One step of the division, in place. -/
theorem normalize_subScaledLoop (f rem : AzPolynomial R) (c : R)
    (h : f.coeffs.size ≤ rem.coeffs.size) :
    normalize (subScaledLoop f.coeffs c (rem.natDegree - f.natDegree) f.coeffs.size 0
        rem.coeffs) =
      rem - mulBasecaseFold (monomial (rem.natDegree - f.natDegree) c) f := by
  apply toPoly_inj.mp
  ext j
  rw [coeff_toPoly_eq, coeff_normalize, subScaledLoop_getElem?, toPoly_sub,
    toPoly_mulBasecaseFold, toPoly_monomial, Polynomial.coeff_sub,
    ← Polynomial.C_mul_X_pow_eq_monomial, mul_assoc, Polynomial.coeff_C_mul,
    Polynomial.coeff_X_pow_mul', coeff_toPoly_eq, coeff_toPoly_eq]
  unfold natDegree coeff
  by_cases hk : rem.coeffs.size - 1 - (f.coeffs.size - 1) ≤ j
  · by_cases hin : j < rem.coeffs.size - 1 - (f.coeffs.size - 1) + 0 + f.coeffs.size ∧
        j < rem.coeffs.size
    · have hc : rem.coeffs.size - 1 - (f.coeffs.size - 1) + 0 ≤ j ∧
          j < rem.coeffs.size - 1 - (f.coeffs.size - 1) + 0 + f.coeffs.size ∧
          j < rem.coeffs.size := ⟨by omega, hin.1, hin.2⟩
      simp only [hc, and_self, ↓reduceIte, hk]
    · have hc : ¬(rem.coeffs.size - 1 - (f.coeffs.size - 1) + 0 ≤ j ∧
          j < rem.coeffs.size - 1 - (f.coeffs.size - 1) + 0 + f.coeffs.size ∧
          j < rem.coeffs.size) := fun hc => hin ⟨hc.2.1, hc.2.2⟩
      have hfn : f.coeffs[j - (rem.coeffs.size - 1 - (f.coeffs.size - 1))]? = none :=
        Array.getElem?_eq_none (by omega)
      simp only [hc, ↓reduceIte, hk, hfn, Option.getD_none, mul_zero, sub_zero]
  · have hc : ¬(rem.coeffs.size - 1 - (f.coeffs.size - 1) + 0 ≤ j ∧
        j < rem.coeffs.size - 1 - (f.coeffs.size - 1) + 0 + f.coeffs.size ∧
        j < rem.coeffs.size) := fun hc => hk (by omega)
    simp only [hc, ↓reduceIte, hk, mul_zero, sub_zero]

/-- The remainder of the division by a monic polynomial, computed in place; the fuel-driven
core.  Equal to the second component of `divModByMonicAux` (`modByMonicAuxFast_eq`). -/
def modByMonicAuxFast (f : AzPolynomial R) : ℕ → AzPolynomial R → AzPolynomial R
  | 0, rem => if rem.coeffs.size < f.coeffs.size then rem else 0
  | fuel + 1, rem =>
    if rem.coeffs.size < f.coeffs.size then rem
    else
      let k := rem.natDegree - f.natDegree
      let c := rem.leadingCoeff
      modByMonicAuxFast f fuel
        (normalize (subScaledLoop f.coeffs c k f.coeffs.size 0 rem.coeffs))

theorem modByMonicAuxFast_eq (f : AzPolynomial R) :
    ∀ (fuel : ℕ) (rem : AzPolynomial R),
      modByMonicAuxFast f fuel rem = (divModByMonicAux f fuel rem).2 := by
  intro fuel
  induction fuel with
  | zero => intro rem; rfl
  | succ n ih =>
    intro rem
    rw [modByMonicAuxFast, divModByMonicAux]
    split
    · rfl
    · next hlt =>
      simp only []
      rw [normalize_subScaledLoop f rem _ (by omega), ih]

/-- **The remainder modulo a monic polynomial, in place.**  What `modByMonic` compiles to. -/
def modByMonicFast (P f : AzPolynomial R) : AzPolynomial R :=
  modByMonicAuxFast f (P.coeffs.size + 1) P

@[csimp] theorem modByMonic_eq_modByMonicFast : @modByMonic = @modByMonicFast := by
  funext R _ _ P f
  exact (modByMonicAuxFast_eq f _ P).symm

/-- The remainder produced by `divModByMonicAux` always has size (hence degree)
strictly below `f`, for **any** `f` with `0 < f.coeffs.size`.  This is the
`AzPolyMod` reduced-invariant lemma; it needs no monic hypothesis because the
fuel-out branch resets the remainder to `0`. -/
theorem divModByMonicAux_rem_size (f : AzPolynomial R) (hf : 0 < f.coeffs.size) :
    ∀ (fuel : ℕ) (rem : AzPolynomial R),
      (divModByMonicAux f fuel rem).2.coeffs.size < f.coeffs.size := by
  intro fuel
  induction fuel with
  | zero =>
    intro rem
    simp only [divModByMonicAux]
    split
    · assumption
    · simpa using hf
  | succ n ih =>
    intro rem
    simp only [divModByMonicAux]
    split
    · assumption
    · exact ih _

/-- The remainder `modByMonic P f` has size (hence degree) strictly below `f`
whenever `f` is nonzero. -/
theorem modByMonic_coeffs_size_lt (P f : AzPolynomial R) (hf : 0 < f.coeffs.size) :
    (modByMonic P f).coeffs.size < f.coeffs.size :=
  divModByMonicAux_rem_size f hf _ P

end Azurite.AzPolynomial

-- ── Tests ────────────────────────────────────────────────────────────────────

section Tests

open Azurite Azurite.AzPolynomial

/-- Divide `P` by monic `f` and render `(quotient, remainder)` as strings. -/
private def divModStr (P f : String) : String × String :=
  let p := (parseAzPolynomial (R := AzInt) P).get!
  let g := (parseAzPolynomial (R := AzInt) f).get!
  let (q, r) := divModByMonic p g
  (toChars q, toChars r)

-- (x^2 + 2x + 1) / (x + 1) = (x + 1, 0)
#guard divModStr "x^2+2*x+1" "x+1" == ("x+1", "0")
-- (x^2 + 1) / (x + 1) = (x - 1, 2)
#guard divModStr "x^2+1" "x+1" == ("x-1", "2")
-- (x^3 - 2x + 1) / (x^2 + 1) = (x, -3x + 1)
#guard divModStr "x^3-2*x+1" "x^2+1" == ("x", "-3*x+1")
-- (x^3) / (x^2 - x - 1) = (x + 1, 2x + 1)   [Fibonacci-style monic]
#guard divModStr "x^3" "x^3-x-1" == ("1", "x+1")
-- deg P < deg f: (x + 1) / (x^2 + 1) = (0, x + 1)
#guard divModStr "x+1" "x^2+1" == ("0", "x+1")
-- P = 0
#guard divModStr "0" "x^2+1" == ("0", "0")

-- Reconstruction  P = q * f + r  (integer coefficients, monic divisor).
private def reconstructs (P f : String) : Bool :=
  let p := (parseAzPolynomial (R := AzInt) P).get!
  let g := (parseAzPolynomial (R := AzInt) f).get!
  let (q, r) := divModByMonic p g
  toChars (q * g + r) == toChars p

#guard reconstructs "x^4+3*x^2+7" "x^2+1"
#guard reconstructs "5*x^5-4*x^3+2*x-9" "x^3-x-1"
#guard reconstructs "x^2+2*x+1" "x+1"
#guard reconstructs "7" "x^2+1"

-- The in-place remainder against the second component of `divModByMonic` (which the compiler
-- does not replace), for monic, non-monic and zero divisors.
private def fastAgrees (P f : String) : Bool :=
  let p := (parseAzPolynomial (R := AzInt) P).get!
  let g := (parseAzPolynomial (R := AzInt) f).get!
  modByMonicFast p g == (divModByMonic p g).2

#guard fastAgrees "x^4+3*x^2+7" "x^2+1"
#guard fastAgrees "5*x^5-4*x^3+2*x-9" "x^3-x-1"
#guard fastAgrees "x^9-x^8+5*x^3-2" "x^4+7*x^3-x+3"
#guard fastAgrees "x^2+2*x+1" "x+1"
#guard fastAgrees "7" "x^2+1"
#guard fastAgrees "0" "x^2+1"
#guard fastAgrees "x^5+x+1" "1"
#guard fastAgrees "x^5+x+1" "2*x^2+1"
#guard fastAgrees "4*x^5+x+1" "2*x^2-x"
#guard fastAgrees "x^5+x+1" "3"
#guard fastAgrees "x^5+x+1" "0"

end Tests
