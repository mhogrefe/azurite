/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzPolynomial.InvertRoots
import Azurite.AzPolynomial.Equiv.Add
import Mathlib.Algebra.Polynomial.Reverse

/-!
# Equivalence: AzPolynomial.invertRoots ↔ Polynomial.reverse

Proves that `AzPolynomial.invertRoots p` agrees with Mathlib's
`Polynomial.reverse`, and establishes the root inversion property via Mathlib's
`eval₂_reverse_eq_zero_iff`.

## Main results

- `toPoly_invertRoots` — `toPoly (invertRoots p) = (toPoly p).reverse`
- `ofPoly_invertRoots` — `(ofPoly q).invertRoots = ofPoly q.reverse`
- `eval_invertRoots_field` — `eval z = z^(deg P) · eval z⁻¹ P` for `z ≠ 0`
- `isRoot_invertRoots_iff` — for `z ≠ 0`, root at `z` ↔ root of `P` at `z⁻¹`
- `isRoot_invertRoots_map_iff` — same across a ring homomorphism `f : R →+* K`
- `natDegree_invertRoots`, `leadingCoeff_invertRoots`,
  `invertRoots_invertRoots` — for `P(0) ≠ 0`: degree preserved, leading
  coefficient becomes the constant term, and the operation is an involution
  (over any commutative ring — reversal multiplies no coefficients)
- `invertRoots_eq_zero_iff` — unconditional preservation of nonvanishing
-/

set_option autoImplicit false

open Polynomial

namespace Azurite.AzPolynomial

variable {R : Type _} [CommRing R] [DecidableEq R]

/-- **Structural spec.** `toPoly (invertRoots p) = (toPoly p).reverse`. -/
theorem toPoly_invertRoots (p : AzPolynomial R) :
    AzPolynomial.toPoly p.invertRoots = (AzPolynomial.toPoly p).reverse := by
  ext n
  rw [AzPolynomial.coeff_toPoly, Polynomial.coeff_reverse, AzPolynomial.natDegree_toPoly]
  by_cases hn : n ≤ p.natDegree
  · rw [Polynomial.revAt_le hn, coeff_invertRoots p hn, AzPolynomial.coeff_toPoly]
  · rw [Polynomial.revAt_eq_self_of_lt (by omega), AzPolynomial.coeff_toPoly]
    show (p.invertRoots).coeff n = p.coeff n
    have h1 : (p.invertRoots).coeff n = 0 := by
      rw [invertRoots, coeff_normalize, Array.getElem?_eq_none (by
        rw [Array.size_reverse]
        show p.coeffs.size ≤ n
        have : p.natDegree = p.coeffs.size - 1 := rfl
        rcases Nat.eq_zero_or_pos p.coeffs.size with h | h <;> omega)]
      rfl
    have h2 : p.coeff n = 0 := by
      show (p.coeffs[n]?).getD 0 = 0
      rw [Array.getElem?_eq_none (by
        have : p.natDegree = p.coeffs.size - 1 := rfl
        rcases Nat.eq_zero_or_pos p.coeffs.size with h | h <;> omega)]
      rfl
    rw [h1, h2]

/-- **`ofPoly` version.** -/
theorem ofPoly_invertRoots (q : Polynomial R) :
    (AzPolynomial.ofPoly q).invertRoots = AzPolynomial.ofPoly q.reverse := by
  rw [← toPoly_inj, toPoly_invertRoots, toPoly_ofPoly, toPoly_ofPoly]

/-- **Root inversion across a ring homomorphism.**

    If `f : R →+* K` maps into a field and `z ≠ 0`, then `z` is a root of
    `map f (toPoly (invertRoots p))` iff `z⁻¹` is a root of `map f (toPoly p)`.

    **Application:** if `P ∈ ℤ[X]` is a defining polynomial of a nonzero
    algebraic number `α`, then `invertRoots P` is a defining polynomial of
    `α⁻¹`. -/
theorem isRoot_invertRoots_map_iff {K : Type _} [Field K] [DecidableEq K]
    (f : R →+* K) (p : AzPolynomial R) {z : K} (hz : z ≠ 0) :
    Polynomial.IsRoot (Polynomial.map f (AzPolynomial.toPoly p.invertRoots)) z ↔
    Polynomial.IsRoot (Polynomial.map f (AzPolynomial.toPoly p)) z⁻¹ := by
  have : Invertible z⁻¹ := invertibleOfNonzero (inv_ne_zero hz)
  have hkey := Polynomial.eval₂_reverse_eq_zero_iff f z⁻¹ (AzPolynomial.toPoly p)
  rw [invOf_eq_inv, inv_inv] at hkey
  simp only [Polynomial.IsRoot, toPoly_invertRoots, ← Polynomial.eval₂_eq_eval_map]
  exact hkey

/-- **Root inversion.** For `z ≠ 0`, `z` is a root of `invertRoots p` iff `z⁻¹`
is a root of `P`: the roots of `invertRoots p` are the reciprocals of the
nonzero roots of `p`. -/
theorem isRoot_invertRoots_iff {K : Type _} [Field K] [DecidableEq K]
    (p : AzPolynomial K) {z : K} (hz : z ≠ 0) :
    Polynomial.IsRoot (AzPolynomial.toPoly p.invertRoots) z ↔
    Polynomial.IsRoot (AzPolynomial.toPoly p) z⁻¹ := by
  have h := isRoot_invertRoots_map_iff (RingHom.id K) p hz
  rwa [Polynomial.map_id, Polynomial.map_id] at h

/-- **Field evaluation identity.** For `z ≠ 0`,
`eval z (toPoly (invertRoots p)) = z^(deg P) · eval z⁻¹ (toPoly p)`. -/
theorem eval_invertRoots_field {K : Type _} [Field K] [DecidableEq K]
    (p : AzPolynomial K) {z : K} (hz : z ≠ 0) :
    Polynomial.eval z (AzPolynomial.toPoly p.invertRoots)
      = z ^ p.natDegree * Polynomial.eval z⁻¹ (AzPolynomial.toPoly p) := by
  have : Invertible z⁻¹ := invertibleOfNonzero (inv_ne_zero hz)
  have hkey := Polynomial.eval₂_reverse_mul_pow (RingHom.id K) z⁻¹ (AzPolynomial.toPoly p)
  rw [invOf_eq_inv, inv_inv] at hkey
  simp only [Polynomial.eval₂_id] at hkey
  rw [toPoly_invertRoots, AzPolynomial.natDegree_toPoly] at *
  calc Polynomial.eval z (AzPolynomial.toPoly p).reverse
      = Polynomial.eval z (AzPolynomial.toPoly p).reverse
          * ((z⁻¹) ^ p.natDegree * z ^ p.natDegree) := by
        rw [← mul_pow, inv_mul_cancel₀ hz, one_pow, mul_one]
    _ = z ^ p.natDegree * Polynomial.eval z⁻¹ (AzPolynomial.toPoly p) := by
        rw [← mul_assoc, hkey]; ring

/-! ### Degree data

When the constant term is nonzero (`P(0) ≠ 0` — no roots at `0`), inversion
preserves the degree and is an involution, over any commutative ring: reversal
multiplies no coefficients, so no domain hypothesis is needed. -/

/-- For `P(0) ≠ 0`, root inversion preserves the degree. -/
theorem natDegree_invertRoots (p : AzPolynomial R) (hp0 : p.coeff 0 ≠ 0) :
    (p.invertRoots).natDegree = p.natDegree := by
  have h0 : (AzPolynomial.toPoly p).coeff 0 ≠ 0 := by
    rw [AzPolynomial.coeff_toPoly]; exact hp0
  have htr : (AzPolynomial.toPoly p).natTrailingDegree = 0 := by
    have := Polynomial.natTrailingDegree_le_of_ne_zero h0
    omega
  rw [← AzPolynomial.natDegree_toPoly, toPoly_invertRoots, Polynomial.reverse_natDegree, htr,
    Nat.sub_zero, AzPolynomial.natDegree_toPoly]

/-- For `P(0) ≠ 0`, the leading coefficient of the reversal is the constant
term of `P`. -/
theorem leadingCoeff_invertRoots (p : AzPolynomial R) (hp0 : p.coeff 0 ≠ 0) :
    (p.invertRoots).leadingCoeff = p.coeff 0 := by
  have h0 : (AzPolynomial.toPoly p).coeff 0 ≠ 0 := by
    rw [AzPolynomial.coeff_toPoly]; exact hp0
  have htr : (AzPolynomial.toPoly p).natTrailingDegree = 0 := by
    have := Polynomial.natTrailingDegree_le_of_ne_zero h0
    omega
  rw [← leadingCoeff_toPoly, toPoly_invertRoots, Polynomial.reverse_leadingCoeff,
    Polynomial.trailingCoeff, htr, AzPolynomial.coeff_toPoly]

/-- Root inversion preserves nonvanishing (unconditionally: the reversal's
constant term is the leading coefficient of `P`). -/
theorem invertRoots_eq_zero_iff (p : AzPolynomial R) : p.invertRoots = 0 ↔ p = 0 := by
  constructor
  · intro h
    have hc := coeff_invertRoots_zero p
    rw [h, show (0 : AzPolynomial R).coeff 0 = 0 from rfl] at hc
    have : AzPolynomial.toPoly p = 0 := by
      rw [← Polynomial.leadingCoeff_eq_zero, leadingCoeff_toPoly, ← hc]
    exact toPoly_inj.mp (by rw [this, toPoly_zero])
  · rintro rfl
    exact invertRoots_zero

/-- For `P(0) ≠ 0`, root inversion is an involution. -/
theorem invertRoots_invertRoots (p : AzPolynomial R) (hp0 : p.coeff 0 ≠ 0) :
    p.invertRoots.invertRoots = p := by
  have h0 : (AzPolynomial.toPoly p).coeff 0 ≠ 0 := by
    rw [AzPolynomial.coeff_toPoly]; exact hp0
  have htr : (AzPolynomial.toPoly p).natTrailingDegree = 0 := by
    have := Polynomial.natTrailingDegree_le_of_ne_zero h0
    omega
  rw [← toPoly_inj, toPoly_invertRoots, toPoly_invertRoots]
  ext n
  rw [Polynomial.coeff_reverse, Polynomial.coeff_reverse, Polynomial.reverse_natDegree, htr,
    Nat.sub_zero, Polynomial.revAt_invol]

end Azurite.AzPolynomial
