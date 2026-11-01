/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/


import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.Trunc

/-!
# Formal Lagrange inversion

* `coeff_inv_pow_mul_derivative`: `res Ψ^{−m}Ψ′ = δ_{m1}` in power-series form.
* `lagrange_inversion`: if `Ψ = Xφ(Ψ)`, `Ψ(0) = 0`, `φ(0) ≠ 0`, then
  `n [wⁿ] H(Ψ) = [v^{n−1}] H′φⁿ` for every power series `H` and `n ≥ 1` (proved from scratch
  over any field of characteristic `0`; not in Mathlib).
* `lagrangeF` (`F₀ = f₀`, `sFₛ = [v^{s+1}](1 + vG)ˢ`) and `inv_subst_eq_lagrangeF`:
  `1/φ(Ψ) = 1 − F₀w − F₁w² − ⋯` for `φ = 1 + vG`.
-/

open PowerSeries

namespace Azurite.DLMF

variable {K : Type*} [Field K]

/-- The residue computation behind Lagrange inversion: for `Ψ = X·u` with `u(0) ≠ 0` and
`m ≥ 1`, the coefficient of `w^{m−1}` in `u^{−m} Ψ′` is `1` if `m = 1` and `0` otherwise
(i.e. `res Ψ^{−m} Ψ′ = δ_{m1}`). -/
theorem coeff_inv_pow_mul_derivative [CharZero K] (u : K⟦X⟧) (hu : constantCoeff u ≠ 0) (m : ℕ)
    (hm : 1 ≤ m) :
    coeff (m - 1) (u⁻¹ ^ m * d⁄dX (X * u)) = if m = 1 then 1 else 0 := by
  have hd : d⁄dX (X * u) = u + X * d⁄dX u := by
    rw [Derivation.leibniz, derivative_X, smul_eq_mul, smul_eq_mul, mul_one]; ring
  have hinv : u⁻¹ * u = 1 := PowerSeries.inv_mul_cancel u hu
  rw [hd]
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  rcases k with _ | k
  · simp only [zero_add, pow_one, Nat.sub_self, ite_true]
    rw [mul_add, hinv, map_add, coeff_zero_eq_constantCoeff_apply, map_one,
      ← mul_assoc, mul_comm u⁻¹ X, mul_assoc, coeff_zero_eq_constantCoeff_apply, map_mul,
      constantCoeff_X, zero_mul, add_zero]
  · set B := u⁻¹ ^ (k + 1)
    have hB : u⁻¹ ^ (k + 2) * u = B := by
      rw [pow_succ, mul_assoc, hinv, mul_one]
    have hdB : d⁄dX B = -((k + 1 : K⟦X⟧)) * (u⁻¹ ^ (k + 2) * d⁄dX u) := by
      rw [derivative_pow, derivative_inv']
      push_cast
      ring
    have hX : u⁻¹ ^ (k + 2) * d⁄dX u = C (-(1 / ((k : K) + 1))) * d⁄dX B := by
      rw [hdB, ← mul_assoc]
      have : C (-(1 / ((k : K) + 1))) * -((k + 1 : K⟦X⟧)) = 1 := by
        rw [show ((k + 1 : K⟦X⟧)) = C ((k : K) + 1) by simp, ← map_neg, ← map_mul]
        rw [show -(1 / ((k : K) + 1)) * -((k : K) + 1) = 1 by
          field_simp]
        simp
      rw [this, one_mul]
    simp only [show k + 1 + 1 - 1 = k + 1 by omega, show k + 1 + 1 = k + 2 by omega]
    rw [ite_eq_right_iff.mpr (fun h => absurd h (by omega)), mul_add, hB, ← mul_assoc,
      mul_comm (u⁻¹ ^ (k + 2)) X, mul_assoc, hX,
      map_add, coeff_succ_X_mul, coeff_C_mul, coeff_derivative]
    field_simp
    ring

/-- **Lagrange inversion** (formal): if `Ψ = X·φ(Ψ)` with `Ψ(0) = 0`, `φ(0) ≠ 0`, then for every
power series `H` and `n ≥ 1`, `n [wⁿ] H(Ψ(w)) = [v^{n−1}] H′(v) φ(v)ⁿ`. -/
theorem lagrange_inversion [CharZero K] {φ Ψ : K⟦X⟧} (hΨ0 : constantCoeff Ψ = 0)
    (hφ0 : constantCoeff φ ≠ 0) (hΨ : Ψ = X * φ.subst Ψ) (H : K⟦X⟧) {n : ℕ} (hn : 1 ≤ n) :
    (n : K) * coeff n (H.subst Ψ) = coeff (n - 1) (d⁄dX H * φ ^ n) := by
  have hs : HasSubst Ψ := HasSubst.of_constantCoeff_zero' hΨ0
  set u : K⟦X⟧ := φ.subst Ψ with hu_def
  have hu0 : constantCoeff u = constantCoeff φ := by
    have := constantCoeff_subst_of_constantCoeff_zero (a := Ψ) hΨ0 φ
    exact this
  have hu : constantCoeff u ≠ 0 := by rw [hu0]; exact hφ0
  have huinv : u * u⁻¹ = 1 := PowerSeries.mul_inv_cancel u hu
  set A := d⁄dX H * φ ^ n
  -- step 1: `n [wⁿ] F = [w^{n−1}] F′`
  have h1 : (n : K) * coeff n (H.subst Ψ) = coeff (n - 1) (d⁄dX (H.subst Ψ)) := by
    rw [coeff_derivative, show n - 1 + 1 = n by omega, mul_comm]
    push_cast [show ((n - 1 : ℕ) : K) + 1 = n by
      rw [Nat.cast_sub hn]; push_cast; ring]
    ring
  rw [h1, derivative_subst hs]
  -- step 2: `H′(Ψ) = A(Ψ) u^{−n}`
  have hA : (d⁄dX H).subst Ψ = A.subst Ψ * u⁻¹ ^ n := by
    rw [subst_mul hs, subst_pow hs, mul_assoc, ← mul_pow, ← hu_def, huinv, one_pow, mul_one]
  -- step 3: split `A = Xⁿ R + (trunc n A)`
  have hsplit := eq_X_pow_mul_shift_add_trunc n A
  set R := mk fun i => coeff (i + n) A
  have hAΨ : A.subst Ψ = X ^ n * (u ^ n * R.subst Ψ) +
      ∑ j ∈ Finset.range n, C (coeff j A) * (X ^ j * u ^ j) := by
    conv_lhs => rw [hsplit]
    rw [subst_add hs, subst_mul hs, subst_pow hs, subst_X hs, subst_coe hs,
      Polynomial.aeval_eq_sum_range' (n := n) (by
        rcases n with _ | n
        · omega
        · exact natDegree_trunc_lt A n)]
    congr 1
    · rw [hΨ, mul_pow]; ring
    · refine Finset.sum_congr rfl fun j hj => ?_
      rw [coeff_trunc, ite_eq_left_iff.mpr (fun h => absurd (Finset.mem_range.mp hj) h),
        smul_eq_C_mul, hΨ, mul_pow]
  rw [hA, hAΨ]
  have hdΨ : d⁄dX Ψ = d⁄dX (X * u) := by rw [← hΨ]
  rw [hdΨ, add_mul, add_mul, map_add]
  -- the `Xⁿ` part does not contribute
  rw [mul_assoc, mul_assoc, coeff_X_pow_mul', ite_eq_right_iff.mpr (fun h => absurd h (by omega)),
    zero_add]
  rw [Finset.sum_mul, Finset.sum_mul, map_sum]
  have hterm : ∀ j ∈ Finset.range n, coeff (n - 1) (C (coeff j A) * (X ^ j * u ^ j) * u⁻¹ ^ n *
      d⁄dX (X * u)) = if j = n - 1 then coeff j A else 0 := by
    intro j hj
    have hjn : j < n := Finset.mem_range.mp hj
    obtain ⟨k, hk⟩ : ∃ k, n = j + k := ⟨n - j, by omega⟩
    have e : u ^ j * u⁻¹ ^ n = u⁻¹ ^ k := by
      rw [hk, pow_add, ← mul_assoc, ← mul_pow, huinv, one_pow, one_mul]
    rw [show C (coeff j A) * (X ^ j * u ^ j) * u⁻¹ ^ n * d⁄dX (X * u) =
        C (coeff j A) * (X ^ j * ((u ^ j * u⁻¹ ^ n) * d⁄dX (X * u))) by ring, e, coeff_C_mul,
      coeff_X_pow_mul', ite_eq_left_iff.mpr (fun h => absurd (by omega) h),
      show n - 1 - j = k - 1 by omega, coeff_inv_pow_mul_derivative u hu k (by omega)]
    by_cases hjk : j = n - 1
    · simp only [hjk, ↓reduceIte, show k = 1 by omega, mul_one]
    · simp only [hjk, ↓reduceIte, show k ≠ 1 by omega, mul_zero]
  rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq' (Finset.range n) (n - 1)]
  simp only [Finset.mem_range, show n - 1 < n by omega, ↓reduceIte]

/-! ### Lagrange's coefficients for the reversion 2.2.8 -/

/-- `F₀ = f₀` and `Fₛ = (1/s) [v^{s+1}] (1 + v G(v))ˢ` (`s ≥ 1`), `G = ∑ fₖvᵏ`: `s Fₛ` is the
coefficient of `x⁻¹` in `(x + f₀ + f₁x⁻¹ + ⋯)ˢ = xˢ(1 + f₀x⁻¹ + f₁x⁻² + ⋯)ˢ`. -/
noncomputable def lagrangeF (fc : ℕ → K) (s : ℕ) : K :=
  if s = 0 then fc 0 else 1 / (s : K) * coeff (s + 1) ((1 + X * mk fc) ^ s)

theorem constantCoeff_one_add_X_mul (G : K⟦X⟧) : constantCoeff (1 + X * G) = 1 := by simp

/-- With `φ = 1 + vG(v)` and `Ψ = X φ(Ψ)`, `1/φ(Ψ) = 1 − F₀w − F₁w² − ⋯`. -/
theorem inv_subst_eq_lagrangeF [CharZero K] {fc : ℕ → K} {Ψ : K⟦X⟧}
    (hΨ0 : constantCoeff Ψ = 0) (hΨ : Ψ = X * (1 + X * mk fc).subst Ψ) :
    (1 + X * mk fc)⁻¹.subst Ψ = 1 - X * mk (lagrangeF fc) := by
  set φ := 1 + X * mk fc
  have hφ1 : constantCoeff φ = 1 := constantCoeff_one_add_X_mul _
  have hφ0 : constantCoeff φ ≠ 0 := by rw [hφ1]; exact one_ne_zero
  have hinv : φ⁻¹ * φ = 1 := PowerSeries.inv_mul_cancel φ hφ0
  have hdφ : coeff 0 (d⁄dX φ) = fc 0 := by
    rw [coeff_derivative]; simp [φ]
  ext n
  rcases n with _ | _ | m
  · have := constantCoeff_subst_of_constantCoeff_zero (a := Ψ) hΨ0 φ⁻¹
    rw [coeff_zero_eq_constantCoeff_apply]
    have h0 : constantCoeff (φ⁻¹.subst Ψ) = 1 := by
      have e : constantCoeff (φ⁻¹.subst Ψ) = (algebraMap K K) (constantCoeff φ⁻¹) := this
      rw [e]; simp [PowerSeries.constantCoeff_inv, hφ1]
    rw [h0]; simp
  · have h := lagrange_inversion hΨ0 hφ0 hΨ φ⁻¹ (n := 1) le_rfl
    rw [Nat.cast_one, one_mul, pow_one, derivative_inv'] at h
    rw [h, show (-φ⁻¹ ^ 2 * d⁄dX φ * φ) = -(φ⁻¹ * (φ⁻¹ * φ)) * d⁄dX φ by ring, hinv, mul_one,
      Nat.sub_self, coeff_zero_eq_constantCoeff_apply, map_mul, map_neg,
      PowerSeries.constantCoeff_inv, hφ1, ← coeff_zero_eq_constantCoeff_apply, hdφ]
    simp [lagrangeF]
  · have h := lagrange_inversion hΨ0 hφ0 hΨ φ⁻¹ (n := m + 2) (by omega)
    rw [derivative_inv'] at h
    have e : -φ⁻¹ ^ 2 * d⁄dX φ * φ ^ (m + 2) =
        C (-(1 / ((m : K) + 1))) * d⁄dX (φ ^ (m + 1)) := by
      rw [derivative_pow]
      have : φ⁻¹ ^ 2 * φ ^ (m + 2) = φ ^ m := by
        rw [pow_add, ← mul_assoc, mul_comm (φ⁻¹ ^ 2), mul_assoc, ← mul_pow, hinv, one_pow,
          mul_one]
      rw [show -φ⁻¹ ^ 2 * d⁄dX φ * φ ^ (m + 2) = -(φ⁻¹ ^ 2 * φ ^ (m + 2)) * d⁄dX φ by ring,
        this, show m + 1 - 1 = m by omega, ← mul_assoc, ← mul_assoc]
      congr 1
      rw [show ((m + 1 : ℕ) : K⟦X⟧) = C ((m : K) + 1) by simp, ← map_mul]
      rw [show -(1 / ((m : K) + 1)) * ((m : K) + 1) = -1 by field_simp]
      simp
    rw [e, coeff_C_mul, show m + 2 - 1 = m + 1 by omega, coeff_derivative] at h
    rw [map_sub, coeff_succ_X_mul, coeff_mk]
    simp only [lagrangeF, show m + 1 ≠ 0 by omega, ↓reduceIte, Nat.cast_add, Nat.cast_one,
      PowerSeries.coeff_one, show m + 1 + 1 ≠ 0 by omega]
    have hm1 : ((m : K) + 1) ≠ 0 := Nat.cast_add_one_ne_zero m
    have hm2 : ((m : K) + 2) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (m + 1)
    have h' : coeff (m + 1 + 1) (φ⁻¹.subst Ψ) =
        -(1 / ((m : K) + 1)) * coeff (m + 1 + 1) (φ ^ (m + 1)) := by
      push_cast at h
      have h2 : ((m : K) + 2) * (((m : K) + 1) * coeff (m + 1 + 1) (φ⁻¹.subst Ψ)) =
          ((m : K) + 2) * (-coeff (m + 1 + 1) (φ ^ (m + 1))) := by
        rw [show m + 1 + 1 = m + 2 by omega]
        rw [show m + 1 + 1 = m + 2 by omega] at h
        field_simp at h
        linear_combination h
      have h3 := mul_left_cancel₀ hm2 h2
      field_simp
      linear_combination h3
    rw [h']
    ring

end Azurite.DLMF
