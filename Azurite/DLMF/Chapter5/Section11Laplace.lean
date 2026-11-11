/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter5.Section11Gstar
import Azurite.DLMF.Chapter2.Section3LaplaceCoeff

/-!
# DLMF §5.11(i): the coefficients `aₖ` (5.11.5–5.11.6), formal part

The coefficients `aₖ` of 5.11.5–5.11.6 (`stirlingA`: `a₀ = ½√2` and
`a₀aₖ + ½a₁a_{k−1} + ⋯ + a_k a₀/(k + 1) = a_{k−1}/k`) are the coefficients of Laplace's method
(§2.3(iii), `laplaceMethodCoeff`) for `∫ e^{−x(τ − 1 − ln τ)} dτ` at `τ = 1`.

With `p(1 + σ'u) − p(1) = ∑ σˢ u^{s+2}/(s + 2)` (`σ = −1` for `τ > 1`, `σ = 1` after `τ ↦ 2 − τ`
for `τ < 1`), `P = ∑ σˢ Xˢ/(s + 2)`, `U = P^{1/2}`, `W = XU` and `B = ∑ bₛ Xˢ` the Laplace
coefficients, `laplaceMethod_formal` gives `B(W) = D⁻¹U` with `D = 2P + XP′ = (1 − σX)⁻¹`, and
`2UW′ = D`; so `B(W) W′ = ½`, the antiderivative `C` of `B` has `C(W) = X/2`, and substituting
`W` shows `CB = X/2 − σXC` (`laplaceCoeff_series`). Its coefficients are the recursion
5.11.6 twisted by `σ` (`laplaceCoeff_rec`), which determines the coefficients
(`eq_stirlingA_of_rec`): `bₛ = aₛ` for `σ = −1` and `bₛ = (−1)ˢ aₛ` for `σ = 1`
(`laplaceCoeff_neg_one`, `laplaceCoeff_one`).
-/

open PowerSeries
open scoped Real

namespace Azurite.DLMF

/-! ### The recursion 5.11.6 -/

/-- The coefficients `aₖ` of 5.11.5–5.11.6: `a₀ = ½√2` and, solving 5.11.6 for `a_{k+1}`,
`a_{k+1} = (aₖ/(k + 1) − ∑_{j=1}^{k} aⱼ a_{k+1−j}/(j + 1)) / (a₀ (k + 3)/(k + 2))`. -/
noncomputable def stirlingA : ℕ → ℝ
  | 0 => Real.sqrt 2 / 2
  | k + 1 => (stirlingA k / ((k : ℝ) + 1) -
      ∑ j : Fin k, stirlingA (j + 1) * stirlingA (k - j) / ((j : ℝ) + 2)) /
        (stirlingA 0 * (((k : ℝ) + 3) / ((k : ℝ) + 2)))
  decreasing_by all_goals (try have := j.isLt); omega

theorem stirlingA_zero : stirlingA 0 = Real.sqrt 2 / 2 := by rw [stirlingA]

theorem stirlingA_zero_pos : 0 < stirlingA 0 := by
  rw [stirlingA_zero]; positivity

/-- The recursion in the form `∑_{j=0}^{k+1} aⱼ a_{k+1−j}/(j + 1) = aₖ/(k + 1)`. -/
theorem stirlingRec_iff {a : ℕ → ℂ} (ha0 : a 0 ≠ 0) (k : ℕ) :
    (∑ j ∈ Finset.range (k + 2), a j * a (k + 1 - j) / ((j : ℂ) + 1) = a k / ((k : ℂ) + 1)) ↔
      a (k + 1) = (a k / ((k : ℂ) + 1) -
        ∑ j ∈ Finset.range k, a (j + 1) * a (k - j) / ((j : ℂ) + 2)) /
          (a 0 * (((k : ℂ) + 3) / ((k : ℂ) + 2))) := by
  have hsplit : ∑ j ∈ Finset.range (k + 2), a j * a (k + 1 - j) / ((j : ℂ) + 1) =
      a (k + 1) * (a 0 * (((k : ℂ) + 3) / ((k : ℂ) + 2))) +
        ∑ j ∈ Finset.range k, a (j + 1) * a (k - j) / ((j : ℂ) + 2) := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ']
    simp only [Nat.sub_zero, Nat.cast_zero, zero_add, div_one, Nat.sub_self]
    have e : ∀ j ∈ Finset.range k, a (j + 1) * a (k + 1 - (j + 1)) / (((j + 1 : ℕ) : ℂ) + 1) =
        a (j + 1) * a (k - j) / ((j : ℂ) + 2) := fun j _ => by
      rw [show k + 1 - (j + 1) = k - j by omega]; push_cast; ring
    rw [Finset.sum_congr rfl e]
    have h2 : ((k : ℂ) + 2) ≠ 0 := by exact_mod_cast (show k + 2 ≠ 0 by omega)
    have key : a 0 * a (k + 1) + a (k + 1) * a 0 / ((k : ℂ) + 1 + 1) =
        a (k + 1) * (a 0 * (((k : ℂ) + 3) / ((k : ℂ) + 2))) := by
      rw [show (k : ℂ) + 1 + 1 = k + 2 by ring]
      field_simp
      ring
    push_cast
    linear_combination key
  have hden : a 0 * (((k : ℂ) + 3) / ((k : ℂ) + 2)) ≠ 0 := by
    have h2 : ((k : ℂ) + 2) ≠ 0 := by exact_mod_cast (show k + 2 ≠ 0 by omega)
    have h3 : ((k : ℂ) + 3) ≠ 0 := by exact_mod_cast (show k + 3 ≠ 0 by omega)
    exact mul_ne_zero ha0 (div_ne_zero h3 h2)
  rw [hsplit, eq_div_iff hden]
  constructor <;> intro h <;> linear_combination h

/-- **DLMF 5.11.6**: `a₀aₖ + ½a₁a_{k−1} + ⅓a₂a_{k−2} + ⋯ + aₖa₀/(k + 1) = a_{k−1}/k`, `k ≥ 1`. -/
theorem dlmf_5_11_6 {k : ℕ} (hk : 1 ≤ k) :
    ∑ j ∈ Finset.range (k + 1), stirlingA j * stirlingA (k - j) / ((j : ℝ) + 1) =
      stirlingA (k - 1) / k := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  have ha0 : ((stirlingA 0 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast stirlingA_zero_pos.ne'
  have h := (stirlingRec_iff (a := fun j => (stirlingA j : ℂ)) ha0 m).mpr (by
    rw [stirlingA.eq_2]
    push_cast
    rw [Finset.sum_fin_eq_sum_range]
    congr 2
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [dite_eq_left (Finset.mem_range.mp hj)])
  simp only [Nat.add_sub_cancel]
  have h' : ((∑ j ∈ Finset.range (m + 2), stirlingA j * stirlingA (m + 1 - j) / ((j : ℝ) + 1) :
      ℝ) : ℂ) = ((stirlingA m / ((m : ℝ) + 1) : ℝ) : ℂ) := by
    push_cast; exact h
  push_cast
  exact_mod_cast h'

/-- The recursion determines the coefficients: if `b₀ = a₀` and `b` satisfies 5.11.6, `b = a`. -/
theorem eq_stirlingA_of_rec {b : ℕ → ℂ} (hb0 : b 0 = (stirlingA 0 : ℂ))
    (hrec : ∀ k, ∑ j ∈ Finset.range (k + 2), b j * b (k + 1 - j) / ((j : ℂ) + 1) =
      b k / ((k : ℂ) + 1)) : ∀ n, b n = (stirlingA n : ℂ) := by
  have ha0 : ((stirlingA 0 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast stirlingA_zero_pos.ne'
  have hb0' : b 0 ≠ 0 := by rw [hb0]; exact ha0
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases n with _ | k
    · exact hb0
    · have hc : ∑ j ∈ Finset.range (k + 2), (stirlingA j : ℂ) * (stirlingA (k + 1 - j) : ℂ) /
          ((j : ℂ) + 1) = (stirlingA k : ℂ) / ((k : ℂ) + 1) := by
        have := dlmf_5_11_6 (k := k + 1) (by omega)
        simp only [Nat.add_sub_cancel] at this
        exact_mod_cast this
      rw [(stirlingRec_iff hb0' k).mp (hrec k), ih k (by omega), hb0,
        (stirlingRec_iff (a := fun j => (stirlingA j : ℂ)) ha0 k).mp hc]
      congr 2
      refine Finset.sum_congr rfl fun j hj => ?_
      have := Finset.mem_range.mp hj
      rw [ih (j + 1) (by omega), ih (k - j) (by omega)]

/-! ### The Laplace coefficients of `τ − 1 − ln τ` at `τ = 1` -/

/-- `pₛ = σˢ/(s + 2)`: `p(1 + u) − p(1) = ∑ (−1)ˢ u^{s+2}/(s + 2)` (`σ = −1`) and
`p(1 − u) − p(1) = ∑ u^{s+2}/(s + 2)` (`σ = 1`), `p(τ) = τ − 1 − ln τ`. -/
noncomputable def laplacePs (σ : ℝ) (s : ℕ) : ℝ := σ ^ s / ((s : ℝ) + 2)

/-- `q = 1`. -/
def laplaceQs (s : ℕ) : ℂ := if s = 0 then 1 else 0

/-- The Laplace coefficients `bₛ` (2.3.18) with `λ = 1`, `μ = 2`. -/
noncomputable abbrev laplaceB (σ : ℝ) : ℕ → ℂ := laplaceMethodCoeff (laplacePs σ) laplaceQs 1 2

/-- The antiderivative `∑ b_{n−1} Xⁿ/n` of `∑ bₙ Xⁿ`. -/
noncomputable def antiderivPS (b : ℕ → ℂ) : ℂ⟦X⟧ := mk fun n => if n = 0 then 0 else b (n - 1) / n

theorem derivative_antiderivPS (b : ℕ → ℂ) : d⁄dX (antiderivPS b) = mk b := by
  ext n
  rw [coeff_derivative, antiderivPS, coeff_mk, coeff_mk, ite_eq_right (by omega),
    Nat.add_sub_cancel]
  have : ((n : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  push_cast
  field_simp

theorem eq_C_mul_X_of_derivative {f : ℂ⟦X⟧} {c : ℂ} (h0 : constantCoeff f = 0)
    (hd : d⁄dX f = C c) : f = C c * X := by
  ext n
  rcases n with _ | n
  · simp [h0]
  · have := congrArg (coeff n) hd
    rw [coeff_derivative, coeff_C] at this
    rw [coeff_succ_mul_X, coeff_C]
    have hn : ((n : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
    split_ifs at this ⊢ with h
    · subst h; simpa using this
    · exact (mul_eq_zero.mp this).resolve_right (by exact_mod_cast hn)

theorem laplacePs_zero (σ : ℝ) : laplacePs σ 0 = 1 / 2 := by simp [laplacePs]

theorem mk_laplaceQs : mk laplaceQs = 1 := by
  ext n; rcases n with _ | n <;> simp [laplaceQs, coeff_one]

theorem mk_derivExp_laplacePs (σ : ℝ) :
    (mk fun s => ((s : ℝ) + 2) * laplacePs σ s) = mk fun s => σ ^ s := by
  ext s
  simp only [coeff_mk, laplacePs]
  have : (s : ℝ) + 2 ≠ 0 := by positivity
  field_simp

theorem geom_mul_one_sub (c : ℂ) : (mk fun s => c ^ s) * (1 - C c * X) = 1 := by
  rw [show (mk fun s => c ^ s) * (1 - C c * X) =
    mk (fun s => c ^ s) - C c * (mk (fun s => c ^ s) * X) by ring]
  ext n
  rw [map_sub, coeff_C_mul]
  rcases n with _ | n
  · simp
  · rw [coeff_succ_mul_X, coeff_mk, coeff_mk, coeff_one, pow_succ]
    simp only [Nat.succ_ne_zero, ↓reduceIte]
    ring

/-- **The formal identity**: with `C` the antiderivative of `B = ∑ bₛ Xˢ`, `CB = X/2 − σXC`. -/
theorem laplaceCoeff_series (σ : ℝ) :
    antiderivPS (laplaceB σ) * mk (laplaceB σ) =
      (1 / 2 : ℂ) • X - (σ : ℂ) • (X * antiderivPS (laplaceB σ)) := by
  set P : ℝ⟦X⟧ := mk (laplacePs σ) with hPdef
  have hp0 : 0 < laplacePs σ 0 := by rw [laplacePs_zero]; norm_num
  have hP : 0 < constantCoeff P := by simpa [hPdef] using hp0
  have hF := laplaceMethod_formal laplaceQs (lam := 1) (μ := 2) two_pos hp0
  rw [mk_laplaceQs, one_mul, mk_derivExp_laplacePs, show ((2 : ℝ) - 1) / 2 = 1 / 2 by norm_num]
    at hF
  set u : ℝ⟦X⟧ := rpowPS P (1 / 2) with hu
  set U : ℂ⟦X⟧ := toCPS u with hU
  set W : ℂ⟦X⟧ := X * U with hW
  set D : ℂ⟦X⟧ := toCPS (mk fun s => σ ^ s) with hD
  set B : ℂ⟦X⟧ := mk (laplaceB σ) with hB
  -- `D⁻¹ = 1 − σX`
  have hDmk : D = mk fun s => (σ : ℂ) ^ s := by
    ext n; simp [hD, coeff_map]
  have hD0 : constantCoeff D ≠ 0 := by rw [hDmk]; simp
  have hDinv : D⁻¹ = 1 - C (σ : ℂ) * X := by
    rw [inv_eq_iff_mul_eq_one hD0, mul_comm, hDmk]
    exact geom_mul_one_sub _
  -- `2 U W′ = D`
  have huu : u * u = P := by rw [hu, rpowPS_mul hP, show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num,
    rpowPS_one hP]
  have hdu : d⁄dX u * P = C (1 / 2 : ℝ) * u * d⁄dX P := derivative_rpowPS_mul hP (1 / 2)
  have hP0 : P ≠ 0 := fun h => by rw [h, map_zero] at hP; exact lt_irrefl 0 hP
  have h2udu : C (2 : ℝ) * u * d⁄dX u = d⁄dX P := by
    have hc : C (2 : ℝ) * C (1 / 2 : ℝ) = 1 := by rw [← map_mul]; norm_num
    have h1 : P * (C (2 : ℝ) * u * d⁄dX u) = P * d⁄dX P := by
      calc P * (C (2 : ℝ) * u * d⁄dX u) = C (2 : ℝ) * u * (d⁄dX u * P) := by ring
        _ = C (2 : ℝ) * u * (C (1 / 2 : ℝ) * u * d⁄dX P) := by rw [hdu]
        _ = (C (2 : ℝ) * C (1 / 2 : ℝ)) * (u * u) * d⁄dX P := by ring
        _ = P * d⁄dX P := by rw [hc, huu, one_mul]
    exact mul_left_cancel₀ hP0 h1
  have hDreal : C (2 : ℝ) * u * d⁄dX (X * u) = mk fun s => σ ^ s := by
    rw [← mk_derivExp_laplacePs, mk_derivExp, ← hPdef, Derivation.leibniz, derivative_X,
      smul_eq_mul, smul_eq_mul, ← h2udu, ← huu]
    ring
  have hDc : C (2 : ℂ) * U * d⁄dX W = D := by
    have := congrArg toCPS hDreal
    rw [map_mul, map_mul, ← derivative_map_ofReal, map_mul, map_X] at this
    rw [hW, hU, hD, ← this]
    congr 1
    simp [map_C]
  have hBW : B.subst W * d⁄dX W = C (1 / 2 : ℂ) := by
    have h1 : C (2 : ℂ) * (B.subst W * d⁄dX W) = 1 := by
      rw [← hF, show C (2 : ℂ) * (D⁻¹ * U * d⁄dX W) = D⁻¹ * (C (2 : ℂ) * U * d⁄dX W) by ring,
        hDc, PowerSeries.inv_mul_cancel _ hD0]
    calc B.subst W * d⁄dX W = C (1 / 2 : ℂ) * (C (2 : ℂ) * (B.subst W * d⁄dX W)) := by
          rw [← mul_assoc, ← map_mul]; norm_num
      _ = C (1 / 2 : ℂ) := by rw [h1, mul_one]
  have hW0 : constantCoeff W = 0 := by simp [hW]
  have hsW : HasSubst W := HasSubst.of_constantCoeff_zero' hW0
  set Cs := antiderivPS (laplaceB σ) with hCs
  have hCW : Cs.subst W = C (1 / 2 : ℂ) * X := by
    refine eq_C_mul_X_of_derivative ?_ ?_
    · exact constantCoeff_subst_eq_zero hW0 _ (by simp [hCs, antiderivPS])
    · rw [derivative_subst hsW, hCs, derivative_antiderivPS, ← hB, hBW]
  have hU0 : constantCoeff U = ((((1 / 2 : ℝ) ^ (1 / 2 : ℝ)) : ℝ) : ℂ) := by
    rw [hU, constantCoeff_toCPS, hu, constantCoeff_rpowPS hP]
    simp [hPdef, laplacePs_zero]
  have hW1 : IsUnit (coeff 1 W) := by
    rw [hW, coeff_succ_X_mul, coeff_zero_eq_constantCoeff_apply, hU0]
    exact (Complex.ofReal_ne_zero.mpr (Real.rpow_pos_of_pos (by norm_num) _).ne').isUnit
  set Ψ := substInvOfIsUnit W hW1 with hΨ
  have hsΨ : HasSubst Ψ := HasSubst.substInvOfIsUnit _ _
  have hWΨ : W.subst Ψ = X := subst_substInvOfIsUnit_right _ hW0 _
  have hinj : ∀ F G : ℂ⟦X⟧, F.subst W = G.subst W → F = G := fun F G h => by
    have h' := congrArg (subst Ψ) h
    rw [subst_comp_subst_apply hsW hsΨ, subst_comp_subst_apply hsW hsΨ, hWΨ,
      ← map_algebraMap_eq_subst_X, ← map_algebraMap_eq_subst_X] at h'
    simpa using h'
  refine hinj _ _ ?_
  rw [subst_mul hsW, hCW, ← hF, subst_sub hsW, subst_smul hsW, subst_smul hsW, subst_mul hsW,
    subst_X hsW, hCW, hDinv, smul_eq_C_mul, smul_eq_C_mul]
  rw [hW]
  ring

/-- The coefficients of `CB = X/2 − σXC`: `∑_{j=0}^{k+1} bⱼ b_{k+1−j}/(j + 1) = −σ bₖ/(k + 1)`. -/
theorem laplaceCoeff_rec (σ : ℝ) (k : ℕ) :
    ∑ j ∈ Finset.range (k + 2), laplaceB σ j * laplaceB σ (k + 1 - j) / ((j : ℂ) + 1) =
      -(σ : ℂ) * laplaceB σ k / ((k : ℂ) + 1) := by
  have h := congrArg (coeff (k + 2)) (laplaceCoeff_series σ)
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_range_succ',
    map_sub, coeff_smul, coeff_smul, coeff_X, coeff_succ_X_mul] at h
  simp only [antiderivPS, coeff_mk, ↓reduceIte, zero_mul, add_zero, Nat.succ_ne_zero,
    show k + 2 ≠ 1 by omega, smul_eq_mul, mul_zero, zero_sub] at h
  calc ∑ j ∈ Finset.range (k + 2), laplaceB σ j * laplaceB σ (k + 1 - j) / ((j : ℂ) + 1)
      = ∑ x ∈ Finset.range (k + 2), laplaceB σ (x + 1 - 1) / ((x + 1 : ℕ) : ℂ) *
          laplaceB σ (k + 2 - (x + 1)) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [show k + 2 - (j + 1) = k + 1 - j by omega, Nat.add_sub_cancel]
        push_cast
        ring
    _ = -((σ : ℂ) * (laplaceB σ (k + 1 - 1) / ((k + 1 : ℕ) : ℂ))) := h
    _ = -(σ : ℂ) * laplaceB σ k / ((k : ℂ) + 1) := by
        rw [Nat.add_sub_cancel]; push_cast; ring

theorem laplaceCoeff_zero (σ : ℝ) : laplaceB σ 0 = (stirlingA 0 : ℂ) := by
  have hP : 0 < constantCoeff (mk (laplacePs σ) : ℝ⟦X⟧) := by
    simp [laplacePs_zero]
  rw [laplaceB, laplaceMethodCoeff, mk_laplaceQs, one_mul, coeff_zero_eq_constantCoeff_apply,
    constantCoeff_toCPS, constantCoeff_rpowPS hP, stirlingA_zero]
  simp only [constantCoeff_mk, laplacePs_zero, Nat.cast_zero, add_zero]
  rw [show -((1 : ℝ) / 2) = -(1 / 2) from rfl, Real.rpow_neg (by norm_num),
    ← Real.sqrt_eq_rpow, Real.sqrt_div' 1 (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_one]
  push_cast
  have : (Real.sqrt 2 : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr two_pos).ne'
  field_simp

/-- For `τ > 1` (`σ = −1`): `bₛ = aₛ`. -/
theorem laplaceCoeff_neg_one (n : ℕ) : laplaceB (-1) n = (stirlingA n : ℂ) :=
  eq_stirlingA_of_rec (laplaceCoeff_zero _) (fun k => by
    rw [laplaceCoeff_rec]; push_cast; ring) n

/-- For `τ < 1` (`σ = 1`): `bₛ = (−1)ˢ aₛ`. -/
theorem laplaceCoeff_one (n : ℕ) : laplaceB 1 n = (-1) ^ n * (stirlingA n : ℂ) := by
  have h := eq_stirlingA_of_rec (b := fun j => (-1) ^ j * laplaceB 1 j)
    (by simp [laplaceCoeff_zero]) (fun k => by
      have hr := laplaceCoeff_rec 1 k
      have e : ∀ j ∈ Finset.range (k + 2), (-1 : ℂ) ^ j * laplaceB 1 j *
          ((-1) ^ (k + 1 - j) * laplaceB 1 (k + 1 - j)) / ((j : ℂ) + 1) =
          (-1) ^ (k + 1) * (laplaceB 1 j * laplaceB 1 (k + 1 - j) / ((j : ℂ) + 1)) :=
        fun j hj => by
          have := Finset.mem_range.mp hj
          rw [show (-1 : ℂ) ^ (k + 1) = (-1) ^ j * (-1) ^ (k + 1 - j) by
            rw [← pow_add]; congr 1; omega]
          ring
      rw [Finset.sum_congr rfl e, ← Finset.mul_sum, hr, pow_succ]
      push_cast
      ring) n
  have hsq : (-1 : ℂ) ^ n * (-1) ^ n = 1 := by rw [← mul_pow]; norm_num
  calc laplaceB 1 n = (-1) ^ n * ((-1) ^ n * laplaceB 1 n) := by rw [← mul_assoc, hsq, one_mul]
    _ = (-1) ^ n * (stirlingA n : ℂ) := by rw [h]

end Azurite.DLMF
