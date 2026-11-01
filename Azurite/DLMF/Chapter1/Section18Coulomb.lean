/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter1.Section18Radial
import Mathlib.Analysis.Calculus.ContDiff.Polynomial
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.ExpDecay
import Mathlib.MeasureTheory.Function.L2Space

/-!
# DLMF §1.18(viii), Example 2: the Schrödinger–Coulomb problem

https://dlmf.nist.gov/1.18.viii

For `V = −1/r`, DLMF states that the point spectrum of `ℒ_ℓ` is infinite for every `ℓ` and
accumulates at the onset `0` of the continuum. This file builds the bound states explicitly:
`u_{n,ℓ}(r) = e^{−r/n} P(r)` (`coulombFun`), where `P = Σ a_k r^k` (`coulombPoly`) has
`a_k = 0` for `k ≤ ℓ`, `a_{ℓ+1} = 1`, and
`((k + 1)k − ℓ(ℓ + 1)) a_{k+1} = −(2/n)(n − k) a_k` (`coulombCoeff`), which terminates at
degree `n`. Up to normalization, `P = r^{ℓ+1} L^{(2ℓ+1)}_{n−ℓ−1}(2r/n)` (Laguerre), which is not
used here. The radial equation reduces to the polynomial identity
`r²P″ − (2/n) r²P′ + 2rP − ℓ(ℓ + 1)P = 0` (`coulombResidual_eq_zero`), checked
coefficientwise.

* `dlmf_1_18_viii_coulomb`: for each `n ≥ ℓ + 1`, `ℒ_ℓ u_{n,ℓ} = −u_{n,ℓ}/(2n²)` on `(0, ∞)`,
  with `u_{n,ℓ}` smooth, nonzero, `u_{n,ℓ}(0) = 0`, and in `L²(0, ∞)`. The eigenvalues
  `−1/(2n²)` are negative, strictly increasing, and tend to `0`.
* `integral_coulombFun_mul`: orthogonality `∫₀^∞ u_{n,ℓ} u_{m,ℓ} dr = 0` for `n ≠ m` (DLMF
  (1.18.61) for this example), via the Lagrange identity and the decay of the Wronskian.

Completeness of the bound states together with the continuum (Bethe–Salpeter's transform
pair) is not formalized.
-/

open Set Filter Topology MeasureTheory Polynomial
open scoped ContDiff

namespace Azurite.DLMF

/-! ### Coefficients -/

/-- Coefficients of `P = r^{ℓ+1} L(2r/n)`, by the recurrence
`((k + 1)k − ℓ(ℓ + 1)) a_{k+1} = −(2/n)(n − k) a_k`, with `a_{ℓ+1} = 1`. -/
noncomputable def coulombCoeff (n ℓ : ℕ) : ℕ → ℝ
  | 0 => 0
  | k + 1 => if k = ℓ then 1 else
      -(2 / n) * ((n : ℝ) - k) * coulombCoeff n ℓ k / (((k : ℝ) + 1) * k - ℓ * (ℓ + 1))

theorem coulombCoeff_of_le (n ℓ : ℕ) : ∀ k, k ≤ ℓ → coulombCoeff n ℓ k = 0
  | 0, _ => rfl
  | k + 1, hk => by
    have hne : k ≠ ℓ := by omega
    rw [coulombCoeff, coulombCoeff_of_le n ℓ k (by omega)]
    simp [hne]

theorem coulombCoeff_rec (n ℓ k : ℕ) (hk : k ≠ ℓ) :
    (((k : ℝ) + 1) * k - ℓ * (ℓ + 1)) * coulombCoeff n ℓ (k + 1) =
      -(2 / n) * ((n : ℝ) - k) * coulombCoeff n ℓ k := by
  have hD : ((k : ℝ) + 1) * k - ℓ * (ℓ + 1) ≠ 0 := by
    intro h
    rcases lt_or_gt_of_ne hk with h' | h'
    · have : (k : ℝ) + 1 ≤ ℓ := by exact_mod_cast h'
      have : (0 : ℝ) ≤ k := k.cast_nonneg
      nlinarith
    · have : (ℓ : ℝ) + 1 ≤ k := by exact_mod_cast h'
      have : (0 : ℝ) ≤ ℓ := ℓ.cast_nonneg
      nlinarith
  rw [coulombCoeff]
  simp only [hk, ↓reduceIte]
  rw [mul_comm]
  exact div_mul_cancel₀ _ hD

theorem coulombCoeff_of_gt {n ℓ : ℕ} (hn : ℓ + 1 ≤ n) : ∀ k, n + 1 ≤ k → coulombCoeff n ℓ k = 0
  | 0, h => by omega
  | k + 1, h => by
    have hne : k ≠ ℓ := by omega
    rw [coulombCoeff]
    simp only [hne, ↓reduceIte]
    rcases Nat.eq_or_lt_of_le (Nat.le_of_succ_le_succ h) with h' | h'
    · subst h'; simp
    · rw [coulombCoeff_of_gt hn k h']; simp

/-- The polynomial `P = Σ a_k X^k`. -/
noncomputable def coulombPoly (n ℓ : ℕ) : ℝ[X] :=
  ∑ k ∈ Finset.range (n + 1), C (coulombCoeff n ℓ k) * X ^ k

theorem coeff_coulombPoly {n ℓ : ℕ} (hn : ℓ + 1 ≤ n) (k : ℕ) :
    (coulombPoly n ℓ).coeff k = coulombCoeff n ℓ k := by
  rw [coulombPoly, finsetSum_coeff]
  simp only [coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq]
  split_ifs with h
  · rfl
  · rw [coulombCoeff_of_gt hn k (by simp at h; omega)]

/-- The polynomial form of the radial Coulomb equation:
`r²P″ − (2/n) r²P′ + 2rP − ℓ(ℓ + 1)P`. -/
noncomputable def coulombResidual (n ℓ : ℕ) (P : ℝ[X]) : ℝ[X] :=
  X ^ 2 * (derivative (derivative P) - C (2 / (n : ℝ)) * derivative P) + C 2 * (X * P) -
    C ((ℓ : ℝ) * (ℓ + 1)) * P

theorem coeff_coulombResidual_zero (n ℓ : ℕ) (P : ℝ[X]) :
    (coulombResidual n ℓ P).coeff 0 = -((ℓ : ℝ) * (ℓ + 1)) * P.coeff 0 := by
  simp [coulombResidual]

theorem coeff_coulombResidual_succ (n ℓ : ℕ) (hn : n ≠ 0) (P : ℝ[X]) (k : ℕ) :
    (coulombResidual n ℓ P).coeff (k + 1) =
      ((((k : ℝ) + 1) * k - ℓ * (ℓ + 1)) * P.coeff (k + 1) +
        (2 / n) * ((n : ℝ) - k) * P.coeff k) := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  rcases k with _ | k
  · simp only [coulombResidual, coeff_sub, coeff_add, coeff_X_pow_mul', coeff_C_mul, coeff_X_mul,
      coeff_derivative]
    simp
    rw [div_mul_cancel₀ _ hn']
    ring
  · simp only [coulombResidual, coeff_sub, coeff_add, coeff_X_pow_mul', coeff_C_mul, coeff_X_mul,
      coeff_derivative]
    simp only [show 2 ≤ k + 1 + 1 by omega, ↓reduceIte, show k + 1 + 1 - 2 = k by omega]
    push_cast
    field_simp
    ring

theorem coulombResidual_eq_zero {n ℓ : ℕ} (hn : ℓ + 1 ≤ n) :
    coulombResidual n ℓ (coulombPoly n ℓ) = 0 := by
  have hn0 : n ≠ 0 := by omega
  ext k
  rw [coeff_zero]
  rcases k with _ | k
  · rw [coeff_coulombResidual_zero, coeff_coulombPoly hn, coulombCoeff]; ring
  · rw [coeff_coulombResidual_succ n ℓ hn0, coeff_coulombPoly hn, coeff_coulombPoly hn]
    by_cases hk : k = ℓ
    · subst hk
      rw [coulombCoeff_of_le n k k le_rfl]
      ring
    · rw [coulombCoeff_rec n ℓ k hk]
      ring

/-! ### The eigenfunctions -/

/-- The Coulomb bound state `u_{n,ℓ}(r) = e^{−r/n} P(r)`, with `P = r^{ℓ+1} × (Laguerre)`. -/
noncomputable def coulombFun (n ℓ : ℕ) (r : ℝ) : ℝ :=
  Real.exp (-(r / n)) * (coulombPoly n ℓ).eval r

theorem hasDerivAt_exp_mul_eval (b : ℝ) (P : ℝ[X]) (r : ℝ) :
    HasDerivAt (fun r => Real.exp (-(r * b)) * P.eval r)
      (Real.exp (-(r * b)) * (P.derivative - C b * P).eval r) r := by
  have h := (((hasDerivAt_id r).mul_const b).neg.exp).mul (P.hasDerivAt r)
  refine h.congr_deriv ?_
  simp only [id, Pi.neg_apply, eval_sub, eval_mul, eval_C]
  ring

/-- `P′ − P/n`, so that `u′ = e^{−r/n}(P′ − P/n)`. -/
noncomputable def coulombD (n ℓ : ℕ) : ℝ[X] :=
  derivative (coulombPoly n ℓ) - C (1 / (n : ℝ)) * coulombPoly n ℓ

theorem deriv_coulombFun (n ℓ : ℕ) :
    deriv (coulombFun n ℓ) = fun r => Real.exp (-(r / n)) * (coulombD n ℓ).eval r := by
  funext r
  have h := hasDerivAt_exp_mul_eval (1 / n) (coulombPoly n ℓ) r
  simp only [mul_one_div] at h
  exact h.deriv

theorem deriv_deriv_coulombFun (n ℓ : ℕ) (r : ℝ) : deriv (deriv (coulombFun n ℓ)) r =
    Real.exp (-(r / n)) *
      (derivative (coulombD n ℓ) - C (1 / (n : ℝ)) * coulombD n ℓ).eval r := by
  rw [deriv_coulombFun]
  have h := hasDerivAt_exp_mul_eval (1 / n) (coulombD n ℓ) r
  simp only [mul_one_div] at h
  exact h.deriv

/-- The radial Coulomb equation `ℒ_ℓ u = −u/(2n²)` with `V = −1/r`. -/
theorem radialOp_coulombFun {n ℓ : ℕ} (hn : ℓ + 1 ≤ n) {r : ℝ} (hr : r ≠ 0) :
    radialOp ℓ (fun r => -r⁻¹) (coulombFun n ℓ) r = -(1 / (2 * n ^ 2)) * coulombFun n ℓ r := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hQ := congrArg (eval r) (coulombResidual_eq_zero hn)
  simp only [coulombResidual, eval_sub, eval_add, eval_mul, eval_pow, eval_X, eval_C,
    eval_zero] at hQ
  rw [radialOp, deriv_deriv_coulombFun, coulombFun]
  simp only [coulombD, derivative_sub, derivative_mul, derivative_C, zero_mul, zero_add,
    eval_sub, eval_mul, eval_C]
  field_simp at hQ
  field_simp
  linear_combination (-n) * hQ

theorem continuous_coulombFun (n ℓ : ℕ) : Continuous (coulombFun n ℓ) := by
  unfold coulombFun; fun_prop

theorem contDiff_coulombFun (n ℓ : ℕ) : ContDiff ℝ ∞ (coulombFun n ℓ) := by
  have hP : ContDiff ℝ ∞ fun r : ℝ => (coulombPoly n ℓ).eval r := by
    simpa using (coulombPoly n ℓ).contDiff_aeval (𝕜 := ℝ) ∞
  exact (Real.contDiff_exp.comp (contDiff_id.div_const _).neg).mul hP

theorem coulombFun_zero {n ℓ : ℕ} (hn : ℓ + 1 ≤ n) : coulombFun n ℓ 0 = 0 := by
  rw [coulombFun, ← coeff_zero_eq_eval_zero, coeff_coulombPoly hn, coulombCoeff, mul_zero]

theorem coulombPoly_ne_zero {n ℓ : ℕ} (hn : ℓ + 1 ≤ n) : coulombPoly n ℓ ≠ 0 := by
  intro h
  have := coeff_coulombPoly hn (ℓ + 1)
  rw [h, coeff_zero, coulombCoeff] at this
  simp at this

theorem exists_coulombFun_ne_zero {n ℓ : ℕ} (hn : ℓ + 1 ≤ n) : ∃ r > 0, coulombFun n ℓ r ≠ 0 := by
  obtain ⟨r, hr, hroot⟩ := (Ioi_infinite (0 : ℝ)).exists_notMem_finset
    (coulombPoly n ℓ).roots.toFinset
  refine ⟨r, hr, mul_ne_zero (Real.exp_pos _).ne' fun h => hroot ?_⟩
  simpa [coulombPoly_ne_zero hn] using h

/-- A polynomial times `e^{−br}` tends to `0`. -/
theorem tendsto_eval_mul_exp_neg (P : ℝ[X]) {b : ℝ} (hb : 0 < b) :
    Tendsto (fun r => P.eval r * Real.exp (-(b * r))) atTop (𝓝 0) := by
  have h : ∀ i : ℕ, Tendsto (fun r => P.coeff i * r ^ i * Real.exp (-(b * r))) atTop (𝓝 0) :=
    fun i => by
      have h1 := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero i).comp
        (tendsto_id.const_mul_atTop hb)
      have h2 := h1.const_mul (P.coeff i / b ^ i)
      rw [mul_zero] at h2
      refine h2.congr fun r => ?_
      simp only [Function.comp, id]
      field_simp
      ring
  have := tendsto_finsetSum (Finset.range (P.natDegree + 1)) fun i _ => h i
  simp only [Finset.sum_const_zero] at this
  refine this.congr fun r => ?_
  rw [eval_eq_sum_range, Finset.sum_mul]

theorem memLp_coulombFun {n ℓ : ℕ} (hn : ℓ + 1 ≤ n) :
    MemLp (coulombFun n ℓ) 2 (volume.restrict (Ioi 0)) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hc := continuous_coulombFun n ℓ
  refine (memLp_two_iff_integrable_sq_norm hc.aestronglyMeasurable).mpr ?_
  refine integrable_of_isBigO_exp_neg (b := 1 / n) (by positivity) (by fun_prop) ?_
  have ht := (tendsto_eval_mul_exp_neg (coulombPoly n ℓ ^ 2) (b := 1 / n) (by positivity))
  have h1 := ((ht.isBigO_one ℝ).mul
    (Asymptotics.isBigO_refl (fun x => Real.exp (-(1 / n) * x)) atTop)).congr_right
      fun r => one_mul (Real.exp (-(1 / n) * r))
  refine h1.congr_left fun r => ?_
  rw [Real.norm_eq_abs, sq_abs, coulombFun, mul_pow, eval_pow, mul_assoc, ← Real.exp_add, mul_comm]
  congr 2
  rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
