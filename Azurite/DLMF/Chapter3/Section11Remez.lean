/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter3.Section11Minimax
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.Polynomial

/-!
# DLMF §3.11(i): local quadratic convergence of the Remez iteration

"The iterative process converges locally and quadratically": let `f ∈ C²`, and let `p*` (degree
`≤ n`) equioscillate on nodes `x₀* < x₁* < ⋯ < x_{n+1}*`, `ε*(x_j*) = (−1)^j m*`
(`ε* = f − p*`), with nondegenerate interior extrema `ε*′(x_j*) = 0`, `ε*″(x_j*) ≠ 0`
(`1 ≤ j ≤ n`). Then for `p` near `p*`:

* near each interior `x_j*` the derivative `εₙ′` of `εₙ = f − p` has exactly one zero, and
* the update 3.11.4–3.11.5 computed with these nodes and `x₀ = x₀*`, `x_{n+1} = x_{n+1}*`
  satisfies `‖p_new − p*‖ ≤ K ‖p − p*‖²` and `|E − m*| ≤ K ‖p − p*‖²`
  (`dlmf_3_11_i_remez_local`), in the coefficient norm `cn n p = ∑_{k≤n} |p_k|`;
* iterating, the process converges quadratically (`dlmf_3_11_i_remez_converges`).

Ingredients: uniform invertibility of the Remez system near the nodes (`remez_lower`, by
compactness and `remezSystem_injective`), linearization of `ε*′` at a nondegenerate zero
(`lin_near`, `lin_lower`, `lin_unique`, `lin_exists`), and the second-order bound at a critical
point (`lin_taylor`). Only the interior nodes move; DLMF's process also lets endpoints move when
`ε` has an interior extremum there, which is not covered.

The update is characterized by `p_new(x_j) = f(x_j) − (−1)^j m` (`remez_step_iff`), equivalently
by DLMF's correction form 3.11.5 with `m_j = (−1)^j εₙ(x_j)` (3.11.3) (`remez_step_iff_delta`).
By `dlmf_3_11_i_sufficient`, `p*` is the minimax polynomial on `[x₀*, x_{n+1}*]` when moreover
`|ε*| ≤ |m*|` there.
-/

open Polynomial Finset Set Filter Topology Metric

namespace Azurite.DLMF

/-! ### Coefficient norm -/

/-- The coefficient norm `∑_{k ≤ n} |p_k|`. -/
noncomputable def cn (n : ℕ) (p : ℝ[X]) : ℝ := ∑ k ∈ range (n + 1), |p.coeff k|

theorem cn_nonneg (n : ℕ) (p : ℝ[X]) : 0 ≤ cn n p := sum_nonneg fun _ _ => abs_nonneg _

theorem eval_bound {q : ℝ[X]} {n : ℕ} (hq : q.natDegree ≤ n) {R : ℝ} (hR : 1 ≤ R) {x : ℝ}
    (hx : |x| ≤ R) : |q.eval x| ≤ R ^ n * cn n q := by
  rw [eval_eq_sum_range' (Nat.lt_succ_of_le hq), cn, mul_sum]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun k hk => ?_)
  have hk' : k ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hk)
  rw [abs_mul, abs_pow, mul_comm]
  gcongr
  calc |x| ^ k ≤ R ^ k := pow_le_pow_left₀ (abs_nonneg _) hx k
    _ ≤ R ^ n := pow_le_pow_right₀ hR hk'

theorem natDegree_derivative_le' {q : ℝ[X]} {n : ℕ} (hq : q.natDegree ≤ n) :
    q.derivative.natDegree ≤ n :=
  (natDegree_derivative_le q).trans (by omega)

theorem cn_derivative {q : ℝ[X]} {n : ℕ} (hq : q.natDegree ≤ n) :
    cn n q.derivative ≤ n * cn n q := by
  have hzero : q.coeff (n + 1) = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
  have h1 : ∀ k ∈ range (n + 1), |q.derivative.coeff k| ≤ n * |q.coeff (k + 1)| := by
    intro k hk
    rw [coeff_derivative, abs_mul, mul_comm]
    by_cases hkn : k + 1 ≤ n
    · gcongr
      rw [abs_of_nonneg (by positivity)]
      exact_mod_cast hkn
    · have : k = n := by have := mem_range.mp hk; omega
      subst this
      simp [hzero]
  have h2 : ∑ k ∈ range (n + 1), |q.coeff (k + 1)| ≤ cn n q := by
    rw [sum_range_succ, hzero, abs_zero, add_zero, cn, sum_range_succ']
    linarith [abs_nonneg (q.coeff 0)]
  calc cn n q.derivative ≤ ∑ k ∈ range (n + 1), n * |q.coeff (k + 1)| := sum_le_sum h1
    _ = n * ∑ k ∈ range (n + 1), |q.coeff (k + 1)| := by rw [mul_sum]
    _ ≤ n * cn n q := by gcongr

/-! ### Uniform invertibility of the Remez system near the nodes -/

theorem remezSystem_apply {n : ℕ} (x : Fin (n + 2) → ℝ) (v : (Fin (n + 1) → ℝ) × ℝ)
    (j : Fin (n + 2)) :
    remezSystem x v j = ∑ k : Fin (n + 1), x j ^ (k : ℕ) * v.1 k + (-1) ^ (j : ℕ) * v.2 := rfl

theorem continuous_remezSystem {n : ℕ} :
    Continuous fun z : (Fin (n + 2) → ℝ) × ((Fin (n + 1) → ℝ) × ℝ) => remezSystem z.1 z.2 := by
  refine continuous_pi fun j => ?_
  simp only [remezSystem_apply]
  refine Continuous.add (continuous_finsetSum _ fun k _ => ?_) ?_
  · exact ((continuous_apply j).comp continuous_fst).pow _ |>.mul
      ((continuous_apply k).comp (continuous_fst.comp continuous_snd))
  · exact continuous_const.mul (continuous_snd.comp continuous_snd)

/-- Near strictly increasing nodes `xs`, the Remez system is uniformly invertible:
`c ‖v‖ ≤ ‖S(x) v‖`. -/
theorem remez_lower {n : ℕ} {xs : Fin (n + 2) → ℝ} (hxs : StrictMono xs) :
    ∃ ρ > 0, ∃ c > 0, ∀ x : Fin (n + 2) → ℝ, (∀ j, |x j - xs j| ≤ ρ) →
      StrictMono x ∧ ∀ v, c * ‖v‖ ≤ ‖remezSystem x v‖ := by
  -- a third of the smallest gap
  set gap := Finset.univ.inf' ⟨0, mem_univ _⟩ fun j : Fin (n + 1) => xs j.succ - xs j.castSucc
  have hgap : 0 < gap := (Finset.lt_inf'_iff _).mpr fun j _ =>
    sub_pos.mpr (hxs Fin.castSucc_lt_succ)
  set ρ := gap / 3 with hρdef
  have hρ : 0 < ρ := by positivity
  have hmono : ∀ x : Fin (n + 2) → ℝ, (∀ j, |x j - xs j| ≤ ρ) → StrictMono x := by
    intro x hx
    refine Fin.strictMono_iff_lt_succ.mpr fun j => ?_
    have h1 := (abs_le.mp (hx j.castSucc)).2
    have h2 := (abs_le.mp (hx j.succ)).1
    have h3 : gap ≤ xs j.succ - xs j.castSucc := Finset.inf'_le _ (mem_univ j)
    linarith
  set D := closedBall xs ρ
  set S := sphere (0 : (Fin (n + 1) → ℝ) × ℝ) 1
  have hD : ∀ x ∈ D, ∀ j, |x j - xs j| ≤ ρ := fun x hx j => by
    have := (mem_closedBall_iff_norm.mp hx)
    exact (norm_le_pi_norm (x - xs) j).trans this
  have hDc : IsCompact (D ×ˢ S) := (isCompact_closedBall _ _).prod (isCompact_sphere _ _)
  have hne : (D ×ˢ S).Nonempty := ⟨(xs, (0, 1)), mem_closedBall_self hρ.le, by simp [S]⟩
  obtain ⟨z0, hz0, hmin⟩ := hDc.exists_isMinOn hne
    (continuous_remezSystem.norm.continuousOn)
  set c := ‖remezSystem z0.1 z0.2‖
  have hc : 0 < c := by
    refine norm_pos_iff.mpr fun h0 => ?_
    have hinj := remezSystem_injective (hmono z0.1 (hD z0.1 hz0.1))
    have : z0.2 = 0 := hinj (by rw [h0, map_zero])
    have hs := hz0.2
    rw [this] at hs
    simp [S] at hs
  refine ⟨ρ, hρ, c, hc, fun x hx => ⟨hmono x hx, fun v => ?_⟩⟩
  rcases eq_or_ne v 0 with rfl | hv
  · simp
  · have hvn : 0 < ‖v‖ := norm_pos_iff.mpr hv
    set u := ‖v‖⁻¹ • v
    have hu : u ∈ S := by
      simp only [S, mem_sphere_zero_iff_norm, u, norm_smul, norm_inv, norm_norm]
      field_simp
    have hxD : x ∈ D := by
      rw [mem_closedBall_iff_norm]
      exact (pi_norm_le_iff_of_nonneg hρ.le).mpr fun j => by
        simpa [Real.norm_eq_abs] using hx j
    have hle := hmin (show (x, u) ∈ D ×ˢ S from ⟨hxD, hu⟩)
    simp only [Set.mem_ofPred_eq] at hle
    have hvu : v = ‖v‖ • u := by simp [u, smul_smul, mul_inv_cancel₀ hvn.ne']
    calc c * ‖v‖ ≤ ‖remezSystem x u‖ * ‖v‖ := by gcongr
      _ = ‖remezSystem x v‖ := by
          conv_rhs => rw [hvu, map_smul, norm_smul, norm_norm]
          ring

/-! ### Linearization at a nondegenerate zero -/

/-- A `C¹` function is linear to within half its slope near a point where the slope is nonzero. -/
theorem lin_near {g : ℝ → ℝ} (hg : ContDiff ℝ 1 g) (x0 : ℝ) (hne : deriv g x0 ≠ 0) :
    ∃ δ > 0, ∀ y z, |y - x0| ≤ δ → |z - x0| ≤ δ →
      |g z - g y - deriv g x0 * (z - y)| ≤ |deriv g x0| / 2 * |z - y| := by
  have hc := hg.continuous_deriv le_rfl
  have hd := hg.differentiable one_ne_zero
  obtain ⟨δ', hδ', hball⟩ := Metric.continuous_iff.mp hc x0 (|deriv g x0| / 2)
    (by positivity)
  refine ⟨δ' / 2, by positivity, fun y z hy hz => ?_⟩
  have hmem : ∀ t, |t - x0| ≤ δ' / 2 → t ∈ Set.Icc (x0 - δ' / 2) (x0 + δ' / 2) := fun t ht => by
    rw [abs_le] at ht; constructor <;> linarith
  have key := (convex_Icc (x0 - δ' / 2) (x0 + δ' / 2)).norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun t => g t - t * deriv g x0) (f' := fun t => deriv g t - deriv g x0)
    (C := |deriv g x0| / 2)
    (fun t _ => ((hd t).hasDerivAt.sub (hasDerivAt_mul_const _)).hasDerivWithinAt)
    (fun t ht => ?_) (hmem y hy) (hmem z hz)
  · simp only [Real.norm_eq_abs] at key
    calc |g z - g y - deriv g x0 * (z - y)|
        = |g z - z * deriv g x0 - (g y - y * deriv g x0)| := by congr 1; ring
      _ ≤ _ := key
  · have h1 : dist t x0 < δ' := by
      have := ht.1; have := ht.2; rw [Real.dist_eq, abs_lt]; constructor <;> linarith
    have := hball t h1
    rw [Real.dist_eq] at this
    rw [Real.norm_eq_abs]; exact this.le

theorem lin_lower {g : ℝ → ℝ} {x0 c δ : ℝ}
    (hA : ∀ y z, |y - x0| ≤ δ → |z - x0| ≤ δ → |g z - g y - c * (z - y)| ≤ |c| / 2 * |z - y|)
    {y z : ℝ} (hy : |y - x0| ≤ δ) (hz : |z - x0| ≤ δ) : |c| / 2 * |z - y| ≤ |g z - g y| := by
  have h1 := hA y z hy hz
  have h2 := abs_sub_abs_le_abs_sub (c * (z - y)) (g z - g y)
  rw [abs_mul, abs_sub_comm (c * (z - y))] at h2
  linarith

theorem lin_unique {g : ℝ → ℝ} {x0 c δ : ℝ}
    (hA : ∀ y z, |y - x0| ≤ δ → |z - x0| ≤ δ → |g z - g y - c * (z - y)| ≤ |c| / 2 * |z - y|)
    {D : ℝ → ℝ} {lam : ℝ} (hlam : lam < |c| / 2)
    (hD : ∀ y z, |y - x0| ≤ δ → |z - x0| ≤ δ → |D z - D y| ≤ lam * |z - y|)
    {y z : ℝ} (hy : |y - x0| ≤ δ) (hz : |z - x0| ≤ δ) (hyz : g y - D y = g z - D z) :
    y = z := by
  have h1 := lin_lower hA hy hz
  have h2 := hD y z hy hz
  have h3 : g z - g y = D z - D y := by linarith
  rw [h3] at h1
  have h4 : |z - y| ≤ 0 := by nlinarith [abs_nonneg (z - y)]
  have := abs_nonpos_iff.mp h4
  linarith

theorem lin_exists {g : ℝ → ℝ} {x0 c δ : ℝ}
    (hA : ∀ y z, |y - x0| ≤ δ → |z - x0| ≤ δ → |g z - g y - c * (z - y)| ≤ |c| / 2 * |z - y|)
    (hc : c ≠ 0) (hδ : 0 ≤ δ) (hg0 : g x0 = 0) {D : ℝ → ℝ}
    (hcont : ContinuousOn (fun t => g t - D t) (Set.Icc (x0 - δ) (x0 + δ)))
    {β : ℝ} (hβ : β < |c| / 2 * δ) (hD : ∀ t, |t - x0| ≤ δ → |D t| ≤ β) :
    ∃ y, |y - x0| ≤ δ ∧ g y = D y := by
  have hp : |(x0 + δ) - x0| ≤ δ := by rw [add_sub_cancel_left, abs_of_nonneg hδ]
  have hm : |(x0 - δ) - x0| ≤ δ := by rw [sub_sub_cancel_left, abs_neg, abs_of_nonneg hδ]
  have h0 : |x0 - x0| ≤ δ := by simpa using hδ
  have e1 := hA x0 (x0 + δ) h0 hp
  have e2 := hA x0 (x0 - δ) h0 hm
  have d1 := hD _ hp
  have d2 := hD _ hm
  rw [hg0, show x0 + δ - x0 = δ by ring, abs_of_nonneg hδ] at e1
  rw [hg0, show x0 - δ - x0 = -δ by ring, abs_neg, abs_of_nonneg hδ] at e2
  rw [abs_le] at e1 e2 d1 d2
  have hab : x0 - δ ≤ x0 + δ := by linarith
  have hmem : ∀ y ∈ Set.Icc (x0 - δ) (x0 + δ), |y - x0| ≤ δ := fun y hy =>
    abs_le.mpr ⟨by linarith [hy.1], by linarith [hy.2]⟩
  rcases lt_or_gt_of_ne hc with hneg | hpos
  · rw [abs_of_neg hneg] at e1 e2 hβ
    obtain ⟨y, hy, hy0⟩ := intermediate_value_Icc' hab hcont
      (show (0 : ℝ) ∈ Set.Icc _ _ from ⟨by linarith, by linarith⟩)
    exact ⟨y, hmem y hy, by simpa [sub_eq_zero] using hy0⟩
  · rw [abs_of_pos hpos] at e1 e2 hβ
    obtain ⟨y, hy, hy0⟩ := intermediate_value_Icc hab hcont
      (show (0 : ℝ) ∈ Set.Icc _ _ from ⟨by linarith, by linarith⟩)
    exact ⟨y, hmem y hy, by simpa [sub_eq_zero] using hy0⟩

/-- The second-order bound at a critical point: `|e(y) − e(x₀)| ≤ 3 (|c|/2) |y − x₀|²`. -/
theorem lin_taylor {g : ℝ → ℝ} {x0 c δ : ℝ}
    (hA : ∀ y z, |y - x0| ≤ δ → |z - x0| ≤ δ → |g z - g y - c * (z - y)| ≤ |c| / 2 * |z - y|)
    (hg0 : g x0 = 0) {e : ℝ → ℝ} (he : ∀ t, |t - x0| ≤ δ → HasDerivAt e (g t) t) {y : ℝ}
    (hy : |y - x0| ≤ δ) : |e y - e x0| ≤ 3 * (|c| / 2) * |y - x0| ^ 2 := by
  have hsub : ∀ t ∈ uIcc x0 y, |t - x0| ≤ |y - x0| := fun t ht => abs_sub_left_of_mem_uIcc ht
  have h0 : |x0 - x0| ≤ δ := by simpa using (abs_nonneg _).trans hy
  have key := (convex_uIcc x0 y).norm_image_sub_le_of_norm_hasDerivWithin_le (f := e) (f' := g)
    (C := 3 * (|c| / 2) * |y - x0|)
    (fun t ht => (he t ((hsub t ht).trans hy)).hasDerivWithinAt)
    (fun t ht => ?_) left_mem_uIcc right_mem_uIcc
  · simp only [Real.norm_eq_abs] at key
    calc |e y - e x0| ≤ _ := key
      _ = _ := by ring
  · have ht' := hsub t ht
    have h1 := hA x0 t h0 (ht'.trans hy)
    rw [hg0] at h1
    have h2 : |g t| ≤ |g t - 0 - c * (t - x0)| + |c * (t - x0)| := by
      calc |g t| = |(g t - 0 - c * (t - x0)) + c * (t - x0)| := by congr 1; ring
        _ ≤ _ := abs_add_le _ _
    rw [abs_mul] at h2
    have h3 := mul_le_mul_of_nonneg_left ht' (abs_nonneg c)
    rw [Real.norm_eq_abs]
    linarith

/-! ### Polynomial bounds -/

theorem abs_le_of_near {t x0 δ R : ℝ} (ht : |t - x0| ≤ δ) (h : |x0| + δ ≤ R) : |t| ≤ R := by
  have := abs_sub_abs_le_abs_sub t x0
  linarith

theorem deriv_eval_bound {d : ℝ[X]} {n : ℕ} (hd : d.natDegree ≤ n) {R : ℝ} (hR : 1 ≤ R)
    {t : ℝ} (ht : |t| ≤ R) : |d.derivative.eval t| ≤ R ^ n * n * cn n d := by
  have h1 := eval_bound (natDegree_derivative_le' hd) hR ht
  have h2 := cn_derivative hd
  have : 0 ≤ R ^ n := by positivity
  calc _ ≤ R ^ n * cn n d.derivative := h1
    _ ≤ R ^ n * (n * cn n d) := by gcongr
    _ = _ := by ring

theorem deriv2_eval_bound {d : ℝ[X]} {n : ℕ} (hd : d.natDegree ≤ n) {R : ℝ} (hR : 1 ≤ R)
    {t : ℝ} (ht : |t| ≤ R) :
    |d.derivative.derivative.eval t| ≤ R ^ n * (n * n) * cn n d := by
  have hd' := natDegree_derivative_le' hd
  have h1 := eval_bound (natDegree_derivative_le' hd') hR ht
  have h2 := cn_derivative hd'
  have h3 := cn_derivative hd
  have : 0 ≤ R ^ n := by positivity
  calc _ ≤ R ^ n * cn n d.derivative.derivative := h1
    _ ≤ R ^ n * (n * (n * cn n d)) := by gcongr; exact h2.trans (by gcongr)
    _ = _ := by ring

theorem deriv_lip {d : ℝ[X]} {n : ℕ} (hd : d.natDegree ≤ n) {R : ℝ} (hR : 1 ≤ R) {x0 δ : ℝ}
    (hRx : |x0| + δ ≤ R) {y z : ℝ} (hy : |y - x0| ≤ δ) (hz : |z - x0| ≤ δ) :
    |d.derivative.eval z - d.derivative.eval y| ≤ R ^ n * (n * n) * cn n d * |z - y| := by
  have hmem : ∀ t, |t - x0| ≤ δ → t ∈ Set.Icc (x0 - δ) (x0 + δ) := fun t ht => by
    rw [abs_le] at ht; constructor <;> linarith
  have key := (convex_Icc (x0 - δ) (x0 + δ)).norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun t => d.derivative.eval t) (f' := fun t => d.derivative.derivative.eval t)
    (C := R ^ n * (n * n) * cn n d)
    (fun t _ => (d.derivative.hasDerivAt t).hasDerivWithinAt)
    (fun t ht => by
      rw [Real.norm_eq_abs]
      exact deriv2_eval_bound hd hR (abs_le_of_near
        (abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩) hRx))
    (hmem y hy) (hmem z hz)
  simpa only [Real.norm_eq_abs] using key

/-! ### The Remez step -/

/-- The polynomial `∑_{k ≤ n} b_k x^k` of 3.11.5. -/
noncomputable def remezPoly {n : ℕ} (b : Fin (n + 1) → ℝ) : ℝ[X] :=
  ∑ k : Fin (n + 1), C (b k) * X ^ (k : ℕ)

theorem remezPoly_natDegree {n : ℕ} (b : Fin (n + 1) → ℝ) : (remezPoly b).natDegree ≤ n := by
  refine natDegree_sum_le_of_forall_le _ _ fun k _ => ?_
  refine (natDegree_C_mul_le _ _).trans ?_
  rw [natDegree_X_pow]; exact Nat.lt_succ_iff.mp k.isLt

theorem remezPoly_coeff {n : ℕ} (b : Fin (n + 1) → ℝ) (k : Fin (n + 1)) :
    (remezPoly b).coeff k = b k := by
  simp [remezPoly, finsetSum_coeff, Fin.val_inj]

theorem remezPoly_eval {n : ℕ} (b : Fin (n + 1) → ℝ) (t : ℝ) :
    (remezPoly b).eval t = ∑ k : Fin (n + 1), t ^ (k : ℕ) * b k := by
  simp only [remezPoly, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X]
  exact sum_congr rfl fun _ _ => mul_comm _ _

/-- The Remez system 3.11.5 in polynomial form: `p_new(x_j) + (−1)^j E = f(x_j)`. -/
theorem remez_step_iff {n : ℕ} (x : Fin (n + 2) → ℝ) (f : ℝ → ℝ) (v : (Fin (n + 1) → ℝ) × ℝ) :
    remezSystem x v = (fun j => f (x j)) ↔
      ∀ j, (remezPoly v.1).eval (x j) + (-1) ^ (j : ℕ) * v.2 = f (x j) := by
  simp only [funext_iff, remezSystem_apply, remezPoly_eval]

theorem remezSystem_coeff {n : ℕ} (x : Fin (n + 2) → ℝ) {q : ℝ[X]} (hq : q.natDegree ≤ n)
    (m : ℝ) (j : Fin (n + 2)) :
    remezSystem x (fun k : Fin (n + 1) => q.coeff k, m) j = q.eval (x j) + (-1) ^ (j : ℕ) * m := by
  rw [remezSystem_apply, eval_eq_sum_range' (Nat.lt_succ_of_le hq),
    ← Fin.sum_univ_eq_sum_range (fun i => q.coeff i * x j ^ i)]
  exact congrArg (· + _) (sum_congr rfl fun _ _ => mul_comm _ _)

/-- DLMF 3.11.3–3.11.5: the new coefficients are `a_k + δa_k` with
`∑ x_j^k δa_k = (−1)^j (m_j − m)`, `m_j = (−1)^j εₙ(x_j)`. -/
theorem remez_step_iff_delta {n : ℕ} (x : Fin (n + 2) → ℝ) (f : ℝ → ℝ) {p : ℝ[X]}
    (hp : p.natDegree ≤ n) (b : Fin (n + 1) → ℝ) (m : ℝ) :
    remezSystem x (b, m) = (fun j => f (x j)) ↔ ∀ j : Fin (n + 2),
      ∑ k : Fin (n + 1), x j ^ (k : ℕ) * (b k - p.coeff k) =
        (-1) ^ (j : ℕ) * ((-1) ^ (j : ℕ) * (f (x j) - p.eval (x j)) - m) := by
  have hs : ∀ j, ∑ k : Fin (n + 1), x j ^ (k : ℕ) * (b k - p.coeff k) =
      ∑ k : Fin (n + 1), x j ^ (k : ℕ) * b k - p.eval (x j) := fun j => by
    have := remezSystem_coeff x hp 0 j
    rw [remezSystem_apply] at this
    simp only [mul_zero, add_zero] at this
    simp only [mul_sub, sum_sub_distrib, this]
  simp only [funext_iff, remezSystem_apply, hs]
  refine forall_congr' fun j => ?_
  have h1 : ((-1 : ℝ) ^ (j : ℕ)) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; simp
  constructor <;> intro h
  · linear_combination h - (f (x j) - p.eval (x j)) * h1
  · linear_combination h + (f (x j) - p.eval (x j)) * h1

theorem cn_remezPoly_sub {n : ℕ} (b : Fin (n + 1) → ℝ) (q : ℝ[X]) :
    cn n (remezPoly b - q) ≤ (n + 1) * ‖b - fun k : Fin (n + 1) => q.coeff k‖ := by
  rw [cn, ← Fin.sum_univ_eq_sum_range (fun k => |(remezPoly b - q).coeff k|)]
  calc ∑ k : Fin (n + 1), |(remezPoly b - q).coeff k|
      ≤ ∑ _k : Fin (n + 1), ‖b - fun k : Fin (n + 1) => q.coeff k‖ :=
        sum_le_sum fun k _ => by
          rw [coeff_sub, remezPoly_coeff]
          simpa [Real.norm_eq_abs] using norm_le_pi_norm (b - fun k : Fin (n + 1) => q.coeff k) k
    _ = _ := by simp [nsmul_eq_mul]

/-! ### Local quadratic convergence -/

/-- DLMF §3.11(i): "The iterative process converges locally and quadratically." Near the
equioscillation nodes `xs` of `p*` (interior extrema nondegenerate, endpoints fixed), for every
`p` close to `p*` the derivative `f′ − p′` has exactly one zero within `δ` of each interior node,
and the Remez update `(p_new, E)` (3.11.5 at these nodes) satisfies
`‖p_new − p*‖ ≤ K ‖p − p*‖²` and `|E − m*| ≤ K ‖p − p*‖²`. -/
theorem dlmf_3_11_i_remez_local {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) {n : ℕ} {ps : ℝ[X]}
    (hps : ps.natDegree ≤ n) {ms : ℝ} {xs : Fin (n + 2) → ℝ} (hxs : StrictMono xs)
    (heq : ∀ j, f (xs j) - ps.eval (xs j) = (-1) ^ (j : ℕ) * ms)
    (hd1 : ∀ j : Fin (n + 2), j ≠ 0 → j ≠ Fin.last _ →
      deriv f (xs j) = ps.derivative.eval (xs j))
    (hd2 : ∀ j : Fin (n + 2), j ≠ 0 → j ≠ Fin.last _ →
      deriv (deriv f) (xs j) ≠ ps.derivative.derivative.eval (xs j)) :
    ∃ η > 0, ∃ δ > 0, ∃ K ≥ 0, ∀ p : ℝ[X], p.natDegree ≤ n → cn n (p - ps) ≤ η →
      (∀ j : Fin (n + 2), j ≠ 0 → j ≠ Fin.last _ →
        ∃! y, |y - xs j| ≤ δ ∧ deriv f y = p.derivative.eval y) ∧
      ∀ x : Fin (n + 2) → ℝ, x 0 = xs 0 → x (Fin.last _) = xs (Fin.last _) →
        (∀ j : Fin (n + 2), j ≠ 0 → j ≠ Fin.last _ →
          |x j - xs j| ≤ δ ∧ deriv f (x j) = p.derivative.eval (x j)) →
        StrictMono x ∧ ∀ v, remezSystem x v = (fun j => f (x j)) →
          cn n (remezPoly v.1 - ps) ≤ K * cn n (p - ps) ^ 2 ∧
          |v.2 - ms| ≤ K * cn n (p - ps) ^ 2 := by
  -- `g = ε*′`, the derivative of the error `ε* = f − p*`
  set g : ℝ → ℝ := fun y => deriv f y - ps.derivative.eval y with hgdef
  have hfd : Differentiable ℝ f := hf.differentiable (by norm_num)
  have hf1 : ContDiff ℝ 1 (deriv f) := hf.deriv'
  have hpc : ∀ q : ℝ[X], ContDiff ℝ 1 (fun y => q.eval y) := fun q =>
    contDiff_aeval q 1
  have hg : ContDiff ℝ 1 g := hf1.sub (hpc _)
  have hgd : ∀ y, deriv g y = deriv (deriv f) y - ps.derivative.derivative.eval y := fun y =>
    (((hf1.differentiable one_ne_zero) y).hasDerivAt.sub (ps.derivative.hasDerivAt y)).deriv
  have he : ∀ t, HasDerivAt (fun y => f y - ps.eval y) (g t) t := fun t =>
    (hfd t).hasDerivAt.sub (ps.hasDerivAt t)
  have hgx : ∀ j : Fin (n + 2), j ≠ 0 → j ≠ Fin.last _ → g (xs j) = 0 := fun j h0 hl => by
    simp only [g, hd1 j h0 hl, sub_self]
  have hgx' : ∀ j : Fin (n + 2), j ≠ 0 → j ≠ Fin.last _ → deriv g (xs j) ≠ 0 :=
    fun j h0 hl => by rw [hgd]; exact sub_ne_zero.mpr (hd2 j h0 hl)
  -- local linearization at each interior node
  have hloc : ∀ j : Fin (n + 2), ∃ δ > 0, j ≠ 0 → j ≠ Fin.last _ → ∀ y z, |y - xs j| ≤ δ →
      |z - xs j| ≤ δ →
      |g z - g y - deriv g (xs j) * (z - y)| ≤ |deriv g (xs j)| / 2 * |z - y| := by
    intro j
    by_cases hj : j ≠ 0 ∧ j ≠ Fin.last _
    · obtain ⟨δ, hδ, h⟩ := lin_near hg (xs j) (hgx' j hj.1 hj.2)
      exact ⟨δ, hδ, fun _ _ => h⟩
    · exact ⟨1, one_pos, fun h0 hl => absurd ⟨h0, hl⟩ hj⟩
  choose δf hδf hA using hloc
  set μ := univ.inf' univ_nonempty fun j : Fin (n + 2) =>
    if j ≠ 0 ∧ j ≠ Fin.last _ then |deriv g (xs j)| / 2 else 1 with hμdef
  have hμ : 0 < μ := (lt_inf'_iff _).mpr fun j _ => by
    split_ifs with hj
    · exact half_pos (abs_pos.mpr (hgx' j hj.1 hj.2))
    · exact one_pos
  have hμj : ∀ j : Fin (n + 2), j ≠ 0 → j ≠ Fin.last _ → μ ≤ |deriv g (xs j)| / 2 :=
    fun j h0 hl => (inf'_le _ (mem_univ j)).trans (by simp [h0, hl])
  set M := univ.sup' univ_nonempty fun j : Fin (n + 2) => |deriv g (xs j)| / 2 with hMdef
  have hMj : ∀ j, |deriv g (xs j)| / 2 ≤ M := fun j =>
    le_sup' (fun j : Fin (n + 2) => |deriv g (xs j)| / 2) (mem_univ j)
  have hM : 0 ≤ M := (by positivity : (0 : ℝ) ≤ |deriv g (xs 0)| / 2).trans (hMj 0)
  obtain ⟨ρ, hρ, c, hc, hlow⟩ := remez_lower hxs
  set δ := min (univ.inf' univ_nonempty δf) ρ with hδdef
  have hδ : 0 < δ := lt_min ((lt_inf'_iff _).mpr fun j _ => hδf j) hρ
  have hδj : ∀ j, δ ≤ δf j := fun j => (min_le_left _ _).trans (inf'_le _ (mem_univ j))
  have hδρ : δ ≤ ρ := min_le_right _ _
  set A := univ.sup' univ_nonempty fun j : Fin (n + 2) => |xs j| with hAdef
  have hAj : ∀ j, |xs j| ≤ A := fun j => le_sup' (fun j : Fin (n + 2) => |xs j|) (mem_univ j)
  have hA0 : 0 ≤ A := (abs_nonneg _).trans (hAj 0)
  set R := 1 + A + δ with hRdef
  have hR : 1 ≤ R := by linarith
  have hRj : ∀ j, |xs j| + δ ≤ R := fun j => by linarith [hAj j]
  set L := R ^ n * ((n : ℝ) * n + n + 1) with hLdef
  have hRn : 0 < R ^ n := by positivity
  have hL : 0 < L := by positivity
  set η := μ * min δ 1 / (2 * L) with hηdef
  have hη : 0 < η := by positivity
  set K0 := 3 * M * (R ^ n * n / μ) ^ 2 / c with hK0def
  have hK0 : 0 ≤ K0 := by positivity
  refine ⟨η, hη, δ, hδ, (n + 1) * K0 + K0, by positivity, fun p hp hpη => ?_⟩
  set d := p - ps with hd_def
  have hd : d.natDegree ≤ n := (natDegree_sub_le _ _).trans (max_le hp hps)
  set γ := cn n d with hγdef
  have hγ : 0 ≤ γ := cn_nonneg _ _
  have hLγ : L * γ < μ * min δ 1 := by
    have h1 : L * γ ≤ L * η := mul_le_mul_of_nonneg_left hpη hL.le
    have h2 : L * η = μ * min δ 1 / 2 := by rw [hηdef]; field_simp
    have h3 : 0 < μ * min δ 1 := by positivity
    linarith
  have hmin1 : μ * min δ 1 ≤ μ := mul_le_of_le_one_right hμ.le (min_le_right _ _)
  have hminδ : μ * min δ 1 ≤ μ * δ := mul_le_mul_of_nonneg_left (min_le_left _ _) hμ.le
  have hn1 : R ^ n * n * γ ≤ L * γ := by
    refine mul_le_mul_of_nonneg_right ?_ hγ
    rw [hLdef]
    exact mul_le_mul_of_nonneg_left (by nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]) hRn.le
  have hn2 : R ^ n * (n * n) * γ ≤ L * γ := by
    refine mul_le_mul_of_nonneg_right ?_ hγ
    rw [hLdef]
    exact mul_le_mul_of_nonneg_left (by nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]) hRn.le
  -- the critical-point equation in terms of `g`
  have hcrit : ∀ y, deriv f y = p.derivative.eval y ↔ g y = d.derivative.eval y := fun y => by
    simp only [g, d, derivative_sub, eval_sub]
    constructor <;> intro h <;> linarith
  have hA' : ∀ j : Fin (n + 2), j ≠ 0 → j ≠ Fin.last _ → ∀ y z, |y - xs j| ≤ δ →
      |z - xs j| ≤ δ →
      |g z - g y - deriv g (xs j) * (z - y)| ≤ |deriv g (xs j)| / 2 * |z - y| :=
    fun j h0 hl y z hy hz => hA j h0 hl y z (hy.trans (hδj j)) (hz.trans (hδj j))
  have hDb : ∀ j : Fin (n + 2), ∀ t, |t - xs j| ≤ δ → |d.derivative.eval t| ≤ R ^ n * n * γ :=
    fun j t ht => deriv_eval_bound hd hR (abs_le_of_near ht (hRj j))
  refine ⟨fun j h0 hl => ?_, fun x hx0 hxl hx => ?_⟩
  · -- the new nodes: existence and uniqueness
    have hμc := hμj j h0 hl
    obtain ⟨y, hy, hgy⟩ := lin_exists (hA' j h0 hl) (hgx' j h0 hl) hδ.le (hgx j h0 hl)
      (D := fun t => d.derivative.eval t)
      (hg.continuous.sub d.derivative.continuous).continuousOn (β := R ^ n * n * γ)
      (by nlinarith) (hDb j)
    refine ⟨y, ⟨hy, (hcrit y).mpr hgy⟩, fun z ⟨hz, hfz⟩ => ?_⟩
    exact lin_unique (hA' j h0 hl) (lam := R ^ n * (n * n) * γ) (by linarith)
      (fun y z hy hz => deriv_lip hd hR (hRj j) hy hz) hz hy
      (by simp only [(hcrit z).mp hfz, hgy, sub_self])
  · -- the quadratic bound
    have hxj : ∀ j : Fin (n + 2), |x j - xs j| ≤ δ := fun j => by
      by_cases h0 : j = 0
      · subst h0; rw [hx0, sub_self, abs_zero]; exact hδ.le
      by_cases hl : j = Fin.last _
      · subst hl; rw [hxl, sub_self, abs_zero]; exact hδ.le
      exact (hx j h0 hl).1
    obtain ⟨hmono, hcv⟩ := hlow x fun j => (hxj j).trans hδρ
    refine ⟨hmono, fun v hv => ?_⟩
    have hr : ∀ j, remezSystem x (v - (fun k : Fin (n + 1) => ps.coeff k, ms)) j =
        (f (x j) - ps.eval (x j)) - (f (xs j) - ps.eval (xs j)) := fun j => by
      rw [map_sub, Pi.sub_apply, hv, remezSystem_coeff x hps ms j, heq j]
      ring
    have hrb : ∀ j, |(f (x j) - ps.eval (x j)) - (f (xs j) - ps.eval (xs j))| ≤
        3 * M * (R ^ n * n * γ / μ) ^ 2 := fun j => by
      by_cases hj : j ≠ 0 ∧ j ≠ Fin.last _
      · obtain ⟨hxj', hfx⟩ := hx j hj.1 hj.2
        have hlow' := lin_lower (hA' j hj.1 hj.2) (y := xs j) (z := x j)
          (by simpa using hδ.le) hxj'
        rw [hgx j hj.1 hj.2, sub_zero, (hcrit _).mp hfx] at hlow'
        have hdist : |x j - xs j| ≤ R ^ n * n * γ / μ := by
          rw [le_div_iff₀ hμ]
          have h1 := hDb j (x j) hxj'
          have h2 := mul_le_mul_of_nonneg_right (hμj j hj.1 hj.2) (abs_nonneg (x j - xs j))
          linarith
        have ht := lin_taylor (hA' j hj.1 hj.2) (hgx j hj.1 hj.2)
          (e := fun y => f y - ps.eval y) (fun t _ => he t) hxj'
        calc _ ≤ 3 * (|deriv g (xs j)| / 2) * |x j - xs j| ^ 2 := ht
          _ ≤ 3 * M * (R ^ n * n * γ / μ) ^ 2 :=
            mul_le_mul (by linarith [hMj j]) (pow_le_pow_left₀ (abs_nonneg _) hdist 2)
              (by positivity) (by linarith)
      · have hxe : x j = xs j := by
          by_cases h0 : j = 0
          · rw [h0, hx0]
          · have hl : j = Fin.last _ := by
              by_contra hl; exact hj ⟨h0, hl⟩
            rw [hl, hxl]
        rw [hxe, sub_self, abs_zero]; positivity
    have hrn : ‖remezSystem x (v - (fun k : Fin (n + 1) => ps.coeff k, ms))‖ ≤
        3 * M * (R ^ n * n * γ / μ) ^ 2 :=
      (pi_norm_le_iff_of_nonneg ((abs_nonneg _).trans (hrb 0))).mpr fun j => by
        rw [Real.norm_eq_abs, hr j]; exact hrb j
    have hvv : ‖v - (fun k : Fin (n + 1) => ps.coeff k, ms)‖ ≤ K0 * γ ^ 2 := by
      have h1 := (hcv _).trans hrn
      rw [show K0 * γ ^ 2 = 3 * M * (R ^ n * n * γ / μ) ^ 2 / c by rw [hK0def]; ring,
        le_div_iff₀ hc]
      linarith
    have h1 : ‖v.1 - fun k : Fin (n + 1) => ps.coeff k‖ ≤
        ‖v - (fun k : Fin (n + 1) => ps.coeff k, ms)‖ := by
      simpa using norm_fst_le (v - (fun k : Fin (n + 1) => ps.coeff k, ms))
    have h2 : |v.2 - ms| ≤ ‖v - (fun k : Fin (n + 1) => ps.coeff k, ms)‖ := by
      simpa [Real.norm_eq_abs] using norm_snd_le (v - (fun k : Fin (n + 1) => ps.coeff k, ms))
    have hKγ : 0 ≤ K0 * γ ^ 2 := mul_nonneg hK0 (sq_nonneg γ)
    have hexp : ((n + 1) * K0 + K0) * γ ^ 2 = (n + 1) * (K0 * γ ^ 2) + K0 * γ ^ 2 := by ring
    have hn0 : (0 : ℝ) ≤ n + 1 := by positivity
    have h3 := mul_le_mul_of_nonneg_left (h1.trans hvv) hn0
    have h4 := mul_nonneg hn0 hKγ
    have h5 := cn_remezPoly_sub v.1 ps
    constructor
    · rw [hexp]; linarith
    · rw [hexp]; linarith

/-- DLMF §3.11(i): iterating the Remez step from a starting polynomial close enough to `p*`,
the errors decrease quadratically (and at least geometrically), and the levelled errors `E`
converge to `m*`. -/
theorem dlmf_3_11_i_remez_converges {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) {n : ℕ} {ps : ℝ[X]}
    (hps : ps.natDegree ≤ n) {ms : ℝ} {xs : Fin (n + 2) → ℝ} (hxs : StrictMono xs)
    (heq : ∀ j, f (xs j) - ps.eval (xs j) = (-1) ^ (j : ℕ) * ms)
    (hd1 : ∀ j : Fin (n + 2), j ≠ 0 → j ≠ Fin.last _ →
      deriv f (xs j) = ps.derivative.eval (xs j))
    (hd2 : ∀ j : Fin (n + 2), j ≠ 0 → j ≠ Fin.last _ →
      deriv (deriv f) (xs j) ≠ ps.derivative.derivative.eval (xs j)) :
    ∃ η > 0, ∃ δ > 0, ∃ K ≥ 0, ∀ (p : ℕ → ℝ[X]) (x : ℕ → Fin (n + 2) → ℝ)
      (v : ℕ → (Fin (n + 1) → ℝ) × ℝ), (p 0).natDegree ≤ n → cn n (p 0 - ps) ≤ η →
      (∀ k, x k 0 = xs 0 ∧ x k (Fin.last _) = xs (Fin.last _) ∧
        ∀ j : Fin (n + 2), j ≠ 0 → j ≠ Fin.last _ →
          |x k j - xs j| ≤ δ ∧ deriv f (x k j) = (p k).derivative.eval (x k j)) →
      (∀ k, remezSystem (x k) (v k) = fun j => f (x k j)) →
      (∀ k, p (k + 1) = remezPoly (v k).1) →
      (∀ k, cn n (p (k + 1) - ps) ≤ K * cn n (p k - ps) ^ 2) ∧
      (∀ k, cn n (p k - ps) ≤ cn n (p 0 - ps) * (1 / 2) ^ k) ∧
      Tendsto (fun k => cn n (p k - ps)) atTop (𝓝 0) ∧
      Tendsto (fun k => (v k).2) atTop (𝓝 ms) := by
  obtain ⟨η0, hη0, δ, hδ, K, hK, h⟩ := dlmf_3_11_i_remez_local hf hps hxs heq hd1 hd2
  refine ⟨min η0 (1 / (2 * K + 1)), lt_min hη0 (by positivity), δ, hδ, K, hK,
    fun p x v hp0 hη hx hv hpv => ?_⟩
  set a := fun k => cn n (p k - ps) with hadef
  have ha0 : ∀ k, 0 ≤ a k := fun k => cn_nonneg _ _
  have hstep : ∀ k, (p k).natDegree ≤ n → a k ≤ min η0 (1 / (2 * K + 1)) →
      a (k + 1) ≤ K * a k ^ 2 ∧ |(v k).2 - ms| ≤ K * a k ^ 2 ∧ a (k + 1) ≤ a k / 2 := by
    intro k hpk hak
    obtain ⟨-, hq⟩ := h (p k) hpk (hak.trans (min_le_left _ _))
    obtain ⟨hx0, hxl, hxi⟩ := hx k
    obtain ⟨-, hb⟩ := hq (x k) hx0 hxl hxi
    obtain ⟨hb1, hb2⟩ := hb (v k) (hv k)
    have hb1' : a (k + 1) ≤ K * a k ^ 2 := by simp only [hadef, hpv k]; exact hb1
    refine ⟨hb1', hb2, ?_⟩
    have h1 : a k * (2 * K + 1) ≤ 1 := by
      have := hak.trans (min_le_right _ _)
      rwa [le_div_iff₀ (by positivity)] at this
    nlinarith [ha0 k]
  have hinv : ∀ k, (p k).natDegree ≤ n ∧ a k ≤ min η0 (1 / (2 * K + 1)) ∧
      a k ≤ a 0 * (1 / 2) ^ k := by
    intro k
    induction k with
    | zero => exact ⟨hp0, hη, by simp⟩
    | succ k ih =>
      obtain ⟨hpk, hak, hgeo⟩ := ih
      have := (hstep k hpk hak).2.2
      refine ⟨hpv k ▸ remezPoly_natDegree _, by linarith [ha0 k], ?_⟩
      rw [pow_succ]; linarith
  have hlim : Tendsto a atTop (𝓝 0) := squeeze_zero ha0 (fun k => (hinv k).2.2) (by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num)).const_mul (a 0))
  refine ⟨fun k => (hstep k (hinv k).1 (hinv k).2.1).1, fun k => (hinv k).2.2, hlim, ?_⟩
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (g := fun k => K * a k ^ 2) (fun _ => norm_nonneg _)
    (fun k => by rw [Real.norm_eq_abs]; exact (hstep k (hinv k).1 (hinv k).2.1).2.1) ?_
  simpa using (hlim.pow 2).const_mul K

end Azurite.DLMF
