/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter1.Section18ODE
import Azurite.DLMF.Chapter1.Section18WeylDef

/-!
# Complex linear second-order ODEs: global existence on an open interval

* Volterra iteration for complex `u″ = W u` with bounded continuous `W` (`cIter`, `cSol`,
  `exists_solution_bounded`).
* `exists_solution_on`: global existence on an open interval `X`, for `W` only continuous on
  `X`. `W` is clamped to compact subintervals and the pieces are glued by uniqueness.
-/

open Set Filter Topology MeasureTheory
open scoped Nat

namespace Azurite.DLMF

/-! ### Volterra iteration for `u″ = W u` with bounded continuous `W : ℝ → ℂ` -/

section Volterra

variable (W : ℝ → ℂ) (a b : ℂ) (x0 : ℝ)

/-- Picard iterates of `u(x) = a + b(x − x₀) + ∫_{x₀}^x (x − t) W(t) u(t) dt`. -/
noncomputable def cIter : ℕ → ℝ → ℂ
  | 0 => fun x => a + b * ((x : ℂ) - x0)
  | n + 1 => fun x => a + b * ((x : ℂ) - x0) + ∫ t in x0..x, ((x : ℂ) - t) * (W t * cIter n t)

noncomputable def cDiff (n : ℕ) (x : ℝ) : ℂ := cIter W a b x0 (n + 1) x - cIter W a b x0 n x

/-- `x ↦ ∫_{x₀}^x (x − t) f(t) dt` is continuous for continuous `f`. -/
theorem continuous_kernel {f : ℝ → ℂ} (hf : Continuous f) :
    Continuous fun x : ℝ => ∫ t in x0..x, ((x : ℂ) - t) * f t := by
  have hG : Continuous fun t : ℝ => (t : ℂ) * f t := Complex.continuous_ofReal.mul hf
  have e : (fun x : ℝ => ∫ t in x0..x, ((x : ℂ) - t) * f t) =
      fun x : ℝ => (x : ℂ) * (∫ t in x0..x, f t) - ∫ t in x0..x, (t : ℂ) * f t := by
    funext x
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_sub
      ((hf.intervalIntegrable _ _).const_mul _) (hG.intervalIntegrable _ _)]
    exact intervalIntegral.integral_congr fun t _ => by ring
  rw [e]
  have c1 : Continuous fun x => ∫ t in x0..x, f t := continuous_iff_continuousAt.mpr fun x =>
    (hf.integral_hasStrictDerivAt x0 x).hasDerivAt.continuousAt
  have c2 : Continuous fun x => ∫ t in x0..x, (t : ℂ) * f t :=
    continuous_iff_continuousAt.mpr fun x =>
      (hG.integral_hasStrictDerivAt x0 x).hasDerivAt.continuousAt
  exact (Complex.continuous_ofReal.mul c1).sub c2

variable {W} (hW : Continuous W)
include hW

theorem continuous_cIter (n : ℕ) : Continuous (cIter W a b x0 n) := by
  induction n with
  | zero => simp only [cIter]; fun_prop
  | succ n ih =>
    simp only [cIter]
    exact (continuous_const.add (continuous_const.mul
      (Complex.continuous_ofReal.sub continuous_const))).add (continuous_kernel x0 (hW.mul ih))

theorem continuous_cDiff (n : ℕ) : Continuous (cDiff W a b x0 n) :=
  (continuous_cIter a b x0 hW (n + 1)).sub (continuous_cIter a b x0 hW n)

omit hW in
theorem cDiff_zero (x : ℝ) :
    cDiff W a b x0 0 x = ∫ t in x0..x, ((x : ℂ) - t) * (W t * cIter W a b x0 0 t) := by
  simp only [cDiff, cIter]; ring

theorem cDiff_succ (n : ℕ) (x : ℝ) :
    cDiff W a b x0 (n + 1) x = ∫ t in x0..x, ((x : ℂ) - t) * (W t * cDiff W a b x0 n t) := by
  have hc : ∀ m, Continuous fun t : ℝ => ((x : ℂ) - t) * (W t * cIter W a b x0 m t) := fun m =>
    (continuous_const.sub Complex.continuous_ofReal).mul (hW.mul (continuous_cIter a b x0 hW m))
  simp only [cDiff]
  rw [show cIter W a b x0 (n + 1 + 1) x - cIter W a b x0 (n + 1) x =
      (∫ t in x0..x, ((x : ℂ) - t) * (W t * cIter W a b x0 (n + 1) t)) -
        ∫ t in x0..x, ((x : ℂ) - t) * (W t * cIter W a b x0 n t) by
      simp only [cIter]; ring,
    ← intervalIntegral.integral_sub ((hc _).intervalIntegrable _ _) ((hc _).intervalIntegrable _ _)]
  exact intervalIntegral.integral_congr fun t _ => by ring

end Volterra

theorem norm_integral_le_pow {g : ℝ → ℂ} (hg : Continuous g) {x0 x C : ℝ} (n : ℕ)
    (hC : ∀ t ∈ uIcc x0 x, ‖g t‖ ≤ C * |t - x0| ^ n) :
    ‖∫ t in x0..x, g t‖ ≤ C * |x - x0| ^ (n + 1) / (n + 1) := by
  have h := abs_integral_le_pow (g := fun t => ‖g t‖) hg.norm n fun t ht => by
    rw [abs_of_nonneg (norm_nonneg _)]; exact hC t ht
  refine (intervalIntegral.norm_integral_le_abs_integral_norm).trans ?_
  exact h

section CSolution

variable {W : ℝ → ℂ} {a b : ℂ} (x0 : ℝ) (hW : Continuous W) {M B : ℝ}
  (hM : ∀ t, ‖W t‖ ≤ M) (hBa : ‖a‖ ≤ B) (hBb : ‖b‖ ≤ B)

include hBa hBb in
theorem norm_cIter_zero_le {L : ℝ} (x : ℝ) (hx : |x - x0| ≤ L) :
    ‖cIter W a b x0 0 x‖ ≤ B * (1 + L) := by
  simp only [cIter]
  have hxc : ‖(x : ℂ) - x0‖ = |x - x0| := by
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  calc ‖a + b * ((x : ℂ) - x0)‖ ≤ ‖a‖ + ‖b‖ * ‖(x : ℂ) - x0‖ := by
        rw [← norm_mul]; exact norm_add_le _ _
    _ ≤ B + B * L := by
        rw [hxc]
        gcongr
        · exact (norm_nonneg _).trans hBb
    _ = B * (1 + L) := by ring

theorem norm_ofReal_sub (x t : ℝ) : ‖(x : ℂ) - t‖ = |x - t| := by
  rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]

include hW hM hBa hBb in
theorem norm_cDiff_le (n : ℕ) {L : ℝ} (hL : 0 ≤ L) :
    ∀ x, |x - x0| ≤ L → ‖cDiff W a b x0 n x‖ ≤
      B * (1 + L) * (M * L) ^ (n + 1) * |x - x0| ^ (n + 1) / (n + 1)! := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  have hB0 : 0 ≤ B := (norm_nonneg _).trans hBa
  induction n with
  | zero =>
    intro x hx
    rw [cDiff_zero]
    have h := norm_integral_le_pow (x0 := x0) (x := x) (C := L * (M * (B * (1 + L))))
      (g := fun t => ((x : ℂ) - t) * (W t * cIter W a b x0 0 t))
      ((continuous_const.sub Complex.continuous_ofReal).mul
        (hW.mul (continuous_cIter a b x0 hW 0)))
      0 fun t ht => by
        rw [pow_zero, mul_one, norm_mul, norm_mul, norm_ofReal_sub]
        have h1 : |x - t| ≤ L := (abs_sub_right_of_mem_uIcc ht).trans hx
        have h2 : |t - x0| ≤ L := (abs_sub_left_of_mem_uIcc ht).trans hx
        gcongr
        · exact hM t
        · exact norm_cIter_zero_le x0 hBa hBb t h2
    refine h.trans (le_of_eq ?_)
    simp only [zero_add, Nat.cast_zero, pow_one, div_one, Nat.factorial_one, Nat.cast_one]
    ring
  | succ n ih =>
    intro x hx
    rw [cDiff_succ a b x0 hW]
    have h := norm_integral_le_pow (x0 := x0) (x := x)
      (C := L * M * (B * (1 + L) * (M * L) ^ (n + 1) / (n + 1)!))
      (g := fun t => ((x : ℂ) - t) * (W t * cDiff W a b x0 n t))
      ((continuous_const.sub Complex.continuous_ofReal).mul (hW.mul (continuous_cDiff a b x0 hW n)))
      (n + 1) fun t ht => by
        rw [norm_mul, norm_mul, norm_ofReal_sub]
        have h1 : |x - t| ≤ L := (abs_sub_right_of_mem_uIcc ht).trans hx
        have h2 : |t - x0| ≤ L := (abs_sub_left_of_mem_uIcc ht).trans hx
        have h3 := ih t h2
        calc |x - t| * (‖W t‖ * ‖cDiff W a b x0 n t‖)
            ≤ L * (M * (B * (1 + L) * (M * L) ^ (n + 1) * |t - x0| ^ (n + 1) / (n + 1)!)) := by
              gcongr
              · exact hM t
          _ = L * M * (B * (1 + L) * (M * L) ^ (n + 1) / (n + 1)!) * |t - x0| ^ (n + 1) := by
              ring
    refine h.trans (le_of_eq ?_)
    rw [Nat.factorial_succ (n + 1)]
    push_cast
    field_simp
    ring

include hW hM hBa hBb in
theorem norm_cDiff_le_bound (n : ℕ) {L : ℝ} (hL : 0 ≤ L) (x : ℝ) (hx : |x - x0| ≤ L) :
    ‖cDiff W a b x0 n x‖ ≤ volterraBound M B L n := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  have hB0 : 0 ≤ B := (norm_nonneg _).trans hBa
  refine (norm_cDiff_le x0 hW hM hBa hBb n hL x hx).trans ?_
  have key : (M * L) ^ (n + 1) * |x - x0| ^ (n + 1) ≤ (M * L * L) ^ (n + 1) := by
    rw [show (M * L * L) ^ (n + 1) = (M * L) ^ (n + 1) * L ^ (n + 1) from mul_pow _ _ _]
    gcongr
  rw [volterraBound]
  calc B * (1 + L) * (M * L) ^ (n + 1) * |x - x0| ^ (n + 1) / (n + 1)!
      = B * (1 + L) * ((M * L) ^ (n + 1) * |x - x0| ^ (n + 1)) / (n + 1)! := by ring
    _ ≤ B * (1 + L) * (M * L * L) ^ (n + 1) / (n + 1)! := by gcongr

/-- The solution `u = lim cIter`. -/
noncomputable def cSol (W : ℝ → ℂ) (a b : ℂ) (x0 x : ℝ) : ℂ :=
  cIter W a b x0 0 x + ∑' n, cDiff W a b x0 n x

include hW hM hBa hBb in
theorem summable_cDiff (x : ℝ) : Summable fun n => cDiff W a b x0 n x :=
  (summable_volterraBound M B |x - x0|).of_norm_bounded fun n =>
    norm_cDiff_le_bound x0 hW hM hBa hBb n (abs_nonneg _) x le_rfl

theorem cIter_eq_sum (n : ℕ) (x : ℝ) :
    cIter W a b x0 n x = cIter W a b x0 0 x + ∑ k ∈ Finset.range n, cDiff W a b x0 k x := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, ← add_assoc, ← ih, cDiff]; ring

include hW hM hBa hBb in
theorem tendsto_cIter (x : ℝ) :
    Tendsto (fun n => cIter W a b x0 n x) atTop (𝓝 (cSol W a b x0 x)) := by
  rw [show (fun n => cIter W a b x0 n x) = fun n => cIter W a b x0 0 x +
    ∑ k ∈ Finset.range n, cDiff W a b x0 k x from funext fun n => cIter_eq_sum x0 n x]
  exact ((summable_cDiff x0 hW hM hBa hBb x).hasSum.tendsto_sum_nat).const_add _

include hW hM hBa hBb in
theorem continuous_cSol : Continuous (cSol W a b x0) := by
  rw [continuous_iff_continuousAt]
  intro p
  set L := |p - x0| + 1
  have hL : 0 ≤ L := by positivity
  set S := {q : ℝ | |q - x0| < L}
  have hS : IsOpen S := isOpen_lt (by fun_prop) continuous_const
  have hp : p ∈ S := by simp [S, L]
  have hc : ContinuousOn (fun q => ∑' n, cDiff W a b x0 n q) S :=
    continuousOn_tsum (fun n => (continuous_cDiff a b x0 hW n).continuousOn)
      (summable_volterraBound M B L) fun n q hq =>
        norm_cDiff_le_bound x0 hW hM hBa hBb n hL q (le_of_lt hq)
  exact (((continuous_cIter a b x0 hW 0).continuousOn.add hc).continuousAt (hS.mem_nhds hp))

include hW hM hBa hBb in
theorem cSol_eq (x : ℝ) : cSol W a b x0 x = a + b * ((x : ℂ) - x0) +
    ∫ t in x0..x, ((x : ℂ) - t) * (W t * cSol W a b x0 t) := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  have hB0 : 0 ≤ B := (norm_nonneg _).trans hBa
  set L := |x - x0|
  set Cb := B * (1 + L) + ∑' k, volterraBound M B L k
  have hbd : ∀ n, ∀ t ∈ uIcc x0 x, ‖cIter W a b x0 n t‖ ≤ Cb := fun n t ht => by
    have htL : |t - x0| ≤ L := abs_sub_left_of_mem_uIcc ht
    rw [cIter_eq_sum x0]
    refine (norm_add_le _ _).trans (add_le_add (norm_cIter_zero_le x0 hBa hBb t htL) ?_)
    refine (norm_sum_le _ _).trans ?_
    refine (Finset.sum_le_sum fun k _ =>
      norm_cDiff_le_bound x0 hW hM hBa hBb k (abs_nonneg _) t htL).trans ?_
    exact (summable_volterraBound M B L).sum_le_tsum _ fun k _ => by
      unfold volterraBound; positivity
  have hlim : Tendsto (fun n => ∫ t in x0..x, ((x : ℂ) - t) * (W t * cIter W a b x0 n t))
      atTop (𝓝 (∫ t in x0..x, ((x : ℂ) - t) * (W t * cSol W a b x0 t))) := by
    refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ => L * (M * Cb))
      (Eventually.of_forall fun n => ((continuous_const.sub Complex.continuous_ofReal).mul
        (hW.mul (continuous_cIter a b x0 hW n))).aestronglyMeasurable) ?_
      intervalIntegrable_const (ae_of_all _ fun t _ => ?_)
    · refine Eventually.of_forall fun n => ae_of_all _ fun t ht => ?_
      have ht' : t ∈ uIcc x0 x := uIoc_subset_uIcc ht
      rw [norm_mul, norm_mul, norm_ofReal_sub]
      have h1 : |x - t| ≤ L := abs_sub_right_of_mem_uIcc ht'
      gcongr
      · exact hM t
      · exact hbd n t ht'
    · exact ((tendsto_cIter x0 hW hM hBa hBb t).const_mul (W t)).const_mul ((x : ℂ) - t)
  have h2 := (tendsto_cIter x0 hW hM hBa hBb x).comp (tendsto_add_atTop_nat 1)
  have h3 : Tendsto (fun n => cIter W a b x0 (n + 1) x) atTop
      (𝓝 (a + b * ((x : ℂ) - x0) + ∫ t in x0..x, ((x : ℂ) - t) * (W t * cSol W a b x0 t))) := by
    simp only [cIter]
    exact hlim.const_add _
  exact tendsto_nhds_unique h2 h3

/-- The derivative `u′ = b + ∫_{x₀}^x W u`. -/
noncomputable def cSolD (W : ℝ → ℂ) (a b : ℂ) (x0 x : ℝ) : ℂ :=
  b + ∫ t in x0..x, W t * cSol W a b x0 t

include hW hM hBa hBb in
theorem hasDerivAt_cSol (x : ℝ) : HasDerivAt (cSol W a b x0) (cSolD W a b x0 x) x := by
  set F : ℝ → ℂ := fun t => W t * cSol W a b x0 t
  have hF : Continuous F := hW.mul (continuous_cSol x0 hW hM hBa hBb)
  have hG : Continuous fun t : ℝ => (t : ℂ) * F t := Complex.continuous_ofReal.mul hF
  have e : cSol W a b x0 = fun y : ℝ => a + b * ((y : ℂ) - x0) +
      ((y : ℂ) * (∫ t in x0..y, F t) - ∫ t in x0..y, (t : ℂ) * F t) := by
    funext y
    rw [cSol_eq x0 hW hM hBa hBb]
    congr 1
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_sub]
    · exact intervalIntegral.integral_congr fun t _ => by simp only [F]; ring
    · exact (continuous_const.mul hF).intervalIntegrable _ _
    · exact hG.intervalIntegrable _ _
  rw [e]
  have h1 := (hF.integral_hasStrictDerivAt x0 x).hasDerivAt
  have h2 := (hG.integral_hasStrictDerivAt x0 x).hasDerivAt
  have hx : HasDerivAt (fun y : ℝ => (y : ℂ)) 1 x := by
    simpa using (hasDerivAt_id x).ofReal_comp
  have h := ((hx.sub_const (x0 : ℂ)).const_mul b).const_add a |>.add ((hx.mul h1).sub h2)
  refine h.congr_deriv ?_
  simp only [cSolD, F]
  ring

include hW hM hBa hBb in
theorem hasDerivAt_cSolD (x : ℝ) :
    HasDerivAt (cSolD W a b x0) (W x * cSol W a b x0 x) x :=
  ((hW.mul (continuous_cSol x0 hW hM hBa hBb)).integral_hasStrictDerivAt x0 x).hasDerivAt.const_add
    b

include hW hM hBa hBb in
theorem cSol_init : cSol W a b x0 x0 = a := by
  rw [cSol_eq x0 hW hM hBa hBb]; simp

theorem cSolD_init : cSolD W a b x0 x0 = b := by simp [cSolD]

/-- Global existence on `ℝ` for bounded continuous `W`. -/
theorem exists_solution_bounded (hW : Continuous W) {M : ℝ} (hM : ∀ t, ‖W t‖ ≤ M) (a b : ℂ)
    (x0 : ℝ) : ∃ u u' : ℝ → ℂ, (∀ x, HasDerivAt u (u' x) x ∧ HasDerivAt u' (W x * u x) x) ∧
      u x0 = a ∧ u' x0 = b := by
  have hBa : ‖a‖ ≤ max ‖a‖ ‖b‖ := le_max_left _ _
  have hBb : ‖b‖ ≤ max ‖a‖ ‖b‖ := le_max_right _ _
  exact ⟨cSol W a b x0, cSolD W a b x0, fun x => ⟨hasDerivAt_cSol x0 hW hM hBa hBb x,
    hasDerivAt_cSolD x0 hW hM hBa hBb x⟩, cSol_init x0 hW hM hBa hBb, cSolD_init x0⟩

end CSolution

/-! ### Existence on an open interval -/

theorem exists_solution_Icc {W : ℝ → ℂ} {α β : ℝ} (hαβ : α ≤ β) (hW : ContinuousOn W (Icc α β))
    (a b : ℂ) (x0 : ℝ) : ∃ u u' : ℝ → ℂ,
      (∀ x ∈ Icc α β, HasDerivAt u (u' x) x ∧ HasDerivAt u' (W x * u x) x) ∧
        u x0 = a ∧ u' x0 = b := by
  set cl : ℝ → ℝ := fun x => max α (min x β)
  have hcl : Continuous cl := continuous_const.max (continuous_id.min continuous_const)
  have hclI : ∀ x, cl x ∈ Icc α β := fun x =>
    ⟨le_max_left _ _, max_le hαβ (min_le_right _ _)⟩
  set W' : ℝ → ℂ := fun x => W (cl x)
  have hW' : Continuous W' := hW.comp_continuous hcl hclI
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hW
  obtain ⟨u, u', hu, h0, h1⟩ := exists_solution_bounded hW' (fun t => hM _ (hclI t)) a b x0
  refine ⟨u, u', fun x hx => ⟨(hu x).1, ?_⟩, h0, h1⟩
  have : cl x = x := by simp only [cl]; rw [min_eq_left hx.2, max_eq_right hx.1]
  have h := (hu x).2
  simp only [W', this] at h
  exact h

/-- **Global existence** for `u″ = W u` on an open interval `X` with `W` continuous on `X`. -/
theorem exists_solution_on {X : Set ℝ} (hX : IsOpen X) (hXc : X.OrdConnected) {W : ℝ → ℂ}
    (hW : ContinuousOn W X) {x0 : ℝ} (hx0 : x0 ∈ X) (a b : ℂ) :
    ∃ u u' : ℝ → ℂ, (∀ x ∈ X, HasDerivAt u (u' x) x ∧ HasDerivAt u' (W x * u x) x) ∧
      u x0 = a ∧ u' x0 = b := by
  have key : ∀ x ∈ X, ∃ αβ : ℝ × ℝ, ∃ UU : (ℝ → ℂ) × (ℝ → ℂ), x ∈ Ioo αβ.1 αβ.2 ∧
      x0 ∈ Ioo αβ.1 αβ.2 ∧ Icc αβ.1 αβ.2 ⊆ X ∧
      (∀ y ∈ Icc αβ.1 αβ.2, HasDerivAt UU.1 (UU.2 y) y ∧ HasDerivAt UU.2 (W y * UU.1 y) y) ∧
      UU.1 x0 = a ∧ UU.2 x0 = b := by
    intro x hx
    obtain ⟨α, β, hα, hβ, hαβ, hK, hx0'⟩ := exists_Ioo_of_isCompact hX isCompact_singleton
      (singleton_subset_iff.mpr hx) hx0
    have hIcc : Icc α β ⊆ X := hXc.out hα hβ
    obtain ⟨U, U', hU, h0, h1⟩ := exists_solution_Icc hαβ.le (hW.mono hIcc) a b x0
    exact ⟨(α, β), (U, U'), hK rfl, hx0', hIcc, hU, h0, h1⟩
  choose! αβ UU hxI hx0I hIX hUU hU0 hU1 using key
  -- two local solutions agree on the overlap
  have agree : ∀ x ∈ X, ∀ y ∈ X, ∀ s ∈ Ioo (αβ x).1 (αβ x).2 ∩ Ioo (αβ y).1 (αβ y).2,
      (UU x).1 s = (UU y).1 s ∧ (UU x).2 s = (UU y).2 s := by
    intro x hx y hy
    set Y := Ioo (αβ x).1 (αβ x).2 ∩ Ioo (αβ y).1 (αβ y).2
    have hYo : IsOpen Y := isOpen_Ioo.inter isOpen_Ioo
    have hYc : Y.OrdConnected := ordConnected_Ioo.inter ordConnected_Ioo
    have hx0Y : x0 ∈ Y := ⟨hx0I x hx, hx0I y hy⟩
    have hYx : ∀ s ∈ Y, s ∈ Icc (αβ x).1 (αβ x).2 := fun s hs => Ioo_subset_Icc_self hs.1
    have hYy : ∀ s ∈ Y, s ∈ Icc (αβ y).1 (αβ y).2 := fun s hs => Ioo_subset_Icc_self hs.2
    have hWY : ContinuousOn W Y := hW.mono fun s hs => hIX x hx (hYx s hs)
    have hz := ode2c_eq_zero_on hYc hWY (w := fun s => (UU x).1 s - (UU y).1 s)
      (w' := fun s => (UU x).2 s - (UU y).2 s)
      (fun s hs => ((hUU x hx s (hYx s hs)).1.sub (hUU y hy s (hYy s hs)).1))
      (fun s hs => ((hUU x hx s (hYx s hs)).2.sub (hUU y hy s (hYy s hs)).2).congr_deriv
        (by ring)) hx0Y (by simp [hU0 x hx, hU0 y hy]) (by simp [hU1 x hx, hU1 y hy])
    intro s hs
    have h1 : (UU x).1 s = (UU y).1 s := sub_eq_zero.mp (hz s hs)
    refine ⟨h1, ?_⟩
    have hev : (UU x).1 =ᶠ[𝓝 s] (UU y).1 :=
      Filter.eventuallyEq_of_mem (hYo.mem_nhds hs) fun t ht => sub_eq_zero.mp (hz t ht)
    exact (hUU x hx s (hYx s hs)).1.unique ((hUU y hy s (hYy s hs)).1.congr_of_eventuallyEq hev)
  set u : ℝ → ℂ := fun x => (UU x).1 x
  set u' : ℝ → ℂ := fun x => (UU x).2 x
  have hloc : ∀ x ∈ X, u =ᶠ[𝓝 x] (UU x).1 ∧ u' =ᶠ[𝓝 x] (UU x).2 := by
    intro x hx
    have hmem : Ioo (αβ x).1 (αβ x).2 ∈ 𝓝 x := isOpen_Ioo.mem_nhds (hxI x hx)
    constructor
    · filter_upwards [hmem] with y hy
      have hyX : y ∈ X := hIX x hx (Ioo_subset_Icc_self hy)
      exact (agree x hx y hyX y ⟨hy, hxI y hyX⟩).1.symm
    · filter_upwards [hmem] with y hy
      have hyX : y ∈ X := hIX x hx (Ioo_subset_Icc_self hy)
      exact (agree x hx y hyX y ⟨hy, hxI y hyX⟩).2.symm
  refine ⟨u, u', fun x hx => ⟨?_, ?_⟩, hU0 x0 hx0, hU1 x0 hx0⟩
  · exact ((hUU x hx x (Ioo_subset_Icc_self (hxI x hx))).1).congr_of_eventuallyEq (hloc x hx).1
  · exact ((hUU x hx x (Ioo_subset_Icc_self (hxI x hx))).2).congr_of_eventuallyEq (hloc x hx).2

end Azurite.DLMF
