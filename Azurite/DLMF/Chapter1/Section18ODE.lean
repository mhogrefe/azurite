/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Real linear second-order ODEs with a parameter

Solutions of `u″ = V(κ, x) u`, `u(x₀) = a(κ)`, `u′(x₀) = b(κ)` on all of `ℝ`, by Picard iteration of
the Volterra equation `u(x) = a + b(x − x₀) + ∫_{x₀}^x (x − t) V(κ, t) u(t) dt`, for `V` jointly
continuous and bounded, and `a`, `b` continuous and bounded. The solution is jointly continuous in
`(κ, x)`, as is its derivative. Uniqueness is by Grönwall. Used for the bound-state theorem of
§1.18(viii).
-/

open Set Filter Topology MeasureTheory
open scoped Nat

namespace Azurite.DLMF

section Picard

variable (V : ℝ → ℝ → ℝ) (a b : ℝ → ℝ) (x0 : ℝ)

/-- The Picard iterates of the Volterra equation. -/
noncomputable def volterraIter : ℕ → ℝ → ℝ → ℝ
  | 0 => fun κ x => a κ + b κ * (x - x0)
  | n + 1 => fun κ x => a κ + b κ * (x - x0) + ∫ t in x0..x, (x - t) * (V κ t * volterraIter n κ t)

/-- Successive differences of the Picard iterates. -/
noncomputable def volterraDiff (n : ℕ) (κ x : ℝ) : ℝ :=
  volterraIter V a b x0 (n + 1) κ x - volterraIter V a b x0 n κ x

variable {V a b}
variable (hV : Continuous fun p : ℝ × ℝ => V p.1 p.2) (ha : Continuous a) (hb : Continuous b)
include hV ha hb

theorem continuous_volterraIter (n : ℕ) :
    Continuous fun p : ℝ × ℝ => volterraIter V a b x0 n p.1 p.2 := by
  induction n with
  | zero => simp only [volterraIter]; fun_prop
  | succ n ih =>
    simp only [volterraIter]
    refine ((ha.comp continuous_fst).add ((hb.comp continuous_fst).mul
      (continuous_snd.sub continuous_const))).add ?_
    have hf : Continuous fun q : (ℝ × ℝ) × ℝ => (q.1.2 - q.2) * (V q.1.1 q.2 *
        volterraIter V a b x0 n q.1.1 q.2) :=
      (continuous_snd.comp continuous_fst |>.sub continuous_snd).mul
        ((hV.comp ((continuous_fst.comp continuous_fst).prodMk continuous_snd)).mul
          (ih.comp ((continuous_fst.comp continuous_fst).prodMk continuous_snd)))
    exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
      (f := fun (p : ℝ × ℝ) (t : ℝ) => (p.2 - t) * (V p.1 t * volterraIter V a b x0 n p.1 t))
      hf continuous_snd

theorem continuous_volterraIter_x (n : ℕ) (κ : ℝ) :
    Continuous fun x => volterraIter V a b x0 n κ x :=
  (continuous_volterraIter x0 hV ha hb n).comp (continuous_const.prodMk continuous_id)

theorem continuous_volterraDiff (n : ℕ) :
    Continuous fun p : ℝ × ℝ => volterraDiff V a b x0 n p.1 p.2 :=
  (continuous_volterraIter x0 hV ha hb (n + 1)).sub (continuous_volterraIter x0 hV ha hb n)

omit hV ha hb in
theorem volterraDiff_zero (κ x : ℝ) :
    volterraDiff V a b x0 0 κ x =
      ∫ t in x0..x, (x - t) * (V κ t * volterraIter V a b x0 0 κ t) := by
  simp only [volterraDiff, volterraIter]
  ring

theorem volterraDiff_succ (n : ℕ) (κ x : ℝ) :
    volterraDiff V a b x0 (n + 1) κ x =
      ∫ t in x0..x, (x - t) * (V κ t * volterraDiff V a b x0 n κ t) := by
  have hc : ∀ m, Continuous fun t => (x - t) * (V κ t * volterraIter V a b x0 m κ t) := fun m =>
    (continuous_const.sub continuous_id).mul
      ((hV.comp (continuous_const.prodMk continuous_id)).mul
        (continuous_volterraIter_x x0 hV ha hb m κ))
  simp only [volterraDiff]
  rw [show volterraIter V a b x0 (n + 1 + 1) κ x - volterraIter V a b x0 (n + 1) κ x =
      (∫ t in x0..x, (x - t) * (V κ t * volterraIter V a b x0 (n + 1) κ t)) -
        ∫ t in x0..x, (x - t) * (V κ t * volterraIter V a b x0 n κ t) by
      simp only [volterraIter]; ring,
    ← intervalIntegral.integral_sub ((hc _).intervalIntegrable _ _) ((hc _).intervalIntegrable _ _)]
  refine intervalIntegral.integral_congr fun t _ => ?_
  ring

end Picard

/-! ### A Volterra estimate -/

theorem abs_integral_le_pow {g : ℝ → ℝ} (hg : Continuous g) {x0 x C : ℝ} (n : ℕ)
    (hC : ∀ t ∈ uIcc x0 x, |g t| ≤ C * |t - x0| ^ n) :
    |∫ t in x0..x, g t| ≤ C * |x - x0| ^ (n + 1) / (n + 1) := by
  rcases le_total x0 x with h | h
  · have h1 := intervalIntegral.norm_integral_le_integral_norm (μ := volume) (f := g) h
    have h2 : ∫ t in x0..x, ‖g t‖ ≤ ∫ t in x0..x, C * (t - x0) ^ n :=
      intervalIntegral.integral_mono_on h (hg.norm.intervalIntegrable _ _)
        ((by fun_prop : Continuous fun t => C * (t - x0) ^ n).intervalIntegrable _ _)
        fun t ht => by
          rw [Real.norm_eq_abs]
          have := hC t (by rw [uIcc_of_le h]; exact ht)
          rwa [abs_of_nonneg (sub_nonneg.mpr ht.1)] at this
    have h3 : ∫ t in x0..x, C * (t - x0) ^ n = C * (x - x0) ^ (n + 1) / (n + 1) := by
      rw [intervalIntegral.integral_const_mul,
        intervalIntegral.integral_comp_sub_right (fun t => t ^ n), sub_self, integral_pow,
        zero_pow (Nat.succ_ne_zero n), sub_zero, mul_div_assoc]
    rw [Real.norm_eq_abs] at h1
    rw [abs_of_nonneg (sub_nonneg.mpr h)]
    linarith
  · rw [intervalIntegral.integral_symm, abs_neg]
    have h1 := intervalIntegral.norm_integral_le_integral_norm (μ := volume) (f := g) h
    have h2 : ∫ t in x..x0, ‖g t‖ ≤ ∫ t in x..x0, C * (x0 - t) ^ n :=
      intervalIntegral.integral_mono_on h (hg.norm.intervalIntegrable _ _)
        ((by fun_prop : Continuous fun t => C * (x0 - t) ^ n).intervalIntegrable _ _)
        fun t ht => by
          rw [Real.norm_eq_abs]
          have := hC t (by rw [uIcc_of_ge h]; exact ht)
          rwa [abs_of_nonpos (sub_nonpos.mpr ht.2), neg_sub] at this
    have h3 : ∫ t in x..x0, C * (x0 - t) ^ n = C * (x0 - x) ^ (n + 1) / (n + 1) := by
      rw [intervalIntegral.integral_const_mul,
        intervalIntegral.integral_comp_sub_left (fun t => t ^ n), sub_self, integral_pow,
        zero_pow (Nat.succ_ne_zero n), sub_zero, mul_div_assoc]
    rw [Real.norm_eq_abs] at h1
    rw [abs_of_nonpos (sub_nonpos.mpr h), neg_sub]
    linarith

/-! ### Convergence of the Picard iterates -/

section Solution

variable {V : ℝ → ℝ → ℝ} {a b : ℝ → ℝ} (x0 : ℝ)
variable (hV : Continuous fun p : ℝ × ℝ => V p.1 p.2) (ha : Continuous a) (hb : Continuous b)
variable {M B : ℝ} (hM : ∀ κ t, |V κ t| ≤ M) (hBa : ∀ κ, |a κ| ≤ B) (hBb : ∀ κ, |b κ| ≤ B)

/-- The majorant `B(1 + L)(ML²)^{n+1}/(n+1)!` of the `n`th Picard difference on `|x − x₀| ≤ L`. -/
noncomputable def volterraBound (M B L : ℝ) (n : ℕ) : ℝ :=
  B * (1 + L) * (M * L * L) ^ (n + 1) / (n + 1)!

theorem summable_volterraBound (M B L : ℝ) : Summable (volterraBound M B L) := by
  have h := ((summable_nat_add_iff 1).mpr
    (Real.summable_pow_div_factorial (M * L * L))).mul_left (B * (1 + L))
  refine h.congr fun n => ?_
  simp only [volterraBound]
  ring

include hBa hBb in
theorem abs_volterraIter_zero_le {L : ℝ} (κ x : ℝ) (hx : |x - x0| ≤ L) :
    |volterraIter V a b x0 0 κ x| ≤ B * (1 + L) := by
  simp only [volterraIter]
  calc |a κ + b κ * (x - x0)| ≤ |a κ| + |b κ| * |x - x0| := by
        rw [← abs_mul]; exact abs_add_le _ _
    _ ≤ B + B * L := by gcongr <;> [exact hBa κ; exact (abs_nonneg _).trans (hBb κ); exact hBb κ]
    _ = B * (1 + L) := by ring

include hV ha hb hM hBa hBb in
theorem abs_volterraDiff_le (n : ℕ) {L : ℝ} (hL : 0 ≤ L) (κ : ℝ) :
    ∀ x, |x - x0| ≤ L → |volterraDiff V a b x0 n κ x| ≤
      B * (1 + L) * (M * L) ^ (n + 1) * |x - x0| ^ (n + 1) / (n + 1)! := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0 0)
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hBa 0)
  have hcV : Continuous fun t => V κ t := hV.comp (continuous_const.prodMk continuous_id)
  induction n with
  | zero =>
    intro x hx
    rw [volterraDiff_zero]
    have h := abs_integral_le_pow (x0 := x0) (x := x) (C := L * (M * (B * (1 + L))))
      (g := fun t => (x - t) * (V κ t * volterraIter V a b x0 0 κ t))
      ((continuous_const.sub continuous_id).mul
        (hcV.mul (continuous_volterraIter_x x0 hV ha hb 0 κ)))
      0 fun t ht => by
        rw [pow_zero, mul_one, abs_mul, abs_mul]
        have h1 : |x - t| ≤ L := (abs_sub_right_of_mem_uIcc ht).trans hx
        have h2 : |t - x0| ≤ L := (abs_sub_left_of_mem_uIcc ht).trans hx
        gcongr
        · exact hM κ t
        · exact abs_volterraIter_zero_le x0 hBa hBb κ t h2
    refine h.trans (le_of_eq ?_)
    simp only [zero_add, Nat.cast_zero, pow_one, div_one, Nat.factorial_one, Nat.cast_one]
    ring
  | succ n ih =>
    intro x hx
    rw [volterraDiff_succ x0 hV ha hb]
    have hcd : Continuous fun t => volterraDiff V a b x0 n κ t :=
      (continuous_volterraDiff x0 hV ha hb n).comp (continuous_const.prodMk continuous_id)
    have h := abs_integral_le_pow (x0 := x0) (x := x)
      (C := L * M * (B * (1 + L) * (M * L) ^ (n + 1) / (n + 1)!))
      (g := fun t => (x - t) * (V κ t * volterraDiff V a b x0 n κ t))
      ((continuous_const.sub continuous_id).mul (hcV.mul hcd)) (n + 1) fun t ht => by
        rw [abs_mul, abs_mul]
        have h1 : |x - t| ≤ L := (abs_sub_right_of_mem_uIcc ht).trans hx
        have h2 : |t - x0| ≤ L := (abs_sub_left_of_mem_uIcc ht).trans hx
        have h3 := ih t h2
        calc |x - t| * (|V κ t| * |volterraDiff V a b x0 n κ t|)
            ≤ L * (M * (B * (1 + L) * (M * L) ^ (n + 1) * |t - x0| ^ (n + 1) / (n + 1)!)) := by
              gcongr
              · exact hM κ t
          _ = L * M * (B * (1 + L) * (M * L) ^ (n + 1) / (n + 1)!) * |t - x0| ^ (n + 1) := by
              ring
    refine h.trans (le_of_eq ?_)
    rw [Nat.factorial_succ (n + 1)]
    push_cast
    field_simp
    ring

include hV ha hb hM hBa hBb in
theorem abs_volterraDiff_le_bound (n : ℕ) {L : ℝ} (hL : 0 ≤ L) (κ x : ℝ) (hx : |x - x0| ≤ L) :
    |volterraDiff V a b x0 n κ x| ≤ volterraBound M B L n := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0 0)
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hBa 0)
  refine (abs_volterraDiff_le x0 hV ha hb hM hBa hBb n hL κ x hx).trans ?_
  have key : (M * L) ^ (n + 1) * |x - x0| ^ (n + 1) ≤ (M * L * L) ^ (n + 1) := by
    rw [show (M * L * L) ^ (n + 1) = (M * L) ^ (n + 1) * L ^ (n + 1) from mul_pow _ _ _]
    gcongr
  rw [volterraBound]
  calc B * (1 + L) * (M * L) ^ (n + 1) * |x - x0| ^ (n + 1) / (n + 1)!
      = B * (1 + L) * ((M * L) ^ (n + 1) * |x - x0| ^ (n + 1)) / (n + 1)! := by ring
    _ ≤ B * (1 + L) * (M * L * L) ^ (n + 1) / (n + 1)! := by gcongr

/-- The solution `u(κ, x) = lim volterraIter`. -/
noncomputable def odeSol (V : ℝ → ℝ → ℝ) (a b : ℝ → ℝ) (x0 κ x : ℝ) : ℝ :=
  volterraIter V a b x0 0 κ x + ∑' n, volterraDiff V a b x0 n κ x

include hV ha hb hM hBa hBb in
theorem summable_volterraDiff (κ x : ℝ) : Summable fun n => volterraDiff V a b x0 n κ x :=
  (summable_volterraBound M B |x - x0|).of_norm_bounded fun n =>
    abs_volterraDiff_le_bound x0 hV ha hb hM hBa hBb n (abs_nonneg _) κ x le_rfl

theorem volterraIter_eq_sum (n : ℕ) (κ x : ℝ) : volterraIter V a b x0 n κ x =
    volterraIter V a b x0 0 κ x + ∑ k ∈ Finset.range n, volterraDiff V a b x0 k κ x := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, ← add_assoc, ← ih, volterraDiff]; ring

include hV ha hb hM hBa hBb in
theorem tendsto_volterraIter (κ x : ℝ) :
    Tendsto (fun n => volterraIter V a b x0 n κ x) atTop (𝓝 (odeSol V a b x0 κ x)) := by
  rw [show (fun n => volterraIter V a b x0 n κ x) = fun n => volterraIter V a b x0 0 κ x +
    ∑ k ∈ Finset.range n, volterraDiff V a b x0 k κ x from
      funext fun n => volterraIter_eq_sum x0 n κ x]
  exact ((summable_volterraDiff x0 hV ha hb hM hBa hBb κ x).hasSum.tendsto_sum_nat).const_add _

include hV ha hb hM hBa hBb in
/-- The solution is jointly continuous in `(κ, x)`. -/
theorem continuous_odeSol : Continuous fun p : ℝ × ℝ => odeSol V a b x0 p.1 p.2 := by
  rw [continuous_iff_continuousAt]
  intro p
  set L := |p.2 - x0| + 1
  have hL : 0 ≤ L := by positivity
  set S := {q : ℝ × ℝ | |q.2 - x0| < L}
  have hS : IsOpen S := isOpen_lt (by fun_prop) continuous_const
  have hp : p ∈ S := by simp [S, L]
  have hc : ContinuousOn (fun q : ℝ × ℝ => ∑' n, volterraDiff V a b x0 n q.1 q.2) S :=
    continuousOn_tsum (fun n => (continuous_volterraDiff x0 hV ha hb n).continuousOn)
      (summable_volterraBound M B L) fun n q hq => by
        rw [Real.norm_eq_abs]
        exact abs_volterraDiff_le_bound x0 hV ha hb hM hBa hBb n hL q.1 q.2 (le_of_lt hq)
  exact (((continuous_volterraIter x0 hV ha hb 0).continuousOn.add hc).continuousAt
    (hS.mem_nhds hp))

include hV ha hb hM hBa hBb in
theorem continuous_odeSol_x (κ : ℝ) : Continuous fun x => odeSol V a b x0 κ x :=
  (continuous_odeSol x0 hV ha hb hM hBa hBb).comp (continuous_const.prodMk continuous_id)

include hV ha hb hM hBa hBb in
/-- The Volterra integral equation. -/
theorem odeSol_eq (κ x : ℝ) : odeSol V a b x0 κ x = a κ + b κ * (x - x0) +
    ∫ t in x0..x, (x - t) * (V κ t * odeSol V a b x0 κ t) := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0 0)
  set L := |x - x0|
  set Cb := B * (1 + L) + ∑' k, volterraBound M B L k
  have hcV : Continuous fun t => V κ t := hV.comp (continuous_const.prodMk continuous_id)
  have hbd : ∀ n, ∀ t ∈ uIcc x0 x, |volterraIter V a b x0 n κ t| ≤ Cb := fun n t ht => by
    have htL : |t - x0| ≤ L := abs_sub_left_of_mem_uIcc ht
    rw [volterraIter_eq_sum x0]
    refine (abs_add_le _ _).trans (add_le_add (abs_volterraIter_zero_le x0 hBa hBb κ t htL) ?_)
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine (Finset.sum_le_sum fun k _ =>
      abs_volterraDiff_le_bound x0 hV ha hb hM hBa hBb k (abs_nonneg _) κ t htL).trans ?_
    exact (summable_volterraBound M B L).sum_le_tsum _ fun k _ => by
      unfold volterraBound
      have : 0 ≤ B := (abs_nonneg _).trans (hBa 0)
      positivity
  have hlim : Tendsto (fun n => ∫ t in x0..x, (x - t) * (V κ t * volterraIter V a b x0 n κ t))
      atTop (𝓝 (∫ t in x0..x, (x - t) * (V κ t * odeSol V a b x0 κ t))) := by
    refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ => L * (M * Cb))
      (Eventually.of_forall fun n => ((continuous_const.sub continuous_id).mul
        (hcV.mul (continuous_volterraIter_x x0 hV ha hb n κ))).aestronglyMeasurable) ?_
      intervalIntegrable_const (ae_of_all _ fun t _ => ?_)
    · refine Eventually.of_forall fun n => ae_of_all _ fun t ht => ?_
      have ht' : t ∈ uIcc x0 x := uIoc_subset_uIcc ht
      rw [Real.norm_eq_abs, abs_mul, abs_mul]
      have h1 : |x - t| ≤ L := abs_sub_right_of_mem_uIcc ht'
      gcongr
      · exact hM κ t
      · exact hbd n t ht'
    · exact ((tendsto_volterraIter x0 hV ha hb hM hBa hBb κ t).const_mul (V κ t)).const_mul (x - t)
  have h2 := (tendsto_volterraIter x0 hV ha hb hM hBa hBb κ x).comp (tendsto_add_atTop_nat 1)
  have h3 : Tendsto (fun n => volterraIter V a b x0 (n + 1) κ x) atTop
      (𝓝 (a κ + b κ * (x - x0) + ∫ t in x0..x, (x - t) * (V κ t * odeSol V a b x0 κ t))) := by
    simp only [volterraIter]
    exact hlim.const_add _
  exact tendsto_nhds_unique h2 h3

/-- The derivative `u′(κ, x) = b(κ) + ∫_{x₀}^x V(κ, t) u(κ, t) dt`. -/
noncomputable def odeSolD (V : ℝ → ℝ → ℝ) (a b : ℝ → ℝ) (x0 κ x : ℝ) : ℝ :=
  b κ + ∫ t in x0..x, V κ t * odeSol V a b x0 κ t

include hV ha hb hM hBa hBb in
theorem hasDerivAt_odeSol (κ x : ℝ) :
    HasDerivAt (odeSol V a b x0 κ) (odeSolD V a b x0 κ x) x := by
  set F : ℝ → ℝ := fun t => V κ t * odeSol V a b x0 κ t
  have hF : Continuous F := (hV.comp (continuous_const.prodMk continuous_id)).mul
    (continuous_odeSol_x x0 hV ha hb hM hBa hBb κ)
  have hG : Continuous fun t => t * F t := continuous_id.mul hF
  have e : odeSol V a b x0 κ = fun y => a κ + b κ * (y - x0) + (y * (∫ t in x0..y, F t) -
      ∫ t in x0..y, t * F t) := by
    funext y
    rw [odeSol_eq x0 hV ha hb hM hBa hBb]
    congr 1
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_sub]
    · exact intervalIntegral.integral_congr fun t _ => by simp only [F]; ring
    · exact (continuous_const.mul hF).intervalIntegrable _ _
    · exact hG.intervalIntegrable _ _
  rw [e]
  have h1 := (hF.integral_hasStrictDerivAt x0 x).hasDerivAt
  have h2 := (hG.integral_hasStrictDerivAt x0 x).hasDerivAt
  have h := (((hasDerivAt_id x).sub_const x0).const_mul (b κ)).const_add (a κ) |>.add
    (((hasDerivAt_id x).mul h1).sub h2)
  refine h.congr_deriv ?_
  simp only [odeSolD, F, id]
  ring

include hV ha hb hM hBa hBb in
theorem hasDerivAt_odeSolD (κ x : ℝ) :
    HasDerivAt (odeSolD V a b x0 κ) (V κ x * odeSol V a b x0 κ x) x := by
  have hF : Continuous fun t => V κ t * odeSol V a b x0 κ t :=
    (hV.comp (continuous_const.prodMk continuous_id)).mul
      (continuous_odeSol_x x0 hV ha hb hM hBa hBb κ)
  exact (hF.integral_hasStrictDerivAt x0 x).hasDerivAt.const_add (b κ)

include hV ha hb hM hBa hBb in
theorem continuous_odeSolD : Continuous fun p : ℝ × ℝ => odeSolD V a b x0 p.1 p.2 := by
  have hf : Continuous fun q : ℝ × ℝ => V q.1 q.2 * odeSol V a b x0 q.1 q.2 :=
    hV.mul (continuous_odeSol x0 hV ha hb hM hBa hBb)
  exact (hb.comp continuous_fst).add
    (intervalIntegral.continuous_parametric_primitive_of_continuous (a₀ := x0)
      (f := fun κ t => V κ t * odeSol V a b x0 κ t) hf)

include hV ha hb hM hBa hBb in
theorem odeSol_init (κ : ℝ) : odeSol V a b x0 κ x0 = a κ := by
  rw [odeSol_eq x0 hV ha hb hM hBa hBb]; simp

theorem odeSolD_init (κ : ℝ) : odeSolD V a b x0 κ x0 = b κ := by simp [odeSolD]

end Solution

/-! ### Uniqueness -/

/-- Uniqueness to the right of `x₁` for `w″ = W w` with `W` bounded on `[x₁, ∞)`. -/
theorem ode2_eq_zero_right {W w w' : ℝ → ℝ} {K x1 : ℝ} (hK : ∀ x, x1 ≤ x → |W x| ≤ K)
    (hw : ∀ x, x1 ≤ x → HasDerivAt w (w' x) x)
    (hw' : ∀ x, x1 ≤ x → HasDerivAt w' (W x * w x) x)
    (h0 : w x1 = 0) (h1 : w' x1 = 0) : ∀ x, x1 ≤ x → w x = 0 := by
  intro x hx
  set Y : ℝ → ℝ × ℝ := fun s => (w s, w' s)
  have hY : ∀ s, x1 ≤ s → HasDerivAt Y (w' s, W s * w s) s := fun s hs =>
    (hw s hs).prodMk (hw' s hs)
  have h := eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right (f := Y)
    (f' := fun s => (w' s, W s * w s)) (K := max 1 K) (a := x1) (b := x)
    (fun s hs => (hY s hs.1).continuousAt.continuousWithinAt)
    (fun s hs => (hY s hs.1).hasDerivWithinAt) (by simp [Y, h0, h1]) fun s hs => by
      simp only [Prod.norm_def, Real.norm_eq_abs, Y]
      have hKs := hK s hs.1
      refine max_le ?_ ?_
      · calc |w' s| ≤ max |w s| |w' s| := le_max_right _ _
          _ ≤ max 1 K * max |w s| |w' s| :=
            le_mul_of_one_le_left (by positivity) (le_max_left _ _)
      · rw [abs_mul]
        calc |W s| * |w s| ≤ K * max |w s| |w' s| := by
              gcongr
              · exact (abs_nonneg _).trans hKs
              · exact le_max_left _ _
          _ ≤ max 1 K * max |w s| |w' s| := by gcongr; exact le_max_right _ _
  exact congrArg Prod.fst (h x ⟨hx, le_rfl⟩)

/-- Uniqueness to the left of `x₁`, by reflection. -/
theorem ode2_eq_zero_left {W w w' : ℝ → ℝ} {K x1 : ℝ} (hK : ∀ x, x ≤ x1 → |W x| ≤ K)
    (hw : ∀ x, x ≤ x1 → HasDerivAt w (w' x) x)
    (hw' : ∀ x, x ≤ x1 → HasDerivAt w' (W x * w x) x)
    (h0 : w x1 = 0) (h1 : w' x1 = 0) : ∀ x, x ≤ x1 → w x = 0 := by
  intro x hx
  have := ode2_eq_zero_right (W := fun s => W (-s)) (w := fun s => w (-s))
    (w' := fun s => -w' (-s)) (x1 := -x1) (fun s hs => hK (-s) (by linarith))
    (fun s hs => ((hw (-s) (by linarith)).comp s (hasDerivAt_neg s)).congr_deriv (by ring))
    (fun s hs => ((hw' (-s) (by linarith)).comp s (hasDerivAt_neg s)).neg.congr_deriv
      (by ring))
    (by simpa using h0) (by simp [h1]) (-x) (by linarith)
  simpa using this

/-- Uniqueness for `w″ = W w` with bounded `W`: `w(x₁) = w′(x₁) = 0` forces `w = 0`. -/
theorem ode2_eq_zero {W w w' : ℝ → ℝ} {K : ℝ} (hK : ∀ x, |W x| ≤ K)
    (hw : ∀ x, HasDerivAt w (w' x) x) (hw' : ∀ x, HasDerivAt w' (W x * w x) x) {x1 : ℝ}
    (h0 : w x1 = 0) (h1 : w' x1 = 0) : ∀ x, w x = 0 := by
  intro x
  rcases le_total x1 x with h | h
  · exact ode2_eq_zero_right (fun s _ => hK s) (fun s _ => hw s) (fun s _ => hw' s) h0 h1 x h
  · exact ode2_eq_zero_left (fun s _ => hK s) (fun s _ => hw s) (fun s _ => hw' s) h0 h1 x h

end Azurite.DLMF
