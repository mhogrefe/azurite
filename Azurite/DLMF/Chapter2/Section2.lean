/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/


import Azurite.DLMF.Chapter2.Section1Generalized
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# DLMF §2.2: transcendental equations

* 2.2.1–2.2.2: `rootDLMF f a y` (the root of `f(x) = y` in `(a, ∞)`), `rootDLMF_spec` (existence
  and uniqueness for `y > f(a)`), `tendsto_rootDLMF`, `dlmf_2_2_2` (`x(y) ∼ y`). The hypotheses are
  continuity on `[a, ∞)` and strict increase on `(a, ∞)`. DLMF imprecision: continuity on
  `a < x < ∞` alone does not suffice (`dlmf_2_2_1_counterexample`).
* Example 2.2.3–2.2.6, `t² − ln t = y`: `tlogF` (`x − ½ ln x`, `a = ½`), `tlogT`,
  `dlmf_2_2_3` (the equation, uniqueness), `dlmf_2_2_4`, `dlmf_2_2_5`, `dlmf_2_2_6`.
-/

open Set Filter Topology Asymptotics

namespace Azurite.DLMF

/-! ### The root of `f(x) = y` (2.2.1–2.2.2) -/

open Classical in
/-- The root `x(y)` of `f(x) = y` in `(a, ∞)` (junk `0` if there is none). -/
noncomputable def rootDLMF (f : ℝ → ℝ) (a y : ℝ) : ℝ :=
  if h : ∃ x, a < x ∧ f x = y then h.choose else 0

section Root

variable {f : ℝ → ℝ} {a : ℝ} (hf : ContinuousOn f (Ici a)) (hm : StrictMonoOn f (Ioi a))
  (hfx : AsympEqDLMF atTop f id)

include hfx in
theorem tendsto_atTop_of_asympEq_id : Tendsto f atTop atTop := by
  have h2 : ∀ᶠ x in atTop, 1 / 2 ≤ f x / x :=
    hfx.eventually (Ici_mem_nhds (by norm_num : (1 / 2 : ℝ) < 1))
  refine tendsto_atTop_mono' atTop ?_ (tendsto_id.atTop_div_const (by norm_num : (0 : ℝ) < 2))
  filter_upwards [h2, eventually_gt_atTop 0] with x hx hx0
  rw [le_div_iff₀ hx0] at hx
  simp only [id]; linarith

include hf hm in
theorem le_of_mem_Ioi {x : ℝ} (hx : a < x) : f a < f x := by
  -- `f a = lim f` from the right, and `f` is strictly increasing on `(a, ∞)`
  have hc : Tendsto f (𝓝[>] a) (𝓝 (f a)) :=
    ((hf a (le_refl a : a ∈ Ici a)).mono_left (nhdsWithin_mono _ Ioi_subset_Ici_self))
  have hle : f a ≤ f ((a + x) / 2) := by
    refine le_of_tendsto hc ?_
    filter_upwards [Ioo_mem_nhdsGT (show a < (a + x) / 2 by linarith)] with t ht
    exact (hm ht.1 (show a < (a + x) / 2 by linarith) ht.2).le
  exact hle.trans_lt (hm (show a < (a + x) / 2 by linarith) hx (by linarith))

include hf hm hfx in
/-- **DLMF §2.2**: for `y > f(a)` the equation `f(x) = y` has a unique root `x(y)` in `(a, ∞)`. -/
theorem rootDLMF_spec {y : ℝ} (hy : f a < y) :
    a < rootDLMF f a y ∧ f (rootDLMF f a y) = y ∧ ∀ x, a < x → f x = y → x = rootDLMF f a y := by
  have hex : ∃ x, a < x ∧ f x = y := by
    obtain ⟨b, hb⟩ :=
      (tendsto_atTop_of_asympEq_id hfx).eventually_gt_atTop y |>.exists_forall_of_atTop
    set c := max b (a + 1)
    have hc := hb c (le_max_left _ _)
    have hac : a ≤ c := by linarith [le_max_right b (a + 1)]
    obtain ⟨x, hx, hfx'⟩ := intermediate_value_Ioo hac (hf.mono Icc_subset_Ici_self) ⟨hy, hc⟩
    exact ⟨x, hx.1, hfx'⟩
  have hroot : a < rootDLMF f a y ∧ f (rootDLMF f a y) = y := by
    have := hex.choose_spec
    simp only [rootDLMF, hex, ↓reduceDIte]
    exact this
  refine ⟨hroot.1, hroot.2, fun x hx hfx' => ?_⟩
  exact hm.injOn hx hroot.1 (hfx'.trans hroot.2.symm)

include hf hm hfx in
theorem tendsto_rootDLMF : Tendsto (rootDLMF f a) atTop atTop := by
  rw [tendsto_atTop]
  intro M
  set M' := max M (a + 1)
  filter_upwards [eventually_gt_atTop (max (f a) (f M'))] with y hy
  obtain ⟨h1, h2, -⟩ := rootDLMF_spec hf hm hfx (lt_of_le_of_lt (le_max_left _ _) hy)
  by_contra h
  push Not at h
  have hlt : rootDLMF f a y < M' := lt_of_lt_of_le h (le_max_left _ _)
  have := hm h1 (show a < M' by linarith [le_max_right M (a + 1)]) hlt
  rw [h2] at this
  linarith [le_max_right (f a) (f M')]

include hf hm hfx in
/-- **DLMF 2.2.1–2.2.2**: if `f` is continuous and strictly increasing on `(a, ∞)` (continuous at
`a` from the right) and `f(x) ∼ x` as `x → ∞`, then the root satisfies `x(y) ∼ y` as `y → ∞`. -/
theorem dlmf_2_2_2 : AsympEqDLMF atTop (rootDLMF f a) id := by
  have ht := tendsto_rootDLMF hf hm hfx
  have h := (hfx.comp ht).inv₀ one_ne_zero
  rw [inv_one] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (f a), eventually_gt_atTop 0] with y hy hy0
  obtain ⟨h1, h2, -⟩ := rootDLMF_spec hf hm hfx hy
  simp only [Function.comp_apply, id, h2, inv_div]

end Root

/-- **DLMF imprecision in §2.2**: continuity on `a < x < ∞` alone does not give a root for every
`y > f(a)`; continuity at `a` is needed. Here `f = id` on `(0, ∞)`, `f(0) = −1`, and `y = −½`. -/
theorem dlmf_2_2_1_counterexample :
    let f : ℝ → ℝ := fun x => if x = 0 then -1 else x
    ContinuousOn f (Ioi 0) ∧ StrictMonoOn f (Ioi 0) ∧ AsympEqDLMF atTop f id ∧
      f 0 < -1 / 2 ∧ ¬ ∃ x, 0 < x ∧ f x = -1 / 2 := by
  intro f
  have hfx : ∀ x : ℝ, 0 < x → f x = x := fun x hx => by simp [f, hx.ne']
  refine ⟨fun x hx => (continuousOn_id.congr fun t ht => hfx t ht) x hx |>.mono subset_rfl,
    fun x hx y hy hxy => by rw [hfx x hx, hfx y hy]; exact hxy, ?_, by norm_num [f], ?_⟩
  · refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with x hx
    rw [hfx x hx, id, div_self hx.ne']
  · rintro ⟨x, hx, h⟩
    rw [hfx x hx] at h; linarith

/-! ### Example: `t² − ln t = y` (2.2.3–2.2.6) -/

/-- `f(x) = x − ½ ln x` (with `x = t²`). -/
noncomputable def tlogF (x : ℝ) : ℝ := x - 1 / 2 * Real.log x

/-- The solution `t(y) = √x(y)` of 2.2.3. -/
noncomputable def tlogT (y : ℝ) : ℝ := √(rootDLMF tlogF (1 / 2) y)

theorem tlogF_continuousOn : ContinuousOn tlogF (Ici (1 / 2)) :=
  continuousOn_id.sub (continuousOn_const.mul (Real.continuousOn_log.mono fun x hx => by
    simp only [mem_compl_iff, mem_singleton_iff]; exact (by linarith [mem_Ici.mp hx] : x ≠ 0)))

theorem tlogF_strictMonoOn : StrictMonoOn tlogF (Ioi (1 / 2)) := by
  refine strictMonoOn_of_deriv_pos (convex_Ioi _) (tlogF_continuousOn.mono Ioi_subset_Ici_self)
    fun x hx => ?_
  rw [interior_Ioi] at hx
  have hx0 : x ≠ 0 := by linarith [mem_Ioi.mp hx]
  have hd : HasDerivAt tlogF (1 - 1 / 2 * x⁻¹) x :=
    (hasDerivAt_id x).sub ((Real.hasDerivAt_log hx0).const_mul (1 / 2))
  rw [hd.deriv]
  have : x⁻¹ < 2 := by
    rw [inv_lt_comm₀ (by linarith [mem_Ioi.mp hx]) two_pos]
    have := mem_Ioi.mp hx; norm_num at this ⊢; exact this
  linarith

theorem tlogF_asympEq : AsympEqDLMF atTop tlogF id := by
  have hlog : Tendsto (fun x => Real.log x / x) atTop (𝓝 0) := by
    simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
  have := (hlog.const_mul (1 / 2)).const_sub 1
  rw [mul_zero, sub_zero] at this
  refine this.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with x hx
  simp only [tlogF, id]; field_simp

/-- **DLMF 2.2.3**: for `y > f(½)`, `t = t(y)` solves `t² − ln t = y` (`t > 1/√2`), and it is the
only solution with `t² > ½`. -/
theorem dlmf_2_2_3 {y : ℝ} (hy : tlogF (1 / 2) < y) :
    tlogT y ^ 2 - Real.log (tlogT y) = y ∧ 1 / 2 < tlogT y ^ 2 ∧
      ∀ t : ℝ, 0 < t → 1 / 2 < t ^ 2 → t ^ 2 - Real.log t = y → t = tlogT y := by
  obtain ⟨h1, h2, h3⟩ := rootDLMF_spec tlogF_continuousOn tlogF_strictMonoOn
    tlogF_asympEq hy
  set x := rootDLMF tlogF (1 / 2) y
  have hx0 : 0 ≤ x := by linarith
  have hsq : tlogT y ^ 2 = x := Real.sq_sqrt hx0
  have hlog : Real.log (tlogT y) = 1 / 2 * Real.log x := by
    rw [tlogT, Real.log_sqrt hx0]; ring
  refine ⟨by rw [hsq, hlog]; exact h2, by rw [hsq]; exact h1, fun t ht ht2 heq => ?_⟩
  have hlt : Real.log t = 1 / 2 * Real.log (t ^ 2) := by
    rw [Real.log_pow]; push_cast; ring
  have := h3 (t ^ 2) ht2 (by rw [tlogF, ← hlt]; exact heq)
  show t = √x
  rw [← this, Real.sqrt_sq ht.le]

theorem tlogT_sq_div (y : ℝ) (hy : tlogF (1 / 2) < y) :
    tlogT y ^ 2 = rootDLMF tlogF (1 / 2) y := by
  obtain ⟨h1, -, -⟩ := rootDLMF_spec tlogF_continuousOn tlogF_strictMonoOn
    tlogF_asympEq hy
  exact Real.sq_sqrt (by linarith)

/-- `t(y)²/y → 1`. -/
theorem tendsto_tlogT_sq_div : Tendsto (fun y => tlogT y ^ 2 / y) atTop (𝓝 1) := by
  have h := dlmf_2_2_2 tlogF_continuousOn tlogF_strictMonoOn tlogF_asympEq
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (tlogF (1 / 2))] with y hy
  rw [tlogT_sq_div y hy, id]

/-- **DLMF 2.2.4**: `t = y^{1/2}(1 + o(1))` as `y → ∞`. -/
theorem dlmf_2_2_4 : IsLittleODLMF atTop (fun y => tlogT y / √y - 1) 1 := by
  have h := (Real.continuous_sqrt.tendsto 1).comp tendsto_tlogT_sq_div
  rw [Real.sqrt_one] at h
  have h' := h.sub_const 1
  rw [sub_self] at h'
  simp only [IsLittleODLMF, Pi.one_apply, div_one]
  refine h'.congr' ?_
  filter_upwards [eventually_gt_atTop (tlogF (1 / 2)), eventually_gt_atTop 0] with y hy hy0
  simp only [Function.comp_apply]
  rw [Real.sqrt_div' _ hy0.le, Real.sqrt_sq (show 0 ≤ tlogT y from Real.sqrt_nonneg _)]

/-- **DLMF 2.2.5**: `t² = y + ln t = y + ½ ln y + o(1)`. -/
theorem dlmf_2_2_5 :
    (∀ y, tlogF (1 / 2) < y → tlogT y ^ 2 = y + Real.log (tlogT y)) ∧
      Tendsto (fun y => tlogT y ^ 2 - (y + 1 / 2 * Real.log y)) atTop (𝓝 0) := by
  refine ⟨fun y hy => by linarith [(dlmf_2_2_3 hy).1], ?_⟩
  have h := ((Real.continuousAt_log one_ne_zero).tendsto.comp tendsto_tlogT_sq_div).const_mul
    (1 / 2)
  rw [Real.log_one, mul_zero] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (tlogF (1 / 2)), eventually_gt_atTop 0] with y hy hy0
  have h3 := (dlmf_2_2_3 hy).1
  have hT : 0 < tlogT y ^ 2 := by linarith [(dlmf_2_2_3 hy).2.1]
  have hlog : Real.log (tlogT y) = 1 / 2 * Real.log (tlogT y ^ 2) := by
    rw [Real.log_pow]; push_cast; ring
  simp only [Function.comp_apply]
  rw [Real.log_div hT.ne' hy0.ne']
  linarith

theorem abs_sqrt_one_add_sub_le {u : ℝ} (hu : -1 ≤ u) :
    |√(1 + u) - 1 - u / 2| ≤ u ^ 2 / 2 := by
  set s := √(1 + u)
  have hs : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : s ^ 2 = 1 + u := Real.sq_sqrt (by linarith)
  have e : s - 1 - u / 2 = -((s - 1) ^ 2 / 2) := by
    have : u = s ^ 2 - 1 := by linarith
    rw [this]; ring
  rw [e, abs_neg, abs_of_nonneg (by positivity)]
  have hsu : (s - 1) ^ 2 * (s + 1) ^ 2 = u ^ 2 := by
    have : (s - 1) * (s + 1) = u := by nlinarith
    rw [← this]; ring
  have h1 : 1 ≤ (s + 1) ^ 2 := by nlinarith
  have : (s - 1) ^ 2 ≤ u ^ 2 := by nlinarith [sq_nonneg (s - 1)]
  linarith

/-- **DLMF 2.2.6**: `t = y^{1/2}(1 + ¼y⁻¹ ln y + o(y⁻¹))` as `y → ∞`. -/
theorem dlmf_2_2_6 :
    IsLittleODLMF atTop (fun y => tlogT y / √y - 1 - 1 / 4 * y⁻¹ * Real.log y)
      fun y => y⁻¹ := by
  set ε : ℝ → ℝ := fun y => tlogT y ^ 2 - (y + 1 / 2 * Real.log y)
  have hε : Tendsto ε atTop (𝓝 0) := dlmf_2_2_5.2
  have hl2 : Tendsto (fun y => Real.log y ^ 2 / y) atTop (𝓝 0) := by
    simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 2 one_ne_zero
  have hl1 : Tendsto (fun y => Real.log y / y) atTop (𝓝 0) := by
    simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
  have hinv : Tendsto (fun y : ℝ => y⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
  -- the bound `y·u²/2 = (½ ln y + ε)²/(2y)`
  have hB : Tendsto (fun y => (1 / 2 * Real.log y + ε y) ^ 2 / (2 * y) + |ε y| / 2) atTop
      (𝓝 0) := by
    have e : ∀ y, (1 / 2 * Real.log y + ε y) ^ 2 / (2 * y) =
        1 / 8 * (Real.log y ^ 2 / y) + 1 / 2 * ((Real.log y / y) * ε y) +
          1 / 2 * (ε y ^ 2 * y⁻¹) := fun y => by
      rcases eq_or_ne y 0 with rfl | hy
      · simp
      · field_simp; ring
    simp only [e]
    have := (((hl2.const_mul (1 / 8)).add ((hl1.mul hε).const_mul (1 / 2))).add
      (((hε.pow 2).mul hinv).const_mul (1 / 2))).add (hε.abs.div_const 2)
    simpa using this
  rw [IsLittleODLMF, tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hB
  filter_upwards [eventually_gt_atTop (tlogF (1 / 2)), eventually_gt_atTop 0] with y hy hy0
  set u := (tlogT y ^ 2 - y) / y
  have hT : 0 < tlogT y ^ 2 := by linarith [(dlmf_2_2_3 hy).2.1]
  have hu : -1 ≤ u := by
    rw [le_div_iff₀ hy0]; linarith
  have hsq : tlogT y / √y = √(1 + u) := by
    have : 1 + u = tlogT y ^ 2 / y := by simp only [u]; field_simp; ring
    rw [this, Real.sqrt_div' _ hy0.le, Real.sqrt_sq (show 0 ≤ tlogT y from Real.sqrt_nonneg _)]
  have hu' : u = (1 / 2 * Real.log y + ε y) / y := by simp only [u, ε]; ring
  have key : (tlogT y / √y - 1 - 1 / 4 * y⁻¹ * Real.log y) / y⁻¹ =
      y * (√(1 + u) - 1 - u / 2) + ε y / 2 := by
    rw [hsq, hu']; field_simp; ring
  rw [key, Real.norm_eq_abs]
  have h1 := abs_sqrt_one_add_sub_le hu
  calc |y * (√(1 + u) - 1 - u / 2) + ε y / 2|
      ≤ |y * (√(1 + u) - 1 - u / 2)| + |ε y / 2| := abs_add_le _ _
    _ ≤ y * (u ^ 2 / 2) + |ε y| / 2 := by
      rw [abs_mul, abs_of_pos hy0, abs_div, abs_two]
      gcongr
    _ = (1 / 2 * Real.log y + ε y) ^ 2 / (2 * y) + |ε y| / 2 := by
      rw [hu']; field_simp

end Azurite.DLMF
