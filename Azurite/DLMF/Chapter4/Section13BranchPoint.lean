/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the
Apache License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter4.Section13Cut
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Complex.RemovableSingularity

/-!
# DLMF §4.13: the branch point `−e⁻¹`

* `eq_neg_one_of_mul_exp`: the only solution of `w e^w = −e⁻¹` with `|ℑw| ≤ 2π` is `w = −1`
  (off the real axis, `ℑ(w e^w) = 0` forces `ξ = −η cot η`, and then either `ℜ(w e^w) > 0` or
  `ln|w e^w| < −1`).
* `tendsto_neg_one_of_mul_exp`: any `f` with `f e^f → −e⁻¹` and `|ℑf| ≤ 2π` tends to `−1`
  (the values lie in a compact box, whose only possible cluster point is `−1`).
* `dlmf_4_13_2_limits`: `W₀` is continuous at `−e⁻¹`, and `W_{±1}(−e⁻¹ ∓ 0i) = −1`.
-/

open Set Filter Topology Complex
open scoped Real

namespace Azurite.DLMF

/-- No root of `w e^w = −e⁻¹` with `0 < ℑw ≤ 2π` (in real coordinates `w = ξ + iη`). -/
theorem not_mul_exp_eq_neg_exp_neg_one {ξ η : ℝ} (h0 : 0 < η) (h2 : η ≤ 2 * π)
    (him : ξ * Real.sin η + η * Real.cos η = 0)
    (hre : Real.exp ξ * (ξ * Real.cos η - η * Real.sin η) = -Real.exp (-1)) : False := by
  have hsc := Real.sin_sq_add_cos_sq η
  have key : Real.exp ξ * η = Real.exp (-1) * Real.sin η := by
    linear_combination (-Real.sin η) * hre + (Real.exp ξ * Real.cos η) * him +
      (-Real.exp ξ * η) * hsc
  have hpos : 0 < Real.exp ξ * η := mul_pos (Real.exp_pos _) h0
  rcases le_or_gt (Real.sin η) 0 with hs | hs
  · nlinarith [Real.exp_pos (-1)]
  have hηπ : η < π := by
    by_contra h; push Not at h
    have : 0 ≤ Real.sin (η - π) :=
      Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
    rw [Real.sin_sub_pi] at this; linarith
  have hg := omegaG_pi_gt (α := π - η) ⟨by linarith, by rw [min_self]; linarith⟩
  rw [omegaG_pi_eq ⟨by linarith, by rw [min_self]; linarith⟩, sub_sub_cancel] at hg
  have hξ : ξ = -(η * Real.cos η / Real.sin η) := by
    field_simp; linear_combination him
  have hl : Real.log (η / Real.sin η) = -1 - ξ := by
    have : η / Real.sin η = Real.exp (-1 - ξ) := by
      rw [div_eq_iff hs.ne', Real.exp_sub]; field_simp; linear_combination key
    rw [this, Real.log_exp]
  rw [hl] at hg
  linarith

theorem mul_exp_re (w : ℂ) : (w * exp w).re =
    Real.exp w.re * (w.re * Real.cos w.im - w.im * Real.sin w.im) := by
  simp only [mul_re, exp_re, exp_im]; ring

theorem mul_exp_im (w : ℂ) : (w * exp w).im =
    Real.exp w.re * (w.re * Real.sin w.im + w.im * Real.cos w.im) := by
  simp only [mul_im, exp_re, exp_im]; ring

/-- `x e^x = −e⁻¹` (real) only at `x = −1`. -/
theorem eq_neg_one_of_real_mul_exp {x : ℝ} (h : x * Real.exp x = -Real.exp (-1)) : x = -1 := by
  by_contra hx
  have hy : -(x + 1) ≠ 0 := fun h' => hx (by linarith)
  have h1 := Real.add_one_lt_exp hy
  have h2 : (-x) * Real.exp (x + 1) = 1 := by
    rw [Real.exp_add, show Real.exp 1 = (Real.exp (-1))⁻¹ by rw [Real.exp_neg, inv_inv]]
    field_simp; linarith
  have h3 : Real.exp (-(x + 1)) * Real.exp (x + 1) = 1 := by rw [← Real.exp_add]; simp
  have h4 := Real.exp_pos (x + 1)
  nlinarith

/-- The only solution of `w e^w = −e⁻¹` with `|ℑw| ≤ 2π` is `w = −1`. -/
theorem eq_neg_one_of_mul_exp {w : ℂ} (hw : w * exp w = ((-Real.exp (-1) : ℝ) : ℂ))
    (him : |w.im| ≤ 2 * π) : w = -1 := by
  have hre := congrArg re hw
  have hi := congrArg im hw
  rw [mul_exp_re, ofReal_re] at hre
  rw [mul_exp_im, ofReal_im] at hi
  have hi' : w.re * Real.sin w.im + w.im * Real.cos w.im = 0 := by
    rcases mul_eq_zero.mp hi with h | h
    · exact absurd h (Real.exp_pos _).ne'
    · exact h
  rcases lt_trichotomy w.im 0 with hη | hη | hη
  · exfalso
    refine not_mul_exp_eq_neg_exp_neg_one (ξ := w.re) (η := -w.im) (by linarith)
      (by linarith [neg_abs_le w.im]) ?_ ?_
    · rw [Real.sin_neg, Real.cos_neg]; linear_combination -hi'
    · rw [Real.sin_neg, Real.cos_neg]; linear_combination hre
  · rw [hη, Real.sin_zero, Real.cos_zero] at hre
    have hx := eq_neg_one_of_real_mul_exp (x := w.re) (by linarith)
    apply Complex.ext <;> simp [hx, hη]
  · exact (not_mul_exp_eq_neg_exp_neg_one hη (by linarith [le_abs_self w.im]) hi' hre).elim

/-- The box `[−10, 2] × [−2π, 2π]` containing the relevant solutions. -/
def branchBox : Set ℂ := {w | w.re ∈ Icc (-10) 2 ∧ |w.im| ≤ 2 * π}

theorem isCompact_branchBox : IsCompact branchBox := by
  refine Metric.isCompact_of_isClosed_isBounded ?_ ?_
  · exact ((isClosed_Icc.preimage continuous_re).inter
      (isClosed_le (continuous_abs.comp continuous_im) continuous_const))
  · rw [isBounded_iff_forall_norm_le]
    refine ⟨10 + 2 * π, fun w hw => ?_⟩
    obtain ⟨⟨h1, h2⟩, h3⟩ := hw
    have := norm_le_abs_re_add_abs_im w
    have : |w.re| ≤ 10 := abs_le.mpr ⟨by linarith, by linarith⟩
    linarith

/-- If `1/3 ≤ |w e^w| ≤ 1` and `|ℑw| ≤ 2π`, then `w` lies in `branchBox`. -/
theorem mem_branchBox {w : ℂ} (h1 : 1 / 3 ≤ ‖w * exp w‖) (h2 : ‖w * exp w‖ ≤ 1)
    (him : |w.im| ≤ 2 * π) : w ∈ branchBox := by
  rw [norm_mul, norm_exp] at h1 h2
  have hn := norm_le_abs_re_add_abs_im w
  have hpi := Real.pi_lt_d2
  refine ⟨⟨?_, ?_⟩, him⟩
  · by_contra h; push Not at h
    set y := -w.re
    have hy : 10 < y := by simp only [y]; linarith
    have hq := Real.quadratic_le_exp_of_nonneg (by linarith : 0 ≤ y)
    have he : Real.exp w.re * Real.exp y = 1 := by
      rw [← Real.exp_add]; simp [y]
    have hre : |w.re| = y := by rw [abs_of_neg (by linarith)]
    have hnorm : ‖w‖ ≤ y + 7 := by linarith
    have hexp := Real.exp_pos w.re
    -- `‖w‖ e^{−y} ≤ (y + 7)/(1 + y + y²/2) < 1/3`
    have : ‖w‖ * Real.exp w.re * Real.exp y ≤ (y + 7) * (Real.exp w.re * Real.exp y) := by
      have := mul_le_mul_of_nonneg_right hnorm (mul_pos hexp (Real.exp_pos y)).le
      linarith
    rw [he] at this
    nlinarith
  · by_contra h; push Not at h
    have hq := Real.add_one_le_exp w.re
    have : w.re ≤ ‖w‖ := (le_abs_self _).trans (abs_re_le_norm w)
    nlinarith

/-- A cluster point of `F` with `F ≤ 𝓝 c` is `c`. -/
theorem ClusterPt.eq_of_le_nhds' {X : Type*} [TopologicalSpace X] [T2Space X] {x c : X}
    {F : Filter X} (h : ClusterPt x F) (hle : F ≤ 𝓝 c) : x = c := by
  by_contra hne
  have := h.mono hle
  rw [ClusterPt, (disjoint_nhds_nhds.mpr hne).eq_bot] at this
  exact this.ne rfl

/-- Any `f` with `f e^f → −e⁻¹` and `|ℑf| ≤ 2π` tends to `−1`. -/
theorem tendsto_neg_one_of_mul_exp {α : Type*} {l : Filter α} {f : α → ℂ}
    (hf : Tendsto (fun x => f x * exp (f x)) l (𝓝 ((-Real.exp (-1) : ℝ) : ℂ)))
    (him : ∀ᶠ x in l, |(f x).im| ≤ 2 * π) : Tendsto f l (𝓝 (-1)) := by
  have hc : ‖((-Real.exp (-1) : ℝ) : ℂ)‖ = Real.exp (-1) := by
    rw [norm_real, Real.norm_eq_abs, abs_neg, abs_of_pos (Real.exp_pos _)]
  have he1 : 1 / 3 < Real.exp (-1) := by
    rw [Real.exp_neg, one_div]
    exact inv_strictAnti₀ (Real.exp_pos 1) (by linarith [Real.exp_one_lt_d9])
  have he2 : Real.exp (-1) < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
  have hn := hf.norm
  rw [hc] at hn
  have hev1 := hn.eventually (lt_mem_nhds he1)
  have hev2 := hn.eventually (gt_mem_nhds he2)
  refine isCompact_branchBox.tendsto_nhds_of_unique_mapClusterPt ?_ fun w hw hcl => ?_
  · filter_upwards [hev1, hev2, him] with x h1 h2 h3
    exact mem_branchBox h1.le h2.le h3
  · have hcont : Continuous fun w : ℂ => w * exp w := continuous_id.mul continuous_exp
    have h1 := hcl.tendsto_comp (hcont.tendsto w)
    have h2 : w * exp w = ((-Real.exp (-1) : ℝ) : ℂ) := ClusterPt.eq_of_le_nhds' h1 hf
    exact eq_neg_one_of_mul_exp h2 hw.2

/-- `ℑW_k(z) + ph W_k(z) = ph z + 2πk` forces `|ℑW_k(z)| ≤ 2π` when `|ph z + 2πk| ≤ 2π`. -/
theorem abs_im_lambertW_le (k : ℤ) {z : ℂ} (hz : z ≠ 0) (hθ : |arg z + 2 * π * k| ≤ 2 * π) :
    |(lambertW k z).im| ≤ 2 * π := by
  rw [lambertW_of_ne hz]
  by_cases hL : omegaLm (log z + 2 * π * k * I)
  · rw [wrightOmega_of_Lm hL, ofReal_im, abs_zero]; positivity
  have h := congrArg im (dlmf_4_13_1_2 hL)
  rw [add_log_im] at h
  have hre : ((2 * π * k : ℂ)).re = 2 * π * k := by
    rw [show (2 * π * k : ℂ) = ((2 * π * k : ℝ) : ℂ) by push_cast; ring, ofReal_re]
  simp only [add_im, log_im, mul_im, I_re, I_im, mul_zero, mul_one, hre] at h
  set w := wrightOmega (log z + 2 * π * k * I)
  obtain ⟨hθ1, hθ2⟩ := abs_le.mp hθ
  rcases lt_trichotomy w.im 0 with hη | hη | hη
  · have := (arg_mem_Ioo_of_im_neg hη).2
    rw [abs_of_neg hη]; linarith
  · rw [hη, abs_zero]; positivity
  · have := (arg_mem_Ioo_of_im_pos hη).1
    rw [abs_of_pos hη]; linarith

theorem neg_exp_neg_one_ne_zero : ((-Real.exp (-1) : ℝ) : ℂ) ≠ 0 := by
  rw [ofReal_ne_zero]; exact neg_ne_zero.mpr (Real.exp_pos _).ne'

/-- `W₀(z) → −1` as `z → −e⁻¹`. -/
theorem tendsto_lambertW_zero_neg_exp :
    Tendsto (lambertW 0) (𝓝 ((-Real.exp (-1) : ℝ) : ℂ)) (𝓝 (-1)) := by
  refine tendsto_neg_one_of_mul_exp ?_ (Eventually.of_forall fun z => ?_)
  · simp only [dlmf_4_13_1]; exact tendsto_id
  · by_cases hz : z = 0
    · rw [hz, lambertW_zero_arg, zero_im, abs_zero]; positivity
    · refine abs_im_lambertW_le 0 hz ?_
      simp only [Int.cast_zero, mul_zero, add_zero]
      exact (abs_arg_le_pi z).trans (by linarith [Real.pi_pos])

/-- `W_k(z) → −1` as `z → −e⁻¹` within a set where `|ph z + 2πk| ≤ 2π`. -/
theorem tendsto_lambertW_neg_exp_within (k : ℤ) {s : Set ℂ}
    (hs : ∀ z ∈ s, z ≠ 0 → |arg z + 2 * π * k| ≤ 2 * π) :
    Tendsto (lambertW k) (𝓝[s] ((-Real.exp (-1) : ℝ) : ℂ)) (𝓝 (-1)) := by
  refine tendsto_neg_one_of_mul_exp ?_ ?_
  · simp only [dlmf_4_13_1]; exact tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
  · have hne : ∀ᶠ z in 𝓝[s] ((-Real.exp (-1) : ℝ) : ℂ), z ≠ 0 :=
      nhdsWithin_le_nhds (isOpen_ne.mem_nhds neg_exp_neg_one_ne_zero)
    filter_upwards [hne, self_mem_nhdsWithin] with z hz hzs
    exact abs_im_lambertW_le k hz (hs z hzs hz)

/-- **DLMF 4.13.2** (the limits): `W₀` is continuous at `−e⁻¹`, and
`W₁(−e⁻¹ − 0i) = W_{−1}(−e⁻¹ + 0i) = −1` as limits from the lower and upper half-planes. -/
theorem dlmf_4_13_2_limits :
    ContinuousAt (lambertW 0) ((-Real.exp (-1) : ℝ) : ℂ) ∧
      Tendsto (lambertW 1) (𝓝[{z | z.im < 0}] ((-Real.exp (-1) : ℝ) : ℂ)) (𝓝 (-1)) ∧
      ContinuousWithinAt (lambertW (-1)) {z | 0 ≤ z.im} ((-Real.exp (-1) : ℝ) : ℂ) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [ContinuousAt, dlmf_4_13_2.1]; exact tendsto_lambertW_zero_neg_exp
  · refine tendsto_lambertW_neg_exp_within 1 fun z hz _ => ?_
    have h1 := neg_pi_lt_arg z
    have h2 : arg z < 0 := arg_neg_iff.mpr hz
    rw [abs_le]; push_cast; constructor <;> linarith
  · rw [ContinuousWithinAt, dlmf_4_13_2.2.1]
    refine tendsto_lambertW_neg_exp_within (-1) fun z hz _ => ?_
    have h1 := arg_le_pi z
    have h2 : 0 ≤ arg z := arg_nonneg_iff.mpr hz
    rw [abs_le]; push_cast; constructor <;> linarith

/-! ### Limits on the cut `(−∞, −e⁻¹)` -/

theorem log_ofReal_of_neg {x : ℝ} (hx : x < 0) : log (x : ℂ) = Real.log ‖(x : ℂ)‖ + π * I := by
  apply Complex.ext <;> simp [log_re, log_im, arg_ofReal_of_neg hx]

theorem not_omegaL_of_lt_neg_exp {x : ℝ} (hx : x < -Real.exp (-1)) (k : ℤ) :
    ¬omegaLm (log (x : ℂ) + 2 * π * k * I) ∧ ¬omegaLp (log (x : ℂ) + 2 * π * k * I) := by
  have hre : (log (x : ℂ) + 2 * π * k * I).re = Real.log (-x) := by
    simp [log_re, abs_of_neg (by linarith [Real.exp_pos (-1)] : x < 0)]
  have hl : -1 < Real.log (-x) := by
    rw [← Real.log_exp (-1)]; exact Real.log_lt_log (Real.exp_pos _) (by linarith)
  exact ⟨fun h => by linarith [h.2], fun h => by linarith [h.2]⟩

theorem continuousAt_wrightOmega_cut {x : ℝ} (hx : x < -Real.exp (-1)) (k : ℤ) :
    ContinuousAt wrightOmega (log (x : ℂ) + 2 * π * k * I) :=
  (hasDerivAt_wrightOmega (not_omegaL_of_lt_neg_exp hx k).1
    (not_omegaL_of_lt_neg_exp hx k).2).continuousAt

theorem lambertW_eventually_eq {z₀ : ℂ} (hz₀ : z₀ ≠ 0) (k : ℤ) :
    ∀ᶠ z in 𝓝 z₀, lambertW k z = wrightOmega (log z + 2 * π * k * I) :=
  (eventually_ne_nhds hz₀).mono fun _ hz => lambertW_of_ne hz

/-- On the cut `x < −e⁻¹`, every `W_k` is continuous from above. -/
theorem continuousWithinAt_lambertW_cut {x : ℝ} (hx : x < -Real.exp (-1)) (k : ℤ) :
    ContinuousWithinAt (lambertW k) {z : ℂ | 0 ≤ z.im} (x : ℂ) := by
  have hx0 : x < 0 := by linarith [Real.exp_pos (-1)]
  have hne : (x : ℂ) ≠ 0 := by exact_mod_cast hx0.ne
  have hlog := continuousWithinAt_log_of_re_neg_of_im_zero (z := (x : ℂ)) (by simpa using hx0)
    (by simp)
  have h2 : ContinuousWithinAt (fun z => log z + 2 * π * k * I) {z : ℂ | 0 ≤ z.im} (x : ℂ) :=
    hlog.add continuousWithinAt_const
  have h := ContinuousAt.comp_continuousWithinAt (f := fun z => log z + 2 * π * k * I)
    (continuousAt_wrightOmega_cut hx k) h2
  rw [ContinuousWithinAt, lambertW_of_ne hne]
  exact h.tendsto.congr' (nhdsWithin_le_nhds
    ((lambertW_eventually_eq hne k).mono fun _ h => h.symm))

/-- On the cut `x < −e⁻¹`, `W_k(x − 0i) = W_{k−1}(x)`. -/
theorem tendsto_lambertW_cut_below {x : ℝ} (hx : x < -Real.exp (-1)) (k : ℤ) :
    Tendsto (lambertW k) (𝓝[{z : ℂ | z.im < 0}] (x : ℂ)) (𝓝 (lambertW (k - 1) x)) := by
  have hx0 : x < 0 := by linarith [Real.exp_pos (-1)]
  have hne : (x : ℂ) ≠ 0 := by exact_mod_cast hx0.ne
  have hlog := tendsto_log_nhdsWithin_im_neg_of_re_neg_of_im_zero (z := (x : ℂ))
    (by simpa using hx0) (by simp)
  have hpt : (Real.log ‖(x : ℂ)‖ - π * I) + 2 * π * k * I =
      log (x : ℂ) + 2 * π * ((k - 1 : ℤ) : ℂ) * I := by
    rw [log_ofReal_of_neg hx0]; push_cast; ring
  have h2 := hlog.add (tendsto_const_nhds (x := 2 * π * (k : ℂ) * I))
  rw [hpt] at h2
  have h := (continuousAt_wrightOmega_cut hx (k - 1)).tendsto.comp h2
  rw [lambertW_of_ne hne]
  exact h.congr' (nhdsWithin_le_nhds ((lambertW_eventually_eq hne k).mono fun _ h => h.symm))

/-! ### Gluing the branches `W₀`, `W_{±1}` along a square-root coordinate -/

/-- The sheet over the variable `p` (`p` playing the role of a square root of `ez + 1`, or of
the `t` of 4.13.6): `W₀` for `ℜp > 0` (and on the upper imaginary axis), `W₁` in the second
quadrant, `W_{−1}` in the closed third quadrant (without the upper imaginary axis). -/
noncomputable def lambertGlue (p z : ℂ) : ℂ :=
  if 0 < p.re ∨ (p.re = 0 ∧ 0 ≤ p.im) then lambertW 0 z
  else if 0 < p.im then lambertW 1 z else lambertW (-1) z

/-- `ℑw` has the sign of `ℜp ℑp` (weakly). -/
def ImSign (p w : ℂ) : Prop := (0 ≤ p.re * p.im → 0 ≤ w.im) ∧ (p.re * p.im < 0 → w.im < 0)

theorem lambertGlue_mul_exp (p z : ℂ) : lambertGlue p z * exp (lambertGlue p z) = z := by
  unfold lambertGlue; split_ifs <;> exact dlmf_4_13_1 _ _

theorem tendsto_glue_piece {k : ℤ} {A S : Set ℂ} {Z : ℂ → ℂ} {p₀ v : ℂ}
    (hZ : ContinuousAt Z p₀) (hW : Tendsto (lambertW k) (𝓝[S] (Z p₀)) (𝓝 v))
    (hS : ∀ᶠ p in 𝓝[A] p₀, Z p ∈ S ∧ lambertGlue p (Z p) = lambertW k (Z p)) :
    Tendsto (fun p => lambertGlue p (Z p)) (𝓝[A] p₀) (𝓝 v) :=
  (hW.comp (tendsto_nhdsWithin_iff.mpr ⟨hZ.tendsto.mono_left nhdsWithin_le_nhds,
    hS.mono fun _ h => h.1⟩)).congr' (hS.mono fun _ h => h.2.symm)

theorem tendsto_split {f : ℂ → ℂ} {p₀ v : ℂ} (A : Set ℂ) (h1 : Tendsto f (𝓝[A] p₀) (𝓝 v))
    (h2 : Tendsto f (𝓝[Aᶜ] p₀) (𝓝 v)) : Tendsto f (𝓝 p₀) (𝓝 v) := by
  rw [← nhdsWithin_univ, ← union_compl_self A, nhdsWithin_union]
  exact h1.sup h2

theorem eventually_re_lt {p₀ : ℂ} (h : p₀.re < 0) : ∀ᶠ p in 𝓝 p₀, p.re < 0 :=
  continuous_re.continuousAt.eventually (Iio_mem_nhds h)

theorem eventually_re_gt {p₀ : ℂ} (h : 0 < p₀.re) : ∀ᶠ p in 𝓝 p₀, 0 < p.re :=
  continuous_re.continuousAt.eventually (Ioi_mem_nhds h)

theorem eventually_im_lt {p₀ : ℂ} (h : p₀.im < 0) : ∀ᶠ p in 𝓝 p₀, p.im < 0 :=
  continuous_im.continuousAt.eventually (Iio_mem_nhds h)

theorem eventually_im_gt {p₀ : ℂ} (h : 0 < p₀.im) : ∀ᶠ p in 𝓝 p₀, 0 < p.im :=
  continuous_im.continuousAt.eventually (Ioi_mem_nhds h)

theorem slitPlane_subset_cutW0 : slitPlane ⊆ cutW0 := by
  intro z hz ⟨h1, h2⟩
  rcases mem_slitPlane_iff.mp hz with h | h
  · linarith [Real.exp_pos (-1)]
  · exact h h1

/-- Continuity of the glued branch at `p₀`. -/
theorem continuousAt_lambertGlue {Z : ℂ → ℂ} {p₀ : ℂ} (hZ : ContinuousAt Z p₀)
    (h0 : 0 < p₀.re → Z p₀ ∈ cutW0) (h1 : p₀.re < 0 → p₀.im ≠ 0 → Z p₀ ∈ slitPlane)
    (hneg : p₀.re < 0 → p₀.im = 0 → ∃ x : ℝ, -Real.exp (-1) < x ∧ x < 0 ∧ Z p₀ = x)
    (himag : p₀.re = 0 → p₀.im ≠ 0 → ∃ x : ℝ, x < -Real.exp (-1) ∧ Z p₀ = x)
    (hzero : p₀ = 0 → Z p₀ = ((-Real.exp (-1) : ℝ) : ℂ))
    (hsign : p₀.re = 0 ∨ p₀.im = 0 → ∀ᶠ p in 𝓝 p₀, ImSign p (Z p)) :
    ContinuousAt (fun p => lambertGlue p (Z p)) p₀ := by
  rcases lt_trichotomy p₀.re 0 with hr | hr | hr
  · rcases lt_trichotomy p₀.im 0 with hi | hi | hi
    · -- third quadrant: `W_{−1}`
      have hc := ((dlmf_4_13_Wk_analytic (-1) _ (h1 hr hi.ne)).continuousAt).comp hZ
      refine hc.congr ?_
      filter_upwards [eventually_re_lt hr, eventually_im_lt hi] with p hp hq
      simp [lambertGlue, not_lt.mpr hp.le, hp.ne, not_lt.mpr hq.le]
    · -- negative real axis
      obtain ⟨x, hx1, hx2, hx⟩ := hneg hr hi
      have hev := hsign (Or.inr hi)
      rw [ContinuousAt]
      have hv : lambertGlue p₀ (Z p₀) = lambertW (-1) x := by
        simp [lambertGlue, not_lt.mpr hr.le, hr.ne, hi, hx]
      rw [hv]
      refine tendsto_split {p | 0 < p.im} ?_ ?_
      · rw [lambertW_neg_one_ofReal hx1.le hx2]
        refine tendsto_glue_piece (k := 1) (S := {z | z.im < 0}) hZ
          (by rw [hx]; exact tendsto_lambertW_one_below hx1 hx2) ?_
        filter_upwards [nhdsWithin_le_nhds hev, nhdsWithin_le_nhds (eventually_re_lt hr),
          self_mem_nhdsWithin] with p hs hp hq
        refine ⟨hs.2 (mul_neg_of_neg_of_pos hp hq), ?_⟩
        simp [lambertGlue, not_lt.mpr hp.le, hp.ne, show 0 < p.im from hq]
      · refine tendsto_glue_piece (k := -1) (S := {z | 0 ≤ z.im}) hZ
          (by rw [hx]; exact continuousWithinAt_lambertW_neg_one hx1 hx2) ?_
        filter_upwards [nhdsWithin_le_nhds hev, nhdsWithin_le_nhds (eventually_re_lt hr),
          self_mem_nhdsWithin] with p hs hp hq
        have hq' : p.im ≤ 0 := not_lt.mp hq
        refine ⟨hs.1 (mul_nonneg_of_nonpos_of_nonpos hp.le hq'), ?_⟩
        simp [lambertGlue, not_lt.mpr hp.le, hp.ne, not_lt.mpr hq']
    · -- second quadrant: `W₁`
      have hc := ((dlmf_4_13_Wk_analytic 1 _ (h1 hr hi.ne')).continuousAt).comp hZ
      refine hc.congr ?_
      filter_upwards [eventually_re_lt hr, eventually_im_gt hi] with p hp hq
      simp [lambertGlue, not_lt.mpr hp.le, hp.ne, hq]
  · rcases lt_trichotomy p₀.im 0 with hi | hi | hi
    · -- lower imaginary axis
      obtain ⟨x, hx1, hx⟩ := himag hr hi.ne
      have hev := hsign (Or.inl hr)
      rw [ContinuousAt]
      have hv : lambertGlue p₀ (Z p₀) = lambertW (-1) x := by
        simp [lambertGlue, hr, not_le.mpr hi, not_lt.mpr hi.le, hx]
      rw [hv]
      refine tendsto_split {p | 0 < p.re} ?_ ?_
      · refine tendsto_glue_piece (k := 0) (S := {z | z.im < 0}) hZ
          (by rw [hx]; simpa using tendsto_lambertW_cut_below hx1 0) ?_
        filter_upwards [nhdsWithin_le_nhds hev, nhdsWithin_le_nhds (eventually_im_lt hi),
          self_mem_nhdsWithin] with p hs hq hp
        refine ⟨hs.2 (mul_neg_of_pos_of_neg hp hq), ?_⟩
        simp [lambertGlue, show 0 < p.re from hp]
      · refine tendsto_glue_piece (k := -1) (S := {z | 0 ≤ z.im}) hZ
          (by rw [hx]; exact continuousWithinAt_lambertW_cut hx1 (-1)) ?_
        filter_upwards [nhdsWithin_le_nhds hev, nhdsWithin_le_nhds (eventually_im_lt hi),
          self_mem_nhdsWithin] with p hs hq hp
        have hp' : p.re ≤ 0 := not_lt.mp hp
        refine ⟨hs.1 (mul_nonneg_of_nonpos_of_nonpos hp' hq.le), ?_⟩
        simp [lambertGlue, not_lt.mpr hp', not_le.mpr hq, not_lt.mpr hq.le]
    · -- the branch point `p = 0`
      have hp0 : p₀ = 0 := Complex.ext hr hi
      have hz := hzero hp0
      have hev := hsign (Or.inl hr)
      rw [ContinuousAt, show lambertGlue p₀ (Z p₀) = -1 by
        rw [show lambertGlue p₀ (Z p₀) = lambertW 0 (Z p₀) by simp [lambertGlue, hr, hi], hz,
          dlmf_4_13_2.1]]
      have hZt : Tendsto Z (𝓝 p₀) (𝓝 ((-Real.exp (-1) : ℝ) : ℂ)) := by
        rw [← hz]; exact hZ.tendsto
      refine tendsto_neg_one_of_mul_exp (by simpa [lambertGlue_mul_exp] using hZt) ?_
      have hne : ∀ᶠ p in 𝓝 p₀, Z p ≠ 0 :=
        hZ.eventually (isOpen_ne.mem_nhds (by rw [hz]; exact neg_exp_neg_one_ne_zero))
      filter_upwards [hev, hne] with p hs hz0
      unfold lambertGlue
      split_ifs with ha hb
      · refine abs_im_lambertW_le 0 hz0 ?_
        simpa using (abs_arg_le_pi _).trans (by linarith [Real.pi_pos])
      · have hp : p.re < 0 := by
          rcases lt_trichotomy p.re 0 with h | h | h
          · exact h
          · exact absurd (Or.inr ⟨h, hb.le⟩) ha
          · exact absurd (Or.inl h) ha
        have him := hs.2 (mul_neg_of_neg_of_pos hp hb)
        refine abs_im_lambertW_le 1 hz0 ?_
        have := neg_pi_lt_arg (Z p)
        have := arg_neg_iff.mpr him
        rw [abs_le]; push_cast; constructor <;> linarith
      · have hq : p.im ≤ 0 := not_lt.mp hb
        have hp : p.re ≤ 0 := by
          by_contra h; exact ha (Or.inl (not_le.mp h))
        have him := hs.1 (mul_nonneg_of_nonpos_of_nonpos hp hq)
        refine abs_im_lambertW_le (-1) hz0 ?_
        have := arg_le_pi (Z p)
        have := arg_nonneg_iff.mpr him
        rw [abs_le]; push_cast; constructor <;> linarith
    · -- upper imaginary axis
      obtain ⟨x, hx1, hx⟩ := himag hr hi.ne'
      have hev := hsign (Or.inl hr)
      rw [ContinuousAt]
      have hv : lambertGlue p₀ (Z p₀) = lambertW 0 x := by
        simp [lambertGlue, hr, hi.le, hx]
      rw [hv]
      refine tendsto_split {p | 0 ≤ p.re} ?_ ?_
      · refine tendsto_glue_piece (k := 0) (S := {z | 0 ≤ z.im}) hZ
          (by rw [hx]; exact continuousWithinAt_lambertW_cut hx1 0) ?_
        filter_upwards [nhdsWithin_le_nhds hev, nhdsWithin_le_nhds (eventually_im_gt hi),
          self_mem_nhdsWithin] with p hs hq hp
        have hp' : 0 ≤ p.re := hp
        refine ⟨hs.1 (mul_nonneg hp' hq.le), ?_⟩
        have : 0 < p.re ∨ (p.re = 0 ∧ 0 ≤ p.im) := by
          rcases hp'.lt_or_eq with h | h
          · exact Or.inl h
          · exact Or.inr ⟨h.symm, hq.le⟩
        simp [lambertGlue, this]
      · refine tendsto_glue_piece (k := 1) (S := {z | z.im < 0}) hZ
          (by rw [hx]; simpa using tendsto_lambertW_cut_below hx1 1) ?_
        filter_upwards [nhdsWithin_le_nhds hev, nhdsWithin_le_nhds (eventually_im_gt hi),
          self_mem_nhdsWithin] with p hs hq hp
        have hp' : p.re < 0 := not_le.mp hp
        refine ⟨hs.2 (mul_neg_of_neg_of_pos hp' hq), ?_⟩
        simp [lambertGlue, not_lt.mpr hp'.le, hp'.ne, hq]
  · -- right half-plane: `W₀`
    have hc := ((analyticOnNhd_lambertW_zero _ (h0 hr)).continuousAt).comp hZ
    refine hc.congr ?_
    filter_upwards [eventually_re_gt hr] with p hp
    simp [lambertGlue, hp]

/-! ### Analyticity of a continuous solution of `w e^w = Z` -/

/-- A solution `f` of `f e^f = Z`, continuous at `p₀` with `f(p₀) ≠ −1`, is differentiable there
(it is the local inverse of `w e^w` composed with `Z`). -/
theorem differentiableAt_of_mul_exp {f Z : ℂ → ℂ} {p₀ : ℂ} (hf : ContinuousAt f p₀)
    (hZ : DifferentiableAt ℂ Z p₀) (heq : ∀ᶠ p in 𝓝 p₀, f p * exp (f p) = Z p)
    (h1 : f p₀ ≠ -1) : DifferentiableAt ℂ f p₀ := by
  set w₀ := f p₀
  have hs := hasStrictDerivAt_mul_exp w₀
  have hd : (1 + w₀) * exp w₀ ≠ 0 :=
    mul_ne_zero (fun e => h1 (by linear_combination e)) (exp_ne_zero _)
  have hg := hs.to_localInverse hd
  have hleft := hs.eventually_left_inverse hd
  have hZ0 : Z p₀ = w₀ * exp w₀ := heq.self_of_nhds.symm
  have hev : f =ᶠ[𝓝 p₀] fun p => hs.localInverse _ _ _ hd (Z p) := by
    filter_upwards [hf.eventually hleft, heq] with p h1 h2
    rw [← h2]; exact h1.symm
  refine (DifferentiableAt.comp p₀ ?_ hZ).congr_of_eventuallyEq hev
  rw [hZ0]; exact hg.hasDerivAt.differentiableAt

/-- The glued branch over `Z` is analytic on an open set `U ∋ 0` where `Z` is differentiable,
`Z = −e⁻¹` only at `0`, and the conditions of `continuousAt_lambertGlue` hold. -/
theorem differentiableOn_lambertGlue {Z : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U) (h0U : (0 : ℂ) ∈ U)
    (hZd : DifferentiableOn ℂ Z U)
    (hcont : ∀ p ∈ U, ContinuousAt (fun p => lambertGlue p (Z p)) p)
    (hm1 : ∀ p ∈ U, Z p = ((-Real.exp (-1) : ℝ) : ℂ) → p = 0) :
    DifferentiableOn ℂ (fun p => lambertGlue p (Z p)) U := by
  rw [← Complex.differentiableOn_compl_singleton_and_continuousAt_iff (hU.mem_nhds h0U)]
  refine ⟨fun p hp => ?_, hcont 0 h0U⟩
  have hpU : p ∈ U := hp.1
  refine (differentiableAt_of_mul_exp (hcont p hpU) (hZd.differentiableAt (hU.mem_nhds hpU))
    (Eventually.of_forall fun q => lambertGlue_mul_exp q (Z q)) fun e => ?_).differentiableWithinAt
  have h := lambertGlue_mul_exp p (Z p)
  rw [e] at h
  exact hp.2 (hm1 p hpU (by rw [← h]; push_cast; ring))

end Azurite.DLMF
