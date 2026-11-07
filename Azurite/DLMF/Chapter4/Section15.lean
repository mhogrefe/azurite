/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Mathlib.Analysis.SpecialFunctions.Complex.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Azurite.DLMF.Chapter4.Section2
import Azurite.DLMF.Chapter4.Section14

/-!
# DLMF §4.15 Graphics (trigonometric and inverse trigonometric functions)

The inverse trigonometric functions are only defined in DLMF §4.23, so their definitions are
formalized here first, from the integrals of §4.23(i):

* general values: `arcsinGen` (4.23.1, `C¹` paths from `0` avoiding `±1`, the square root
  continued from its principal value at `t = 0`), `arccosGen` (4.23.2), `arccscGen`, `arcsecGen`
  (4.23.4–4.23.5); `mem_arcsinGen_iff`, `mem_arccosGen_iff` (the values solve `sin w = z`,
  `cos w = z`), via `sin_cos_of_arcsin_path`;
* principal values (§4.23(ii)): `arcsinD`, `arctanD` (4.23.1, 4.23.3 along the segment `[0, z]`,
  which does not cross the cuts `arcsinCut`, `arctanCut`), `arccosD` (4.23.2 along `[z, 0]` and
  `[0, 1]`), `arccscD`, `arcsecD`, `arccotD` (4.23.7–4.23.9); `arctanD_eq` (`= Complex.arctan`),
  `dlmf_4_23_16`, `dlmf_4_23_17`.

§4.15 itself:

* Figure 4.15.2: `dlmf_4_15_F2`; Figure 4.15.4: `dlmf_4_15_F4`; Figure 4.15.6: `dlmf_4_15_F6`,
  `dlmf_4_15_F6_real`.
* Figure 4.15.7 (`w = sin z` on the strip `sinStrip`): `dlmf_4_15_F7_bijOn`, `_inverse`,
  `_conformal`, `_ellipses`, `_hyperbolas` (**erratum** `_not_rectangular`), `_points`,
  `_points_D`, `_edges`.
* Branch cuts of Figures 4.15.9, 4.15.11, 4.15.13: `dlmf_4_15_F9`, `dlmf_4_15_F11`,
  `dlmf_4_15_F13`.
* 4.15.1–4.15.3: `dlmf_4_15_1`, `dlmf_4_15_2`, `dlmf_4_15_3`.
-/

open Set Filter Topology Complex MeasureTheory
open scoped Real Interval

namespace Azurite.DLMF

/-! ### General values (DLMF §4.23(i)) -/

/-- **DLMF 4.23.1** (general values): `w ∈ Arcsin z` when `w = ∫₀^z dt/(1 − t²)^{1/2}` along a
C¹ path `γ : [0, 1] → ℂ` from `0` to `z` that does not pass through `±1`. The square root `g` is
continued continuously along the path from its principal value `1` at the start `t = 0`. -/
def arcsinGen (z : ℂ) : Set ℂ :=
  {w | ∃ γ γ' g : ℝ → ℂ, γ 0 = 0 ∧ γ 1 = z ∧
    (∀ s ∈ Icc (0 : ℝ) 1, HasDerivWithinAt γ (γ' s) (Icc 0 1) s) ∧ ContinuousOn γ' (Icc 0 1) ∧
    (∀ s ∈ Icc (0 : ℝ) 1, γ s ≠ 1 ∧ γ s ≠ -1) ∧ ContinuousOn g (Icc 0 1) ∧
    (∀ s ∈ Icc (0 : ℝ) 1, g s ^ 2 = 1 - γ s ^ 2) ∧ g 0 = 1 ∧
    w = ∫ s in (0 : ℝ)..1, γ' s / g s}

/-- A continuous square root of a differentiable function is differentiable where nonzero. -/
theorem hasDerivAt_of_sq_eq {g q : ℝ → ℂ} {s : ℝ} {q' : ℂ} (hq : HasDerivAt q q' s)
    (hg : ContinuousAt g s) (hsq : ∀ᶠ u in 𝓝 s, g u ^ 2 = q u) (hne : g s ≠ 0) :
    HasDerivAt g (q' / (2 * g s)) s := by
  rw [hasDerivAt_iff_tendsto_slope] at hq ⊢
  have h2 : Tendsto (fun u => g u + g s) (𝓝[≠] s) (𝓝 (2 * g s)) := by
    have : Tendsto (fun u => g u + g s) (𝓝[≠] s) (𝓝 (g s + g s)) :=
      (hg.tendsto.add (tendsto_const_nhds (x := g s))).mono_left nhdsWithin_le_nhds
    rwa [← two_mul] at this
  have h20 : (2 : ℂ) * g s ≠ 0 := mul_ne_zero two_ne_zero hne
  refine (hq.div h2 h20).congr' ?_
  have hev : ∀ᶠ u in 𝓝[≠] s, g u + g s ≠ 0 := h2.eventually_ne h20
  have hss : g s ^ 2 = q s := hsq.self_of_nhds
  filter_upwards [hev, nhdsWithin_le_nhds hsq] with u hu hsu
  rw [Pi.div_apply, slope_def_module, slope_def_module, ← hsu, ← hss, Complex.real_smul,
    Complex.real_smul]
  field_simp
  ring

/-- A function on `[0, 1]`, continuous there with zero derivative inside, is constant. -/
theorem eq_of_hasDerivAt_zero_Icc {f : ℝ → ℂ} (hc : ContinuousOn f (Icc 0 1))
    (hd : ∀ s ∈ Ioo (0 : ℝ) 1, HasDerivAt f 0 s) : ∀ s ∈ Icc (0 : ℝ) 1, f s = f 0 := by
  intro s hs
  rcases hs.1.eq_or_lt with h | h
  · rw [← h]
  have hsub : Icc 0 s ⊆ Icc (0 : ℝ) 1 := Icc_subset_Icc le_rfl hs.2
  have key : ∀ L : ℂ →L[ℝ] ℝ, L (f s) = L (f 0) := by
    intro L
    obtain ⟨c, -, hcs⟩ := exists_hasDerivAt_eq_slope (fun x => L (f x)) (fun _ => 0) h
      (L.continuous.comp_continuousOn (hc.mono hsub))
      (fun x hx => by
        have := L.hasFDerivAt.comp_hasDerivAt x (hd x ⟨hx.1, hx.2.trans_le hs.2⟩)
        simp only [map_zero] at this
        exact this)
    rw [eq_comm, div_eq_zero_iff] at hcs
    rcases hcs with hcs | hcs
    · linarith
    · linarith
  apply Complex.ext
  · simpa using key reCLM
  · simpa using key imCLM

/-- The key property of a 4.23.1 path: along it, `Φ(s) = ∫₀^{γ(s)} dt/(1 − t²)^{1/2}` satisfies
`sin Φ(s) = γ(s)` and `cos Φ(s) = g(s)`. -/
theorem sin_cos_of_arcsin_path {γ γ' g : ℝ → ℂ} (h0 : γ 0 = 0)
    (hγ : ∀ s ∈ Icc (0 : ℝ) 1, HasDerivWithinAt γ (γ' s) (Icc 0 1) s)
    (hγ' : ContinuousOn γ' (Icc 0 1)) (hne : ∀ s ∈ Icc (0 : ℝ) 1, γ s ≠ 1 ∧ γ s ≠ -1)
    (hg : ContinuousOn g (Icc 0 1)) (hsq : ∀ s ∈ Icc (0 : ℝ) 1, g s ^ 2 = 1 - γ s ^ 2)
    (hg0 : g 0 = 1) :
    ∀ s ∈ Icc (0 : ℝ) 1, sin (∫ u in (0 : ℝ)..s, γ' u / g u) = γ s ∧
      cos (∫ u in (0 : ℝ)..s, γ' u / g u) = g s := by
  have hgne : ∀ s ∈ Icc (0 : ℝ) 1, g s ≠ 0 := by
    intro s hs h
    have h' := hsq s hs
    rw [h] at h'
    have : (1 - γ s) * (1 + γ s) = 0 := by linear_combination -h'
    rcases mul_eq_zero.mp this with h1 | h1
    · exact (hne s hs).1 (by linear_combination -h1)
    · exact (hne s hs).2 (by linear_combination h1)
  set f : ℝ → ℂ := fun u => γ' u / g u with hf
  have hfc : ContinuousOn f (Icc 0 1) := hγ'.div hg hgne
  set Φ : ℝ → ℂ := fun s => ∫ u in (0 : ℝ)..s, f u with hΦ
  have hΦc : ContinuousOn Φ (Icc 0 1) := by
    have := intervalIntegral.continuousOn_primitive_interval (a := (0 : ℝ)) (b := 1)
      (μ := volume) (f := f) (by rw [uIcc_of_le zero_le_one]; exact hfc.integrableOn_Icc)
    rwa [uIcc_of_le zero_le_one] at this
  have hΦd : ∀ s ∈ Ioo (0 : ℝ) 1, HasDerivAt Φ (f s) s := by
    intro s hs
    apply intervalIntegral.integral_hasDerivAt_right
    · apply ContinuousOn.intervalIntegrable
      rw [uIcc_of_le hs.1.le]
      exact hfc.mono (Icc_subset_Icc le_rfl hs.2.le)
    · exact (hfc.mono Ioo_subset_Icc_self).stronglyMeasurableAtFilter isOpen_Ioo s hs
    · exact hfc.continuousAt (Icc_mem_nhds hs.1 hs.2)
  have hγd : ∀ s ∈ Ioo (0 : ℝ) 1, HasDerivAt γ (γ' s) s := fun s hs =>
    (hγ s (Ioo_subset_Icc_self hs)).hasDerivAt (Icc_mem_nhds hs.1 hs.2)
  have hgd : ∀ s ∈ Ioo (0 : ℝ) 1, HasDerivAt g (-(2 * γ s * γ' s) / (2 * g s)) s := by
    intro s hs
    have hsI : Icc (0 : ℝ) 1 ∈ 𝓝 s := Icc_mem_nhds hs.1 hs.2
    have hq : HasDerivAt (fun u => 1 - γ u ^ 2) (-(2 * γ s * γ' s)) s := by
      have := ((hγd s hs).pow 2).const_sub 1
      convert this using 1
      simp only [Nat.cast_ofNat]
      ring
    exact hasDerivAt_of_sq_eq hq (hg.continuousAt hsI)
      (Filter.mem_of_superset hsI fun u hu => hsq u hu) (hgne s (Ioo_subset_Icc_self hs))
  have hγc : ContinuousOn γ (Icc 0 1) := fun s hs => (hγ s hs).continuousWithinAt
  have hcos := continuous_cos.comp_continuousOn hΦc
  have hsin := continuous_sin.comp_continuousOn hΦc
  set E : ℝ → ℂ := fun s => γ s * cos (Φ s) - g s * sin (Φ s) with hE
  set F : ℝ → ℂ := fun s => g s * cos (Φ s) + γ s * sin (Φ s) with hF
  have hEc : ContinuousOn E (Icc 0 1) := (hγc.mul hcos).sub (hg.mul hsin)
  have hFc : ContinuousOn F (Icc 0 1) := (hg.mul hcos).add (hγc.mul hsin)
  have hEd : ∀ s ∈ Ioo (0 : ℝ) 1, HasDerivAt E 0 s := by
    intro s hs
    have hc := (Complex.hasDerivAt_cos (Φ s)).comp s (hΦd s hs)
    have hsn := (Complex.hasDerivAt_sin (Φ s)).comp s (hΦd s hs)
    have := ((hγd s hs).mul hc).sub ((hgd s hs).mul hsn)
    refine this.congr_deriv ?_
    have := hgne s (Ioo_subset_Icc_self hs)
    simp only [hf, Function.comp_apply]
    field_simp
    ring
  have hFd : ∀ s ∈ Ioo (0 : ℝ) 1, HasDerivAt F 0 s := by
    intro s hs
    have hc := (Complex.hasDerivAt_cos (Φ s)).comp s (hΦd s hs)
    have hsn := (Complex.hasDerivAt_sin (Φ s)).comp s (hΦd s hs)
    have := ((hgd s hs).mul hc).add ((hγd s hs).mul hsn)
    refine this.congr_deriv ?_
    have := hgne s (Ioo_subset_Icc_self hs)
    simp only [hf, Function.comp_apply]
    field_simp
    ring
  have hE0 : E 0 = 0 := by simp [hE, hΦ, h0]
  have hF0 : F 0 = 1 := by simp [hF, hΦ, h0, hg0]
  intro s hs
  have e := eq_of_hasDerivAt_zero_Icc hEc hEd s hs
  have f' := eq_of_hasDerivAt_zero_Icc hFc hFd s hs
  rw [hE0] at e
  rw [hF0] at f'
  simp only [hE, hF] at e f'
  have hsc := sin_sq_add_cos_sq (Φ s)
  constructor
  · linear_combination (-cos (Φ s)) * e - sin (Φ s) * f' + γ s * hsc
  · linear_combination sin (Φ s) * e - cos (Φ s) * f' + g s * hsc

/-- **DLMF 4.23.1** (general values): for `z ≠ ±1` the values of `Arcsin z` are exactly the
solutions `w` of `sin w = z` (compare 4.23.28 and 4.23.31). -/
theorem mem_arcsinGen_iff {z w : ℂ} (h1 : z ≠ 1) (h2 : z ≠ -1) :
    w ∈ arcsinGen z ↔ sin w = z := by
  constructor
  · rintro ⟨γ, γ', g, h0, h1', hγ, hγ', hne, hg, hsq, hg0, rfl⟩
    rw [← h1']
    exact (sin_cos_of_arcsin_path h0 hγ hγ' hne hg hsq hg0 1 ⟨zero_le_one, le_rfl⟩).1
  · intro hw
    have hcw : cos w ≠ 0 := by
      intro hc
      have h' := sin_sq_add_cos_sq w
      rw [hc, hw] at h'
      have : (z - 1) * (z + 1) = 0 := by linear_combination h'
      rcases mul_eq_zero.mp this with h | h
      · exact h1 (by linear_combination h)
      · exact h2 (by linear_combination h)
    set c : ℂ := if 0 ≤ w.im then 1 else -1 with hc
    set ℓ : ℝ → ℂ := fun s => s * w + I * c * (s - s ^ 2) with hℓdef
    set ℓ' : ℝ → ℂ := fun s => w + I * c * (1 - 2 * s) with hℓ'def
    have hℓ : ∀ s, HasDerivAt ℓ (ℓ' s) s := by
      intro s
      have h := ((hasDerivAt_id s).ofReal_comp.mul_const w).add
        (((hasDerivAt_id s).sub ((hasDerivAt_id s).pow 2)).ofReal_comp.const_mul (I * c))
      convert h using 1
      · ext u
        simp [hℓdef]
      · simp [hℓ'def]
    have hℓc : Continuous ℓ := continuous_iff_continuousAt.mpr fun s => (hℓ s).continuousAt
    have hℓ'c : Continuous ℓ' := by
      simp only [hℓ'def]
      fun_prop
    have hcl : ∀ s ∈ Icc (0 : ℝ) 1, cos (ℓ s) ≠ 0 := by
      intro s hs hcs
      rcases hs.1.eq_or_lt with h | h
      · rw [← h] at hcs
        simp [hℓdef] at hcs
      rcases hs.2.eq_or_lt with h' | h'
      · rw [h'] at hcs
        simp [hℓdef] at hcs
        exact hcw hcs
      obtain ⟨k, hk⟩ := Complex.cos_eq_zero_iff.mp hcs
      have him := congrArg im hk
      have hpos : 0 < s - s ^ 2 := by nlinarith
      by_cases hw0 : 0 ≤ w.im
      · simp [hℓdef, hc, hw0, ← ofReal_pow] at him
        nlinarith
      · simp [hℓdef, hc, hw0, ← ofReal_pow] at him
        nlinarith
    refine ⟨fun s => sin (ℓ s), fun s => cos (ℓ s) * ℓ' s, fun s => cos (ℓ s), ?_, ?_, ?_, ?_,
      ?_, ?_, ?_, ?_, ?_⟩
    · simp [hℓdef]
    · simpa [hℓdef] using hw
    · exact fun s _ => ((Complex.hasDerivAt_sin _).comp s (hℓ s)).hasDerivWithinAt
    · exact ((continuous_cos.comp hℓc).mul hℓ'c).continuousOn
    · intro s hs
      have hsc := sin_sq_add_cos_sq (ℓ s)
      refine ⟨fun h => hcl s hs ?_, fun h => hcl s hs ?_⟩ <;> simp only at h <;>
        rw [h] at hsc <;>
        exact pow_eq_zero_iff (n := 2) two_ne_zero |>.mp (by linear_combination hsc)
    · exact (continuous_cos.comp hℓc).continuousOn
    · intro s _
      linear_combination sin_sq_add_cos_sq (ℓ s)
    · simp [hℓdef]
    · rw [intervalIntegral.integral_congr (g := ℓ') (fun s hs => by
        rw [uIcc_of_le zero_le_one] at hs
        exact mul_div_cancel_left₀ _ (hcl s hs)),
        intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hℓ s)
          (hℓ'c.intervalIntegrable _ _)]
      simp [hℓdef]

/-! ### Principal values (DLMF §4.23(ii)) -/

/-- Real and imaginary parts of `sin z` and `cos z`. -/
theorem re_sin (z : ℂ) : (sin z).re = Real.sin z.re * Real.cosh z.im := by
  rw [sin_eq]; simp [← ofReal_sin, ← ofReal_cos, ← ofReal_cosh, ← ofReal_sinh]

theorem im_sin (z : ℂ) : (sin z).im = Real.cos z.re * Real.sinh z.im := by
  rw [sin_eq]; simp [← ofReal_sin, ← ofReal_cos, ← ofReal_cosh, ← ofReal_sinh]

theorem re_cos (z : ℂ) : (cos z).re = Real.cos z.re * Real.cosh z.im := by
  rw [cos_eq]; simp [← ofReal_sin, ← ofReal_cos, ← ofReal_cosh, ← ofReal_sinh]

theorem im_cos (z : ℂ) : (cos z).im = -(Real.sin z.re * Real.sinh z.im) := by
  rw [cos_eq]; simp [← ofReal_sin, ← ofReal_cos, ← ofReal_cosh, ← ofReal_sinh]

theorem sq_cpow_one_half (u : ℂ) : (u ^ (1 / 2 : ℂ)) ^ 2 = u := by
  have := cpow_nat_inv_pow u (n := 2) two_ne_zero
  rwa [Nat.cast_ofNat, ← one_div] at this

/-- The principal square root of a point of the cut plane has positive real part. -/
theorem re_cpow_half_pos_of_mem_slitPlane {u : ℂ} (hu : u ∈ slitPlane) :
    0 < (u ^ (1 / 2 : ℂ)).re := by
  rw [cpow_def_of_ne_zero (slitPlane_ne_zero hu), exp_re]
  apply mul_pos (Real.exp_pos _)
  apply Real.cos_pos_of_mem_Ioo
  have h1 := neg_pi_lt_arg u
  have h2 : arg u < π := lt_of_le_of_ne (arg_le_pi u) (mem_slitPlane_iff_arg.mp hu).1
  have : (log u * (1 / 2 : ℂ)).im = arg u / 2 := by simp [log_im, div_eq_mul_inv]
  rw [this]
  constructor <;> linarith

/-- The `z`-plane cut along `(−∞, −1]` and `[1, ∞)` (DLMF Figure 4.23.1(i)). -/
def arcsinCut : Set ℂ := {z | z.im ≠ 0 ∨ |z.re| < 1}

/-- The strip `−π/2 < Re z < π/2`. -/
def sinStrip : Set ℂ := {z | -(π / 2) < z.re ∧ z.re < π / 2}

theorem isOpen_sinStrip : IsOpen sinStrip :=
  (isOpen_lt continuous_const continuous_re).inter (isOpen_lt continuous_re continuous_const)

theorem cos_re_pos_of_mem_sinStrip {z : ℂ} (hz : z ∈ sinStrip) : 0 < Real.cos z.re :=
  Real.cos_pos_of_mem_Ioo ⟨hz.1, hz.2⟩

theorem cos_ne_zero_of_mem_sinStrip {z : ℂ} (hz : z ∈ sinStrip) : cos z ≠ 0 := by
  intro h
  have := congrArg re h
  rw [re_cos, zero_re] at this
  exact (mul_pos (cos_re_pos_of_mem_sinStrip hz) (Real.cosh_pos _)).ne' this

/-- On the segment `[0, z]` with `z` off the cuts, `1 − t²` stays in the cut plane of the
principal square root. -/
theorem one_sub_sq_mem_slitPlane {z : ℂ} (hz : z ∈ arcsinCut) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    1 - (s * z) ^ 2 ∈ slitPlane := by
  rw [mem_slitPlane_iff]
  by_contra h
  push Not at h
  obtain ⟨hre, him⟩ := h
  simp only [sub_re, one_re, sq, mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero, mul_im,
    sub_im, one_im, zero_sub, neg_eq_zero] at hre him
  have hs0 := hs.1
  have hs1 := hs.2
  rcases hz with hz | hz
  · -- `Im z ≠ 0`: then `s = 0` or `Re z = 0`
    have : s * z.re * (s * z.im) = 0 := by linarith
    have hsz : s * z.re = 0 ∨ s = 0 := by
      rcases mul_eq_zero.mp this with h | h
      · exact Or.inl h
      · rcases mul_eq_zero.mp h with h | h
        · exact Or.inr h
        · exact absurd h hz
    rcases hsz with h | h
    · rw [h] at hre; nlinarith
    · rw [h] at hre; nlinarith
  · have hx : z.re ^ 2 < 1 := by nlinarith [abs_lt.mp hz]
    nlinarith [mul_nonneg hs0 hs0, sq_nonneg (s * z.im), mul_le_mul_of_nonneg_left hs1 hs0]

/-- **DLMF §4.23(ii)**, principal value `arcsin z`: the integral 4.23.1 taken along the segment
`[0, z]`, which does not cross the cuts of Figure 4.23.1(i). On it `(1 − t²)^{1/2}` is the
principal square root, which is continuous there and principal on `(−1, 1)`. -/
noncomputable def arcsinD (z : ℂ) : ℂ :=
  ∫ s in (0 : ℝ)..1, z / (1 - (s * z) ^ 2) ^ (1 / 2 : ℂ)

/-- The principal value `arcsin z` (`z` off the cuts) is one of the general values 4.23.1, lies in
the strip `|Re| < π/2`, and satisfies `sin(arcsin z) = z`, `cos(arcsin z) = (1 − z²)^{1/2}`. -/
theorem arcsinD_props {z : ℂ} (hz : z ∈ arcsinCut) :
    arcsinD z ∈ arcsinGen z ∧ arcsinD z ∈ sinStrip ∧ sin (arcsinD z) = z ∧
      cos (arcsinD z) = (1 - z ^ 2) ^ (1 / 2 : ℂ) := by
  set γ : ℝ → ℂ := fun s => s * z with hγdef
  set g : ℝ → ℂ := fun s => (1 - (s * z) ^ 2) ^ (1 / 2 : ℂ) with hgdef
  have hγ : ∀ s ∈ Icc (0 : ℝ) 1, HasDerivWithinAt γ z (Icc 0 1) s := fun s _ => by
    simpa using ((hasDerivAt_id s).ofReal_comp.mul_const z).hasDerivWithinAt
  have hgc : ContinuousOn g (Icc 0 1) := fun s hs =>
    (ContinuousAt.comp (f := fun s : ℝ => 1 - ((s : ℂ) * z) ^ 2)
      (g := fun u : ℂ => u ^ (1 / 2 : ℂ)) (x := s)
      (continuousAt_cpow_const (one_sub_sq_mem_slitPlane hz hs)) (by fun_prop)).continuousWithinAt
  have hne : ∀ s ∈ Icc (0 : ℝ) 1, γ s ≠ 1 ∧ γ s ≠ -1 := by
    intro s hs
    have h := slitPlane_ne_zero (one_sub_sq_mem_slitPlane hz hs)
    constructor <;> intro h' <;> apply h <;> simp only [hγdef] at h' <;> rw [h'] <;> ring
  have hsq : ∀ s ∈ Icc (0 : ℝ) 1, g s ^ 2 = 1 - γ s ^ 2 := fun s _ => sq_cpow_one_half _
  have hg0 : g 0 = 1 := by simp [hgdef]
  have hpath := sin_cos_of_arcsin_path (γ := γ) (γ' := fun _ => z) (g := g) (by simp [hγdef])
    hγ continuousOn_const hne hgc hsq hg0
  set Φ : ℝ → ℂ := fun s => ∫ u in (0 : ℝ)..s, z / g u with hΦ
  have hΦ1 : Φ 1 = arcsinD z := rfl
  have hgne : ∀ s ∈ Icc (0 : ℝ) 1, g s ≠ 0 := fun s hs h => by
    have := hsq s hs
    rw [h] at this
    exact (hne s hs).1 (by
      have h2 : (1 - γ s) * (1 + γ s) = 0 := by linear_combination -this
      rcases mul_eq_zero.mp h2 with h3 | h3
      · linear_combination -h3
      · exact absurd (by linear_combination h3) (hne s hs).2)
  have hΦc : ContinuousOn Φ (Icc 0 1) := by
    have := intervalIntegral.continuousOn_primitive_interval (a := (0 : ℝ)) (b := 1)
      (μ := volume) (f := fun u => z / g u)
      (by rw [uIcc_of_le zero_le_one]; exact (continuousOn_const.div hgc hgne).integrableOn_Icc)
    rwa [uIcc_of_le zero_le_one] at this
  have hcos : ∀ s ∈ Icc (0 : ℝ) 1, 0 < Real.cos (Φ s).re := by
    intro s hs
    have h1 : 0 < (g s).re := re_cpow_half_pos_of_mem_slitPlane (one_sub_sq_mem_slitPlane hz hs)
    rw [← (hpath s hs).2, re_cos] at h1
    exact pos_of_mul_pos_left h1 (Real.cosh_pos _).le
  have hrec : ContinuousOn (fun s => (Φ s).re) (Icc 0 1) := continuous_re.comp_continuousOn hΦc
  have hΦ0 : (Φ 0).re = 0 := by simp [hΦ]
  have hstrip : Φ 1 ∈ sinStrip := by
    constructor
    · by_contra h
      push Not at h
      obtain ⟨s, hs, hs'⟩ := intermediate_value_Icc' zero_le_one hrec
        ⟨h, by show -(π / 2) ≤ (Φ 0).re; rw [hΦ0]; linarith [Real.pi_pos]⟩
      have := hcos s hs
      simp only at hs'
      rw [hs', Real.cos_neg, Real.cos_pi_div_two] at this
      exact lt_irrefl _ this
    · by_contra h
      push Not at h
      obtain ⟨s, hs, hs'⟩ := intermediate_value_Icc zero_le_one hrec
        ⟨by show (Φ 0).re ≤ π / 2; rw [hΦ0]; linarith [Real.pi_pos], h⟩
      have := hcos s hs
      simp only at hs'
      rw [hs', Real.cos_pi_div_two] at this
      exact lt_irrefl _ this
  have h1 := hpath 1 ⟨zero_le_one, le_rfl⟩
  refine ⟨⟨γ, fun _ => z, g, by simp [hγdef], by simp [hγdef], hγ, continuousOn_const, hne, hgc,
    hsq, hg0, rfl⟩, hstrip, ?_, ?_⟩
  · rw [← hΦ1, h1.1]; simp [hγdef]
  · rw [← hΦ1, h1.2]; simp [hgdef]

/-- `sin` is injective on the strip `|Re z| < π/2`. -/
theorem injOn_sin_sinStrip : InjOn sin sinStrip := by
  intro a ha b hb h
  obtain ⟨k, hk | hk⟩ := sin_eq_sin_iff.mp h
  · have hre := congrArg re hk
    simp at hre
    have h1 : (k : ℝ) * π < π / 2 := by nlinarith [ha.1, ha.2, hb.1, hb.2]
    have h2 : -(π / 2) < (k : ℝ) * π := by nlinarith [ha.1, ha.2, hb.1, hb.2]
    have hk1 : (k : ℝ) < 1 := by
      by_contra hc; push Not at hc; nlinarith [Real.pi_pos]
    have hk2 : (-1 : ℝ) < k := by
      by_contra hc; push Not at hc; nlinarith [Real.pi_pos]
    have : k = 0 := by
      have : k < 1 := by exact_mod_cast hk1
      have : -1 < k := by exact_mod_cast hk2
      omega
    rw [hk, this]; simp
  · have hre := congrArg re hk
    simp at hre
    have h1 : (2 * (k : ℝ) + 1) * π < π := by nlinarith [ha.1, ha.2, hb.1, hb.2]
    have h2 : -π < (2 * (k : ℝ) + 1) * π := by nlinarith [ha.1, ha.2, hb.1, hb.2]
    have hk1 : (k : ℝ) < 0 := by
      by_contra hc; push Not at hc; nlinarith [Real.pi_pos]
    have hk2 : (-1 : ℝ) < k := by
      by_contra hc; push Not at hc; nlinarith [Real.pi_pos]
    have : k < 0 := by exact_mod_cast hk1
    have : -1 < k := by exact_mod_cast hk2
    omega

theorem sin_mem_arcsinCut {z : ℂ} (hz : z ∈ sinStrip) : sin z ∈ arcsinCut := by
  by_cases h : (sin z).im = 0
  · right
    rw [im_sin] at h
    have hsh : Real.sinh z.im = 0 :=
      (mul_eq_zero.mp h).resolve_left (cos_re_pos_of_mem_sinStrip hz).ne'
    have hy : z.im = 0 := Real.sinh_eq_zero.mp hsh
    rw [re_sin, hy, Real.cosh_zero, mul_one]
    have hc := cos_re_pos_of_mem_sinStrip hz
    have hsc := Real.sin_sq_add_cos_sq z.re
    have : Real.sin z.re ^ 2 < 1 := by nlinarith
    exact abs_lt.mpr ⟨by nlinarith, by nlinarith⟩
  · exact Or.inl h

theorem arcsinD_sin {z : ℂ} (hz : z ∈ sinStrip) : arcsinD (sin z) = z := by
  obtain ⟨-, h1, h2, -⟩ := arcsinD_props (sin_mem_arcsinCut hz)
  exact injOn_sin_sinStrip h1 hz h2

/-- **Figure 4.15.7**: `w = sin z` maps the strip `−π/2 < Re z < π/2` bijectively onto the
`w`-plane cut along `(−∞, −1]` and `[1, ∞)`. -/
theorem dlmf_4_15_F7_bijOn : BijOn sin sinStrip arcsinCut :=
  ⟨fun _ hz => sin_mem_arcsinCut hz, injOn_sin_sinStrip, fun w hw =>
    ⟨arcsinD w, (arcsinD_props hw).2.1, (arcsinD_props hw).2.2.1⟩⟩

/-- **Figure 4.15.7**: on the strip and the cut plane, `z = arcsin w` and `w = sin z` are
inverse. -/
theorem dlmf_4_15_F7_inverse :
    (∀ z ∈ sinStrip, arcsinD (sin z) = z) ∧ (∀ w ∈ arcsinCut, sin (arcsinD w) = w) :=
  ⟨fun _ hz => arcsinD_sin hz, fun _ hw => (arcsinD_props hw).2.2.1⟩

/-- `arcsin` is holomorphic off the cuts, with derivative `(1 − w²)^{−1/2}`. -/
theorem hasStrictDerivAt_arcsinD {w : ℂ} (hw : w ∈ arcsinCut) :
    HasStrictDerivAt arcsinD ((1 - w ^ 2) ^ (1 / 2 : ℂ))⁻¹ w := by
  obtain ⟨-, hs, hsin, hcos⟩ := arcsinD_props hw
  have h := (hasStrictDerivAt_sin (arcsinD w)).to_local_left_inverse
    (cos_ne_zero_of_mem_sinStrip hs)
    (Filter.mem_of_superset (isOpen_sinStrip.mem_nhds hs) fun x hx => arcsinD_sin hx)
  rwa [hsin, hcos] at h

/-- **Figure 4.15.7**: the map is conformal: `sin z` and `arcsin w` are holomorphic with
nonvanishing derivatives on the strip and on the cut plane. -/
theorem dlmf_4_15_F7_conformal :
    (∀ z ∈ sinStrip, HasDerivAt sin (cos z) z ∧ cos z ≠ 0) ∧
      (∀ w ∈ arcsinCut, HasDerivAt arcsinD ((1 - w ^ 2) ^ (1 / 2 : ℂ))⁻¹ w ∧
        (1 - w ^ 2) ^ (1 / 2 : ℂ) ≠ 0) := by
  refine ⟨fun z hz => ⟨hasDerivAt_sin z, cos_ne_zero_of_mem_sinStrip hz⟩, fun w hw =>
    ⟨(hasStrictDerivAt_arcsinD hw).hasDerivAt, ?_⟩⟩
  rw [← (arcsinD_props hw).2.2.2]
  exact cos_ne_zero_of_mem_sinStrip (arcsinD_props hw).2.1

/-- `|sin z ∓ 1| = cosh y ∓ sin x` for `z = x + iy`. -/
theorem norm_sin_sub_one (z : ℂ) : ‖sin z - 1‖ = Real.cosh z.im - Real.sin z.re := by
  have hn : 0 ≤ Real.cosh z.im - Real.sin z.re := by
    linarith [Real.one_le_cosh z.im, Real.sin_le_one z.re]
  rw [← Real.sqrt_sq hn, ← Real.sqrt_sq (norm_nonneg _), Complex.sq_norm, normSq_apply]
  congr 1
  simp only [sub_re, one_re, sub_im, one_im, sub_zero, re_sin, im_sin]
  linear_combination (Real.sinh z.im) ^ 2 * Real.sin_sq_add_cos_sq z.re +
    (Real.sin z.re ^ 2 - 1) * Real.cosh_sq z.im

theorem norm_sin_add_one (z : ℂ) : ‖sin z + 1‖ = Real.cosh z.im + Real.sin z.re := by
  have hn : 0 ≤ Real.cosh z.im + Real.sin z.re := by
    linarith [Real.one_le_cosh z.im, Real.neg_one_le_sin z.re]
  rw [← Real.sqrt_sq hn, ← Real.sqrt_sq (norm_nonneg _), Complex.sq_norm, normSq_apply]
  congr 1
  simp only [add_re, one_re, add_im, one_im, add_zero, re_sin, im_sin]
  linear_combination (Real.sinh z.im) ^ 2 * Real.sin_sq_add_cos_sq z.re +
    (Real.sin z.re ^ 2 - 1) * Real.cosh_sq z.im

/-- **Figure 4.15.7**: "Lines parallel to the real axis in the `z`-plane map onto ellipses in
the `w`-plane with foci at `w = ±1`": `Im z = c ≠ 0` goes onto the ellipse with semi-axes
`cosh c`, `|sinh c|`, on which `|w − 1| + |w + 1| = 2 cosh c`. -/
theorem dlmf_4_15_F7_ellipses {c : ℝ} (hc : c ≠ 0) :
    sin '' {z | z.im = c} = {w | (w.re / Real.cosh c) ^ 2 + (w.im / Real.sinh c) ^ 2 = 1} ∧
      ∀ w ∈ sin '' {z | z.im = c}, ‖w - 1‖ + ‖w + 1‖ = 2 * Real.cosh c := by
  have hch := (Real.cosh_pos c).ne'
  have hsh : Real.sinh c ≠ 0 := fun h => hc (Real.sinh_eq_zero.mp h)
  refine ⟨?_, ?_⟩
  · ext w
    simp only [mem_image, mem_ofPred_eq]
    constructor
    · rintro ⟨z, rfl, rfl⟩
      rw [re_sin, im_sin, mul_div_cancel_right₀ _ hch, mul_div_cancel_right₀ _ hsh]
      exact Real.sin_sq_add_cos_sq z.re
    · intro hw
      set a := w.re / Real.cosh c
      set b := w.im / Real.sinh c
      set ζ : ℂ := b + a * I
      have hζ : ‖ζ‖ = 1 := by
        rw [norm_add_mul_I, show b ^ 2 + a ^ 2 = 1 by linarith, Real.sqrt_one]
      have hζ0 : ζ ≠ 0 := by intro h; rw [h, norm_zero] at hζ; exact zero_ne_one hζ
      refine ⟨arg ζ + c * I, by simp, ?_⟩
      apply Complex.ext
      · rw [re_sin]
        simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
          sub_zero, add_zero, add_im, mul_im, zero_add]
        rw [sin_arg, hζ, div_one, (show ζ.im = a by simp [ζ])]
        simp only [a]
        field_simp
      · rw [im_sin]
        simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
          sub_zero, add_zero, add_im, mul_im, zero_add]
        rw [cos_arg hζ0, hζ, div_one, (show ζ.re = b by simp [ζ])]
        simp only [b]
        field_simp
  · rintro w ⟨z, hz, rfl⟩
    rw [norm_sin_sub_one, norm_sin_add_one, show z.im = c from hz]
    ring

/-- **Figure 4.15.7**: "lines parallel to the imaginary axis map onto ... hyperbolas confocal
with the ellipses": `Re z = c` (`sin c, cos c ≠ 0`) goes onto the branch `u sin c > 0` of the
hyperbola with semi-axes `|sin c|`, `|cos c|`, on which `|w + 1| − |w − 1| = 2 sin c`. -/
theorem dlmf_4_15_F7_hyperbolas {c : ℝ} (hs : Real.sin c ≠ 0) (hc : Real.cos c ≠ 0) :
    sin '' {z | z.re = c} =
        {w | (w.re / Real.sin c) ^ 2 - (w.im / Real.cos c) ^ 2 = 1 ∧ 0 < w.re * Real.sin c} ∧
      ∀ w ∈ sin '' {z | z.re = c}, ‖w + 1‖ - ‖w - 1‖ = 2 * Real.sin c := by
  refine ⟨?_, ?_⟩
  · ext w
    simp only [mem_image, mem_ofPred_eq]
    constructor
    · rintro ⟨z, rfl, rfl⟩
      rw [re_sin, im_sin]
      refine ⟨?_, ?_⟩
      · rw [mul_div_cancel_left₀ _ hs, mul_div_cancel_left₀ _ hc]
        linear_combination Real.cosh_sq z.im
      · have := Real.cosh_pos z.im
        have : 0 < Real.sin z.re ^ 2 := by positivity
        nlinarith
    · rintro ⟨hw, hpos⟩
      set A := w.re / Real.sin c
      set B := w.im / Real.cos c
      have hA : 0 < A := by
        have : A = w.re * Real.sin c / Real.sin c ^ 2 := by simp only [A]; field_simp
        rw [this]; positivity
      have hAB : Real.cosh (Real.arsinh B) = A := by
        rw [Real.cosh_arsinh, show 1 + B ^ 2 = A ^ 2 by linarith, Real.sqrt_sq hA.le]
      refine ⟨c + Real.arsinh B * I, by simp, ?_⟩
      apply Complex.ext
      · rw [re_sin]
        simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
          sub_zero, add_zero, add_im, mul_im, zero_add]
        rw [hAB]; simp only [A]; field_simp
      · rw [im_sin]
        simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
          sub_zero, add_zero, add_im, mul_im, zero_add]
        rw [Real.sinh_arsinh]; simp only [B]; field_simp
  · rintro w ⟨z, hz, rfl⟩
    rw [norm_sin_sub_one, norm_sin_add_one, show z.re = c from hz]
    ring

/-- **Figure 4.15.7** (erratum): the hyperbolas are not rectangular in general. The image of
`Re z = c`, `0 < c < π/2`, has equal semi-axes `sin c = cos c` only for `c = π/4`. -/
theorem dlmf_4_15_F7_not_rectangular {c : ℝ} (h0 : 0 < c) (h1 : c < π / 2) :
    Real.sin c = Real.cos c ↔ c = π / 4 := by
  constructor
  · intro h
    have hs : Real.sin (c - π / 4) = 0 := by
      rw [Real.sin_sub, Real.sin_pi_div_four, Real.cos_pi_div_four, h]; ring
    have := (Real.sin_eq_zero_iff_of_lt_of_lt (by linarith [Real.pi_pos])
      (by linarith [Real.pi_pos])).mp hs
    linarith
  · rintro rfl
    rw [Real.sin_pi_div_four, Real.cos_pi_div_four]

/-- **Figure 4.15.7**: the labelled corresponding points (`r` a real parameter): `A = 0 ↦ 0`,
`B = π/2 ↦ 1`, `C, C̄ = π/2 ± ir ↦ cosh r`, `D, D̄ = ±ir ↦ ±i sinh r`,
`E, Ē = −π/2 ± ir ↦ −cosh r`, `F = −π/2 ↦ −1`. -/
theorem dlmf_4_15_F7_points (r : ℝ) :
    sin 0 = 0 ∧ sin (π / 2) = 1 ∧ sin (π / 2 + r * I) = Real.cosh r ∧
      sin (π / 2 - r * I) = Real.cosh r ∧ sin (r * I) = I * Real.sinh r ∧
      sin (-(r * I)) = -(I * Real.sinh r) ∧ sin (-(π / 2) + r * I) = -Real.cosh r ∧
      sin (-(π / 2) - r * I) = -Real.cosh r ∧ sin (-(π / 2)) = -1 := by
  refine ⟨sin_zero, sin_pi_div_two, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    apply Complex.ext <;>
    simp [re_sin, im_sin, Real.cosh_neg, Real.sinh_neg, -ofReal_sinh, -ofReal_cosh]

/-- **Figure 4.15.7**: the interior labelled points `D, D̄`: `arcsin(±i sinh r) = ±ir`. -/
theorem dlmf_4_15_F7_points_D (r : ℝ) :
    arcsinD (I * Real.sinh r) = r * I ∧ arcsinD (-(I * Real.sinh r)) = -(r * I) := by
  have hD : (r * I : ℂ) ∈ sinStrip := by
    constructor <;> simp [Real.pi_pos]
  have hD' : (-(r * I) : ℂ) ∈ sinStrip := by
    constructor <;> simp [Real.pi_pos]
  obtain ⟨-, -, -, -, h5, h6, -⟩ := dlmf_4_15_F7_points r
  exact ⟨by rw [← h5]; exact arcsinD_sin hD, by rw [← h6]; exact arcsinD_sin hD'⟩

/-- A point `x ∈ (−π, π)` with `cos x > 0` lies in `(−π/2, π/2)`. -/
theorem abs_lt_pi_div_two_of_cos_pos {x : ℝ} (h1 : -π < x) (h2 : x < π) (hc : 0 < Real.cos x) :
    -(π / 2) < x ∧ x < π / 2 := by
  constructor
  · by_contra h
    push Not at h
    have := Real.cos_nonpos_of_pi_div_two_le_of_le (x := -x) (by linarith) (by linarith)
    rw [Real.cos_neg] at this
    linarith
  · by_contra h
    push Not at h
    have := Real.cos_nonpos_of_pi_div_two_le_of_le h (by linarith)
    linarith

/-- Limits of `arcsin` at the edges of the cuts: approaching `sin a` (`Re a = ±π/2`,
`Im a ≠ 0`) from the side where `Im w` has the sign of `Im a`, `arcsin w → a`. -/
theorem tendsto_arcsinD_edge {a : ℂ} (ha : |a.re| = π / 2) (hb : a.im ≠ 0) {S : Set ℂ}
    (hS : S ⊆ {w | 0 < w.im * a.im}) : Tendsto arcsinD (𝓝[S] (sin a)) (𝓝 a) := by
  have hpi : (0 : ℝ) ≤ π / 2 := by linarith [Real.pi_pos]
  have hsa : |Real.sin a.re| = 1 := by
    rcases (abs_eq hpi).mp ha with h | h
    · rw [h, Real.sin_pi_div_two, abs_one]
    · rw [h, Real.sin_neg, Real.sin_pi_div_two, abs_neg, abs_one]
  have hcos : cos a ≠ 0 := by
    intro h
    have := congrArg im h
    rw [im_cos, zero_im, neg_eq_zero] at this
    rcases mul_eq_zero.mp this with h' | h'
    · rw [h', abs_zero] at hsa; exact zero_ne_one hsa
    · exact hb (Real.sinh_eq_zero.mp h')
  have hmap := (hasStrictDerivAt_sin a).map_nhds_eq hcos
  rw [nhdsWithin, ← hmap, ← Filter.map_inf_principal_preimage, tendsto_map'_iff]
  have hev : ∀ᶠ z in 𝓝 a, 0 < z.im * a.im ∧ |z.re - a.re| < π / 2 := by
    refine (continuousAt_const.eventually_lt (f := fun _ : ℂ => (0 : ℝ))
      (g := fun z : ℂ => z.im * a.im) (by fun_prop) (mul_self_pos.mpr hb)).and ?_
    exact ContinuousAt.eventually_lt (f := fun z : ℂ => |z.re - a.re|)
      (g := fun _ => π / 2) (by fun_prop) continuousAt_const (by simp [Real.pi_pos])
  refine (tendsto_id.mono_left inf_le_left).congr' ?_
  filter_upwards [inf_le_left (b := 𝓟 (sin ⁻¹' S)) hev,
    mem_inf_of_right (mem_principal_self _)] with z hz hzS
  have hS' : 0 < (sin z).im * a.im := hS hzS
  rw [im_sin, mul_assoc] at hS'
  have hsh : 0 < Real.sinh z.im * a.im := by
    rcases pos_and_pos_or_neg_and_neg_of_mul_pos hz.1 with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact mul_pos (Real.sinh_pos_iff.mpr h1) h2
    · exact mul_pos_of_neg_of_neg (Real.sinh_neg_iff.mpr h1) h2
  have hc := (pos_iff_pos_of_mul_pos hS').mpr hsh
  have hx := abs_lt.mp hz.2
  have hx' : -π < z.re ∧ z.re < π := by
    rcases (abs_eq hpi).mp ha with h | h <;> constructor <;> linarith
  exact (arcsinD_sin (abs_lt_pi_div_two_of_cos_pos hx'.1 hx'.2 hc)).symm

/-- **Figure 4.15.7**: the edges `Re z = ±π/2` of the strip correspond to the two sides of the
cuts (`r > 0`): `C = π/2 + ir ↔ cosh r + i0`, `C̄ = π/2 − ir ↔ cosh r − i0`,
`E = −π/2 + ir ↔ −cosh r + i0`, `Ē = −π/2 − ir ↔ −cosh r − i0`, as limits of `arcsin w`. -/
theorem dlmf_4_15_F7_edges {r : ℝ} (hr : 0 < r) :
    Tendsto arcsinD (𝓝[{w | 0 < w.im}] (Real.cosh r : ℂ)) (𝓝 (π / 2 + r * I)) ∧
      Tendsto arcsinD (𝓝[{w | w.im < 0}] (Real.cosh r : ℂ)) (𝓝 (π / 2 - r * I)) ∧
      Tendsto arcsinD (𝓝[{w | 0 < w.im}] (-Real.cosh r : ℂ)) (𝓝 (-(π / 2) + r * I)) ∧
      Tendsto arcsinD (𝓝[{w | w.im < 0}] (-Real.cosh r : ℂ)) (𝓝 (-(π / 2) - r * I)) := by
  obtain ⟨-, -, h3, h4, -, -, h7, h8, -⟩ := dlmf_4_15_F7_points r
  have hpi : |π / 2| = π / 2 := abs_of_pos (by linarith [Real.pi_pos])
  refine ⟨?_, ?_, ?_, ?_⟩
  · have := tendsto_arcsinD_edge (a := π / 2 + r * I) (by simpa using hpi) (by simpa using hr.ne')
      (S := {w | 0 < w.im}) (fun w hw => by simp only [mem_ofPred_eq] at hw ⊢; simp; positivity)
    rwa [h3] at this
  · have := tendsto_arcsinD_edge (a := π / 2 - r * I) (by simpa using hpi) (by simpa using hr.ne')
      (S := {w | w.im < 0}) (fun w hw => by
        simp only [mem_ofPred_eq] at hw ⊢; simp; nlinarith)
    rwa [h4] at this
  · have := tendsto_arcsinD_edge (a := -(π / 2) + r * I) (by simpa using hpi)
      (by simpa using hr.ne') (S := {w | 0 < w.im})
      (fun w hw => by simp only [mem_ofPred_eq] at hw ⊢; simp; positivity)
    rwa [h7] at this
  · have := tendsto_arcsinD_edge (a := -(π / 2) - r * I) (by simpa using hpi)
      (by simpa using hr.ne') (S := {w | w.im < 0}) (fun w hw => by
        simp only [mem_ofPred_eq] at hw ⊢; simp; nlinarith)
    rwa [h8] at this

theorem exists_cosh_eq {x : ℝ} (hx : 1 < x) : ∃ r : ℝ, 0 < r ∧ Real.cosh r = x :=
  ⟨Real.arsinh √(x ^ 2 - 1), Real.arsinh_pos_iff.mpr (Real.sqrt_pos.mpr (by nlinarith)), by
    rw [Real.cosh_arsinh, Real.sq_sqrt (by nlinarith), show 1 + (x ^ 2 - 1) = x ^ 2 by ring,
      Real.sqrt_sq (by linarith)]⟩

/-- Approach along a ray: `𝓝[S] p` is nontrivial when `p + t d ∈ S` for all `t > 0`. -/
theorem neBot_nhdsWithin_of_ray (p d : ℂ) {S : Set ℂ} (h : ∀ t : ℝ, 0 < t → p + t * d ∈ S) :
    (𝓝[S] p).NeBot := by
  rw [← mem_closure_iff_nhdsWithin_neBot, mem_closure_iff_seq_limit]
  refine ⟨fun n => p + ((1 : ℝ) / (n + 1) : ℝ) * d, fun n => h _ (by positivity), ?_⟩
  have := ((continuous_ofReal.tendsto 0).comp tendsto_one_div_add_atTop_nhds_zero_nat).mul_const d
  simpa using (tendsto_const_nhds (x := p)).add this

/-- Two different one-sided limits rule out continuity. -/
theorem not_continuousAt_of_tendsto_ne {f : ℂ → ℂ} {x b c : ℂ} {S T : Set ℂ}
    (hS : (𝓝[S] x).NeBot) (hT : (𝓝[T] x).NeBot) (h1 : Tendsto f (𝓝[S] x) (𝓝 b))
    (h2 : Tendsto f (𝓝[T] x) (𝓝 c)) (hbc : b ≠ c) : ¬ ContinuousAt f x := fun hc =>
  hbc ((tendsto_nhds_unique h1 (hc.tendsto.mono_left nhdsWithin_le_nhds)).trans
    (tendsto_nhds_unique h2 (hc.tendsto.mono_left nhdsWithin_le_nhds)).symm)

theorem neBot_upper (x : ℝ) : (𝓝[{w : ℂ | 0 < w.im}] (x : ℂ)).NeBot :=
  neBot_nhdsWithin_of_ray x I fun t ht => by simpa using ht

theorem neBot_lower (x : ℝ) : (𝓝[{w : ℂ | w.im < 0}] (x : ℂ)).NeBot :=
  neBot_nhdsWithin_of_ray x (-I) fun t ht => by simpa using ht

/-- The limits of `arcsin` from above and below at a point `x` of the cuts, `|x| > 1`: they are
`±π/2 ± ir` with `cosh r = |x|`, `r > 0`. -/
theorem arcsinD_cut_limits {x : ℝ} (hx : 1 < |x|) : ∃ r : ℝ, 0 < r ∧
    Tendsto arcsinD (𝓝[{w | 0 < w.im}] (x : ℂ))
      (𝓝 (((SignType.sign x : ℝ) : ℂ) * (π / 2) + r * I)) ∧
    Tendsto arcsinD (𝓝[{w | w.im < 0}] (x : ℂ))
      (𝓝 (((SignType.sign x : ℝ) : ℂ) * (π / 2) - r * I)) := by
  rcases lt_abs.mp hx with h | h
  · obtain ⟨r, hr, hcr⟩ := exists_cosh_eq h
    obtain ⟨e1, e2, -, -⟩ := dlmf_4_15_F7_edges hr
    rw [hcr] at e1 e2
    refine ⟨r, hr, ?_, ?_⟩ <;> rw [sign_pos (by linarith)] <;> simpa using ‹_›
  · obtain ⟨r, hr, hcr⟩ := exists_cosh_eq h
    obtain ⟨-, -, e3, e4⟩ := dlmf_4_15_F7_edges hr
    have hx' : (-Real.cosh r : ℂ) = x := by rw [hcr]; push_cast; ring
    rw [hx'] at e3 e4
    refine ⟨r, hr, ?_, ?_⟩ <;> rw [sign_neg (by linarith)] <;> simpa using ‹_›

/-- **Figure 4.15.9** (`arcsin(x + iy)`, principal value): "There are branch cuts along the
real axis from `−∞` to `−1` and `1` to `∞`": `arcsin` is holomorphic off the cuts and is
discontinuous at every point `x` of the cuts with `|x| > 1`. -/
theorem dlmf_4_15_F9 :
    DifferentiableOn ℂ arcsinD arcsinCut ∧ ∀ x : ℝ, 1 < |x| → ¬ ContinuousAt arcsinD x := by
  refine ⟨fun w hw =>
    (hasStrictDerivAt_arcsinD hw).hasDerivAt.differentiableAt.differentiableWithinAt, ?_⟩
  intro x hx
  obtain ⟨r, hr, e1, e2⟩ := arcsinD_cut_limits hx
  refine not_continuousAt_of_tendsto_ne (neBot_upper _) (neBot_lower _) e1 e2 fun h => ?_
  have := congrArg im h
  simp at this
  linarith

/-! ### Arccos (DLMF 4.23.2) -/

/-- The integral `∫₀¹ dt/(1 − t²)^{1/2} = π/2` (an improper but Lebesgue-integrable integral). -/
theorem integral_one_div_sqrt_one_sub_sq :
    ∫ t in (0 : ℝ)..1, (1 : ℂ) / (1 - (t : ℂ) ^ 2) ^ (1 / 2 : ℂ) = (π / 2 : ℂ) := by
  have hd : ∀ x ∈ Ioo (0 : ℝ) 1, HasDerivAt Real.arcsin (1 / √(1 - x ^ 2)) x := fun x hx =>
    Real.hasDerivAt_arcsin (by linarith [hx.1]) hx.2.ne
  have hint : IntervalIntegrable (fun x : ℝ => 1 / √(1 - x ^ 2)) volume 0 1 :=
    intervalIntegral.intervalIntegrable_deriv_of_nonneg (g := Real.arcsin)
      Real.continuous_arcsin.continuousOn (fun x hx => hd x (by simpa using hx))
      (fun x _ => by positivity)
  have hr : ∫ x in (0 : ℝ)..1, 1 / √(1 - x ^ 2) = π / 2 := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le zero_le_one
      Real.continuous_arcsin.continuousOn hd hint]
    simp
  rw [intervalIntegral.integral_congr (g := fun t : ℝ => ((1 / √(1 - t ^ 2) : ℝ) : ℂ)),
    intervalIntegral.integral_ofReal, hr]
  · push_cast; ring
  · intro t ht
    rw [uIcc_of_le zero_le_one] at ht
    have h0 : 0 ≤ 1 - t ^ 2 := by nlinarith [ht.1, ht.2]
    simp only
    rw [show (1 : ℂ) - (t : ℂ) ^ 2 = ((1 - t ^ 2 : ℝ) : ℂ) by push_cast; ring,
      show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring, ← ofReal_cpow h0,
      ← Real.sqrt_eq_rpow]
    push_cast
    ring

/-- **DLMF 4.23.2** (general values): `Arccos z = ∫_z^1 dt/(1 − t²)^{1/2}`, along a path from `z`
to `0` (the reverse of a 4.23.1 path) followed by `[0, 1]`, the square root being principal at
`t = 0`: so the values are `∫₀¹ dt/(1 − t²)^{1/2} − v` with `v ∈ Arcsin z`. -/
def arccosGen (z : ℂ) : Set ℂ :=
  {w | ∃ v ∈ arcsinGen z, w = (∫ t in (0 : ℝ)..1, (1 : ℂ) / (1 - (t : ℂ) ^ 2) ^ (1 / 2 : ℂ)) - v}

/-- **DLMF §4.23(ii)**, principal value `arccos z`: 4.23.2 along `[z, 0]` and `[0, 1]`, which do
not cross the cuts. -/
noncomputable def arccosD (z : ℂ) : ℂ :=
  (∫ t in (0 : ℝ)..1, (1 : ℂ) / (1 - (t : ℂ) ^ 2) ^ (1 / 2 : ℂ)) - arcsinD z

/-- **DLMF 4.23.16**: `arccos z = π/2 − arcsin z`. -/
theorem dlmf_4_23_16 (z : ℂ) : arccosD z = π / 2 - arcsinD z := by
  rw [arccosD, integral_one_div_sqrt_one_sub_sq]

/-- **DLMF 4.23.2** (general values): for `z ≠ ±1` the values of `Arccos z` are exactly the
solutions `w` of `cos w = z` (compare 4.23.29). -/
theorem mem_arccosGen_iff {z w : ℂ} (h1 : z ≠ 1) (h2 : z ≠ -1) :
    w ∈ arccosGen z ↔ cos w = z := by
  simp only [arccosGen, integral_one_div_sqrt_one_sub_sq, mem_ofPred_eq]
  constructor
  · rintro ⟨v, hv, rfl⟩
    rw [Complex.cos_pi_div_two_sub, (mem_arcsinGen_iff h1 h2).mp hv]
  · intro hw
    exact ⟨π / 2 - w, (mem_arcsinGen_iff h1 h2).mpr (by rw [Complex.sin_pi_div_two_sub, hw]),
      by ring⟩

theorem arcsinD_ofReal {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) : arcsinD x = Real.arcsin x := by
  have hcut : (x : ℂ) ∈ arcsinCut := Or.inr (by simpa [abs_lt] using hx)
  obtain ⟨-, hs, hsin, -⟩ := arcsinD_props hcut
  refine injOn_sin_sinStrip hs ⟨by simpa using Real.neg_pi_div_two_lt_arcsin.mpr hx.1,
    by simpa using Real.arcsin_lt_pi_div_two.mpr hx.2⟩ ?_
  rw [hsin, ← ofReal_sin, Real.sin_arcsin hx.1.le hx.2.le]

theorem arccosD_ofReal {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) : arccosD x = Real.arccos x := by
  rw [dlmf_4_23_16, arcsinD_ofReal hx, Real.arccos_eq_pi_div_two_sub_arcsin]
  push_cast
  ring

/-- **Figure 4.15.2**: `Arcsin x` and `Arccos x` for `−1 < x < 1`. The general values (4.23.1,
4.23.2) are `(−1)^k arcsin x + kπ` and `±arccos x + 2kπ`, `k ∈ ℤ`. The principal values
(thickened) are `arcsin x ∈ [−π/2, π/2]` and `arccos x ∈ [0, π]`. -/
theorem dlmf_4_15_F2 {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    arcsinGen x = {w | ∃ k : ℤ, w = (-1 : ℂ) ^ k * Real.arcsin x + k * π} ∧
      arccosGen x = {w | ∃ k : ℤ, w = (Real.arccos x : ℂ) + 2 * k * π ∨
        w = -(Real.arccos x : ℂ) + 2 * k * π} ∧
      arcsinD x = Real.arcsin x ∧ arccosD x = Real.arccos x ∧
      Real.arcsin x ∈ Icc (-(π / 2)) (π / 2) ∧ Real.arccos x ∈ Icc 0 π := by
  have h1 : (x : ℂ) ≠ 1 := fun h => by
    have := congrArg re h; simp at this; linarith [hx.2]
  have h2 : (x : ℂ) ≠ -1 := fun h => by
    have := congrArg re h; simp at this; linarith [hx.1]
  refine ⟨?_, ?_, arcsinD_ofReal hx, arccosD_ofReal hx,
    ⟨Real.neg_pi_div_two_le_arcsin x, Real.arcsin_le_pi_div_two x⟩,
    ⟨Real.arccos_nonneg x, Real.arccos_le_pi x⟩⟩
  · ext w
    have hx' : (x : ℂ) = sin (Real.arcsin x) := by
      rw [← ofReal_sin, Real.sin_arcsin hx.1.le hx.2.le]
    rw [mem_arcsinGen_iff h1 h2, hx', show (sin w = sin _) ↔ (sin _ = sin w) from eq_comm,
      sin_eq_sin_iff]
    simp only [mem_ofPred_eq]
    constructor
    · rintro ⟨k, h | h⟩
      · exact ⟨2 * k, by rw [h, Even.neg_one_zpow ⟨k, by ring⟩]; push_cast; ring⟩
      · exact ⟨2 * k + 1, by rw [h, Odd.neg_one_zpow ⟨k, rfl⟩]; push_cast; ring⟩
    · rintro ⟨k, rfl⟩
      obtain ⟨m, rfl | rfl⟩ := Int.even_or_odd' k
      · exact ⟨m, Or.inl (by rw [Even.neg_one_zpow ⟨m, by ring⟩]; push_cast; ring)⟩
      · exact ⟨m, Or.inr (by rw [Odd.neg_one_zpow ⟨m, rfl⟩]; push_cast; ring)⟩
  · ext w
    have hx' : (x : ℂ) = cos (Real.arccos x) := by
      rw [← ofReal_cos, Real.cos_arccos hx.1.le hx.2.le]
    rw [mem_arccosGen_iff h1 h2, hx', show (cos w = cos _) ↔ (cos _ = cos w) from eq_comm,
      cos_eq_cos_iff]
    simp only [mem_ofPred_eq]
    constructor
    · rintro ⟨k, h | h⟩
      · exact ⟨k, Or.inl (by rw [h]; ring)⟩
      · exact ⟨k, Or.inr (by rw [h]; ring)⟩
    · rintro ⟨k, h | h⟩
      · exact ⟨k, Or.inl (by rw [h]; ring)⟩
      · exact ⟨k, Or.inr (by rw [h]; ring)⟩

/-! ### Identities 4.15.1–4.15.3 -/

/-- **DLMF 4.15.1**: `cos(x + iy) = sin(x + π/2 + iy)`. -/
theorem dlmf_4_15_1 (x y : ℝ) : cos (x + y * I) = sin (x + π / 2 + y * I) := by
  rw [show (x : ℂ) + π / 2 + y * I = (x + y * I) + π / 2 by ring, Complex.sin_add_pi_div_two]

/-- **DLMF 4.15.2**: `cot(x + iy) = −tan(x + π/2 + iy)`. -/
theorem dlmf_4_15_2 (x y : ℝ) : cot (x + y * I) = -tan (x + π / 2 + y * I) := by
  rw [show (x : ℂ) + π / 2 + y * I = (x + y * I) + π / 2 by ring, tan_eq_sin_div_cos,
    Complex.sin_add_pi_div_two, Complex.cos_add_pi_div_two, cot_eq_cos_div_sin, div_neg, neg_neg]

/-- **DLMF 4.15.3**: `sec(x + iy) = csc(x + π/2 + iy)`. -/
theorem dlmf_4_15_3 (x y : ℝ) : secC (x + y * I) = cscC (x + π / 2 + y * I) := by
  rw [secC, cscC, show (x : ℂ) + π / 2 + y * I = (x + y * I) + π / 2 by ring,
    Complex.sin_add_pi_div_two]

/-! ### Arctan (DLMF 4.23.3) and arccot (DLMF 4.23.9) -/

/-- The `z`-plane cut along `(−i∞, −i]` and `[i, i∞)` (DLMF Figure 4.23.1(ii)). -/
def arctanCut : Set ℂ := {z | z.re ≠ 0 ∨ |z.im| < 1}

theorem isOpen_arctanCut : IsOpen arctanCut :=
  (isOpen_ne_fun continuous_re continuous_const).union
    (isOpen_lt (continuous_abs.comp continuous_im) continuous_const)

theorem mem_arctanCut_seg {z : ℂ} (hz : z ∈ arctanCut) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    (s * z) ∈ arctanCut := by
  rcases hs.1.eq_or_lt with h | h
  · right; rw [← h]; simp
  rcases hz with hz | hz
  · left; simp [h.ne', hz]
  · right
    simp only [mul_im, ofReal_re, ofReal_im, zero_mul, add_zero]
    rw [abs_mul, abs_of_pos h]
    nlinarith [hs.2, abs_nonneg z.im]

theorem arctan_ratio_props {a : ℂ} (h : a ∈ arctanCut) :
    1 - a * I ≠ 0 ∧ 1 + a * I ≠ 0 ∧ (1 + a * I) / (1 - a * I) ∈ slitPlane := by
  have hre1 : (1 - a * I).re = 1 + a.im := by simp
  have him1 : (1 - a * I).im = -a.re := by simp
  have hre2 : (1 + a * I).re = 1 - a.im := by simp; ring
  have him2 : (1 + a * I).im = a.re := by simp
  have h1 : 1 - a * I ≠ 0 := by
    intro h0
    have e1 : 1 + a.im = 0 := by rw [← hre1, h0]; simp
    have e2 : -a.re = 0 := by rw [← him1, h0]; simp
    rcases h with h | h
    · exact h (by linarith)
    · rw [abs_lt] at h; linarith
  have h2 : 1 + a * I ≠ 0 := by
    intro h0
    have e1 : 1 - a.im = 0 := by rw [← hre2, h0]; simp
    have e2 : a.re = 0 := by rw [← him2, h0]; simp
    rcases h with h | h
    · exact h e2
    · rw [abs_lt] at h; linarith
  refine ⟨h1, h2, ?_⟩
  rw [mem_slitPlane_iff]
  have hN : 0 < normSq (1 - a * I) := normSq_pos.mpr h1
  by_cases hp : a.re = 0
  · left
    have hq : |a.im| < 1 := h.resolve_left (not_not.mpr hp)
    rw [Complex.div_re, hre1, hre2, him1, him2, hp]
    rw [abs_lt] at hq
    have : 0 < (1 - a.im) * (1 + a.im) := by nlinarith
    rw [show (1 - a.im) * (1 + a.im) / normSq (1 - a * I) + 0 * -0 / normSq (1 - a * I) =
      (1 - a.im) * (1 + a.im) / normSq (1 - a * I) by ring]
    exact div_pos this hN
  · right
    rw [Complex.div_im, hre1, him1, hre2, him2,
      show a.re * (1 + a.im) / normSq (1 - a * I) - (1 - a.im) * -a.re / normSq (1 - a * I) =
        2 * a.re / normSq (1 - a * I) by ring]
    exact div_ne_zero (mul_ne_zero two_ne_zero hp) hN.ne'

theorem one_add_sq_eq_mul (a : ℂ) : 1 + a ^ 2 = (1 + a * I) * (1 - a * I) := by
  ring_nf; rw [I_sq]; ring

/-- `Complex.arctan` is holomorphic off the cuts, with derivative `1/(1 + z²)`. -/
theorem hasDerivAt_arctan_of_mem {z : ℂ} (hz : z ∈ arctanCut) :
    HasDerivAt arctan (1 / (1 + z ^ 2)) z := by
  obtain ⟨h1, h2, hs⟩ := arctan_ratio_props hz
  have hr : HasDerivAt (fun z => (1 + z * I) / (1 - z * I)) (2 * I / (1 - z * I) ^ 2) z := by
    have := (((hasDerivAt_id' z).mul_const I).const_add 1).div
      (((hasDerivAt_id' z).mul_const I).const_sub 1) h1
    convert this using 1
    field_simp
    ring
  have h := (hr.clog hs).const_mul (-I / 2)
  have hfun : arctan = fun z => -I / 2 * log ((1 + z * I) / (1 - z * I)) := rfl
  rw [hfun]
  convert h using 1
  rw [one_add_sq_eq_mul]
  field_simp
  ring_nf
  rw [I_sq]
  ring

/-- **DLMF §4.23(ii)**, principal value `arctan z`: the integral 4.23.3 along the segment
`[0, z]`, which does not cross the cuts of Figure 4.23.1(ii). -/
noncomputable def arctanD (z : ℂ) : ℂ := ∫ s in (0 : ℝ)..1, z / (1 + (s * z) ^ 2)

theorem one_add_sq_ne_zero_of_mem_arctanCut {a : ℂ} (h : a ∈ arctanCut) : 1 + a ^ 2 ≠ 0 := by
  obtain ⟨h1, h2, -⟩ := arctan_ratio_props h
  rw [one_add_sq_eq_mul]
  exact mul_ne_zero h2 h1

/-- Off the cuts the integral 4.23.3 along `[0, z]` is Mathlib's `Complex.arctan`
(`−(i/2) ln((1 + iz)/(1 − iz))`). -/
theorem arctanD_eq {z : ℂ} (hz : z ∈ arctanCut) : arctanD z = arctan z := by
  have hd : ∀ s ∈ uIcc (0 : ℝ) 1,
      HasDerivAt (fun s : ℝ => arctan (s * z)) (z / (1 + (s * z) ^ 2)) s := by
    intro s hs
    rw [uIcc_of_le zero_le_one] at hs
    have h := (hasDerivAt_arctan_of_mem (mem_arctanCut_seg hz hs)).comp (s : ℂ)
      ((hasDerivAt_id' (s : ℂ)).mul_const z)
    refine h.comp_ofReal.congr_deriv ?_
    ring
  have hc : ContinuousOn (fun s : ℝ => z / (1 + (s * z) ^ 2)) (uIcc 0 1) := by
    apply ContinuousOn.div continuousOn_const (by fun_prop)
    intro s hs
    rw [uIcc_of_le zero_le_one] at hs
    exact one_add_sq_ne_zero_of_mem_arctanCut (mem_arctanCut_seg hz hs)
  rw [arctanD, intervalIntegral.integral_eq_sub_of_hasDerivAt hd hc.intervalIntegrable]
  simp [Complex.arctan]

theorem im_arctan_ratio (z : ℂ) :
    ((1 + z * I) / (1 - z * I)).im = 2 * z.re / normSq (1 - z * I) := by
  rw [Complex.div_im]
  simp only [add_im, one_im, mul_im, I_re, mul_zero, I_im, mul_one, zero_add, sub_re, one_re,
    sub_im, zero_sub, add_re]
  ring

/-- The limits of `arctan` from the right and the left at a point `iy`, `|y| > 1`, of its cuts,
explicitly. -/
theorem arctanD_cut_tendsto {y : ℝ} (hy : 1 < |y|) :
    Tendsto arctanD (𝓝[{z | 0 < z.re}] (y * I))
        (𝓝 (-I / 2 * (Real.log |(1 - y) / (1 + y)| + π * I))) ∧
      Tendsto arctanD (𝓝[{z | z.re < 0}] (y * I))
        (𝓝 (-I / 2 * (Real.log |(1 - y) / (1 + y)| - π * I))) := by
  set z₀ : ℂ := y * I with hz₀
  set x₀ : ℝ := (1 - y) / (1 + y) with hx₀def
  have hy1 : 1 + y ≠ 0 := by intro h; rcases lt_abs.mp hy with h' | h' <;> linarith
  have hx₀ : x₀ < 0 := by
    have hneg : (1 - y) * (1 + y) < 0 := by rcases lt_abs.mp hy with h' | h' <;> nlinarith
    have : x₀ = (1 - y) * (1 + y) / (1 + y) ^ 2 := by rw [hx₀def]; field_simp
    rw [this]
    exact div_neg_of_neg_of_pos hneg (by positivity)
  set ρ : ℂ → ℂ := fun z => (1 + z * I) / (1 - z * I) with hρ
  have hII : z₀ * I = -(y : ℂ) := by rw [hz₀, mul_assoc, I_mul_I]; ring
  have hd0 : 1 - z₀ * I ≠ 0 := by
    rw [hII, sub_neg_eq_add]
    exact_mod_cast hy1
  have hρ0 : ρ z₀ = x₀ := by
    rw [hρ]; simp only; rw [hII, hx₀def]; push_cast; ring
  have hρc : ContinuousAt ρ z₀ :=
    (by fun_prop : ContinuousAt (fun z : ℂ => 1 + z * I) z₀).div (by fun_prop) hd0
  have hρne : ∀ z : ℂ, z.re ≠ 0 → 1 - z * I ≠ 0 := fun z hz h => hz (by
    have := congrArg im h; simpa using this)
  have hlim : Tendsto ρ (𝓝 z₀) (𝓝 (x₀ : ℂ)) := by rw [← hρ0]; exact hρc.tendsto
  have hR : Tendsto ρ (𝓝[{z | 0 < z.re}] z₀) (𝓝[{w | 0 < w.im}] (x₀ : ℂ)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨hlim.mono_left nhdsWithin_le_nhds, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with z hz
    show 0 < ((1 + z * I) / (1 - z * I)).im
    rw [im_arctan_ratio]
    exact div_pos (by linarith) (normSq_pos.mpr (hρne z hz.ne'))
  have hL : Tendsto ρ (𝓝[{z | z.re < 0}] z₀) (𝓝[{w | w.im < 0}] (x₀ : ℂ)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨hlim.mono_left nhdsWithin_le_nhds, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with z hz
    show ((1 + z * I) / (1 - z * I)).im < 0
    rw [im_arctan_ratio]
    exact div_neg_of_neg_of_pos (by linarith) (normSq_pos.mpr (hρne z hz.ne))
  obtain ⟨hu, hl⟩ := dlmf_4_2_7 hx₀
  have hTR : Tendsto arctanD (𝓝[{z | 0 < z.re}] z₀)
      (𝓝 (-I / 2 * (Real.log |x₀| + π * I))) := by
    refine ((hu.comp hR).const_mul (-I / 2)).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with z hz
    rw [arctanD_eq (Or.inl (ne_of_gt hz))]
    rfl
  have hTL : Tendsto arctanD (𝓝[{z | z.re < 0}] z₀)
      (𝓝 (-I / 2 * (Real.log |x₀| - π * I))) := by
    refine ((hl.comp hL).const_mul (-I / 2)).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with z hz
    rw [arctanD_eq (Or.inl (ne_of_lt hz))]
    rfl
  exact ⟨hTR, hTL⟩

/-- The limits of `arctan` from the right and the left at a point `iy`, `|y| > 1`, of its cuts:
they differ by `π` in the real part. -/
theorem arctanD_cut_limits {y : ℝ} (hy : 1 < |y|) : ∃ b c : ℂ, b.re ≠ c.re ∧
    Tendsto arctanD (𝓝[{z | 0 < z.re}] (y * I)) (𝓝 b) ∧
    Tendsto arctanD (𝓝[{z | z.re < 0}] (y * I)) (𝓝 c) := by
  obtain ⟨h1, h2⟩ := arctanD_cut_tendsto hy
  refine ⟨_, _, ?_, h1, h2⟩
  simp
  linarith [Real.pi_pos]

/-- **Figure 4.15.11** (`arctan(x + iy)`, principal value): "There are branch cuts along the
imaginary axis from `−i∞` to `−i` and `i` to `i∞`": `arctan` is holomorphic off the cuts and is
discontinuous at every point `iy`, `|y| > 1`, of the cuts. -/
theorem dlmf_4_15_F11 :
    DifferentiableOn ℂ arctanD arctanCut ∧
      ∀ y : ℝ, 1 < |y| → ¬ ContinuousAt arctanD (y * I) := by
  refine ⟨fun z hz => ?_, fun y hy => ?_⟩
  · have hev : arctanD =ᶠ[𝓝 z] arctan :=
      Filter.mem_of_superset (isOpen_arctanCut.mem_nhds hz) fun w hw => arctanD_eq hw
    exact ((hasDerivAt_arctan_of_mem hz).differentiableAt.congr_of_eventuallyEq
      hev).differentiableWithinAt
  obtain ⟨b, c, hbc, hTR, hTL⟩ := arctanD_cut_limits hy
  refine not_continuousAt_of_tendsto_ne
    (neBot_nhdsWithin_of_ray (y * I) 1 fun t ht => by simpa using ht)
    (neBot_nhdsWithin_of_ray (y * I) (-1) fun t ht => by simpa using ht) hTR hTL fun h => ?_
  exact hbc (congrArg re h)

/-- **DLMF 4.23.9**: `arccot z = arctan(1/z)`. -/
noncomputable def arccotD (z : ℂ) : ℂ := arctanD (1 / z)

theorem arctanD_ofReal (x : ℝ) : arctanD x = Real.arctan x := by
  rw [arctanD_eq (Or.inr (by simp)), Complex.ofReal_arctan]

theorem arccotD_ofReal (x : ℝ) : arccotD x = Real.arctan (1 / x) := by
  rw [arccotD, show (1 : ℂ) / x = ((1 / x : ℝ) : ℂ) by rw [ofReal_div, ofReal_one],
    arctanD_ofReal]

/-- **Figure 4.15.4**: `arctan x` and `arccot x` (principal values, real `x`): both are real,
`arccot x = arctan(1/x)`, and "`arccot x` is discontinuous at `x = 0`": its limits there from
the right and the left are `π/2` and `−π/2`. -/
theorem dlmf_4_15_F4 :
    (∀ x : ℝ, arctanD x = Real.arctan x) ∧ (∀ x : ℝ, arccotD x = Real.arctan (1 / x)) ∧
      Tendsto (fun x : ℝ => arccotD x) (𝓝[>] 0) (𝓝 (π / 2)) ∧
      Tendsto (fun x : ℝ => arccotD x) (𝓝[<] 0) (𝓝 (-(π / 2))) ∧
      ¬ ContinuousAt (fun x : ℝ => arccotD x) 0 := by
  have hf : (fun x : ℝ => arccotD x) = ofReal ∘ Real.arctan ∘ fun x => x⁻¹ :=
    funext fun x => by simp only [Function.comp, arccotD_ofReal, one_div]
  have hR : Tendsto (fun x : ℝ => arccotD x) (𝓝[>] 0) (𝓝 (π / 2)) := by
    rw [hf]
    convert (continuous_ofReal.tendsto _).comp
      ((Real.tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds).comp tendsto_inv_nhdsGT_zero)
      using 2
    push_cast; ring
  have hL : Tendsto (fun x : ℝ => arccotD x) (𝓝[<] 0) (𝓝 (-(π / 2))) := by
    rw [hf]
    convert (continuous_ofReal.tendsto _).comp
      ((Real.tendsto_arctan_atBot.mono_right nhdsWithin_le_nhds).comp tendsto_inv_nhdsLT_zero)
      using 2
    push_cast; ring
  refine ⟨arctanD_ofReal, arccotD_ofReal, hR, hL, fun hc => ?_⟩
  have h1 := tendsto_nhds_unique hR (hc.tendsto.mono_left nhdsWithin_le_nhds)
  have h2 := tendsto_nhds_unique hL (hc.tendsto.mono_left nhdsWithin_le_nhds)
  have := congrArg re (h1.trans h2.symm)
  simp at this
  linarith [Real.pi_pos]

/-! ### Arccsc and arcsec (DLMF 4.23.4–4.23.5, 4.23.7–4.23.8) -/

/-- **DLMF 4.23.4**: `Arccsc z = Arcsin(1/z)` (general values). -/
def arccscGen (z : ℂ) : Set ℂ := arcsinGen (1 / z)

/-- **DLMF 4.23.5**: `Arcsec z = Arccos(1/z)` (general values). -/
def arcsecGen (z : ℂ) : Set ℂ := arccosGen (1 / z)

/-- **DLMF 4.23.7**: `arccsc z = arcsin(1/z)`. -/
noncomputable def arccscD (z : ℂ) : ℂ := arcsinD (1 / z)

/-- **DLMF 4.23.8**: `arcsec z = arccos(1/z)`. -/
noncomputable def arcsecD (z : ℂ) : ℂ := arccosD (1 / z)

/-- **DLMF 4.23.17**: `arcsec z = π/2 − arccsc z`. -/
theorem dlmf_4_23_17 (z : ℂ) : arcsecD z = π / 2 - arccscD z := dlmf_4_23_16 _

/-- Off `[−1, 1]`, `1/z` lies off the cuts of `arcsin`. -/
theorem one_div_mem_arcsinCut {z : ℂ} (h : z.im ≠ 0 ∨ 1 < |z.re|) :
    z ≠ 0 ∧ 1 / z ∈ arcsinCut := by
  have hz : z ≠ 0 := by
    rintro rfl
    rcases h with h | h
    · exact h rfl
    · simp at h; linarith
  refine ⟨hz, ?_⟩
  by_cases him : z.im = 0
  · right
    have hzr : z = (z.re : ℂ) := Complex.ext (by simp) (by simp [him])
    have hr : 1 < |z.re| := h.resolve_left (not_not.mpr him)
    rw [hzr, show (1 : ℂ) / (z.re : ℂ) = ((1 / z.re : ℝ) : ℂ) by rw [ofReal_div, ofReal_one],
      ofReal_re, abs_div, abs_one]
    exact (div_lt_one (by linarith)).mpr hr
  · left
    rw [one_div, inv_im]
    exact div_ne_zero (neg_ne_zero.mpr him) (normSq_pos.mpr hz).ne'

/-- `z ↦ 1/z` exchanges the two sides of the real axis near a real `x ≠ 0`. -/
theorem tendsto_one_div_nhdsWithin {x : ℝ} (hx : x ≠ 0) :
    Tendsto (fun z : ℂ => 1 / z) (𝓝[{w | 0 < w.im}] (x : ℂ))
        (𝓝[{w | w.im < 0}] ((1 / x : ℝ) : ℂ)) ∧
      Tendsto (fun z : ℂ => 1 / z) (𝓝[{w | w.im < 0}] (x : ℂ))
        (𝓝[{w | 0 < w.im}] ((1 / x : ℝ) : ℂ)) := by
  have hx' : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hx
  have hc : Tendsto (fun z : ℂ => 1 / z) (𝓝 (x : ℂ)) (𝓝 ((1 / x : ℝ) : ℂ)) := by
    rw [ofReal_div, ofReal_one]
    exact ((continuousAt_const (y := (1 : ℂ))).div continuousAt_id hx').tendsto
  have him : ∀ z : ℂ, (1 / z).im = -z.im / normSq z := fun z => by rw [one_div, inv_im]
  constructor
  · refine tendsto_nhdsWithin_iff.mpr ⟨hc.mono_left nhdsWithin_le_nhds, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with z hz
    have hz0 : z ≠ 0 := fun h => by rw [h] at hz; simp at hz
    rw [him]
    exact div_neg_of_neg_of_pos (by linarith) (normSq_pos.mpr hz0)
  · refine tendsto_nhdsWithin_iff.mpr ⟨hc.mono_left nhdsWithin_le_nhds, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with z hz
    have hz0 : z ≠ 0 := fun h => by rw [h] at hz; simp at hz
    rw [him]
    exact div_pos (by linarith) (normSq_pos.mpr hz0)

theorem one_lt_abs_one_div {x : ℝ} (hx0 : x ≠ 0) (hx1 : |x| < 1) : 1 < |1 / x| := by
  rw [abs_one_div]
  exact one_lt_one_div (abs_pos.mpr hx0) hx1

/-- The limits of `arccsc` from above and below at a point `x` of its cut, `0 < |x| < 1`: they
are `±π/2 ∓ ir` with `cosh r = 1/|x|`, `r > 0`. -/
theorem arccscD_cut_limits {x : ℝ} (hx0 : x ≠ 0) (hx1 : |x| < 1) : ∃ r : ℝ, 0 < r ∧
    Tendsto arccscD (𝓝[{w | 0 < w.im}] (x : ℂ))
      (𝓝 (((SignType.sign x : ℝ) : ℂ) * (π / 2) - r * I)) ∧
    Tendsto arccscD (𝓝[{w | w.im < 0}] (x : ℂ))
      (𝓝 (((SignType.sign x : ℝ) : ℂ) * (π / 2) + r * I)) := by
  obtain ⟨r, hr, e1, e2⟩ := arcsinD_cut_limits (one_lt_abs_one_div hx0 hx1)
  have hs : SignType.sign (1 / x) = SignType.sign x := by
    rcases lt_or_gt_of_ne hx0 with h | h
    · rw [sign_neg h, sign_neg (one_div_neg.mpr h)]
    · rw [sign_pos h, sign_pos (one_div_pos.mpr h)]
  rw [hs] at e1 e2
  obtain ⟨t1, t2⟩ := tendsto_one_div_nhdsWithin hx0
  exact ⟨r, hr, e2.comp t1, e1.comp t2⟩

/-- **Figure 4.15.13** (`arccsc(x + iy)`, principal value): "There is a branch cut along the
real axis from `−1` to `1`": `arccsc` is holomorphic off `[−1, 1]` and is discontinuous at every
point `x ≠ 0` of the cut. -/
theorem dlmf_4_15_F13 :
    (∀ z : ℂ, z.im ≠ 0 ∨ 1 < |z.re| → DifferentiableAt ℂ arccscD z) ∧
      ∀ x : ℝ, x ≠ 0 → |x| < 1 → ¬ ContinuousAt arccscD x := by
  refine ⟨fun z hz => ?_, fun x hx0 hx1 => ?_⟩
  · obtain ⟨hz0, hc⟩ := one_div_mem_arcsinCut hz
    exact (hasStrictDerivAt_arcsinD hc).hasDerivAt.differentiableAt.comp z
      ((differentiableAt_const (c := (1 : ℂ))).div differentiableAt_id hz0)
  · obtain ⟨r, hr, e1, e2⟩ := arccscD_cut_limits hx0 hx1
    refine not_continuousAt_of_tendsto_ne (neBot_upper _) (neBot_lower _) e1 e2 fun h => ?_
    have := congrArg im h
    simp at this
    linarith

/-- **Figure 4.15.6**: `arccsc x` and `arcsec x`, principal values: for `|x| > 1` they are the
real `arcsin(1/x)`, `arccos(1/x)`. -/
theorem dlmf_4_15_F6_real {x : ℝ} (hx : 1 < |x|) :
    arccscD x = Real.arcsin (1 / x) ∧ arcsecD x = Real.arccos (1 / x) := by
  have h : 1 / x ∈ Ioo (-1 : ℝ) 1 := by
    rw [mem_Ioo, ← abs_lt, abs_one_div]
    exact (div_lt_one (by linarith)).mpr hx
  rw [arccscD, arcsecD,
    (show (1 : ℂ) / x = ((1 / x : ℝ) : ℂ) by rw [ofReal_div, ofReal_one])]
  exact ⟨arcsinD_ofReal h, arccosD_ofReal h⟩

/-- **Figure 4.15.6**: "(Both functions are complex when `−1 < x < 1`)": for `0 < |x| < 1`
every general value 4.23.4–4.23.5 of `Arccsc x`, `Arcsec x` is nonreal, and so are the two
values of the principal branches on their cut (the limits from above and below). -/
theorem dlmf_4_15_F6 {x : ℝ} (hx0 : x ≠ 0) (hx1 : |x| < 1) :
    (∀ w ∈ arccscGen x, w.im ≠ 0) ∧ (∀ w ∈ arcsecGen x, w.im ≠ 0) ∧
      (∃ b c : ℂ, b.im ≠ 0 ∧ c.im ≠ 0 ∧ Tendsto arccscD (𝓝[{w | 0 < w.im}] (x : ℂ)) (𝓝 b) ∧
        Tendsto arccscD (𝓝[{w | w.im < 0}] (x : ℂ)) (𝓝 c)) ∧
      (∃ b c : ℂ, b.im ≠ 0 ∧ c.im ≠ 0 ∧ Tendsto arcsecD (𝓝[{w | 0 < w.im}] (x : ℂ)) (𝓝 b) ∧
        Tendsto arcsecD (𝓝[{w | w.im < 0}] (x : ℂ)) (𝓝 c)) := by
  have h1 := one_lt_abs_one_div hx0 hx1
  have hc : (1 / (x : ℂ)) = ((1 / x : ℝ) : ℂ) := by rw [ofReal_div, ofReal_one]
  have hne1 : (1 / (x : ℂ)) ≠ 1 := by
    rw [hc]; intro h
    have := congrArg re h
    simp only [ofReal_re, one_re] at this
    rw [this, abs_one] at h1; exact lt_irrefl _ h1
  have hne2 : (1 / (x : ℂ)) ≠ -1 := by
    rw [hc]; intro h
    have := congrArg re h
    simp only [ofReal_re, neg_re, one_re] at this
    rw [this, abs_neg, abs_one] at h1; exact lt_irrefl _ h1
  have hreal : ∀ w : ℂ, w.im = 0 → w = (w.re : ℂ) := fun w h =>
    Complex.ext (by simp) (by simp [h])
  obtain ⟨r, hr, e1, e2⟩ := arccscD_cut_limits hx0 hx1
  refine ⟨fun w hw him => ?_, fun w hw him => ?_,
    ⟨_, _, by simpa using hr.ne', by simpa using hr.ne', e1, e2⟩, ?_⟩
  · rw [arccscGen, mem_arcsinGen_iff hne1 hne2, hreal w him, ← ofReal_sin, hc] at hw
    have hs := Real.abs_sin_le_one w.re
    rw [ofReal_injective hw] at hs
    linarith
  · rw [arcsecGen, mem_arccosGen_iff hne1 hne2, hreal w him, ← ofReal_cos, hc] at hw
    have hs := Real.abs_cos_le_one w.re
    rw [ofReal_injective hw] at hs
    linarith
  · have hfun : arcsecD = fun z => π / 2 - arccscD z := funext dlmf_4_23_17
    rw [hfun]
    exact ⟨_, _, by simpa using hr.ne', by simpa using hr.ne', tendsto_const_nhds.sub e1,
      tendsto_const_nhds.sub e2⟩

end Azurite.DLMF
