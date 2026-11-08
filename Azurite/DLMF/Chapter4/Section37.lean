/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter4.Section29

/-!
# DLMF §4.37 Inverse Hyperbolic Functions

The principal values of §4.37(ii) were formalized for §4.29 (`Section29InvHyp.lean`): `arcsinhD`,
`arccoshD`, `arctanhD`, `arccschD`, `arcsechD`, `arccothD`, with the cut planes `arcsinhCut`,
`arccoshCut`, `arctanhCut`.

## §4.37(i) General Definitions

* 4.37.1: `arcsinhGen` (`C¹` paths from `0` avoiding `±i`, branch of `(1 + t²)^{1/2}` continued
  from `1` at `t = 0`); `mem_arcsinhGen_iff`: for `z ≠ ±i` the values are the solutions of
  `sinh w = z` (via `Arcsin` at `iz`, `mem_arcsinhGen_iff_I`).
* 4.37.2: `arccoshGen` (`C¹` paths from `1` avoiding `±1` afterwards, a continuous branch of
  `(t² − 1)^{1/2}`, integrable integrand); `mem_arccoshGen_iff`: for `z ≠ ±1` the values are the
  solutions of `cosh w = z` (`cosh_sinh_of_arccosh_path`).
* 4.37.3: `arctanhGen`; `mem_arctanhGen_iff` (`cosh w ≠ 0`, `tanh w = z`).
* 4.37.4–4.37.6: `arccschGen`, `arcsechGen`, `arccothGen` (`dlmf_4_37_4_6`).
* "Each of the six functions is a multivalued function of `z`": `dlmf_4_37_i_multivalued`.
* Branch points `±i` (`Arcsinh`, `Arccsch`) and `±1` (the other four):
  `dlmf_4_37_i_branch_points` (no continuous branch on a punctured disc; reduced to §4.23(i) by
  `z ↦ ±iz`).
* **Imprecisions**:
  - `Arccsch`, `Arcsech` also have a branch point at `0` (`dlmf_4_37_i_branch_zero`).
  - 4.37.1: the square root cannot be principal at every real point of the paths
    (`dlmf_4_37_1_branch`, `cosh_of_arcsinh_path`); it is principal at the start `t = 0`.
  - 4.37.2: the path starts at the excluded branch point `1`, and the square root cannot be
    principal at every point of `(1, ∞)` (`dlmf_4_37_2_branch`, `sinh_of_arccosh_path`).

## §4.37(ii) Principal Values

* The principal branches are values of the general functions: `dlmf_4_37_ii_principal_mem`.
* "Each is two-valued on the corresponding cut(s)": `dlmf_4_37_ii_two_valued`.
* "each is real on the part of the real axis that remains": `dlmf_4_37_ii_real`.
* 4.37.7–4.37.9: `dlmf_4_37_7_9`. **Erratum** (typo): DLMF introduces them as the principal
  values of the inverse hyperbolic "cosecant, hyperbolic secant, and hyperbolic tangent"; 4.37.9
  is the hyperbolic cotangent.
* "These functions are analytic in the cut plane depicted in Figure 4.37.1(iv), (v), (vi)":
  `dlmf_4_37_ii_analytic` (also `arcsinh`, `arccosh`, `arctanh` in (i)–(iii)).

## §4.37(iii) Reflection Formulas

* 4.37.10, 4.37.12, 4.37.13, 4.37.15: `dlmf_4_37_10`, `dlmf_4_37_12`, `dlmf_4_37_13`,
  `dlmf_4_37_15` (directly from the integrals; for all `z`).
* **Errata** 4.37.11, 4.37.14: the signs are reversed. Correct: `arccosh(−z) = ∓πi + arccosh z`
  and `arcsech(−z) = ±πi + arcsech z` for `ℑz ≷ 0` (`dlmf_4_37_11`, `dlmf_4_37_14`, via
  `coshRoot_neg` and `ln(−w) = ln w ∓ πi`); counterexamples at `z = i`
  (`dlmf_4_37_11_erratum`, `dlmf_4_37_14_erratum`). DLMF's own 4.37.20 gives
  `arccosh(±i) = ±½πi + ln(√2 + 1)`, so `arccosh(−i) = arccosh i − πi`.
-/

open Set Filter Topology Complex MeasureTheory
open scoped Real Interval

namespace Azurite.DLMF

/-! ### §4.37(i) General Definitions -/

/-- **DLMF 4.37.1** (general values): `Arcsinh z = ∫₀^z dt/(1 + t²)^{1/2}` over `C¹` paths from
`0` to `z` avoiding `±i`, the square root continued from its principal value `1` at `t = 0`. -/
def arcsinhGen (z : ℂ) : Set ℂ :=
  {w | ∃ γ γ' g : ℝ → ℂ, γ 0 = 0 ∧ γ 1 = z ∧
    (∀ s ∈ Icc (0 : ℝ) 1, HasDerivWithinAt γ (γ' s) (Icc 0 1) s) ∧ ContinuousOn γ' (Icc 0 1) ∧
    (∀ s ∈ Icc (0 : ℝ) 1, γ s ≠ I ∧ γ s ≠ -I) ∧ ContinuousOn g (Icc 0 1) ∧
    (∀ s ∈ Icc (0 : ℝ) 1, g s ^ 2 = 1 + γ s ^ 2) ∧ g 0 = 1 ∧
    w = ∫ s in (0 : ℝ)..1, γ' s / g s}

/-- **DLMF 4.37.2** (general values): `Arccosh z = ∫₁^z dt/(t² − 1)^{1/2}` over `C¹` paths from
`1` to `z` that avoid `±1` after leaving `1`, with a continuous branch of `(t² − 1)^{1/2}`; the
integrand is (improperly) integrable at `t = 1`. -/
def arccoshGen (z : ℂ) : Set ℂ :=
  {w | ∃ γ γ' g : ℝ → ℂ, γ 0 = 1 ∧ γ 1 = z ∧
    (∀ s ∈ Icc (0 : ℝ) 1, HasDerivWithinAt γ (γ' s) (Icc 0 1) s) ∧ ContinuousOn γ' (Icc 0 1) ∧
    (∀ s ∈ Ioc (0 : ℝ) 1, γ s ≠ 1 ∧ γ s ≠ -1) ∧ ContinuousOn g (Icc 0 1) ∧
    (∀ s ∈ Icc (0 : ℝ) 1, g s ^ 2 = γ s ^ 2 - 1) ∧
    IntervalIntegrable (fun s => γ' s / g s) volume 0 1 ∧
    w = ∫ s in (0 : ℝ)..1, γ' s / g s}

/-- **DLMF 4.37.3** (general values): `Arctanh z = ∫₀^z dt/(1 − t²)` over `C¹` paths from `0` to
`z` avoiding `±1`. -/
def arctanhGen (z : ℂ) : Set ℂ :=
  {w | ∃ γ γ' : ℝ → ℂ, γ 0 = 0 ∧ γ 1 = z ∧
    (∀ s ∈ Icc (0 : ℝ) 1, HasDerivWithinAt γ (γ' s) (Icc 0 1) s) ∧ ContinuousOn γ' (Icc 0 1) ∧
    (∀ s ∈ Icc (0 : ℝ) 1, γ s ≠ 1 ∧ γ s ≠ -1) ∧
    w = ∫ s in (0 : ℝ)..1, γ' s / (1 - γ s ^ 2)}

/-- **DLMF 4.37.4**: `Arccsch z = Arcsinh(1/z)`. -/
def arccschGen (z : ℂ) : Set ℂ := arcsinhGen (1 / z)

/-- **DLMF 4.37.5**: `Arcsech z = Arccosh(1/z)`. -/
def arcsechGen (z : ℂ) : Set ℂ := arccoshGen (1 / z)

/-- **DLMF 4.37.6**: `Arccoth z = Arctanh(1/z)`. -/
def arccothGen (z : ℂ) : Set ℂ := arctanhGen (1 / z)

theorem I_mul_eq_one_iff {a : ℂ} : I * a = 1 ↔ a = -I := by
  constructor
  · intro h; linear_combination -I * h + a * I_sq
  · rintro rfl; rw [mul_neg, I_mul_I, neg_neg]

theorem I_mul_eq_neg_one_iff {a : ℂ} : I * a = -1 ↔ a = I := by
  constructor
  · intro h; linear_combination -I * h + a * I_sq
  · rintro rfl; rw [I_mul_I]

theorem I_mul_eq_I_iff {a : ℂ} : I * a = I ↔ a = 1 := by
  constructor
  · intro h; exact mul_left_cancel₀ I_ne_zero (h.trans (mul_one I).symm)
  · rintro rfl; rw [mul_one]

theorem I_mul_eq_neg_I_iff {a : ℂ} : I * a = -I ↔ a = -1 := by
  constructor
  · intro h; exact mul_left_cancel₀ I_ne_zero (h.trans (by ring))
  · rintro rfl; ring

theorem neg_I_mul_I_mul' (a : ℂ) : -I * (I * a) = a := by
  rw [← mul_assoc, neg_mul, I_mul_I]; ring

/-- `w ∈ Arcsinh z ↔ iw ∈ Arcsin(iz)` (the paths correspond under `γ ↦ iγ`). -/
theorem mem_arcsinhGen_iff_I {z w : ℂ} : w ∈ arcsinhGen z ↔ I * w ∈ arcsinGen (I * z) := by
  constructor
  · rintro ⟨γ, γ', g, h0, h1, hγ, hγ', hne, hg, hsq, hg0, rfl⟩
    refine ⟨fun s => I * γ s, fun s => I * γ' s, g, by simp [h0], by simp [h1],
      fun s hs => (hγ s hs).const_mul I, continuousOn_const.mul hγ', fun s hs => ⟨fun h => ?_,
      fun h => ?_⟩, hg, fun s hs => ?_, hg0, ?_⟩
    · exact (hne s hs).2 (I_mul_eq_one_iff.mp h)
    · exact (hne s hs).1 (I_mul_eq_neg_one_iff.mp h)
    · linear_combination hsq s hs + γ s ^ 2 * I_sq
    · rw [← intervalIntegral.integral_const_mul]
      congr 1; funext s; ring
  · rintro ⟨γ, γ', g, h0, h1, hγ, hγ', hne, hg, hsq, hg0, hw⟩
    refine ⟨fun s => -I * γ s, fun s => -I * γ' s, g, by simp [h0],
      by show -I * γ 1 = z; rw [h1]; linear_combination -z * I_sq,
      fun s hs => (hγ s hs).const_mul (-I), continuousOn_const.mul hγ',
      fun s hs => ⟨fun h => ?_, fun h => ?_⟩, hg, fun s hs => ?_, hg0, ?_⟩
    · exact (hne s hs).2 (by linear_combination I * h + (γ s + 1) * I_sq)
    · exact (hne s hs).1 (by linear_combination I * h + (γ s - 1) * I_sq)
    · linear_combination hsq s hs - γ s ^ 2 * I_sq
    · have : ∫ s in (0 : ℝ)..1, -I * γ' s / g s = -I * ∫ s in (0 : ℝ)..1, γ' s / g s := by
        rw [← intervalIntegral.integral_const_mul]; congr 1; funext s; ring
      rw [this, ← hw, neg_I_mul_I_mul']

/-- **DLMF 4.37.1** (general values): for `z ≠ ±i` the values of `Arcsinh z` are exactly the
solutions `w` of `sinh w = z`. -/
theorem mem_arcsinhGen_iff {z w : ℂ} (h1 : z ≠ I) (h2 : z ≠ -I) :
    w ∈ arcsinhGen z ↔ sinh w = z := by
  rw [mem_arcsinhGen_iff_I, mem_arcsinGen_iff (fun h => h2 (I_mul_eq_one_iff.mp h))
    (fun h => h1 (I_mul_eq_neg_one_iff.mp h)), dlmf_4_28_8]
  exact ⟨fun h => mul_left_cancel₀ I_ne_zero h, fun h => by rw [h]⟩

/-- `w ∈ Arctanh z ↔ iw ∈ Arctan(iz)`. -/
theorem mem_arctanhGen_iff_I {z w : ℂ} : w ∈ arctanhGen z ↔ I * w ∈ arctanGen (I * z) := by
  constructor
  · rintro ⟨γ, γ', h0, h1, hγ, hγ', hne, rfl⟩
    refine ⟨fun s => I * γ s, fun s => I * γ' s, by simp [h0], by simp [h1],
      fun s hs => (hγ s hs).const_mul I, continuousOn_const.mul hγ', fun s hs => ⟨fun h => ?_,
      fun h => ?_⟩, ?_⟩
    · exact (hne s hs).1 (I_mul_eq_I_iff.mp h)
    · exact (hne s hs).2 (I_mul_eq_neg_I_iff.mp h)
    · rw [← intervalIntegral.integral_const_mul]
      congr 1; funext s
      rw [mul_pow, I_sq]; ring
  · rintro ⟨γ, γ', h0, h1, hγ, hγ', hne, hw⟩
    refine ⟨fun s => -I * γ s, fun s => -I * γ' s, by simp [h0],
      by show -I * γ 1 = z; rw [h1]; linear_combination -z * I_sq,
      fun s hs => (hγ s hs).const_mul (-I), continuousOn_const.mul hγ',
      fun s hs => ⟨fun h => ?_, fun h => ?_⟩, ?_⟩
    · exact (hne s hs).1 (by linear_combination I * h + γ s * I_sq)
    · exact (hne s hs).2 (by linear_combination I * h + γ s * I_sq)
    · have : ∫ s in (0 : ℝ)..1, -I * γ' s / (1 - (-I * γ s) ^ 2) =
          -I * ∫ s in (0 : ℝ)..1, γ' s / (1 + γ s ^ 2) := by
        rw [← intervalIntegral.integral_const_mul]; congr 1; funext s
        rw [mul_pow, neg_sq, I_sq]; ring
      rw [this, ← hw, neg_I_mul_I_mul']

/-- **DLMF 4.37.3** (general values): the values of `Arctanh z` are exactly the solutions `w` of
`tanh w = z` with `cosh w ≠ 0`. -/
theorem mem_arctanhGen_iff {z w : ℂ} : w ∈ arctanhGen z ↔ cosh w ≠ 0 ∧ tanh w = z := by
  rw [mem_arctanhGen_iff_I, mem_arctanGen_iff, dlmf_4_28_9, dlmf_4_28_10]
  exact and_congr_right fun _ => ⟨fun h => mul_left_cancel₀ I_ne_zero h, fun h => by rw [h]⟩

/-- The key property of a 4.37.2 path: along it, `Φ(s) = ∫₁^{γ(s)} dt/(t² − 1)^{1/2}` satisfies
`cosh Φ(s) = γ(s)` and `sinh Φ(s) = g(s)` (the invariants `γ cosh Φ − g sinh Φ = 1` and
`g cosh Φ − γ sinh Φ = 0`; the start `t = 1` is a singular point of the integrand). -/
theorem cosh_sinh_of_arccosh_path {γ γ' g : ℝ → ℂ} (h0 : γ 0 = 1)
    (hγ : ∀ s ∈ Icc (0 : ℝ) 1, HasDerivWithinAt γ (γ' s) (Icc 0 1) s)
    (hγ' : ContinuousOn γ' (Icc 0 1)) (hne : ∀ s ∈ Ioc (0 : ℝ) 1, γ s ≠ 1 ∧ γ s ≠ -1)
    (hg : ContinuousOn g (Icc 0 1)) (hsq : ∀ s ∈ Icc (0 : ℝ) 1, g s ^ 2 = γ s ^ 2 - 1)
    (hint : IntervalIntegrable (fun s => γ' s / g s) volume 0 1) :
    ∀ s ∈ Icc (0 : ℝ) 1, cosh (∫ u in (0 : ℝ)..s, γ' u / g u) = γ s ∧
      sinh (∫ u in (0 : ℝ)..s, γ' u / g u) = g s := by
  have hgne : ∀ s ∈ Ioc (0 : ℝ) 1, g s ≠ 0 := by
    intro s hs h
    have h' := hsq s (Ioc_subset_Icc_self hs)
    rw [h] at h'
    have : (γ s - 1) * (γ s + 1) = 0 := by linear_combination -h'
    rcases mul_eq_zero.mp this with h1 | h1
    · exact (hne s hs).1 (by linear_combination h1)
    · exact (hne s hs).2 (by linear_combination h1)
  have hg0 : g 0 = 0 := by
    have := hsq 0 (left_mem_Icc.mpr zero_le_one)
    rw [h0] at this
    exact pow_eq_zero_iff two_ne_zero |>.mp (by rw [this]; ring)
  set f : ℝ → ℂ := fun u => γ' u / g u with hf
  have hfc : ContinuousOn f (Ioc 0 1) :=
    (hγ'.mono Ioc_subset_Icc_self).div (hg.mono Ioc_subset_Icc_self) hgne
  set Φ : ℝ → ℂ := fun s => ∫ u in (0 : ℝ)..s, f u with hΦ
  have hΦc : ContinuousOn Φ (Icc 0 1) := by
    have := intervalIntegral.continuousOn_primitive_interval (a := (0 : ℝ)) (b := 1)
      (μ := volume) (f := f) (by
        rw [uIcc_of_le zero_le_one]
        exact (intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one).mp hint)
    rwa [uIcc_of_le zero_le_one] at this
  have hΦd : ∀ s ∈ Ioo (0 : ℝ) 1, HasDerivAt Φ (f s) s := by
    intro s hs
    apply intervalIntegral.integral_hasDerivAt_right
    · exact hint.mono_set (by
        rw [uIcc_of_le hs.1.le, uIcc_of_le zero_le_one]
        exact Icc_subset_Icc le_rfl hs.2.le)
    · exact (hfc.mono Ioo_subset_Ioc_self).stronglyMeasurableAtFilter isOpen_Ioo s hs
    · exact (hfc.mono Ioo_subset_Ioc_self).continuousAt (isOpen_Ioo.mem_nhds hs)
  have hγd : ∀ s ∈ Ioo (0 : ℝ) 1, HasDerivAt γ (γ' s) s := fun s hs =>
    (hγ s (Ioo_subset_Icc_self hs)).hasDerivAt (Icc_mem_nhds hs.1 hs.2)
  have hgd : ∀ s ∈ Ioo (0 : ℝ) 1, HasDerivAt g (2 * γ s * γ' s / (2 * g s)) s := by
    intro s hs
    have hsI : Icc (0 : ℝ) 1 ∈ 𝓝 s := Icc_mem_nhds hs.1 hs.2
    have hq : HasDerivAt (fun u => γ u ^ 2 - 1) (2 * γ s * γ' s) s := by
      have := ((hγd s hs).pow 2).sub_const 1
      convert this using 1
      simp only [Nat.cast_ofNat]
      ring
    exact hasDerivAt_of_sq_eq hq (hg.continuousAt hsI)
      (Filter.mem_of_superset hsI fun u hu => hsq u hu) (hgne s (Ioo_subset_Ioc_self hs))
  have hγc : ContinuousOn γ (Icc 0 1) := fun s hs => (hγ s hs).continuousWithinAt
  have hcosh := continuous_cosh.comp_continuousOn hΦc
  have hsinh := continuous_sinh.comp_continuousOn hΦc
  set E : ℝ → ℂ := fun s => γ s * cosh (Φ s) - g s * sinh (Φ s) with hE
  set F : ℝ → ℂ := fun s => g s * cosh (Φ s) - γ s * sinh (Φ s) with hF
  have hEc : ContinuousOn E (Icc 0 1) := (hγc.mul hcosh).sub (hg.mul hsinh)
  have hFc : ContinuousOn F (Icc 0 1) := (hg.mul hcosh).sub (hγc.mul hsinh)
  have hEd : ∀ s ∈ Ioo (0 : ℝ) 1, HasDerivAt E 0 s := by
    intro s hs
    have hc := (Complex.hasDerivAt_cosh (Φ s)).comp s (hΦd s hs)
    have hsn := (Complex.hasDerivAt_sinh (Φ s)).comp s (hΦd s hs)
    have := ((hγd s hs).mul hc).sub ((hgd s hs).mul hsn)
    refine this.congr_deriv ?_
    have := hgne s (Ioo_subset_Ioc_self hs)
    simp only [hf, Function.comp_apply]
    field_simp
    ring
  have hFd : ∀ s ∈ Ioo (0 : ℝ) 1, HasDerivAt F 0 s := by
    intro s hs
    have hc := (Complex.hasDerivAt_cosh (Φ s)).comp s (hΦd s hs)
    have hsn := (Complex.hasDerivAt_sinh (Φ s)).comp s (hΦd s hs)
    have := ((hgd s hs).mul hc).sub ((hγd s hs).mul hsn)
    refine this.congr_deriv ?_
    have := hgne s (Ioo_subset_Ioc_self hs)
    simp only [hf, Function.comp_apply]
    field_simp
    ring
  have hE0 : E 0 = 1 := by simp [hE, hΦ, h0, hg0]
  have hF0 : F 0 = 0 := by simp [hF, hΦ, h0, hg0]
  intro s hs
  have e := eq_of_hasDerivAt_zero_Icc hEc hEd s hs
  have f' := eq_of_hasDerivAt_zero_Icc hFc hFd s hs
  rw [hE0] at e
  rw [hF0] at f'
  simp only [hE, hF] at e f'
  have hsc := cosh_sq_sub_sinh_sq (Φ s)
  constructor
  · linear_combination (-cosh (Φ s)) * e - sinh (Φ s) * f' + γ s * hsc
  · linear_combination (-sinh (Φ s)) * e - cosh (Φ s) * f' + g s * hsc

theorem sinh_ne_zero_of_re_ne {u : ℂ} (h : u.re ≠ 0) : sinh u ≠ 0 := fun h0 => by
  obtain ⟨k, hk⟩ := (dlmf_4_28_sinh_zeros u).mp h0
  apply h; rw [hk]; simp

/-- **DLMF 4.37.2** (general values): for `z ≠ ±1` the values of `Arccosh z` are exactly the
solutions `w` of `cosh w = z`. -/
theorem mem_arccoshGen_iff {z w : ℂ} (h1 : z ≠ 1) (h2 : z ≠ -1) :
    w ∈ arccoshGen z ↔ cosh w = z := by
  constructor
  · rintro ⟨γ, γ', g, h0, h1', hγ, hγ', hne, hg, hsq, hint, rfl⟩
    rw [← h1']
    exact (cosh_sinh_of_arccosh_path h0 hγ hγ' hne hg hsq hint 1 ⟨zero_le_one, le_rfl⟩).1
  · intro hw
    -- the path `γ(s) = cosh φ(s)`, `φ(s) = s w + c s(1 − s)` with `c = ±1` keeping `ℜφ ≠ 0`
    obtain ⟨c, hc1, hcre⟩ : ∃ c : ℝ, (c = 1 ∨ c = -1) ∧
        ∀ s ∈ Ioo (0 : ℝ) 1, s * w.re + c * (s * (1 - s)) ≠ 0 := by
      rcases le_or_gt 0 w.re with h | h
      · refine ⟨1, Or.inl rfl, fun s hs => ?_⟩
        have : 0 < s * (1 - s) := mul_pos hs.1 (by linarith [hs.2])
        nlinarith [hs.1]
      · refine ⟨-1, Or.inr rfl, fun s hs => ?_⟩
        have : 0 < s * (1 - s) := mul_pos hs.1 (by linarith [hs.2])
        nlinarith [hs.1]
    set φ : ℝ → ℂ := fun s => (s : ℂ) * w + (c : ℂ) * ((s : ℂ) * (1 - (s : ℂ))) with hφ
    set φ' : ℝ → ℂ := fun s => w + (c : ℂ) * (1 - 2 * (s : ℂ)) with hφ'
    have hφd : ∀ s : ℝ, HasDerivAt φ (φ' s) s := fun s => by
      have hs := (hasDerivAt_id s).ofReal_comp
      simp only [id, ofReal_one] at hs
      have := (hs.mul_const w).add ((hs.mul (hs.const_sub 1)).const_mul (c : ℂ))
      refine this.congr_deriv ?_
      simp only [hφ']; ring
    have hre : ∀ s : ℝ, (φ s).re = s * w.re + c * (s * (1 - s)) := fun s => by
      simp [hφ]
    have hφ1 : φ 1 = w := by simp [hφ]
    have hsinh1 : sinh w ≠ 0 := fun h0 => by
      have := cosh_sq_sub_sinh_sq w
      rw [h0, hw] at this
      have : (z - 1) * (z + 1) = 0 := by linear_combination this
      rcases mul_eq_zero.mp this with h | h
      · exact h1 (by linear_combination h)
      · exact h2 (by linear_combination h)
    have hsne : ∀ s ∈ Ioc (0 : ℝ) 1, sinh (φ s) ≠ 0 := by
      intro s hs
      rcases hs.2.lt_or_eq with h | h
      · exact sinh_ne_zero_of_re_ne (by rw [hre]; exact hcre s ⟨hs.1, h⟩)
      · rw [h, hφ1]; exact hsinh1
    have hint : ∀ s ∈ Ioc (0 : ℝ) 1, sinh (φ s) * φ' s / sinh (φ s) = φ' s := fun s hs => by
      field_simp [hsne s hs]
    refine ⟨fun s => cosh (φ s), fun s => sinh (φ s) * φ' s, fun s => sinh (φ s),
      by simp [hφ], by simp only [hφ1, hw],
      fun s _ => ((Complex.hasDerivAt_cosh (φ s)).comp s (hφd s)).hasDerivWithinAt,
      (Continuous.continuousOn (by simp only [hφ, hφ']; fun_prop)),
      fun s hs => ⟨fun h => hsne s hs ?_, fun h => hsne s hs ?_⟩,
      (Continuous.continuousOn (by simp only [hφ]; fun_prop)),
      fun s _ => by linear_combination -cosh_sq_sub_sinh_sq (φ s), ?_, ?_⟩
    · have h' : cosh (φ s) = 1 := h
      have := cosh_sq_sub_sinh_sq (φ s); rw [h'] at this
      exact pow_eq_zero_iff two_ne_zero |>.mp (by linear_combination -this)
    · have h' : cosh (φ s) = -1 := h
      have := cosh_sq_sub_sinh_sq (φ s); rw [h'] at this
      exact pow_eq_zero_iff two_ne_zero |>.mp (by linear_combination -this)
    · have hφc : Continuous φ' := by rw [hφ']; fun_prop
      refine (hφc.intervalIntegrable (μ := volume) 0 1 |>.congr ?_)
      rw [uIoc_of_le zero_le_one]
      exact fun s hs => (hint s hs).symm
    · have hcongr : ∫ s in (0 : ℝ)..1, sinh (φ s) * φ' s / sinh (φ s) =
          ∫ s in (0 : ℝ)..1, φ' s := by
        refine intervalIntegral.integral_congr_ae ?_
        refine Eventually.of_forall fun s hs => ?_
        rw [uIoc_of_le zero_le_one] at hs
        exact hint s hs
      rw [hcongr, intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hφd s)
        ((Continuous.intervalIntegrable (by rw [hφ']; fun_prop) 0 1)), hφ1]
      simp [hφ]

/-! ### The definitions restated; multivaluedness -/

/-- **DLMF 4.37.1–4.37.6**: the general values (as defined above). -/
theorem dlmf_4_37_4_6 (z : ℂ) :
    arccschGen z = arcsinhGen (1 / z) ∧ arcsechGen z = arccoshGen (1 / z) ∧
      arccothGen z = arctanhGen (1 / z) :=
  ⟨rfl, rfl, rfl⟩

/-- "Each of the six functions is a multivalued function of `z`": at every admissible `z` each
of `Arcsinh`, `Arccosh`, `Arctanh` has two different values. -/
theorem dlmf_4_37_i_multivalued {z : ℂ} :
    (z ≠ I → z ≠ -I → ∃ w₁ ∈ arcsinhGen z, ∃ w₂ ∈ arcsinhGen z, w₁ ≠ w₂) ∧
    (z ≠ 1 → z ≠ -1 → ∃ w₁ ∈ arccoshGen z, ∃ w₂ ∈ arccoshGen z, w₁ ≠ w₂) ∧
    (z ≠ 1 → z ≠ -1 → ∃ w₁ ∈ arctanhGen z, ∃ w₂ ∈ arctanhGen z, w₁ ≠ w₂) := by
  have hI : ∀ {w₁ w₂ : ℂ}, w₁ ≠ w₂ → -I * w₁ ≠ -I * w₂ := fun h h' =>
    h (mul_left_cancel₀ (neg_ne_zero.mpr I_ne_zero) h')
  refine ⟨fun h1 h2 => ?_, fun h1 h2 => ?_, fun h1 h2 => ?_⟩
  · obtain ⟨w₁, hw₁, w₂, hw₂, hne⟩ := (dlmf_4_23_i_multivalued (z := I * z)).1
      (fun h => h2 (I_mul_eq_one_iff.mp h)) (fun h => h1 (I_mul_eq_neg_one_iff.mp h))
    exact ⟨-I * w₁, mem_arcsinhGen_iff_I.mpr (by rwa [← mul_assoc, mul_neg, I_mul_I, neg_neg,
      one_mul]), -I * w₂, mem_arcsinhGen_iff_I.mpr (by rwa [← mul_assoc, mul_neg, I_mul_I,
      neg_neg, one_mul]), hI hne⟩
  · obtain ⟨u, hu⟩ := cos_surjective z
    have hπ : (2 * π * I : ℂ) ≠ 0 :=
      mul_ne_zero (mul_ne_zero two_ne_zero (ofReal_ne_zero.mpr Real.pi_ne_zero)) I_ne_zero
    have hw : cosh (I * u) = z := by
      rw [← dlmf_4_28_9, ← mul_assoc, I_mul_I, neg_one_mul, cos_neg, hu]
    refine ⟨I * u, (mem_arccoshGen_iff h1 h2).mpr hw, I * u + 2 * π * I,
      (mem_arccoshGen_iff h1 h2).mpr (by rw [dlmf_4_28_cosh_periodic, hw]),
      fun h => hπ (by linear_combination -h)⟩
  · obtain ⟨w₁, hw₁, w₂, hw₂, hne⟩ := (dlmf_4_23_i_multivalued (z := I * z)).2.2
      (fun h => h1 (I_mul_eq_I_iff.mp h)) (fun h => h2 (I_mul_eq_neg_I_iff.mp h))
    exact ⟨-I * w₁, mem_arctanhGen_iff_I.mpr (by rwa [← mul_assoc, mul_neg, I_mul_I, neg_neg,
      one_mul]), -I * w₂, mem_arctanhGen_iff_I.mpr (by rwa [← mul_assoc, mul_neg, I_mul_I,
      neg_neg, one_mul]), hI hne⟩

/-! ### Branch points -/

theorem mapsTo_mul_ball {a c : ℂ} (ha : ‖a‖ = 1) (r : ℝ) :
    MapsTo (fun u => a * u) (Metric.ball c r \ {c}) (Metric.ball (a * c) r \ {a * c}) := by
  intro u ⟨hu, hu'⟩
  have ha0 : a ≠ 0 := fun h => by rw [h, norm_zero] at ha; exact zero_ne_one ha
  refine ⟨?_, fun h => hu' (mul_left_cancel₀ ha0 h)⟩
  rw [Metric.mem_ball, dist_eq_norm, ← mul_sub, norm_mul, ha, one_mul, ← dist_eq_norm]
  exact hu

theorem norm_neg_I : ‖-I‖ = 1 := by rw [norm_neg, norm_I]

/-- If `f` is continuous on a punctured disc around `s`, then `u ↦ b f(a u)` (`|a| = 1`) is
continuous on the punctured disc around `c` with `a c = s`. -/
theorem continuousOn_comp_mul {f : ℂ → ℂ} {a b c s : ℂ} (ha : ‖a‖ = 1) (hc : a * c = s) {r : ℝ}
    (hf : ContinuousOn f (Metric.ball s r \ {s})) :
    ContinuousOn (fun u => b * f (a * u)) (Metric.ball c r \ {c}) := by
  subst hc
  exact continuousOn_const.mul (hf.comp (continuous_const.mul continuous_id).continuousOn
    (mapsTo_mul_ball ha r))

theorem mem_ball_mul {a c s u : ℂ} (ha : ‖a‖ = 1) (hc : a * c = s) {r : ℝ}
    (hu : u ∈ Metric.ball c r \ {c}) : a * u ∈ Metric.ball s r \ {s} :=
  hc ▸ mapsTo_mul_ball ha r hu

theorem I_mul_one_div_I_mul (u : ℂ) : I * (1 / (I * u)) = 1 / u := by
  rcases eq_or_ne u 0 with rfl | hu
  · simp
  · field_simp

theorem I_mul_neg_I_mul' (a : ℂ) : I * (-I * a) = a := by
  rw [← mul_assoc, mul_neg, I_mul_I, neg_neg, one_mul]

/-- **DLMF §4.37(i)**: "`Arcsinh z` and `Arccsch z` have branch points at `z = ±i`; the other four
functions have branch points at `z = ±1`". At none of these points is there a continuous
single-valued branch on any punctured disc (reduced to §4.23(i) by `z ↦ ±iz`). -/
theorem dlmf_4_37_i_branch_points {r : ℝ} (hr : 0 < r) {f : ℂ → ℂ} :
    (∀ s : ℂ, (s = I ∨ s = -I) → ContinuousOn f (Metric.ball s r \ {s}) →
      (¬ ∀ z ∈ Metric.ball s r \ {s}, sinh (f z) = z) ∧
      (¬ ∀ z ∈ Metric.ball s r \ {s}, sinh (f z) = 1 / z)) ∧
    (∀ s : ℂ, (s = 1 ∨ s = -1) → ContinuousOn f (Metric.ball s r \ {s}) →
      (¬ ∀ z ∈ Metric.ball s r \ {s}, cosh (f z) = z) ∧
      (¬ ∀ z ∈ Metric.ball s r \ {s}, tanh (f z) = z) ∧
      (¬ ∀ z ∈ Metric.ball s r \ {s}, cosh (f z) = 1 / z) ∧
      (¬ ∀ z ∈ Metric.ball s r \ {s}, tanh (f z) = 1 / z)) := by
  have hI1 : ‖(I : ℂ)‖ = 1 := norm_I
  refine ⟨fun s hs hf => ⟨fun h => ?_, fun h => ?_⟩, fun s hs hf =>
    ⟨fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_⟩⟩
  · -- `F(u) = i f(−iu)`: `sin F(u) = u` near `is ∈ {±1}`
    have hc : -I * (I * s) = s := neg_I_mul_I_mul' s
    refine no_arcsin_branch (s := I * s) (f := fun u => I * f (-I * u)) ?_ hr
      (continuousOn_comp_mul norm_neg_I hc hf) fun u hu => ?_
    · rcases hs with rfl | rfl
      · right; rw [I_mul_I]
      · left; rw [mul_neg, I_mul_I, neg_neg]
    · rw [dlmf_4_28_8, h _ (mem_ball_mul norm_neg_I hc hu), I_mul_neg_I_mul']
  · -- `F(u) = i f(iu)`: `sin F(u) = 1/u` near `−is ∈ {±1}`
    have hc : I * (-I * s) = s := I_mul_neg_I_mul' s
    refine no_arccsc_branch (s := -I * s) (f := fun u => I * f (I * u)) ?_ hr
      (continuousOn_comp_mul hI1 hc hf) fun u hu => ?_
    · rcases hs with rfl | rfl
      · left; rw [neg_mul, I_mul_I, neg_neg]
      · right; rw [mul_neg, neg_mul, I_mul_I, neg_neg]
    · rw [dlmf_4_28_8, h _ (mem_ball_mul hI1 hc hu), I_mul_one_div_I_mul]
  · exact no_arccos_branch hs hr (f := fun u => I * f u) (continuousOn_const.mul hf)
      fun u hu => by rw [dlmf_4_28_9, h u hu]
  · have hc : -I * (I * s) = s := neg_I_mul_I_mul' s
    refine no_arctan_branch (s := I * s) (f := fun u => I * f (-I * u)) ?_ hr
      (continuousOn_comp_mul norm_neg_I hc hf) fun u hu => ?_
    · rcases hs with rfl | rfl
      · left; rw [mul_one]
      · right; rw [mul_neg, mul_one]
    · rw [dlmf_4_28_10, h _ (mem_ball_mul norm_neg_I hc hu), I_mul_neg_I_mul']
  · exact no_arcsec_branch hs hr (f := fun u => I * f u) (continuousOn_const.mul hf)
      fun u hu => by rw [dlmf_4_28_9, h u hu]
  · have hc : I * (-I * s) = s := I_mul_neg_I_mul' s
    refine no_arccot_branch (s := -I * s) (f := fun u => I * f (I * u)) ?_ hr
      (continuousOn_comp_mul hI1 hc hf) fun u hu => ?_
    · rcases hs with rfl | rfl
      · right; rw [mul_one]
      · left; rw [mul_neg, mul_one, neg_neg]
    · rw [dlmf_4_28_10, h _ (mem_ball_mul hI1 hc hu), I_mul_one_div_I_mul]

/-- **Imprecision** (§4.37(i)): `Arccsch z = Arcsinh(1/z)` and `Arcsech z = Arccosh(1/z)` also have
a branch point at `z = 0`, which DLMF's list omits (as `Arccsc`, `Arcsec` in §4.23(i)). -/
theorem dlmf_4_37_i_branch_zero {r : ℝ} (hr : 0 < r) {f : ℂ → ℂ}
    (hf : ContinuousOn f (Metric.ball 0 r \ {0})) :
    (¬ ∀ z ∈ Metric.ball (0 : ℂ) r \ {0}, sinh (f z) = 1 / z) ∧
      (¬ ∀ z ∈ Metric.ball (0 : ℂ) r \ {0}, cosh (f z) = 1 / z) := by
  have hI1 : ‖(I : ℂ)‖ = 1 := norm_I
  refine ⟨fun h => ?_, fun h => ?_⟩
  · exact no_arccsc_branch_zero hr (f := fun u => I * f (I * u))
      (continuousOn_comp_mul hI1 (mul_zero I) hf) fun u hu => by
        rw [dlmf_4_28_8, h _ (mem_ball_mul hI1 (mul_zero I) hu), I_mul_one_div_I_mul]
  · exact no_arcsec_branch_zero hr (f := fun u => I * f u) (continuousOn_const.mul hf)
      fun u hu => by rw [dlmf_4_28_9, h u hu]

/-! ### The branch of the square root on the real axis -/

/-- Along a 4.37.1 path, the value `w` and the end of the branch satisfy `cosh w = g(1)`. -/
theorem cosh_of_arcsinh_path {γ γ' g : ℝ → ℂ} (h0 : γ 0 = 0)
    (hγ : ∀ s ∈ Icc (0 : ℝ) 1, HasDerivWithinAt γ (γ' s) (Icc 0 1) s)
    (hγ' : ContinuousOn γ' (Icc 0 1)) (hne : ∀ s ∈ Icc (0 : ℝ) 1, γ s ≠ I ∧ γ s ≠ -I)
    (hg : ContinuousOn g (Icc 0 1)) (hsq : ∀ s ∈ Icc (0 : ℝ) 1, g s ^ 2 = 1 + γ s ^ 2)
    (hg0 : g 0 = 1) : cosh (∫ s in (0 : ℝ)..1, γ' s / g s) = g 1 := by
  have h := (sin_cos_of_arcsin_path (γ := fun s => I * γ s) (γ' := fun s => I * γ' s) (g := g)
    (by simp [h0]) (fun s hs => (hγ s hs).const_mul I) (continuousOn_const.mul hγ')
    (fun s hs => ⟨fun h => (hne s hs).2 (I_mul_eq_one_iff.mp h),
      fun h => (hne s hs).1 (I_mul_eq_neg_one_iff.mp h)⟩) hg
    (fun s hs => by linear_combination hsq s hs + γ s ^ 2 * I_sq) hg0 1
    ⟨zero_le_one, le_rfl⟩).2
  rw [← h, show (∫ u in (0 : ℝ)..1, I * γ' u / g u) = I * ∫ u in (0 : ℝ)..1, γ' u / g u by
    rw [← intervalIntegral.integral_const_mul]; congr 1; funext u; ring, dlmf_4_28_9]

/-- **Imprecision** (4.37.1): "the function `(1 + t²)^{1/2}` assumes its principal value when `t`
is real" cannot hold at every real point of the paths. For real `x`, `πi − arcsinh x` is a value
of `Arcsinh x` (a solution of `sinh w = x`), but `cosh(πi − arcsinh x) =
−(1 + x²)^{1/2}`, so by `cosh_of_arcsinh_path` every path reaching this value ends at the real
point `t = x` on the negative branch. The branch is principal at the start `t = 0` and continued
from there (`arcsinhGen`). -/
theorem dlmf_4_37_1_branch (x : ℝ) :
    (π * I - (Real.arsinh x : ℂ)) ∈ arcsinhGen x ∧
      cosh (π * I - (Real.arsinh x : ℂ)) = -((√(1 + x ^ 2) : ℝ) : ℂ) := by
  have hpi : sinh (π * I) = 0 ∧ cosh (π * I) = -1 := by
    rw [sinh_mul_I, cosh_mul_I, sin_pi, cos_pi]; simp
  have hxI : (x : ℂ) ≠ I := fun h => by simpa using congrArg im h
  have hxI' : (x : ℂ) ≠ -I := fun h => by simpa using congrArg im h
  refine ⟨(mem_arcsinhGen_iff hxI hxI').mpr ?_, ?_⟩
  · rw [sinh_sub, hpi.1, hpi.2, ← ofReal_sinh, Real.sinh_arsinh]; ring
  · rw [cosh_sub, hpi.1, hpi.2, ← ofReal_cosh, Real.cosh_arsinh]; ring

/-- Along a 4.37.2 path, the value `w` and the end of the branch satisfy `sinh w = g(1)`. -/
theorem sinh_of_arccosh_path {γ γ' g : ℝ → ℂ} (h0 : γ 0 = 1)
    (hγ : ∀ s ∈ Icc (0 : ℝ) 1, HasDerivWithinAt γ (γ' s) (Icc 0 1) s)
    (hγ' : ContinuousOn γ' (Icc 0 1)) (hne : ∀ s ∈ Ioc (0 : ℝ) 1, γ s ≠ 1 ∧ γ s ≠ -1)
    (hg : ContinuousOn g (Icc 0 1)) (hsq : ∀ s ∈ Icc (0 : ℝ) 1, g s ^ 2 = γ s ^ 2 - 1)
    (hint : IntervalIntegrable (fun s => γ' s / g s) volume 0 1) :
    sinh (∫ s in (0 : ℝ)..1, γ' s / g s) = g 1 :=
  (cosh_sinh_of_arccosh_path h0 hγ hγ' hne hg hsq hint 1 ⟨zero_le_one, le_rfl⟩).2

/-- **Imprecision** (4.37.2): the path starts at the excluded point `t = 1`, where the integrand
is singular (`arccoshGen` takes paths that leave `1` and avoid `±1` afterwards, with an integrable
integrand). Moreover "`(t² − 1)^{1/2}` assumes its principal value when `t ∈ (1, ∞)`" cannot hold
at every such point: for `x > 1`, `−arccosh x` is a value of `Arccosh x`, but
`sinh(−arccosh x) = −(x² − 1)^{1/2}`, so by `sinh_of_arccosh_path` every path reaching it ends at
`t = x ∈ (1, ∞)` on the negative branch. -/
theorem dlmf_4_37_2_branch {x : ℝ} (hx : 1 < x) :
    (-(Real.arcosh x : ℂ)) ∈ arccoshGen x ∧
      sinh (-(Real.arcosh x : ℂ)) = -((√(x ^ 2 - 1) : ℝ) : ℂ) := by
  have h1 : (x : ℂ) ≠ 1 := fun h => by
    have := congrArg re h; simp at this; linarith
  have h2 : (x : ℂ) ≠ -1 := fun h => by
    have := congrArg re h; simp at this; linarith
  refine ⟨(mem_arccoshGen_iff h1 h2).mpr ?_, ?_⟩
  · rw [cosh_neg, ← ofReal_cosh, Real.cosh_arcosh hx.le]
  · rw [sinh_neg, ← ofReal_sinh, Real.sinh_arcosh hx.le]

/-! ### §4.37(ii) Principal Values -/

theorem arcsinhCut_ne {z : ℂ} (hz : z ∈ arcsinhCut) : z ≠ I ∧ z ≠ -I := by
  refine ⟨fun h => ?_, fun h => ?_⟩ <;> subst h <;> rcases hz with h | h <;> simp at h

theorem arccoshCut_ne {z : ℂ} (hz : z ∈ arccoshCut) : z ≠ 1 ∧ z ≠ -1 := by
  refine ⟨fun h => ?_, fun h => ?_⟩ <;> subst h <;> rcases hz with h | h <;> norm_num at h

/-- **DLMF §4.37(ii)**: the principal branches are values of the general functions (the
integrals along paths that do not cross the cuts). -/
theorem dlmf_4_37_ii_principal_mem {z : ℂ} :
    (z ∈ arcsinhCut → arcsinhD z ∈ arcsinhGen z) ∧
      (z ∈ arccoshCut → arccoshD z ∈ arccoshGen z) ∧
      (z ∈ arctanhCut → arctanhD z ∈ arctanhGen z) := by
  refine ⟨fun hz => ?_, fun hz => ?_, fun hz => ?_⟩
  · exact (mem_arcsinhGen_iff (arcsinhCut_ne hz).1 (arcsinhCut_ne hz).2).mpr (sinh_arcsinhD hz)
  · exact (mem_arccoshGen_iff (arccoshCut_ne hz).1 (arccoshCut_ne hz).2).mpr (cosh_arccoshD hz)
  · refine mem_arctanhGen_iff.mpr ⟨fun h0 => ?_, tanh_arctanhD hz⟩
    have := tanh_arctanhD hz
    rw [tanh_eq_sinh_div_cosh, h0, div_zero] at this
    rw [← this, arctanhD] at h0
    simp at h0

theorem tendsto_I_mul_re_side (y : ℝ) :
    Tendsto (fun z : ℂ => I * z) (𝓝[{z | 0 < z.re}] ((y : ℂ) * I))
        (𝓝[{w | 0 < w.im}] ((-y : ℝ) : ℂ)) ∧
      Tendsto (fun z : ℂ => I * z) (𝓝[{z | z.re < 0}] ((y : ℂ) * I))
        (𝓝[{w | w.im < 0}] ((-y : ℝ) : ℂ)) := by
  have hI : Tendsto (fun z : ℂ => I * z) (𝓝 ((y : ℂ) * I)) (𝓝 ((-y : ℝ) : ℂ)) := by
    have : Continuous fun z : ℂ => I * z := by fun_prop
    have h := this.tendsto ((y : ℂ) * I)
    rwa [show I * ((y : ℂ) * I) = ((-y : ℝ) : ℂ) by push_cast; ring_nf; rw [I_sq]; ring] at h
  refine ⟨tendsto_nhdsWithin_iff.mpr ⟨hI.mono_left nhdsWithin_le_nhds, ?_⟩,
    tendsto_nhdsWithin_iff.mpr ⟨hI.mono_left nhdsWithin_le_nhds, ?_⟩⟩
  · filter_upwards [self_mem_nhdsWithin] with z hz
    have hz' : 0 < z.re := hz
    show 0 < (I * z).im
    simpa using hz'
  · filter_upwards [self_mem_nhdsWithin] with z hz
    have hz' : z.re < 0 := hz
    show (I * z).im < 0
    simpa using hz'

theorem im_arccoshD_nonneg {z : ℂ} (hz : 0 < z.im) : 0 ≤ (arccoshD z).im := by
  rw [arccoshD_eq_log (Or.inl hz.ne'), log_im]
  exact arg_nonneg_iff.mpr (by rw [add_im]; linarith [im_coshRoot_nonneg hz])

theorem im_arccoshD_nonpos {z : ℂ} (hz : z.im < 0) : (arccoshD z).im ≤ 0 := by
  rw [arccoshD_eq_log (Or.inl hz.ne), log_im]
  exact (arg_neg_iff.mpr (by rw [add_im]; linarith [im_coshRoot_nonpos hz])).le

/-- **DLMF §4.37(ii)**: "Each is two-valued on the corresponding cut(s)": at every point of the
cuts of `arcsinh` (`iy`, `|y| > 1`), `arccosh` (`x < 1`) and `arctanh` (`|x| > 1`) the limits
from the two sides exist and differ. -/
theorem dlmf_4_37_ii_two_valued :
    (∀ y : ℝ, 1 < |y| → ∃ b c : ℂ, b ≠ c ∧
      Tendsto arcsinhD (𝓝[{z | 0 < z.re}] (y * I)) (𝓝 b) ∧
      Tendsto arcsinhD (𝓝[{z | z.re < 0}] (y * I)) (𝓝 c)) ∧
    (∀ x : ℝ, x < 1 → ∃ b c : ℂ, b ≠ c ∧
      Tendsto arccoshD (𝓝[{w | 0 < w.im}] (x : ℂ)) (𝓝 b) ∧
      Tendsto arccoshD (𝓝[{w | w.im < 0}] (x : ℂ)) (𝓝 c)) ∧
    (∀ x : ℝ, 1 < |x| → ∃ b c : ℂ, b ≠ c ∧
      Tendsto arctanhD (𝓝[{w | 0 < w.im}] (x : ℂ)) (𝓝 b) ∧
      Tendsto arctanhD (𝓝[{w | w.im < 0}] (x : ℂ)) (𝓝 c)) := by
  refine ⟨fun y hy => ?_, fun x hx => ?_, fun x hx => ?_⟩
  · obtain ⟨r, hr, e1, e2⟩ := arcsinD_cut_limits (x := -y) (by rwa [abs_neg])
    obtain ⟨t1, t2⟩ := tendsto_I_mul_re_side y
    have he : arcsinhD = fun z => -I * arcsinD (I * z) := funext arcsinhD_eq
    refine ⟨_, _, fun h => ?_, by rw [he]; exact (e1.comp t1).const_mul _,
      by rw [he]; exact (e2.comp t2).const_mul _⟩
    have := congrArg re h
    simp at this
    linarith
  · obtain ⟨b, c, hb, hc, e1, e2⟩ := arccoshD_cut_limits hx
    have hb0 : 0 ≤ b.im := by
      have := neBot_upper x
      exact ge_of_tendsto ((continuous_im.tendsto b).comp e1)
        (eventually_nhdsWithin_of_forall fun z hz => im_arccoshD_nonneg hz)
    have hc0 : c.im ≤ 0 := by
      have := neBot_lower x
      exact le_of_tendsto ((continuous_im.tendsto c).comp e2)
        (eventually_nhdsWithin_of_forall fun z hz => im_arccoshD_nonpos hz)
    refine ⟨b, c, fun h => ?_, e1, e2⟩
    rw [h] at hb0 hb
    exact hb (le_antisymm hc0 hb0)
  · obtain ⟨b, c, hbc, e1, e2⟩ := arctanD_cut_limits hx
    obtain ⟨t1, t2⟩ := tendsto_I_mul_side x
    have he : arctanhD = fun z => -I * arctanD (I * z) := funext arctanhD_eq
    refine ⟨-I * c, -I * b, fun h => hbc ?_, by rw [he]; exact (e2.comp t1).const_mul _,
      by rw [he]; exact (e1.comp t2).const_mul _⟩
    have := mul_left_cancel₀ (neg_ne_zero.mpr I_ne_zero) h
    rw [this]

/-- **DLMF §4.37(ii)**: "each is real on the part of the real axis that remains after deleting
the intersections with the corresponding cuts". -/
theorem dlmf_4_37_ii_real :
    (∀ x : ℝ, arcsinhD x = Real.arsinh x) ∧ (∀ x : ℝ, 1 < x → arccoshD x = Real.arcosh x) ∧
      ∀ x : ℝ, |x| < 1 → arctanhD x = Real.artanh x :=
  ⟨arcsinhD_ofReal, fun _ hx => arccoshD_ofReal hx.le, fun _ hx => arctanhD_ofReal (abs_lt.mp hx)⟩

/-- **DLMF 4.37.7–4.37.9**: `arccsch z = arcsinh(1/z)`, `arcsech z = arccosh(1/z)`,
`arccoth z = arctanh(1/z)`. -/
theorem dlmf_4_37_7_9 (z : ℂ) :
    arccschD z = arcsinhD (1 / z) ∧ arcsechD z = arccoshD (1 / z) ∧
      arccothD z = arctanhD (1 / z) :=
  ⟨rfl, rfl, rfl⟩

theorem arctanhD_differentiableAt {z : ℂ} (hz : z ∈ arctanhCut) :
    DifferentiableAt ℂ arctanhD z := by
  have he : arctanhD = fun z => -I * arctanD (I * z) := funext arctanhD_eq
  have hc := I_mul_mem_arctanCut.mpr hz
  rw [he]
  exact (((dlmf_4_15_F11.1 _ hc).differentiableAt (isOpen_arctanCut.mem_nhds hc)).comp z
    ((differentiableAt_id).const_mul I)).const_mul _

theorem one_div_mem_arccoshCut {z : ℂ} (hz : z.im ≠ 0 ∨ (0 < z.re ∧ z.re < 1)) :
    z ≠ 0 ∧ 1 / z ∈ arccoshCut := by
  have hz0 : z ≠ 0 := by
    rintro rfl
    rcases hz with h | h <;> simp at h
  refine ⟨hz0, ?_⟩
  by_cases him : z.im = 0
  · right
    obtain ⟨h1, h2⟩ := hz.resolve_left (not_not.mpr him)
    rw [one_div, inv_re, normSq_apply, him, mul_zero, add_zero, lt_div_iff₀ (by positivity)]
    nlinarith
  · left
    rw [one_div, inv_im]
    exact div_ne_zero (neg_ne_zero.mpr him) (normSq_pos.mpr hz0).ne'

/-- **DLMF §4.37(ii)**: "These functions are analytic in the cut plane depicted in Figure
4.37.1(iv), (v), (vi), respectively": `arccsch` off `[−i, i]`, `arcsech` off `(−∞, 0] ∪ [1, ∞)`,
`arccoth` off `[−1, 1]`. Also `arcsinh`, `arccosh`, `arctanh` in Figures 4.37.1(i)–(iii). -/
theorem dlmf_4_37_ii_analytic :
    DifferentiableOn ℂ arcsinhD arcsinhCut ∧ DifferentiableOn ℂ arccoshD arccoshCut ∧
      DifferentiableOn ℂ arctanhD arctanhCut ∧
      (∀ z : ℂ, z.re ≠ 0 ∨ 1 < |z.im| → DifferentiableAt ℂ arccschD z) ∧
      (∀ z : ℂ, z.im ≠ 0 ∨ (0 < z.re ∧ z.re < 1) → DifferentiableAt ℂ arcsechD z) ∧
      (∀ z : ℂ, z.im ≠ 0 ∨ 1 < |z.re| → DifferentiableAt ℂ arccothD z) := by
  have hinv : ∀ z : ℂ, z ≠ 0 → DifferentiableAt ℂ (fun z : ℂ => 1 / z) z := fun z hz =>
    (differentiableAt_const _).div differentiableAt_id hz
  refine ⟨fun z hz => (hasDerivAt_arcsinhD hz).differentiableAt.differentiableWithinAt,
    fun z hz => (hasDerivAt_arccoshD hz).differentiableAt.differentiableWithinAt,
    fun z hz => (arctanhD_differentiableAt hz).differentiableWithinAt, fun z hz => ?_,
    fun z hz => ?_, fun z hz => ?_⟩
  · obtain ⟨hz0, hc⟩ := one_div_mem_arctanCut hz
    exact (hasDerivAt_arcsinhD hc).differentiableAt.comp z (hinv z hz0)
  · obtain ⟨hz0, hc⟩ := one_div_mem_arccoshCut hz
    exact (hasDerivAt_arccoshD hc).differentiableAt.comp z (hinv z hz0)
  · obtain ⟨hz0, hc⟩ := one_div_mem_arcsinCut hz
    exact (arctanhD_differentiableAt hc).comp z (hinv z hz0)

/-! ### §4.37(iii) Reflection Formulas -/

/-- **DLMF 4.37.10**: `arcsinh(−z) = −arcsinh z`. -/
theorem dlmf_4_37_10 (z : ℂ) : arcsinhD (-z) = -arcsinhD z := by
  rw [arcsinhD, arcsinhD, ← intervalIntegral.integral_neg]
  congr 1; funext s
  rw [mul_neg, neg_sq, neg_div]

/-- **DLMF 4.37.12**: `arctanh(−z) = −arctanh z` (`z ≠ ±1`; in Lean for all `z`). -/
theorem dlmf_4_37_12 (z : ℂ) : arctanhD (-z) = -arctanhD z := by
  rw [arctanhD, arctanhD, ← intervalIntegral.integral_neg]
  congr 1; funext s
  rw [mul_neg, neg_sq, neg_div]

/-- **DLMF 4.37.13**: `arccsch(−z) = −arccsch z`. -/
theorem dlmf_4_37_13 (z : ℂ) : arccschD (-z) = -arccschD z := by
  rw [arccschD, arccschD, one_div_neg_eq_neg_one_div, dlmf_4_37_10]

/-- **DLMF 4.37.15**: `arccoth(−z) = −arccoth z` (`z ≠ ±1`; in Lean for all `z`). -/
theorem dlmf_4_37_15 (z : ℂ) : arccothD (-z) = -arccothD z := by
  rw [arccothD, arccothD, one_div_neg_eq_neg_one_div, dlmf_4_37_12]

theorem log_neg_of_im_pos {u : ℂ} (hu : 0 < u.im) : log (-u) = log u - π * I := by
  apply Complex.ext
  · simp [log_re]
  · simp [log_im, arg_neg_eq_arg_sub_pi_of_im_pos hu]

theorem log_neg_of_im_neg {u : ℂ} (hu : u.im < 0) : log (-u) = log u + π * I := by
  apply Complex.ext
  · simp [log_re]
  · simp [log_im, arg_neg_eq_arg_add_pi_of_im_neg hu]

theorem cpow_half_neg_of_im_pos {u : ℂ} (hu : 0 < u.im) :
    (-u) ^ (1 / 2 : ℂ) = -I * u ^ (1 / 2 : ℂ) := by
  have hu0 : u ≠ 0 := fun h => by rw [h] at hu; simp at hu
  rw [cpow_half_eq_exp (neg_ne_zero.mpr hu0), cpow_half_eq_exp hu0, log_neg_of_im_pos hu,
    show (log u - π * I) * (1 / 2) = log u * (1 / 2) + (-(π / 2) : ℂ) * I by ring, exp_add,
    exp_mul_I, cos_neg, sin_neg, cos_pi_div_two, sin_pi_div_two]
  ring

theorem cpow_half_neg_of_im_neg {u : ℂ} (hu : u.im < 0) :
    (-u) ^ (1 / 2 : ℂ) = I * u ^ (1 / 2 : ℂ) := by
  have hu0 : u ≠ 0 := fun h => by rw [h] at hu; simp at hu
  rw [cpow_half_eq_exp (neg_ne_zero.mpr hu0), cpow_half_eq_exp hu0, log_neg_of_im_neg hu,
    show (log u + π * I) * (1 / 2) = log u * (1 / 2) + ((π / 2 : ℂ)) * I by ring, exp_add,
    exp_mul_I, cos_pi_div_two, sin_pi_div_two]
  ring

/-- Off the real axis, `coshRoot(−z) = −coshRoot z`. -/
theorem coshRoot_neg {z : ℂ} (hz : z.im ≠ 0) : coshRoot (-z) = -coshRoot z := by
  rw [coshRoot, coshRoot, show -z - 1 = -(z + 1) by ring, show -z + 1 = -(z - 1) by ring]
  rcases lt_or_gt_of_ne hz with h | h
  · rw [cpow_half_neg_of_im_neg (by simpa using h), cpow_half_neg_of_im_neg (by simpa using h)]
    ring_nf; rw [I_sq]; ring
  · rw [cpow_half_neg_of_im_pos (by simpa using h), cpow_half_neg_of_im_pos (by simpa using h)]
    ring_nf; rw [I_sq]; ring

/-- **DLMF 4.37.11**, corrected: `arccosh(−z) = ∓πi + arccosh z` for `ℑz ≷ 0`. -/
theorem dlmf_4_37_11 {z : ℂ} :
    (0 < z.im → arccoshD (-z) = -(π * I) + arccoshD z) ∧
      (z.im < 0 → arccoshD (-z) = π * I + arccoshD z) := by
  refine ⟨fun hz => ?_, fun hz => ?_⟩
  · have hc : (-z) ∈ arccoshCut := Or.inl (by simpa using hz.ne')
    rw [arccoshD_eq_log hc, arccoshD_eq_log (Or.inl hz.ne'), coshRoot_neg hz.ne',
      show -z + -coshRoot z = -(z + coshRoot z) by ring,
      log_neg_of_im_pos (by rw [add_im]; linarith [im_coshRoot_nonneg hz])]
    ring
  · have hc : (-z) ∈ arccoshCut := Or.inl (by simpa using hz.ne)
    rw [arccoshD_eq_log hc, arccoshD_eq_log (Or.inl hz.ne), coshRoot_neg hz.ne,
      show -z + -coshRoot z = -(z + coshRoot z) by ring,
      log_neg_of_im_neg (by rw [add_im]; linarith [im_coshRoot_nonpos hz])]
    ring

/-- **Erratum** (4.37.11): DLMF's "`arccosh(−z) = ±πi + arccosh z`, `ℑz ≷ 0`" has the signs
reversed: at `z = i`, `arccosh(−i) ≠ πi + arccosh i`. -/
theorem dlmf_4_37_11_erratum : arccoshD (-I) ≠ π * I + arccoshD I := by
  rw [(dlmf_4_37_11 (z := I)).1 (by simp)]
  intro h
  have := congrArg im h
  simp at this
  linarith [Real.pi_pos]

theorem im_one_div_neg_of_pos {z : ℂ} (hz : 0 < z.im) : (1 / z).im < 0 := by
  have hz0 : z ≠ 0 := fun h => by rw [h] at hz; simp at hz
  rw [one_div, inv_im]
  exact div_neg_of_neg_of_pos (by linarith) (normSq_pos.mpr hz0)

theorem im_one_div_pos_of_neg {z : ℂ} (hz : z.im < 0) : 0 < (1 / z).im := by
  have hz0 : z ≠ 0 := fun h => by rw [h] at hz; simp at hz
  rw [one_div, inv_im]
  exact div_pos (by linarith) (normSq_pos.mpr hz0)

/-- **DLMF 4.37.14**, corrected: `arcsech(−z) = ±πi + arcsech z` for `ℑz ≷ 0`. -/
theorem dlmf_4_37_14 {z : ℂ} :
    (0 < z.im → arcsechD (-z) = π * I + arcsechD z) ∧
      (z.im < 0 → arcsechD (-z) = -(π * I) + arcsechD z) := by
  refine ⟨fun hz => ?_, fun hz => ?_⟩
  · rw [arcsechD, arcsechD, one_div_neg_eq_neg_one_div]
    exact (dlmf_4_37_11 (z := 1 / z)).2 (im_one_div_neg_of_pos hz)
  · rw [arcsechD, arcsechD, one_div_neg_eq_neg_one_div]
    exact (dlmf_4_37_11 (z := 1 / z)).1 (im_one_div_pos_of_neg hz)

/-- **Erratum** (4.37.14): DLMF's "`arcsech(−z) = ∓πi + arcsech z`, `ℑz ≷ 0`" has the signs
reversed: at `z = i`, `arcsech(−i) ≠ −πi + arcsech i`. -/
theorem dlmf_4_37_14_erratum : arcsechD (-I) ≠ -(π * I) + arcsechD I := by
  rw [(dlmf_4_37_14 (z := I)).1 (by simp)]
  intro h
  have := congrArg im h
  simp at this
  linarith [Real.pi_pos]

end Azurite.DLMF
