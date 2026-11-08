/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter4.Section23Gudermannian
import Azurite.DLMF.Chapter4.Section28

/-!
# Principal inverse hyperbolic functions (DLMF 4.37, for §4.29)

The graphs of §4.29 use the principal values of DLMF §4.37(ii). As for the inverse trigonometric
functions in §4.15, we define them from DLMF's integrals 4.37.1–4.37.3 along paths that do not
cross the cuts of Figure 4.37.1, and 4.37.7–4.37.9.

* `arcsinhD z = ∫₀^z dt/(1 + t²)^{1/2}` along `[0, z]`, cuts `(−i∞, −i]`, `[i, i∞)`
  (`arcsinhCut`). It is `−i arcsin(iz)` (`arcsinD_I_mul_arcsinhD`), so §4.15 transfers.
* `arctanhD z = ∫₀^z dt/(1 − t²)` along `[0, z]`, cuts `(−∞, −1]`, `[1, ∞)` (`arctanhCut`);
  `arctanD_I_mul_arctanhD`.
* `arccoshD z = ∫₁^z dt/(t² − 1)^{1/2}` along `[1, z]`, cut `(−∞, 1]` (`arccoshCut`). The
  branch of `(t² − 1)^{1/2}` that is principal on `(1, ∞)` and continuous off the cut is
  `coshRoot t = (t − 1)^{1/2}(t + 1)^{1/2}` (`coshRoot_sq`, `coshRoot_ofReal`).
* `arccschD`, `arcsechD`, `arccothD` via `1/z`.
-/

open Set Filter Topology Complex MeasureTheory
open scoped Real Interval

namespace Azurite.DLMF

/-! ### Cuts -/

/-- The cut plane of `arcsinh`: `ℂ` minus `(−i∞, −i]` and `[i, i∞)`. -/
def arcsinhCut : Set ℂ := {z | z.re ≠ 0 ∨ |z.im| < 1}

/-- The cut plane of `arctanh`: `ℂ` minus `(−∞, −1]` and `[1, ∞)`. -/
def arctanhCut : Set ℂ := {z | z.im ≠ 0 ∨ |z.re| < 1}

/-- The cut plane of `arccosh`: `ℂ` minus `(−∞, 1]`. -/
def arccoshCut : Set ℂ := {z | z.im ≠ 0 ∨ 1 < z.re}

theorem I_mul_mem_arcsinCut {z : ℂ} : I * z ∈ arcsinCut ↔ z ∈ arcsinhCut := by
  simp [arcsinCut, arcsinhCut]

theorem I_mul_mem_arctanCut {z : ℂ} : I * z ∈ arctanCut ↔ z ∈ arctanhCut := by
  simp [arctanCut, arctanhCut]

/-! ### Definitions -/

/-- **DLMF 4.37.1** (principal value): `arcsinh z = ∫₀^z dt/(1 + t²)^{1/2}` along `[0, z]`. -/
noncomputable def arcsinhD (z : ℂ) : ℂ := ∫ s in (0 : ℝ)..1, z / (1 + (s * z) ^ 2) ^ (1 / 2 : ℂ)

/-- **DLMF 4.37.3** (principal value): `arctanh z = ∫₀^z dt/(1 − t²)` along `[0, z]`. -/
noncomputable def arctanhD (z : ℂ) : ℂ := ∫ s in (0 : ℝ)..1, z / (1 - (s * z) ^ 2)

/-- The branch of `(t² − 1)^{1/2}` in 4.37.2: principal on `(1, ∞)`, continuous off `(−∞, 1]`. -/
noncomputable def coshRoot (t : ℂ) : ℂ := (t - 1) ^ (1 / 2 : ℂ) * (t + 1) ^ (1 / 2 : ℂ)

/-- **DLMF 4.37.2** (principal value): `arccosh z = ∫₁^z dt/(t² − 1)^{1/2}` along `[1, z]`. -/
noncomputable def arccoshD (z : ℂ) : ℂ := ∫ s in (0 : ℝ)..1, (z - 1) / coshRoot (1 + s * (z - 1))

/-- **DLMF 4.37.7**: `arccsch z = arcsinh(1/z)`. -/
noncomputable def arccschD (z : ℂ) : ℂ := arcsinhD (1 / z)

/-- **DLMF 4.37.8**: `arcsech z = arccosh(1/z)`. -/
noncomputable def arcsechD (z : ℂ) : ℂ := arccoshD (1 / z)

/-- **DLMF 4.37.9**: `arccoth z = arctanh(1/z)`. -/
noncomputable def arccothD (z : ℂ) : ℂ := arctanhD (1 / z)

/-! ### `arcsinh` and `arctanh` through `arcsin` and `arctan` -/

theorem arcsinD_I_mul_arcsinhD (z : ℂ) : arcsinD (I * z) = I * arcsinhD z := by
  rw [arcsinD, arcsinhD, ← intervalIntegral.integral_const_mul]
  congr 1; funext s
  rw [show (1 : ℂ) - (↑s * (I * z)) ^ 2 = 1 + (↑s * z) ^ 2 by ring_nf; rw [I_sq]; ring]
  ring

theorem arctanD_I_mul_arctanhD (z : ℂ) : arctanD (I * z) = I * arctanhD z := by
  rw [arctanD, arctanhD, ← intervalIntegral.integral_const_mul]
  congr 1; funext s
  rw [show (1 : ℂ) + (↑s * (I * z)) ^ 2 = 1 - (↑s * z) ^ 2 by ring_nf; rw [I_sq]; ring]
  ring

theorem neg_I_mul_I_mul (w : ℂ) : -I * (I * w) = w := by
  rw [← mul_assoc, neg_mul, I_mul_I]; ring

theorem arcsinhD_eq (z : ℂ) : arcsinhD z = -I * arcsinD (I * z) := by
  rw [arcsinD_I_mul_arcsinhD, neg_I_mul_I_mul]

theorem arctanhD_eq (z : ℂ) : arctanhD z = -I * arctanD (I * z) := by
  rw [arctanD_I_mul_arctanhD, neg_I_mul_I_mul]

theorem I_mul_neg_I_mul (w : ℂ) : I * (-I * w) = w := by
  rw [← mul_assoc, mul_neg, I_mul_I]; ring

/-- `sinh(arcsinh z) = z` off the cuts. -/
theorem sinh_arcsinhD {z : ℂ} (hz : z ∈ arcsinhCut) : sinh (arcsinhD z) = z := by
  rw [sinh_eq_neg_I_mul_sin, arcsinhD_eq, I_mul_neg_I_mul,
    (arcsinD_props (I_mul_mem_arcsinCut.mpr hz)).2.2.1, neg_I_mul_I_mul]

/-- `tanh(arctanh z) = z` off the cuts. -/
theorem tanh_arctanhD {z : ℂ} (hz : z ∈ arctanhCut) : tanh (arctanhD z) = z := by
  have hc := I_mul_mem_arctanCut.mpr hz
  have h1 : I * z ≠ I := fun h => by
    have : z = 1 := mul_left_cancel₀ I_ne_zero (h.trans (mul_one I).symm)
    rw [this] at hz; simp [arctanhCut] at hz
  have h2 : I * z ≠ -I := fun h => by
    have : z = -1 := mul_left_cancel₀ I_ne_zero (h.trans (by ring))
    rw [this] at hz; simp [arctanhCut] at hz
  rw [tanh_eq_neg_I_mul_tan, arctanhD_eq, I_mul_neg_I_mul, arctanD_eq hc, tan_arctan h1 h2,
    neg_I_mul_I_mul]

/-- `arcsinh` is holomorphic off the cuts: `(arcsinh z)′ = (1 + z²)^{−1/2}`. -/
theorem hasDerivAt_arcsinhD {z : ℂ} (hz : z ∈ arcsinhCut) :
    HasDerivAt arcsinhD ((1 + z ^ 2) ^ (1 / 2 : ℂ))⁻¹ z := by
  have h := ((hasStrictDerivAt_arcsinD (I_mul_mem_arcsinCut.mpr hz)).hasDerivAt.comp z
    ((hasDerivAt_id z).const_mul I)).const_mul (-I)
  have he : arcsinhD = fun z => -I * arcsinD (I * z) := funext arcsinhD_eq
  rw [he]
  convert h using 1
  · funext y; rfl
  rw [show (1 : ℂ) - (I * z) ^ 2 = 1 + z ^ 2 by ring_nf; rw [I_sq]; ring]
  linear_combination ((1 + z ^ 2) ^ (1 / 2 : ℂ))⁻¹ * I_sq

/-! ### Real arguments -/

/-- `arcsinh x = Real.arsinh x` for real `x` (the real axis is off the cuts). -/
theorem arcsinhD_ofReal (x : ℝ) : arcsinhD x = Real.arsinh x := by
  have hd : ∀ s ∈ [[(0 : ℝ), 1]], HasDerivAt (fun s => Real.arsinh (s * x))
      (x / √(1 + (s * x) ^ 2)) s := by
    intro s _
    refine (hasDerivAt_mul_const (x := s) x).arsinh.congr_deriv ?_
    rw [smul_eq_mul]
    field_simp
  have hc : Continuous fun s : ℝ => x / √(1 + (s * x) ^ 2) :=
    continuous_const.div (by fun_prop) fun s => (Real.sqrt_pos.mpr (by positivity)).ne'
  have hI := intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hc.intervalIntegrable _ _)
  simp only [one_mul, zero_mul, Real.arsinh_zero, sub_zero] at hI
  rw [arcsinhD, ← hI, ← intervalIntegral.integral_ofReal]
  refine intervalIntegral.integral_congr fun s _ => ?_
  have hp : 0 ≤ 1 + (s * x) ^ 2 := by positivity
  rw [show (1 : ℂ) + (↑s * ↑x) ^ 2 = ((1 + (s * x) ^ 2 : ℝ) : ℂ) by push_cast; ring,
    show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring, ← ofReal_cpow hp,
    ← Real.sqrt_eq_rpow]
  push_cast
  ring

/-- `arctanh x = Real.artanh x` for `−1 < x < 1`. -/
theorem arctanhD_ofReal {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) : arctanhD x = Real.artanh x := by
  have hs : ∀ s ∈ [[(0 : ℝ), 1]], s * x ∈ Ioo (-1 : ℝ) 1 := by
    intro s hs
    rw [Set.uIcc_of_le zero_le_one] at hs
    constructor <;> nlinarith [hs.1, hs.2, hx.1, hx.2]
  have hd : ∀ s ∈ [[(0 : ℝ), 1]], HasDerivAt
      (fun s => 1 / 2 * (Real.log (1 + s * x) - Real.log (1 - s * x)))
      (x / (1 - (s * x) ^ 2)) s := by
    intro s hs'
    obtain ⟨h1, h2⟩ := hs s hs'
    have h1' : (1 + s * x) ≠ 0 := by linarith
    have h2' : (1 - s * x) ≠ 0 := by linarith
    have hl := (hasDerivAt_id s).mul_const x
    have := ((hl.const_add 1).log h1').sub ((hl.const_sub 1).log h2')
    have h3 : 1 - (s * x) ^ 2 ≠ 0 := by
      rw [show 1 - (s * x) ^ 2 = (1 - s * x) * (1 + s * x) by ring]; exact mul_ne_zero h2' h1'
    refine (this.const_mul (1 / 2)).congr_deriv ?_
    have h4 : 1 + x * s ≠ 0 := by rw [mul_comm]; exact h1'
    have h5 : 1 - x * s ≠ 0 := by rw [mul_comm]; exact h2'
    have h6 : 1 - x ^ 2 * s ^ 2 ≠ 0 := by rw [← mul_pow, mul_comm]; exact h3
    simp only [id, one_mul]
    field_simp
    ring
  have hint : IntervalIntegrable (fun s : ℝ => x / (1 - (s * x) ^ 2)) volume 0 1 := by
    refine ContinuousOn.intervalIntegrable ?_
    refine continuousOn_const.div (by fun_prop) fun s hs' => ?_
    obtain ⟨h1, h2⟩ := hs s hs'
    nlinarith
  have hI := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hint
  simp only [one_mul, zero_mul, add_zero, sub_zero, Real.log_one, sub_self, mul_zero] at hI
  rw [arctanhD, Real.artanh_eq_half_log ⟨hx.1.le, hx.2.le⟩,
    Real.log_div (by linarith [hx.1]) (by linarith [hx.2]), ← hI,
    ← intervalIntegral.integral_ofReal]
  refine intervalIntegral.integral_congr fun s _ => ?_
  push_cast
  ring

/-! ### The branch `coshRoot` and the closed form of `arccosh` -/

theorem sqrt_half_sq (w : ℂ) : (w ^ (1 / 2 : ℂ)) ^ 2 = w := by
  rw [one_div, cpow_ofNat_inv_pow]

theorem coshRoot_sq (t : ℂ) : coshRoot t ^ 2 = t ^ 2 - 1 := by
  rw [coshRoot, mul_pow, sqrt_half_sq, sqrt_half_sq]; ring

theorem ofReal_cpow_half {x : ℝ} (hx : 0 ≤ x) : (x : ℂ) ^ (1 / 2 : ℂ) = (√x : ℝ) := by
  rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring, ← ofReal_cpow hx,
    Real.sqrt_eq_rpow]

/-- On `[1, ∞)`, `coshRoot` is the principal `(t² − 1)^{1/2}`. -/
theorem coshRoot_ofReal {x : ℝ} (hx : 1 ≤ x) :
    coshRoot x = (√(x ^ 2 - 1) : ℝ) ∧ ((x : ℂ) ^ 2 - 1) ^ (1 / 2 : ℂ) = (√(x ^ 2 - 1) : ℝ) := by
  have h1 : (x : ℂ) - 1 = ((x - 1 : ℝ) : ℂ) := by push_cast; ring
  have h2 : (x : ℂ) + 1 = ((x + 1 : ℝ) : ℂ) := by push_cast; ring
  have h3 : (x : ℂ) ^ 2 - 1 = ((x ^ 2 - 1 : ℝ) : ℂ) := by push_cast; ring
  refine ⟨?_, by rw [h3, ofReal_cpow_half (by nlinarith)]⟩
  rw [coshRoot, h1, h2, ofReal_cpow_half (by linarith), ofReal_cpow_half (by linarith),
    ← ofReal_mul, ← Real.sqrt_mul (by linarith)]
  congr 2; ring

theorem sub_one_mem_slitPlane {t : ℂ} (ht : t ∈ arccoshCut) : t - 1 ∈ slitPlane := by
  rw [mem_slitPlane_iff]
  rcases ht with h | h
  · right; simpa using h
  · left; simp; linarith

theorem add_one_mem_slitPlane {t : ℂ} (ht : t ∈ arccoshCut) : t + 1 ∈ slitPlane := by
  rw [mem_slitPlane_iff]
  rcases ht with h | h
  · right; simpa using h
  · left; simp; linarith

theorem coshRoot_ne_zero {t : ℂ} (ht : t ∈ arccoshCut) : coshRoot t ≠ 0 := by
  rw [coshRoot]
  exact mul_ne_zero (cpow_ne_zero_iff.mpr (Or.inl (slitPlane_ne_zero (sub_one_mem_slitPlane ht))))
    (cpow_ne_zero_iff.mpr (Or.inl (slitPlane_ne_zero (add_one_mem_slitPlane ht))))

theorem hasDerivAt_sqrt_half {w : ℂ} (hw : w ∈ slitPlane) :
    HasDerivAt (fun w => w ^ (1 / 2 : ℂ)) (w ^ (1 / 2 : ℂ) / (2 * w)) w := by
  have h := (hasDerivAt_id w).cpow_const (c := (1 / 2 : ℂ)) hw
  refine h.congr_deriv ?_
  have hw0 := slitPlane_ne_zero hw
  simp only [id, mul_one]
  rw [cpow_sub _ _ hw0, cpow_one]
  field_simp

/-- `coshRoot′ = t/coshRoot` off the cut. -/
theorem hasDerivAt_coshRoot {t : ℂ} (ht : t ∈ arccoshCut) :
    HasDerivAt coshRoot (t / coshRoot t) t := by
  have h1 := sub_one_mem_slitPlane ht
  have h2 := add_one_mem_slitPlane ht
  have ha := (hasDerivAt_sqrt_half h1).comp t ((hasDerivAt_id t).sub_const 1)
  have hb := (hasDerivAt_sqrt_half h2).comp t ((hasDerivAt_id t).add_const 1)
  have h := ha.mul hb
  have hq := coshRoot_ne_zero ht
  refine h.congr_deriv ?_
  have e1 := slitPlane_ne_zero h1
  have e2 := slitPlane_ne_zero h2
  have hq' : (t - 1) ^ (1 / 2 : ℂ) * (t + 1) ^ (1 / 2 : ℂ) ≠ 0 := hq
  have ha2 := sqrt_half_sq (t - 1)
  have hb2 := sqrt_half_sq (t + 1)
  simp only [Function.comp_apply, id, mul_one, coshRoot]
  set a := (t - 1) ^ (1 / 2 : ℂ)
  set b := (t + 1) ^ (1 / 2 : ℂ)
  have ha0 : a ≠ 0 := left_ne_zero_of_mul hq'
  have hb0 : b ≠ 0 := right_ne_zero_of_mul hq'
  rw [← ha2, ← hb2]
  field_simp
  linear_combination ha2 + hb2

theorem isOpen_arccoshCut : IsOpen arccoshCut :=
  (isOpen_ne_fun continuous_im continuous_const).union (isOpen_lt continuous_const continuous_re)

/-- `(t + coshRoot t)(t − coshRoot t) = 1`. -/
theorem add_coshRoot_mul_sub (t : ℂ) : (t + coshRoot t) * (t - coshRoot t) = 1 := by
  linear_combination -coshRoot_sq t

/-- Off the cut, `t + coshRoot t` lies off the cut of `ln`. -/
theorem add_coshRoot_mem_slitPlane {t : ℂ} (ht : t ∈ arccoshCut) :
    t + coshRoot t ∈ slitPlane := by
  set w := t + coshRoot t
  have hw := add_coshRoot_mul_sub t
  have hw0 : w ≠ 0 := left_ne_zero_of_mul_eq_one hw
  rw [mem_slitPlane_iff]
  by_contra h
  push Not at h
  obtain ⟨hre, him⟩ := h
  have hr : w = (w.re : ℂ) := Complex.ext (by simp) (by simp [him])
  have hr0 : w.re ≠ 0 := fun h0 => hw0 (by rw [hr, h0, ofReal_zero])
  have hneg : w.re < 0 := lt_of_le_of_ne hre hr0
  have ht2 : 2 * t = w + w⁻¹ := by
    have : t - coshRoot t = w⁻¹ := by rw [eq_inv_of_mul_eq_one_right hw]
    linear_combination this
  have ht' : t = ((w.re + w.re⁻¹) / 2 : ℝ) := by
    have : t = (w + w⁻¹) / 2 := by linear_combination ht2 / 2
    obtain ⟨r, hrr⟩ : ∃ r, r = w.re := ⟨_, rfl⟩
    rw [← hrr] at hr ⊢
    rw [this, hr]; push_cast; ring
  have hle : (w.re + w.re⁻¹) / 2 ≤ -1 := by
    have : w.re + w.re⁻¹ + 2 = (w.re + 1) ^ 2 / w.re := by field_simp; ring
    have : (w.re + 1) ^ 2 / w.re ≤ 0 := div_nonpos_of_nonneg_of_nonpos (sq_nonneg _) hneg.le
    linarith
  rw [ht'] at ht
  rcases ht with h | h
  · exact h (ofReal_im _)
  · rw [ofReal_re] at h; linarith

theorem hasDerivAt_log_add_coshRoot {t : ℂ} (ht : t ∈ arccoshCut) :
    HasDerivAt (fun t => log (t + coshRoot t)) (1 / coshRoot t) t := by
  have hq := coshRoot_ne_zero ht
  have hw := add_coshRoot_mem_slitPlane ht
  have hw0 := slitPlane_ne_zero hw
  refine (((hasDerivAt_id t).add (hasDerivAt_coshRoot ht)).clog hw).congr_deriv ?_
  simp only [Pi.add_apply, id]
  field_simp
  ring

/-- Points of the segment `[1, z]` other than `1` are off the cut. -/
theorem seg_mem_arccoshCut {z : ℂ} (hz : z ∈ arccoshCut) {s : ℝ} (hs : 0 < s) :
    1 + (s : ℂ) * (z - 1) ∈ arccoshCut := by
  rcases hz with h | h
  · left; simp [hs.ne', h]
  · right; simp; nlinarith

theorem continuousAt_coshRoot_one : ContinuousAt coshRoot 1 := by
  have h1 : ContinuousAt (fun t : ℂ => (t - 1) ^ (1 / 2 : ℂ)) 1 :=
    (continuousAt_cpow_const_of_re_pos (Or.inl (by simp)) (by norm_num)).comp
      (continuousAt_id.sub continuousAt_const)
  have h2 : ContinuousAt (fun t : ℂ => (t + 1) ^ (1 / 2 : ℂ)) 1 :=
    (continuousAt_cpow_const_of_re_pos (Or.inl (by norm_num)) (by norm_num)).comp
      (continuousAt_id.add continuousAt_const)
  exact h1.mul h2

theorem coshRoot_one : coshRoot 1 = 0 := by
  simp [coshRoot]

theorem norm_cpow_half (w : ℂ) : ‖w ^ (1 / 2 : ℂ)‖ = ‖w‖ ^ (1 / 2 : ℝ) := by
  rcases eq_or_ne w 0 with rfl | hw
  · simp
  · rw [norm_cpow_of_ne_zero hw]; simp

/-- **DLMF 4.37.2**, principal value in closed form: `arccosh z = ln(z + (z² − 1)^{1/2})` with the
branch `coshRoot`, off the cut `(−∞, 1]`. -/
theorem arccoshD_eq_log {z : ℂ} (hz : z ∈ arccoshCut) : arccoshD z = log (z + coshRoot z) := by
  set T : ℝ → ℂ := fun s => 1 + (s : ℂ) * (z - 1) with hT
  set φ : ℝ → ℂ := fun s => log (T s + coshRoot (T s)) with hφ
  have hTd : ∀ s : ℝ, HasDerivAt T (z - 1) s := fun s => by
    have := ((hasDerivAt_id s).ofReal_comp.mul_const (z - 1)).const_add 1
    simp only [id, ofReal_one, one_mul] at this
    exact this
  have hcontF : ∀ s ∈ Icc (0 : ℝ) 1,
      ContinuousAt (fun t => log (t + coshRoot t)) (T s) := by
    intro s hs
    rcases hs.1.eq_or_lt with h | h
    · subst h
      simp only [hT, ofReal_zero, zero_mul, add_zero]
      refine (continuousAt_clog ?_).comp (continuousAt_id.add continuousAt_coshRoot_one)
      simp [coshRoot_one]
    · exact (hasDerivAt_log_add_coshRoot (seg_mem_arccoshCut hz h)).continuousAt
  have hcont : ContinuousOn φ (Icc 0 1) := fun s hs =>
    ((hcontF s hs).comp (hTd s).continuousAt).continuousWithinAt
  have hderiv : ∀ s ∈ Ioo (0 : ℝ) 1, HasDerivAt φ ((z - 1) / coshRoot (T s)) s := by
    intro s hs
    have h := (hasDerivAt_log_add_coshRoot (seg_mem_arccoshCut hz hs.1)).comp s (hTd s)
    refine h.congr_deriv ?_
    ring
  -- integrability: `‖(z − 1)/coshRoot(T s)‖ ≤ C s^{−1/2}`
  have hz1 : z - 1 ≠ 0 := slitPlane_ne_zero (sub_one_mem_slitPlane hz)
  have hTp : ∀ s ∈ Icc (0 : ℝ) 1, T s + 1 ≠ 0 := by
    intro s hs
    rcases hs.1.eq_or_lt with h | h
    · subst h; simp [hT]
    · exact slitPlane_ne_zero (add_one_mem_slitPlane (seg_mem_arccoshCut hz h))
  have hTc : Continuous T := by rw [hT]; fun_prop
  obtain ⟨s₀, hs₀, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr zero_le_one)
    ((hTc.add continuous_const).norm.continuousOn)
  obtain ⟨m, hm⟩ : ∃ m, m = ‖T s₀ + 1‖ := ⟨_, rfl⟩
  have hm0 : 0 < m := by rw [hm]; exact norm_pos_iff.mpr (hTp s₀ hs₀)
  have hmle : ∀ s ∈ Icc (0 : ℝ) 1, m ≤ ‖T s + 1‖ := fun s hs => by rw [hm]; exact hmin hs
  obtain ⟨c, hc⟩ : ∃ c, c = ‖z - 1‖ := ⟨_, rfl⟩
  have hc0 : 0 < c := by rw [hc]; exact norm_pos_iff.mpr hz1
  obtain ⟨C, hC⟩ : ∃ C, C = c / (c ^ (1 / 2 : ℝ) * m ^ (1 / 2 : ℝ)) := ⟨_, rfl⟩
  have hbound : ∀ s ∈ Ioc (0 : ℝ) 1,
      ‖(z - 1) / coshRoot (T s)‖ ≤ C * s ^ (-(1 / 2) : ℝ) := by
    intro s hs
    have hs1 : T s - 1 = (s : ℂ) * (z - 1) := by simp [hT]
    have hN := hmle s ⟨hs.1.le, hs.2⟩
    rw [norm_div, coshRoot, norm_mul, norm_cpow_half, norm_cpow_half, hs1, norm_mul,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs.1, ← hc,
      Real.mul_rpow hs.1.le hc0.le, Real.rpow_neg hs.1.le]
    have h1 : 0 < s ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hs.1 _
    have h2 : 0 < c ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hc0 _
    have h3 : 0 < m ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hm0 _
    have h4 : m ^ (1 / 2 : ℝ) ≤ ‖T s + 1‖ ^ (1 / 2 : ℝ) :=
      Real.rpow_le_rpow hm0.le hN (by norm_num)
    rw [show C * (s ^ (1 / 2 : ℝ))⁻¹ = c / (s ^ (1 / 2 : ℝ) * c ^ (1 / 2 : ℝ) * m ^ (1 / 2 : ℝ))
      by rw [hC]; field_simp]
    apply div_le_div_of_nonneg_left hc0.le (by positivity)
    exact mul_le_mul_of_nonneg_left h4 (by positivity)
  have hint : IntervalIntegrable (fun s => (z - 1) / coshRoot (T s)) volume 0 1 := by
    refine IntervalIntegrable.mono_fun'
      ((intervalIntegral.intervalIntegrable_rpow' (by norm_num : (-1 : ℝ) < -(1 / 2))).const_mul
        C) ?_ ?_
    · rw [uIoc_of_le zero_le_one]
      refine ContinuousOn.aestronglyMeasurable (fun s hs => ?_) measurableSet_Ioc
      have hm' := seg_mem_arccoshCut hz hs.1
      have hcomp : ContinuousAt (fun s => coshRoot (T s)) s :=
        ContinuousAt.comp (f := T) (g := coshRoot) (hasDerivAt_coshRoot hm').continuousAt
          (hTd s).continuousAt
      exact (continuousAt_const.div hcomp (coshRoot_ne_zero hm')).continuousWithinAt
    · rw [uIoc_of_le zero_le_one]
      exact ae_restrict_of_forall_mem measurableSet_Ioc hbound
  have hI := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le zero_le_one hcont hderiv hint
  show ∫ s in (0 : ℝ)..1, (z - 1) / coshRoot (T s) = _
  rw [hI]
  simp [hφ, hT, coshRoot_one]

/-- `cosh(arccosh z) = z` off the cut. -/
theorem cosh_arccoshD {z : ℂ} (hz : z ∈ arccoshCut) : cosh (arccoshD z) = z := by
  have hw := add_coshRoot_mem_slitPlane hz
  have hw0 := slitPlane_ne_zero hw
  have hinv : (z + coshRoot z)⁻¹ = z - coshRoot z :=
    (eq_inv_of_mul_eq_one_right (add_coshRoot_mul_sub z)).symm
  rw [arccoshD_eq_log hz, cosh, exp_log hw0, exp_neg, exp_log hw0, hinv]
  ring

/-- `arccosh` is holomorphic off the cut, with derivative `1/(z² − 1)^{1/2}` (branch
`coshRoot`). -/
theorem hasDerivAt_arccoshD {z : ℂ} (hz : z ∈ arccoshCut) :
    HasDerivAt arccoshD (1 / coshRoot z) z :=
  (hasDerivAt_log_add_coshRoot hz).congr_of_eventuallyEq
    (eventually_of_mem (isOpen_arccoshCut.mem_nhds hz) fun _ hy => arccoshD_eq_log hy)

/-- `arccosh x = Real.arcosh x` for `x ≥ 1`. -/
theorem arccoshD_ofReal {x : ℝ} (hx : 1 ≤ x) : arccoshD x = Real.arcosh x := by
  rcases hx.eq_or_lt with h | h
  · subst h
    simp [arccoshD, Real.arcosh]
  have hz : (x : ℂ) ∈ arccoshCut := Or.inr (by simpa using h)
  have hp : 0 < x + √(x ^ 2 - 1) := by positivity
  rw [arccoshD_eq_log hz, (coshRoot_ofReal hx).1, ← ofReal_add, ← ofReal_log hp.le, Real.arcosh]

/-! ### One-sided limits on the cuts -/

theorem mem_arccoshCut_of_im_ne {z : ℂ} (hz : z.im ≠ 0) : z ∈ arccoshCut := Or.inl hz

theorem re_neg_im_zero_of_not_mem_slitPlane {w : ℂ} (hw : w ≠ 0) (hs : w ∉ slitPlane) :
    w.re < 0 ∧ w.im = 0 := by
  rw [mem_slitPlane_iff, not_or, not_lt, not_not] at hs
  refine ⟨lt_of_le_of_ne hs.1 fun h => hw ?_, hs.2⟩
  apply Complex.ext
  · rw [h, zero_re]
  · rw [hs.2, zero_im]

/-- The limit of `ln` at `w₀ ≠ 0` from the upper half-plane exists. -/
theorem exists_tendsto_log_upper {w₀ : ℂ} (hw : w₀ ≠ 0) :
    ∃ c, Tendsto log (𝓝[{w | 0 < w.im}] w₀) (𝓝 c) := by
  by_cases hs : w₀ ∈ slitPlane
  · exact ⟨_, (continuousAt_clog hs).tendsto.mono_left nhdsWithin_le_nhds⟩
  obtain ⟨hre, him⟩ := re_neg_im_zero_of_not_mem_slitPlane hw hs
  have hsub : {w : ℂ | 0 < w.im} ⊆ {w : ℂ | 0 ≤ w.im} :=
    ofPred_subset_ofPred.mpr fun _ h => h.le
  exact ⟨_, ((continuousWithinAt_log_of_re_neg_of_im_zero hre him).mono hsub).tendsto⟩

/-- The limit of `ln` at `w₀ ≠ 0` from the lower half-plane exists. -/
theorem exists_tendsto_log_lower {w₀ : ℂ} (hw : w₀ ≠ 0) :
    ∃ c, Tendsto log (𝓝[{w | w.im < 0}] w₀) (𝓝 c) := by
  by_cases hs : w₀ ∈ slitPlane
  · exact ⟨_, (continuousAt_clog hs).tendsto.mono_left nhdsWithin_le_nhds⟩
  obtain ⟨hre, him⟩ := re_neg_im_zero_of_not_mem_slitPlane hw hs
  exact ⟨_, tendsto_log_nhdsWithin_im_neg_of_re_neg_of_im_zero hre him⟩

theorem cpow_half_eq_exp {w : ℂ} (hw : w ≠ 0) : w ^ (1 / 2 : ℂ) = exp (log w * (1 / 2)) :=
  cpow_def_of_ne_zero hw _

/-- The limit of `w^{1/2}` at any real `a` from either half-plane exists. -/
theorem exists_tendsto_sqrt_side (a : ℝ) :
    (∃ c, Tendsto (fun w : ℂ => w ^ (1 / 2 : ℂ)) (𝓝[{w | 0 < w.im}] (a : ℂ)) (𝓝 c)) ∧
      ∃ c, Tendsto (fun w : ℂ => w ^ (1 / 2 : ℂ)) (𝓝[{w | w.im < 0}] (a : ℂ)) (𝓝 c) := by
  rcases eq_or_ne a 0 with rfl | ha
  · have h := (continuousAt_cpow_const_of_re_pos (z := ((0 : ℝ) : ℂ)) (w := (1 / 2 : ℂ))
      (Or.inl (by simp)) (by norm_num)).tendsto
    exact ⟨⟨_, h.mono_left nhdsWithin_le_nhds⟩, ⟨_, h.mono_left nhdsWithin_le_nhds⟩⟩
  have ha' : (a : ℂ) ≠ 0 := ofReal_ne_zero.mpr ha
  obtain ⟨c₁, h₁⟩ := exists_tendsto_log_upper ha'
  obtain ⟨c₂, h₂⟩ := exists_tendsto_log_lower ha'
  refine ⟨⟨exp (c₁ * (1 / 2)), ?_⟩, ⟨exp (c₂ * (1 / 2)), ?_⟩⟩
  · refine ((continuous_exp.tendsto _).comp (h₁.mul_const _)).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with w hw
    exact (cpow_half_eq_exp fun h => by rw [h] at hw; simp at hw).symm
  · refine ((continuous_exp.tendsto _).comp (h₂.mul_const _)).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with w hw
    exact (cpow_half_eq_exp fun h => by rw [h] at hw; simp at hw).symm

/-- Shifting by a real constant preserves the half-planes. -/
theorem tendsto_add_real_side (x b : ℝ) :
    Tendsto (fun z : ℂ => z + b) (𝓝[{w | 0 < w.im}] (x : ℂ)) (𝓝[{w | 0 < w.im}] ((x + b : ℝ) : ℂ)) ∧
      Tendsto (fun z : ℂ => z + b) (𝓝[{w | w.im < 0}] (x : ℂ))
        (𝓝[{w | w.im < 0}] ((x + b : ℝ) : ℂ)) := by
  have hc : Tendsto (fun z : ℂ => z + b) (𝓝 (x : ℂ)) (𝓝 ((x + b : ℝ) : ℂ)) := by
    have : Continuous fun z : ℂ => z + b := by fun_prop
    simpa using this.tendsto (x : ℂ)
  refine ⟨tendsto_nhdsWithin_iff.mpr ⟨hc.mono_left nhdsWithin_le_nhds, ?_⟩,
    tendsto_nhdsWithin_iff.mpr ⟨hc.mono_left nhdsWithin_le_nhds, ?_⟩⟩ <;>
  · filter_upwards [self_mem_nhdsWithin] with w hw
    simpa using hw

theorem im_coshRoot {z : ℂ} (h1 : z - 1 ≠ 0) (h2 : z + 1 ≠ 0) :
    (coshRoot z).im = Real.exp ((log (z - 1) * (1 / 2) + log (z + 1) * (1 / 2)).re) *
      Real.sin ((arg (z - 1) + arg (z + 1)) / 2) := by
  rw [coshRoot, cpow_half_eq_exp h1, cpow_half_eq_exp h2, ← exp_add, exp_im]
  congr 2
  simp [log_im]
  ring

theorem im_coshRoot_nonneg {z : ℂ} (hz : 0 < z.im) : 0 ≤ (coshRoot z).im := by
  have h1 : z - 1 ≠ 0 := fun h => by have := congrArg im h; simp at this; linarith
  have h2 : z + 1 ≠ 0 := fun h => by have := congrArg im h; simp at this; linarith
  rw [im_coshRoot h1 h2]
  have a1 : 0 ≤ arg (z - 1) := arg_nonneg_iff.mpr (by simp; linarith)
  have a2 : 0 ≤ arg (z + 1) := arg_nonneg_iff.mpr (by simp; linarith)
  have b1 := arg_le_pi (z - 1)
  have b2 := arg_le_pi (z + 1)
  exact mul_nonneg (Real.exp_pos _).le
    (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith))

theorem im_coshRoot_nonpos {z : ℂ} (hz : z.im < 0) : (coshRoot z).im ≤ 0 := by
  have h1 : z - 1 ≠ 0 := fun h => by have := congrArg im h; simp at this; linarith
  have h2 : z + 1 ≠ 0 := fun h => by have := congrArg im h; simp at this; linarith
  rw [im_coshRoot h1 h2]
  have a1 : arg (z - 1) < 0 := arg_neg_iff.mpr (by simp; linarith)
  have a2 : arg (z + 1) < 0 := arg_neg_iff.mpr (by simp; linarith)
  have b1 := neg_pi_lt_arg (z - 1)
  have b2 := neg_pi_lt_arg (z + 1)
  exact mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le
    (Real.sin_nonpos_of_nonpos_of_neg_pi_le (by linarith) (by linarith))

/-- If `G ∘ F = id` near `x` along `l` and `F → L`, with `G` continuous at `L`, then `G L = x`. -/
theorem apply_eq_of_tendsto {F G : ℂ → ℂ} {l : Filter ℂ} [l.NeBot] {x L : ℂ} (hl : l ≤ 𝓝 x)
    (hF : Tendsto F l (𝓝 L)) (hG : ContinuousAt G L) (hGF : ∀ᶠ z in l, G (F z) = z) :
    G L = x :=
  tendsto_nhds_unique (hG.tendsto.comp hF)
    ((tendsto_id.mono_left hl).congr' (hGF.mono fun _ h => h.symm))

theorem eq_ofReal_re_of_im_eq_zero {L : ℂ} (h : L.im = 0) : L = (L.re : ℂ) :=
  Complex.ext (by simp) (by simp [h])

/-- On its cut `(−∞, 1)`, `arccosh` has limits from above and below, both nonreal ("`arccosh x`
is complex when `x < 1`"). -/
theorem arccoshD_cut_limits {x : ℝ} (hx : x < 1) :
    ∃ b c : ℂ, b.im ≠ 0 ∧ c.im ≠ 0 ∧ Tendsto arccoshD (𝓝[{w | 0 < w.im}] (x : ℂ)) (𝓝 b) ∧
      Tendsto arccoshD (𝓝[{w | w.im < 0}] (x : ℂ)) (𝓝 c) := by
  obtain ⟨⟨a₁, ha₁⟩, ⟨a₁', ha₁'⟩⟩ := exists_tendsto_sqrt_side (x + -1)
  obtain ⟨⟨a₂, ha₂⟩, ⟨a₂', ha₂'⟩⟩ := exists_tendsto_sqrt_side (x + 1)
  obtain ⟨s₁, s₁'⟩ := tendsto_add_real_side x (-1)
  obtain ⟨s₂, s₂'⟩ := tendsto_add_real_side x 1
  have e1 : ∀ z : ℂ, z + ((-1 : ℝ) : ℂ) = z - 1 := fun z => by push_cast; ring
  have e2 : ∀ z : ℂ, z + ((1 : ℝ) : ℂ) = z + 1 := fun z => by push_cast; ring
  have hcosh : ∀ L : ℂ, cosh L = x → L.im ≠ 0 := fun L hL him => by
    rw [eq_ofReal_re_of_im_eq_zero him, ← ofReal_cosh, ofReal_inj] at hL
    linarith [Real.one_le_cosh L.re]
  have hid : ∀ S : Set ℂ, Tendsto (fun z : ℂ => z) (𝓝[S] (x : ℂ)) (𝓝 (x : ℂ)) :=
    fun S => tendsto_id.mono_left nhdsWithin_le_nhds
  have hw0 : ∀ (S : Set ℂ) [(𝓝[S] (x : ℂ)).NeBot] (q : ℂ),
      Tendsto coshRoot (𝓝[S] (x : ℂ)) (𝓝 q) → (x : ℂ) + q ≠ 0 := by
    intro S _ q hq
    have h1 := ((hid S).add hq).mul ((hid S).sub hq)
    have h2 : (fun z => (z + coshRoot z) * (z - coshRoot z)) = fun _ => (1 : ℂ) :=
      funext add_coshRoot_mul_sub
    rw [h2] at h1
    exact left_ne_zero_of_mul_eq_one (tendsto_nhds_unique h1 tendsto_const_nhds)
  have hcoshEv : ∀ S : Set ℂ, (∀ z ∈ S, z.im ≠ 0) →
      ∀ᶠ z in 𝓝[S] (x : ℂ), cosh (arccoshD z) = z := fun S hS => by
    filter_upwards [self_mem_nhdsWithin] with z hz
    exact cosh_arccoshD (Or.inl (hS z hz))
  have hlogEv : ∀ S : Set ℂ, (∀ z ∈ S, z.im ≠ 0) →
      (fun z => log (z + coshRoot z)) =ᶠ[𝓝[S] (x : ℂ)] arccoshD := fun S hS => by
    filter_upwards [self_mem_nhdsWithin] with z hz
    exact (arccoshD_eq_log (Or.inl (hS z hz))).symm
  -- above
  have hq₁ : Tendsto coshRoot (𝓝[{w | 0 < w.im}] (x : ℂ)) (𝓝 (a₁ * a₂)) := by
    refine ((ha₁.comp s₁).mul (ha₂.comp s₂)).congr fun z => ?_
    simp only [Function.comp_apply, e1, e2, coshRoot]
  have := neBot_upper x
  have hS₁ : ∀ z ∈ {w : ℂ | 0 < w.im}, z.im ≠ 0 := fun z hz => ne_of_gt hz
  have hW₁ : Tendsto (fun z => z + coshRoot z) (𝓝[{w | 0 < w.im}] (x : ℂ))
      (𝓝[{w | 0 < w.im}] ((x : ℂ) + a₁ * a₂)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨(hid _).add hq₁, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with z hz
    have hz' : 0 < z.im := hz
    show 0 < (z + coshRoot z).im
    rw [add_im]; linarith [im_coshRoot_nonneg hz']
  obtain ⟨c₁, hc₁⟩ := exists_tendsto_log_upper (hw0 _ _ hq₁)
  have hb := (hc₁.comp hW₁).congr' (hlogEv _ hS₁)
  -- below
  have hq₂ : Tendsto coshRoot (𝓝[{w | w.im < 0}] (x : ℂ)) (𝓝 (a₁' * a₂')) := by
    refine ((ha₁'.comp s₁').mul (ha₂'.comp s₂')).congr fun z => ?_
    simp only [Function.comp_apply, e1, e2, coshRoot]
  have := neBot_lower x
  have hS₂ : ∀ z ∈ {w : ℂ | w.im < 0}, z.im ≠ 0 := fun z hz => ne_of_lt hz
  have hW₂ : Tendsto (fun z => z + coshRoot z) (𝓝[{w | w.im < 0}] (x : ℂ))
      (𝓝[{w | w.im < 0}] ((x : ℂ) + a₁' * a₂')) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨(hid _).add hq₂, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with z hz
    have hz' : z.im < 0 := hz
    show (z + coshRoot z).im < 0
    rw [add_im]; linarith [im_coshRoot_nonpos hz']
  obtain ⟨c₂, hc₂⟩ := exists_tendsto_log_lower (hw0 _ _ hq₂)
  have hc := (hc₂.comp hW₂).congr' (hlogEv _ hS₂)
  exact ⟨c₁, c₂,
    hcosh _ (apply_eq_of_tendsto nhdsWithin_le_nhds hb continuous_cosh.continuousAt
      (hcoshEv _ hS₁)),
    hcosh _ (apply_eq_of_tendsto nhdsWithin_le_nhds hc continuous_cosh.continuousAt
      (hcoshEv _ hS₂)), hb, hc⟩

theorem tendsto_I_mul_side (x : ℝ) :
    Tendsto (fun z : ℂ => I * z) (𝓝[{w | 0 < w.im}] (x : ℂ)) (𝓝[{z | z.re < 0}] ((x : ℂ) * I)) ∧
      Tendsto (fun z : ℂ => I * z) (𝓝[{w | w.im < 0}] (x : ℂ))
        (𝓝[{z | 0 < z.re}] ((x : ℂ) * I)) := by
  have hI : Tendsto (fun z : ℂ => I * z) (𝓝 (x : ℂ)) (𝓝 ((x : ℂ) * I)) := by
    have : Continuous fun z : ℂ => I * z := by fun_prop
    simpa [mul_comm] using this.tendsto (x : ℂ)
  refine ⟨tendsto_nhdsWithin_iff.mpr ⟨hI.mono_left nhdsWithin_le_nhds, ?_⟩,
    tendsto_nhdsWithin_iff.mpr ⟨hI.mono_left nhdsWithin_le_nhds, ?_⟩⟩
  · filter_upwards [self_mem_nhdsWithin] with z hz
    have hz' : 0 < z.im := hz
    show (I * z).re < 0
    simp; linarith
  · filter_upwards [self_mem_nhdsWithin] with z hz
    have hz' : z.im < 0 := hz
    show 0 < (I * z).re
    simp; linarith

/-- On its cuts `|x| > 1`, `arctanh` has limits from above and below, both nonreal ("`arctanh x`
is complex when `x < −1` or `x > 1`"). -/
theorem arctanhD_cut_limits {x : ℝ} (hx : 1 < |x|) :
    ∃ b c : ℂ, b.im ≠ 0 ∧ c.im ≠ 0 ∧ Tendsto arctanhD (𝓝[{w | 0 < w.im}] (x : ℂ)) (𝓝 b) ∧
      Tendsto arctanhD (𝓝[{w | w.im < 0}] (x : ℂ)) (𝓝 c) := by
  obtain ⟨b, c, -, hb, hc⟩ := arctanD_cut_limits hx
  obtain ⟨hup, hdn⟩ := tendsto_I_mul_side x
  have he : arctanhD = fun z => -I * arctanD (I * z) := funext arctanhD_eq
  have h1 : Tendsto arctanhD (𝓝[{w | 0 < w.im}] (x : ℂ)) (𝓝 (-I * c)) := by
    rw [he]; exact (hc.comp hup).const_mul _
  have h2 : Tendsto arctanhD (𝓝[{w | w.im < 0}] (x : ℂ)) (𝓝 (-I * b)) := by
    rw [he]; exact (hb.comp hdn).const_mul _
  have hreal : ∀ (S : Set ℂ) (_ : (𝓝[S] (x : ℂ)).NeBot) (L : ℂ), (∀ z ∈ S, z.im ≠ 0) →
      Tendsto arctanhD (𝓝[S] (x : ℂ)) (𝓝 L) → L.im ≠ 0 := by
    intro S hne L hS hL him
    have hL' := eq_ofReal_re_of_im_eq_zero him
    have hcont : ContinuousAt tanh L := by
      rw [hL']
      have hc : cosh (L.re : ℂ) ≠ 0 := by
        rw [← ofReal_cosh]; exact_mod_cast (Real.cosh_pos _).ne'
      have : tanh = fun z => sinh z / cosh z := funext tanh_eq_sinh_div_cosh
      rw [this]
      exact continuous_sinh.continuousAt.div continuous_cosh.continuousAt hc
    have heq := apply_eq_of_tendsto nhdsWithin_le_nhds hL hcont (by
      filter_upwards [self_mem_nhdsWithin] with z hz
      exact tanh_arctanhD (Or.inl (hS z hz)))
    rw [hL', ← ofReal_tanh, ofReal_inj] at heq
    have := Real.abs_tanh_lt_one L.re
    rw [heq] at this
    linarith
  exact ⟨_, _, hreal _ (neBot_upper x) _ (fun z hz => ne_of_gt hz) h1,
    hreal _ (neBot_lower x) _ (fun z hz => ne_of_lt hz) h2, h1, h2⟩
