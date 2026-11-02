/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/


import Azurite.DLMF.Chapter2.Section10Parts
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Cotangent

/-!
# DLMF §2.10(iii): Asymptotic Expansions of Entire Functions — 2.10.19, 2.10.21, 2.10.24

* 2.10.19 (`hyp0F2`): `₀F₂(−; 1, 1; x) = ∑_{j=0}^∞ x^j/(j!)³`, an entire function
  (`summable_hyp0F2`).
* 2.10.21 (`dlmf_2_10_21`): `cot(πt)/(2i) = −½ − 1/(e^{−2πit} − 1) = ½ + 1/(e^{2πit} − 1)`.
* 2.10.24 (`dlmf_2_10_24`): `₀F₂(−; 1, 1; x) ∼ exp(3x^{1/3})/(2π 3^{1/2} x^{1/3})` as
  `x → +∞`.

The proof of 2.10.24 is real-variable, not DLMF's contour argument (which needs the complex
Stirling bounds 5.11.7): with `y = x^{1/3}`, `₀F₂ = e^{3y} ∑ bⱼ³`, `bⱼ = e^{−y}yʲ/j!`
(`poissonW`). Stirling's formula at integers gives `bⱼ = e^{−yφ(j/y)}/(σⱼ√(2j))`,
`φ(s) = s ln s − s + 1` (`entPhi`, `poissonW_eq`); on the window `|j − y| ≤ y^{3/5}` the cubic
Taylor bound `|φ(1+u) − u²/2| ≤ 4|u|³` (`entPhi_taylor`) turns `bⱼ³` into the Gaussian
`(2πy)^{−3/2} e^{−3(j−y)²/(2y)}`, whose window sum is a Riemann sum of `√(2πy/3)`; outside the
window the tangent inequality (`entPhi_tangent`) makes `bⱼ ≤ e^{−y^{1/5}/4}`.

Not formalized: the contour representation 2.10.20, its deformation 2.10.22, and 2.10.23 (they
need the complex Stirling bounds 5.11.7 for `1/Γ(t+1)³` on large arcs and vertical lines).
-/

open Filter Topology Set MeasureTheory intervalIntegral Finset
open scoped Nat Real

namespace Azurite.DLMF

/-! ### 2.10.19 and 2.10.21 -/

/-- **DLMF 2.10.19**: `₀F₂(−; 1, 1; x) = ∑_{j=0}^∞ x^j/(j!)³`. -/
noncomputable def hyp0F2 (x : ℝ) : ℝ := ∑' j : ℕ, x ^ j / ((j ! : ℝ) ^ 3)

theorem summable_hyp0F2_complex (z : ℂ) :
    Summable fun j : ℕ => z ^ j / ((j ! : ℂ) ^ 3) := by
  refine Summable.of_norm_bounded (Real.summable_pow_div_factorial ‖z‖) fun j => ?_
  rw [norm_div, norm_pow, norm_pow, Complex.norm_natCast]
  have h1 : (1 : ℝ) ≤ j ! := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero j)
  gcongr
  calc (j ! : ℝ) = (j ! : ℝ) ^ 1 := (pow_one _).symm
    _ ≤ (j ! : ℝ) ^ 3 := pow_le_pow_right₀ h1 (by norm_num)

/-- The series 2.10.19 converges for every complex `x` (`₀F₂` is entire). -/
theorem summable_hyp0F2 (x : ℝ) : Summable fun j : ℕ => x ^ j / ((j ! : ℝ) ^ 3) := by
  refine Summable.of_norm_bounded (Real.summable_pow_div_factorial |x|) fun j => ?_
  rw [norm_div, norm_pow, norm_pow, Real.norm_eq_abs, Real.norm_natCast]
  have h1 : (1 : ℝ) ≤ j ! := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero j)
  gcongr
  calc (j ! : ℝ) = (j ! : ℝ) ^ 1 := (pow_one _).symm
    _ ≤ (j ! : ℝ) ^ 3 := pow_le_pow_right₀ h1 (by norm_num)

/-- **DLMF 2.10.21**: `cot(πt)/(2i) = −½ − 1/(e^{−2πit} − 1) = ½ + 1/(e^{2πit} − 1)` for
`t ∉ ℤ`. -/
theorem dlmf_2_10_21 {t : ℂ} (ht : ∀ n : ℤ, t ≠ n) :
    Complex.cot (π * t) / (2 * Complex.I) =
        -1 / 2 - 1 / (Complex.exp (-2 * π * Complex.I * t) - 1) ∧
      Complex.cot (π * t) / (2 * Complex.I) =
        1 / 2 + 1 / (Complex.exp (2 * π * Complex.I * t) - 1) := by
  set E := Complex.exp (2 * π * Complex.I * t) with hE
  have hE1 : E ≠ 1 := by
    intro h
    rw [hE, Complex.exp_eq_one_iff] at h
    obtain ⟨n, hn⟩ := h
    have h2 : (2 * π * Complex.I : ℂ) ≠ 0 := by
      simp [Real.pi_ne_zero, Complex.I_ne_zero]
    exact ht n (mul_left_cancel₀ h2 (by linear_combination hn))
  have hE0 : E ≠ 0 := Complex.exp_ne_zero _
  have hEinv : Complex.exp (-2 * π * Complex.I * t) = E⁻¹ := by
    rw [hE, ← Complex.exp_neg]
    ring_nf
  have hEm : E - 1 ≠ 0 := sub_ne_zero.mpr hE1
  have hEm' : E⁻¹ - 1 ≠ 0 := by
    intro h
    apply hE1
    field_simp at h
    linear_combination -h
  have key : Complex.cot (π * t) / (2 * Complex.I) = (E + 1) / (2 * (E - 1)) := by
    rw [Complex.cot_pi_eq_exp_ratio, ← hE, div_div,
      show Complex.I * (1 - E) * (2 * Complex.I) = 2 * (E - 1) by
        linear_combination (2 * (1 - E)) * Complex.I_sq]
  rw [key, hEinv]
  constructor <;> field_simp <;> ring

/-! ### The function `φ(s) = s ln s − s + 1` -/

/-- `φ(s) = s ln s − s + 1`. -/
noncomputable def entPhi (s : ℝ) : ℝ := s * Real.log s - s + 1

/-- `|φ(1+u) − u²/2| ≤ 4|u|³` for `|u| ≤ 1/2`. -/
theorem entPhi_taylor {u : ℝ} (hu : |u| ≤ 1 / 2) : |entPhi (1 + u) - u ^ 2 / 2| ≤ 4 * |u| ^ 3 := by
  have hlt : |-u| < 1 := by rw [abs_neg]; linarith
  have h := Real.abs_log_sub_add_sum_range_le hlt 2
  simp only [sum_range_succ, sum_range_zero, zero_add, abs_neg, sub_neg_eq_add] at h
  set R := Real.log (1 + u) - u + u ^ 2 / 2 with hR
  have hR' : |R| ≤ 2 * |u| ^ 3 := by
    have e : R = (-u) ^ (0 + 1) / ((0 : ℕ) + 1 : ℝ) + (-u) ^ (1 + 1) / ((1 : ℕ) + 1 : ℝ) +
        Real.log (1 + u) := by
      rw [hR]
      push_cast
      ring
    rw [e]
    refine h.trans ?_
    rw [show 2 + 1 = 3 from rfl, div_le_iff₀ (by linarith)]
    have : 0 ≤ |u| ^ 3 := by positivity
    nlinarith
  have e : entPhi (1 + u) - u ^ 2 / 2 = -u ^ 3 / 2 + (1 + u) * R := by
    rw [entPhi, hR]
    ring
  rw [e]
  have h1u : |1 + u| ≤ 3 / 2 := by
    rw [abs_le]
    constructor <;> linarith [abs_le.mp hu |>.1, abs_le.mp hu |>.2]
  calc |-u ^ 3 / 2 + (1 + u) * R| ≤ |-u ^ 3 / 2| + |(1 + u) * R| := abs_add_le _ _
    _ = |u| ^ 3 / 2 + |1 + u| * |R| := by
        rw [abs_mul, abs_div, abs_neg, abs_pow]
        norm_num
    _ ≤ |u| ^ 3 / 2 + 3 / 2 * (2 * |u| ^ 3) := by
        gcongr
    _ ≤ 4 * |u| ^ 3 := by nlinarith [abs_nonneg u, pow_nonneg (abs_nonneg u) 3]

/-- The tangent inequality `φ(s) ≥ φ(t) + ln t · (s − t)` for `s ≥ 0 < t`. -/
theorem entPhi_tangent {s t : ℝ} (hs : 0 ≤ s) (ht : 0 < t) :
    entPhi t + Real.log t * (s - t) ≤ entPhi s := by
  rw [entPhi, entPhi]
  rcases hs.eq_or_lt with rfl | hs
  · simp
    linarith
  · have h := Real.one_sub_inv_le_log_of_pos (div_pos hs ht)
    rw [Real.log_div hs.ne' ht.ne', inv_div] at h
    have : s * (1 - t / s) ≤ s * (Real.log s - Real.log t) := mul_le_mul_of_nonneg_left h hs.le
    rw [mul_sub, mul_one, mul_div_cancel₀ _ hs.ne'] at this
    nlinarith

/-- `φ(1 ± d) ≥ d²/4` for `0 ≤ d ≤ 1/16`. -/
theorem entPhi_ge {u : ℝ} (hu : |u| ≤ 1 / 16) : u ^ 2 / 4 ≤ entPhi (1 + u) := by
  have h := entPhi_taylor (u := u) (by linarith)
  have h3 : 4 * |u| ^ 3 ≤ u ^ 2 / 4 := by
    have : |u| ^ 3 = |u| * u ^ 2 := by rw [pow_succ, sq_abs, mul_comm]
    rw [this]
    nlinarith [sq_nonneg u, abs_nonneg u]
  linarith [(abs_le.mp h).1]

/-! ### Poisson weights and Stirling -/

/-- `bⱼ = e^{−y} yʲ/j!`. -/
noncomputable def poissonW (y : ℝ) (j : ℕ) : ℝ := Real.exp (-y) * y ^ j / (j ! : ℝ)

theorem poissonW_nonneg {y : ℝ} (hy : 0 ≤ y) (j : ℕ) : 0 ≤ poissonW y j := by
  unfold poissonW
  positivity

theorem hasSum_poissonW (y : ℝ) : HasSum (poissonW y) 1 := by
  have h := (NormedSpace.expSeries_div_hasSum_exp y).mul_left (Real.exp (-y))
  rw [← Real.exp_eq_exp_ℝ, ← Real.exp_add, neg_add_cancel, Real.exp_zero] at h
  refine h.congr_fun fun j => ?_
  rw [poissonW, mul_div_assoc]

/-- `bⱼ σⱼ √(2j) = e^{−yφ(j/y)}` for `j ≥ 1`, `σⱼ = stirlingSeq j`. -/
theorem poissonW_eq {y : ℝ} (hy : 0 < y) {j : ℕ} (hj : 1 ≤ j) :
    poissonW y j * (Stirling.stirlingSeq j * √(2 * j)) = Real.exp (-(y * entPhi (j / y))) := by
  have hj0 : (0 : ℝ) < j := by exact_mod_cast hj
  have hs : Stirling.stirlingSeq j * √(2 * j) = (j ! : ℝ) / ((j : ℝ) / Real.exp 1) ^ j := by
    rw [Stirling.stirlingSeq]
    have : √(2 * (j : ℝ)) ≠ 0 := by positivity
    field_simp
  rw [hs, poissonW]
  have hexp : Real.exp (-(y * entPhi (j / y))) =
      Real.exp (-y) * Real.exp 1 ^ j * ((y / j) ^ j) := by
    rw [entPhi, show -(y * ((j : ℝ) / y * Real.log (j / y) - j / y + 1)) =
      -y + j * 1 + j * Real.log (y / j) by
        rw [Real.log_div hy.ne' hj0.ne', Real.log_div hj0.ne' hy.ne']
        field_simp
        ring,
      Real.exp_add, Real.exp_add, Real.exp_nat_mul, Real.exp_nat_mul, Real.exp_log (by positivity)]
  rw [hexp, div_pow, div_pow]
  have : (j ! : ℝ) ≠ 0 := by positivity
  have : (j : ℝ) ^ j ≠ 0 := by positivity
  have : Real.exp 1 ^ j ≠ 0 := by positivity
  field_simp

theorem poissonW_le_exp {y : ℝ} (hy : 0 < y) (j : ℕ) :
    poissonW y j ≤ Real.exp (-(y * entPhi (j / y))) := by
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · simp [poissonW, entPhi]
  · have h := poissonW_eq hy hj
    have hσ : 1 ≤ Stirling.stirlingSeq j * √(2 * j) := by
      have h1 := Stirling.sqrt_pi_le_stirlingSeq (n := j) (by omega)
      have h2 : (1 : ℝ) ≤ √π := by
        rw [Real.one_le_sqrt]; linarith [Real.two_le_pi]
      have h3 : (1 : ℝ) ≤ √(2 * j) := by
        rw [Real.one_le_sqrt]
        have : (1 : ℝ) ≤ j := by exact_mod_cast hj
        linarith
      nlinarith
    rw [← h]
    have := poissonW_nonneg hy.le j
    nlinarith

/-! ### The window `|j − y| ≤ y^{3/5}`, parametrized by `y = v⁵` -/

section Window

/-- `P = ⌈v⁵ − v³⌉`, the first index of the window. -/
noncomputable def winP (v : ℝ) : ℕ := ⌈v ^ 5 - v ^ 3⌉₊

/-- `Q = ⌊v⁵ + v³⌋`, the last index of the window. -/
noncomputable def winQ (v : ℝ) : ℕ := ⌊v ^ 5 + v ^ 3⌋₊

/-- The Gaussian `exp(−3(t − y)²/(2y))`, `y = v⁵`. -/
noncomputable def gaussW (v t : ℝ) : ℝ := Real.exp (-(3 / (2 * v ^ 5)) * (t - v ^ 5) ^ 2)

variable {v : ℝ}

theorem window_facts (hv : 4 ≤ v) :
    0 < v ^ 3 ∧ v ^ 3 ≤ v ^ 5 / 16 ∧ 1 ≤ v ^ 5 - v ^ 3 := by
  have h3 : 64 ≤ v ^ 3 := by nlinarith [pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 4) hv 3]
  have h5 : v ^ 5 = v ^ 2 * v ^ 3 := by ring
  have h2 : 16 ≤ v ^ 2 := by nlinarith
  refine ⟨by positivity, ?_, ?_⟩ <;> rw [h5] <;> nlinarith

theorem mem_window {j : ℕ} (hv : 4 ≤ v) (hj : j ∈ Finset.Icc (winP v) (winQ v)) :
    1 ≤ j ∧ |(j : ℝ) - v ^ 5| ≤ v ^ 3 := by
  obtain ⟨h0, h1, h2⟩ := window_facts hv
  have hP : v ^ 5 - v ^ 3 ≤ winP v := Nat.le_ceil _
  have hQ : (winQ v : ℝ) ≤ v ^ 5 + v ^ 3 := Nat.floor_le (by positivity)
  have hjP : (winP v : ℝ) ≤ j := by exact_mod_cast (Finset.mem_Icc.mp hj).1
  have hjQ : (j : ℝ) ≤ winQ v := by exact_mod_cast (Finset.mem_Icc.mp hj).2
  refine ⟨by exact_mod_cast (show (1 : ℝ) ≤ j by linarith), abs_le.mpr ⟨by linarith, by linarith⟩⟩

/-- Outside the window, `bⱼ ≤ e^{−v/4}`. -/
theorem poissonW_tail {j : ℕ} (hv : 4 ≤ v) (hj : j ∉ Finset.Icc (winP v) (winQ v)) :
    poissonW (v ^ 5) j ≤ Real.exp (-(v / 4)) := by
  obtain ⟨h0, h1, h2⟩ := window_facts hv
  have hy : 0 < v ^ 5 := by positivity
  refine (poissonW_le_exp hy j).trans (Real.exp_le_exp.mpr (neg_le_neg ?_))
  set d := v ^ 3 / v ^ 5 with hd
  have hd0 : 0 < d := by positivity
  have hd16 : d ≤ 1 / 16 := by rw [hd, div_le_iff₀ hy]; linarith
  have hyd : v ^ 5 * (d ^ 2 / 4) = v / 4 := by
    rw [hd]
    field_simp
  have hs : 0 ≤ (j : ℝ) / v ^ 5 := by positivity
  rw [Finset.mem_Icc, not_and_or, not_le, not_le] at hj
  rcases hj with hj | hj
  · have hjr : (j : ℝ) < v ^ 5 - v ^ 3 := Nat.lt_ceil.mp hj
    have ht := entPhi_tangent hs (show 0 < 1 + -d by linarith)
    have hlog : Real.log (1 + -d) ≤ 0 := Real.log_nonpos (by linarith) (by linarith)
    have hsj : (j : ℝ) / v ^ 5 - (1 + -d) ≤ 0 := by
      rw [hd, div_sub' hy.ne', div_nonpos_iff]
      right
      constructor <;> nlinarith
    have hge := entPhi_ge (u := -d) (by rw [abs_neg, abs_of_pos hd0]; exact hd16)
    rw [neg_sq] at hge
    have : d ^ 2 / 4 ≤ entPhi ((j : ℝ) / v ^ 5) := by nlinarith
    nlinarith
  · have hjr : v ^ 5 + v ^ 3 < j := lt_of_lt_of_le (Nat.lt_floor_add_one _)
      (by exact_mod_cast hj)
    have ht := entPhi_tangent hs (show 0 < 1 + d by linarith)
    have hlog : 0 ≤ Real.log (1 + d) := Real.log_nonneg (by linarith)
    have hsj : 0 ≤ (j : ℝ) / v ^ 5 - (1 + d) := by
      have e : (j : ℝ) / v ^ 5 - (1 + d) = ((j : ℝ) - v ^ 5 - v ^ 3) / v ^ 5 := by
        rw [hd]; field_simp; ring
      rw [e]
      exact div_nonneg (by linarith) hy.le
    have hge := entPhi_ge (u := d) (by rw [abs_of_pos hd0]; exact hd16)
    have : d ^ 2 / 4 ≤ entPhi ((j : ℝ) / v ^ 5) := by nlinarith
    nlinarith

/-- In the window, `|yφ(j/y) − (j − y)²/(2y)| ≤ 4/v`. -/
theorem window_phi {j : ℕ} (hv : 4 ≤ v) (hj : |(j : ℝ) - v ^ 5| ≤ v ^ 3) :
    |v ^ 5 * entPhi ((j : ℝ) / v ^ 5) - 3 / (2 * v ^ 5) * ((j : ℝ) - v ^ 5) ^ 2 / 3| ≤ 4 / v := by
  obtain ⟨h0, h1, h2⟩ := window_facts hv
  have hy : 0 < v ^ 5 := by positivity
  have hv0 : 0 < v := by linarith
  set u := ((j : ℝ) - v ^ 5) / v ^ 5 with hu
  have hu1 : |u| ≤ v ^ 3 / v ^ 5 := by
    rw [hu, abs_div, abs_of_pos hy]
    exact div_le_div_of_nonneg_right hj hy.le
  have hu2 : |u| ≤ 1 / 2 := hu1.trans (by rw [div_le_iff₀ hy]; linarith)
  have ht := entPhi_taylor hu2
  have hs : (j : ℝ) / v ^ 5 = 1 + u := by rw [hu]; field_simp; ring
  rw [hs]
  have e : v ^ 5 * entPhi (1 + u) - 3 / (2 * v ^ 5) * ((j : ℝ) - v ^ 5) ^ 2 / 3 =
      v ^ 5 * (entPhi (1 + u) - u ^ 2 / 2) := by
    rw [hu]; field_simp
  rw [e, abs_mul, abs_of_pos hy]
  have hu3 : |u| ^ 3 ≤ (v ^ 3 / v ^ 5) ^ 3 := pow_le_pow_left₀ (abs_nonneg u) hu1 3
  calc v ^ 5 * |entPhi (1 + u) - u ^ 2 / 2| ≤ v ^ 5 * (4 * |u| ^ 3) :=
        mul_le_mul_of_nonneg_left ht hy.le
    _ ≤ v ^ 5 * (4 * (v ^ 3 / v ^ 5) ^ 3) := by gcongr
    _ = 4 / v := by field_simp

/-- The Stirling numbers are bounded on the window: `√π ≤ σⱼ ≤ σ_P`. -/
theorem stirling_window {j : ℕ} (hv : 4 ≤ v) (hj : j ∈ Finset.Icc (winP v) (winQ v)) :
    √π ≤ Stirling.stirlingSeq j ∧ Stirling.stirlingSeq j ≤ Stirling.stirlingSeq (winP v) := by
  have hj1 := (mem_window hv hj).1
  have hP1 : 1 ≤ winP v := by
    obtain ⟨-, -, h2⟩ := window_facts hv
    exact Nat.one_le_iff_ne_zero.mpr (by
      intro h
      have := Nat.le_ceil (v ^ 5 - v ^ 3)
      rw [show ⌈v ^ 5 - v ^ 3⌉₊ = winP v from rfl, h] at this
      push_cast at this
      linarith)
  refine ⟨Stirling.sqrt_pi_le_stirlingSeq (by omega), ?_⟩
  have hPj := (Finset.mem_Icc.mp hj).1
  obtain ⟨a, ha⟩ : ∃ a, winP v = a + 1 := ⟨winP v - 1, by omega⟩
  obtain ⟨b, hb⟩ : ∃ b, j = b + 1 := ⟨j - 1, by omega⟩
  rw [ha, hb]
  exact Stirling.stirlingSeq'_antitone (show a ≤ b by omega)

/-- Each window term: `e^{−12/v} g(j)/(σ_P √(2(y+L)))³ ≤ bⱼ³ ≤ e^{12/v} g(j)/(√π √(2(y−L)))³`. -/
theorem window_term {j : ℕ} (hv : 4 ≤ v) (hj : j ∈ Finset.Icc (winP v) (winQ v)) :
    gaussW v j * Real.exp (-(12 / v)) /
        (Stirling.stirlingSeq (winP v) * √(2 * (v ^ 5 + v ^ 3))) ^ 3 ≤ poissonW (v ^ 5) j ^ 3 ∧
      poissonW (v ^ 5) j ^ 3 ≤
        gaussW v j * Real.exp (12 / v) / (√π * √(2 * (v ^ 5 - v ^ 3))) ^ 3 := by
  obtain ⟨h0, h1, h2⟩ := window_facts hv
  obtain ⟨hj1, hjw⟩ := mem_window hv hj
  obtain ⟨hσ1, hσ2⟩ := stirling_window hv hj
  have hy : 0 < v ^ 5 := by positivity
  have hv0 : 0 < v := by linarith
  have heq := poissonW_eq hy hj1
  have hphi := window_phi hv hjw
  have hjr : (j : ℝ) ≤ v ^ 5 + v ^ 3 := by linarith [(abs_le.mp hjw).2]
  have hjl : v ^ 5 - v ^ 3 ≤ j := by linarith [(abs_le.mp hjw).1]
  have hpi : 0 < √π := Real.sqrt_pos.mpr Real.pi_pos
  set D := Stirling.stirlingSeq j * √(2 * j) with hD
  have hD0 : 0 < D := by
    have : 0 < √(2 * (j : ℝ)) := Real.sqrt_pos.mpr (by positivity)
    rw [hD]
    nlinarith
  have hDlo : √π * √(2 * (v ^ 5 - v ^ 3)) ≤ D :=
    mul_le_mul hσ1 (Real.sqrt_le_sqrt (by linarith)) (Real.sqrt_nonneg _) (by linarith)
  have hDhi : D ≤ Stirling.stirlingSeq (winP v) * √(2 * (v ^ 5 + v ^ 3)) :=
    mul_le_mul hσ2 (Real.sqrt_le_sqrt (by linarith)) (Real.sqrt_nonneg _) (by linarith)
  have hpw : poissonW (v ^ 5) j ^ 3 = Real.exp (-(3 * (v ^ 5 * entPhi ((j : ℝ) / v ^ 5)))) /
      D ^ 3 := by
    rw [show Real.exp (-(3 * (v ^ 5 * entPhi ((j : ℝ) / v ^ 5)))) =
      Real.exp (-(v ^ 5 * entPhi ((j : ℝ) / v ^ 5))) ^ 3 by
        rw [← Real.exp_nat_mul]; push_cast; ring_nf, ← heq]
    field_simp
  set X := v ^ 5 * entPhi ((j : ℝ) / v ^ 5)
  set G := 3 / (2 * v ^ 5) * ((j : ℝ) - v ^ 5) ^ 2
  have hgauss : gaussW v j = Real.exp (-G) := by
    rw [gaussW]; congr 1; ring
  have hX := abs_le.mp hphi
  have h12 : 12 / v = 3 * (4 / v) := by ring
  have hlo : Real.exp (-G) * Real.exp (-(12 / v)) ≤ Real.exp (-(3 * X)) := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr (by linarith)
  have hhi : Real.exp (-(3 * X)) ≤ Real.exp (-G) * Real.exp (12 / v) := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr (by linarith)
  rw [hpw, hgauss]
  have hlo0 : 0 < √π * √(2 * (v ^ 5 - v ^ 3)) :=
    mul_pos hpi (Real.sqrt_pos.mpr (by linarith))
  constructor
  · calc Real.exp (-G) * Real.exp (-(12 / v)) /
          (Stirling.stirlingSeq (winP v) * √(2 * (v ^ 5 + v ^ 3))) ^ 3
        ≤ Real.exp (-G) * Real.exp (-(12 / v)) / D ^ 3 := by
          gcongr
      _ ≤ Real.exp (-(3 * X)) / D ^ 3 := by gcongr
  · calc Real.exp (-(3 * X)) / D ^ 3 ≤ Real.exp (-G) * Real.exp (12 / v) / D ^ 3 := by gcongr
      _ ≤ Real.exp (-G) * Real.exp (12 / v) / (√π * √(2 * (v ^ 5 - v ^ 3))) ^ 3 := by
          gcongr

end Window

/-! ### The Gaussian window sum -/

section Gauss

variable {v : ℝ}

theorem gaussW_le_one (v t : ℝ) (hv : 0 < v) : gaussW v t ≤ 1 := by
  rw [gaussW, Real.exp_le_one_iff]
  have : 0 ≤ 3 / (2 * v ^ 5) * (t - v ^ 5) ^ 2 := by positivity
  linarith

theorem gaussW_nonneg (v t : ℝ) : 0 ≤ gaussW v t := (Real.exp_pos _).le

theorem continuous_gaussW (v : ℝ) : Continuous (gaussW v) := by
  unfold gaussW
  fun_prop

theorem hasDerivAt_gaussW (v t : ℝ) :
    HasDerivAt (gaussW v) (-(3 / (2 * v ^ 5)) * (2 * (t - v ^ 5)) * gaussW v t) t := by
  have h := ((((hasDerivAt_id t).sub_const (v ^ 5)).pow 2).const_mul
    (-(3 / (2 * v ^ 5)))).exp
  convert h using 1
  · rfl
  · simp only [gaussW, Pi.pow_apply, id]
    norm_num
    ring

/-- One Riemann step: `|g(j) − ∫_j^{j+1} g| ≤ (3/y)(L + 1)` in the window. -/
theorem gauss_step (hv : 4 ≤ v) {j : ℕ} (hj : |(j : ℝ) - v ^ 5| ≤ v ^ 3) :
    |gaussW v j - ∫ t in (j : ℝ)..j + 1, gaussW v t| ≤ 3 / v ^ 5 * (v ^ 3 + 1) := by
  have hv0 : 0 < v := by linarith
  have hC : 0 ≤ 3 / v ^ 5 * (v ^ 3 + 1) := by positivity
  have hmvt := norm_image_sub_le_of_norm_deriv_le_segment' (f := gaussW v)
    (f' := fun t => -(3 / (2 * v ^ 5)) * (2 * (t - v ^ 5)) * gaussW v t)
    (C := 3 / v ^ 5 * (v ^ 3 + 1)) (a := (j : ℝ)) (b := j + 1)
    (fun t _ => (hasDerivAt_gaussW v t).hasDerivWithinAt) (fun t ht => by
      have h1 : |t - v ^ 5| ≤ v ^ 3 + 1 := by
        rw [abs_le] at hj ⊢
        constructor <;> linarith [ht.1, ht.2]
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_neg, abs_of_pos (by positivity : (0 : ℝ) <
        3 / (2 * v ^ 5)), abs_mul, abs_two, abs_of_nonneg (gaussW_nonneg v t)]
      have hg := gaussW_le_one v t hv0
      have hg0 := gaussW_nonneg v t
      calc 3 / (2 * v ^ 5) * (2 * |t - v ^ 5|) * gaussW v t
          ≤ 3 / (2 * v ^ 5) * (2 * (v ^ 3 + 1)) * 1 := by gcongr
        _ = 3 / v ^ 5 * (v ^ 3 + 1) := by field_simp)
  have hconst : gaussW v j = ∫ _t in (j : ℝ)..j + 1, gaussW v j := by simp
  rw [hconst, ← intervalIntegral.integral_sub intervalIntegrable_const
    ((continuous_gaussW v).intervalIntegrable _ _)]
  have := intervalIntegral.norm_integral_le_of_norm_le_const (a := (j : ℝ)) (b := j + 1)
    (C := 3 / v ^ 5 * (v ^ 3 + 1)) (f := fun t => gaussW v j - gaussW v t) (fun t ht => by
      rw [Set.uIoc_of_le (by linarith)] at ht
      have := hmvt t ⟨ht.1.le, ht.2⟩
      rw [norm_sub_rev]
      calc ‖gaussW v t - gaussW v j‖ ≤ 3 / v ^ 5 * (v ^ 3 + 1) * (t - j) := this
        _ ≤ 3 / v ^ 5 * (v ^ 3 + 1) * 1 := by gcongr; linarith [ht.2]
        _ = _ := mul_one _)
  rw [Real.norm_eq_abs] at this
  refine this.trans (le_of_eq ?_)
  rw [show (j : ℝ) + 1 - j = 1 by ring, abs_one, mul_one]

/-- The Gaussian window sum `G = ∑_{j=P}^{Q} g(j)`. -/
noncomputable def gaussSum (v : ℝ) : ℝ := ∑ j ∈ Finset.Icc (winP v) (winQ v), gaussW v j

theorem winP_le (hv : 4 ≤ v) : (winP v : ℝ) < v ^ 5 - v ^ 3 + 1 := by
  obtain ⟨-, -, h2⟩ := window_facts hv
  exact Nat.ceil_lt_add_one (by linarith)

theorem le_winQ (v : ℝ) : v ^ 5 + v ^ 3 < winQ v + 1 := Nat.lt_floor_add_one _

theorem winP_le_winQ (hv : 4 ≤ v) : winP v ≤ winQ v := by
  obtain ⟨h0, -, -⟩ := window_facts hv
  have h1 := winP_le hv
  have h2 : (winP v : ℝ) ≤ winQ v := by
    have := Nat.floor_le (show 0 ≤ v ^ 5 + v ^ 3 by positivity)
    have h3 : v ^ 5 - v ^ 3 + 1 ≤ v ^ 5 + v ^ 3 := by nlinarith [window_facts hv]
    have := Nat.le_floor (show ((winP v : ℕ) : ℝ) ≤ v ^ 5 + v ^ 3 by linarith)
    exact_mod_cast this
  exact_mod_cast h2

/-- The window sum versus the integral over `[P, Q + 1]`. -/
theorem gaussSum_riemann (hv : 4 ≤ v) :
    |gaussSum v - ∫ t in (winP v : ℝ)..(winQ v + 1 : ℕ), gaussW v t| ≤
      (2 * v ^ 3 + 1) * (3 / v ^ 5 * (v ^ 3 + 1)) := by
  have hPQ := winP_le_winQ hv
  have hint : ∫ t in (winP v : ℝ)..(winQ v + 1 : ℕ), gaussW v t =
      ∑ j ∈ Finset.Icc (winP v) (winQ v), ∫ t in (j : ℝ)..j + 1, gaussW v t := by
    rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
    have := sum_integral_adjacent_intervals (a := fun k : ℕ => ((winP v + k : ℕ) : ℝ))
      (n := winQ v + 1 - winP v) (f := gaussW v) (μ := volume)
      fun k _ => (continuous_gaussW v).intervalIntegrable _ _
    simp only [Nat.add_zero, Nat.add_sub_cancel' (show winP v ≤ winQ v + 1 by omega)] at this
    rw [← this]
    refine sum_congr rfl fun k _ => ?_
    push_cast
    ring_nf
  rw [hint, gaussSum, ← sum_sub_distrib]
  refine (abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ j ∈ Finset.Icc (winP v) (winQ v),
        |gaussW v j - ∫ t in (j : ℝ)..j + 1, gaussW v t|
      ≤ ∑ _j ∈ Finset.Icc (winP v) (winQ v), 3 / v ^ 5 * (v ^ 3 + 1) :=
        sum_le_sum fun j hj => gauss_step hv (mem_window hv hj).2
    _ = ((winQ v + 1 - winP v : ℕ) : ℝ) * (3 / v ^ 5 * (v ^ 3 + 1)) := by
        rw [sum_const, Nat.card_Icc, nsmul_eq_mul]
    _ ≤ (2 * v ^ 3 + 1) * (3 / v ^ 5 * (v ^ 3 + 1)) := by
        have hv0 : 0 < v := by linarith
        gcongr
        have h1 := winP_le hv
        have h2 : (winQ v : ℝ) ≤ v ^ 5 + v ^ 3 :=
          Nat.floor_le (by obtain ⟨h0, -, h2⟩ := window_facts hv; linarith)
        have h3 : (v ^ 5 - v ^ 3 : ℝ) ≤ winP v := Nat.le_ceil _
        rw [Nat.cast_sub (by omega)]
        push_cast
        linarith

theorem integral_gaussW (v : ℝ) :
    ∫ t, gaussW v t = √(2 * π * v ^ 5 / 3) := by
  have h := integral_gaussian (3 / (2 * v ^ 5))
  rw [← MeasureTheory.integral_sub_right_eq_self _ (v ^ 5)] at h
  show ∫ t, Real.exp (-(3 / (2 * v ^ 5)) * (t - v ^ 5) ^ 2) = _
  rw [h, div_div_eq_mul_div]
  congr 1
  ring

theorem integrable_gaussW (v : ℝ) (hv : 0 < v) : Integrable (gaussW v) := by
  have h := (integrable_exp_neg_mul_sq (show 0 < 3 / (2 * v ^ 5) by positivity)).comp_sub_right
    (v ^ 5)
  refine h.congr (Eventually.of_forall fun t => ?_)
  simp only [gaussW]

/-- The central integral after scaling: `∫_{y−c}^{y+c} g = (1/√a) ∫_{−c√a}^{c√a} e^{−u²}`. -/
theorem integral_gaussW_center (v c : ℝ) (hv : 0 < v) :
    ∫ t in v ^ 5 - c..v ^ 5 + c, gaussW v t =
      (√(3 / (2 * v ^ 5)))⁻¹ * ∫ u in -(c * √(3 / (2 * v ^ 5)))..(c * √(3 / (2 * v ^ 5))),
        Real.exp (-1 * u ^ 2) := by
  have ha : 0 < √(3 / (2 * v ^ 5)) := Real.sqrt_pos.mpr (by positivity)
  have h1 := intervalIntegral.integral_comp_sub_right (fun t => Real.exp (-(3 / (2 * v ^ 5)) *
    t ^ 2)) (a := v ^ 5 - c) (b := v ^ 5 + c) (v ^ 5)
  simp only [sub_sub_cancel_left, add_sub_cancel_left] at h1
  have h2 := intervalIntegral.integral_comp_mul_left (fun u => Real.exp (-1 * u ^ 2))
    (a := -c) (b := c) ha.ne'
  simp only [smul_eq_mul] at h2
  have e : ∀ s : ℝ, Real.exp (-1 * (√(3 / (2 * v ^ 5)) * s) ^ 2) =
      Real.exp (-(3 / (2 * v ^ 5)) * s ^ 2) := fun s => by
    rw [mul_pow, Real.sq_sqrt (by positivity)]
    ring_nf
  simp only [e] at h2
  rw [show (∫ t in v ^ 5 - c..v ^ 5 + c, gaussW v t) =
    ∫ t in v ^ 5 - c..v ^ 5 + c, Real.exp (-(3 / (2 * v ^ 5)) * (t - v ^ 5) ^ 2) from rfl, h1,
    h2, mul_neg, mul_comm c]

/-- **The Gaussian window sum**: `G/√(2πy/3) → 1`. -/
theorem tendsto_gaussSum :
    Tendsto (fun v => gaussSum v / √(2 * π * v ^ 5 / 3)) atTop (𝓝 1) := by
  set A := fun v : ℝ => √(2 * π * v ^ 5 / 3) with hA
  set R := fun v : ℝ => (v ^ 3 - 1) * √(3 / (2 * v ^ 5)) with hR
  -- `R → ∞`
  have hRsq : ∀ v : ℝ, 4 ≤ v → 3 * v / 8 ≤ R v ^ 2 := by
    intro v hv
    have h3 : v ^ 3 / 2 ≤ v ^ 3 - 1 := by
      nlinarith [pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 4) hv 3]
    rw [hR, mul_pow, Real.sq_sqrt (by positivity)]
    have hv0 : 0 < v := by linarith
    calc 3 * v / 8 = (v ^ 3 / 2) ^ 2 * (3 / (2 * v ^ 5)) := by field_simp; norm_num
      _ ≤ (v ^ 3 - 1) ^ 2 * (3 / (2 * v ^ 5)) := by
          gcongr
  have hRtop : Tendsto R atTop atTop := by
    refine tendsto_atTop_mono' atTop ?_ ((Real.tendsto_sqrt_atTop.comp
      (tendsto_id.const_mul_atTop (show (0 : ℝ) < 3 / 8 by norm_num))))
    filter_upwards [eventually_ge_atTop 4] with v hv
    have hR0 : 0 ≤ R v := by
      rw [hR]
      have : (1 : ℝ) ≤ v ^ 3 := by nlinarith [pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 4) hv 3]
      positivity
    simp only [Function.comp_apply, id]
    rw [← Real.sqrt_sq hR0]
    exact Real.sqrt_le_sqrt (by have := hRsq v hv; linarith)
  -- the central integral ratio `→ 1`
  have hcent : Tendsto (fun v => (√π)⁻¹ * ∫ u in -R v..R v, Real.exp (-1 * u ^ 2)) atTop
      (𝓝 1) := by
    have h := intervalIntegral_tendsto_integral (integrable_exp_neg_mul_sq one_pos)
      (tendsto_neg_atTop_atBot.comp hRtop) hRtop
    rw [integral_gaussian, div_one] at h
    have := h.const_mul (√π)⁻¹
    rw [inv_mul_cancel₀ (Real.sqrt_pos.mpr Real.pi_pos).ne'] at this
    exact this
  -- the error ratio `→ 0`
  have herr : Tendsto (fun v : ℝ => 18 / v) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  have hEA : ∀ v : ℝ, 4 ≤ v → (2 * v ^ 3 + 1) * (3 / v ^ 5 * (v ^ 3 + 1)) / A v ≤ 18 / v := by
    intro v hv
    have hv0 : 0 < v := by linarith
    have hA2 : v ^ 2 ≤ A v := by
      rw [hA]
      refine Real.le_sqrt_of_sq_le ?_
      have : 1 ≤ 2 * π * v / 3 := by nlinarith [Real.two_le_pi]
      nlinarith [pow_pos hv0 4]
    have hv3 : 1 ≤ v ^ 3 := by nlinarith [pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 4) hv 3]
    rw [div_le_div_iff₀ (by positivity) hv0]
    calc (2 * v ^ 3 + 1) * (3 / v ^ 5 * (v ^ 3 + 1)) * v
        ≤ (3 * v ^ 3) * (3 / v ^ 5 * (2 * v ^ 3)) * v := by gcongr <;> linarith
      _ = 18 * v ^ 2 := by field_simp; ring
      _ ≤ 18 * A v := by linarith
  -- squeeze
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' (g := fun v => (√π)⁻¹ *
    (∫ u in -R v..R v, Real.exp (-1 * u ^ 2)) - 18 / v) (h := fun v => 1 + 18 / v)
    (by simpa using hcent.sub herr) (by simpa using tendsto_const_nhds.add herr) ?_ ?_
  · filter_upwards [eventually_ge_atTop 4] with v hv
    have hv0 : 0 < v := by linarith
    have hA0 : 0 < A v := Real.sqrt_pos.mpr (by positivity)
    have hrie := abs_le.mp (gaussSum_riemann hv)
    have hcen := integral_gaussW_center v (v ^ 3 - 1) hv0
    have hsub : ∫ t in v ^ 5 - (v ^ 3 - 1)..v ^ 5 + (v ^ 3 - 1), gaussW v t ≤
        ∫ t in (winP v : ℝ)..(winQ v + 1 : ℕ), gaussW v t := by
      refine intervalIntegral.integral_mono_interval (by linarith [winP_le hv])
        (by nlinarith [window_facts hv]) (by push_cast; linarith [le_winQ v])
        (Eventually.of_forall fun t => gaussW_nonneg v t)
        ((continuous_gaussW v).intervalIntegrable _ _)
    have hratio : (∫ t in v ^ 5 - (v ^ 3 - 1)..v ^ 5 + (v ^ 3 - 1), gaussW v t) / A v =
        (√π)⁻¹ * ∫ u in -R v..R v, Real.exp (-1 * u ^ 2) := by
      rw [hcen]
      simp only [hA, hR]
      have h3 : √(2 * π * v ^ 5 / 3) = √π * (√(3 / (2 * v ^ 5)))⁻¹ := by
        rw [← Real.sqrt_inv, ← Real.sqrt_mul Real.pi_pos.le]
        congr 1
        field_simp
      rw [h3]
      have : 0 < √(3 / (2 * v ^ 5)) := Real.sqrt_pos.mpr (by positivity)
      have : 0 < √π := Real.sqrt_pos.mpr Real.pi_pos
      field_simp
    have hE := hEA v hv
    rw [← hratio]
    rw [le_div_iff₀ hA0]
    have : (2 * v ^ 3 + 1) * (3 / v ^ 5 * (v ^ 3 + 1)) ≤ 18 / v * A v := by
      rwa [div_le_iff₀ hA0] at hE
    rw [sub_mul, div_mul_cancel₀ _ hA0.ne']
    linarith
  · filter_upwards [eventually_ge_atTop 4] with v hv
    have hv0 : 0 < v := by linarith
    have hA0 : 0 < A v := Real.sqrt_pos.mpr (by positivity)
    have hrie := abs_le.mp (gaussSum_riemann hv)
    have hle : ∫ t in (winP v : ℝ)..(winQ v + 1 : ℕ), gaussW v t ≤ A v := by
      simp only [hA]
      rw [← integral_gaussW v, intervalIntegral.integral_of_le (by
        exact_mod_cast (show winP v ≤ winQ v + 1 by have := winP_le_winQ hv; omega))]
      exact setIntegral_le_integral (integrable_gaussW v hv0)
        (Eventually.of_forall fun t => gaussW_nonneg v t)
    have hE := hEA v hv
    rw [div_le_iff₀ hA0]
    have : (2 * v ^ 3 + 1) * (3 / v ^ 5 * (v ^ 3 + 1)) ≤ 18 / v * A v := by
      rwa [div_le_iff₀ hA0] at hE
    nlinarith

end Gauss

/-! ### 2.10.24 -/

section Main

theorem poissonW_le_one {y : ℝ} (hy : 0 ≤ y) (j : ℕ) : poissonW y j ≤ 1 :=
  le_hasSum (hasSum_poissonW y) j fun i _ => poissonW_nonneg hy i

theorem summable_poissonW_cube {y : ℝ} (hy : 0 ≤ y) : Summable fun j => poissonW y j ^ 3 :=
  (hasSum_poissonW y).summable.of_nonneg_of_le (fun j => pow_nonneg (poissonW_nonneg hy j) 3)
    fun j => by
      have h0 := poissonW_nonneg hy j
      have h1 := poissonW_le_one hy j
      calc poissonW y j ^ 3 = poissonW y j * poissonW y j ^ 2 := by ring
        _ ≤ poissonW y j * 1 := by gcongr; exact pow_le_one₀ h0 h1
        _ = poissonW y j := mul_one _

/-- The tail outside the window: `∑' bⱼ³ ≤ ∑_{window} bⱼ³ + e^{−v/2}`. -/
theorem tsum_cube_le {v : ℝ} (hv : 4 ≤ v) :
    ∑' j, poissonW (v ^ 5) j ^ 3 ≤
      ∑ j ∈ Finset.Icc (winP v) (winQ v), poissonW (v ^ 5) j ^ 3 + Real.exp (-(v / 2)) := by
  have hy : 0 ≤ v ^ 5 := by positivity
  set W := Finset.Icc (winP v) (winQ v)
  have hle : ∀ j, poissonW (v ^ 5) j ^ 3 ≤ (if j ∈ W then poissonW (v ^ 5) j ^ 3 else 0) +
      Real.exp (-(v / 2)) * poissonW (v ^ 5) j := by
    intro j
    have h0 := poissonW_nonneg hy j
    split_ifs with hj
    · have : 0 ≤ Real.exp (-(v / 2)) * poissonW (v ^ 5) j := by positivity
      linarith
    · have ht := poissonW_tail hv hj
      have hsq : poissonW (v ^ 5) j ^ 2 ≤ Real.exp (-(v / 2)) := by
        calc poissonW (v ^ 5) j ^ 2 ≤ Real.exp (-(v / 4)) ^ 2 := pow_le_pow_left₀ h0 ht 2
          _ = Real.exp (-(v / 2)) := by rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
      calc poissonW (v ^ 5) j ^ 3 = poissonW (v ^ 5) j ^ 2 * poissonW (v ^ 5) j := by ring
        _ ≤ Real.exp (-(v / 2)) * poissonW (v ^ 5) j := by gcongr
        _ = 0 + Real.exp (-(v / 2)) * poissonW (v ^ 5) j := by ring
  have hs1 : Summable fun j => (if j ∈ W then poissonW (v ^ 5) j ^ 3 else 0) :=
    summable_of_ne_finset_zero (s := W) fun j hj => by simp [hj]
  have hs2 : Summable fun j => Real.exp (-(v / 2)) * poissonW (v ^ 5) j :=
    (hasSum_poissonW _).summable.mul_left _
  refine ((summable_poissonW_cube hy).tsum_le_tsum hle (hs1.add hs2)).trans (le_of_eq ?_)
  rw [hs1.tsum_add hs2, tsum_mul_left, (hasSum_poissonW _).tsum_eq, mul_one,
    tsum_eq_sum (s := W) (fun j hj => by simp [hj])]
  congr 1
  exact sum_congr rfl fun j hj => by simp [hj]

/-- `(2π√3 y √(2πy/3)/(σ√(2ℓ))³)² = π³y³/(σ⁶ℓ³)`. -/
theorem kform {y σ ℓ : ℝ} (hy : 0 < y) (hσ : 0 < σ) (hℓ : 0 < ℓ) :
    2 * π * √3 * y * √(2 * π * y / 3) / (σ * √(2 * ℓ)) ^ 3 =
      √((π / σ ^ 2) ^ 3 * (y / ℓ) ^ 3) := by
  have hpos : 0 ≤ 2 * π * √3 * y * √(2 * π * y / 3) / (σ * √(2 * ℓ)) ^ 3 := by positivity
  rw [← Real.sqrt_sq hpos]
  congr 1
  have h1 : (2 * π * √3 * y * √(2 * π * y / 3)) ^ 2 =
      (2 * π) ^ 2 * 3 * y ^ 2 * (2 * π * y / 3) := by
    simp only [mul_pow, Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num),
      Real.sq_sqrt (show 0 ≤ 2 * π * y / 3 by positivity)]
  have h2 : ((σ * √(2 * ℓ)) ^ 3) ^ 2 = (σ ^ 2 * (2 * ℓ)) ^ 3 := by
    calc ((σ * √(2 * ℓ)) ^ 3) ^ 2 = ((σ * √(2 * ℓ)) ^ 2) ^ 3 := by ring
      _ = (σ ^ 2 * (2 * ℓ)) ^ 3 := by rw [mul_pow, Real.sq_sqrt (by positivity)]
  rw [div_pow, h1, h2]
  field_simp

theorem tendsto_winP : Tendsto winP atTop atTop := by
  refine tendsto_nat_ceil_atTop.comp (tendsto_atTop_mono' atTop ?_ tendsto_id)
  filter_upwards [eventually_ge_atTop 4] with v hv
  have := window_facts hv
  simp only [id]
  nlinarith [pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 4) hv 3]

theorem tendsto_ratio_pm (c : ℝ) :
    Tendsto (fun v : ℝ => v ^ 5 / (v ^ 5 + c * v ^ 3)) atTop (𝓝 1) := by
  have h : Tendsto (fun v : ℝ => 1 / (1 + c * (v ^ 2)⁻¹)) atTop (𝓝 (1 / (1 + c * 0))) :=
    tendsto_const_nhds.div (tendsto_const_nhds.add ((tendsto_inv_atTop_zero.comp
      (tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0))).const_mul c)) (by norm_num)
  simp only [mul_zero, add_zero, div_one] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with v hv
  field_simp

/-- `2π√3 y ∑ bⱼ³ → 1` (`y = v⁵`). -/
theorem tendsto_main :
    Tendsto (fun v : ℝ => 2 * π * √3 * v ^ 5 * ∑' j, poissonW (v ^ 5) j ^ 3) atTop (𝓝 1) := by
  set A := fun v : ℝ => √(2 * π * v ^ 5 / 3)
  set σP := fun v : ℝ => Stirling.stirlingSeq (winP v)
  -- the limits of the factors
  have hσ : Tendsto σP atTop (𝓝 √π) := Stirling.tendsto_stirlingSeq_sqrt_pi.comp tendsto_winP
  have hKlo : Tendsto (fun v => √((π / σP v ^ 2) ^ 3 * (v ^ 5 / (v ^ 5 + 1 * v ^ 3)) ^ 3))
      atTop (𝓝 1) := by
    have h1 : Tendsto (fun v => π / σP v ^ 2) atTop (𝓝 1) := by
      have := (tendsto_const_nhds (x := π)).div (hσ.pow 2) (by
        rw [Real.sq_sqrt Real.pi_pos.le]; exact Real.pi_pos.ne')
      rwa [Real.sq_sqrt Real.pi_pos.le, div_self Real.pi_pos.ne'] at this
    have h := (h1.pow 3).mul ((tendsto_ratio_pm 1).pow 3)
    rw [one_pow, one_mul] at h
    have := (Real.continuous_sqrt.tendsto 1).comp h
    rwa [Real.sqrt_one] at this
  have hKhi : Tendsto (fun v => √((v ^ 5 / (v ^ 5 + -1 * v ^ 3)) ^ 3)) atTop (𝓝 1) := by
    have h := (tendsto_ratio_pm (-1)).pow 3
    rw [one_pow] at h
    have := (Real.continuous_sqrt.tendsto 1).comp h
    rwa [Real.sqrt_one] at this
  have hexp : ∀ c : ℝ, Tendsto (fun v : ℝ => Real.exp (c / v)) atTop (𝓝 1) := fun c => by
    have h0 : Tendsto (fun v : ℝ => c / v) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_id
    have := (Real.continuous_exp.tendsto 0).comp h0
    rwa [Real.exp_zero] at this
  have htail : Tendsto (fun v : ℝ => 2 * π * √3 * v ^ 5 * Real.exp (-(v / 2))) atTop (𝓝 0) := by
    have h := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 5).comp
      (tendsto_id.atTop_div_const (show (0 : ℝ) < 2 by norm_num))
    have h2 := h.const_mul (2 * π * √3 * 32)
    rw [mul_zero] at h2
    refine h2.congr fun v => ?_
    simp only [Function.comp_apply, id]
    ring_nf
  have hlo := (tendsto_gaussSum.mul (hexp (-12))).mul hKlo
  have hhi := ((tendsto_gaussSum.mul (hexp 12)).mul hKhi).add htail
  rw [mul_one, mul_one] at hlo
  rw [mul_one, mul_one, add_zero] at hhi
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hhi ?_ ?_
  · filter_upwards [eventually_ge_atTop 4] with v hv
    obtain ⟨h0, h1, h2⟩ := window_facts hv
    have hy : 0 < v ^ 5 := by positivity
    have hA0 : 0 < A v := Real.sqrt_pos.mpr (by positivity)
    have hσ0 : 0 < σP v := lt_of_lt_of_le (Real.sqrt_pos.mpr Real.pi_pos)
      (Stirling.sqrt_pi_le_stirlingSeq (by
        have := (mem_window hv (Finset.left_mem_Icc.mpr (winP_le_winQ hv))).1; omega))
    have hD0 : 0 < σP v * √(2 * (v ^ 5 + v ^ 3)) :=
      mul_pos hσ0 (Real.sqrt_pos.mpr (by positivity))
    have hsum : gaussSum v * Real.exp (-(12 / v)) / (σP v * √(2 * (v ^ 5 + v ^ 3))) ^ 3 ≤
        ∑ j ∈ Finset.Icc (winP v) (winQ v), poissonW (v ^ 5) j ^ 3 := by
      rw [gaussSum, sum_mul, sum_div]
      exact sum_le_sum fun j hj => (window_term hv hj).1
    have hle := (summable_poissonW_cube hy.le).sum_le_tsum (Finset.Icc (winP v) (winQ v))
      (fun j _ => pow_nonneg (poissonW_nonneg hy.le j) 3)
    have hk := kform hy hσ0 (show 0 < v ^ 5 + 1 * v ^ 3 by positivity)
    rw [← hk, one_mul]
    have e : gaussSum v / A v * Real.exp (-12 / v) *
        (2 * π * √3 * v ^ 5 * A v / (σP v * √(2 * (v ^ 5 + v ^ 3))) ^ 3) =
        2 * π * √3 * v ^ 5 * (gaussSum v * Real.exp (-(12 / v)) /
          (σP v * √(2 * (v ^ 5 + v ^ 3))) ^ 3) := by
      rw [neg_div]
      field_simp
    rw [e]
    gcongr
    exact hsum.trans hle
  · filter_upwards [eventually_ge_atTop 4] with v hv
    obtain ⟨h0, h1, h2⟩ := window_facts hv
    have hy : 0 < v ^ 5 := by positivity
    have hA0 : 0 < A v := Real.sqrt_pos.mpr (by positivity)
    have hpi : 0 < √π := Real.sqrt_pos.mpr Real.pi_pos
    have hD0 : 0 < √π * √(2 * (v ^ 5 - v ^ 3)) := mul_pos hpi (Real.sqrt_pos.mpr (by linarith))
    have hsum : ∑ j ∈ Finset.Icc (winP v) (winQ v), poissonW (v ^ 5) j ^ 3 ≤
        gaussSum v * Real.exp (12 / v) / (√π * √(2 * (v ^ 5 - v ^ 3))) ^ 3 := by
      rw [gaussSum, sum_mul, sum_div]
      exact sum_le_sum fun j hj => (window_term hv hj).2
    have htl := tsum_cube_le hv
    have hk := kform hy hpi (show 0 < v ^ 5 + -1 * v ^ 3 by linarith)
    rw [show v ^ 5 + -1 * v ^ 3 = v ^ 5 - v ^ 3 by ring, Real.sq_sqrt Real.pi_pos.le,
      div_self Real.pi_pos.ne', one_pow, one_mul] at hk
    rw [show v ^ 5 + -1 * v ^ 3 = v ^ 5 - v ^ 3 by ring, ← hk]
    have e : gaussSum v / A v * Real.exp (12 / v) *
        (2 * π * √3 * v ^ 5 * A v / (√π * √(2 * (v ^ 5 - v ^ 3))) ^ 3) =
        2 * π * √3 * v ^ 5 * (gaussSum v * Real.exp (12 / v) /
          (√π * √(2 * (v ^ 5 - v ^ 3))) ^ 3) := by
      field_simp
    rw [e]
    have hc : 0 ≤ 2 * π * √3 * v ^ 5 := by positivity
    calc 2 * π * √3 * v ^ 5 * ∑' j, poissonW (v ^ 5) j ^ 3
        ≤ 2 * π * √3 * v ^ 5 * (∑ j ∈ Finset.Icc (winP v) (winQ v), poissonW (v ^ 5) j ^ 3 +
          Real.exp (-(v / 2))) := mul_le_mul_of_nonneg_left htl hc
      _ ≤ 2 * π * √3 * v ^ 5 * (gaussSum v * Real.exp (12 / v) /
          (√π * √(2 * (v ^ 5 - v ^ 3))) ^ 3 + Real.exp (-(v / 2))) := by gcongr
      _ = _ := by ring

/-- `₀F₂(−; 1, 1; v¹⁵) = e^{3v⁵} ∑ bⱼ³`. -/
theorem hyp0F2_eq (v : ℝ) :
    hyp0F2 (v ^ 15) = Real.exp (3 * v ^ 5) * ∑' j, poissonW (v ^ 5) j ^ 3 := by
  rw [hyp0F2, ← tsum_mul_left]
  refine tsum_congr fun j => ?_
  rw [poissonW, div_pow, mul_pow, ← Real.exp_nat_mul]
  have : (j ! : ℝ) ≠ 0 := by positivity
  rw [show ((3 : ℕ) : ℝ) * -v ^ 5 = -(3 * v ^ 5) by push_cast; ring, Real.exp_neg]
  have : Real.exp (3 * v ^ 5) ≠ 0 := (Real.exp_pos _).ne'
  field_simp
  ring

/-- **DLMF 2.10.24**: `₀F₂(−; 1, 1; x) ∼ exp(3x^{1/3})/(2π 3^{1/2} x^{1/3})` as `x → +∞`. -/
theorem dlmf_2_10_24 :
    AsympEqDLMF atTop hyp0F2
      (fun x => Real.exp (3 * x ^ (1 / 3 : ℝ)) / (2 * π * √3 * x ^ (1 / 3 : ℝ))) := by
  have hv : Tendsto (fun x : ℝ => x ^ (1 / 15 : ℝ)) atTop atTop :=
    tendsto_rpow_atTop (by norm_num)
  refine (tendsto_main.comp hv).congr' ?_
  filter_upwards [eventually_gt_atTop 0] with x hx
  set v := x ^ (1 / 15 : ℝ) with hvdef
  have hv0 : 0 < v := Real.rpow_pos_of_pos hx _
  have hx15 : v ^ 15 = x := by
    rw [hvdef, ← Real.rpow_natCast, ← Real.rpow_mul hx.le]
    norm_num
  have hx3 : x ^ (1 / 3 : ℝ) = v ^ 5 := by
    rw [hvdef, ← Real.rpow_natCast, ← Real.rpow_mul hx.le]
    norm_num
  simp only [Function.comp_apply]
  rw [← hvdef, hx3, show hyp0F2 x = hyp0F2 (v ^ 15) by rw [hx15], hyp0F2_eq]
  have : Real.exp (3 * v ^ 5) ≠ 0 := (Real.exp_pos _).ne'
  have : 0 < 2 * π * √3 * v ^ 5 := by positivity
  field_simp

end Main

end Azurite.DLMF
