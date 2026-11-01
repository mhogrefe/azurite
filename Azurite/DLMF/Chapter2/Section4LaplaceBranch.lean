/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/


import Azurite.DLMF.Chapter2.Section4WatsonRotation

/-!
# DLMF §2.4(iii): branches of `log` and of powers along a direction

DLMF 2.4.11 uses "the branches of `(t − a)^λ` and `(t − a)^μ` continuous and constructed with
`ph(t − a) → ω` as `t → a` along `𝒫`". Here

* `logBr ω z` is the branch of `log z` with imaginary part in `(ω − π, ω + π]`;
* `brPow ω c z = exp(c · logBr ω z)` is `z^c` with `ph z` taken in `(ω − π, ω + π]`;
* `sectorBr ω α` is the open sector `|ph z − ω| < α` (vertex removed), on which `logBr ω` is
  analytic when `α ≤ π` (`hasDerivAt_logBr`).

`logBr_eq_of_exp` characterizes `logBr ω` as the inverse of `exp` on the strip, which is how all
branch identities are proved.
-/

open Set Filter Topology Complex

namespace Azurite.DLMF

/-- The branch of `log` with imaginary part in `(ω − π, ω + π]`. -/
noncomputable def logBr (ω : ℝ) (z : ℂ) : ℂ := Complex.log (z * cexp (-(ω * I))) + ω * I

/-- `z^c` with `ph z ∈ (ω − π, ω + π]`. -/
noncomputable def brPow (ω : ℝ) (c z : ℂ) : ℂ := cexp (c * logBr ω z)

/-- The open sector `|ph z − ω| < α`, vertex removed. -/
def sectorBr (ω α : ℝ) : Set ℂ := {z | z ≠ 0 ∧ |(logBr ω z).im - ω| < α}

theorem exp_neg_mul_I_mul_exp (ω : ℝ) : cexp (-(ω * I)) * cexp (ω * I) = 1 := by
  rw [← Complex.exp_add, neg_add_cancel, Complex.exp_zero]

theorem exp_logBr {ω : ℝ} {z : ℂ} (hz : z ≠ 0) : cexp (logBr ω z) = z := by
  rw [logBr, Complex.exp_add, Complex.exp_log (mul_ne_zero hz (Complex.exp_ne_zero _)),
    mul_assoc, exp_neg_mul_I_mul_exp, mul_one]

theorem logBr_im_mem (ω : ℝ) (z : ℂ) : (logBr ω z).im ∈ Ioc (ω - Real.pi) (ω + Real.pi) := by
  have h := arg_mem_Ioc (z * cexp (-(ω * I)))
  simp only [logBr, add_im, log_im, mul_im, ofReal_re, ofReal_im, I_re, I_im, mul_zero, mul_one]
  exact ⟨by linarith [h.1], by linarith [h.2]⟩

theorem logBr_re {ω : ℝ} (z : ℂ) : (logBr ω z).re = Real.log ‖z‖ := by
  simp only [logBr, add_re, log_re, mul_re, ofReal_re, ofReal_im, I_re, I_im, mul_zero, mul_one,
    sub_zero, add_zero, norm_mul]
  rw [show cexp (-(ω * I)) = cexp (((-ω : ℝ) : ℂ) * I) by push_cast; ring_nf,
    norm_exp_ofReal_mul_I, mul_one]

/-- `logBr ω` is the inverse of `exp` on the strip `ω − π < Im < ω + π`. -/
theorem logBr_eq_of_exp {ω : ℝ} {L z : ℂ} (hL : cexp L = z) (h1 : ω - Real.pi < L.im)
    (h2 : L.im ≤ ω + Real.pi) : logBr ω z = L := by
  rw [logBr, ← hL, ← Complex.exp_add,
    Complex.log_exp (by simp only [add_im, neg_im, mul_im, ofReal_re, ofReal_im, I_re, I_im,
      mul_zero, mul_one, add_zero]; linarith)
      (by simp only [add_im, neg_im, mul_im, ofReal_re, ofReal_im, I_re, I_im, mul_zero, mul_one,
        add_zero]; linarith)]
  ring

theorem logBr_polar {ω r ψ : ℝ} (hr : 0 < r) (h1 : ω - Real.pi < ψ) (h2 : ψ ≤ ω + Real.pi) :
    logBr ω ((r : ℂ) * cexp (ψ * I)) = Real.log r + ψ * I := by
  refine logBr_eq_of_exp ?_ (by simp; linarith) (by simp; linarith)
  rw [Complex.exp_add, ← ofReal_exp, Real.exp_log hr]

theorem logBr_ofReal_pos {ω r : ℝ} (hr : 0 < r) (h1 : ω - Real.pi < 0) (h2 : 0 ≤ ω + Real.pi) :
    logBr ω r = Real.log r := by
  have := logBr_polar (ω := ω) hr (ψ := 0) h1 h2
  simpa using this

theorem brPow_polar {ω r ψ : ℝ} (hr : 0 < r) (h1 : ω - Real.pi < ψ) (h2 : ψ ≤ ω + Real.pi)
    (c : ℂ) : brPow ω c ((r : ℂ) * cexp (ψ * I)) = (r : ℂ) ^ c * cexp (ψ * I * c) := by
  rw [brPow, logBr_polar hr h1 h2, mul_add, Complex.exp_add, cpow_def_of_ne_zero
    (ofReal_ne_zero.mpr hr.ne'), ← ofReal_log hr.le, mul_comm (c : ℂ)]
  ring_nf

theorem brPow_mul_exp (ω : ℝ) (c₁ c₂ : ℂ) (z : ℂ) :
    brPow ω c₁ z * brPow ω c₂ z = brPow ω (c₁ + c₂) z := by
  rw [brPow, brPow, brPow, ← Complex.exp_add, add_mul]

theorem brPow_ne_zero (ω : ℝ) (c z : ℂ) : brPow ω c z ≠ 0 := Complex.exp_ne_zero _

theorem norm_brPow {ω : ℝ} (c : ℂ) {z : ℂ} (hz : z ≠ 0) :
    ‖brPow ω c z‖ = ‖z‖ ^ c.re * Real.exp (-(c.im * (logBr ω z).im)) := by
  rw [brPow, Complex.norm_exp, mul_re, logBr_re z, Real.rpow_def_of_pos (norm_pos_iff.mpr hz),
    ← Real.exp_add]
  congr 1
  ring

theorem norm_brPow_le {ω : ℝ} (c : ℂ) {z : ℂ} (hz : z ≠ 0) :
    ‖brPow ω c z‖ ≤ ‖z‖ ^ c.re * Real.exp (|c.im| * (|ω| + Real.pi)) := by
  rw [norm_brPow c hz]
  gcongr
  have h := logBr_im_mem ω z
  have h1 : |(logBr ω z).im| ≤ |ω| + Real.pi := by
    rw [abs_le]
    constructor <;> linarith [h.1, h.2, neg_abs_le ω, le_abs_self ω]
  calc -(c.im * (logBr ω z).im) ≤ |c.im * (logBr ω z).im| := neg_le_abs _
    _ = |c.im| * |(logBr ω z).im| := abs_mul _ _
    _ ≤ |c.im| * (|ω| + Real.pi) := by gcongr

/-! ### The sector and analyticity -/

theorem mem_sectorBr_iff {ω α : ℝ} {z : ℂ} :
    z ∈ sectorBr ω α ↔ z ≠ 0 ∧ |arg (z * cexp (-(ω * I)))| < α := by
  simp only [sectorBr, mem_ofPred_eq, logBr, add_im, log_im, mul_im, ofReal_re, ofReal_im, I_re,
    I_im, mul_zero, mul_one, add_zero, add_sub_cancel_right]

theorem mem_slitPlane_of_mem_sectorBr {ω α : ℝ} (hα : α ≤ Real.pi) {z : ℂ}
    (hz : z ∈ sectorBr ω α) : z * cexp (-(ω * I)) ∈ slitPlane := by
  obtain ⟨h0, h⟩ := mem_sectorBr_iff.mp hz
  rw [mem_slitPlane_iff_arg]
  refine ⟨fun h1 => ?_, mul_ne_zero h0 (Complex.exp_ne_zero _)⟩
  rw [h1, abs_of_pos Real.pi_pos] at h
  linarith

theorem hasDerivAt_logBr {ω : ℝ} {z : ℂ} (h : z * cexp (-(ω * I)) ∈ slitPlane) :
    HasDerivAt (logBr ω) z⁻¹ z := by
  have h1 := ((hasDerivAt_id z).mul_const (cexp (-(ω * I)))).clog h
  have h2 : HasDerivAt (logBr ω) (1 * cexp (-(ω * I)) / (z * cexp (-(ω * I)))) z :=
    h1.add_const (ω * I)
  have hz : z ≠ 0 := by
    rintro rfl
    simp at h
  refine h2.congr_deriv ?_
  field_simp

theorem hasDerivAt_brPow {ω : ℝ} (c : ℂ) {z : ℂ} (h : z * cexp (-(ω * I)) ∈ slitPlane) :
    HasDerivAt (brPow ω c) (c * brPow ω c z / z) z := by
  have h1 := ((hasDerivAt_logBr h).const_mul c).cexp
  refine h1.congr_deriv ?_
  rw [brPow]
  ring

theorem sectorBr_eq {ω α : ℝ} (hα : α ≤ Real.pi) :
    sectorBr ω α = (fun z : ℂ => z * cexp (-(ω * I))) ⁻¹' (slitPlane ∩ arg ⁻¹' Ioo (-α) α) := by
  ext z
  rw [mem_sectorBr_iff, mem_preimage, mem_inter_iff, mem_preimage, mem_Ioo, mem_slitPlane_iff_arg,
    ← abs_lt]
  constructor
  · rintro ⟨h0, h⟩
    refine ⟨⟨fun h1 => ?_, mul_ne_zero h0 (Complex.exp_ne_zero _)⟩, h⟩
    rw [h1, abs_of_pos Real.pi_pos] at h
    linarith
  · rintro ⟨⟨-, h0⟩, h⟩
    exact ⟨fun h1 => h0 (by rw [h1, zero_mul]), h⟩

theorem isOpen_sectorBr {ω α : ℝ} (hα : α ≤ Real.pi) : IsOpen (sectorBr ω α) := by
  rw [sectorBr_eq hα]
  have hc : ContinuousOn arg slitPlane := fun x hx => (continuousAt_arg hx).continuousWithinAt
  exact (hc.isOpen_inter_preimage isOpen_slitPlane isOpen_Ioo).preimage (by fun_prop)

theorem sectorBr_mono {ω α β : ℝ} (h : α ≤ β) : sectorBr ω α ⊆ sectorBr ω β :=
  fun _ hz => ⟨hz.1, hz.2.trans_le h⟩

theorem mem_sectorBr_of_mem {ω α : ℝ} {z : ℂ} (hz : z ∈ sectorBr ω α) (hα : α ≤ Real.pi) :
    z * cexp (-(ω * I)) ∈ slitPlane :=
  mem_slitPlane_of_mem_sectorBr hα hz

/-- `logBr ω` is continuous on the sector `|ph z − ω| < π`. -/
theorem continuousOn_logBr (ω : ℝ) : ContinuousOn (logBr ω) (sectorBr ω Real.pi) := fun _ hz =>
  (hasDerivAt_logBr (mem_slitPlane_of_mem_sectorBr le_rfl hz)).continuousAt.continuousWithinAt

/-- Polar points lie in the sector. -/
theorem polar_mem_sectorBr {ω α r ψ : ℝ} (hr : 0 < r) (hψ : |ψ - ω| < α) (hα : α ≤ Real.pi) :
    (r : ℂ) * cexp (ψ * I) ∈ sectorBr ω α := by
  have h := abs_lt.mp hψ
  refine ⟨polar_ne_zero hr ψ, ?_⟩
  rw [logBr_polar hr (by linarith) (by linarith)]
  simpa using hψ

/-- Every point of the sector is a polar point `r e^{iψ}` with `|ψ − ω| < α`. -/
theorem exists_polar_of_mem_sectorBr {ω α : ℝ} {z : ℂ} (hz : z ∈ sectorBr ω α) :
    ∃ r ψ : ℝ, 0 < r ∧ |ψ - ω| < α ∧ z = (r : ℂ) * cexp (ψ * I) := by
  refine ⟨‖z‖, (logBr ω z).im, norm_pos_iff.mpr hz.1, hz.2, ?_⟩
  have h := exp_logBr (ω := ω) hz.1
  conv_lhs => rw [← h, ← re_add_im (logBr ω z)]
  rw [Complex.exp_add, logBr_re z, ← ofReal_exp, Real.exp_log (norm_pos_iff.mpr hz.1)]

end Azurite.DLMF
