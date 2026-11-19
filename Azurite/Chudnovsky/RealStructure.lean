/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.Chudnovsky.CM
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Real structure and mean values of `℘`

* **Conjugation.**  If the lattice is stable under complex conjugation, then
  `℘(z̄) = conj ℘(z)` and `℘′(z̄) = conj ℘′(z)` (`weierstrassP_conj`, `derivWeierstrassP_conj`);
  so `℘` and `℘′` are real at real points, and — if moreover `1` is a period — `℘` is real on
  the line `Re z = 1/2` (`weierstrassP_half_add_I_im`).  The lattices `ℤ[i]`, `ℤ[ρ]` are
  stable (`latI_conj_mem`, `latRho_conj_mem`).
* **Mean values.**  `∫₀¹ ℘(z₀ + tv) v dt = ζ(z₀) − ζ(z₀ + v)` along a segment that avoids the
  lattice (`integral_weierstrassP_segment`): the mean of `℘` over a period is minus a
  quasi-period.
-/

open Module Filter MeasureTheory
open scoped Topology ComplexConjugate

namespace Azurite.Chudnovsky

/-! ### Conjugation -/

section Conj

variable (L : PeriodPair)

/-- Conjugation preserves the lattice if it maps the two periods into it. -/
theorem conj_mem_lattice (h₁ : conj L.ω₁ ∈ L.lattice) (h₂ : conj L.ω₂ ∈ L.lattice) {l : ℂ}
    (hl : l ∈ L.lattice) : conj l ∈ L.lattice := by
  obtain ⟨m, n, rfl⟩ := PeriodPair.mem_lattice.mp hl
  have : conj ((m : ℂ) * L.ω₁ + n * L.ω₂) = m • conj L.ω₁ + n • conj L.ω₂ := by
    simp [zsmul_eq_mul]
  rw [this]
  exact add_mem (zsmul_mem h₁ m) (zsmul_mem h₂ n)

variable {L} (hc : ∀ l ∈ L.lattice, conj l ∈ L.lattice)

/-- Conjugation as a permutation of a stable lattice. -/
noncomputable def conjEquiv (hc : ∀ l ∈ L.lattice, conj l ∈ L.lattice) :
    L.lattice ≃ L.lattice where
  toFun l := ⟨conj (l : ℂ), hc l l.2⟩
  invFun l := ⟨conj (l : ℂ), hc l l.2⟩
  left_inv l := by
    apply Subtype.ext
    simp
  right_inv l := by
    apply Subtype.ext
    simp

include hc in
/-- `℘(z̄) = conj ℘(z)` for a lattice stable under conjugation. -/
theorem weierstrassP_conj (z : ℂ) : L.weierstrassP (conj z) = conj (L.weierstrassP z) := by
  unfold PeriodPair.weierstrassP
  rw [Complex.conj_tsum, ← (conjEquiv hc).tsum_eq]
  refine tsum_congr fun l => ?_
  simp [conjEquiv]

include hc in
/-- `℘′(z̄) = conj ℘′(z)` for a lattice stable under conjugation. -/
theorem derivWeierstrassP_conj (z : ℂ) :
    L.derivWeierstrassP (conj z) = conj (L.derivWeierstrassP z) := by
  unfold PeriodPair.derivWeierstrassP
  rw [map_neg, Complex.conj_tsum, ← (conjEquiv hc).tsum_eq]
  congr 1
  refine tsum_congr fun l => ?_
  simp [conjEquiv, Complex.conj_ofNat]

include hc in
/-- `℘` is real at real points. -/
theorem weierstrassP_ofReal_im (x : ℝ) : (L.weierstrassP (x : ℂ)).im = 0 := by
  have h := weierstrassP_conj hc (x : ℂ)
  rw [Complex.conj_ofReal] at h
  exact Complex.conj_eq_iff_im.mp h.symm

include hc in
/-- `℘′` is real at real points. -/
theorem derivWeierstrassP_ofReal_im (x : ℝ) : (L.derivWeierstrassP (x : ℂ)).im = 0 := by
  have h := derivWeierstrassP_conj hc (x : ℂ)
  rw [Complex.conj_ofReal] at h
  exact Complex.conj_eq_iff_im.mp h.symm

include hc in
/-- If `1` is a period, `℘` is real on the line `Re z = 1/2`. -/
theorem weierstrassP_half_add_I_im (h1 : (1 : ℂ) ∈ L.lattice) (y : ℝ) :
    (L.weierstrassP (1 / 2 + y * Complex.I)).im = 0 := by
  have h := weierstrassP_conj hc (1 / 2 + y * Complex.I)
  have e : conj ((1 : ℂ) / 2 + y * Complex.I) = -(1 / 2 + y * Complex.I) + (1 : ℂ) := by
    simp only [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I, map_div₀, map_one,
      map_ofNat]
    ring
  rw [e, show (1 : ℂ) = ((⟨1, h1⟩ : L.lattice) : ℂ) from rfl, L.weierstrassP_add_coe,
    L.weierstrassP_neg] at h
  exact Complex.conj_eq_iff_im.mp h.symm

end Conj

theorem latI_conj_mem {l : ℂ} (hl : l ∈ latI.lattice) : conj l ∈ latI.lattice := by
  refine conj_mem_lattice latI ?_ ?_ hl
  · rw [pairOf_ω₁, map_one]
    exact latI.ω₁_mem_lattice
  · rw [pairOf_ω₂, UpperHalfPlane.coe_I, Complex.conj_I]
    exact neg_mem latI.ω₂_mem_lattice

theorem latRho_conj_mem {l : ℂ} (hl : l ∈ latRho.lattice) : conj l ∈ latRho.lattice := by
  refine conj_mem_lattice latRho ?_ ?_ hl
  · rw [pairOf_ω₁, map_one]
    exact latRho.ω₁_mem_lattice
  · rw [pairOf_ω₂]
    have : conj (UpperHalfPlane.ρ : ℂ) = -1 - (UpperHalfPlane.ρ : ℂ) := by
      apply Complex.ext <;> simp [UpperHalfPlane.ρ]
      ring
    rw [this]
    exact sub_mem (neg_mem latRho.ω₁_mem_lattice) latRho.ω₂_mem_lattice

/-! ### Mean values -/

/-- `∫₀¹ ℘(z₀ + tv) v dt = ζ(z₀) − ζ(z₀ + v)` along a segment off the lattice. -/
theorem integral_weierstrassP_segment (L : PeriodPair) (z₀ v : ℂ)
    (h : ∀ t ∈ Set.Icc (0 : ℝ) 1, z₀ + t * v ∉ L.lattice) :
    ∫ t in (0 : ℝ)..1, L.weierstrassP (z₀ + t * v) * v
      = weierstrassZeta L z₀ - weierstrassZeta L (z₀ + v) := by
  have hderiv : ∀ t ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt (fun t : ℝ => -weierstrassZeta L (z₀ + t * v))
        (L.weierstrassP (z₀ + t * v) * v) t := by
    intro t ht
    rw [Set.uIcc_of_le zero_le_one] at ht
    have h1 := hasDerivAt_weierstrassZeta L (h t ht)
    have h2 : HasDerivAt (fun t : ℝ => z₀ + (t : ℂ) * v) v t := by
      have := ((Complex.ofRealCLM.hasDerivAt (x := t)).mul_const v).const_add z₀
      simpa using this
    have h3 := (h1.scomp t h2).neg
    refine h3.congr_deriv ?_
    simp only [smul_eq_mul]
    ring
  have hcont : ContinuousOn (fun t : ℝ => L.weierstrassP (z₀ + t * v) * v) (Set.uIcc 0 1) := by
    rw [Set.uIcc_of_le zero_le_one]
    intro t ht
    have hd : DifferentiableAt ℂ L.weierstrassP (z₀ + t * v) :=
      L.differentiableOn_weierstrassP.differentiableAt
        (L.isClosed_lattice.isOpen_compl.mem_nhds (h t ht))
    have hc2 : Continuous fun t : ℝ => z₀ + (t : ℂ) * v := by fun_prop
    exact ((hd.continuousAt.comp (f := fun t : ℝ => z₀ + (t : ℂ) * v)
      hc2.continuousAt).mul continuousAt_const).continuousWithinAt
  have := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable
  rw [this]
  simp only [Complex.ofReal_one, one_mul, Complex.ofReal_zero, zero_mul, add_zero]
  ring

end Azurite.Chudnovsky
