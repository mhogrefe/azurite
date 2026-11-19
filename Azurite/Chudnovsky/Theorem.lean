/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.Chudnovsky.CM
import Azurite.Chudnovsky.Parameters

/-!
# Chudnovsky's theorem for lattices with complex multiplication

`CMData.ev2_ne_zero`: for a CM lattice `ℤ + ℤτ` as in `CMData`, if the quasi-period
`ϖ = η(1)` has a transcendence measure of Fel'dman's type, then `ϖ` and `e = ℘(1/2)` are
algebraically independent: no nonzero `R ∈ ℤ[X][Y]` vanishes at `(ϖ, e)`.

Proof: a relation gives a pair measure (`exists_pairMeasure`), which is contradictory
(`CMData.core_false`) for the parameters of `exists_params`.

`chudnovsky_rho`: the lattice `ℤ[ρ]` — `2π/√3` and `℘(1/2)` are algebraically independent.
-/

namespace Azurite.Chudnovsky

open Polynomial UpperHalfPlane

namespace CMData

variable (D : CMData)

theorem half_le_im : 1 / 2 ≤ (D.τ : ℂ).im := by
  have h1 : (D.τ : ℂ).re ^ 2 + (D.τ : ℂ).im ^ 2 = 1 := by
    have := Complex.sq_norm (D.τ : ℂ)
    rw [D.hn, Complex.normSq_apply] at this
    linarith
  have hr2 : (D.τ : ℂ).re ^ 2 ≤ 1 / 4 := by
    have := abs_le.mp D.hr
    nlinarith
  have hpos : 0 < (D.τ : ℂ).im := D.τ.im_pos
  nlinarith

/-- **Chudnovsky's theorem** for a CM lattice whose quasi-period has a transcendence measure:
`ϖ` and `e = ℘(1/2)` are algebraically independent. -/
theorem ev2_ne_zero {c₀ : ℕ} (hϖ : HasMeasure D.ϖ c₀) {R : ℤ[X][X]} (hR : R ≠ 0) :
    ev2 D.ϖ D.e R ≠ 0 := by
  intro h0
  have hτ : 1 ≤ ‖(D.τ : ℂ) - (D.p - D.τ)‖ := by
    have h1 := Complex.abs_im_le_norm ((D.τ : ℂ) - (D.p - D.τ))
    have h2 : ((D.τ : ℂ) - (D.p - D.τ)).im = 2 * (D.τ : ℂ).im := by
      simp
      ring
    rw [h2, abs_of_pos (by have := D.half_le_im; linarith)] at h1
    have := D.half_le_im
    linarith
  have hτ' : ‖((D.p : ℂ) - D.τ)‖ ≤ 1 := by
    have h1 : (D.τ : ℂ) * (D.p - D.τ) = D.q := by linear_combination -D.hsq
    have h2 := congrArg norm h1
    rw [norm_mul, D.hn, one_mul, Complex.norm_intCast] at h2
    rw [h2]
    exact_mod_cast D.hq
  obtain ⟨cst, hm⟩ := exists_pairMeasure (τ := D.τ) (τ' := D.p - D.τ) (p := D.p) (q := D.q)
    (by ring) (by linear_combination -D.hsq) D.hp D.hq hτ hτ' hϖ hR h0
  obtain ⟨C₁, hC₁⟩ := exists_weierstrassP_bound D.hn
  obtain ⟨C₂, hC₂0, hC₂⟩ := exists_weierstrassZeta_bound D.hn D.hr
  obtain ⟨γ, -, hall⟩ := exists_nat_bounds [‖D.ϖ‖, ‖D.e‖, max 1 C₁, max 1 (4 * C₂)]
  obtain ⟨P⟩ := exists_params cst γ
  exact D.core_false hm hC₁ hC₂0 hC₂ (hall _ (by simp)).2 (hall _ (by simp)).2
    (hall _ (by simp)).2 (hall _ (by simp)).2 (fun Q hQ => hϖ.aeval_ne_zero hQ) P

end CMData

/-! ### The lattice `ℤ[ρ]` -/

/-- The CM data of the lattice `ℤ[ρ]`. -/
noncomputable def cmRho : CMData where
  τ := ρ
  p := -1
  q := 1
  u := -1
  v := -1
  c := 0
  hn := norm_ρ
  hr := by
    simp [UpperHalfPlane.ρ]
    norm_num [abs_le]
  hsq := by
    rw [ρ_sq]
    push_cast
    ring
  hp := by norm_num
  hq := by norm_num
  hη := by
    have h := quasiPeriod_latRho_rho
    rw [rho_inv] at h
    rw [h, quasiPeriod_latRho_one]
    push_cast
    ring
  hu := by norm_num
  hv := by norm_num
  hg := by
    have := g₂_latRho
    rw [this]
    simp
  hc := by norm_num
  hα := by
    intro h
    have him := congrArg Complex.im h
    have hpos := ρ.im_pos
    simp at him
    linarith

/-- **Chudnovsky's theorem for `ℤ[ρ]`**: `2π/√3` and `℘(1/2)` are algebraically independent. -/
theorem chudnovsky_rho {R : ℤ[X][X]} (hR : R ≠ 0) :
    ev2 (2 * (Real.pi : ℂ) / (Real.sqrt 3 : ℝ)) (halfValue latRho) R ≠ 0 := by
  obtain ⟨c₀, hc₀⟩ := exists_hasMeasure_two_pi_div_sqrt_three
  have hϖ : cmRho.ϖ = 2 * (Real.pi : ℂ) / (Real.sqrt 3 : ℝ) := quasiPeriod_latRho_one
  have := cmRho.ev2_ne_zero (by rw [hϖ]; exact hc₀) hR
  rwa [hϖ] at this

end Azurite.Chudnovsky
