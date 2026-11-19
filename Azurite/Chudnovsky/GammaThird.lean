/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.Chudnovsky.AlgOver
import Azurite.Chudnovsky.PeriodRho

/-!
# `Γ(1/3)` is transcendental over `ℚ(π)`

`not_algOver_gamma_one_third`: `Γ(1/3)` is not algebraic over `ℤ[2π/√3]` — Chudnovsky's
theorem for the lattice `ℤ[ρ]` (`chudnovsky_rho`) and `℘(1/2)³ = c Γ(1/3)¹⁸/π⁶`
(`rhoE_cube`).  Consequences: `Γ(1/3)`, `Γ(2/3)`, `Γ(1/6)`, `Γ(5/6)` are irrational.
-/

namespace Azurite.Chudnovsky

open Polynomial

/-- The quasi-period `2π/√3` of `ℤ[ρ]`. -/
noncomputable def varpiRho : ℂ := 2 * (Real.pi : ℂ) / (Real.sqrt 3 : ℝ)

theorem varpiRho_sq : 3 * varpiRho ^ 2 = 4 * (Real.pi : ℂ) ^ 2 := by
  have h3 : ((Real.sqrt 3 : ℝ) : ℂ) ^ 2 = 3 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]
    norm_num
  rw [varpiRho, div_pow, h3]
  ring

theorem varpiRho_ne_zero : varpiRho ≠ 0 := by
  intro h
  have := varpiRho_sq
  rw [h] at this
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  simp [hπ] at this

theorem varpiRho_pow_six : 27 * varpiRho ^ 6 = 64 * (Real.pi : ℂ) ^ 6 := by
  have h := varpiRho_sq
  have : (3 * varpiRho ^ 2) ^ 3 = (4 * (Real.pi : ℂ) ^ 2) ^ 3 := by rw [h]
  linear_combination this

/-- `π` is algebraic over `ℤ[2π/√3]`. -/
theorem algOver_pi : AlgOver varpiRho (Real.pi : ℂ) := by
  refine AlgOver.of_pow (n := 2) (by norm_num) ?_
  have h : (Real.pi : ℂ) ^ 2 = ((3 / 4 : ℚ) : ℂ) * varpiRho ^ 2 := by
    push_cast
    linear_combination (-1 / 4 : ℂ) * varpiRho_sq
  rw [h]
  exact (algOver_ratCast _ _).mul ((algOver_self _).pow 2)

/-- **`Γ(1/3)` is not algebraic over `ℤ[2π/√3]`.** -/
theorem not_algOver_gamma_one_third :
    ¬ AlgOver varpiRho ((Real.Gamma (1 / 3) : ℝ) : ℂ) := by
  intro hG
  obtain ⟨c₀, hc₀⟩ := exists_hasMeasure_two_pi_div_sqrt_three
  have hϖ : cmRho.ϖ = varpiRho := quasiPeriod_latRho_one
  have he : cmRho.e = (rhoE : ℂ) := halfValue_latRho
  have hnot : ¬ AlgOver varpiRho (rhoE : ℂ) := by
    have := cmRho.not_algOver (c₀ := c₀) (by rw [hϖ]; exact hc₀)
    rwa [hϖ, he] at this
  have hne : rhoE ≠ 0 := by
    intro h0
    apply hnot
    rw [h0]
    exact_mod_cast algOver_natCast varpiRho 0
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hπ6 : (Real.pi : ℝ) ^ 6 ≠ 0 := pow_ne_zero 6 Real.pi_ne_zero
  have h18 := hG.pow 18
  -- `π⁶ ℘(1/2)³` is algebraic in both cases
  have hprod : AlgOver varpiRho ((Real.pi : ℂ) ^ 6 * (rhoE : ℂ) ^ 3) := by
    rcases rhoE_cube hne with h | h
    · have hR : Real.pi ^ 6 * rhoE ^ 3 = (1 / 256 : ℚ) * Real.Gamma (1 / 3) ^ 18 := by
        rw [h]
        push_cast
        field_simp
      have hC : (Real.pi : ℂ) ^ 6 * (rhoE : ℂ) ^ 3
          = ((1 / 256 : ℚ) : ℂ) * ((Real.Gamma (1 / 3) : ℝ) : ℂ) ^ 18 := by exact_mod_cast hR
      rw [hC]
      exact (algOver_ratCast _ _).mul h18
    · have hR : Real.pi ^ 6 * rhoE ^ 3 = (-1 / 6912 : ℚ) * Real.Gamma (1 / 3) ^ 18 := by
        rw [h]
        push_cast
        field_simp
      have hC : (Real.pi : ℂ) ^ 6 * (rhoE : ℂ) ^ 3
          = ((-1 / 6912 : ℚ) : ℂ) * ((Real.Gamma (1 / 3) : ℝ) : ℂ) ^ 18 := by exact_mod_cast hR
      rw [hC]
      exact (algOver_ratCast _ _).mul h18
  have h3 : AlgOver varpiRho ((rhoE : ℂ) ^ 3) :=
    AlgOver.of_mul (pow_ne_zero 6 hπ) (algOver_pi.pow 6) hprod
  exact hnot (h3.of_pow (by norm_num))

/-- **`Γ(1/3)` is irrational.** -/
theorem irrational_gamma_one_third : Irrational (Real.Gamma (1 / 3)) :=
  irrational_of_not_algOver not_algOver_gamma_one_third

end Azurite.Chudnovsky
