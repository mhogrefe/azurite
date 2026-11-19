/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.Chudnovsky.QuasiPeriod

/-!
# `℘″`, and the values of `℘`, `℘′` at the points `ω₁/2 + l`

* `derivWeierstrassP_half`: `℘′(ω₁/2) = 0` (odd and periodic); `halfValue L = ℘(ω₁/2) = e₁`
  with `four_mul_halfValue_cube`: `4e₁³ − g₂e₁ − g₃ = 0`;
* `weierstrassP_half_add`, `derivWeierstrassP_half_add`: `℘ = e₁`, `℘′ = 0` at `ω₁/2 + l`;
* `derivWeierstrassP_not_eqOn_zero`: `℘′` does not vanish identically off the lattice (else `℘`
  would be constant there, against its pole of order `2`);
* `deriv_derivWeierstrassP`: `℘″ = 6℘² − g₂/2` off the lattice.
-/

open Module Filter
open scoped Topology

namespace Azurite.Chudnovsky

open PeriodPair

variable (L : PeriodPair)

/-- `℘′(ω₁/2) = 0`. -/
theorem derivWeierstrassP_half : L.derivWeierstrassP (L.ω₁ / 2) = 0 := by
  have h1 := L.derivWeierstrassP_neg (L.ω₁ / 2)
  have h2 := L.derivWeierstrassP_add_coe (-(L.ω₁ / 2)) ⟨L.ω₁, L.ω₁_mem_lattice⟩
  rw [show -(L.ω₁ / 2) + L.ω₁ = L.ω₁ / 2 by ring] at h2
  rw [h1] at h2
  have : 2 * L.derivWeierstrassP (L.ω₁ / 2) = 0 := by linear_combination h2
  simpa using this

/-- `e₁ = ℘(ω₁/2)`. -/
noncomputable def halfValue : ℂ := L.weierstrassP (L.ω₁ / 2)

/-- `4e₁³ − g₂e₁ − g₃ = 0`. -/
theorem four_mul_halfValue_cube :
    4 * halfValue L ^ 3 - L.g₂ * halfValue L - L.g₃ = 0 := by
  have h := L.derivWeierstrassP_sq (L.ω₁ / 2) L.ω₁_div_two_notMem_lattice
  rw [derivWeierstrassP_half] at h
  unfold halfValue
  linear_combination -h

theorem weierstrassP_half_add (l : L.lattice) :
    L.weierstrassP (L.ω₁ / 2 + l) = halfValue L := L.weierstrassP_add_coe _ l

theorem derivWeierstrassP_half_add (l : L.lattice) :
    L.derivWeierstrassP (L.ω₁ / 2 + l) = 0 := by
  rw [L.derivWeierstrassP_add_coe, derivWeierstrassP_half]

/-- `℘′` is not identically zero off the lattice. -/
theorem derivWeierstrassP_not_eqOn_zero :
    ¬ ∀ z ∈ (L.lattice : Set ℂ)ᶜ, L.derivWeierstrassP z = 0 := by
  intro h0
  -- `℘` would be constant off the lattice
  have hd : DifferentiableOn ℂ L.weierstrassP (L.lattice : Set ℂ)ᶜ :=
    L.differentiableOn_weierstrassP
  have hconst := (isOpen_compl_lattice L).eqOn_of_deriv_eq (isPreconnected_compl_lattice L)
    (f := L.weierstrassP) (g := fun _ => L.weierstrassP (L.ω₁ / 2)) hd
    (differentiableOn_const _)
    (fun x hx => by
      rw [L.deriv_weierstrassP, deriv_const]
      exact h0 x hx)
    (x := L.ω₁ / 2) L.ω₁_div_two_notMem_lattice rfl
  -- against the pole of order `2` at `0`
  have hev : L.weierstrassP =ᶠ[𝓝[≠] (0 : ℂ)] fun _ => L.weierstrassP (L.ω₁ / 2) := by
    have hnhds := L.compl_lattice_sdiff_singleton_mem_nhds 0
    rw [eventuallyEq_nhdsWithin_iff]
    filter_upwards [hnhds] with z hz hz0
    exact hconst fun hmem => hz ⟨hmem, hz0⟩
  have hord := L.order_weierstrassP 0 (zero_mem _)
  rw [meromorphicOrderAt_congr hev] at hord
  classical
  rw [meromorphicOrderAt_const] at hord
  split_ifs at hord
  · exact absurd hord (by decide)
  · exact absurd hord (by decide)

/-- **`℘″ = 6℘² − g₂/2`** off the lattice. -/
theorem deriv_derivWeierstrassP {z : ℂ} (hz : z ∉ L.lattice) :
    deriv L.derivWeierstrassP z = 6 * L.weierstrassP z ^ 2 - L.g₂ / 2 := by
  have hU := isOpen_compl_lattice L
  have hP : AnalyticOnNhd ℂ L.weierstrassP (L.lattice : Set ℂ)ᶜ := L.analyticOnNhd_weierstrassP
  have hP' : AnalyticOnNhd ℂ L.derivWeierstrassP (L.lattice : Set ℂ)ᶜ :=
    L.analyticOnNhd_derivWeierstrassP
  have hP'' : AnalyticOnNhd ℂ (deriv L.derivWeierstrassP) (L.lattice : Set ℂ)ᶜ := hP'.deriv
  -- the derivative of the differential equation
  have hprod : ∀ x ∈ (L.lattice : Set ℂ)ᶜ, L.derivWeierstrassP x
      * (2 * deriv L.derivWeierstrassP x - 12 * L.weierstrassP x ^ 2 + L.g₂) = 0 := by
    intro x hx
    have hev : (fun w => L.derivWeierstrassP w ^ 2)
        =ᶠ[𝓝 x] fun w => 4 * L.weierstrassP w ^ 3 - L.g₂ * L.weierstrassP w - L.g₃ := by
      filter_upwards [hU.mem_nhds hx] with w hw
      exact L.derivWeierstrassP_sq w hw
    have h1 := hev.deriv_eq
    have dP : HasDerivAt L.weierstrassP (L.derivWeierstrassP x) x := by
      have := (hP x hx).differentiableAt.hasDerivAt
      rwa [L.deriv_weierstrassP] at this
    have dP' : HasDerivAt L.derivWeierstrassP (deriv L.derivWeierstrassP x) x :=
      (hP' x hx).differentiableAt.hasDerivAt
    have e1 : deriv (fun w => L.derivWeierstrassP w ^ 2) x
        = 2 * L.derivWeierstrassP x * deriv L.derivWeierstrassP x := by
      have h2 : HasDerivAt (fun w => L.derivWeierstrassP w ^ 2)
          (((2 : ℕ) : ℂ) * L.derivWeierstrassP x ^ (2 - 1) * deriv L.derivWeierstrassP x) x :=
        dP'.pow 2
      rw [h2.deriv]
      norm_num
    have e2 : deriv (fun w => 4 * L.weierstrassP w ^ 3 - L.g₂ * L.weierstrassP w - L.g₃) x
        = 12 * L.weierstrassP x ^ 2 * L.derivWeierstrassP x - L.g₂ * L.derivWeierstrassP x := by
      have h3 : HasDerivAt (fun w => 4 * L.weierstrassP w ^ 3 - L.g₂ * L.weierstrassP w - L.g₃)
          (4 * (((3 : ℕ) : ℂ) * L.weierstrassP x ^ (3 - 1) * L.derivWeierstrassP x)
            - L.g₂ * L.derivWeierstrassP x) x :=
        (((dP.pow 3).const_mul 4).sub (dP.const_mul L.g₂)).sub_const L.g₃
      rw [h3.deriv]
      norm_num
      ring
    rw [e1, e2] at h1
    linear_combination h1
  have hfac : AnalyticOnNhd ℂ
      (fun x => 2 * deriv L.derivWeierstrassP x - 12 * L.weierstrassP x ^ 2 + L.g₂)
      (L.lattice : Set ℂ)ᶜ := fun x hx =>
    ((analyticAt_const.mul (hP'' x hx)).sub (analyticAt_const.mul ((hP x hx).pow 2))).add
      analyticAt_const
  rcases AnalyticOnNhd.eq_zero_or_eq_zero_of_mul_eq_zero hP' hfac hprod
    (isPreconnected_compl_lattice L) with h | h
  · exact absurd h (derivWeierstrassP_not_eqOn_zero L)
  · have := h z hz
    linear_combination this / 2

end Azurite.Chudnovsky
