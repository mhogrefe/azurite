/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.Chudnovsky.Start
import Mathlib.Analysis.Complex.OpenMapping

/-!
# `z`, `℘(z)`, `ζ(z)` are algebraically independent functions

`CMData.coef_eq_zero`: if `∑ c i j k (2z)^i ℘(z)^j (2ζ(z))^k` vanishes off the lattice, then
all `c i j k` are zero.

Proof.  Translating `z₀` by the lattice points `m + nτ` leaves `℘` unchanged and adds
`2(m + nτ)` to `2z` and `2ϖ(m + nα)` to `2ζ` (`α = u + vτ ≠ τ`); a polynomial in two variables
vanishing at these points for all integers `m, n` vanishes identically (`affine_vanish`,
twice), and the points fill `ℂ²` since `ϖ(α − τ) ≠ 0`.  So for every `z₀` the polynomial
`∑_{i,k} (∑_j c i j k ℘(z₀)^j) U^i V^k` is zero, and `℘` takes infinitely many values
(`weierstrassP_poly_eq_zero`, by the open mapping theorem).
-/

namespace Azurite.Chudnovsky

open Polynomial Filter Topology

/-- A polynomial function vanishing identically has zero coefficients. -/
theorem coeff_eq_zero_of_forall_eval {a : ℕ → ℂ} {n : ℕ}
    (h : ∀ U : ℂ, ∑ i ∈ Finset.range n, a i * U ^ i = 0) : ∀ i < n, a i = 0 := by
  set P : ℂ[X] := ∑ i ∈ Finset.range n, C (a i) * X ^ i with hP
  have hev : ∀ U : ℂ, P.eval U = 0 := fun U => by
    rw [hP, eval_finsetSum]
    simpa using h U
  have hP0 : P = 0 := eq_zero_of_infinite_isRoot P
    (Set.infinite_univ.mono fun x _ => hev x)
  intro i hi
  have hc : P.coeff i = a i := by
    rw [hP, finsetSum_coeff]
    simp only [coeff_C_mul_X_pow]
    rw [Finset.sum_ite_eq (Finset.range n) i]
    simp [hi]
  rw [← hc, hP0, coeff_zero]

/-- A polynomial in two affine functions of `t` vanishing at the integers vanishes
identically. -/
theorem affine_vanish (b : ℕ → ℕ → ℂ) (n : ℕ) (p₀ p₁ q₀ q₁ : ℂ)
    (h : ∀ m : ℤ, ∑ i ∈ Finset.range n, ∑ k ∈ Finset.range n,
      b i k * (p₀ + p₁ * m) ^ i * (q₀ + q₁ * m) ^ k = 0) (t : ℂ) :
    ∑ i ∈ Finset.range n, ∑ k ∈ Finset.range n,
      b i k * (p₀ + p₁ * t) ^ i * (q₀ + q₁ * t) ^ k = 0 := by
  set P : ℂ[X] := ∑ i ∈ Finset.range n, ∑ k ∈ Finset.range n,
    C (b i k) * (C p₀ + C p₁ * X) ^ i * (C q₀ + C q₁ * X) ^ k with hP
  have hev : ∀ s : ℂ, P.eval s = ∑ i ∈ Finset.range n, ∑ k ∈ Finset.range n,
      b i k * (p₀ + p₁ * s) ^ i * (q₀ + q₁ * s) ^ k := fun s => by
    rw [hP, eval_finsetSum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [eval_finsetSum]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp
  have hP0 : P = 0 := eq_zero_of_infinite_isRoot P
    ((Set.infinite_range_of_injective (f := fun m : ℤ => (m : ℂ)) Int.cast_injective).mono
      (by
        rintro _ ⟨m, rfl⟩
        show P.eval (m : ℂ) = 0
        rw [hev]
        exact h m))
  rw [← hev, hP0, eval_zero]

variable (L : PeriodPair)

/-- `℘` takes infinitely many values. -/
theorem infinite_image_weierstrassP :
    (L.weierstrassP '' (L.lattice : Set ℂ)ᶜ).Infinite := by
  have hU : IsOpen (L.lattice : Set ℂ)ᶜ := L.isClosed_lattice.isOpen_compl
  rcases L.analyticOnNhd_weierstrassP.is_constant_or_isOpen (isPreconnected_compl_lattice L)
    with ⟨w, hw⟩ | hopen
  · exfalso
    refine derivWeierstrassP_not_eqOn_zero L fun z hz => ?_
    have hev : L.weierstrassP =ᶠ[𝓝 z] fun _ => w := by
      filter_upwards [hU.mem_nhds hz] with x hx
      exact hw x hx
    have := hev.deriv_eq
    rw [L.deriv_weierstrassP, deriv_const] at this
    exact this
  · have ho := hopen _ subset_rfl hU
    have hne : (L.weierstrassP '' (L.lattice : Set ℂ)ᶜ).Nonempty :=
      ⟨_, Set.mem_image_of_mem _ L.ω₁_div_two_notMem_lattice⟩
    intro hfin
    have hclopen : IsClopen (L.weierstrassP '' (L.lattice : Set ℂ)ᶜ) := ⟨hfin.isClosed, ho⟩
    have huniv := hclopen.eq_univ hne
    rw [huniv] at hfin
    exact Set.infinite_univ hfin

/-- A polynomial vanishing at all values of `℘` is zero. -/
theorem weierstrassP_poly_eq_zero {a : ℕ → ℂ} {n : ℕ}
    (h : ∀ z, z ∉ L.lattice → ∑ j ∈ Finset.range n, a j * L.weierstrassP z ^ j = 0) :
    ∀ j < n, a j = 0 := by
  set P : ℂ[X] := ∑ i ∈ Finset.range n, C (a i) * X ^ i with hP
  have hev : ∀ U : ℂ, P.eval U = ∑ i ∈ Finset.range n, a i * U ^ i := fun U => by
    rw [hP, eval_finsetSum]
    simp
  have hP0 : P = 0 := eq_zero_of_infinite_isRoot P
    ((infinite_image_weierstrassP L).mono (by
      rintro _ ⟨z, hz, rfl⟩
      show P.eval _ = 0
      rw [hev]
      exact h z hz))
  exact coeff_eq_zero_of_forall_eval fun U => by rw [← hev, hP0, eval_zero]

namespace CMData

variable (D : CMData)

theorem quasiPeriod_lat (m n : ℤ) :
    quasiPeriod D.L ((m : ℂ) + n * D.τ) = m * D.ϖ + n * ((D.u + D.v * D.τ) * D.ϖ) := by
  have h := quasiPeriod_int_combo D.L m n
  simp only [L, pairOf_ω₁, pairOf_ω₂, mul_one] at h
  simp only [L]
  rw [h, D.hη]
  rfl

/-- **`z`, `℘`, `ζ` are algebraically independent.** -/
theorem coef_eq_zero (hϖ : D.ϖ ≠ 0) {Lc : ℕ} {c : ℕ → ℕ → ℕ → ℂ}
    (h : ∀ z, z ∉ D.L.lattice → PhiC D.L Lc c z = 0) :
    ∀ i < Lc, ∀ j < Lc, ∀ k < Lc, c i j k = 0 := by
  set α : ℂ := D.u + D.v * D.τ with hα
  have hατ : α - D.τ ≠ 0 := sub_ne_zero.mpr D.hα
  -- for every `z₀` the polynomial in `(U, V)` vanishes
  have key : ∀ z₀, z₀ ∉ D.L.lattice → ∀ U V : ℂ,
      ∑ i ∈ Finset.range Lc, ∑ k ∈ Finset.range Lc,
        (∑ j ∈ Finset.range Lc, c i j k * D.L.weierstrassP z₀ ^ j) * U ^ i * V ^ k = 0 := by
    intro z₀ hz₀ U V
    set b : ℕ → ℕ → ℂ := fun i k => ∑ j ∈ Finset.range Lc, c i j k * D.L.weierstrassP z₀ ^ j
      with hb
    set ζ₀ := weierstrassZeta D.L z₀ with hζ₀
    -- vanishing at the lattice translates
    have hint : ∀ m n : ℤ, ∑ i ∈ Finset.range Lc, ∑ k ∈ Finset.range Lc,
        b i k * (2 * z₀ + 2 * m + 2 * D.τ * n) ^ i
          * (2 * ζ₀ + 2 * D.ϖ * m + 2 * D.ϖ * α * n) ^ k = 0 := by
      intro m n
      have hl := D.lat_mem m n
      have h1 := h _ (add_coe_notMem D.L hz₀ ⟨_, hl⟩)
      have hP := D.L.weierstrassP_add_coe z₀ ⟨_, hl⟩
      have hZ := weierstrassZeta_add_coe D.L ⟨_, hl⟩ hz₀
      simp only at h1 hP hZ
      rw [D.quasiPeriod_lat] at hZ
      unfold PhiC at h1
      rw [← h1]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [hb, Finset.sum_mul, Finset.sum_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hP, hZ]
      ring
    -- all complex `y`, then all complex `x`
    have h1 : ∀ (m : ℤ) (y : ℂ), ∑ i ∈ Finset.range Lc, ∑ k ∈ Finset.range Lc,
        b i k * (2 * z₀ + 2 * m + 2 * D.τ * y) ^ i
          * (2 * ζ₀ + 2 * D.ϖ * m + 2 * D.ϖ * α * y) ^ k = 0 := fun m y =>
      affine_vanish b Lc (2 * z₀ + 2 * m) (2 * D.τ) (2 * ζ₀ + 2 * D.ϖ * m) (2 * D.ϖ * α)
        (fun n => hint m n) y
    have h2 : ∀ x y : ℂ, ∑ i ∈ Finset.range Lc, ∑ k ∈ Finset.range Lc,
        b i k * (2 * z₀ + 2 * D.τ * y + 2 * x) ^ i
          * (2 * ζ₀ + 2 * D.ϖ * α * y + 2 * D.ϖ * x) ^ k = 0 := fun x y =>
      affine_vanish b Lc (2 * z₀ + 2 * D.τ * y) 2 (2 * ζ₀ + 2 * D.ϖ * α * y) (2 * D.ϖ)
        (fun m => by
          rw [← h1 m y]
          refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
          ring) x
    -- solve for `(U, V)`
    set y : ℂ := ((V - 2 * ζ₀) / (2 * D.ϖ) - (U - 2 * z₀) / 2) / (α - D.τ) with hy
    set x : ℂ := (U - 2 * z₀) / 2 - y * D.τ with hx
    have hU : 2 * z₀ + 2 * D.τ * y + 2 * x = U := by
      rw [hx]
      ring
    have hV : 2 * ζ₀ + 2 * D.ϖ * α * y + 2 * D.ϖ * x = V := by
      have hyα : y * (α - D.τ) = (V - 2 * ζ₀) / (2 * D.ϖ) - (U - 2 * z₀) / 2 := by
        rw [hy, div_mul_cancel₀ _ hατ]
      have e1 : 2 * ζ₀ + 2 * D.ϖ * α * y + 2 * D.ϖ * x
          = 2 * ζ₀ + 2 * D.ϖ * (y * (α - D.τ) + (U - 2 * z₀) / 2) := by
        rw [hx]
        ring
      rw [e1, hyα]
      field_simp
      ring
    have := h2 x y
    rw [hU, hV] at this
    exact this
  intro i hi j hj k hk
  -- the coefficients of the polynomial in `(U, V)`
  have hb0 : ∀ z₀, z₀ ∉ D.L.lattice →
      ∑ j ∈ Finset.range Lc, c i j k * D.L.weierstrassP z₀ ^ j = 0 := by
    intro z₀ hz₀
    have hV : ∀ V : ℂ, ∑ k ∈ Finset.range Lc,
        (∑ j ∈ Finset.range Lc, c i j k * D.L.weierstrassP z₀ ^ j) * V ^ k = 0 := by
      intro V
      have hUall : ∀ U : ℂ, ∑ i ∈ Finset.range Lc, (∑ k ∈ Finset.range Lc,
          (∑ j ∈ Finset.range Lc, c i j k * D.L.weierstrassP z₀ ^ j) * V ^ k) * U ^ i = 0 := by
        intro U
        rw [← key z₀ hz₀ U V]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun k _ => ?_
        ring
      exact coeff_eq_zero_of_forall_eval hUall i hi
    exact coeff_eq_zero_of_forall_eval hV k hk
  exact weierstrassP_poly_eq_zero D.L hb0 j hj

end CMData

end Azurite.Chudnovsky
