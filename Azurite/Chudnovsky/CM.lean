/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.Chudnovsky.EtaG2
import Azurite.Chudnovsky.Values

/-!
# Complex multiplication: the lattices `ℤ[i]` and `ℤ[ρ]`

* **Homogeneity.**  If `c ≠ 0` and `cΛ = Λ`, then `ζ(cz) = c⁻¹ ζ(z)` (`weierstrassZeta_mul`),
  `℘(cz) = c⁻² ℘(z)` (`weierstrassP_mul`), `η(cl) = c⁻¹ η(l)` (`quasiPeriod_mul`) and
  `G_n = c⁻ⁿ G_n` (`G_mul`).
* **`G₂` at the fixed points.**  `G₂(i) = π` and `G₂(ρ) = 2π/√3` (`G2_I`, `G2_rho`), from
  Mathlib's `G2_S_transform` and `G2_T_transform` (`−1/i = i`, `−1/ρ = ρ + 1`).
* **The quasi-periods** (Legendre's relation for these lattices): for `ℤ[i]`,
  `η(1) = π`, `η(i) = −iπ`, and `g₃ = 0`; for `ℤ[ρ]`, `η(1) = 2π/√3`, `η(ρ) = ρ⁻¹ · 2π/√3`,
  and `g₂ = 0`.
-/

open UpperHalfPlane hiding I
open EisensteinSeries ModularGroup Filter
open scoped Real

namespace Azurite.Chudnovsky

/-! ### Homogeneity -/

section Homogeneity

variable (L : PeriodPair)

/-- Multiplication by `c` preserves the lattice if it maps the two periods into it. -/
theorem mul_mem_lattice {c : ℂ} (h₁ : c * L.ω₁ ∈ L.lattice) (h₂ : c * L.ω₂ ∈ L.lattice) {l : ℂ}
    (hl : l ∈ L.lattice) : c * l ∈ L.lattice := by
  obtain ⟨m, n, rfl⟩ := PeriodPair.mem_lattice.mp hl
  have : c * (m * L.ω₁ + n * L.ω₂) = m • (c * L.ω₁) + n • (c * L.ω₂) := by
    simp only [zsmul_eq_mul]
    ring
  rw [this]
  exact add_mem (zsmul_mem h₁ m) (zsmul_mem h₂ n)

variable {L} {c : ℂ} (hc0 : c ≠ 0) (hc : ∀ l ∈ L.lattice, c * l ∈ L.lattice)
  (hc' : ∀ l ∈ L.lattice, c⁻¹ * l ∈ L.lattice)

/-- Multiplication by `c` as a permutation of the lattice. -/
noncomputable def mulEquiv (hc0 : c ≠ 0) (hc : ∀ l ∈ L.lattice, c * l ∈ L.lattice)
    (hc' : ∀ l ∈ L.lattice, c⁻¹ * l ∈ L.lattice) : L.lattice ≃ L.lattice where
  toFun l := ⟨c * l, hc l l.2⟩
  invFun l := ⟨c⁻¹ * l, hc' l l.2⟩
  left_inv l := by
    apply Subtype.ext
    simp [hc0]
  right_inv l := by
    apply Subtype.ext
    simp [hc0]

include hc0 in
theorem zetaTerm_mul (l z : ℂ) : zetaTerm (c * l) (c * z) = c⁻¹ * zetaTerm l z := by
  unfold zetaTerm
  have e1 : 1 / (c * z - c * l) = c⁻¹ * (1 / (z - l)) := by
    rw [← mul_sub, one_div, mul_inv, one_div]
  have e2 : 1 / (c * l) = c⁻¹ * (1 / l) := by rw [one_div, mul_inv, one_div]
  have e3 : c * z / (c * l) ^ 2 = c⁻¹ * (z / l ^ 2) := by
    rw [mul_pow, div_eq_mul_inv, mul_inv, div_eq_mul_inv]
    field_simp
  rw [e1, e2, e3]
  ring

include hc0 hc hc' in
/-- `ζ(cz) = c⁻¹ ζ(z)` when `cΛ = Λ`. -/
theorem weierstrassZeta_mul (z : ℂ) :
    weierstrassZeta L (c * z) = c⁻¹ * weierstrassZeta L z := by
  unfold weierstrassZeta
  rw [← (mulEquiv hc0 hc hc').tsum_eq, ← tsum_mul_left]
  exact tsum_congr fun l => zetaTerm_mul hc0 l z

include hc0 hc hc' in
/-- `℘(cz) = c⁻² ℘(z)` when `cΛ = Λ`. -/
theorem weierstrassP_mul (z : ℂ) :
    L.weierstrassP (c * z) = (c ^ 2)⁻¹ * L.weierstrassP z := by
  unfold PeriodPair.weierstrassP
  rw [← (mulEquiv hc0 hc hc').tsum_eq, ← tsum_mul_left]
  refine tsum_congr fun l => ?_
  simp only [mulEquiv, Equiv.coe_fn_mk]
  rw [← mul_sub, mul_pow, mul_pow, one_div, one_div, mul_inv, mul_inv, one_div, one_div]
  ring

include hc0 hc hc' in
/-- `G_n = c⁻ⁿ G_n` when `cΛ = Λ`. -/
theorem G_mul (n : ℕ) : L.G n = (c ^ n)⁻¹ * L.G n := by
  conv_lhs => rw [PeriodPair.G, ← (mulEquiv hc0 hc hc').tsum_eq]
  rw [PeriodPair.G, ← tsum_mul_left]
  refine tsum_congr fun l => ?_
  simp only [mulEquiv, Equiv.coe_fn_mk]
  rw [mul_pow, mul_inv]

include hc0 hc hc' in
/-- `η(cl) = c⁻¹ η(l)` when `cΛ = Λ`. -/
theorem quasiPeriod_mul (l : L.lattice) :
    quasiPeriod L (c * l) = c⁻¹ * quasiPeriod L l := by
  have hz : c * (L.ω₁ / 2) ∉ L.lattice := fun h => by
    have := hc' _ h
    rw [← mul_assoc, inv_mul_cancel₀ hc0, one_mul] at this
    exact L.ω₁_div_two_notMem_lattice this
  have h1 := weierstrassZeta_add_coe L ⟨c * l, hc l l.2⟩ hz
  have h2 := weierstrassZeta_add_coe L l L.ω₁_div_two_notMem_lattice
  rw [show c * (L.ω₁ / 2) + ((⟨c * l, hc l l.2⟩ : L.lattice) : ℂ) = c * (L.ω₁ / 2 + l) by
    simp only; ring, weierstrassZeta_mul hc0 hc hc', weierstrassZeta_mul hc0 hc hc', h2] at h1
  simp only at h1
  linear_combination -h1

end Homogeneity

/-! ### `G₂` at the fixed points of the modular group -/

theorem G2_T_smul (z : ℍ) : G2 (T • z) = G2 z := by
  simpa [denom_apply, ModularForm.SL_slash_apply] using congr($G2_T_transform z)

/-- **`G₂(i) = π`.** -/
theorem G2_I : G2 UpperHalfPlane.I = π := by
  have hS : S • UpperHalfPlane.I = UpperHalfPlane.I := by
    rw [UpperHalfPlane.ext_iff, modular_S_smul, coe_mk, coe_I, inv_neg, Complex.inv_I, neg_neg]
  have h := G2_S_transform UpperHalfPlane.I
  rw [hS, coe_I] at h
  have h2 : ((Complex.I : ℂ) ^ 2)⁻¹ = -1 := by rw [Complex.I_sq]; norm_num
  have h3 : -2 * (π : ℂ) * Complex.I / Complex.I = -2 * π := by
    field_simp [Complex.I_ne_zero]
  rw [h2, h3] at h
  linear_combination h / 2

theorem rho_sq_add (z : ℂ) (hz : z = (UpperHalfPlane.ρ : ℂ)) : z ^ 2 + z + 1 = 0 := by
  subst hz
  apply Complex.ext
  · simp [UpperHalfPlane.ρ, pow_two, Complex.mul_re]
    have h3 : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
    nlinarith
  · simp [UpperHalfPlane.ρ, pow_two, Complex.mul_im]
    ring

theorem rho_ne_zero : (UpperHalfPlane.ρ : ℂ) ≠ 0 := UpperHalfPlane.ne_zero _

/-- **`G₂(ρ) = 2π/√3`.** -/
theorem G2_rho : G2 UpperHalfPlane.ρ = 2 * π / Real.sqrt 3 := by
  have hq := rho_sq_add _ rfl
  set r : ℂ := (UpperHalfPlane.ρ : ℂ) with hr
  have hr0 : r ≠ 0 := rho_ne_zero
  have hinv : r⁻¹ = -r - 1 := by
    field_simp
    linear_combination hq
  have hS : S • UpperHalfPlane.ρ = T • UpperHalfPlane.ρ := by
    rw [UpperHalfPlane.ext_iff, modular_S_smul, coe_mk, modular_T_smul, coe_vadd, inv_neg,
      ← hr, hinv]
    push_cast
    ring
  have h := G2_S_transform UpperHalfPlane.ρ
  rw [hS, G2_T_smul, ← hr] at h
  -- `r = −1/2 + (√3/2) i`
  have h3 : (Real.sqrt 3 : ℂ) ^ 2 = 3 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]
    norm_num
  have hs3 : (Real.sqrt 3 : ℂ) ≠ 0 := by
    intro h0
    rw [h0] at h3
    norm_num at h3
  have hre : r = -1 / 2 + (Real.sqrt 3 / 2 : ℂ) * Complex.I := by
    apply Complex.ext <;> simp [hr, UpperHalfPlane.ρ]
  -- `G₂ (r² − 1) = 2πi r`, and `r² − 1 = i√3 r`
  have h4 : G2 UpperHalfPlane.ρ * (r ^ 2 - 1) = 2 * π * Complex.I * r := by
    have h5 : (r ^ 2)⁻¹ * r ^ 2 = 1 := inv_mul_cancel₀ (pow_ne_zero 2 hr0)
    have h6 : -2 * (π : ℂ) * Complex.I / r * r ^ 2 = -2 * π * Complex.I * r := by
      field_simp
    linear_combination (r ^ 2) * h + (G2 UpperHalfPlane.ρ) * h5 - h6
  have h7 : r ^ 2 - 1 = Complex.I * Real.sqrt 3 * r := by
    rw [hre]
    linear_combination (-3 / 4 : ℂ) * Complex.I_sq + (-1 / 4 * Complex.I ^ 2 : ℂ) * h3
  rw [h7] at h4
  rw [eq_div_iff hs3]
  have h8 : Complex.I * (Complex.I * r) ≠ 0 :=
    mul_ne_zero Complex.I_ne_zero (mul_ne_zero Complex.I_ne_zero hr0)
  have : (G2 UpperHalfPlane.ρ * Real.sqrt 3 - 2 * π) * (Complex.I * r) = 0 := by
    linear_combination h4
  rcases mul_eq_zero.mp this with h9 | h9
  · linear_combination h9
  · exact absurd h9 (mul_ne_zero Complex.I_ne_zero hr0)

/-! ### The lattice `ℤ[i]` -/

/-- The period pair `(1, i)`. -/
noncomputable abbrev latI : PeriodPair := pairOf UpperHalfPlane.I

theorem latI_mul_I {l : ℂ} (hl : l ∈ latI.lattice) : Complex.I * l ∈ latI.lattice := by
  refine mul_mem_lattice latI ?_ ?_ hl
  · rw [pairOf_ω₁, mul_one]
    exact latI.ω₂_mem_lattice
  · rw [pairOf_ω₂, coe_I, Complex.I_mul_I]
    exact neg_mem latI.ω₁_mem_lattice

theorem latI_mul_I_inv {l : ℂ} (hl : l ∈ latI.lattice) : Complex.I⁻¹ * l ∈ latI.lattice := by
  refine mul_mem_lattice latI ?_ ?_ hl
  · rw [pairOf_ω₁, mul_one, Complex.inv_I]
    exact neg_mem latI.ω₂_mem_lattice
  · rw [pairOf_ω₂, coe_I, inv_mul_cancel₀ Complex.I_ne_zero]
    exact latI.ω₁_mem_lattice

/-- **`η₁ = π` for `ℤ[i]`.** -/
theorem quasiPeriod_latI_one : quasiPeriod latI 1 = π := by
  rw [quasiPeriod_one_eq_G2, G2_I]

/-- **`η₂ = −iπ` for `ℤ[i]`.** -/
theorem quasiPeriod_latI_I : quasiPeriod latI Complex.I = -Complex.I * π := by
  have h := quasiPeriod_mul Complex.I_ne_zero (fun l hl => latI_mul_I hl)
    (fun l hl => latI_mul_I_inv hl) (⟨1, latI.ω₁_mem_lattice⟩ : latI.lattice)
  simp only [mul_one] at h
  rw [h, quasiPeriod_latI_one, Complex.inv_I]

/-- `g₃ = 0` for `ℤ[i]`. -/
theorem g₃_latI : latI.g₃ = 0 := by
  have h := G_mul (L := latI) Complex.I_ne_zero (fun l hl => latI_mul_I hl)
    (fun l hl => latI_mul_I_inv hl) 6
  have h6 : (Complex.I ^ 6 : ℂ) = -1 := by
    rw [show (6 : ℕ) = 2 * 3 by norm_num, pow_mul, Complex.I_sq]
    norm_num
  rw [h6] at h
  have : latI.G 6 = 0 := by linear_combination h / 2 + (latI.G 6 / 2) * (by norm_num :
    ((-1 : ℂ))⁻¹ = -1)
  rw [PeriodPair.g₃, this, mul_zero]

/-! ### The lattice `ℤ[ρ]` -/

/-- The period pair `(1, ρ)`, `ρ = e^{2πi/3}`. -/
noncomputable abbrev latRho : PeriodPair := pairOf UpperHalfPlane.ρ

theorem rho_inv : ((UpperHalfPlane.ρ : ℂ))⁻¹ = -(UpperHalfPlane.ρ : ℂ) - 1 := by
  have hq := rho_sq_add _ rfl
  have hr0 := rho_ne_zero
  field_simp
  linear_combination hq

theorem rho_cube : (UpperHalfPlane.ρ : ℂ) ^ 3 = 1 := by
  have hq := rho_sq_add _ rfl
  linear_combination ((UpperHalfPlane.ρ : ℂ) - 1) * hq

theorem latRho_mul_rho {l : ℂ} (hl : l ∈ latRho.lattice) :
    (UpperHalfPlane.ρ : ℂ) * l ∈ latRho.lattice := by
  refine mul_mem_lattice latRho ?_ ?_ hl
  · rw [pairOf_ω₁, mul_one]
    exact latRho.ω₂_mem_lattice
  · rw [pairOf_ω₂]
    have hq := rho_sq_add _ rfl
    have : (UpperHalfPlane.ρ : ℂ) * (UpperHalfPlane.ρ : ℂ) = -1 - (UpperHalfPlane.ρ : ℂ) := by
      linear_combination hq
    rw [this]
    exact sub_mem (neg_mem latRho.ω₁_mem_lattice) latRho.ω₂_mem_lattice

theorem latRho_mul_rho_inv {l : ℂ} (hl : l ∈ latRho.lattice) :
    ((UpperHalfPlane.ρ : ℂ))⁻¹ * l ∈ latRho.lattice := by
  refine mul_mem_lattice latRho ?_ ?_ hl
  · rw [pairOf_ω₁, mul_one, rho_inv]
    exact sub_mem (neg_mem latRho.ω₂_mem_lattice) latRho.ω₁_mem_lattice
  · rw [pairOf_ω₂, inv_mul_cancel₀ rho_ne_zero]
    exact latRho.ω₁_mem_lattice

/-- **`η₁ = 2π/√3` for `ℤ[ρ]`.** -/
theorem quasiPeriod_latRho_one : quasiPeriod latRho 1 = 2 * π / Real.sqrt 3 := by
  rw [quasiPeriod_one_eq_G2, G2_rho]

/-- **`η₂ = ρ⁻¹ · 2π/√3` for `ℤ[ρ]`.** -/
theorem quasiPeriod_latRho_rho :
    quasiPeriod latRho (UpperHalfPlane.ρ : ℂ)
      = ((UpperHalfPlane.ρ : ℂ))⁻¹ * (2 * π / Real.sqrt 3) := by
  have h := quasiPeriod_mul rho_ne_zero (fun l hl => latRho_mul_rho hl)
    (fun l hl => latRho_mul_rho_inv hl) (⟨1, latRho.ω₁_mem_lattice⟩ : latRho.lattice)
  simp only [mul_one] at h
  rw [h, quasiPeriod_latRho_one]

/-- `g₂ = 0` for `ℤ[ρ]`. -/
theorem g₂_latRho : latRho.g₂ = 0 := by
  have h := G_mul (L := latRho) rho_ne_zero (fun l hl => latRho_mul_rho hl)
    (fun l hl => latRho_mul_rho_inv hl) 4
  have h4 : ((UpperHalfPlane.ρ : ℂ) ^ 4)⁻¹ = -(UpperHalfPlane.ρ : ℂ) - 1 := by
    rw [show (4 : ℕ) = 3 + 1 by norm_num, pow_add, rho_cube, one_mul, pow_one, rho_inv]
  rw [h4] at h
  have hne : (UpperHalfPlane.ρ : ℂ) + 2 ≠ 0 := by
    intro h0
    have := congrArg Complex.im h0
    simp [UpperHalfPlane.ρ] at this
  have : latRho.G 4 * ((UpperHalfPlane.ρ : ℂ) + 2) = 0 := by linear_combination h
  rcases mul_eq_zero.mp this with h5 | h5
  · rw [PeriodPair.g₂, h5, mul_zero]
  · exact absurd h5 hne

end Azurite.Chudnovsky
