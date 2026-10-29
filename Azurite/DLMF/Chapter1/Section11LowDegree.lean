/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# DLMF §1.11(iii): Polynomials of Degrees Two, Three, and Four

Formalizations of <https://dlmf.nist.gov/1.11.iii> over `ℂ`. Each root formula is proved as a
factorization identity. "The roots of `g(w) = 0`" is the hypothesis `g(w) = ∏ (w − rᵢ)` for all
`w`; Vieta's relations are read off from it with `cubic_coeffs_eq_zero`. Square and cube roots are
arbitrary choices: `s² = D`, `A³ = …`.

* **Quadratics.** `dlmf_1_11_11`: the roots `(−b ± √D)/(2a)`, their sum `−b/a` and their
  product `c/a`.
* **Cubics.**
  * Reduction to `w³ + pw + q`: `dlmf_1_11_iii_cubic_reduce`.
  * 1.11.12: the discriminant `D = ∏ (wᵢ − wⱼ)²` (`dlmf_1_11_12`).
  * 1.11.15: `ρ = e^{2πi/3} = −1/2 + (√3/2)i`, `ρ² = e^{−2πi/3}`, `ρ² + ρ + 1 = 0`
    (`dlmf_1_11_15`).
  * 1.11.13–1.11.14: Cardano's roots `(A + B)/3`, `(ρA + ρ²B)/3`, `(ρ²A + ρB)/3`
    (`dlmf_1_11_14`, via `cubic_factor`). The roots of `f` follow by adding `−a/3`
    (`dlmf_1_11_iii_cubic_roots`).
  * Worked example: `z³ − 6z² + 6z − 2`, with `A = 3∛4`, `B = 3∛2`
    (`dlmf_1_11_iii_cubic_example`).
* **Quartics.**
  * 1.11.16: reduction (`dlmf_1_11_16`).
  * 1.11.17: the discriminant `D = ∏_{i<j} (αᵢ − αⱼ)²` (`dlmf_1_11_17`).
  * 1.11.18–1.11.19: the roots from the resolvent cubic (`dlmf_1_11_19`).
  * 1.11.20: the sign condition `√−θ₁ √−θ₂ √−θ₃ = −q` can always be met (`dlmf_1_11_20`).
  * Worked example: `z⁴ − 4z³ + 5z + 2` (`dlmf_1_11_iii_quartic_example`).
-/

open Complex
open scoped Real

namespace Azurite.DLMF

/-- A cubic `c₃w³ + c₂w² + c₁w + c₀` vanishing identically has zero coefficients. -/
theorem cubic_coeffs_eq_zero {c3 c2 c1 c0 : ℂ}
    (h : ∀ w : ℂ, c3 * w ^ 3 + c2 * w ^ 2 + c1 * w + c0 = 0) :
    c3 = 0 ∧ c2 = 0 ∧ c1 = 0 ∧ c0 = 0 := by
  have h0 := h 0
  have h1 := h 1
  have hm := h (-1)
  have h2 := h 2
  exact ⟨by linear_combination (h2 - 3 * h1 - hm + 3 * h0) / 6,
    by linear_combination (h1 + hm) / 2 - h0,
    by linear_combination (6 * h1 - 2 * hm - h2 - 3 * h0) / 6,
    by linear_combination h0⟩

/-! ### Quadratic equations -/

/-- **DLMF 1.11.11**: for `a ≠ 0` and `√D` any square root of `D = b² − 4ac`, the roots of
`az² + bz + c = 0` are `(−b ± √D)/(2a)`; their sum is `−b/a` and their product `c/a`. -/
theorem dlmf_1_11_11 {a b c s : ℂ} (ha : a ≠ 0) (hs : s ^ 2 = b ^ 2 - 4 * a * c) :
    (∀ z, a * z ^ 2 + b * z + c = a * (z - (-b + s) / (2 * a)) * (z - (-b - s) / (2 * a))) ∧
    (∀ z, a * z ^ 2 + b * z + c = 0 ↔ z = (-b + s) / (2 * a) ∨ z = (-b - s) / (2 * a)) ∧
    (-b + s) / (2 * a) + (-b - s) / (2 * a) = -b / a ∧
    (-b + s) / (2 * a) * ((-b - s) / (2 * a)) = c / a := by
  have hfac : ∀ z,
      a * z ^ 2 + b * z + c = a * (z - (-b + s) / (2 * a)) * (z - (-b - s) / (2 * a)) :=
    fun z => by
      field_simp
      linear_combination hs
  refine ⟨hfac, fun z => ?_, by field_simp; ring, by field_simp; linear_combination (-1) * hs⟩
  rw [hfac, mul_assoc, mul_eq_zero, or_iff_right ha, mul_eq_zero, sub_eq_zero, sub_eq_zero]

/-! ### Cubic equations -/

/-- `p = (3b − a²)/3`. -/
noncomputable def cubicP (a b : ℂ) : ℂ := (3 * b - a ^ 2) / 3

/-- `q = (2a³ − 9ab + 27c)/27`. -/
noncomputable def cubicQ (a b c : ℂ) : ℂ := (2 * a ^ 3 - 9 * a * b + 27 * c) / 27

/-- **DLMF 1.11.12**: the discriminant `D = −4p³ − 27q²` of `w³ + pw + q`. -/
def cubicD (p q : ℂ) : ℂ := -4 * p ^ 3 - 27 * q ^ 2

/-- DLMF §1.11(iii): `z = w − a/3` reduces `z³ + az² + bz + c` to `w³ + pw + q`. -/
theorem dlmf_1_11_iii_cubic_reduce (a b c w : ℂ) :
    (w - a / 3) ^ 3 + a * (w - a / 3) ^ 2 + b * (w - a / 3) + c =
      w ^ 3 + cubicP a b * w + cubicQ a b c := by
  unfold cubicP cubicQ
  ring

/-- **DLMF 1.11.12**: if `w₁, w₂, w₃` are the roots of `g(w) = w³ + pw + q`, then
`D = −4p³ − 27q² = ((w₁ − w₂)(w₁ − w₃)(w₂ − w₃))²`. -/
theorem dlmf_1_11_12 {p q w₁ w₂ w₃ : ℂ}
    (h : ∀ w, w ^ 3 + p * w + q = (w - w₁) * (w - w₂) * (w - w₃)) :
    cubicD p q = ((w₁ - w₂) * (w₁ - w₃) * (w₂ - w₃)) ^ 2 := by
  obtain ⟨-, h1, h2, h3⟩ := cubic_coeffs_eq_zero (c3 := 0) (c2 := w₁ + w₂ + w₃)
    (c1 := p - (w₁ * w₂ + w₁ * w₃ + w₂ * w₃)) (c0 := q + w₁ * w₂ * w₃) fun w => by
      linear_combination h w
  obtain rfl : w₃ = -w₁ - w₂ := by linear_combination h1
  rw [cubicD, show p = w₁ * w₂ + w₁ * (-w₁ - w₂) + w₂ * (-w₁ - w₂) by linear_combination h2,
    show q = -(w₁ * w₂ * (-w₁ - w₂)) by linear_combination h3]
  ring

/-- **DLMF 1.11.15**: `ρ = e^{2πi/3} = −1/2 + (√3/2) i`, `ρ² = e^{−2πi/3}`, and
`ρ² + ρ + 1 = 0`. -/
theorem dlmf_1_11_15 :
    exp (2 * π * I / 3) = -1 / 2 + (Real.sqrt 3 / 2 : ℝ) * I ∧
      exp (2 * π * I / 3) ^ 2 = exp (-2 * π * I / 3) ∧
      exp (2 * π * I / 3) ^ 2 + exp (2 * π * I / 3) + 1 = 0 := by
  have hρ : exp (2 * π * I / 3) = -1 / 2 + (Real.sqrt 3 / 2 : ℝ) * I := by
    rw [show (2 * π * I / 3 : ℂ) = ((π - π / 3 : ℝ) : ℂ) * I by push_cast; ring, exp_mul_I,
      ← ofReal_cos, ← ofReal_sin, Real.cos_pi_sub, Real.sin_pi_sub, Real.cos_pi_div_three,
      Real.sin_pi_div_three]
    push_cast
    ring
  refine ⟨hρ, ?_, ?_⟩
  · rw [← exp_nat_mul, show ((2 : ℕ) : ℂ) * (2 * π * I / 3) = -2 * π * I / 3 + 2 * π * I by
      push_cast; ring, exp_add, exp_two_pi_mul_I, mul_one]
  · rw [hρ]
    have h3 : ((Real.sqrt 3 : ℝ) : ℂ) ^ 2 = 3 := by
      rw [← ofReal_pow, Real.sq_sqrt (by norm_num)]
      norm_num
    push_cast
    linear_combination (I ^ 2 / 4) * h3 + (3 / 4 : ℂ) * I_sq

/-- Factorization behind 1.11.14: if `ω² + ω + 1 = 0`, `AB = −3p` and `A³ + B³ = −27q`, then
`w³ + pw + q = (w − (A + B)/3)(w − (ωA + ω²B)/3)(w − (ω²A + ωB)/3)`. -/
theorem cubic_factor {p q A B ω : ℂ} (hω : ω ^ 2 + ω + 1 = 0) (hAB : A * B = -3 * p)
    (hsum : A ^ 3 + B ^ 3 = -27 * q) (w : ℂ) :
    w ^ 3 + p * w + q =
      (w - (A + B) / 3) * (w - (ω * A + ω ^ 2 * B) / 3) * (w - (ω ^ 2 * A + ω * B) / 3) := by
  linear_combination (w / 3) * hAB + (1 / 27) * hsum - (w - (A + B) / 3) *
    (-w * (A / 3 + B / 3) + (ω - 1) * (A / 3) ^ 2 + (ω ^ 2 - ω + 1) * (A / 3) * (B / 3) +
      (ω - 1) * (B / 3) ^ 2) * hω

/-- **DLMF 1.11.13–1.11.14**: with `√(−3D)` any square root `s` of `−3D`,
`A = ∛(−27q/2 + 3s/2)` any cube root (`A ≠ 0`) and `B = −3p/A`, the roots of `w³ + pw + q = 0`
are `(A + B)/3`, `(ρA + ρ²B)/3`, `(ρ²A + ρB)/3`. -/
theorem dlmf_1_11_14 {p q s A : ℂ} (hs : s ^ 2 = -3 * cubicD p q)
    (hA : A ^ 3 = -27 / 2 * q + 3 / 2 * s) (hA0 : A ≠ 0) (w : ℂ) :
    w ^ 3 + p * w + q = (w - (A + -3 * p / A) / 3) *
      (w - (exp (2 * π * I / 3) * A + exp (2 * π * I / 3) ^ 2 * (-3 * p / A)) / 3) *
      (w - (exp (2 * π * I / 3) ^ 2 * A + exp (2 * π * I / 3) * (-3 * p / A)) / 3) := by
  have hX : A ^ 6 + 27 * q * A ^ 3 - 27 * p ^ 3 = 0 := by
    unfold cubicD at hs
    linear_combination (A ^ 3 + (-27 / 2 * q + 3 / 2 * s) + 27 * q) * hA + (9 / 4) * hs
  refine cubic_factor dlmf_1_11_15.2.2 (by field_simp) ?_ w
  field_simp
  linear_combination hX

/-- DLMF §1.11(iii): adding `−a/3` gives the roots of `z³ + az² + bz + c = 0`. -/
theorem dlmf_1_11_iii_cubic_roots {a b c s A : ℂ}
    (hs : s ^ 2 = -3 * cubicD (cubicP a b) (cubicQ a b c))
    (hA : A ^ 3 = -27 / 2 * cubicQ a b c + 3 / 2 * s) (hA0 : A ≠ 0) (z : ℂ) :
    let B := -3 * cubicP a b / A
    let ρ := exp (2 * π * I / 3)
    z ^ 3 + a * z ^ 2 + b * z + c =
      (z - ((A + B) / 3 - a / 3)) * (z - ((ρ * A + ρ ^ 2 * B) / 3 - a / 3)) *
        (z - ((ρ ^ 2 * A + ρ * B) / 3 - a / 3)) := by
  intro B ρ
  have h := dlmf_1_11_14 hs hA hA0 (z + a / 3)
  have hr := dlmf_1_11_iii_cubic_reduce a b c (z + a / 3)
  simp only [add_sub_cancel_right] at hr
  rw [hr, h]
  ring

/-- **Example** (DLMF §1.11(iii)): `f(z) = z³ − 6z² + 6z − 2` reduces to `g(w) = w³ − 6w − 6`,
`A = 3∛4`, `B = 3∛2`, and the roots of `f(z) = 0` are `2 + ∛4 + ∛2`, `2 + ∛4 ρ + ∛2 ρ²`,
`2 + ∛4 ρ² + ∛2 ρ`. -/
theorem dlmf_1_11_iii_cubic_example :
    let c₂ : ℝ := (2 : ℝ) ^ ((3 : ℝ)⁻¹)
    let c₄ : ℝ := (4 : ℝ) ^ ((3 : ℝ)⁻¹)
    let ρ := exp (2 * π * I / 3)
    cubicP (-6) 6 = -6 ∧ cubicQ (-6) 6 (-2) = -6 ∧
    (3 * c₄ : ℂ) ^ 3 = -27 / 2 * (-6) + 3 / 2 * 18 ∧ (18 : ℂ) ^ 2 = -3 * cubicD (-6) (-6) ∧
    -3 * (-6) / (3 * c₄ : ℂ) = 3 * c₂ ∧
    ∀ z : ℂ, z ^ 3 - 6 * z ^ 2 + 6 * z - 2 =
      (z - (2 + c₄ + c₂)) * (z - (2 + c₄ * ρ + c₂ * ρ ^ 2)) * (z - (2 + c₄ * ρ ^ 2 + c₂ * ρ)) := by
  intro c₂ c₄ ρ
  have h2 : c₂ ^ 3 = 2 := by
    have := Real.rpow_inv_natCast_pow (x := 2) (n := 3) (by norm_num) (by norm_num)
    simpa using this
  have hc₂ : 0 < c₂ := by positivity
  have h4 : c₄ = c₂ ^ 2 := by
    have h4' : c₄ ^ 3 = 4 := by
      have := Real.rpow_inv_natCast_pow (x := 4) (n := 3) (by norm_num) (by norm_num)
      simpa using this
    refine (pow_left_inj₀ (by positivity) (by positivity) (by norm_num : (3 : ℕ) ≠ 0)).mp ?_
    rw [h4', ← pow_mul, show 2 * 3 = 3 * 2 by rfl, pow_mul, h2]
    norm_num
  have h2c : (c₂ : ℂ) ^ 3 = 2 := by exact_mod_cast h2
  have h4c : (c₄ : ℂ) = (c₂ : ℂ) ^ 2 := by exact_mod_cast h4
  have hc0 : (c₂ : ℂ) ≠ 0 := by exact_mod_cast hc₂.ne'
  refine ⟨by unfold cubicP; norm_num, by unfold cubicQ; norm_num, ?_, by unfold cubicD; norm_num,
    ?_, fun z => ?_⟩
  · rw [h4c]
    linear_combination (27 * (c₂ : ℂ) ^ 3 + 54) * h2c
  · rw [h4c]
    field_simp
    linear_combination (-3 : ℂ) * h2c
  · have hω := dlmf_1_11_15.2.2
    have := cubic_factor (p := -6) (q := -6) (A := 3 * c₂ ^ 2) (B := 3 * c₂) hω
      (by linear_combination 9 * h2c) (by linear_combination (27 * (c₂ : ℂ) ^ 3 + 81) * h2c)
      (z - 2)
    rw [h4c]
    linear_combination this

/-! ### Quartic equations -/

/-- `p = (−3a² + 8b)/8`. -/
noncomputable def quarticP (a b : ℂ) : ℂ := (-3 * a ^ 2 + 8 * b) / 8

/-- `q = (a³ − 4ab + 8c)/8`. -/
noncomputable def quarticQ (a b c : ℂ) : ℂ := (a ^ 3 - 4 * a * b + 8 * c) / 8

/-- `r = (−3a⁴ + 16a²b − 64ac + 256d)/256`. -/
noncomputable def quarticR (a b c d : ℂ) : ℂ :=
  (-3 * a ^ 4 + 16 * a ^ 2 * b - 64 * a * c + 256 * d) / 256

/-- **DLMF 1.11.17**: the discriminant of `w⁴ + pw² + qw + r`. -/
def quarticD (p q r : ℂ) : ℂ :=
  16 * p ^ 4 * r - 4 * p ^ 3 * q ^ 2 - 128 * p ^ 2 * r ^ 2 + 144 * p * q ^ 2 * r - 27 * q ^ 4 +
    256 * r ^ 3

/-- **DLMF 1.11.16**: `z = w − a/4` reduces `z⁴ + az³ + bz² + cz + d` to `w⁴ + pw² + qw + r`. -/
theorem dlmf_1_11_16 (a b c d w : ℂ) :
    (w - a / 4) ^ 4 + a * (w - a / 4) ^ 3 + b * (w - a / 4) ^ 2 + c * (w - a / 4) + d =
      w ^ 4 + quarticP a b * w ^ 2 + quarticQ a b c * w + quarticR a b c d := by
  unfold quarticP quarticQ quarticR
  ring

/-- **DLMF 1.11.17**: if `α₁, …, α₄` are the roots of `g(w) = w⁴ + pw² + qw + r`, then
`D = ∏_{i<j} (αᵢ − αⱼ)²`. -/
theorem dlmf_1_11_17 {p q r α₁ α₂ α₃ α₄ : ℂ}
    (h : ∀ w, w ^ 4 + p * w ^ 2 + q * w + r = (w - α₁) * (w - α₂) * (w - α₃) * (w - α₄)) :
    quarticD p q r = ((α₁ - α₂) * (α₁ - α₃) * (α₁ - α₄) * (α₂ - α₃) * (α₂ - α₄) *
      (α₃ - α₄)) ^ 2 := by
  obtain ⟨h1, h2, h3, h4⟩ := cubic_coeffs_eq_zero (c3 := α₁ + α₂ + α₃ + α₄)
    (c2 := p - (α₁ * α₂ + α₁ * α₃ + α₁ * α₄ + α₂ * α₃ + α₂ * α₄ + α₃ * α₄))
    (c1 := q + (α₁ * α₂ * α₃ + α₁ * α₂ * α₄ + α₁ * α₃ * α₄ + α₂ * α₃ * α₄))
    (c0 := r - α₁ * α₂ * α₃ * α₄) fun w => by linear_combination h w
  obtain rfl : α₄ = -α₁ - α₂ - α₃ := by linear_combination h1
  rw [quarticD, show p = α₁ * α₂ + α₁ * α₃ + α₁ * (-α₁ - α₂ - α₃) + α₂ * α₃ +
      α₂ * (-α₁ - α₂ - α₃) + α₃ * (-α₁ - α₂ - α₃) by linear_combination h2,
    show q = -(α₁ * α₂ * α₃ + α₁ * α₂ * (-α₁ - α₂ - α₃) + α₁ * α₃ * (-α₁ - α₂ - α₃) +
      α₂ * α₃ * (-α₁ - α₂ - α₃)) by linear_combination h3,
    show r = α₁ * α₂ * α₃ * (-α₁ - α₂ - α₃) by linear_combination h4]
  ring

/-- **DLMF 1.11.18–1.11.19**: if `θ₁, θ₂, θ₃` are the roots of the resolvent cubic
`z³ − 2pz² + (p² − 4r)z + q² = 0` and `√−θⱼ` are square roots with
`√−θ₁ √−θ₂ √−θ₃ = −q` (1.11.20), then the roots of `w⁴ + pw² + qw + r = 0` are
`α₁ = (√−θ₁ + √−θ₂ + √−θ₃)/2`, `α₂ = (√−θ₁ − √−θ₂ − √−θ₃)/2`, `α₃ = (−√−θ₁ + √−θ₂ − √−θ₃)/2`,
`α₄ = (−√−θ₁ − √−θ₂ + √−θ₃)/2`. -/
theorem dlmf_1_11_19 {p q r θ₁ θ₂ θ₃ s₁ s₂ s₃ : ℂ}
    (hθ : ∀ z, z ^ 3 - 2 * p * z ^ 2 + (p ^ 2 - 4 * r) * z + q ^ 2 =
      (z - θ₁) * (z - θ₂) * (z - θ₃))
    (h₁ : s₁ ^ 2 = -θ₁) (h₂ : s₂ ^ 2 = -θ₂) (h₃ : s₃ ^ 2 = -θ₃) (hprod : s₁ * s₂ * s₃ = -q)
    (w : ℂ) :
    w ^ 4 + p * w ^ 2 + q * w + r =
      (w - (s₁ + s₂ + s₃) / 2) * (w - (s₁ - s₂ - s₃) / 2) * (w - (-s₁ + s₂ - s₃) / 2) *
        (w - (-s₁ - s₂ + s₃) / 2) := by
  obtain ⟨-, e1, e2, -⟩ := cubic_coeffs_eq_zero (c3 := 0) (c2 := θ₁ + θ₂ + θ₃ - 2 * p)
    (c1 := p ^ 2 - 4 * r - (θ₁ * θ₂ + θ₁ * θ₃ + θ₂ * θ₃)) (c0 := q ^ 2 + θ₁ * θ₂ * θ₃)
    fun z => by linear_combination hθ z
  have hS : s₁ ^ 2 + s₂ ^ 2 + s₃ ^ 2 = -2 * p := by linear_combination h₁ + h₂ + h₃ - e1
  have hP : s₁ ^ 2 * s₂ ^ 2 + s₁ ^ 2 * s₃ ^ 2 + s₂ ^ 2 * s₃ ^ 2 = p ^ 2 - 4 * r := by
    rw [h₁, h₂, h₃]
    linear_combination -e2
  linear_combination (w ^ 2 / 2 - (s₁ ^ 2 + s₂ ^ 2 + s₃ ^ 2 - 2 * p) / 16) * hS + w * hprod +
    (1 / 4) * hP

/-- **DLMF 1.11.20**: the square roots can always be chosen with `√−θ₁ √−θ₂ √−θ₃ = −q`. -/
theorem dlmf_1_11_20 {p q r θ₁ θ₂ θ₃ t₁ t₂ t₃ : ℂ}
    (hθ : ∀ z, z ^ 3 - 2 * p * z ^ 2 + (p ^ 2 - 4 * r) * z + q ^ 2 =
      (z - θ₁) * (z - θ₂) * (z - θ₃))
    (h₁ : t₁ ^ 2 = -θ₁) (h₂ : t₂ ^ 2 = -θ₂) (h₃ : t₃ ^ 2 = -θ₃) :
    ∃ s₃, s₃ ^ 2 = -θ₃ ∧ t₁ * t₂ * s₃ = -q := by
  obtain ⟨-, -, -, e3⟩ := cubic_coeffs_eq_zero (c3 := 0) (c2 := θ₁ + θ₂ + θ₃ - 2 * p)
    (c1 := p ^ 2 - 4 * r - (θ₁ * θ₂ + θ₁ * θ₃ + θ₂ * θ₃)) (c0 := q ^ 2 + θ₁ * θ₂ * θ₃)
    fun z => by linear_combination hθ z
  have hsq : (t₁ * t₂ * t₃) ^ 2 = q ^ 2 := by
    rw [mul_pow, mul_pow, h₁, h₂, h₃]
    linear_combination -e3
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with h | h
  · exact ⟨-t₃, by rw [neg_sq, h₃], by linear_combination -h⟩
  · exact ⟨t₃, h₃, h⟩

/-- **Example** (DLMF §1.11(iii)): `f(z) = z⁴ − 4z³ + 5z + 2` reduces to
`g(w) = w⁴ − 6w² − 3w + 4`; the resolvent cubic `z³ + 12z² + 20z + 9 = 0` has roots
`θ₁ = −1`, `θ₂,₃ = −(11 ± √85)/2`, with `√−θ₁ = 1`, `√−θ₂,₃ = (√17 ± √5)/2`; the roots of
`f(z) = 0` are `(3 ± √17)/2` and `(1 ± √5)/2`. -/
theorem dlmf_1_11_iii_quartic_example :
    quarticP (-4) 0 = -6 ∧ quarticQ (-4) 0 5 = -3 ∧ quarticR (-4) 0 5 2 = 4 ∧
    (∀ z : ℝ, z ^ 3 + 12 * z ^ 2 + 20 * z + 9 =
      (z + 1) * (z + (11 + √85) / 2) * (z + (11 - √85) / 2)) ∧
    √(-(-1 : ℝ)) = 1 ∧ √((11 + √85) / 2) = (√17 + √5) / 2 ∧
    √((11 - √85) / 2) = (√17 - √5) / 2 ∧ 1 * ((√17 + √5) / 2) * ((√17 - √5) / 2) = -(-3 : ℝ) ∧
    ∀ z : ℝ, z ^ 4 - 4 * z ^ 3 + 5 * z + 2 =
      (z - (3 + √17) / 2) * (z - (3 - √17) / 2) * (z - (1 + √5) / 2) * (z - (1 - √5) / 2) := by
  have h85 : √85 ^ 2 = 85 := Real.sq_sqrt (by norm_num)
  have h17 : √17 ^ 2 = 17 := Real.sq_sqrt (by norm_num)
  have h5 : √5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hm : √17 * √5 = √85 := by rw [← Real.sqrt_mul (by norm_num)]; norm_num
  have h17_5 : √5 < √17 := Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  refine ⟨by unfold quarticP; norm_num, by unfold quarticQ; norm_num,
    by unfold quarticR; norm_num, fun z => by linear_combination ((z + 1) / 4) * h85,
    by norm_num, ?_, ?_, by linear_combination (1 / 4) * h17 - (1 / 4) * h5, fun z => ?_⟩
  · rw [show (11 + √85) / 2 = ((√17 + √5) / 2) ^ 2 by
      linear_combination (-1 / 4) * h17 - (1 / 4) * h5 - (1 / 2) * hm]
    exact Real.sqrt_sq (by positivity)
  · rw [show (11 - √85) / 2 = ((√17 - √5) / 2) ^ 2 by
      linear_combination (-1 / 4) * h17 - (1 / 4) * h5 + (1 / 2) * hm]
    exact Real.sqrt_sq (by linarith)
  · have hA : (z - (3 + √17) / 2) * (z - (3 - √17) / 2) = z ^ 2 - 3 * z - 2 := by
      linear_combination (-1 / 4) * h17
    have hB : (z - (1 + √5) / 2) * (z - (1 - √5) / 2) = z ^ 2 - z - 1 := by
      linear_combination (-1 / 4) * h5
    rw [show (z - (3 + √17) / 2) * (z - (3 - √17) / 2) * (z - (1 + √5) / 2) * (z - (1 - √5) / 2) =
      ((z - (3 + √17) / 2) * (z - (3 - √17) / 2)) * ((z - (1 + √5) / 2) * (z - (1 - √5) / 2)) by
        ring, hA, hB]
    ring

end Azurite.DLMF
