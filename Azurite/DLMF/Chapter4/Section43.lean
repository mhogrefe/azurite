/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

/-!
# DLMF §4.43 Cubic Equations

"Let `p (≠ 0)` and `q` be real constants and `A = (−⁴⁄₃p)^{1/2}`, `B = (⁴⁄₃p)^{1/2}`" (4.43.1;
in each case the radicand is positive and the principal root is the real `√`). The roots of
`z³ + pz + q = 0` (4.43.2) are stated as the factorization
`z³ + pz + q = (z − z₁)(z − z₂)(z − z₃)`, for every `z ∈ ℂ`.

* The three factorizations hold for any complex `A`, `a` (`cubic_sin_roots`, `cubic_cosh_roots`,
  `cubic_sinh_roots`), by Vieta: the sum, pairwise products and product of the roots are `0`,
  `p`, `−q`, from the addition formulas at `⅔π`, `⁴⁄₃π` and the triple-angle formulas.
* Case (a), `4p³ + 27q² ≤ 0` (then `p < 0`): `dlmf_4_43_2_a`. A real `a` with
  `sin(3a) = 4q/A³` exists (`|4q/A³|² = 27q²/(−4p³) ≤ 1`, `cubic_ratio_sq`), and all the roots are
  real.
* Case (b), `p < 0`, `q < 0`, `4p³ + 27q² > 0`: `dlmf_4_43_2_b`, with a real `a`
  (`cosh(3a) = −4q/A³ > 1`); one real root and a conjugate pair of nonreal roots.
* Case (c), `p > 0`: `dlmf_4_43_2_c`, with `a = ⅓ arsinh(−4q/B³)`; one real root and a conjugate
  pair of nonreal roots.

The page records an erratum (V1.0.10, reported 2014-10-31) that rewrote these cases; the
corrected version is the one formalized here.
-/

open Complex
open scoped Real

namespace Azurite.DLMF

/-! ### The angles `⅔π`, `⁴⁄₃π` -/

theorem cos_two_thirds_pi : Complex.cos (2 / 3 * π) = -(1 / 2) := by
  rw [show (2 / 3 * (π : ℂ)) = ((π - π / 3 : ℝ) : ℂ) by push_cast; ring, ← ofReal_cos,
    Real.cos_pi_sub, Real.cos_pi_div_three]
  push_cast; ring

theorem sin_two_thirds_pi : Complex.sin (2 / 3 * π) = (√3 : ℝ) / 2 := by
  rw [show (2 / 3 * (π : ℂ)) = ((π - π / 3 : ℝ) : ℂ) by push_cast; ring, ← ofReal_sin,
    Real.sin_pi_sub, Real.sin_pi_div_three]
  push_cast; ring

theorem cos_four_thirds_pi : Complex.cos (4 / 3 * π) = -(1 / 2) := by
  rw [show (4 / 3 * (π : ℂ)) = ((π / 3 + π : ℝ) : ℂ) by push_cast; ring, ← ofReal_cos,
    Real.cos_add_pi, Real.cos_pi_div_three]
  push_cast; ring

theorem sin_four_thirds_pi : Complex.sin (4 / 3 * π) = -((√3 : ℝ) / 2) := by
  rw [show (4 / 3 * (π : ℂ)) = ((π / 3 + π : ℝ) : ℂ) by push_cast; ring, ← ofReal_sin,
    Real.sin_add_pi, Real.sin_pi_div_three]
  push_cast; ring

theorem sqrt_three_sq_complex : ((√3 : ℝ) : ℂ) ^ 2 = 3 := by
  rw [← ofReal_pow, Real.sq_sqrt (by norm_num)]; norm_num

/-! ### The three factorizations -/

/-- If `p = −¾A²` and `A³ sin 3a = 4q`, the roots of `z³ + pz + q` are `A sin a`,
`A sin(a + ⅔π)`, `A sin(a + ⁴⁄₃π)`. -/
theorem cubic_sin_roots {A a p q : ℂ} (hp : p = -(3 / 4) * A ^ 2)
    (hq : A ^ 3 * Complex.sin (3 * a) = 4 * q) (z : ℂ) :
    z ^ 3 + p * z + q = (z - A * Complex.sin a) * (z - A * Complex.sin (a + 2 / 3 * π)) *
      (z - A * Complex.sin (a + 4 / 3 * π)) := by
  rw [Complex.sin_add, Complex.sin_add, cos_two_thirds_pi, sin_two_thirds_pi, cos_four_thirds_pi,
    sin_four_thirds_pi, hp]
  have hs := Complex.sin_sq_add_cos_sq a
  have h3 := Complex.sin_three_mul a
  have ht := sqrt_three_sq_complex
  set s := Complex.sin a
  set c := Complex.cos a
  set t : ℂ := ((√3 : ℝ) : ℂ)
  linear_combination (A ^ 2 * z * c ^ 2 / 4 - A ^ 3 * s * c ^ 2 / 4) * ht +
    (3 / 4 * A ^ 2 * z - 3 / 4 * A ^ 3 * s) * hs + A ^ 3 / 4 * h3 - 1 / 4 * hq

/-- If `p = −¾A²` and `A³ cosh 3a = −4q`, the roots of `z³ + pz + q` are `A cosh a`,
`A cosh(a + ⅔πi)`, `A cosh(a + ⁴⁄₃πi)`. -/
theorem cubic_cosh_roots {A a p q : ℂ} (hp : p = -(3 / 4) * A ^ 2)
    (hq : A ^ 3 * Complex.cosh (3 * a) = -(4 * q)) (z : ℂ) :
    z ^ 3 + p * z + q = (z - A * Complex.cosh a) * (z - A * Complex.cosh (a + 2 / 3 * π * I)) *
      (z - A * Complex.cosh (a + 4 / 3 * π * I)) := by
  rw [Complex.cosh_add, Complex.cosh_add, Complex.cosh_mul_I,
    Complex.cosh_mul_I, Complex.sinh_mul_I, Complex.sinh_mul_I, cos_two_thirds_pi,
    sin_two_thirds_pi, cos_four_thirds_pi, sin_four_thirds_pi, hp]
  have hc := Complex.cosh_sq_sub_sinh_sq a
  have h3 := Complex.cosh_three_mul a
  have ht := sqrt_three_sq_complex
  set S := Complex.sinh a
  set C := Complex.cosh a
  set t : ℂ := ((√3 : ℝ) : ℂ)
  linear_combination ((A ^ 2 * z * S ^ 2 / 4 - A ^ 3 * C * S ^ 2 / 4) * I ^ 2) * ht +
    (3 * (A ^ 2 * z * S ^ 2 / 4 - A ^ 3 * C * S ^ 2 / 4)) * I_sq +
    (3 / 4 * A ^ 2 * z - 3 / 4 * A ^ 3 * C) * hc - A ^ 3 / 4 * h3 + 1 / 4 * hq

/-- If `p = ¾B²` and `B³ sinh 3a = −4q`, the roots of `z³ + pz + q` are `B sinh a`,
`B sinh(a + ⅔πi)`, `B sinh(a + ⁴⁄₃πi)`. -/
theorem cubic_sinh_roots {B a p q : ℂ} (hp : p = 3 / 4 * B ^ 2)
    (hq : B ^ 3 * Complex.sinh (3 * a) = -(4 * q)) (z : ℂ) :
    z ^ 3 + p * z + q = (z - B * Complex.sinh a) * (z - B * Complex.sinh (a + 2 / 3 * π * I)) *
      (z - B * Complex.sinh (a + 4 / 3 * π * I)) := by
  rw [Complex.sinh_add, Complex.sinh_add, Complex.cosh_mul_I,
    Complex.cosh_mul_I, Complex.sinh_mul_I, Complex.sinh_mul_I, cos_two_thirds_pi,
    sin_two_thirds_pi, cos_four_thirds_pi, sin_four_thirds_pi, hp]
  have hc := Complex.cosh_sq_sub_sinh_sq a
  have h3 := Complex.sinh_three_mul a
  have ht := sqrt_three_sq_complex
  set S := Complex.sinh a
  set C := Complex.cosh a
  set t : ℂ := ((√3 : ℝ) : ℂ)
  linear_combination ((B ^ 2 * z * C ^ 2 / 4 - B ^ 3 * S * C ^ 2 / 4) * I ^ 2) * ht +
    (3 * (B ^ 2 * z * C ^ 2 / 4 - B ^ 3 * S * C ^ 2 / 4)) * I_sq +
    (-(3 / 4) * B ^ 2 * z + 3 / 4 * B ^ 3 * S) * hc - B ^ 3 / 4 * h3 + 1 / 4 * hq

/-! ### DLMF 4.43.1–4.43.2 -/

/-- `A = (−⁴⁄₃p)^{1/2}` for `p < 0`: `A > 0`, `A² = −⁴⁄₃p`. -/
theorem cubic_A_props {p : ℝ} (hp : p < 0) :
    0 < √(-(4 / 3) * p) ∧ √(-(4 / 3) * p) ^ 2 = -(4 / 3) * p :=
  ⟨Real.sqrt_pos.mpr (by linarith), Real.sq_sqrt (by linarith)⟩

/-- `(4q/A³)² = 27q²/(−4p³)` for `A = (−⁴⁄₃p)^{1/2}`, `p < 0`. -/
theorem cubic_ratio_sq {p q : ℝ} (hp : p < 0) :
    (4 * q / √(-(4 / 3) * p) ^ 3) ^ 2 * (-(4 * p ^ 3)) = 27 * q ^ 2 := by
  obtain ⟨hA, hA2⟩ := cubic_A_props hp
  have h6 : (√(-(4 / 3) * p) ^ 3) ^ 2 = (-(4 / 3) * p) ^ 3 := by
    rw [← pow_mul, show 3 * 2 = 2 * 3 by rfl, pow_mul, hA2]
  rw [div_pow, h6]
  have : (-(4 / 3) * p) ^ 3 ≠ 0 := pow_ne_zero 3 (by linarith)
  have hp0 : p ≠ 0 := hp.ne
  field_simp
  ring

/-- **DLMF 4.43.1–4.43.2, case (a)**: for real `p ≠ 0`, `q` with `4p³ + 27q² ≤ 0`, the roots of
`z³ + pz + q = 0` are `A sin a`, `A sin(a + ⅔π)`, `A sin(a + ⁴⁄₃π)`, `A = (−⁴⁄₃p)^{1/2}`, with
`sin(3a) = 4q/A³`. A real such `a` exists, and then all the roots are real. -/
theorem dlmf_4_43_2_a {p q : ℝ} (hp0 : p ≠ 0) (hd : 4 * p ^ 3 + 27 * q ^ 2 ≤ 0) :
    (∃ a : ℝ, Real.sin (3 * a) = 4 * q / √(-(4 / 3) * p) ^ 3) ∧
      ∀ a : ℝ, Real.sin (3 * a) = 4 * q / √(-(4 / 3) * p) ^ 3 → ∀ z : ℂ,
        z ^ 3 + p * z + q = (z - (√(-(4 / 3) * p) * Real.sin a : ℝ)) *
          (z - (√(-(4 / 3) * p) * Real.sin (a + 2 / 3 * π) : ℝ)) *
          (z - (√(-(4 / 3) * p) * Real.sin (a + 4 / 3 * π) : ℝ)) := by
  have hp : p < 0 := by
    rcases lt_or_gt_of_ne hp0 with h | h
    · exact h
    · nlinarith [pow_pos h 3, sq_nonneg q]
  obtain ⟨hA, hA2⟩ := cubic_A_props hp
  have hp3 : 0 < -(4 * p ^ 3) := by nlinarith [Odd.pow_neg (by decide : Odd 3) hp]
  have hrat := cubic_ratio_sq (q := q) hp
  set A := √(-(4 / 3) * p)
  refine ⟨?_, fun a ha z => ?_⟩
  · set x := 4 * q / A ^ 3
    have hx : x ^ 2 ≤ 1 := le_of_mul_le_mul_right (by linarith) hp3
    obtain ⟨h1, h2⟩ := abs_le.mp ((sq_le_one_iff_abs_le_one x).mp hx)
    exact ⟨Real.arcsin x / 3, by rw [mul_div_cancel₀ _ (by norm_num), Real.sin_arcsin h1 h2]⟩
  · have hp' : (p : ℂ) = -(3 / 4) * (A : ℂ) ^ 2 := by
      have : p = -(3 / 4) * A ^ 2 := by linarith
      have h := congrArg (fun r : ℝ => (r : ℂ)) this
      push_cast at h
      exact h
    have hq' : (A : ℂ) ^ 3 * Complex.sin (3 * (a : ℂ)) = 4 * q := by
      have : A ^ 3 * Real.sin (3 * a) = 4 * q := by
        rw [ha]; field_simp
      exact_mod_cast this
    have h := cubic_sin_roots hp' hq' z
    push_cast
    exact h

theorem cosh_add_thirds (x : ℝ) :
    Complex.cosh (x + 2 / 3 * π * I) = (-(Real.cosh x / 2) : ℝ) + (Real.sinh x * √3 / 2 : ℝ) * I ∧
      Complex.cosh (x + 4 / 3 * π * I) =
        (-(Real.cosh x / 2) : ℝ) - (Real.sinh x * √3 / 2 : ℝ) * I := by
  constructor <;>
  · rw [Complex.cosh_add, Complex.cosh_mul_I, Complex.sinh_mul_I]
    simp only [cos_two_thirds_pi, sin_two_thirds_pi, cos_four_thirds_pi, sin_four_thirds_pi,
      ← ofReal_cosh, ← ofReal_sinh]
    push_cast; ring

theorem sinh_add_thirds (x : ℝ) :
    Complex.sinh (x + 2 / 3 * π * I) = (-(Real.sinh x / 2) : ℝ) + (Real.cosh x * √3 / 2 : ℝ) * I ∧
      Complex.sinh (x + 4 / 3 * π * I) =
        (-(Real.sinh x / 2) : ℝ) - (Real.cosh x * √3 / 2 : ℝ) * I := by
  constructor <;>
  · rw [Complex.sinh_add, Complex.cosh_mul_I, Complex.sinh_mul_I]
    simp only [cos_two_thirds_pi, sin_two_thirds_pi, cos_four_thirds_pi, sin_four_thirds_pi,
      ← ofReal_cosh, ← ofReal_sinh]
    push_cast; ring

theorem conj_ofReal_mul_add_mul_I (A u v : ℝ) :
    starRingEnd ℂ ((A : ℂ) * ((u : ℂ) + (v : ℂ) * I)) = (A : ℂ) * ((u : ℂ) - (v : ℂ) * I) ∧
      ((A : ℂ) * ((u : ℂ) + (v : ℂ) * I)).im = A * v := by
  constructor
  · rw [map_mul, map_add, map_mul, Complex.conj_ofReal, Complex.conj_ofReal, Complex.conj_ofReal,
      Complex.conj_I]
    ring
  · simp

/-- **DLMF 4.43.1–4.43.2, case (b)**: for real `p < 0`, `q < 0` with `4p³ + 27q² > 0`, the roots
of `z³ + pz + q = 0` are `A cosh a`, `A cosh(a + ⅔πi)`, `A cosh(a + ⁴⁄₃πi)`,
`A = (−⁴⁄₃p)^{1/2}`, with `cosh(3a) = −4q/A³`. A real such `a` exists; then `A cosh a` is real and
the other two roots are a conjugate pair of nonreal numbers. -/
theorem dlmf_4_43_2_b {p q : ℝ} (hp : p < 0) (hq : q < 0) (hd : 0 < 4 * p ^ 3 + 27 * q ^ 2) :
    (∃ a : ℝ, Real.cosh (3 * a) = -(4 * q) / √(-(4 / 3) * p) ^ 3) ∧
      ∀ a : ℝ, Real.cosh (3 * a) = -(4 * q) / √(-(4 / 3) * p) ^ 3 →
        (∀ z : ℂ, z ^ 3 + p * z + q = (z - (√(-(4 / 3) * p) * Real.cosh a : ℝ)) *
          (z - (√(-(4 / 3) * p) : ℝ) * Complex.cosh (a + 2 / 3 * π * I)) *
          (z - (√(-(4 / 3) * p) : ℝ) * Complex.cosh (a + 4 / 3 * π * I))) ∧
        starRingEnd ℂ ((√(-(4 / 3) * p) : ℝ) * Complex.cosh (a + 2 / 3 * π * I)) =
          (√(-(4 / 3) * p) : ℝ) * Complex.cosh (a + 4 / 3 * π * I) ∧
        ((√(-(4 / 3) * p) : ℝ) * Complex.cosh (a + 2 / 3 * π * I)).im ≠ 0 := by
  obtain ⟨hA, hA2⟩ := cubic_A_props hp
  have hp3 : 0 < -(4 * p ^ 3) := by nlinarith [Odd.pow_neg (by decide : Odd 3) hp]
  have hrat := cubic_ratio_sq (q := q) hp
  set A := √(-(4 / 3) * p)
  have hx1 : 1 < -(4 * q) / A ^ 3 := by
    have hpos : 0 < -(4 * q) / A ^ 3 := div_pos (by linarith) (by positivity)
    have hsq : 1 < (-(4 * q) / A ^ 3) ^ 2 := by
      rw [neg_div, neg_sq]
      exact lt_of_mul_lt_mul_right (by linarith) hp3.le
    nlinarith
  refine ⟨⟨Real.arcosh (-(4 * q) / A ^ 3) / 3, by
    rw [mul_div_cancel₀ _ (by norm_num), Real.cosh_arcosh hx1.le]⟩,
    fun a ha => ⟨fun z => ?_, ?_, ?_⟩⟩
  · have hp' : (p : ℂ) = -(3 / 4) * (A : ℂ) ^ 2 := by
      have : p = -(3 / 4) * A ^ 2 := by linarith
      have h := congrArg (fun r : ℝ => (r : ℂ)) this
      push_cast at h
      exact h
    have hq' : (A : ℂ) ^ 3 * Complex.cosh (3 * (a : ℂ)) = -(4 * q) := by
      have : A ^ 3 * Real.cosh (3 * a) = -(4 * q) := by
        rw [ha]; field_simp
      exact_mod_cast this
    have h := cubic_cosh_roots hp' hq' z
    push_cast
    exact h
  · obtain ⟨e2, e4⟩ := cosh_add_thirds a
    rw [e2, e4]
    exact (conj_ofReal_mul_add_mul_I _ _ _).1
  · obtain ⟨e2, -⟩ := cosh_add_thirds a
    rw [e2, (conj_ofReal_mul_add_mul_I _ _ _).2]
    have ha0 : a ≠ 0 := by
      rintro rfl
      simp at ha; linarith
    have hs : Real.sinh a ≠ 0 := fun h => ha0 (Real.sinh_eq_zero.mp h)
    have h3 : 0 < √3 := Real.sqrt_pos.mpr (by norm_num)
    exact mul_ne_zero hA.ne' (by positivity)

/-- **DLMF 4.43.1–4.43.2, case (c)**: for real `p > 0`, the roots of `z³ + pz + q = 0` are
`B sinh a`, `B sinh(a + ⅔πi)`, `B sinh(a + ⁴⁄₃πi)`, `B = (⁴⁄₃p)^{1/2}`, with
`sinh(3a) = −4q/B³`. A real such `a` exists; then `B sinh a` is real and the other two roots are a
conjugate pair of nonreal numbers. -/
theorem dlmf_4_43_2_c {p q : ℝ} (hp : 0 < p) :
    (∃ a : ℝ, Real.sinh (3 * a) = -(4 * q) / √(4 / 3 * p) ^ 3) ∧
      ∀ a : ℝ, Real.sinh (3 * a) = -(4 * q) / √(4 / 3 * p) ^ 3 →
        (∀ z : ℂ, z ^ 3 + p * z + q = (z - (√(4 / 3 * p) * Real.sinh a : ℝ)) *
          (z - (√(4 / 3 * p) : ℝ) * Complex.sinh (a + 2 / 3 * π * I)) *
          (z - (√(4 / 3 * p) : ℝ) * Complex.sinh (a + 4 / 3 * π * I))) ∧
        starRingEnd ℂ ((√(4 / 3 * p) : ℝ) * Complex.sinh (a + 2 / 3 * π * I)) =
          (√(4 / 3 * p) : ℝ) * Complex.sinh (a + 4 / 3 * π * I) ∧
        ((√(4 / 3 * p) : ℝ) * Complex.sinh (a + 2 / 3 * π * I)).im ≠ 0 := by
  have hB : 0 < √(4 / 3 * p) := Real.sqrt_pos.mpr (by linarith)
  have hB2 : √(4 / 3 * p) ^ 2 = 4 / 3 * p := Real.sq_sqrt (by linarith)
  set B := √(4 / 3 * p)
  refine ⟨⟨Real.arsinh (-(4 * q) / B ^ 3) / 3, by
    rw [mul_div_cancel₀ _ (by norm_num), Real.sinh_arsinh]⟩, fun a ha => ⟨fun z => ?_, ?_, ?_⟩⟩
  · have hp' : (p : ℂ) = 3 / 4 * (B : ℂ) ^ 2 := by
      have : p = 3 / 4 * B ^ 2 := by linarith
      have h := congrArg (fun r : ℝ => (r : ℂ)) this
      push_cast at h
      exact h
    have hq' : (B : ℂ) ^ 3 * Complex.sinh (3 * (a : ℂ)) = -(4 * q) := by
      have : B ^ 3 * Real.sinh (3 * a) = -(4 * q) := by
        rw [ha]; field_simp
      exact_mod_cast this
    have h := cubic_sinh_roots hp' hq' z
    push_cast
    exact h
  · obtain ⟨e2, e4⟩ := sinh_add_thirds a
    rw [e2, e4]
    exact (conj_ofReal_mul_add_mul_I _ _ _).1
  · obtain ⟨e2, -⟩ := sinh_add_thirds a
    rw [e2, (conj_ofReal_mul_add_mul_I _ _ _).2]
    have h3 : 0 < √3 := Real.sqrt_pos.mpr (by norm_num)
    exact mul_ne_zero hB.ne' (by have := Real.cosh_pos a; positivity)

end Azurite.DLMF
