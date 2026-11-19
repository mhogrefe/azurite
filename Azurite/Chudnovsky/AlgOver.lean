/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.Chudnovsky.Theorem
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.RingTheory.Localization.Integral

/-!
# Algebraicity over `ℚ(ϖ)`

`AlgOver ϖ x`: `x` is a root of a nonzero polynomial in `ℤ[X][Y]` evaluated at `X = ϖ`
(`algOver_iff`), i.e. `x` is algebraic over `ℤ[X]` for the algebra structure `X ↦ ϖ` on `ℂ`.
Mathlib's closure properties of algebraic elements over a domain give `AlgOver.mul`,
`AlgOver.pow`, `AlgOver.of_pow`, `AlgOver.of_poly_mul`.  Chudnovsky's theorem reads
`¬ AlgOver ϖ (℘(1/2))` (`CMData.not_algOver`).
-/

namespace Azurite.Chudnovsky

open Polynomial

/-- `ℂ` as an algebra over `ℤ[X]` through `X ↦ ϖ`. -/
@[reducible] noncomputable def polyAlgebra (ϖ : ℂ) : Algebra ℤ[X] ℂ := (evX ϖ).toAlgebra

/-- `x` is algebraic over `ℤ[ϖ]`. -/
def AlgOver (ϖ x : ℂ) : Prop := @IsAlgebraic ℤ[X] ℂ _ _ (polyAlgebra ϖ) x

variable {ϖ x y : ℂ}

theorem algOver_iff : AlgOver ϖ x ↔ ∃ R : ℤ[X][X], R ≠ 0 ∧ ev2 ϖ x R = 0 := Iff.rfl

theorem AlgOver.mul (hx : AlgOver ϖ x) (hy : AlgOver ϖ y) : AlgOver ϖ (x * y) := by
  let _ := polyAlgebra ϖ
  exact IsAlgebraic.mul hx hy

theorem AlgOver.pow (hx : AlgOver ϖ x) (n : ℕ) : AlgOver ϖ (x ^ n) := by
  let _ := polyAlgebra ϖ
  exact IsAlgebraic.pow hx n

theorem AlgOver.of_pow {n : ℕ} (hn : 0 < n) (hx : AlgOver ϖ (x ^ n)) : AlgOver ϖ x := by
  let _ := polyAlgebra ϖ
  exact IsAlgebraic.of_pow hn hx

theorem algOver_poly (ϖ : ℂ) (q : ℤ[X]) : AlgOver ϖ (evX ϖ q) := by
  let _ := polyAlgebra ϖ
  exact isAlgebraic_algebraMap q

theorem AlgOver.of_poly_mul {q : ℤ[X]} (hq : evX ϖ q ≠ 0) (h : AlgOver ϖ (evX ϖ q * x)) :
    AlgOver ϖ x := by
  let _ := polyAlgebra ϖ
  exact IsAlgebraic.of_mul (mem_nonZeroDivisors_of_ne_zero hq) (isAlgebraic_algebraMap q) h

theorem AlgOver.of_mul (hy0 : y ≠ 0) (hy : AlgOver ϖ y) (h : AlgOver ϖ (y * x)) :
    AlgOver ϖ x := by
  let _ := polyAlgebra ϖ
  exact IsAlgebraic.of_mul (mem_nonZeroDivisors_of_ne_zero hy0) hy h

theorem algOver_one (ϖ : ℂ) : AlgOver ϖ 1 := by
  have h := algOver_poly ϖ 1
  rwa [map_one] at h

theorem AlgOver.inv (hx0 : x ≠ 0) (hx : AlgOver ϖ x) : AlgOver ϖ x⁻¹ :=
  AlgOver.of_mul hx0 hx (by rw [mul_inv_cancel₀ hx0]; exact algOver_one ϖ)

theorem AlgOver.div (hy0 : y ≠ 0) (hx : AlgOver ϖ x) (hy : AlgOver ϖ y) : AlgOver ϖ (x / y) := by
  rw [div_eq_mul_inv]
  exact hx.mul (hy.inv hy0)

theorem algOver_self (ϖ : ℂ) : AlgOver ϖ ϖ := by
  have h := algOver_poly ϖ X
  rwa [evX_apply, aeval_X] at h

/-- Algebraic numbers are algebraic over `ℤ[ϖ]`. -/
theorem algOver_of_isAlgebraic (ϖ : ℂ) (h : IsAlgebraic ℤ x) : AlgOver ϖ x := by
  obtain ⟨p, hp, hx⟩ := h
  refine algOver_iff.mpr ⟨p.map C, ?_, by rw [ev2_map_C]; exact hx⟩
  exact (Polynomial.map_ne_zero_iff C_injective).mpr hp

theorem algOver_ratCast (ϖ : ℂ) (r : ℚ) : AlgOver ϖ (r : ℂ) :=
  algOver_of_isAlgebraic ϖ
    ((IsFractionRing.isAlgebraic_iff ℤ ℚ ℂ).mpr (isAlgebraic_algebraMap (R := ℚ) (A := ℂ) r))

theorem algOver_natCast (ϖ : ℂ) (n : ℕ) : AlgOver ϖ (n : ℂ) := by
  have := algOver_ratCast ϖ (n : ℚ)
  simpa using this

/-- A real number that is not algebraic over `ℤ[ϖ]` is irrational. -/
theorem irrational_of_not_algOver {t : ℝ} (h : ¬ AlgOver ϖ (t : ℂ)) : Irrational t := by
  rintro ⟨r, hr⟩
  apply h
  rw [← hr]
  exact_mod_cast algOver_ratCast ϖ r

/-- **Chudnovsky's theorem**: `℘(1/2)` is not algebraic over `ℤ[ϖ]`. -/
theorem CMData.not_algOver (D : CMData) {c₀ : ℕ} (hϖ : HasMeasure D.ϖ c₀) :
    ¬ AlgOver D.ϖ D.e := by
  rintro ⟨R, hR, h⟩
  exact D.ev2_ne_zero hϖ hR h

end Azurite.Chudnovsky
