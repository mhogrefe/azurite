/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.ECPP.Theory.ManinAlgebra
import Mathlib.FieldTheory.RatFunc.AsPolynomial

/-!
# Manin's proof of the Hasse bound: heights of rational functions

`rfHeight r = max(deg num r, deg den r)`, the height of a rational function, and the Basic
Identity in the form in which it does not mention a curve (`rfHeight_add_of_relations`): if
`U`, `V`, `Z` are rational functions with `Z ≠ x` and

  `U V = ((Z x − a)² − 4b (x + Z))/(Z − x)²`,
  `U + V = 2 (Z x² + Z² x + a x + 2b + a Z)/(Z − x)²`

(Knapp, *Elliptic Curves*, (10.20) and (10.19)), then
`rfHeight U + rfHeight V = 2 rfHeight Z + 2`.
-/

namespace Azurite.ECPP.Manin

open Polynomial

variable {k : Type*} [Field k]

/-- **The height of a rational function**: the larger of the degrees of its numerator and its
denominator in lowest terms. -/
noncomputable def rfHeight (r : RatFunc k) : ℕ := max r.num.natDegree r.denom.natDegree

theorem natDegree_mul_of_isUnit_right {p u : k[X]} (hu : IsUnit u) :
    (p * u).natDegree = p.natDegree := by
  obtain ⟨r, hr, rfl⟩ := Polynomial.isUnit_iff.mp hu
  exact natDegree_mul_C hr.ne_zero

theorem natDegree_mul_of_isUnit_left {p u : k[X]} (hu : IsUnit u) :
    (u * p).natDegree = p.natDegree := by
  rw [mul_comm, natDegree_mul_of_isUnit_right hu]

/-- The heights of two fractions in lowest terms add up to the largest of three degrees
(numerators may vanish). -/
theorem height_add_height' {A B C D : k[X]} (hAB : IsCoprime A B) (hCD : IsCoprime C D)
    (hB : B ≠ 0) (hD : D ≠ 0) :
    max A.natDegree B.natDegree + max C.natDegree D.natDegree
      = max (max (A * C).natDegree (B * D).natDegree) (A * D + B * C).natDegree := by
  by_cases hA : A = 0
  · subst hA
    have hBu : IsUnit B := isCoprime_zero_left.mp hAB
    have hB0 : B.natDegree = 0 := natDegree_eq_zero_of_isUnit hBu
    rw [zero_mul, zero_mul, zero_add, natDegree_zero, natDegree_mul_of_isUnit_left hBu,
      natDegree_mul_of_isUnit_left hBu, hB0]
    simp [max_comm]
  · by_cases hC : C = 0
    · subst hC
      have hDu : IsUnit D := isCoprime_zero_left.mp hCD
      have hD0 : D.natDegree = 0 := natDegree_eq_zero_of_isUnit hDu
      rw [mul_zero, mul_zero, add_zero, natDegree_zero, natDegree_mul_of_isUnit_right hDu,
        natDegree_mul_of_isUnit_right hDu, hD0]
      simp [max_comm]
    · exact height_add_height hA hB hC hD

/-- **The Basic Identity for rational functions.** -/
theorem rfHeight_add_of_relations (a b : k) (h2 : (2 : k) ≠ 0)
    (hΔ : 4 * a ^ 3 + 27 * b ^ 2 ≠ 0) {U V Z : RatFunc k} (hZ : Z ≠ RatFunc.X)
    (hprod : U * V = ((Z * RatFunc.X - RatFunc.C a) ^ 2
      - 4 * RatFunc.C b * (RatFunc.X + Z)) / (Z - RatFunc.X) ^ 2)
    (hsum : U + V = 2 * (Z * RatFunc.X ^ 2 + Z ^ 2 * RatFunc.X + RatFunc.C a * RatFunc.X
      + 2 * RatFunc.C b + RatFunc.C a * Z) / (Z - RatFunc.X) ^ 2) :
    rfHeight U + rfHeight V = 2 * rfHeight Z + 2 := by
  obtain ⟨φ, hφ⟩ : ∃ φ : k[X] →+* RatFunc k, φ = algebraMap k[X] (RatFunc k) := ⟨_, rfl⟩
  have hinj : Function.Injective φ := hφ ▸ RatFunc.algebraMap_injective k
  have hφX : φ X = RatFunc.X := by rw [hφ]; exact RatFunc.algebraMap_X
  have hφC : ∀ c : k, φ (C c) = RatFunc.C c := fun c => by rw [hφ]; exact RatFunc.algebraMap_C c
  have hne : ∀ {p : k[X]}, p ≠ 0 → φ p ≠ 0 := fun hp => (map_ne_zero_iff φ hinj).mpr hp
  obtain ⟨P, hP⟩ : ∃ P, P = Z.num := ⟨_, rfl⟩
  obtain ⟨Q, hQ⟩ : ∃ Q, Q = Z.denom := ⟨_, rfl⟩
  obtain ⟨A, hA⟩ : ∃ A, A = U.num := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B, B = U.denom := ⟨_, rfl⟩
  obtain ⟨C', hC⟩ : ∃ C', C' = V.num := ⟨_, rfl⟩
  obtain ⟨D, hD⟩ : ∃ D, D = V.denom := ⟨_, rfl⟩
  have hQ0 : Q ≠ 0 := hQ ▸ Z.denom_ne_zero
  have hB0 : B ≠ 0 := hB ▸ U.denom_ne_zero
  have hD0 : D ≠ 0 := hD ▸ V.denom_ne_zero
  have hPQ : IsCoprime P Q := by rw [hP, hQ]; exact Z.isCoprime_num_denom
  have hAB : IsCoprime A B := by rw [hA, hB]; exact U.isCoprime_num_denom
  have hCD : IsCoprime C' D := by rw [hC, hD]; exact V.isCoprime_num_denom
  have eZ : Z = φ P / φ Q := by rw [hP, hQ, hφ]; exact (RatFunc.num_div_denom Z).symm
  have eU : U = φ A / φ B := by rw [hA, hB, hφ]; exact (RatFunc.num_div_denom U).symm
  have eV : V = φ C' / φ D := by rw [hC, hD, hφ]; exact (RatFunc.num_div_denom V).symm
  have hφQ := hne hQ0
  have hφB := hne hB0
  have hφD := hne hD0
  -- `Qx − P ≠ 0`
  have hM : Q * X - P ≠ 0 := by
    intro h0
    apply hZ
    have : φ P = φ Q * RatFunc.X := by
      rw [← hφX, ← map_mul]
      exact congrArg φ (sub_eq_zero.mp h0).symm
    rw [eZ, this, mul_div_cancel_left₀ _ hφQ]
  have hZX0 : Z - RatFunc.X ≠ 0 := sub_ne_zero.mpr hZ
  -- the two relations between polynomials
  have r1 : A * C' * formM P Q = B * D * formN1 a b P Q := by
    apply hinj
    have h := hprod
    rw [eU, eV, eZ] at h
    simp only [formM, formN1, map_mul, map_pow, map_sub, map_add, hφX, hφC, map_ofNat]
    have hd : φ P / φ Q - RatFunc.X ≠ 0 := by rw [← eZ]; exact hZX0
    field_simp at h
    have hd' : φ P - RatFunc.X * φ Q ≠ 0 := by
      intro h0
      apply hd
      rw [div_sub' hφQ, mul_comm, h0, zero_div]
    field_simp at h ⊢
    linear_combination h
  have r2 : (A * D + B * C') * formM P Q = 2 * (B * D) * formN2 a b P Q := by
    apply hinj
    have h := hsum
    rw [eU, eV, eZ] at h
    simp only [formM, formN2, map_mul, map_pow, map_sub, map_add, hφX, hφC, map_ofNat]
    have hd : φ P / φ Q - RatFunc.X ≠ 0 := by rw [← eZ]; exact hZX0
    field_simp at h
    have hd' : φ P - RatFunc.X * φ Q ≠ 0 := by
      intro h0
      apply hd
      rw [div_sub' hφQ, mul_comm, h0, zero_div]
    field_simp at h ⊢
    linear_combination h
  obtain ⟨T, hT, eM, eN1, eN2⟩ := exists_unit_of_relations h2 hAB hCD hB0 hD0 r1 r2
    (fun T h1 h2' h3 => isUnit_of_dvd_forms a b h2 hΔ hPQ hM h1 h2' h3)
  have hforms := max_natDegree_forms a b (P := P) hQ0
  have d1 : (formN1 a b P Q).natDegree = (A * C').natDegree := by
    rw [eN1, natDegree_mul_of_isUnit_right hT]
  have d2 : (formM P Q).natDegree = (B * D).natDegree := by
    rw [eM, natDegree_mul_of_isUnit_right hT]
  have d3 : (formN2 a b P Q).natDegree = (A * D + B * C').natDegree := by
    have : (2 * formN2 a b P Q).natDegree = (formN2 a b P Q).natDegree :=
      natDegree_mul_of_isUnit_left (isUnit_two h2)
    rw [← this, eN2, natDegree_mul_of_isUnit_right hT]
  unfold rfHeight
  rw [← hA, ← hB, ← hC, ← hD, ← hP, ← hQ, height_add_height' hAB hCD hB0 hD0, ← d1, ← d2, ← d3,
    hforms]

end Azurite.ECPP.Manin
