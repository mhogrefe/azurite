/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzPolynomial.Equiv.Content
import Azurite.AzPolynomial.Equiv.Derivative
import Azurite.AzPolynomial.Equiv.Gcd
import Azurite.AzPolynomial.Equiv.GcdInt

/-!
# Correctness of the gcd-based predicates

* `coprime_iff` — over a field, `coprime P Q = true ↔ IsCoprime` of the
  represented polynomials;
* `isSquarefree_iff` — over a field, `isSquarefree P = true ↔ Separable`
  of the represented polynomial (separability *is* coprimality with the
  derivative; over characteristic `0` it coincides with squarefreeness);
* `coprime_int_iff` / `isSquarefree_int_iff` — over `AzInt`, the same
  statements for the `ℚ[X]` images (coprimality/separability over the
  fraction field);
* `isPrimitive_int_iff` / `isPrimitive_field_iff` — the primitivity test
  agrees with Mathlib's `Polynomial.IsPrimitive`.
-/

namespace Azurite.AzPolynomial

open Polynomial

attribute [local instance 0] Azurite.BPR.gcdMonoidPolynomial

variable {K : Type _} [Field K] [DecidableEq K]

/-- Over a Euclidean domain, coprimality is the gcd being a unit (stated for
Mathlib's normalized `K[X]` gcd). -/
private theorem isCoprime_iff_isUnit_gcd (A B : K[X]) :
    IsCoprime A B ↔ IsUnit (GCDMonoid.gcd A B) := by
  have hE : Associated (EuclideanDomain.gcd A B) (GCDMonoid.gcd A B) :=
    associated_of_dvd_dvd
      (dvd_gcd (EuclideanDomain.gcd_dvd_left _ _) (EuclideanDomain.gcd_dvd_right _ _))
      (EuclideanDomain.dvd_gcd (gcd_dvd_left _ _) (gcd_dvd_right _ _))
  rw [← EuclideanDomain.gcd_isUnit_iff]
  exact ⟨fun h => hE.isUnit h, fun h => hE.symm.isUnit h⟩

omit [DecidableEq K] in
private theorem isUnit_isCoprime_left {A B : K[X]} (h : IsUnit A) : IsCoprime A B := by
  obtain ⟨u, rfl⟩ := h
  exact ⟨(↑u⁻¹ : K[X]), 0, by simp⟩

omit [DecidableEq K] in
/-- A unit test for `K[X]` in terms of `natDegree` and nonvanishing. -/
private theorem isUnit_iff_natDegree {A : K[X]} :
    IsUnit A ↔ A ≠ 0 ∧ A.natDegree = 0 := by
  rw [Polynomial.isUnit_iff_degree_eq_zero]
  constructor
  · intro h
    have hne : A ≠ 0 := fun h0 => by rw [h0, Polynomial.degree_zero] at h; exact absurd h (by simp)
    exact ⟨hne, Polynomial.natDegree_eq_zero_iff_degree_le_zero.mpr h.le⟩
  · rintro ⟨hne, hdeg⟩
    rw [Polynomial.degree_eq_natDegree hne, hdeg]
    rfl

/-- The main branch: for `deg P > deg Q ≥ 1`, the subresultant gcd is
constant iff the represented polynomials are coprime. -/
private theorem coprime_main {P Q : AzPolynomial K} (hP : P ≠ 0) (hQ : Q ≠ 0)
    (hpq : Q.natDegree < P.natDegree) (hq1 : 1 ≤ Q.natDegree) :
    ((subresGcd P Q).natDegree == 0) = true
      ↔ IsCoprime (AzPolynomial.toPoly P) (AzPolynomial.toPoly Q) := by
  obtain ⟨hassoc, hne⟩ := toPoly_subresGcd_associated P Q hP hQ hpq hq1
  rw [beq_iff_eq, isCoprime_iff_isUnit_gcd]
  constructor
  · intro h
    refine hassoc.isUnit (isUnit_iff_natDegree.mpr ⟨toPoly_ne_zero hne, ?_⟩)
    rw [AzPolynomial.natDegree_toPoly]
    exact h
  · intro h
    have h2 := isUnit_iff_natDegree.mp (hassoc.symm.isUnit h)
    rw [AzPolynomial.natDegree_toPoly] at h2
    exact h2.2

/-- **Correctness of `coprime` over a field**: the test decides Mathlib's
`IsCoprime` of the represented polynomials. -/
theorem coprime_iff (P Q : AzPolynomial K) :
    coprime P Q = true ↔ IsCoprime (AzPolynomial.toPoly P) (AzPolynomial.toPoly Q) := by
  rw [coprime]
  by_cases hP : P = 0
  · subst hP
    rw [ite_eq_left rfl, toPoly_zero, isCoprime_zero_left, isUnit_iff_natDegree]
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨toPoly_ne_zero h1, by rw [AzPolynomial.natDegree_toPoly]; exact h2⟩
    · rintro ⟨h1, h2⟩
      refine ⟨fun h0 => h1 (by rw [h0, toPoly_zero]), ?_⟩
      rw [← AzPolynomial.natDegree_toPoly]
      exact h2
  · rw [ite_eq_right hP]
    by_cases hQ : Q = 0
    · subst hQ
      rw [ite_eq_left rfl, toPoly_zero, isCoprime_zero_right, isUnit_iff_natDegree]
      simp only [beq_iff_eq]
      constructor
      · intro h
        exact ⟨toPoly_ne_zero hP, by rw [AzPolynomial.natDegree_toPoly]; exact h⟩
      · rintro ⟨-, h2⟩
        rw [← AzPolynomial.natDegree_toPoly]
        exact h2
    · rw [ite_eq_right hQ]
      by_cases hconst : P.natDegree = 0 ∨ Q.natDegree = 0
      · rw [ite_eq_left hconst]
        simp only [true_iff]
        rcases hconst with h | h
        · exact isUnit_isCoprime_left (isUnit_iff_natDegree.mpr
            ⟨toPoly_ne_zero hP, by rw [AzPolynomial.natDegree_toPoly]; exact h⟩)
        · exact (isUnit_isCoprime_left (isUnit_iff_natDegree.mpr
            ⟨toPoly_ne_zero hQ, by rw [AzPolynomial.natDegree_toPoly]; exact h⟩)).symm
      · rw [ite_eq_right hconst]
        push Not at hconst
        obtain ⟨hp1, hq1⟩ := hconst
        by_cases hdeq : P.natDegree = Q.natDegree
        · rw [ite_eq_left hdeq]
          have hlcP : P.leadingCoeff ≠ 0 := by
            rw [← leadingCoeff_toPoly]
            exact Polynomial.leadingCoeff_ne_zero.mpr (toPoly_ne_zero hP)
          have hlcQ : Q.leadingCoeff ≠ 0 := by
            rw [← leadingCoeff_toPoly]
            exact Polynomial.leadingCoeff_ne_zero.mpr (toPoly_ne_zero hQ)
          -- the pre-step preserves coprimality
          have hgcd_pre : IsCoprime (AzPolynomial.toPoly P) (AzPolynomial.toPoly (preStep P Q))
              ↔ IsCoprime (AzPolynomial.toPoly P) (AzPolynomial.toPoly Q) := by
            rw [isCoprime_iff_isUnit_gcd, isCoprime_iff_isUnit_gcd]
            rw [show AzPolynomial.toPoly (preStep P Q)
                = Polynomial.C P.leadingCoeff * AzPolynomial.toPoly Q
                  - Polynomial.C Q.leadingCoeff * AzPolynomial.toPoly P from toPoly_pre_step P Q]
            rw [gcd_pre_step _ _ hlcP]
          by_cases hpre : preStep P Q = 0
          · rw [ite_eq_left hpre]
            simp only [Bool.false_eq_true, false_iff]
            -- `preStep = 0` forces `P ∣ Q`, so a coprime pair would make `P` a unit
            intro hco
            have h0 : Polynomial.C P.leadingCoeff * AzPolynomial.toPoly Q
                = Polynomial.C Q.leadingCoeff * AzPolynomial.toPoly P := by
              have h := toPoly_pre_step P Q
              have hpre' : P.leadingCoeff • Q - Q.leadingCoeff • P = 0 := hpre
              rw [hpre', toPoly_zero] at h
              linear_combination -h
            have hdvd : AzPolynomial.toPoly P ∣ AzPolynomial.toPoly Q := by
              refine ⟨Polynomial.C P.leadingCoeff⁻¹ * Polynomial.C Q.leadingCoeff, ?_⟩
              have hCne : (Polynomial.C P.leadingCoeff : K[X]) ≠ 0 := by
                rwa [Ne, Polynomial.C_eq_zero]
              apply mul_left_cancel₀ hCne
              rw [show Polynomial.C P.leadingCoeff * (AzPolynomial.toPoly P
                  * (Polynomial.C P.leadingCoeff⁻¹ * Polynomial.C Q.leadingCoeff))
                = (Polynomial.C P.leadingCoeff * Polynomial.C P.leadingCoeff⁻¹)
                  * (Polynomial.C Q.leadingCoeff * AzPolynomial.toPoly P) from by ring,
                ← Polynomial.C_mul, mul_inv_cancel₀ hlcP, Polynomial.C_1, one_mul, ← h0]
            have hunit := hco.isUnit_of_dvd' dvd_rfl hdvd
            have h2 := (isUnit_iff_natDegree.mp hunit).2
            rw [AzPolynomial.natDegree_toPoly] at h2
            omega
          · rw [ite_eq_right hpre]
            by_cases hpre0 : (preStep P Q).natDegree = 0
            · rw [ite_eq_left hpre0]
              simp only [true_iff]
              rw [← hgcd_pre]
              exact (isUnit_isCoprime_left (isUnit_iff_natDegree.mpr
                ⟨toPoly_ne_zero hpre,
                  by rw [AzPolynomial.natDegree_toPoly]; exact hpre0⟩)).symm
            · rw [ite_eq_right hpre0]
              rw [coprime_main hP hpre
                (pre_step_natDegree_lt hP hQ hdeq hpre) (by omega)]
              exact hgcd_pre
        · rw [ite_eq_right hdeq]
          rcases Nat.lt_or_ge P.natDegree Q.natDegree with hlt | hge
          · rw [ite_eq_left hlt, coprime_main hQ hP hlt (by omega)]
            exact isCoprime_comm
          · rw [ite_eq_right (by omega)]
            exact coprime_main hP hQ (by omega) (by omega)

/-- **Correctness of `isSquarefree` over a field**: the test decides
Mathlib's `Polynomial.Separable` (which over characteristic `0` coincides
with squarefreeness). -/
theorem isSquarefree_iff [PolynomialDerivative K] (P : AzPolynomial K) :
    isSquarefree P = true ↔ (AzPolynomial.toPoly P).Separable := by
  rw [isSquarefree, coprime_iff, toPoly_derivative]
  exact Iff.rfl

/-- **Correctness of `isPrimitive` over a field**: the test decides
Mathlib's `Polynomial.IsPrimitive` (over a field: nonvanishing). -/
theorem isPrimitive_field_iff (P : AzPolynomial K) :
    isPrimitive P = true ↔ (AzPolynomial.toPoly P).IsPrimitive := by
  show (P != 0) = true ↔ _
  rw [bne_iff_ne]
  constructor
  · intro hne r hr
    rcases eq_or_ne r 0 with rfl | hr0
    · exfalso
      rw [Polynomial.C_0, zero_dvd_iff] at hr
      exact toPoly_ne_zero hne hr
    · exact isUnit_iff_ne_zero.mpr hr0
  · intro h hne
    have h0 := h 0 (by rw [Polynomial.C_0, hne, toPoly_zero])
    exact (by simp : ¬ IsUnit (0 : K)) h0

/-! ### The `ℤ` (`AzInt`) versions: statements for the `ℚ[X]` images -/

private theorem hρinj :
    Function.Injective ((Int.castRingHom ℚ).comp AzInt.toIntRingHom) :=
  fun a b h => Azurite.AzInt.ringEquivInt.injective (by
    have := Int.cast_injective (α := ℚ) h
    simpa using this)

private theorem img_ne_zero {P : AzPolynomial AzInt} (hP : P ≠ 0) :
    (AzPolynomial.toPoly P).map ((Int.castRingHom ℚ).comp AzInt.toIntRingHom) ≠ 0 := by
  rw [Ne, Polynomial.map_eq_zero_iff hρinj]
  exact toPoly_ne_zero hP

private theorem natDegree_img (P : AzPolynomial AzInt) :
    ((AzPolynomial.toPoly P).map
      ((Int.castRingHom ℚ).comp AzInt.toIntRingHom)).natDegree = P.natDegree := by
  rw [Polynomial.natDegree_map_eq_of_injective hρinj, AzPolynomial.natDegree_toPoly]

private theorem img_C_lc (P : AzPolynomial AzInt) :
    ((AzPolynomial.toPoly P).map
        ((Int.castRingHom ℚ).comp AzInt.toIntRingHom)).leadingCoeff
      = ((Int.castRingHom ℚ).comp AzInt.toIntRingHom) P.leadingCoeff := by
  rw [Polynomial.leadingCoeff, natDegree_img, Polynomial.coeff_map, coeff_toPoly,
    ← AzPolynomial.leadingCoeff]

/-- The main branch over `AzInt`. -/
private theorem coprime_main_int {P Q : AzPolynomial AzInt} (hP : P ≠ 0) (hQ : Q ≠ 0)
    (hpq : Q.natDegree < P.natDegree) (hq1 : 1 ≤ Q.natDegree) :
    ((subresGcd P Q).natDegree == 0) = true
      ↔ IsCoprime
        ((AzPolynomial.toPoly P).map ((Int.castRingHom ℚ).comp AzInt.toIntRingHom))
        ((AzPolynomial.toPoly Q).map ((Int.castRingHom ℚ).comp AzInt.toIntRingHom)) := by
  obtain ⟨hassoc, hne⟩ := subresGcd_int_qassoc P Q hP hQ hpq hq1
  rw [beq_iff_eq, isCoprime_iff_isUnit_gcd]
  constructor
  · intro h
    refine hassoc.isUnit (isUnit_iff_natDegree.mpr ⟨img_ne_zero hne, ?_⟩)
    rw [natDegree_img]
    exact h
  · intro h
    have h2 := isUnit_iff_natDegree.mp (hassoc.symm.isUnit h)
    rw [natDegree_img] at h2
    exact h2.2

/-- **Correctness of `coprime` over `ℤ` (`AzInt`)**: the test decides
`IsCoprime` of the `ℚ[X]` images — coprimality over the fraction field
(no common factor of positive degree). -/
theorem coprime_int_iff (P Q : AzPolynomial AzInt) :
    coprime P Q = true
      ↔ IsCoprime
        ((AzPolynomial.toPoly P).map ((Int.castRingHom ℚ).comp AzInt.toIntRingHom))
        ((AzPolynomial.toPoly Q).map ((Int.castRingHom ℚ).comp AzInt.toIntRingHom)) := by
  rw [coprime]
  by_cases hP : P = 0
  · subst hP
    rw [ite_eq_left rfl, toPoly_zero, Polynomial.map_zero, isCoprime_zero_left,
      isUnit_iff_natDegree]
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨img_ne_zero h1, by rw [natDegree_img]; exact h2⟩
    · rintro ⟨h1, h2⟩
      refine ⟨fun h0 => h1 (by rw [h0, toPoly_zero, Polynomial.map_zero]), ?_⟩
      rw [← natDegree_img Q]
      exact h2
  · rw [ite_eq_right hP]
    by_cases hQ : Q = 0
    · subst hQ
      rw [ite_eq_left rfl, toPoly_zero, Polynomial.map_zero, isCoprime_zero_right,
        isUnit_iff_natDegree]
      simp only [beq_iff_eq]
      constructor
      · intro h
        exact ⟨img_ne_zero hP, by rw [natDegree_img]; exact h⟩
      · rintro ⟨-, h2⟩
        rw [← natDegree_img P]
        exact h2
    · rw [ite_eq_right hQ]
      by_cases hconst : P.natDegree = 0 ∨ Q.natDegree = 0
      · rw [ite_eq_left hconst]
        simp only [true_iff]
        rcases hconst with h | h
        · exact isUnit_isCoprime_left (isUnit_iff_natDegree.mpr
            ⟨img_ne_zero hP, by rw [natDegree_img]; exact h⟩)
        · exact (isUnit_isCoprime_left (isUnit_iff_natDegree.mpr
            ⟨img_ne_zero hQ, by rw [natDegree_img]; exact h⟩)).symm
      · rw [ite_eq_right hconst]
        push Not at hconst
        obtain ⟨hp1, hq1⟩ := hconst
        by_cases hdeq : P.natDegree = Q.natDegree
        · rw [ite_eq_left hdeq]
          have hlcP : P.leadingCoeff ≠ 0 := by
            rw [← leadingCoeff_toPoly]
            exact Polynomial.leadingCoeff_ne_zero.mpr (toPoly_ne_zero hP)
          have hlcPq : ((Int.castRingHom ℚ).comp AzInt.toIntRingHom) P.leadingCoeff ≠ 0 := by
            intro h
            exact hlcP (hρinj (by rw [h, map_zero]))
          -- the mapped pre-step
          have himg_pre : (AzPolynomial.toPoly (preStep P Q)).map
              ((Int.castRingHom ℚ).comp AzInt.toIntRingHom)
              = Polynomial.C (((Int.castRingHom ℚ).comp AzInt.toIntRingHom) P.leadingCoeff)
                  * ((AzPolynomial.toPoly Q).map ((Int.castRingHom ℚ).comp AzInt.toIntRingHom))
                - Polynomial.C (((Int.castRingHom ℚ).comp AzInt.toIntRingHom) Q.leadingCoeff)
                  * ((AzPolynomial.toPoly P).map
                      ((Int.castRingHom ℚ).comp AzInt.toIntRingHom)) := by
            rw [show AzPolynomial.toPoly (preStep P Q)
                = Polynomial.C P.leadingCoeff * AzPolynomial.toPoly Q
                  - Polynomial.C Q.leadingCoeff * AzPolynomial.toPoly P from toPoly_pre_step P Q,
              Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_mul,
              Polynomial.map_C, Polynomial.map_C]
          have hgcd_pre : IsCoprime
              ((AzPolynomial.toPoly P).map ((Int.castRingHom ℚ).comp AzInt.toIntRingHom))
              ((AzPolynomial.toPoly (preStep P Q)).map
                ((Int.castRingHom ℚ).comp AzInt.toIntRingHom))
              ↔ IsCoprime
              ((AzPolynomial.toPoly P).map ((Int.castRingHom ℚ).comp AzInt.toIntRingHom))
              ((AzPolynomial.toPoly Q).map ((Int.castRingHom ℚ).comp AzInt.toIntRingHom)) := by
            rw [isCoprime_iff_isUnit_gcd, isCoprime_iff_isUnit_gcd, himg_pre,
              gcd_pre_step _ _ hlcPq]
          by_cases hpre : preStep P Q = 0
          · rw [ite_eq_left hpre]
            simp only [Bool.false_eq_true, false_iff]
            intro hco
            have h0 : Polynomial.C (((Int.castRingHom ℚ).comp AzInt.toIntRingHom) P.leadingCoeff)
                * ((AzPolynomial.toPoly Q).map ((Int.castRingHom ℚ).comp AzInt.toIntRingHom))
                = Polynomial.C (((Int.castRingHom ℚ).comp AzInt.toIntRingHom) Q.leadingCoeff)
                  * ((AzPolynomial.toPoly P).map
                      ((Int.castRingHom ℚ).comp AzInt.toIntRingHom)) := by
              have h := himg_pre
              have hpre' : AzPolynomial.toPoly (preStep P Q) = 0 := by
                rw [hpre, toPoly_zero]
              rw [hpre', Polynomial.map_zero] at h
              linear_combination -h
            have hdvd : ((AzPolynomial.toPoly P).map
                ((Int.castRingHom ℚ).comp AzInt.toIntRingHom))
                ∣ ((AzPolynomial.toPoly Q).map
                    ((Int.castRingHom ℚ).comp AzInt.toIntRingHom)) := by
              refine ⟨Polynomial.C
                (((Int.castRingHom ℚ).comp AzInt.toIntRingHom) P.leadingCoeff)⁻¹
                * Polynomial.C
                  (((Int.castRingHom ℚ).comp AzInt.toIntRingHom) Q.leadingCoeff), ?_⟩
              have hCne : (Polynomial.C
                  (((Int.castRingHom ℚ).comp AzInt.toIntRingHom) P.leadingCoeff) : ℚ[X]) ≠ 0 := by
                rwa [Ne, Polynomial.C_eq_zero]
              apply mul_left_cancel₀ hCne
              rw [show ∀ (a b x y : ℚ[X]), a * (x * (b * y)) = (a * b) * (y * x) from
                  fun a b x y => by ring,
                ← Polynomial.C_mul, mul_inv_cancel₀ hlcPq, Polynomial.C_1, one_mul, ← h0]
            have hunit := hco.isUnit_of_dvd' dvd_rfl hdvd
            have h2 := (isUnit_iff_natDegree.mp hunit).2
            rw [natDegree_img] at h2
            omega
          · rw [ite_eq_right hpre]
            by_cases hpre0 : (preStep P Q).natDegree = 0
            · rw [ite_eq_left hpre0]
              simp only [true_iff]
              rw [← hgcd_pre]
              exact (isUnit_isCoprime_left (isUnit_iff_natDegree.mpr
                ⟨img_ne_zero hpre, by rw [natDegree_img]; exact hpre0⟩)).symm
            · rw [ite_eq_right hpre0]
              rw [coprime_main_int hP hpre
                (pre_step_natDegree_lt hP hQ hdeq hpre) (by omega)]
              exact hgcd_pre
        · rw [ite_eq_right hdeq]
          rcases Nat.lt_or_ge P.natDegree Q.natDegree with hlt | hge
          · rw [ite_eq_left hlt, coprime_main_int hQ hP hlt (by omega)]
            exact isCoprime_comm
          · rw [ite_eq_right (by omega)]
            exact coprime_main_int hP hQ (by omega) (by omega)

/-- **Correctness of `isSquarefree` over `ℤ` (`AzInt`)**: the test decides
separability of the `ℚ[X]` image — no repeated roots in any extension. -/
theorem isSquarefree_int_iff (P : AzPolynomial AzInt) :
    isSquarefree P = true
      ↔ ((AzPolynomial.toPoly P).map
          ((Int.castRingHom ℚ).comp AzInt.toIntRingHom)).Separable := by
  rw [isSquarefree, coprime_int_iff, toPoly_derivative, ← Polynomial.derivative_map]
  exact Iff.rfl

/-- **Correctness of `isPrimitive` over `ℤ` (`AzInt`)**: the test decides
Mathlib's `Polynomial.IsPrimitive` of the `ℤ[X]` image. -/
theorem isPrimitive_int_iff (p : AzPolynomial AzInt) :
    isPrimitive p = true ↔ ((AzPolynomial.toPoly p).map AzInt.toIntRingHom).IsPrimitive := by
  show (p.content == 1) = true ↔ _
  rw [beq_iff_eq, Polynomial.isPrimitive_iff_content_eq_one, content_toPoly]
  constructor
  · intro h
    rw [h]
    rfl
  · intro h
    apply Azurite.AzNat.toNat_injective
    exact_mod_cast h

/-! ### `char`: `coprime` decides that the normalized gcd is a nonzero constant

`AzPolynomial.coprime P Q = true ↔ (gcd P Q ≠ 0 ∧ (gcd P Q).natDegree = 0)`
where `gcd = gcdNormalizedInt`. This is a **structural** identity — both
`coprime` and `gcdNormalizedInt` are defined via the same `subresGcd`, so
matching them needs only degree/nonzero bookkeeping on the components
(`signNorm`, `contentGcdInt • ·`, `primPos`) plus `subresGcd ≠ 0` (from
`subresGcd_int_qassoc`); no Gauss theory. Used by
`AzMvPolynomial.coprime_toAzMvPolynomial` (lifting preserves coprimality). -/

private theorem azNatToAzInt_eq_zero {m : AzNat} : azNatToAzInt m = 0 ↔ m = 0 := by
  constructor
  · intro h
    calc m = (azNatToAzInt m).abs := rfl
      _ = (0 : AzInt).abs := by rw [h]
      _ = 0 := rfl
  · intro h; subst h; rfl

private theorem content_ne_zero {P : AzPolynomial AzInt} (hP : P ≠ 0) :
    P.content ≠ 0 := by
  intro h
  have h0 : ((AzPolynomial.toPoly P).map AzInt.toIntRingHom).content = 0 := by
    rw [content_toPoly, h]; rfl
  rw [Polynomial.content_eq_zero_iff] at h0
  exact map_toPoly_ne_zero hP h0

private theorem contentGcdInt_ne_zero {P Q : AzPolynomial AzInt} (hP : P ≠ 0) :
    contentGcdInt P Q ≠ 0 := by
  rw [contentGcdInt, ne_eq, azNatToAzInt_eq_zero]
  intro h
  apply content_ne_zero hP
  apply Azurite.AzNat.toNat_injective
  have hh := congrArg Azurite.AzNat.toNat h
  rw [Azurite.AzNat.toNat_gcd] at hh
  exact (Nat.gcd_eq_zero_iff.mp hh).1

private theorem smul_natDegree {c : AzInt} (hc : c ≠ 0) (p : AzPolynomial AzInt) :
    (c • p).natDegree = p.natDegree := by
  rw [← AzPolynomial.natDegree_toPoly, ← AzPolynomial.natDegree_toPoly, toPoly_smul,
    Polynomial.smul_eq_C_mul, Polynomial.natDegree_C_mul hc]

private theorem smul_eq_zero_iff {c : AzInt} (hc : c ≠ 0) (p : AzPolynomial AzInt) :
    c • p = 0 ↔ p = 0 := by
  constructor
  · intro h
    apply toPoly_inj.mp
    rw [toPoly_zero]
    have hh := congrArg AzPolynomial.toPoly h
    rw [toPoly_smul, Polynomial.smul_eq_C_mul, toPoly_zero, mul_eq_zero] at hh
    rcases hh with h1 | h1
    · exact absurd (Polynomial.C_eq_zero.mp h1) hc
    · exact h1
  · intro h; rw [h, smul_zero]

private theorem primPos_natDegree {g : AzPolynomial AzInt} (hg : g ≠ 0) :
    (primPos g).natDegree = g.natDegree := by
  obtain ⟨c, hc, hkey, _, _⟩ := primPos_spec hg
  have h1 : ((AzPolynomial.toPoly (primPos g)).map AzInt.toIntRingHom).natDegree
      = (primPos g).natDegree := natDegree_map_toPoly (primPos g)
  have h2 : ((AzPolynomial.toPoly g).map AzInt.toIntRingHom).natDegree
      = g.natDegree := natDegree_map_toPoly g
  rw [← h1, ← h2, ← hkey, Polynomial.natDegree_C_mul hc]

private theorem primPos_ne_zero {g : AzPolynomial AzInt} (hg : g ≠ 0) :
    primPos g ≠ 0 := by
  obtain ⟨c, _, hkey, _, _⟩ := primPos_spec hg
  intro h0
  rw [h0, toPoly_zero, Polynomial.map_zero, mul_zero] at hkey
  exact map_toPoly_ne_zero hg hkey.symm

private theorem signNorm_natDegree (p : AzPolynomial AzInt) :
    (signNorm p).natDegree = p.natDegree := by
  rw [signNorm]
  split
  · rfl
  · rw [← AzPolynomial.natDegree_toPoly, ← AzPolynomial.natDegree_toPoly, toPoly_neg,
      Polynomial.natDegree_neg]

private theorem signNorm_eq_zero_iff (p : AzPolynomial AzInt) :
    signNorm p = 0 ↔ p = 0 := by
  rw [signNorm]
  split
  · exact Iff.rfl
  · exact neg_eq_zero

/-- The composite ring isomorphism `AzPolynomial AzInt ≃+* ℤ[X]`, sending
`a` to `(toPoly a).map toIntRingHom`. -/
private noncomputable def intPolyEquiv : AzPolynomial AzInt ≃+* Polynomial ℤ :=
  (Azurite.AzPolynomial.ringEquivPolynomial).trans
    (Polynomial.mapEquiv Azurite.AzInt.ringEquivInt)

private theorem intPolyEquiv_apply (a : AzPolynomial AzInt) :
    intPolyEquiv a = (AzPolynomial.toPoly a).map AzInt.toIntRingHom := rfl

/-- The normalized gcd divides `P` (in `AzPolynomial AzInt`). -/
theorem gcd_dvd_left_int (P Q : AzPolynomial AzInt) : AzPolynomial.gcd P Q ∣ P := by
  rw [← map_dvd_iff intPolyEquiv, intPolyEquiv_apply, intPolyEquiv_apply,
    map_toPoly_gcd_int]
  exact gcd_dvd_left _ _

/-- The normalized gcd divides `Q` (in `AzPolynomial AzInt`). -/
theorem gcd_dvd_right_int (P Q : AzPolynomial AzInt) : AzPolynomial.gcd P Q ∣ Q := by
  rw [← map_dvd_iff intPolyEquiv, intPolyEquiv_apply, intPolyEquiv_apply,
    map_toPoly_gcd_int]
  exact gcd_dvd_right _ _

/-- The normalized gcd is zero iff both inputs are zero. -/
theorem gcd_eq_zero_iff_int {P Q : AzPolynomial AzInt} :
    AzPolynomial.gcd P Q = 0 ↔ P = 0 ∧ Q = 0 := by
  rw [← map_eq_zero_iff intPolyEquiv intPolyEquiv.injective, intPolyEquiv_apply,
    map_toPoly_gcd_int, gcd_eq_zero_iff,
    Polynomial.map_eq_zero_iff hιinj, Polynomial.map_eq_zero_iff hιinj]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨toPoly_inj.mp (h1.trans toPoly_zero.symm),
      toPoly_inj.mp (h2.trans toPoly_zero.symm)⟩
  · rintro ⟨h1, h2⟩; subst h1; subst h2; exact ⟨toPoly_zero, toPoly_zero⟩

/-- **`char`**: the coprimality test decides that the normalized gcd is a
nonzero constant. -/
theorem coprime_iff_gcd_isConstant (P Q : AzPolynomial AzInt) :
    coprime P Q = true
      ↔ (AzPolynomial.gcd P Q ≠ 0 ∧ (AzPolynomial.gcd P Q).natDegree = 0) := by
  show coprime P Q = true ↔ (gcdNormalizedInt P Q ≠ 0 ∧ (gcdNormalizedInt P Q).natDegree = 0)
  unfold coprime gcdNormalizedInt
  simp only []
  split_ifs with h1 h2 h3 h4 h5 h6 h7
  · -- P = 0
    subst h1
    rw [Bool.and_eq_true, bne_iff_ne, beq_iff_eq, signNorm_natDegree, ne_eq, ne_eq,
      signNorm_eq_zero_iff]
  · -- Q = 0
    subst h2
    rw [beq_iff_eq, signNorm_natDegree, ne_eq, signNorm_eq_zero_iff]
    exact ⟨fun h => ⟨h1, h⟩, fun h => h.2⟩
  · -- P.natDegree = 0 ∨ Q.natDegree = 0
    have hc : contentGcdInt P Q ≠ 0 := contentGcdInt_ne_zero h1
    simp only [true_iff]
    exact ⟨(smul_eq_zero_iff hc _).not.mpr one_ne_zero,
      by rw [smul_natDegree hc]; rfl⟩
  · -- P.natDegree = Q.natDegree, preStep = 0
    have hc : contentGcdInt P Q ≠ 0 := contentGcdInt_ne_zero h1
    simp only [false_iff, not_and]
    intro _
    rw [smul_natDegree hc, primPos_natDegree h1]
    push Not at h3
    omega
  · -- P.natDegree = Q.natDegree, preStep ≠ 0, preStep.natDegree = 0
    have hc : contentGcdInt P Q ≠ 0 := contentGcdInt_ne_zero h1
    simp only [true_iff]
    exact ⟨(smul_eq_zero_iff hc _).not.mpr one_ne_zero,
      by rw [smul_natDegree hc]; rfl⟩
  · -- P.natDegree = Q.natDegree, preStep ≠ 0, preStep.natDegree ≠ 0
    have hc : contentGcdInt P Q ≠ 0 := contentGcdInt_ne_zero h1
    have hlt : (preStep P Q).natDegree < P.natDegree :=
      pre_step_natDegree_lt h1 h2 h4 h5
    have hne : subresGcd P (preStep P Q) ≠ 0 :=
      (subresGcd_int_qassoc P (preStep P Q) h1 h5 hlt (by omega)).2
    rw [beq_iff_eq]
    constructor
    · intro h
      exact ⟨(smul_eq_zero_iff hc _).not.mpr (primPos_ne_zero hne),
        by rw [smul_natDegree hc, primPos_natDegree hne]; exact h⟩
    · intro h
      rw [smul_natDegree hc, primPos_natDegree hne] at h
      exact h.2
  · -- P.natDegree < Q.natDegree
    have hc : contentGcdInt P Q ≠ 0 := contentGcdInt_ne_zero h1
    have hne : subresGcd Q P ≠ 0 :=
      (subresGcd_int_qassoc Q P h2 h1 h7 (by push Not at h3; omega)).2
    rw [beq_iff_eq]
    constructor
    · intro h
      exact ⟨(smul_eq_zero_iff hc _).not.mpr (primPos_ne_zero hne),
        by rw [smul_natDegree hc, primPos_natDegree hne]; exact h⟩
    · intro h
      rw [smul_natDegree hc, primPos_natDegree hne] at h
      exact h.2
  · -- P.natDegree > Q.natDegree
    have hc : contentGcdInt P Q ≠ 0 := contentGcdInt_ne_zero h1
    have hne : subresGcd P Q ≠ 0 :=
      (subresGcd_int_qassoc P Q h1 h2 (by push Not at h3 h4 h7; omega)
        (by push Not at h3; omega)).2
    rw [beq_iff_eq]
    constructor
    · intro h
      exact ⟨(smul_eq_zero_iff hc _).not.mpr (primPos_ne_zero hne),
        by rw [smul_natDegree hc, primPos_natDegree hne]; exact h⟩
    · intro h
      rw [smul_natDegree hc, primPos_natDegree hne] at h
      exact h.2

end Azurite.AzPolynomial
