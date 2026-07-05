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
    rw [if_pos rfl, toPoly_zero, isCoprime_zero_left, isUnit_iff_natDegree]
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨toPoly_ne_zero h1, by rw [AzPolynomial.natDegree_toPoly]; exact h2⟩
    · rintro ⟨h1, h2⟩
      refine ⟨fun h0 => h1 (by rw [h0, toPoly_zero]), ?_⟩
      rw [← AzPolynomial.natDegree_toPoly]
      exact h2
  · rw [if_neg hP]
    by_cases hQ : Q = 0
    · subst hQ
      rw [if_pos rfl, toPoly_zero, isCoprime_zero_right, isUnit_iff_natDegree]
      simp only [beq_iff_eq]
      constructor
      · intro h
        exact ⟨toPoly_ne_zero hP, by rw [AzPolynomial.natDegree_toPoly]; exact h⟩
      · rintro ⟨-, h2⟩
        rw [← AzPolynomial.natDegree_toPoly]
        exact h2
    · rw [if_neg hQ]
      by_cases hconst : P.natDegree = 0 ∨ Q.natDegree = 0
      · rw [if_pos hconst]
        simp only [true_iff]
        rcases hconst with h | h
        · exact isUnit_isCoprime_left (isUnit_iff_natDegree.mpr
            ⟨toPoly_ne_zero hP, by rw [AzPolynomial.natDegree_toPoly]; exact h⟩)
        · exact (isUnit_isCoprime_left (isUnit_iff_natDegree.mpr
            ⟨toPoly_ne_zero hQ, by rw [AzPolynomial.natDegree_toPoly]; exact h⟩)).symm
      · rw [if_neg hconst]
        push Not at hconst
        obtain ⟨hp1, hq1⟩ := hconst
        by_cases hdeq : P.natDegree = Q.natDegree
        · rw [if_pos hdeq]
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
          · rw [if_pos hpre]
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
          · rw [if_neg hpre]
            by_cases hpre0 : (preStep P Q).natDegree = 0
            · rw [if_pos hpre0]
              simp only [true_iff]
              rw [← hgcd_pre]
              exact (isUnit_isCoprime_left (isUnit_iff_natDegree.mpr
                ⟨toPoly_ne_zero hpre,
                  by rw [AzPolynomial.natDegree_toPoly]; exact hpre0⟩)).symm
            · rw [if_neg hpre0]
              rw [coprime_main hP hpre
                (pre_step_natDegree_lt hP hQ hdeq hpre) (by omega)]
              exact hgcd_pre
        · rw [if_neg hdeq]
          rcases Nat.lt_or_ge P.natDegree Q.natDegree with hlt | hge
          · rw [if_pos hlt, coprime_main hQ hP hlt (by omega)]
            exact isCoprime_comm
          · rw [if_neg (by omega)]
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
    rw [if_pos rfl, toPoly_zero, Polynomial.map_zero, isCoprime_zero_left,
      isUnit_iff_natDegree]
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨img_ne_zero h1, by rw [natDegree_img]; exact h2⟩
    · rintro ⟨h1, h2⟩
      refine ⟨fun h0 => h1 (by rw [h0, toPoly_zero, Polynomial.map_zero]), ?_⟩
      rw [← natDegree_img Q]
      exact h2
  · rw [if_neg hP]
    by_cases hQ : Q = 0
    · subst hQ
      rw [if_pos rfl, toPoly_zero, Polynomial.map_zero, isCoprime_zero_right,
        isUnit_iff_natDegree]
      simp only [beq_iff_eq]
      constructor
      · intro h
        exact ⟨img_ne_zero hP, by rw [natDegree_img]; exact h⟩
      · rintro ⟨-, h2⟩
        rw [← natDegree_img P]
        exact h2
    · rw [if_neg hQ]
      by_cases hconst : P.natDegree = 0 ∨ Q.natDegree = 0
      · rw [if_pos hconst]
        simp only [true_iff]
        rcases hconst with h | h
        · exact isUnit_isCoprime_left (isUnit_iff_natDegree.mpr
            ⟨img_ne_zero hP, by rw [natDegree_img]; exact h⟩)
        · exact (isUnit_isCoprime_left (isUnit_iff_natDegree.mpr
            ⟨img_ne_zero hQ, by rw [natDegree_img]; exact h⟩)).symm
      · rw [if_neg hconst]
        push Not at hconst
        obtain ⟨hp1, hq1⟩ := hconst
        by_cases hdeq : P.natDegree = Q.natDegree
        · rw [if_pos hdeq]
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
          · rw [if_pos hpre]
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
          · rw [if_neg hpre]
            by_cases hpre0 : (preStep P Q).natDegree = 0
            · rw [if_pos hpre0]
              simp only [true_iff]
              rw [← hgcd_pre]
              exact (isUnit_isCoprime_left (isUnit_iff_natDegree.mpr
                ⟨img_ne_zero hpre, by rw [natDegree_img]; exact hpre0⟩)).symm
            · rw [if_neg hpre0]
              rw [coprime_main_int hP hpre
                (pre_step_natDegree_lt hP hQ hdeq hpre) (by omega)]
              exact hgcd_pre
        · rw [if_neg hdeq]
          rcases Nat.lt_or_ge P.natDegree Q.natDegree with hlt | hge
          · rw [if_pos hlt, coprime_main_int hQ hP hlt (by omega)]
            exact isCoprime_comm
          · rw [if_neg (by omega)]
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

end Azurite.AzPolynomial
