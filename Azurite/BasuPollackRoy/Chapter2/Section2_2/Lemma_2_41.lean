import Azurite.BasuPollackRoy.Chapter2.Section2_2.NormalPolynomial
import Mathlib.Algebra.Polynomial.Degree.Operations

/-!
# BPR Lemma 2.41

The linear polynomial `X - x` is normal iff `x ≤ 0`.
-/

namespace Azurite.BPR

open Polynomial

variable {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]

omit [LinearOrder R] [IsStrictOrderedRing R] in
private lemma coeff_X_sub_C_eq (x : R) (i : ℕ) :
    ((X : R[X]) - C x).coeff i =
      if i = 0 then -x else if i = 1 then 1 else 0 := by
  rw [coeff_sub, coeff_X, coeff_C]
  split_ifs with h0 h1 <;> simp_all

/-- **BPR Lemma 2.41.** The linear polynomial `X - x` is normal iff `x ≤ 0`. -/
lemma isNormal_X_sub_C_iff {x : R} : IsNormal ((X : R[X]) - C x) ↔ x ≤ 0 := by
  constructor
  · intro h
    have h0 := h.coeff_nonneg 0
    rw [coeff_X_sub_C_eq] at h0
    simpa using neg_nonneg.mp h0
  · intro hx
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro i
      rw [coeff_X_sub_C_eq]
      split_ifs
      · exact neg_nonneg.mpr hx
      · exact zero_le_one
      · exact le_refl 0
    · rw [leadingCoeff, natDegree_X_sub_C, coeff_X_sub_C_eq]
      simp
    · intro k
      simp only [coeff_X_sub_C_eq]
      rcases k with _ | _ | k <;> simp
    · rintro j h hjh hj hh i hji hih
      rw [coeff_X_sub_C_eq] at hj hh
      split_ifs at hj with hj0 hj1
      · subst hj0
        split_ifs at hh with hh0 hh1
        · subst hh0; exact absurd hjh (lt_irrefl 0)
        · subst hh1; omega
        · exact absurd hh (lt_irrefl 0)
      · subst hj1
        split_ifs at hh with hh0 hh1
        · subst hh0; omega
        · subst hh1; omega
        · exact absurd hh (lt_irrefl 0)
      · exact absurd hj (lt_irrefl 0)

end Azurite.BPR
