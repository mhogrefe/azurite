import Mathlib.Algebra.Polynomial.Degree.Defs
import Mathlib.Algebra.Polynomial.Degree.Operations

/-!
# BPR Definition: Normal polynomial

A polynomial `A = a_p X^p + ⋯ + a_0` with non-negative coefficients is *normal* if:
(a) `a_p > 0`,
(b) `a_k² ≥ a_{k-1} · a_{k+1}` for all indices `k` (log-concavity),
(c) `a_j > 0` and `a_h > 0` with `j < h` imply `a_{j+1}, …, a_{h-1}` are all `> 0`
    (contiguous positive support),
with the convention `a_i = 0` for `i < 0` or `i > p`.

Under this convention the log-concavity condition at `k = 0` reads
`a_0² ≥ 0 · a_1 = 0` and at `k = p` reads `a_p² ≥ a_{p-1} · 0 = 0`, both automatic;
the substantive content is `1 ≤ k ≤ p - 1`. We state it as
`a_k · a_{k+2} ≤ a_{k+1}²` for all `k : ℕ` — equivalent, and avoids `ℕ`-subtraction.
-/

namespace Azurite.BPR

open Polynomial

variable {R : Type*}

/-- **BPR Definition (normal polynomial).**
`P` is *normal* if every coefficient is non-negative, the leading coefficient is
strictly positive, the coefficient sequence is log-concave, and its positive support
is contiguous (no interior zeros between two positive coefficients). -/
structure IsNormal [CommSemiring R] [PartialOrder R] (P : R[X]) : Prop where
  /-- (BPR prefix) All coefficients are non-negative. -/
  coeff_nonneg : ∀ i, 0 ≤ P.coeff i
  /-- (BPR condition a) The leading coefficient is strictly positive. -/
  leading_pos : 0 < P.leadingCoeff
  /-- (BPR condition b) Log-concavity: `a_k · a_{k+2} ≤ a_{k+1}²` for all `k`.
      Equivalent to BPR's `a_k² ≥ a_{k-1} · a_{k+1}` for `1 ≤ k ≤ p - 1`; the
      boundary cases `k = 0` and `k = p` are automatic under the convention
      `a_i = 0` for `i < 0` or `i > p`. -/
  log_concave : ∀ k, P.coeff k * P.coeff (k + 2) ≤ P.coeff (k + 1) ^ 2
  /-- (BPR condition c) Contiguous positive support: no interior gaps. -/
  no_gap : ∀ {j h : ℕ}, j < h → 0 < P.coeff j → 0 < P.coeff h →
    ∀ {i : ℕ}, j < i → i < h → 0 < P.coeff i

/-! ## Lemma 2.41: linear factors -/

section LinearFactor

variable [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]

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

end LinearFactor

end Azurite.BPR
