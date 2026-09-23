import Azurite.BasuPollackRoy.Chapter2.Section2_2.NormalPolynomial
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Tactic.ComputeDegree

/-!
# BPR Lemma 2.42

The monic quadratic with complex conjugate roots `a ± ib` is normal iff `(a, b)` lies in
the BPR cone `𝓑 = {(a, b) | |b| ≤ -√3 · a}`. We formulate `𝓑` via its squared form
`b² ≤ 3·a²` together with `a ≤ 0` — equivalent (given `a ≤ 0`) to the `√3` form, and
stateable without requiring `√3 ∈ R`.
-/

namespace Azurite.BPR

open Polynomial

variable {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]

/-- **BPR cone 𝓑.** Pairs `(a, b) : R × R` representing the "complex numbers"
    `a + ib ∈ R[i]` that satisfy `|b| ≤ -√3 · a`. We formulate it via the squared
    form `b² ≤ 3·a²` together with `a ≤ 0` — equivalent (given `a ≤ 0`) to the
    `√3` form, and stateable without requiring `√3 ∈ R`. -/
def ConeB : Set (R × R) :=
  {p | p.1 ≤ 0 ∧ p.2 ^ 2 ≤ 3 * p.1 ^ 2}

/-- The monic quadratic with complex conjugate roots `a ± ib`:
    `X² − 2aX + (a² + b²)`. -/
noncomputable def quadFromRoots (a b : R) : R[X] :=
  X ^ 2 - C (2 * a) * X + C (a ^ 2 + b ^ 2)

omit [LinearOrder R] [IsStrictOrderedRing R] in
private lemma coeff_quadFromRoots (a b : R) (i : ℕ) :
    (quadFromRoots a b).coeff i =
      if i = 0 then a ^ 2 + b ^ 2
      else if i = 1 then -(2 * a)
      else if i = 2 then 1
      else 0 := by
  unfold quadFromRoots
  rw [coeff_add, coeff_sub, coeff_C, coeff_X_pow, coeff_C_mul, coeff_X]
  match i with
  | 0 => simp
  | 1 => simp
  | 2 => simp
  | _ + 3 => simp

private lemma natDegree_quadFromRoots (a b : R) :
    (quadFromRoots a b).natDegree = 2 := by
  unfold quadFromRoots
  compute_degree!

/-- **BPR Lemma 2.42.** The monic quadratic `X² − 2aX + (a² + b²)` with complex
    conjugate roots `a ± ib` is normal iff `(a, b) ∈ 𝓑`. -/
lemma isNormal_quadFromRoots_iff (a b : R) :
    IsNormal (quadFromRoots a b) ↔ (a, b) ∈ ConeB := by
  unfold ConeB
  simp only [Set.mem_ofPred_eq]
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · have h1 := h.coeff_nonneg 1
      rw [coeff_quadFromRoots] at h1
      simp at h1
      linarith
    · have hlog := h.log_concave 0
      simp only [coeff_quadFromRoots] at hlog
      simp at hlog
      nlinarith [hlog]
  · rintro ⟨ha, hab⟩
    have hsumsq : (0 : R) ≤ a ^ 2 + b ^ 2 := add_nonneg (sq_nonneg a) (sq_nonneg b)
    have hneg2a : (0 : R) ≤ -(2 * a) := by linarith
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro i
      rw [coeff_quadFromRoots]
      split_ifs
      · exact hsumsq
      · exact hneg2a
      · exact zero_le_one
      · exact le_refl 0
    · rw [leadingCoeff, natDegree_quadFromRoots, coeff_quadFromRoots]
      simp
    · intro k
      simp only [coeff_quadFromRoots]
      match k with
      | 0 => simp; nlinarith [hab]
      | 1 => simp
      | 2 => simp
      | _ + 3 => simp
    · rintro j h hjh hj hh i hji hih
      rw [coeff_quadFromRoots] at hj hh
      split_ifs at hj with hj0 hj1 hj2
      · subst hj0
        split_ifs at hh with hh0 hh1 hh2
        · subst hh0; exact absurd hjh (lt_irrefl 0)
        · subst hh1; omega
        · subst hh2
          have hi : i = 1 := by omega
          subst hi
          rw [coeff_quadFromRoots]
          simp only [show (1 : ℕ) ≠ 0 from by decide, ite_false, ite_true]
          by_contra hnot
          push Not at hnot
          have ha_eq : a = 0 := le_antisymm ha (by linarith)
          rw [ha_eq] at hj hab
          nlinarith [sq_nonneg b]
        · exact absurd hh (lt_irrefl 0)
      · subst hj1
        split_ifs at hh with hh0 hh1 hh2
        · subst hh0; omega
        · subst hh1; omega
        · subst hh2; omega
        · exact absurd hh (lt_irrefl 0)
      · subst hj2
        split_ifs at hh with hh0 hh1 hh2
        · subst hh0; omega
        · subst hh1; omega
        · subst hh2; omega
        · exact absurd hh (lt_irrefl 0)
      · exact absurd hj (lt_irrefl 0)

end Azurite.BPR
