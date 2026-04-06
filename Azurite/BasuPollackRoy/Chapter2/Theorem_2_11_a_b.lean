import Mathlib.RingTheory.AdjoinRoot
import Mathlib.FieldTheory.IsRealClosed.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.FieldTheory.Separable
import Mathlib.Algebra.Polynomial.SpecificDegree

/-!
# BPR Theorem 2.11 a) ⇒ b): Real Closed ⟹ R[i] Algebraically Closed

**Theorem 2.11 (BPR).** If R is a real closed field, then
R[i] := R[X]/(X² + 1) is an algebraically closed field.
-/

namespace Azurite.BPR.Theorem2_11

open Polynomial

/-! ### R[i] = R[X]/(X² + 1) -/

/-- R[i] := R[X]/(X² + 1), the "complex numbers" over a real closed field R. -/
noncomputable abbrev Ri (R : Type*) [CommRing R] :=
  AdjoinRoot (X ^ 2 + 1 : R[X])

/-- The imaginary unit `i` in R[i], i.e., the image of X in R[X]/(X² + 1). -/
noncomputable def Ri.i (R : Type*) [CommRing R] : Ri R :=
  AdjoinRoot.root (X ^ 2 + 1 : R[X])

/-- Conjugation on R[i]: the R-algebra automorphism sending i ↦ −i. -/
noncomputable def Ri.conj (R : Type*) [CommRing R] : Ri R →ₐ[R] Ri R :=
  { AdjoinRoot.lift (AdjoinRoot.of (X ^ 2 + 1 : R[X])) (-Ri.i R)
      (by
        simp only [Ri.i, eval₂_add, eval₂_pow, eval₂_one, eval₂_X, neg_sq]
        have h := AdjoinRoot.eval₂_root (X ^ 2 + 1 : R[X])
        simpa [eval₂_add, eval₂_pow, eval₂_one, eval₂_X] using h) with
    commutes' := fun r => by simp [AdjoinRoot.lift_of] }

/-- Apply conjugation to the coefficients of a polynomial over R[i]. -/
noncomputable def conjPoly (R : Type*) [CommRing R] : (Ri R)[X] → (Ri R)[X] :=
  Polynomial.map (Ri.conj R)

/-! ### Combinatorial indexing -/

/-- The set of ordered pairs (i, j) with i < j from Fin p. -/
def strictPairs (p : ℕ) : Finset (Fin p × Fin p) :=
  Finset.univ.filter (fun ij => ij.1 < ij.2)

/-! ### The polynomials Q, D, F, G, H -/

variable {L : Type*} [Field L] {p : ℕ}

/-- γ_{ij}(Z) = x_i + x_j + Z · x_i · x_j ∈ L[Z].
    Here Z is the polynomial indeterminate. -/
noncomputable def gammaPoly (x : Fin p → L) (i j : Fin p) : L[X] :=
  Polynomial.C (x i + x j) + Polynomial.X * Polynomial.C (x i * x j)

/-- Q(Z, Y) = ∏_{i < j} (Y − γ_{ij}(Z)) ∈ L[Z][Y].
    The outer polynomial ring is in Y; coefficients are polynomials in Z. -/
noncomputable def QPolynomial (x : Fin p → L) : (L[X])[X] :=
  ∏ ij ∈ strictPairs p,
    (Polynomial.X - Polynomial.C (gammaPoly x ij.1 ij.2))

/-- D(Z) = ∏_{a ≠ b in strictPairs} (γ_a(Z) − γ_b(Z)) ∈ L[Z].
    This is (up to sign) the square of the standard discriminant of Q w.r.t. Y.
    D(z) ≠ 0 iff all γ_{ij}(z) are distinct. -/
noncomputable def discPoly (x : Fin p → L) : L[X] :=
  ∏ ab ∈ (strictPairs p).offDiag,
    (gammaPoly x ab.1.1 ab.1.2 - gammaPoly x ab.2.1 ab.2.2)

/-- F(Z, Y) = ∂Q/∂Y, the formal derivative of Q with respect to Y. -/
noncomputable def FPoly (x : Fin p → L) : (L[X])[X] :=
  Polynomial.derivative (QPolynomial x)

/-- G(Z, Y) = ∑_{i<j} (x_i + x_j) · ∏_{(k,l)≠(i,j)} (Y − γ_{kl}(Z)).
    Evaluating at a root γ_{ij} of Q extracts x_i + x_j. -/
noncomputable def GPoly (x : Fin p → L) : (L[X])[X] :=
  ∑ ij ∈ strictPairs p,
    Polynomial.C (Polynomial.C (x ij.1 + x ij.2)) *
    ∏ kl ∈ (strictPairs p).erase ij,
      (Polynomial.X - Polynomial.C (gammaPoly x kl.1 kl.2))

/-- H(Z, Y) = ∑_{i<j} (x_i · x_j) · ∏_{(k,l)≠(i,j)} (Y − γ_{kl}(Z)).
    Evaluating at a root γ_{ij} of Q extracts x_i · x_j. -/
noncomputable def HPoly (x : Fin p → L) : (L[X])[X] :=
  ∑ ij ∈ strictPairs p,
    Polynomial.C (Polynomial.C (x ij.1 * x ij.2)) *
    ∏ kl ∈ (strictPairs p).erase ij,
      (Polynomial.X - Polynomial.C (gammaPoly x kl.1 kl.2))

/-! ### Infrastructure lemmas -/

variable {R : Type*} [Field R]

/-- In a real closed field, −1 is not a square. -/
theorem not_isSquare_neg_one [IsRealClosed R] : ¬ IsSquare (-1 : R) := by
  intro h
  exact IsSemireal.not_isSumSq_neg_one R h.isSumSq

/-- X² + 1 is irreducible over a real closed field R. -/
theorem irred_X_sq_add_one [IsRealClosed R] :
    Irreducible (X ^ 2 + 1 : R[X]) := by
  apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
  · have : (X ^ 2 + 1 : R[X]).natDegree = 2 := by
      rw [show (1 : R[X]) = C 1 from rfl]; exact natDegree_X_pow_add_C
    simp [this, Finset.mem_Icc]
  · intro x
    simp only [IsRoot, eval_add, eval_pow, eval_X, eval_one]
    intro h
    have : (-1 : R) = x * x := by linear_combination -h
    exact not_isSquare_neg_one ⟨x, this⟩

/-- X² + 1 is irreducible (as a Fact, for AdjoinRoot.instField). -/
instance [IsRealClosed R] : Fact (Irreducible (X ^ 2 + 1 : R[X])) :=
  ⟨irred_X_sq_add_one⟩

/-- The defining relation: i² = −1 in R[i]. -/
theorem Ri.i_sq (R : Type*) [CommRing R] :
    (Ri.i R) ^ 2 = -(1 : Ri R) := by
  have h : AdjoinRoot.mk (X ^ 2 + 1 : R[X]) (X ^ 2 + 1 : R[X]) = 0 := AdjoinRoot.mk_self
  simp only [map_add, map_pow, map_one, AdjoinRoot.mk_X] at h
  unfold Ri.i
  linear_combination h

/-- For any a ∈ R, there exists v ∈ R[i] with v² = a. -/
theorem sqrt_of_R_in_Ri [IsRealClosed R] (a : R) :
    ∃ v : Ri R, v ^ 2 = algebraMap R (Ri R) a := by
  rcases IsRealClosed.isSquare_or_isSquare_neg a with ⟨c, hc⟩ | ⟨c, hc⟩
  · exact ⟨algebraMap R (Ri R) c, by
      rw [sq]; simp only [← map_mul, hc]⟩
  · refine ⟨algebraMap R (Ri R) c * Ri.i R, ?_⟩
    rw [mul_pow, Ri.i_sq]
    simp only [sq, ← map_mul, mul_neg, mul_one, ← map_neg]
    have : -(c * c) = a := by rw [← hc, neg_neg]
    simp only [this]

/-! ### Degree arithmetic -/

/-- If p = 2^m · n with m ≥ 1 and n odd, then p(p−1)/2 = 2^{m−1} · n' with n' odd. -/
theorem half_degree_odd_factor {m n : ℕ} (hm : 1 ≤ m) (hn : Odd n) (hp : 0 < n) :
    ∃ n' : ℕ, Odd n' ∧ 2 ^ m * n * (2 ^ m * n - 1) / 2 = 2 ^ (m - 1) * n' := by
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
  subst hk
  simp only [Nat.succ_sub_one]
  refine ⟨n * (2 ^ (k + 1) * n - 1), ?_, ?_⟩
  · apply Odd.mul hn
    refine Nat.Even.sub_odd ?_ ?_ odd_one
    · exact Nat.one_le_iff_ne_zero.mpr (by positivity)
    · exact Even.mul_right ⟨2 ^ k, by ring⟩ n
  · rw [show 2 ^ (k + 1) = 2 * 2 ^ k from by ring]
    rw [show 2 * 2 ^ k * n * (2 * 2 ^ k * n - 1) =
        2 * (2 ^ k * n * (2 * 2 ^ k * n - 1)) from by ring]
    rw [Nat.mul_div_cancel_left _ (by norm_num : 0 < 2)]
    ring

/-! ### Conjugation properties -/

variable {R : Type*} [Field R]

/-- Conjugation is an involution: conj (conj z) = z. -/
theorem Ri.conj_conj [IsRealClosed R] (z : Ri R) :
    (Ri.conj R) ((Ri.conj R) z) = z := by
  have h : (Ri.conj R).comp (Ri.conj R) = AlgHom.id R (Ri R) := by
    apply AdjoinRoot.algHom_ext
    simp only [Ri.conj, AlgHom.comp_apply, AlgHom.coe_mk, Ri.i,
      AdjoinRoot.lift_root, map_neg, neg_neg, AlgHom.id_apply]
  exact AlgHom.congr_fun h z

/-- Conjugation fixes elements of R: conj (algebraMap R (Ri R) r) = algebraMap R (Ri R) r. -/
theorem Ri.conj_algebraMap [IsRealClosed R] (r : R) :
    (Ri.conj R) (algebraMap R (Ri R) r) = algebraMap R (Ri R) r :=
  (Ri.conj R).commutes r

/-- Polynomial evaluation commutes with conjugation:
    If P ∈ Ri[X] and z ∈ Ri, then conj(P(z)) = P̄(conj(z)). -/
theorem conj_eval_eq_eval_conj_map [IsRealClosed R]
    (P : (Ri R)[X]) (z : Ri R) :
    (Ri.conj R) (P.eval z) = (conjPoly R P).eval ((Ri.conj R) z) := by
  simp only [conjPoly, Polynomial.eval_map]
  induction P using Polynomial.induction_on' with
  | add p q hp hq =>
    simp only [eval_add, map_add, eval₂_add]
    rw [hp, hq]
  | monomial n a =>
    simp only [eval_monomial, map_mul, map_pow, eval₂_monomial, RingHom.coe_coe]

end Azurite.BPR.Theorem2_11
