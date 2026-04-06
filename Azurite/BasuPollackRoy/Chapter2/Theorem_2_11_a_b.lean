import Mathlib.RingTheory.AdjoinRoot
import Mathlib.FieldTheory.IsRealClosed.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.FieldTheory.Separable

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

end Azurite.BPR.Theorem2_11
