import Azurite.BasuPollackRoy.Chapter4.Section4_2.Lemma_4_18

/-!
# BPR Proposition 4.20: the Sylvester matrix as a Jacobian

Identifying a monic polynomial `X^q + b_{q-1} X^{q-1} + ⋯ + b_0` with
the tuple `(b_{q-1}, …, b_0) ∈ R^q` and dually for monic `X^p + ⋯`,
the multiplication-of-monics map

  `m : R^q × R^p → R^{p+q}`,
  `m(b, a)_j := (Q · P).coeff j`

(where `Q = X^q + ∑_α b_α X^α` and `P = X^p + ∑_β a_β X^β`) has
partial derivatives

  `∂m_j / ∂b_α = (X^α · P).coeff j`,
  `∂m_j / ∂a_β = (X^β · Q).coeff j`,

read directly from the bilinearity of polynomial multiplication
(`b_q = a_p = 1` are constants, so each `m_j` is a polynomial of degree
2 in the `b_α, a_β` variables and the partial derivatives are linear in
the remaining variables — exactly the polynomial-shift coefficients
that build the Sylvester matrix).

We package this Jacobian as the matrix `monicMulJacobian P Q p q` and
show it equals Mathlib's `Polynomial.sylvester P Q p q` under the
natural degree bounds. Combined with the
`Res = Polynomial.resultant` bridge from Lemma 4.18, the determinant
identity `det(Jacobian) = Res(P, Q)` follows.
-/

namespace Azurite.BPR.Chapter4

open Polynomial

variable {R : Type*} [CommRing R]

/-- BPR's polynomial multiplication map.

    Takes the non-leading coefficients `b : Fin q → R` of a monic
    polynomial `Q = X^q + ∑_α b_α X^α` and `a : Fin p → R` of a monic
    `P = X^p + ∑_β a_β X^β`, returns the non-leading coefficients of
    the product `Q · P` (a monic polynomial of degree `p + q`).

    Output coordinate `j` is the coefficient of `X^j` in `Q · P`, for
    `j ∈ Fin (p + q)`. -/
noncomputable def monicMulMap (p q : ℕ) (b : Fin q → R) (a : Fin p → R)
    (j : Fin (p + q)) : R :=
  let Q : R[X] := X ^ q + ∑ α : Fin q, monomial α.val (b α)
  let P : R[X] := X ^ p + ∑ β : Fin p, monomial β.val (a β)
  (Q * P).coeff j.val

/-- The Jacobian matrix of `monicMulMap` at the point corresponding to
    polynomials `(Q, P)`. Rows are indexed by the output coordinate
    `j ∈ Fin (p + q)`; columns are indexed by the input variable, with
    the first `p` columns corresponding to the `a_β` inputs and the
    last `q` columns to the `b_α` inputs — matching Mathlib's
    `Polynomial.sylvester` column convention.

    Entry at `(j, i)`:
    * if `i.val < p` (column is `a_i`-derivative):
      `∂m_j / ∂a_i = (X^i · Q).coeff j`,
    * if `i.val ≥ p` (column is `b_{i-p}`-derivative):
      `∂m_j / ∂b_{i-p} = (X^{i-p} · P).coeff j`.

    These formulas come straight from the bilinearity of polynomial
    multiplication; see the file docstring for the derivation. -/
noncomputable def monicMulJacobian (P Q : R[X]) (p q : ℕ) :
    Matrix (Fin (p + q)) (Fin (p + q)) R :=
  Matrix.of fun (j i : Fin (p + q)) =>
    if i.val < p then (X ^ i.val * Q).coeff j.val
    else (X ^ (i.val - p) * P).coeff j.val

/-- Under the natural degree bounds, the BPR Jacobian matrix
    coincides with Mathlib's `Polynomial.sylvester P Q p q`. -/
theorem monicMulJacobian_eq_sylvester (P Q : R[X]) (p q : ℕ)
    (hP : P.natDegree ≤ p) (hQ : Q.natDegree ≤ q) :
    monicMulJacobian P Q p q = Polynomial.sylvester P Q p q := by
  ext j i
  unfold monicMulJacobian Polynomial.sylvester
  rw [Matrix.of_apply, Matrix.of_apply]
  by_cases hi : i.val < p
  · -- Q-shift case.
    rw [if_pos hi]
    rw [Polynomial.coeff_X_pow_mul']
    have h_natAdd : i = Fin.castAdd q ⟨i.val, hi⟩ := by
      apply Fin.ext; rfl
    conv_rhs => rw [h_natAdd, Fin.addCases_left]
    simp only [Set.mem_Icc]
    split_ifs with h1 h2 h2
    · rfl
    · apply Polynomial.coeff_eq_zero_of_natDegree_lt
      push Not at h2
      have := h2 h1
      omega
    · exfalso; omega
    · rfl
  · -- P-shift case.
    push Not at hi
    rw [if_neg (not_lt.mpr hi)]
    rw [Polynomial.coeff_X_pow_mul']
    have hi_sub : i.val - p < q := by
      have := i.isLt; omega
    have h_castAdd : i = Fin.natAdd p ⟨i.val - p, hi_sub⟩ := by
      apply Fin.ext
      show i.val = p + (i.val - p)
      omega
    conv_rhs => rw [h_castAdd, Fin.addCases_right]
    simp only [Set.mem_Icc]
    split_ifs with h1 h2 h2
    · rfl
    · apply Polynomial.coeff_eq_zero_of_natDegree_lt
      push Not at h2
      have := h2 h1
      omega
    · exfalso; omega
    · rfl

/-- **BPR Proposition 4.20.** The Jacobian matrix of the
    monic-multiplication map is the Sylvester matrix of `P` and `Q`,
    and the Jacobian (determinant) is the resultant. -/
theorem Proposition_4_20 (P Q : R[X]) (p q : ℕ)
    (hP : P.natDegree ≤ p) (hQ : Q.natDegree ≤ q) :
    (monicMulJacobian P Q p q).det = Res P p Q q := by
  rw [monicMulJacobian_eq_sylvester P Q p q hP hQ]
  show (Polynomial.sylvester P Q p q).det = Res P p Q q
  rw [Res_eq_resultant P Q p q hP hQ]
  rfl

end Azurite.BPR.Chapter4
