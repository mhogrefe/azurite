import Azurite.BasuPollackRoy.Chapter4.Section4_2.Lemma_4_18

/-!
# BPR Proposition 4.19: resultant lies in the ideal `(P, Q)`

For polynomials `P, Q : D[X]` over a commutative ring `D`, the resultant
`Res(P, Q)` can be written as a `D[X]`-linear combination of `P` and `Q`
with small-degree cofactors:

  there exist `U, V : D[X]` with `deg U < q`, `deg V < p`, and
  `Res(P, Q) = U·P + V·Q`.

BPR's proof modifies the Sylvester matrix's last column to hold the
polynomials `X^{q-1} P, …, P, X^{p-1} Q, …, Q` (instead of their leading
coefficient values), expands the determinant of the modified matrix by
this last column to read `Res(P, Q) + ∑_{j ≥ 1} d_j X^j`, and observes
that each `d_j` is the determinant of a matrix with two equal columns
(hence zero), reducing the determinant to `Res(P, Q)`. The cofactor
expansion along the last column then gives the desired identity.

Mathlib's `Polynomial.exists_mul_add_mul_eq_C_resultant` already
establishes this for its `resultant`. We transport it across our
`Res = Polynomial.resultant` bridge (Lemma 4.18).
-/

namespace Azurite.BPR.Chapter4

open Polynomial

variable {D : Type*} [CommRing D]

/-- **BPR Proposition 4.19.** For `P, Q : D[X]` with `P.natDegree ≤ p`,
    `Q.natDegree ≤ q`, and `(p, q) ≠ (0, 0)`, there exist
    `U, V : D[X]` with `deg U < q`, `deg V < p` such that

      `C (Res(P, Q)) = U · P + V · Q`

    in `D[X]` (where `C` embeds the scalar `Res(P, Q) ∈ D` as a constant
    polynomial). -/
theorem Proposition_4_19 (P Q : D[X]) (p q : ℕ)
    (hP : P.natDegree ≤ p) (hQ : Q.natDegree ≤ q)
    (H : p ≠ 0 ∨ q ≠ 0) :
    ∃ U V : D[X], U.degree < q ∧ V.degree < p ∧
      C (Res P p Q q) = U * P + V * Q := by
  rw [Res_eq_resultant P Q p q hP hQ]
  obtain ⟨U, V, hU, hV, h_eq⟩ :=
    Polynomial.exists_mul_add_mul_eq_C_resultant P Q hP hQ H
  refine ⟨U, V, hU, hV, ?_⟩
  linear_combination -h_eq

end Azurite.BPR.Chapter4
