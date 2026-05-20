import Azurite.BasuPollackRoy.Chapter4.Section4_2.Notation_4_22
import Mathlib.Algebra.Polynomial.Coeff

/-!
# BPR Remark 4.23: Sylvester-Habicht matrix as transposed multiplication map

For polynomials `P, Q : D[X]` (over a commutative ring `D`) and index
`j ∈ ℕ` (with BPR's intended range `0 ≤ j ≤ min(Q.natDegree, P.natDegree
- 1)`), the linear map
  `μ_j : (U, V) ↦ U · P + V · Q`,
acting on pairs `(U, V)` with `deg U < Q.natDegree - j` and
`deg V < P.natDegree - j`, becomes a linear map between free `D`-modules
of rank `P.natDegree + Q.natDegree - 2 j`. After composing with the
truncation
  `D[X]_{< p + q - j}  →  D^{p + q - 2 j}`,
  `f  ↦  (f.coeff (p + q - j - 1), …, f.coeff j)`,
which drops the lowest `j` coefficients, the matrix of the composite map
(transposed) is exactly the square Sylvester-Habicht submatrix
`SyHa_{j,j}(P, Q)` of Notation 4.22.

In analogy with Remark 4.14, we formalize this operationally by
defining `SyHa.mulMap P Q j uv` as the polynomial output of `μ_j` on
the coordinate vector `uv` (a single-sum form combining `U·P` and
`V·Q`), and stating `SyHa.transpose_mulVec_apply` which says that the
`(p + q - j)-dimensional` output of multiplying by `(SyHa P Q j)ᵀ` is
the full coefficient vector of `μ_j(uv)` in the descending power basis
`X^{p + q - j - 1}, …, X, 1`. The square-submatrix interpretation —
restricting to the first `p + q - 2j` of those coefficients — is the
content of Lemma 4.24 (the vanishing-subresultant criterion).
-/

namespace Azurite.BPR.Chapter4

open Polynomial

variable {D : Type*} [CommRing D]

/-- The polynomial output of the multiplication map
    `μ_j : (U, V) ↦ U·P + V·Q` (with `deg U < q - j`, `deg V < p - j`),
    expressed directly on the coordinate vector
    `uv : Fin (P.natDegree + Q.natDegree - 2 j) → D`.

    Each coordinate `uv i` contributes either to `U · P` (when `i.val
    < Q.natDegree - j`, multiplying the basis vector `X^{q - j - 1 - i}`
    by `P`) or to `V · Q` (when `i.val ≥ Q.natDegree - j`, multiplying
    `X^{i - (q - j)}` by `Q`). Note that unlike `Syl.mulMap`, the
    Q-block uses *increasing* powers `X^0 Q, X^1 Q, …` to match
    `SyHa`'s row convention. -/
noncomputable def SyHa.mulMap (P Q : D[X]) (j : ℕ)
    (uv : Fin (P.natDegree + Q.natDegree - 2 * j) → D) : D[X] :=
  ∑ i : Fin (P.natDegree + Q.natDegree - 2 * j),
    C (uv i) *
      (if i.val < Q.natDegree - j then
          X ^ (Q.natDegree - j - 1 - i.val) * P
        else
          X ^ (i.val - (Q.natDegree - j)) * Q)

/-- **BPR Remark 4.23.** Multiplying the transpose of the
    (rectangular) Sylvester-Habicht matrix `SyHa P Q j` by a coordinate
    vector `uv` produces the coefficient vector (in the descending
    power basis `X^{p + q - j - 1}, …, X, 1`) of the polynomial
    `μ_j(uv) =` `SyHa.mulMap P Q j uv`. -/
theorem SyHa.transpose_mulVec_apply (P Q : D[X]) (j : ℕ)
    (uv : Fin (P.natDegree + Q.natDegree - 2 * j) → D)
    (i : Fin (P.natDegree + Q.natDegree - j)) :
    (SyHa P Q j).transpose.mulVec uv i =
      (SyHa.mulMap P Q j uv).coeff
        (P.natDegree + Q.natDegree - j - 1 - i.val) := by
  show ∑ k, (SyHa P Q j).transpose i k * uv k = _
  unfold SyHa.mulMap
  rw [Polynomial.finsetSum_coeff]
  apply Finset.sum_congr rfl
  intro k _
  rw [Matrix.transpose_apply, Polynomial.coeff_C_mul,
      apply_ite (Polynomial.coeff ·
        (P.natDegree + Q.natDegree - j - 1 - i.val))]
  show (SyHa P Q j) k i * uv k = _
  unfold SyHa
  rw [Matrix.of_apply, mul_comm]

end Azurite.BPR.Chapter4
