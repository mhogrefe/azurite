import Azurite.BasuPollackRoy.Chapter4.Section4_2.Notation_4_13
import Mathlib.Algebra.Polynomial.Coeff

/-!
# BPR Remark 4.14: Sylvester matrix as transposed multiplication map

For polynomials `P, Q : D[X]` (over a commutative ring `D`) and degrees
`p, q : ℕ`, the linear map
  `μ : (U, V) ↦ U · P + V · Q`,
acting on pairs `(U, V)` with `deg U < q` and `deg V < p`, becomes a
linear map between free `D`-modules of rank `p + q`. Identifying

  domain ≅ D^{p+q}    via the basis `X^{q-1}, …, 1` ⊕ `X^{p-1}, …, 1`,
  codomain ≅ D^{p+q}  via the basis `X^{p+q-1}, …, X, 1`,

the matrix of `μ` is the transpose of the Sylvester matrix `Syl(P, Q)`:
its `j`-th column is the coordinate vector of the image of the `j`-th
basis vector of the domain, which is `X^{q-1-j} · P` for `j < q` and
`X^{p+q-1-j} · Q` for `j ≥ q` — these are precisely the **rows** of
`Syl(P, Q)`.

We formalize this by giving the explicit polynomial form of
`(Syl P p Q q).transpose .mulVec uv`: the coefficient of `X^{p+q-1-i}`
of the polynomial `μ(uv)`, where `μ(uv)` is the single-sum form
combining both `U·P` and `V·Q` directly.
-/

namespace Azurite.BPR.Chapter4

open Polynomial

variable {D : Type*} [CommRing D]

/-- The polynomial output of the multiplication map `μ : (U, V) ↦ U·P + V·Q`,
    expressed directly on the coordinate vector `uv : Fin (p + q) → D`.
    Each coordinate `uv j` contributes either to `U · P` (when `j < q`,
    multiplying the basis vector `X^{q-1-j}` by `P`) or to `V · Q`
    (when `j ≥ q`, multiplying `X^{p+q-1-j}` by `Q`). -/
noncomputable def Syl.mulMap (P : D[X]) (p : ℕ) (Q : D[X]) (q : ℕ)
    (uv : Fin (p + q) → D) : D[X] :=
  ∑ j : Fin (p + q),
    C (uv j) *
      (if j.val < q then X ^ (q - 1 - j.val) * P
        else X ^ (p + q - 1 - j.val) * Q)

/-- **BPR Remark 4.14.** Applying the transpose of the Sylvester matrix
    to a coordinate vector `uv` produces the coefficient vector (in the
    descending power basis) of the polynomial `μ(uv) = U·P + V·Q`. -/
theorem Syl.transpose_mulVec_apply (P : D[X]) (p : ℕ) (Q : D[X]) (q : ℕ)
    (uv : Fin (p + q) → D) (i : Fin (p + q)) :
    (Syl P p Q q).transpose.mulVec uv i =
      (Syl.mulMap P p Q q uv).coeff (p + q - 1 - i.val) := by
  show ∑ j, (Syl P p Q q).transpose i j * uv j = _
  unfold Syl.mulMap
  rw [Polynomial.finsetSum_coeff]
  apply Finset.sum_congr rfl
  intro j _
  rw [Matrix.transpose_apply, Polynomial.coeff_C_mul,
      apply_ite (Polynomial.coeff · (p + q - 1 - i.val))]
  show (Syl P p Q q) j i * uv j = _
  unfold Syl
  rw [Matrix.of_apply, mul_comm]

end Azurite.BPR.Chapter4
