import Azurite.BasuPollackRoy.Chapter2.Section2_4.RealizationOverZeroSet
import Mathlib.Data.Matrix.Basic

/-!
# BPR Definition 2.66: The matrix of signs

Number the family `𝒬 = {Q₁, …, Q_s}` (so the index type is `ι = Fin s`).
Let `A = (α₁, …, α_m)` be a list of elements of `{0,1,2}^𝒬` and
`Σ = (σ₁, …, σ_n)` a list of elements of `{0,1,-1}^𝒬`, **both taken in
the BPR lexicographic order** (Definition~2.14): `0 < 1 < 2` on
`{0,1,2}^𝒬`, and `0 ≺ 1 ≺ -1` on `{0,1,-1}^𝒬`.

> ⚠️ The sign order is BPR's `0 ≺ 1 ≺ -1`, **not** the natural
> `LinearOrder` on `SignType` (`-1 < 0 < 1`). The matrix below is
> parametrised by the lists `A`, `Σ`, so the row/column order *is* the
> order of those lists; the lex order enters when those lists are built.

The **matrix of signs** of `𝒬^A` on `Σ` is the `m × n` matrix
`Mat(A, Σ)` whose `(i, j)`-entry is `σ_j^{α_i}` (`= SignCondition.pow`),
relating `TaQ(𝒬^A, P)` (rows) to `c(Σ, Z)` (columns) in the sequel.
Its entries lie in `SignType` (the signs `0, 1, -1`); cast to `ℤ` for the
linear-algebraic relations.
-/

namespace Azurite.BPR

open Polynomial

variable {ι : Type*} [Fintype ι]

/-- **BPR Definition 2.66.** The *matrix of signs* of `𝒬^A` on `Σ`: the
`m × n` matrix `Mat(A, Σ)` (`m = A.length`, `n = Σ.length`) whose
`(i, j)`-entry is `σ_j^{α_i} = ∏_{Q} σ_j(Q)^{α_i(Q)}`
(`SignCondition.pow (Σ.get j) (A.get i)`). Rows are indexed by the
exponent list `A` and columns by the sign-condition list `Σ`, in their
given (BPR-lex) order. -/
def matrixOfSigns (A : List (ι → ℕ)) (S : List (SignCondition ι)) :
    Matrix (Fin A.length) (Fin S.length) SignType :=
  fun i j => (S.get j).pow (A.get i)

@[simp] theorem matrixOfSigns_apply (A : List (ι → ℕ)) (S : List (SignCondition ι))
    (i : Fin A.length) (j : Fin S.length) :
    matrixOfSigns A S i j = (S.get j).pow (A.get i) :=
  rfl

end Azurite.BPR
