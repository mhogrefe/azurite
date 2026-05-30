import Mathlib.LinearAlgebra.Matrix.Kronecker

/-!
# BPR Notation 2.69: tensor product of matrices

For matrices `M` (dimensions `n × m`) and `M' = [m'_{ij}]`
(dimensions `n' × m'`), the *tensor product* `M ⊗ M'` is the
`nn' × mm'` matrix `[m_{ij} M']` — the block matrix whose `(i, j)`-block
is the scalar multiple `m_{ij} · M'`.

This is exactly the Kronecker product `Matrix.kroneckerMap (· * ·)` from
Mathlib (notation `⊗ₖ`): its `((i, i'), (j, j'))`-entry is
`m_{ij} · m'_{i'j'}`, i.e. the `(i', j')`-entry of the block `m_{ij} M'`.
We expose it under the BPR name `matrixTensor` with notation `⊗ₘ`.

The index types are products `l × n` and `m × p` rather than `Fin (nn')`,
`Fin (mm')`; their cardinalities are the BPR dimensions `nn'` and `mm'`.
-/

namespace Azurite.BPR

open scoped Kronecker

variable {α : Type*} [Mul α] {l m n p : Type*}

/-- **BPR Notation 2.69.** The *tensor product* `M ⊗ M'` of matrices: the
block matrix `[m_{ij} M']`, equal to the Kronecker product
`M ⊗ₖ M'`. Its `((i, i'), (j, j'))`-entry is `M i j * M' i' j'`. -/
def matrixTensor (M : Matrix l m α) (M' : Matrix n p α) : Matrix (l × n) (m × p) α :=
  M ⊗ₖ M'

@[inherit_doc] scoped infixl:100 " ⊗ₘ " => Azurite.BPR.matrixTensor

/-- The `((i, i'), (j, j'))`-entry of `M ⊗ M'` is `m_{ij} · m'_{i'j'}`,
the `(i', j')`-entry of the block `m_{ij} M'`. -/
@[simp] theorem matrixTensor_apply (M : Matrix l m α) (M' : Matrix n p α)
    (i : l × n) (j : m × p) :
    (M ⊗ₘ M') i j = M i.1 j.1 * M' i.2 j.2 :=
  rfl

/-- The BPR tensor product is the Mathlib Kronecker product. -/
theorem matrixTensor_eq_kronecker (M : Matrix l m α) (M' : Matrix n p α) :
    M ⊗ₘ M' = M ⊗ₖ M' :=
  rfl

end Azurite.BPR
