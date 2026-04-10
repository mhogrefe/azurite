import Azurite.AzMatrix.Pow

/-!
# Equivalence: AzMatrix.pow ↔ Matrix.pow

Proves that `AzMatrix.pow A k` (computable, via exponentiation by squaring)
agrees with Mathlib's `Matrix.pow` (i.e., `toMat A ^ k`).

Since the `Semiring` instance on `AzMatrix R n n` already uses `fastPow` as its `npow`,
`A.pow k` is definitionally `A ^ k`, and `toMat (A ^ k) = toMat A ^ k` follows from
the `toMat_npow` lemma in `Equiv/Algebra.lean`.

Note: We use `toMat` (which has type `Matrix (Fin n) (Fin n) R`) rather than `toFn`
(which gives `Fin n → Fin n → R`) because matrix power and pointwise power are different.

## Main Theorems

- `toMat_pow`: `toMat (A.pow k) = toMat A ^ k`
- `ofFn_pow`: `(ofFn f).pow k = ofFn (f ^ k)`
- `get_pow`: `(A.pow k).get i j = (toMat A ^ k) i j`
-/

namespace Azurite

variable {R : Type _} [CommSemiring R] {n : Nat}

/-- Forward direction: `toMat` preserves `pow`.
    Uses `toMat` (not `toFn`) to get the `Matrix`-level `^` rather than `Pi.pow`. -/
@[simp] theorem AzMatrix.toMat_pow (A : AzMatrix R n n) (k : ℕ) :
    toMat (A.pow k) = toMat A ^ k := by
  show toMat (Azurite.fastPow A k) = _
  rw [Azurite.fastPow, toMat_fastPowAux, toMat_one, one_mul]

/-- Component-wise access for matrix power. -/
theorem AzMatrix.get_pow (A : AzMatrix R n n) (k : ℕ) (i j : Fin n) :
    (A.pow k).get i j = (toMat A ^ k) i j :=
  congr_fun (congr_fun (AzMatrix.toMat_pow A k) i) j

omit [CommSemiring R] in
private lemma toMat_ofFn (f : Matrix (Fin n) (Fin n) R) :
    toMat (AzMatrix.ofFn f) = f := by
  ext i j; exact AzMatrix.toFn_ofFn f i j

/-- Backward direction: `ofFn` preserves `pow`. -/
@[simp] theorem AzMatrix.ofFn_pow (f : Matrix (Fin n) (Fin n) R) (k : ℕ) :
    (AzMatrix.ofFn f).pow k = AzMatrix.ofFn (f ^ k) := by
  apply AzMatrix.ext; intro i j
  have h := AzMatrix.toMat_pow (AzMatrix.ofFn f) k
  rw [toMat_ofFn] at h
  exact (congr_fun (congr_fun h i) j).trans (AzMatrix.toFn_ofFn _ i j).symm

end Azurite
