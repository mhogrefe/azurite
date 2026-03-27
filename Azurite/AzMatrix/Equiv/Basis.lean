/-
  Equivalence proofs for AzMatrix identity and single-entry matrices.

  Links `AzMatrix.identity` to Mathlib's `1 : Matrix` and
  `AzMatrix.single` to `Matrix.stdBasisMatrix`.
-/
import Azurite.AzMatrix.Operations
import Mathlib.Data.Matrix.Basic

namespace Azurite
variable {R : Type _} [Zero R] [One R] {m n : Nat}

/-- The identity matrix equals Mathlib's `1 : Matrix (Fin n) (Fin n) R`. -/
theorem AzMatrix.toFn_identity :
    (AzMatrix.identity (R := R) (n := n)).toFn = fun i j => if i = j then 1 else 0 := by
  ext i j; simp [identity, toFn, ofFn, Vector.get]

/-- The single-entry matrix equals Mathlib's `Matrix.stdBasisMatrix`. -/
theorem AzMatrix.toFn_single (i₀ : Fin m) (j₀ : Fin n) :
    (AzMatrix.single (R := R) i₀ j₀).toFn = fun i j => if i = i₀ ∧ j = j₀ then 1 else 0 := by
  ext i j; simp [single, toFn, ofFn, Vector.get]

/-- `ofFn` of the identity function yields `AzMatrix.identity`. -/
theorem AzMatrix.ofFn_identity :
    AzMatrix.ofFn (fun (i j : Fin n) => if i = j then (1 : R) else 0) = AzMatrix.identity := rfl

/-- `ofFn` of a single-entry function yields `AzMatrix.single`. -/
theorem AzMatrix.ofFn_single (i₀ : Fin m) (j₀ : Fin n) :
    AzMatrix.ofFn (fun i j => if i = i₀ ∧ j = j₀ then (1 : R) else 0) =
      AzMatrix.single i₀ j₀ := rfl

end Azurite
