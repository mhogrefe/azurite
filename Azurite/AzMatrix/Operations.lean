/-
  Operations for AzMatrix: Zero, identity, single-entry, transpose.
  Computable predicates for symmetric / skew-symmetric.
-/
import Azurite.AzMatrix.Basic

namespace Azurite
variable {R : Type _} {m n : Nat}

/-! ### Zero -/

instance [Zero R] : Zero (AzMatrix R m n) :=
  ⟨⟨Vector.ofFn (fun _ => Vector.ofFn (fun _ => 0))⟩⟩

/-! ### Identity -/

/-- The identity matrix. Requires square dimensions. -/
def AzMatrix.identity [Zero R] [One R] : AzMatrix R n n :=
  AzMatrix.ofFn (fun i j => if i = j then 1 else 0)

/-! ### Single-entry matrix -/

/-- A matrix with a 1 at position `(i₀, j₀)` and 0 elsewhere. -/
def AzMatrix.single [Zero R] [One R] (i₀ : Fin m) (j₀ : Fin n) : AzMatrix R m n :=
  AzMatrix.ofFn (fun i j => if i = i₀ ∧ j = j₀ then 1 else 0)

/-! ### Transpose -/

/-- Matrix transpose: `(Mᵀ)ᵢⱼ = Mⱼᵢ`. -/
def AzMatrix.transpose (M : AzMatrix R m n) : AzMatrix R n m :=
  AzMatrix.ofFn (fun j i => M.get i j)

/-! ### Symmetric predicates -/

/-- Computable check whether a square matrix is symmetric: `Mᵢⱼ = Mⱼᵢ` for all `i, j`. -/
def AzMatrix.isSymmetricB [DecidableEq R] (M : AzMatrix R n n) : Bool :=
  decide (∀ (i j : Fin n), M.get i j = M.get j i)

/-- Computable check whether a square matrix is skew-symmetric: `Mᵢⱼ = -Mⱼᵢ` for all `i, j`. -/
def AzMatrix.isSkewSymmetricB [DecidableEq R] [Neg R] (M : AzMatrix R n n) : Bool :=
  decide (∀ (i j : Fin n), M.get i j = -(M.get j i))

/-! ### toFn simp lemmas -/

@[simp]
theorem AzMatrix.toFn_zero [Zero R] (i : Fin m) (j : Fin n) :
    (0 : AzMatrix R m n).toFn i j = 0 := by
  show ((Vector.ofFn (fun _ => Vector.ofFn (fun _ => (0 : R)))).get i).get j = 0
  simp [Vector.get]

@[simp]
theorem AzMatrix.get_zero [Zero R] (i : Fin m) (j : Fin n) :
    (0 : AzMatrix R m n).get i j = 0 := by
  show ((Vector.ofFn (fun _ => Vector.ofFn (fun _ => (0 : R)))).get i).get j = 0
  simp [Vector.get]

@[simp]
theorem AzMatrix.toFn_transpose (M : AzMatrix R m n) :
    M.transpose.toFn = fun j i => M.toFn i j := by
  ext j i; simp [transpose, toFn, ofFn, get, Vector.get]

/-! ### Negation -/

instance [Neg R] : Neg (AzMatrix R m n) :=
  ⟨fun M => M.map (- ·)⟩

@[simp]
theorem AzMatrix.toFn_neg [Neg R] (M : AzMatrix R m n) (i : Fin m) (j : Fin n) :
    (-M).toFn i j = -(M.toFn i j) := by
  show (M.map (- ·)).toFn i j = -(M.toFn i j)
  simp

/-! ### Scalar multiplication -/

instance [SMul α R] : SMul α (AzMatrix R m n) :=
  ⟨fun c M => M.map (c • ·)⟩

@[simp]
theorem AzMatrix.toFn_smul [SMul α R] (c : α) (M : AzMatrix R m n) (i : Fin m) (j : Fin n) :
    (c • M).toFn i j = c • M.toFn i j := by
  show (M.map (c • ·)).toFn i j = c • M.toFn i j
  simp

end Azurite
