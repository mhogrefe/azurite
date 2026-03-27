/-
  Operations for AzMatrix: Zero, Add, Sub, Neg, SMul, identity, single-entry, transpose.
  Computable predicates for symmetric / skew-symmetric.
-/
import Azurite.AzMatrix.Basic

namespace Azurite
variable {R : Type _} {m n : Nat}

/-! ### Zero -/

instance [Zero R] : Zero (AzMatrix R m n) :=
  ⟨⟨Vector.ofFn (fun _ => Vector.ofFn (fun _ => 0))⟩⟩

/-! ### Addition -/

instance [Add R] : Add (AzMatrix R m n) :=
  ⟨fun M N => M.zip (· + ·) N⟩

/-! ### Subtraction -/

instance [Sub R] : Sub (AzMatrix R m n) :=
  ⟨fun M N => M.zip (· - ·) N⟩

/-! ### Negation -/

instance [Neg R] : Neg (AzMatrix R m n) :=
  ⟨fun M => M.map (- ·)⟩

/-! ### Scalar multiplication -/

instance [SMul α R] : SMul α (AzMatrix R m n) :=
  ⟨fun c M => M.map (c • ·)⟩

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

end Azurite
