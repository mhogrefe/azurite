/-
  Arithmetic operations for AzVector: Zero, Add, Neg, Sub, SMul.
  Provides `toFn_*` simp lemmas for each operation.
-/
import Azurite.AzVector.Basic
import Mathlib.Algebra.Group.Pi.Basic

namespace Azurite
variable {R : Type _} {n : Nat}

/-! ### Zero -/

instance [Zero R] : Zero (AzVector R n) := ⟨⟨Vector.ofFn (fun _ => 0)⟩⟩

@[simp]
theorem AzVector.toFn_zero [Zero R] :
    (0 : AzVector R n).toFn = 0 := by
  ext i
  show (Vector.ofFn (fun _ => (0 : R))).get i = (0 : Fin n → R) i
  simp [Vector.get]

@[simp]
theorem AzVector.get_zero [Zero R] (i : Fin n) :
    (0 : AzVector R n).data.get i = 0 := by
  show (Vector.ofFn (fun _ => (0 : R))).get i = 0
  simp [Vector.get]

/-! ### Addition -/

instance [Add R] : Add (AzVector R n) :=
  ⟨fun v w => ⟨Vector.zipWith (· + ·) v.data w.data⟩⟩

@[simp]
theorem AzVector.toFn_add [Add R] (v w : AzVector R n) :
    (v + w).toFn = v.toFn + w.toFn := by
  ext i
  show (Vector.zipWith (· + ·) v.data w.data).get i = v.toFn i + w.toFn i
  simp [AzVector.toFn, Vector.get, Vector.zipWith]

/-! ### Negation -/

instance [Neg R] : Neg (AzVector R n) :=
  ⟨fun v => ⟨v.data.map (- ·)⟩⟩

@[simp]
theorem AzVector.toFn_neg [Neg R] (v : AzVector R n) :
    (-v).toFn = -v.toFn := by
  ext i
  show (v.data.map (- ·)).get i = -(v.toFn i)
  simp [AzVector.toFn, Vector.get, Vector.map]

/-! ### Subtraction -/

instance [Sub R] : Sub (AzVector R n) :=
  ⟨fun v w => ⟨Vector.zipWith (· - ·) v.data w.data⟩⟩

@[simp]
theorem AzVector.toFn_sub [Sub R] (v w : AzVector R n) :
    (v - w).toFn = v.toFn - w.toFn := by
  ext i
  show (Vector.zipWith (· - ·) v.data w.data).get i = v.toFn i - w.toFn i
  simp [AzVector.toFn, Vector.get, Vector.zipWith]

/-! ### Scalar multiplication -/

instance [SMul α R] : SMul α (AzVector R n) :=
  ⟨fun c v => ⟨v.data.map (c • ·)⟩⟩

@[simp]
theorem AzVector.toFn_smul [SMul α R] (c : α) (v : AzVector R n) :
    (c • v).toFn = c • v.toFn := by
  ext i
  show (v.data.map (c • ·)).get i = c • v.toFn i
  simp [AzVector.toFn, Vector.get, Vector.map]

end Azurite
