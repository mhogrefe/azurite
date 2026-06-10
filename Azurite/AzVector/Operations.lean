/-
  Arithmetic operations for AzVector: Zero, Add, Neg, Sub, SMul.
  Provides `toFn_*` simp lemmas for each operation.
-/
import Azurite.AzVector.Basic
import Mathlib.Algebra.Group.Pi.Basic

namespace Azurite
variable {R : Type _} {n : Nat}

/-! ### Zero -/

instance instAzVectorZero [Zero R] : Zero (AzVector R n) := ⟨⟨Vector.ofFn (fun _ => 0)⟩⟩

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

instance instAzVectorAdd [Add R] : Add (AzVector R n) :=
  ⟨fun v w => v.zip (· + ·) w⟩

@[simp]
theorem AzVector.toFn_add [Add R] (v w : AzVector R n) :
    (v + w).toFn = v.toFn + w.toFn := by
  ext i
  show (v.zip (· + ·) w).toFn i = v.toFn i + w.toFn i
  simp

/-! ### Negation -/

instance instAzVectorNeg [Neg R] : Neg (AzVector R n) :=
  ⟨fun v => v.map (- ·)⟩

@[simp]
theorem AzVector.toFn_neg [Neg R] (v : AzVector R n) :
    (-v).toFn = -v.toFn := by
  ext i
  show (v.map (- ·)).toFn i = -(v.toFn i)
  simp

/-! ### Subtraction -/

instance instAzVectorSub [Sub R] : Sub (AzVector R n) :=
  ⟨fun v w => v.zip (· - ·) w⟩

@[simp]
theorem AzVector.toFn_sub [Sub R] (v w : AzVector R n) :
    (v - w).toFn = v.toFn - w.toFn := by
  ext i
  show (v.zip (· - ·) w).toFn i = v.toFn i - w.toFn i
  simp

/-! ### Scalar multiplication -/

instance instAzVectorSMul [SMul α R] : SMul α (AzVector R n) :=
  ⟨fun c v => v.map (c • ·)⟩

@[simp]
theorem AzVector.toFn_smul [SMul α R] (c : α) (v : AzVector R n) :
    (c • v).toFn = c • v.toFn := by
  ext i
  show (v.map (c • ·)).toFn i = c • v.toFn i
  simp

end Azurite
