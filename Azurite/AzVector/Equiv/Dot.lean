/-
  Equivalence proofs for AzVector dot product.

  Links the computable `dot` (Array.foldl-based) to Mathlib's
  `dotProduct` (`⬝ᵥ`) from `Mathlib.Data.Matrix.Mul`.
-/
import Azurite.AzVector.Dot
import Azurite.AzVector.Equiv.Algebra
import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.BigOperators.Fin

namespace Azurite

variable {R : Type _} [CommSemiring R] {n : Nat}

/-! ### Helper lemmas: Array.foldl → List.sum → Finset.sum -/

private theorem array_foldl_add_eq_sum [AddCommMonoid R]
    (arr : Array R) : arr.foldl (· + ·) 0 = arr.toList.sum := by
  rw [← Array.foldl_toList]; rw [List.sum_eq_foldl]

private theorem vector_toList_eq_ofFn {α : Type _} {m : Nat} (v : Vector α m) :
    v.toList = List.ofFn v.get := by
  apply List.ext_getElem
  · simp [Vector.length_toList]
  · intro i h1 h2; simp only [Vector.getElem_toList, List.getElem_ofFn]; rfl

private theorem list_zipWith_ofFn {α β γ : Type _} {m : Nat}
    (f : α → β → γ) (g : Fin m → α) (h : Fin m → β) :
    List.zipWith f (List.ofFn g) (List.ofFn h) = List.ofFn (fun i => f (g i) (h i)) := by
  apply List.ext_getElem
  · simp [List.length_zipWith]
  · intro i h1 h2; simp [List.getElem_zipWith, List.getElem_ofFn]

/-! ### Dot product equivalence -/

/-- The computable `dot` equals Mathlib's `dotProduct` (`⬝ᵥ`) via `toFn`. -/
theorem AzVector.dot_eq_dotProduct (v w : AzVector R n) :
    v.dot w = v.toFn ⬝ᵥ w.toFn := by
  unfold dot dotProduct
  rw [array_foldl_add_eq_sum, Vector.toList_toArray, Vector.toList_zipWith,
      vector_toList_eq_ofFn v.data, vector_toList_eq_ofFn w.data,
      list_zipWith_ofFn, List.sum_ofFn]
  simp [AzVector.toFn]

/-- The computable `normSq` equals `v.toFn ⬝ᵥ v.toFn`. -/
theorem AzVector.normSq_eq_dotProduct (v : AzVector R n) :
    v.normSq = v.toFn ⬝ᵥ v.toFn :=
  AzVector.dot_eq_dotProduct v v

end Azurite
