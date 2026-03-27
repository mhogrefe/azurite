/-
  AzMatrix: Computable fixed-size matrix type.

  Wraps `Vector (Vector R n) m` for efficient computation.
  Provides bidirectional conversion with Mathlib's `Matrix (Fin m) (Fin n) R`.
-/
namespace Azurite

/-- A computable `m × n` matrix over `R`. -/
structure AzMatrix (R : Type _) (m n : Nat) where
  data : Vector (Vector R n) m

variable {R : Type _} {m n : Nat}

/-- Convert to a Mathlib-compatible function `Fin m → Fin n → R`. -/
def AzMatrix.toFn (M : AzMatrix R m n) : Fin m → Fin n → R :=
  fun i j => (M.data.get i).get j

/-- Construct from a function `Fin m → Fin n → R`. -/
def AzMatrix.ofFn (f : Fin m → Fin n → R) : AzMatrix R m n :=
  ⟨Vector.ofFn (fun i => Vector.ofFn (f i))⟩

/-- Access the `(i, j)` entry. -/
def AzMatrix.get (M : AzMatrix R m n) (i : Fin m) (j : Fin n) : R :=
  (M.data.get i).get j

/-- Two matrices are equal iff all entries are equal. -/
@[ext]
theorem AzMatrix.ext {M N : AzMatrix R m n}
    (h : ∀ i j, M.get i j = N.get i j) : M = N := by
  cases M; cases N; simp only [AzMatrix.mk.injEq]
  apply Vector.ext; intro i hi
  apply Vector.ext; intro j hj
  exact h ⟨i, hi⟩ ⟨j, hj⟩

@[simp]
theorem AzMatrix.toFn_ofFn (f : Fin m → Fin n → R) (i : Fin m) (j : Fin n) :
    (AzMatrix.ofFn f).toFn i j = f i j := by
  simp [toFn, ofFn, Vector.get]

@[simp]
theorem AzMatrix.ofFn_toFn (M : AzMatrix R m n) : AzMatrix.ofFn M.toFn = M := by
  ext i j; simp [toFn, ofFn, get, Vector.get]

theorem AzMatrix.toFn_injective :
    Function.Injective (AzMatrix.toFn (R := R) (m := m) (n := n)) := by
  intro a b h; ext i j; exact congr (congrFun h i) rfl

/-! ### Map -/

/-- Apply `f` to every entry of a matrix. -/
def AzMatrix.map {S : Type _} (f : R → S) (M : AzMatrix R m n) : AzMatrix S m n :=
  ⟨M.data.map (fun row => row.map f)⟩

@[simp]
theorem AzMatrix.toFn_map {S : Type _} (f : R → S) (M : AzMatrix R m n)
    (i : Fin m) (j : Fin n) :
    (M.map f).toFn i j = f (M.toFn i j) := by
  simp [map, AzMatrix.toFn, Vector.get, Vector.map]

/-! ### Zip -/

/-- Combine two matrices entrywise with `f`. -/
def AzMatrix.zip {S T : Type _} (f : R → S → T)
    (M : AzMatrix R m n) (N : AzMatrix S m n) : AzMatrix T m n :=
  ⟨Vector.zipWith (fun r s => Vector.zipWith f r s) M.data N.data⟩

@[simp]
theorem AzMatrix.toFn_zip {S T : Type _} (f : R → S → T)
    (M : AzMatrix R m n) (N : AzMatrix S m n) (i : Fin m) (j : Fin n) :
    (M.zip f N).toFn i j = f (M.toFn i j) (N.toFn i j) := by
  simp [zip, AzMatrix.toFn, Vector.get, Vector.zipWith]

end Azurite
