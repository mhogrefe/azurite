/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

/-
  AzMatrix: Computable fixed-size matrix type.

  Wraps `Vector (Vector R n) m` for efficient computation.
  Provides bidirectional conversion with Mathlib's `Matrix (Fin m) (Fin n) R`.
-/
namespace Azurite

/-- A computable `m × n` matrix over `R`. -/
structure AzMatrix (R : Type _) (m n : Nat) where
  data : Vector (Vector R n) m
deriving DecidableEq

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
  rfl

@[simp]
theorem AzMatrix.ofFn_toFn (M : AzMatrix R m n) : AzMatrix.ofFn M.toFn = M := by
  ext i j; simp [toFn, ofFn, get, Vector.get]
  rfl

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
  rfl

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
  rfl

/-! ### ofLists -/

/-- Construct a matrix from a list of row lists.
    Usage: `AzMatrix.ofLists [[1, 2], [3, 4]]` -/
def AzMatrix.ofLists (rows : List (List R))
    (hm : rows.length = m := by decide)
    (hn : ∀ r ∈ rows, r.length = n := by decide) : AzMatrix R m n :=
  ⟨⟨(rows.attach.map (fun ⟨r, hr⟩ =>
    (⟨r.toArray, by simp [hn r hr]⟩ : Vector R n))).toArray,
    by simp [hm]⟩⟩

/-! ### toLists -/

/-- Convert a matrix to a list of row lists.
    Inverse of `ofLists`. -/
def AzMatrix.toLists (M : AzMatrix R m n) : List (List R) :=
  M.data.toList.map (·.toList)

@[simp]
theorem AzMatrix.toLists_length (M : AzMatrix R m n) : M.toLists.length = m := by
  simp [toLists]

theorem AzMatrix.mem_toLists_length {M : AzMatrix R m n} {row : List R}
    (h : row ∈ M.toLists) : row.length = n := by
  simp only [toLists, List.mem_map] at h
  obtain ⟨v, _, rfl⟩ := h
  simp

theorem AzMatrix.ofLists_toLists (M : AzMatrix R m n) :
    AzMatrix.ofLists M.toLists M.toLists_length
      (fun _ h => AzMatrix.mem_toLists_length h) = M := by
  ext i j
  simp only [AzMatrix.ofLists, AzMatrix.toLists, AzMatrix.get, Vector.get,
    List.getElem_toArray, List.getElem_map, List.getElem_attach]
  rfl

end Azurite
