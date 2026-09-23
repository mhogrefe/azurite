/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

/-
  Core definitions for AzVector: a computable fixed-length vector.

  `AzVector R n` wraps Lean's `Vector R n` (array-backed).
  Equivalence with Mathlib's `Fin n → R` via `toFn`/`ofFn`.
-/

namespace Azurite

/-- A computable fixed-length vector backed by `Vector`. -/
structure AzVector (R : Type _) (n : Nat) where
  /-- The underlying `Vector`. -/
  data : Vector R n

variable {R : Type _} {n : Nat}

/-- Convert to Mathlib's function representation `Fin n → R`. -/
def AzVector.toFn (v : AzVector R n) : Fin n → R := v.data.get

/-- Convert from Mathlib's function representation. -/
def AzVector.ofFn (f : Fin n → R) : AzVector R n := ⟨Vector.ofFn f⟩

/-- Index into a vector. -/
def AzVector.get (v : AzVector R n) (i : Fin n) : R := v.data.get i

/-- Extensionality: two `AzVector`s are equal iff they agree at every index. -/
@[ext]
theorem AzVector.ext {v w : AzVector R n} (h : ∀ i : Fin n, v.get i = w.get i) : v = w := by
  cases v; cases w; simp only [AzVector.mk.injEq]
  exact Vector.ext (fun i hi => h ⟨i, hi⟩)

@[simp]
theorem AzVector.toFn_ofFn (f : Fin n → R) (i : Fin n) :
    (AzVector.ofFn f).toFn i = f i := by
  simp [toFn, ofFn, Vector.get]
  rfl

@[simp]
theorem AzVector.ofFn_toFn (v : AzVector R n) : AzVector.ofFn v.toFn = v := by
  ext i; simp [toFn, ofFn, get, Vector.get]
  rfl

/-- `toFn` is injective. -/
theorem AzVector.toFn_injective : Function.Injective (AzVector.toFn (R := R) (n := n)) := by
  intro a b h; ext i; exact congrFun h i

/-! ### Map -/

/-- Apply `f` to every entry of a vector. -/
def AzVector.map {S : Type _} (f : R → S) (v : AzVector R n) : AzVector S n :=
  ⟨v.data.map f⟩

@[simp]
theorem AzVector.toFn_map {S : Type _} (f : R → S) (v : AzVector R n) (i : Fin n) :
    (v.map f).toFn i = f (v.toFn i) := by
  simp [map, AzVector.toFn, Vector.get, Vector.map]
  rfl

/-! ### Zip -/

/-- Combine two vectors entrywise with `f`. -/
def AzVector.zip {S T : Type _} (f : R → S → T)
    (v : AzVector R n) (w : AzVector S n) : AzVector T n :=
  ⟨Vector.zipWith f v.data w.data⟩

@[simp]
theorem AzVector.toFn_zip {S T : Type _} (f : R → S → T)
    (v : AzVector R n) (w : AzVector S n) (i : Fin n) :
    (v.zip f w).toFn i = f (v.toFn i) (w.toFn i) := by
  simp [zip, AzVector.toFn, Vector.get, Vector.zipWith]
  rfl

/-! ### ofList -/

/-- Construct a vector from a list with a proof of the correct length.
    Usage: `AzVector.ofList [1, 2, 3]` -/
def AzVector.ofList (l : List R) (h : l.length = n := by decide) : AzVector R n :=
  ⟨⟨l.toArray, by simp [h]⟩⟩

instance : GetElem (AzVector R n) (Fin n) R (fun _ _ => True) where
  getElem v i _ := v.get i

end Azurite
