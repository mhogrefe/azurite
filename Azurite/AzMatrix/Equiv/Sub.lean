/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

/-
  Equivalence proofs for AzMatrix subtraction.
-/
import Azurite.AzMatrix.Operations
import Mathlib.Algebra.Group.Pi.Basic

namespace Azurite
variable {R : Type _} [Sub R] {m n : Nat}

/-- Subtraction commutes with `toFn`. -/
@[simp]
theorem AzMatrix.toFn_sub (M N : AzMatrix R m n) (i : Fin m) (j : Fin n) :
    (M - N).toFn i j = M.toFn i j - N.toFn i j := by
  show (M.zip (· - ·) N).toFn i j = M.toFn i j - N.toFn i j; simp

/-- Subtraction commutes with `ofFn`. -/
@[simp]
theorem AzMatrix.ofFn_sub (f g : Fin m → Fin n → R) :
    AzMatrix.ofFn f - AzMatrix.ofFn g = AzMatrix.ofFn (fun i j => f i j - g i j) := by
  apply AzMatrix.toFn_injective; ext i j; simp

end Azurite
