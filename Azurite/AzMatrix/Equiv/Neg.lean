/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

/-
  Equivalence proofs for AzMatrix negation.
-/
import Azurite.AzMatrix.Operations
import Mathlib.Algebra.Group.Pi.Basic

namespace Azurite
variable {R : Type _} [Neg R] {m n : Nat}

/-- Negation commutes with `toFn`. -/
@[simp]
theorem AzMatrix.toFn_neg (M : AzMatrix R m n) (i : Fin m) (j : Fin n) :
    (-M).toFn i j = -(M.toFn i j) := by
  show (M.map (- ·)).toFn i j = -(M.toFn i j); simp

/-- Negation commutes with `ofFn`. -/
@[simp]
theorem AzMatrix.ofFn_neg (f : Fin m → Fin n → R) :
    -(AzMatrix.ofFn f) = AzMatrix.ofFn (fun i j => -(f i j)) := by
  apply AzMatrix.toFn_injective; ext i j; simp

end Azurite
