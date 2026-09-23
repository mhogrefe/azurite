/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

/-
  Equivalence proofs for AzMatrix scalar multiplication.
-/
import Azurite.AzMatrix.Operations
import Mathlib.Algebra.Group.Pi.Basic

namespace Azurite
variable {R : Type _} {m n : Nat}

/-- Scalar multiplication commutes with `toFn`. -/
@[simp]
theorem AzMatrix.toFn_smul [SMul α R] (c : α) (M : AzMatrix R m n) (i : Fin m) (j : Fin n) :
    (c • M).toFn i j = c • M.toFn i j := by
  show (M.map (c • ·)).toFn i j = c • M.toFn i j; simp

/-- Scalar multiplication commutes with `ofFn`. -/
@[simp]
theorem AzMatrix.ofFn_smul [SMul α R] (c : α) (f : Fin m → Fin n → R) :
    c • AzMatrix.ofFn f = AzMatrix.ofFn (fun i j => c • f i j) := by
  apply AzMatrix.toFn_injective; ext i j; simp

end Azurite
