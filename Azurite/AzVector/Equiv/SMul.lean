/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

/-
  Equivalence proof for AzVector scalar multiplication.
-/
import Azurite.AzVector.Operations
import Mathlib.Algebra.Group.Pi.Basic

namespace Azurite
variable {R : Type _} {n : Nat}

/-- Scalar multiplication commutes with `toFn`. -/
@[simp]
theorem AzVector.toFn_smul' [SMul α R] (c : α) (v : AzVector R n) :
    (c • v).toFn = c • v.toFn := AzVector.toFn_smul c v

/-- Scalar multiplication commutes with `ofFn`. -/
@[simp]
theorem AzVector.ofFn_smul [SMul α R] (c : α) (f : Fin n → R) :
    AzVector.ofFn (c • f) = c • (AzVector.ofFn f) := by
  apply AzVector.toFn_injective; ext i; simp

end Azurite
