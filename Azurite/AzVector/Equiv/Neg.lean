/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

/-
  Equivalence proof for AzVector negation.
-/
import Azurite.AzVector.Operations
import Mathlib.Algebra.Group.Pi.Basic

namespace Azurite
variable {R : Type _} [Neg R] {n : Nat}

/-- Negation commutes with `toFn`. -/
@[simp]
theorem AzVector.toFn_neg' (v : AzVector R n) :
    (-v).toFn = -v.toFn := AzVector.toFn_neg v

/-- Negation commutes with `ofFn`. -/
@[simp]
theorem AzVector.ofFn_neg (f : Fin n → R) :
    AzVector.ofFn (-f) = -(AzVector.ofFn f) := by
  apply AzVector.toFn_injective; ext i; simp

end Azurite
