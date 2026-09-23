/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

/-
  Standard basis vectors for AzVector.
-/
import Azurite.AzVector.Basic

namespace Azurite
variable {R : Type _} {n : Nat}

/-- The `i`-th standard basis vector: 1 at index `i`, 0 elsewhere. -/
def AzVector.stdBasis [Zero R] [One R] (i : Fin n) : AzVector R n :=
  ⟨Vector.ofFn (fun j => if i = j then 1 else 0)⟩

@[simp]
theorem AzVector.get_stdBasis_self [Zero R] [One R] (i : Fin n) :
    (AzVector.stdBasis i).get i = (1 : R) := by
  simp [AzVector.get, stdBasis, Vector.get]
  intro hne
  exact absurd rfl hne

theorem AzVector.get_stdBasis_ne [Zero R] [One R] {i j : Fin n} (h : i ≠ j) :
    (AzVector.stdBasis i).get j = (0 : R) := by
  simp [AzVector.get, stdBasis, Vector.get]
  intro hij
  exact absurd hij h

end Azurite
