/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

/-
  Equivalence proofs for AzMatrix zero.
-/
import Azurite.AzMatrix.Operations

namespace Azurite
variable {R : Type _} [Zero R] {m n : Nat}

/-- Zero commutes with `toFn`. -/
@[simp]
theorem AzMatrix.toFn_zero (i : Fin m) (j : Fin n) :
    (0 : AzMatrix R m n).toFn i j = 0 := by
  show ((Vector.ofFn (fun _ => Vector.ofFn (fun _ => (0 : R)))).get i).get j = 0
  simp [Vector.get]

/-- Zero commutes with `get`. -/
@[simp]
theorem AzMatrix.get_zero (i : Fin m) (j : Fin n) :
    (0 : AzMatrix R m n).get i j = 0 := by
  show ((Vector.ofFn (fun _ => Vector.ofFn (fun _ => (0 : R)))).get i).get j = 0
  simp [Vector.get]

/-- Zero commutes with `ofFn`. -/
@[simp]
theorem AzMatrix.ofFn_zero :
    AzMatrix.ofFn (fun (_ : Fin m) (_ : Fin n) => (0 : R)) = (0 : AzMatrix R m n) := rfl

end Azurite
