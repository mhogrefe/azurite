/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

/-
  Equivalence proofs for AzMatrix transpose.

  Links `AzMatrix.transpose` to Mathlib's `Matrix.transpose`.
-/
import Azurite.AzMatrix.Operations
import Mathlib.Data.Matrix.Basic

namespace Azurite
variable {R : Type _} {m n : Nat}

/-- Transpose commutes with `toFn`. -/
@[simp]
theorem AzMatrix.toFn_transpose (M : AzMatrix R m n) :
    M.transpose.toFn = fun j i => M.toFn i j := by
  ext j i; simp [transpose, toFn, ofFn, get, Vector.get]
  rfl

/-- Transpose commutes with `ofFn`. -/
@[simp]
theorem AzMatrix.ofFn_transpose (f : Fin m → Fin n → R) :
    (AzMatrix.ofFn f).transpose = AzMatrix.ofFn (fun j i => f i j) := by
  ext j i; simp [transpose, ofFn, get, Vector.get]
  rfl

end Azurite
