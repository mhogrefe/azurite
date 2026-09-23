/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

/-
  Dot product, squared norm for AzVector.
-/
import Azurite.AzVector.Operations

namespace Azurite
variable {R : Type _} {n : Nat}

/-- Dot product of two vectors. -/
def AzVector.dot [Mul R] [Add R] [Zero R] (v w : AzVector R n) : R :=
  (v.zip (· * ·) w).data.toArray.foldl (· + ·) 0

/-- Squared norm of a vector: `‖v‖² = v · v`. -/
def AzVector.normSq [Mul R] [Add R] [Zero R] (v : AzVector R n) : R :=
  v.dot v

end Azurite
