/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

/-
  Cross product for 3-dimensional AzVectors.
-/
import Azurite.AzVector.Basic
import Mathlib.Algebra.Ring.Defs

namespace Azurite

variable {R : Type _} [Ring R]

/-- Cross product of two 3-dimensional vectors. -/
def AzVector.cross (v w : AzVector R 3) : AzVector R 3 :=
  let a := v.data; let b := w.data
  ⟨#v[a.get 1 * b.get 2 - a.get 2 * b.get 1,
      a.get 2 * b.get 0 - a.get 0 * b.get 2,
      a.get 0 * b.get 1 - a.get 1 * b.get 0]⟩

end Azurite
