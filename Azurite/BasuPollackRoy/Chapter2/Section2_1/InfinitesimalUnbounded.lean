/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Algebra.Defs

/-! # BPR Section 2.1 — Infinitesimal and unbounded elements

Let `F ⊂ F'` be two ordered fields, with `Algebra F F'` providing the
canonical embedding `algebraMap F F'`.

- `x ∈ F'` is *infinitesimal over F* if its absolute value is
  positive and smaller than every positive element of `F`.
- `x ∈ F'` is *unbounded over F* if its absolute value is greater
  than every positive element of `F`.

Mathlib has specific versions of these for the hyperreals
(`Hyperreal.Infinitesimal` and `Hyperreal.Infinite`). The definitions
below generalise to any ordered-field extension.
-/

namespace Azurite.BPR

variable (F : Type*) [Field F] [LinearOrder F] [IsStrictOrderedRing F]
variable {F' : Type*} [Field F'] [LinearOrder F'] [IsStrictOrderedRing F']
variable [Algebra F F']

/-- **BPR Definition (Infinitesimal).** An element x ∈ F′ is *infinitesimal
    over F* if x ≠ 0 and |x| < ι(a) for every positive a ∈ F,
    where ι = algebraMap F F′. -/
def IsInfinitesimalOver (x : F') : Prop :=
  x ≠ 0 ∧ ∀ a : F, 0 < a → |x| < algebraMap F F' a

/-- **BPR Definition (Unbounded).** An element x ∈ F′ is *unbounded
    over F* if ι(a) < |x| for every positive a ∈ F,
    where ι = algebraMap F F′. -/
def IsUnboundedOver (x : F') : Prop :=
  ∀ a : F, 0 < a → algebraMap F F' a < |x|

end Azurite.BPR
