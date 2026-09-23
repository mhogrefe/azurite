/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.BasuPollackRoy.Chapter1.Section1_1.FieldFormula
import Azurite.BasuPollackRoy.Chapter1.Section1_1.Formula
import Azurite.BasuPollackRoy.Chapter1.Section1_1.Realization
import Azurite.BasuPollackRoy.Chapter1.Section1_3.Projection

/-!
# BPR Section 1.3 — Fibers `S_y`

When `S ⊂ C^{k+1}` is a basic constructible set described by `(𝓟, 𝓠)`
and `y ∈ C^k`, BPR introduces the fiber

  S_y := { x ∈ C | ⋀_{P ∈ 𝓟} P_y(x) = 0 ∧ ⋀_{Q ∈ 𝓠} Q_y(x) ≠ 0} ⊂ C,

obtained by specializing the parameters `Y` to `y` and then asking
which `x ∈ C` satisfy the resulting univariate conditions. The
projection is recovered as `y ∈ π(S) ↔ S_y ≠ ∅`.

In our `Formula` representation, the fiber over `y` is simply the
set of `x ∈ C` for which `Fin.snoc y x` satisfies the formula:
specialization is then a *consequence* of `eval_specialize` rather
than the definition.
-/

namespace Azurite.BPR

variable {k : ℕ} {C : Type*} [Field C]

namespace Formula

/-- BPR's fiber `S_y`: for a formula `Φ` describing a set in
`C^{k+1}` and a point `y : Fin k → C`, `Φ.fiber y` is the subset of
`C` consisting of those `x` such that `Fin.snoc y x` satisfies `Φ`.
-/
noncomputable def fiber
    (Φ : Formula (Fin (k+1)) (FieldAtom (Fin (k+1)) C))
    (y : Fin k → C) : Set C :=
  { x : C | Fin.snoc y x ∈ Φ.realization (C := C) }

/-- A point `y ∈ C^k` lies in the projection `π(S)` iff the fiber
`S_y` is nonempty. -/
theorem mem_proj_iff_fiber_nonempty
    (Φ : Formula (Fin (k+1)) (FieldAtom (Fin (k+1)) C))
    (y : Fin k → C) :
    y ∈ Φ.proj ↔ (Φ.fiber y).Nonempty :=
  Iff.rfl

end Formula

end Azurite.BPR
