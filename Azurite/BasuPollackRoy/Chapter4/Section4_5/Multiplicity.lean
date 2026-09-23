/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.BasuPollackRoy.Chapter4.Section4_5.LocalizationAtPoint
import Mathlib.RingTheory.Localization.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# BPR §4.5: the multiplicity of a zero

For `x ∈ Zer(𝒫, Cᵏ)`, the *multiplicity* `μ(x)` of the zero `x` is the dimension of the
localization `Ā_x` as a `C`-vector space (`multiplicityOfZero`). Here `Ā_x` carries the `C`-algebra
structure obtained from `C → Ā → Ā_x`.
-/

namespace Azurite.BPR.Chapter4

open MvPolynomial

variable {k : ℕ} {K : Type*} [Field K] (C : Type*) [Field C] [Algebra K C]
  (Ps : Finset (MvPolynomial (Fin k) K)) (x : Fin k → C) (hx : x ∈ zerOfFinset C Ps)

/-- The natural `C`-algebra structure on `Ā_x`, obtained from `C → Ā → Ā_x`. -/
noncomputable instance algebraLocalizationAtPoint :
    Algebra C (localizationAtPoint C Ps x hx) :=
  RingHom.toAlgebra ((algebraMap (quotPolysExt C Ps)
      (Localization (evalAtPointSubmonoid C Ps x hx))).comp (algebraMap C (quotPolysExt C Ps)))

/-- **BPR Definition (multiplicity of a zero).** `μ(x)` is the dimension of `Ā_x` as a
`C`-vector space. -/
noncomputable def multiplicityOfZero : ℕ :=
  Module.finrank C (localizationAtPoint C Ps x hx)

end Azurite.BPR.Chapter4
