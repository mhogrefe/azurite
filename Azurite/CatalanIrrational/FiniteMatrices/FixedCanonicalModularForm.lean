/-
Copyright © 2026 Mikhail Hogrefe

Uses code adopted from the OpenAI mathematics repository (<https://github.com/openai/math>,
commit 4eaee87,
`lean/OAI/NumberTheory/Catalan/FiniteMatrices/FixedCanonicalModularForm.lean`),
licensed under the Apache License, Version 2.0.

     Copyright © 2026 OpenAI

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.CatalanIrrational.Arithmetic.FixedCanonicalIntegerBase
import Azurite.CatalanIrrational.Polynomial.FixedCanonicalCoefficientTables

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace InternalCatalan

theorem fixedIntegerBaseCanonical_mod_coefficients (r : Fin 49) (k : Fin 48) :
    (fixedIntegerBaseCanonical r k : ZMod 101) =
      2 * (∑ i ∈ Finset.range 65,
        (fixedCanonicalPCoeff r i : ZMod 101) * (fixedClearedMoment i k : ZMod 101)) -
      3 * (∑ i ∈ Finset.range 65,
        (fixedCanonicalDCoeff r i : ZMod 101) * (fixedClearedZeta i k : ZMod 101)) := by
  simp only [fixedIntegerBaseCanonical, fixedCanonicalPCoeff_eq, fixedCanonicalDCoeff_eq,
    Int.cast_sub, Int.cast_mul, Int.cast_sum, Int.cast_ofNat]

end InternalCatalan

end

end

end OAI
