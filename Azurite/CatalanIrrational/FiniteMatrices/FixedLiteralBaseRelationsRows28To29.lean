/-
Copyright © 2026 Mikhail Hogrefe

Uses code adopted from the OpenAI mathematics repository (<https://github.com/openai/math>,
commit 4eaee87,
`lean/OAI/NumberTheory/Catalan/FiniteMatrices/FixedLiteralBaseRelationsRows28To29.lean`),
licensed under the Apache License, Version 2.0.

     Copyright © 2026 OpenAI

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.CatalanIrrational.FiniteMatrices.FixedLiteralBaseRelationsRows0To1

namespace OAI

section

namespace InternalCatalan

theorem fixedLiteralBaseMod_plus_row_28 : ∀ k : Fin 48,
    fixedLiteralBaseMod (28 : Fin 48).castSucc k +
      fixedLiteralBaseMod (28 : Fin 48).succ k = fixedLiteralModPlus 28 k := by
  decide +kernel

theorem fixedLiteralBaseMod_minus_row_28 : ∀ k : Fin 48,
    fixedLiteralBaseMod (28 : Fin 48).castSucc k -
      fixedLiteralBaseMod (28 : Fin 48).succ k = fixedLiteralModMinus 28 k := by
  decide +kernel

theorem fixedLiteralBaseMod_plus_row_29 : ∀ k : Fin 48,
    fixedLiteralBaseMod (29 : Fin 48).castSucc k +
      fixedLiteralBaseMod (29 : Fin 48).succ k = fixedLiteralModPlus 29 k := by
  decide +kernel

theorem fixedLiteralBaseMod_minus_row_29 : ∀ k : Fin 48,
    fixedLiteralBaseMod (29 : Fin 48).castSucc k -
      fixedLiteralBaseMod (29 : Fin 48).succ k = fixedLiteralModMinus 29 k := by
  decide +kernel

end InternalCatalan

end

end OAI
