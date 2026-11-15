/-
Copyright © 2026 Mikhail Hogrefe

Uses code adopted from the OpenAI mathematics repository (<https://github.com/openai/math>,
commit 4eaee87,
`lean/OAI/NumberTheory/Catalan/FiniteMatrices/FixedLiteralBaseRelationsRows14To15.lean`),
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

theorem fixedLiteralBaseMod_plus_row_14 : ∀ k : Fin 48,
    fixedLiteralBaseMod (14 : Fin 48).castSucc k +
      fixedLiteralBaseMod (14 : Fin 48).succ k = fixedLiteralModPlus 14 k := by
  decide +kernel

theorem fixedLiteralBaseMod_minus_row_14 : ∀ k : Fin 48,
    fixedLiteralBaseMod (14 : Fin 48).castSucc k -
      fixedLiteralBaseMod (14 : Fin 48).succ k = fixedLiteralModMinus 14 k := by
  decide +kernel

theorem fixedLiteralBaseMod_plus_row_15 : ∀ k : Fin 48,
    fixedLiteralBaseMod (15 : Fin 48).castSucc k +
      fixedLiteralBaseMod (15 : Fin 48).succ k = fixedLiteralModPlus 15 k := by
  decide +kernel

theorem fixedLiteralBaseMod_minus_row_15 : ∀ k : Fin 48,
    fixedLiteralBaseMod (15 : Fin 48).castSucc k -
      fixedLiteralBaseMod (15 : Fin 48).succ k = fixedLiteralModMinus 15 k := by
  decide +kernel

end InternalCatalan

end

end OAI
