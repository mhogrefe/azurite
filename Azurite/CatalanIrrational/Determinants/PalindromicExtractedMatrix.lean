/-
Copyright © 2026 Mikhail Hogrefe

Uses code adopted from the OpenAI mathematics repository (<https://github.com/openai/math>,
commit 4eaee87,
`lean/OAI/NumberTheory/Catalan/Determinants/PalindromicExtractedMatrix.lean`),
licensed under the Apache License, Version 2.0.

     Copyright © 2026 OpenAI

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.CatalanIrrational.Estimates.PalindromicExtractedEntries

namespace OAI

section

noncomputable section

namespace InternalCatalan

def palindromicExtractedResidueMatrix (p : ℕ) [Fact p.Prime] :
    Matrix (Fin p × Fin 48) (Fin p × Fin 48) (ZMod p) :=
  fun r k => palindromicExtractedFilteredEntry p r.2 r.1 k.1 k.2

theorem palindromicExtractedResidueMatrix_eq_blocks {p : ℕ} [Fact p.Prime]
    (hp : 260 < p) :
    palindromicExtractedResidueMatrix p = palindromicResidueBlockMatrix p := by
  ext r k
  exact palindromicExtractedFilteredEntry_eq_fixedB hp r.2 r.1 k.1 k.2

theorem palindromicExtractedResidueMatrix_mul_columnChange {p : ℕ} [Fact p.Prime]
    (hp : 260 < p) :
    palindromicExtractedResidueMatrix p * palindromicResidueColumnChange p =
      palindromicReducedBlockMatrix p := by
  rw [palindromicExtractedResidueMatrix_eq_blocks hp]
  exact palindromicResidueBlockMatrix_mul_columnChange (by omega)

theorem det_palindromicExtractedResidueMatrix_ne_zero_of_fixed {p : ℕ} [Fact p.Prime]
    (hp : 260 < p)
    (h0 : (fixedB0Residue p).det ≠ 0)
    (hplus : (fixedB0Residue p + fixedB1Residue p).det ≠ 0)
    (hminus : (fixedB0Residue p - fixedB1Residue p).det ≠ 0) :
    (palindromicExtractedResidueMatrix p).det ≠ 0 := by
  rw [palindromicExtractedResidueMatrix_eq_blocks hp]
  exact det_palindromicResidueBlockMatrix_ne_zero_of_fixed (by omega) h0 hplus hminus

end InternalCatalan

end

end

end OAI
