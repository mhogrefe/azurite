/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter1.Section12

/-!
# DLMF §3.10(i): Continued fractions — introduction

The definitions are those of §1.12 (`Section12`):

* 3.10.1 (`IsCF`, `dlmf_3_10_1`): the continued fraction `C = b₀ + a₁/(b₁ + a₂/(b₂ + ⋯))`,
  `aₙ ≠ 0`, with value `C` when its approximants converge (`CfConverges`).
* 3.10.2 (`dlmf_3_10_2`): the `n`th approximant (convergent)
  `Cₙ = b₀ + a₁/(b₁ + ⋯ aₙ/bₙ) = Aₙ/Bₙ` (`cfConv`, `cfA`, `cfB`, from 1.12.4), with the
  recurrences 1.12.5–1.12.6 (`dlmf_1_12_5`, `dlmf_1_12_6`).
-/

open Filter Topology

namespace Azurite.DLMF

variable {K : Type*} [Field K]

/-- The partial numerators of 3.10.1 do not vanish: `aₙ ≠ 0`, `n ≥ 1`. -/
def IsCF (a : ℕ → K) : Prop := ∀ n, 1 ≤ n → a n ≠ 0

/-- **DLMF 3.10.1**: `C = b₀ + a₁/(b₁ + a₂/(b₂ + ⋯))` (`aₙ ≠ 0`) means that the approximants
`Cₙ` converge to `C`. -/
theorem dlmf_3_10_1 [TopologicalSpace K] (a b : ℕ → K) (C : K) :
    CfConverges a b C ↔ Tendsto (fun n => cfConv a b n) atTop (𝓝 C) := Iff.rfl

/-- **DLMF 3.10.2**: `Cₙ = b₀ + a₁/(b₁ + a₂/(b₂ + ⋯ aₙ/bₙ)) = Aₙ/Bₙ`, where `Aₙ`, `Bₙ` satisfy
`A_k = b_k A_{k−1} + a_k A_{k−2}`, `B_k = b_k B_{k−1} + a_k B_{k−2}`, `A_{−1} = 1`, `A₀ = b₀`,
`B_{−1} = 0`, `B₀ = 1` (when no zero denominator occurs in the nested fraction). -/
theorem dlmf_3_10_2 (a b : ℕ → K) {n : ℕ} (h : CfNonzero a b n 0) :
    cfConv a b n = cfA a b n / cfB a b n ∧
      (∀ k, cfA a b (k + 1) = b (k + 1) * cfA a b k + a (k + 1) * cfP a b k ∧
        cfB a b (k + 1) = b (k + 1) * cfB a b k + a (k + 1) * cfQ a b k) ∧
      cfP a b 0 = 1 ∧ cfA a b 0 = b 0 ∧ cfQ a b 0 = 0 ∧ cfB a b 0 = 1 :=
  ⟨dlmf_1_12_4 a b h, dlmf_1_12_5 a b, dlmf_1_12_6 a b⟩

/-- The first approximants: `C₀ = b₀`, `C₁ = b₀ + a₁/b₁`. -/
theorem cfConv_zero_one (a b : ℕ → K) :
    cfConv a b 0 = b 0 ∧ cfConv a b 1 = b 0 + a 1 / b 1 := by
  simp [cfConv, cfw]

end Azurite.DLMF
