/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.BasuPollackRoy.Chapter4.Section4_4.Proposition_4_68

/-!
# BPR Proposition 4.69: a Gröbner basis generates the ideal

A Gröbner basis `𝒢` of `I` for the monomial ordering `m` is a set of generators of `I`:
`Ideal(𝒢, K) = I`. Indeed `𝒢 ⊆ I` gives `Ideal(𝒢, K) ⊆ I`, and conversely every `P ∈ I` is
reducible to `0` modulo `𝒢` (Proposition 4.68), hence lies in `Ideal(𝒢, K)` (Remark 4.66).
-/

namespace Azurite.BPR.Chapter4

open MvPolynomial

variable {k : ℕ} {K : Type*} [Field K]

/-- **BPR Proposition 4.69.** A Gröbner basis `𝒢` of `I` for the monomial ordering `m`
generates `I`: `Ideal(𝒢, K) = I`. -/
theorem proposition_4_69 (m : MonomialOrder (Fin k)) {I : Ideal (MvPolynomial (Fin k) K)}
    {𝒢 : Finset (MvPolynomial (Fin k) K)} (hG : IsGrobnerBasisOf m I 𝒢) :
    idealOfPolys 𝒢 = I := by
  apply le_antisymm
  · -- `Ideal(𝒢, K) = Ideal.span 𝒢 ≤ I`, since `𝒢 ⊆ I`.
    rw [idealOfPolys, Ideal.span_le]
    exact fun x hx => hG.1 x (Finset.mem_coe.mp hx)
  · -- `I ≤ Ideal(𝒢, K)`: every `P ∈ I` reduces to `0`, hence is in `Ideal(𝒢, K)`.
    intro P hP
    have hred : ReducibleTo m 𝒢 P 0 := (proposition_4_68 m hG P).mp hP
    have hmem := remark_4_66 m 𝒢 hred
    rwa [sub_zero] at hmem

end Azurite.BPR.Chapter4
