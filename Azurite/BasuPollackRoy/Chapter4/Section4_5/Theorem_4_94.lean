/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.BasuPollackRoy.Chapter4.Section4_5.Proposition_4_92
import Azurite.BasuPollackRoy.Chapter4.Section4_5.Proposition_4_93
import Mathlib.RingTheory.Idempotents

/-!
# BPR §4.5, Theorem 4.94: the product decomposition `Ā ≅ ∏_x Ā_x`

For each `x ∈ Zer(𝒫, Cᵏ)` there is an idempotent `e_x` with `e_x Ā ≅ Ā_x` (Propositions 4.92 and
4.93), and
`Ā ≅ ∏_{x ∈ Zer(𝒫, Cᵏ)} Ā_x`.

Proof: the idempotents `(e_x)` form a complete orthogonal family (`∑ e_x = 1`, `e_x e_y = 0`,
`e_x² = e_x` — Proposition 4.92), so `Ā ≅ ∏_x e_x Ā` (Mathlib's
`CompleteOrthogonalIdempotents.ringEquivOfComm`). Composing factor-wise with the isomorphisms
`e_x Ā ≅ Ā_x` of Proposition 4.93 gives `Ā ≅ ∏_x Ā_x`.
-/

namespace Azurite.BPR.Chapter4

open MvPolynomial

variable {k : ℕ} {K : Type*} [Field K]

/-- **BPR Theorem 4.94.** If `Zer(𝒫, Cᵏ)` is finite, then `Ā = C[X]/Ideal(𝒫,C)` decomposes as the
product of the localizations `Ā_x` over the points `x ∈ Zer(𝒫, Cᵏ)`. -/
theorem theorem_4_94 [CharZero K] {C : Type*} [Field C] [IsAlgClosed C] [Algebra K C]
    (Ps : Finset (MvPolynomial (Fin k) K)) (hfin : (zerOfFinset C Ps).Finite) :
    Nonempty (quotPolysExt C Ps ≃+*
      Π i : hfin.toFinset, localizationAtPoint C Ps i.1 (hfin.mem_toFinset.mp i.2)) := by
  classical
  have : CharZero C := charZero_of_injective_algebraMap (algebraMap K C).injective
  obtain ⟨e, hsum, horth, hidem, hval1, hval0⟩ := proposition_4_92 (C := C) Ps hfin
  -- the idempotents `(e_x)` form a complete orthogonal family
  have hCOI : CompleteOrthogonalIdempotents (fun i : hfin.toFinset => e i.1) := by
    refine ⟨⟨fun i => ?_, fun i j hij => ?_⟩, ?_⟩
    · have h := hidem i.1 i.2
      rwa [sq] at h
    · exact horth i.1 i.2 j.1 j.2 (fun h => hij (Subtype.ext h))
    · rw [Finset.sum_coe_sort hfin.toFinset e]; exact hsum
  -- `Ā ≅ ∏_x e_x Ā`, then factor-wise `e_x Ā ≅ Ā_x` by Proposition 4.93
  refine ⟨hCOI.ringEquivOfComm.trans (RingEquiv.piCongrRight fun i =>
    (proposition_4_93 Ps i.1 (hfin.mem_toFinset.mp i.2) (e i.1) (hCOI.idem i)
      (hval1 i.1 (hfin.mem_toFinset.mp i.2))
      (fun y hy hyne => hval0 i.1 (hfin.mem_toFinset.mp i.2) y hy hyne.symm)).some)⟩

end Azurite.BPR.Chapter4
