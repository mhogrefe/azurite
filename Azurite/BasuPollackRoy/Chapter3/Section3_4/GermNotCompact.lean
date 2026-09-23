/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.BasuPollackRoy.Chapter3.Section3_4.NotCompact
import Azurite.BasuPollackRoy.Chapter3.Section3_4.LimEps

/-! # BPR §3.4 — `[0, 1] ⊆ R⟨ε⟩` is not compact

The closed bounded interval `[0, 1]` over the field of germs `R⟨ε⟩ = SemialgGerm R` is **not
compact**: the family `{[0, f) ∪ (r, 1] | f > 0 infinitesimal, r ∈ R, 0 < r < 1}` is an open cover
with no finite subcover. The gap is between the infinitesimals (`f`) and the appreciable standard
positives (`r`): every point of `[0, 1]` is either infinitesimal (covered by some `[0, f)`) or
bounded below by a standard `r > 0` (covered by some `(r, 1]`), but a finite subfamily leaves the
appreciable point `min r / 2` uncovered. -/

namespace Azurite.BPR

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]

-- The germ field `R⟨ε⟩` is real closed (a theorem, not a registered instance); make it available
-- locally so the euclidean topology on `Fin 1 → R⟨ε⟩` is synthesized in the statement below.
attribute [local instance] isRealClosed_semialgGerm

/-- **BPR §3.4, example: `[0, 1] ⊆ R⟨ε⟩` is not compact.** The closed bounded unit interval over the
germ field is not compact, witnessed by the infinitesimal-gap cover. -/
theorem not_isCompact_unitIcc_semialgGerm :
    ¬ IsCompact (unitIcc : Set (Fin 1 → SemialgGerm R)) := by
  apply not_isCompact_unitIcc_of_cover
    {p : SemialgGerm R × SemialgGerm R |
      (0 < p.1 ∧ ∀ r : R, 0 < r → p.1 < algebraMap R (SemialgGerm R) r) ∧
      ∃ r : R, 0 < r ∧ r < 1 ∧ p.2 = algebraMap R (SemialgGerm R) r}
  · -- cover
    intro u hu0 hu1
    by_cases hinf : ∀ r : R, 0 < r → u 0 < algebraMap R (SemialgGerm R) r
    · -- `u 0` infinitesimal: cover by `[0, f)` with `f = u 0 + ε`.
      refine ⟨(u 0 + idGerm, algebraMap R (SemialgGerm R) (1 / 2)),
        ⟨⟨?_, ?_⟩, ⟨1 / 2, by norm_num, by norm_num, rfl⟩⟩, Or.inl ?_⟩
      · have := idGerm_pos (R := R); linarith
      · intro r hr
        have h1 := hinf (r / 2) (by linarith)
        have h2 := idGerm_lt_algebraMap (R := R) (show (0 : R) < r / 2 by linarith)
        have hsum : u 0 + idGerm
            < algebraMap R (SemialgGerm R) (r / 2) + algebraMap R (SemialgGerm R) (r / 2) :=
          add_lt_add h1 h2
        rwa [← map_add, show r / 2 + r / 2 = r by ring] at hsum
      · have := idGerm_pos (R := R); linarith
    · -- `u 0` not infinitesimal: cover by `(s, 1]` with `s = (r / 2)` standard.
      push Not at hinf
      obtain ⟨r, hr, hru⟩ := hinf
      have hr1 : r ≤ 1 := by
        by_contra hc
        push Not at hc
        have hu1' : u 0 ≤ algebraMap R (SemialgGerm R) 1 := by rw [map_one]; exact hu1
        exact absurd (le_trans hru hu1') (not_le.mpr (algebraMap_lt_algebraMap_of_lt hc))
      refine ⟨(idGerm, algebraMap R (SemialgGerm R) (r / 2)),
        ⟨⟨idGerm_pos, fun r' hr' => idGerm_lt_algebraMap hr'⟩,
          ⟨r / 2, by linarith, by linarith, rfl⟩⟩, Or.inr ?_⟩
      calc algebraMap R (SemialgGerm R) (r / 2)
            < algebraMap R (SemialgGerm R) r := algebraMap_lt_algebraMap_of_lt (by linarith)
        _ ≤ u 0 := hru
  · -- separation
    rintro p ⟨⟨_, hp_inf⟩, _⟩ q ⟨_, r, hr, _, hq2⟩
    rw [hq2]; exact hp_inf r hr
  · rintro p ⟨⟨hp1, _⟩, _⟩; exact hp1
  · rintro p ⟨_, r, _, hr1, hq2⟩
    rw [hq2, ← map_one (algebraMap R (SemialgGerm R))]
    exact algebraMap_lt_algebraMap_of_lt hr1

end Azurite.BPR
