/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Catalan

/-!
# Equivalence: Catalan's constant

`catalanConstantPrecRound p mode = liftVal₀ G p mode`
(`catalanConstantPrecRound_eq_liftVal₀`): Catalan's constant is correctly rounded in every mode,
with the exact comparison, and without fuel.
-/

namespace Azurite.AzFloat

/-- **Catalan's constant is correctly rounded.** -/
theorem catalanConstantPrecRound_eq_liftVal₀ (p : ℕ) [NeZero p] (mode : RoundingMode) :
    catalanConstantPrecRound p mode =
      liftVal₀ (some ((Azurite.catalanConstant : ℝ) : EReal)) p mode := by
  unfold catalanConstantPrecRound liftVal₀
  split_ifs with hp
  · exact absurd hp (NeZero.ne p)
  apply zivLoopCertified_eq_threshold' p mode catalanApprox Azurite.catalanConstant
    (not_mem_floatSet_of_irrational p irrational_catalanConstant) (p + zivGuardBits)
    (by unfold zivGuardBits; omega)
  intro w hw
  obtain ⟨lv, hv, hl, hh, hlo, hhi, -⟩ :=
    catalanApprox_spec (w := w) (by unfold zivGuardBits at hw; omega)
  exact ⟨lv, hv, hl, hh, hlo, hhi⟩

end Azurite.AzFloat
