/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.GammaConstants
import Azurite.AzFloat.Equiv.GammaConstantsEncl
import Azurite.AzFloat.Equiv.AgmConstants

/-!
# Equivalence: the constants `Γ(1/4)` and `Γ(1/3)`

**`gammaOneQuarterPrecRound_eq`, `gammaOneThirdPrecRound_eq`**: the constants are the correct
roundings of `Real.Gamma (1/4)` and `Real.Gamma (1/3)`, unconditionally — the values are
irrational by Chudnovsky's theorem and the Ziv loops have termination certificates
(`Equiv/AgmConstants.lean`).  The enclosures are in `Equiv/GammaConstantsEncl.lean`.
-/

namespace Azurite.AzFloat

open Azurite.Chudnovsky

/-- **`Γ(1/4)` is correctly rounded.** -/
theorem gammaOneQuarterPrecRound_eq (p : ℕ) [NeZero p] (mode : RoundingMode) :
    gammaOneQuarterPrecRound p mode
      = roundVal p mode (some ((Real.Gamma (1 / 4) : ℝ) : EReal)) := by
  unfold gammaOneQuarterPrecRound
  rw [dite_eq_right (NeZero.ne p)]
  exact zivLoopBacked_eq p mode gammaOneQuarterApprox
    (not_mem_floatSet_of_irrational p (irrational_of_not_algOver not_algOver_gamma_one_quarter))
    64 (fun w hw => Or.inl (by
      obtain ⟨lv, hv, h1, h2, h3, h4, -⟩ := gammaOneQuarterApprox_spec hw
      exact ⟨lv, hv, h1, h2, h3, h4⟩))
    _ _ (le_max_left _ _) (by omega) _

/-- **`Γ(1/3)` is correctly rounded.** -/
theorem gammaOneThirdPrecRound_eq (p : ℕ) [NeZero p] (mode : RoundingMode) :
    gammaOneThirdPrecRound p mode
      = roundVal p mode (some ((Real.Gamma (1 / 3) : ℝ) : EReal)) := by
  unfold gammaOneThirdPrecRound
  rw [dite_eq_right (NeZero.ne p)]
  exact zivLoopBacked_eq p mode gammaOneThirdApprox
    (not_mem_floatSet_of_irrational p (irrational_of_not_algOver not_algOver_gamma_one_third))
    64 (fun w hw => Or.inl (by
      obtain ⟨lv, hv, h1, h2, h3, h4, -⟩ := gammaOneThirdApprox_spec hw
      exact ⟨lv, hv, h1, h2, h3, h4⟩))
    _ _ (le_max_left _ _) (by omega) _

/-- `Γ(1/4)` is correctly rounded (the weaker form, kept for its users). -/
theorem gammaOneQuarterPrecRound_eq_or (p : ℕ) [NeZero p] (mode : RoundingMode) :
    gammaOneQuarterPrecRound p mode
        = roundVal p mode (some ((Real.Gamma (1 / 4) : ℝ) : EReal)) ∨
      gammaOneQuarterPrecRound p mode = (nan, .eq) :=
  Or.inl (gammaOneQuarterPrecRound_eq p mode)

/-- `Γ(1/3)` is correctly rounded (the weaker form, kept for its users). -/
theorem gammaOneThirdPrecRound_eq_or (p : ℕ) [NeZero p] (mode : RoundingMode) :
    gammaOneThirdPrecRound p mode
        = roundVal p mode (some ((Real.Gamma (1 / 3) : ℝ) : EReal)) ∨
      gammaOneThirdPrecRound p mode = (nan, .eq) :=
  Or.inl (gammaOneThirdPrecRound_eq p mode)

end Azurite.AzFloat
