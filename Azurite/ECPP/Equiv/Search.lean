/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.ECPP.Gen.Search
import Azurite.ECPP.Equiv.Check
import Azurite.ECPP.Equiv.Export

/-!
# Soundness of primality proving by elliptic curves

The generator is not verified; its output is checked.  **`provePrime_sound`**:
`provePrime n P = true → Nat.Prime n.toNat`, for every choice of parameters.
-/

namespace Azurite.ECPP

/-- **`provePrime` proves primality.** -/
theorem provePrime_sound {n : AzNat} {P : GenParams} (h : provePrime n P = true) :
    Nat.Prime n.toNat := by
  unfold provePrime at h
  split at h
  · exact check_prime h
  · exact absurd h (by simp)

/-- **The bound the search uses implies the checker's**: a `q` with `(⌊√q⌋ − 1)⁴ > n` passes
the two conditions on `q` of `checkStep`. -/
theorem aboveBound_of_strictBound {n q : AzNat} (h : strictBound n q = true) :
    aboveBound n q = true := by
  obtain ⟨h1, h2⟩ := strictBound_nat ((strictBound_eq_true_iff n q).1 h)
  unfold aboveBound
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨?_, ?_⟩
  · rw [AzNat.lt_iff_toNat_lt, AzNat.toNat_add, AzNat.toNat_sqrt]
    exact h1
  · rw [AzNat.lt_iff_toNat_lt, AzNat.toNat_mul, AzNat.toNat_mul, AzNat.toNat_sub,
      AzNat.toNat_sub, AzNat.toNat_sqrt, AzNat.toNat_ofNat]
    rw [pow_two] at h2
    exact h2

end Azurite.ECPP
