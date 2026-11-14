/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.SinCosWithPeriodBracket
import Azurite.AzFloat.Equiv.SinWithPeriodBracket
import Azurite.AzFloat.Equiv.ZivPair

/-!
# Equivalence: the joint bracket of `sin (2πr)` and `cos (2πr)`

`sinCosPeriodApprox_isSome_exists`: the joint Ziv certificate for `r ∈ [0, 1)` whose reduced
denominator is none of `1, 2, 3, 4, 6, 12` (both values irrational by Niven's theorem), from the
specifications of the two components; `zivLoopCertified₂_sinCosPeriodApprox`: the joint loop
returns the pair of the two separate loops.
-/

namespace Azurite.AzFloat

/-- The joint Ziv certificate for `± sin (2πr)` and `cos (2πr)`. -/
theorem sinCosPeriodApprox_isSome_exists (p : ℕ) [NeZero p] (mode : RoundingMode) (neg : Bool)
    (r : AzRat) (hr0 : 0 ≤ ((AzRat.toRat r : ℚ) : ℝ)) (hr1 : ((AzRat.toRat r : ℚ) : ℝ) < 1)
    (h1 : r.den ≠ AzNat.ofNat 1) (h2 : r.den ≠ AzNat.ofNat 2) (h3 : r.den ≠ AzNat.ofNat 3)
    (h4 : r.den ≠ AzNat.ofNat 4) (h6 : r.den ≠ AzNat.ofNat 6) (h12 : r.den ≠ AzNat.ofNat 12)
    (w₀ : ℕ) (hw₀ : 0 < w₀) :
    ∃ f : ℕ, (roundingPossible₂ (sinCosPeriodApprox neg r (w₀ * 2 ^ f)) p mode).isSome = true :=
  exists_isSome₂_of_irrational_threshold p mode (sinCosPeriodApprox neg r)
    (irrational_sign_mul (irrational_sin_two_pi_mul_toRat r h1 h2 h4 h12) neg)
    (irrational_cos_two_pi_mul_toRat r h1 h2 h3 h4 h6) sinPeriodEps cosPeriodEps
    tendsto_sinPeriodEps tendsto_cosPeriodEps 64
    (fun w hw => by rw [sinCosPeriodApprox_fst]; exact sinPeriodApprox_spec neg r hr0 hr1 hw)
    (fun w hw => by rw [sinCosPeriodApprox_snd]; exact cosPeriodApprox_spec r hr0 hr1 hw) w₀ hw₀

/-- **The joint loop returns the results of the two separate loops.** -/
theorem zivLoopCertified₂_sinCosPeriodApprox (p : ℕ) [NeZero p] (mode : RoundingMode)
    (neg : Bool) (r : AzRat) (hr0 : 0 ≤ ((AzRat.toRat r : ℚ) : ℝ))
    (hr1 : ((AzRat.toRat r : ℚ) : ℝ) < 1) (h1 : r.den ≠ AzNat.ofNat 1)
    (h2 : r.den ≠ AzNat.ofNat 2) (h3 : r.den ≠ AzNat.ofNat 3) (h4 : r.den ≠ AzNat.ofNat 4)
    (h6 : r.den ≠ AzNat.ofNat 6) (h12 : r.den ≠ AzNat.ofNat 12) (w₀ : ℕ) (hw₀ : 64 ≤ w₀)
    (h : ∃ f : ℕ, (roundingPossible₂ (sinCosPeriodApprox neg r (w₀ * 2 ^ f)) p mode).isSome
      = true)
    (hs : ∃ f : ℕ, (roundingPossible (sinPeriodApprox neg r (w₀ * 2 ^ f)).1
      (sinPeriodApprox neg r (w₀ * 2 ^ f)).2 p mode).isSome = true)
    (hc : ∃ f : ℕ, (roundingPossible (cosPeriodApprox r (w₀ * 2 ^ f)).1
      (cosPeriodApprox r (w₀ * 2 ^ f)).2 p mode).isSome = true) :
    zivLoopCertified₂ (sinCosPeriodApprox neg r) p mode w₀ h
      = (zivLoopCertified (sinPeriodApprox neg r) p mode w₀ hs,
        zivLoopCertified (cosPeriodApprox r) p mode w₀ hc) := by
  have hB₁ := not_mem_floatSet_of_irrational p
    (irrational_sign_mul (irrational_sin_two_pi_mul_toRat r h1 h2 h4 h12) neg)
  have hB₂ := not_mem_floatSet_of_irrational p (irrational_cos_two_pi_mul_toRat r h1 h2 h3 h4 h6)
  rw [zivLoopCertified_eq_threshold' p mode _ _ hB₁ w₀ (by omega)
      (fun w hw => by
        obtain ⟨lv, hv', hl, hh, hlo, hhi, -⟩ := sinPeriodApprox_spec neg r hr0 hr1 (w := w)
          (by omega)
        exact ⟨lv, hv', hl, hh, hlo, hhi⟩) hs,
    zivLoopCertified_eq_threshold' p mode _ _ hB₂ w₀ (by omega)
      (fun w hw => by
        obtain ⟨lv, hv', hl, hh, hlo, hhi, -⟩ := cosPeriodApprox_spec r hr0 hr1 (w := w)
          (by omega)
        exact ⟨lv, hv', hl, hh, hlo, hhi⟩) hc]
  refine zivLoopCertified₂_eq p mode _ _ _ hB₁ hB₂ w₀ (by omega) (fun w hw => ?_) h
  obtain ⟨l₁, h₁, hl₁, hh₁, a₁, b₁, -⟩ := sinPeriodApprox_spec neg r hr0 hr1 (w := w) (by omega)
  obtain ⟨l₂, h₂, hl₂, hh₂, a₂, b₂, -⟩ := cosPeriodApprox_spec r hr0 hr1 (w := w) (by omega)
  exact ⟨l₁, h₁, l₂, h₂, hl₁, hh₁, a₁, b₁, hl₂, hh₂, a₂, b₂⟩

end Azurite.AzFloat
