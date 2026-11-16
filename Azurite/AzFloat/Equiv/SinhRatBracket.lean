/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.SinhRatBracket
import Azurite.AzFloat.Equiv.SinhBracket
import Azurite.AzFloat.Equiv.TanRatBracket

/-!
# Equivalence: the bracket of `sinh q` for a rational `q`

`sinhRatBracket_spec` (width at most `sinhRatEps`, which tends to `0`), `sinhRatApprox_spec`,
`irrational_sinh_toRat`, `sinhRatApprox_isSome_exists` (the Ziv certificate).
-/

open Real

namespace Azurite.AzFloat

/-- The width bound of `sinhRatBracket`. -/
noncomputable def sinhRatEps (q : AzRat) (w : ℕ) : ℝ :=
  sinhWidth (Real.exp (AzRat.toRat q.abs : ℝ) - 1)
    (expM1RatEps (AzRat.toRat q.abs : ℝ)
      (expM1Comp (AzInt.ofInt (AzRat.floorLogBaseAbs 2 q.abs + 2))) w) w

theorem tendsto_sinhRatEps (q : AzRat) :
    Filter.Tendsto (sinhRatEps q) Filter.atTop (nhds 0) :=
  tendsto_sinhWidth _ (tendsto_expM1RatEps _ _)

/-- **`sinhRatBracket q w` encloses `sinh |q|`** for a rational `q ≠ 0`. -/
theorem sinhRatBracket_spec {w : ℕ} (hw : 64 ≤ w) (q : AzRat) (h0 : q.num ≠ 0) :
    IsEnclW (sinhRatBracket q w) (Real.sinh |((AzRat.toRat q : ℚ) : ℝ)|) (sinhRatEps q w) := by
  have habs : ((AzRat.toRat q.abs : ℚ) : ℝ) = |((AzRat.toRat q : ℚ) : ℝ)| := by
    rw [AzRat.toRat_abs]
    push_cast
    rfl
  obtain ⟨lo, hi, hlo, hhi, h1, h2, h3⟩ := expM1RatBracket_spec hw q.abs h0
  have h := sinhOfExpM1_width hlo hhi (by rw [habs]; exact abs_nonneg _) h1 h2 h3 w
  rw [habs] at h
  rw [sinhRatEps, habs]
  exact h

/-- `sinhRatApprox` as a pair of `Roundable`s bracketing `sinh q`. -/
theorem sinhRatApprox_spec {w : ℕ} (hw : 64 ≤ w) (q : AzRat) (h0 : q.num ≠ 0) :
    ∃ lv hv : ℝ, Rounds (sinhRatApprox q w).1 lv ∧ Rounds (sinhRatApprox q w).2 hv ∧
      lv ≤ Real.sinh (AzRat.toRat q : ℝ) ∧ Real.sinh (AzRat.toRat q : ℝ) ≤ hv ∧
      hv - lv ≤ sinhRatEps q w := by
  have hq0 : (AzRat.toRat q : ℝ) ≠ 0 := fun h => h0 ((AzRat.toRat_eq_zero_iff q).mp h)
  have hs := toRat_sign_iff q h0
  have hneg : (!q.sign) = true ↔ (AzRat.toRat q : ℝ) < 0 := by
    constructor
    · intro h
      rcases lt_or_gt_of_ne hq0 with h' | h'
      · exact h'
      · rw [hs.mpr h'] at h
        cases h
    · intro h
      cases hsg : q.sign
      · rfl
      · exact absurd (hs.mp hsg) (not_lt.mpr h.le)
  obtain ⟨lo, hi, hlo, hhi, h1, h2, hwid⟩ := sinhRatBracket_spec hw q h0
  obtain ⟨lv, hv, hR1, hR2, hl, hh, he⟩ := enclApprox_spec (!q.sign) hlo hhi h1 h2
  rw [sinh_abs_eq hneg] at hl hh
  exact ⟨lv, hv, hR1, hR2, hl, hh, by rw [he]; exact hwid⟩

/-- `sinh q` is irrational for a rational `q ≠ 0`. -/
theorem irrational_sinh_toRat (q : AzRat) (h0 : q.num ≠ 0) :
    Irrational (Real.sinh (AzRat.toRat q : ℝ)) :=
  irrational_sinh_rat (q := AzRat.toRat q)
    (fun h => h0 ((AzRat.toRat_eq_zero_iff q).mp (by rw [h, Rat.cast_zero])))

/-- The Ziv certificate for `sinh q`. -/
theorem sinhRatApprox_isSome_exists (p : ℕ) [NeZero p] (mode : RoundingMode) (q : AzRat)
    (h0 : q.num ≠ 0) (w₀ : ℕ) (hw₀ : 0 < w₀) :
    ∃ f : ℕ, (roundingPossible (sinhRatApprox q (w₀ * 2 ^ f)).1
      (sinhRatApprox q (w₀ * 2 ^ f)).2 p mode).isSome = true :=
  exists_isSome_of_irrational_threshold p mode (sinhRatApprox q) (irrational_sinh_toRat q h0)
    (sinhRatEps q) (tendsto_sinhRatEps q) 64 (fun _ hw => sinhRatApprox_spec hw q h0) w₀ hw₀

end Azurite.AzFloat
