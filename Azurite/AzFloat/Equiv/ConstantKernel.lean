/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Equiv.Agm
import Azurite.AzFloat.Equiv.ExpConstants
import Azurite.AzFloat.Equiv.Interval

/-!
# Kernel certification of correctly rounded constants

The correctly rounded constants (`ePrecRound`, `ln10PrecRound`, `log10EPrecRound`, …) run Ziv's
loop with a termination certificate (`zivLoopCertified`), whose well-founded recursion the kernel
cannot reduce. For a concrete precision and rounding mode, `const_eq_zivLoop` identifies such a
constant with Ziv's loop with fuel (`zivLoop`, structural, so `decide +kernel` evaluates it) as soon
as the fuel loop does not give up; `le_of_floor_data` and `ge_of_ceiling_data` read real bounds off
the kernel-computed `valData` of the values rounded down and up. The `…_approx_ok` lemmas are the
bracket hypotheses for `e = exp 1`, `ln 10` and `log₁₀ e`.
-/

namespace Azurite.AzFloat

open Encl

/-- A correctly rounded constant equals Ziv's loop with fuel whenever the loop does not give up. -/
theorem const_eq_zivLoop {p : ℕ} [NeZero p] {mode : RoundingMode} {c : AzFloat × Ordering}
    {approx : ℕ → Roundable × Roundable} {v : ℝ} {w₀ : ℕ}
    (happrox : ∀ w, w₀ ≤ w → ∃ lv hv : ℝ, Rounds (approx w).1 lv ∧ Rounds (approx w).2 hv ∧
      lv ≤ v ∧ v ≤ hv ∧ (lv = v → hv = v))
    (hc : c = roundVal p mode (some (v : EReal))) {fuel w : ℕ} (hw : w₀ ≤ w)
    {d : Bool × ℕ × ℕ} (hd : valData (zivLoop approx p mode fuel w).1 = some d) :
    c = zivLoop approx p mode fuel w := by
  have hne : zivLoop approx p mode fuel w ≠ (nan, .eq) := by
    intro h
    have h0 : valData nan = none := rfl
    rw [h] at hd
    exact absurd (h0.symm.trans hd) (by simp)
  rw [hc, zivLoop_eq_of_ne_nan_threshold p mode approx v w₀ happrox fuel w hw hne]

/-- A value rounded down is a lower bound. -/
theorem le_of_floor_data {p : ℕ} [NeZero p] {v : ℝ} {x : AzFloat × Ordering}
    (hx : x = roundVal p .Floor (some (v : EReal))) {n d : ℕ}
    (hd : valData x.1 = some (true, n, d)) : (n : ℝ) / d ≤ v := by
  obtain ⟨r, hr, hle, -⟩ := roundVal_floor_spec p v
  rw [← hx, toVal_of_valData hd] at hr
  have := EReal.coe_injective (Option.some_injective _ hr)
  rw [← this] at hle
  simpa [signedVal] using hle

/-- A value rounded up is an upper bound. -/
theorem ge_of_ceiling_data {p : ℕ} [NeZero p] {v : ℝ} {x : AzFloat × Ordering}
    (hx : x = roundVal p .Ceiling (some (v : EReal))) {n d : ℕ}
    (hd : valData x.1 = some (true, n, d)) : v ≤ (n : ℝ) / d := by
  obtain ⟨r, hr, hle⟩ := roundVal_ceiling_spec p v
  rw [← hx, toVal_of_valData hd] at hr
  have := EReal.coe_injective (Option.some_injective _ hr)
  rw [← this] at hle
  simpa [signedVal] using hle

theorem ln10Approx_ok : ∀ w, 64 ≤ w → ∃ lv hv : ℝ, Rounds (ln10Approx w).1 lv ∧
    Rounds (ln10Approx w).2 hv ∧ lv ≤ Real.log 10 ∧ Real.log 10 ≤ hv ∧
      (lv = Real.log 10 → hv = Real.log 10) := fun w hw => by
  obtain ⟨lv, hv, hl, hh, hlo, hhi, -⟩ := ln10Approx_spec (w := w) hw
  exact ⟨lv, hv, hl, hh, hlo.le, hhi.le, fun h => absurd h hlo.ne⟩

theorem log10EApprox_ok : ∀ w, 64 ≤ w → ∃ lv hv : ℝ, Rounds (log10EApprox w).1 lv ∧
    Rounds (log10EApprox w).2 hv ∧ lv ≤ (Real.log 10)⁻¹ ∧ (Real.log 10)⁻¹ ≤ hv ∧
      (lv = (Real.log 10)⁻¹ → hv = (Real.log 10)⁻¹) := fun w hw => by
  obtain ⟨lv, hv, hl, hh, hlo, hhi, -⟩ := log10EApprox_spec (w := w) hw
  exact ⟨lv, hv, hl, hh, hlo.le, hhi.le, fun h => absurd h hlo.ne⟩

theorem eApprox_ok : ∀ w, 64 ≤ w → ∃ lv hv : ℝ, Rounds (expApprox one 1 w).1 lv ∧
    Rounds (expApprox one 1 w).2 hv ∧ lv ≤ Real.exp 1 ∧ Real.exp 1 ≤ hv ∧
      (lv = Real.exp 1 → hv = Real.exp 1) := fun w hw => by
  obtain ⟨s, q, m, hv, hone⟩ : ∃ s q m hv, one = .finite s 1 q m hv := ⟨_, _, _, _, rfl⟩
  have h1 : finiteVal s 1 m = 1 := by
    have := toVal_one'
    rw [hone, toVal_finite] at this
    exact EReal.coe_injective (Option.some_injective _ this)
  obtain ⟨lv, hv', hl, hh, hlo, hhi, -⟩ := expApprox_spec (w := w) hw s 1 hv
  rw [← hone, h1] at *
  exact ⟨lv, hv', hl, hh, hlo.le, hhi.le, fun h => absurd h hlo.ne⟩

end Azurite.AzFloat
