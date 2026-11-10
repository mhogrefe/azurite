/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.ExpM1Tiny
import Azurite.AzFloat.Equiv.ExpApprox
import Azurite.AzFloat.Equiv.PowBracket

/-!
# Equivalence: the tiny-exponent path of `b^x − 1`

`expM1Tiny?_eq` (the rounding of `exp (x λ) − 1`), `expM1TinyFloat?_eq` and `expM1TinyRat?_eq`
(a float and a rational `x`).  No irrationality is needed: `x λ < exp (x λ) − 1` strictly.
-/

namespace Azurite.AzFloat

theorem expM1TinyCore_eq {lo h₀ : AzFloat} {E : AzInt} {p : ℕ} [NeZero p]
    {mode : RoundingMode} {r : AzFloat × Ordering} {v lv hv t : ℝ}
    (hlo : lo.toVal = some (lv : EReal)) (hh0 : h₀.toVal = some (hv : EReal)) (h1 : lv ≤ v)
    (h2 : v ≤ hv) (ht : t = (2 : ℝ) ^ E.toInt) (ht1 : t ≤ 1) (hE : |v| < t) (hv0 : v ≠ 0)
    (h : expM1TinyCore lo h₀ E p mode = some r) :
    r = roundVal p mode (some ((Real.exp v - 1 : ℝ) : EReal)) := by
  unfold expM1TinyCore at h
  have : NeZero (p + zivGuardBits + 8) := ⟨by omega⟩
  have ht0 : 0 < t := by rw [ht]; positivity
  have hd : ((one <<< E) <<< E).toVal = some ((1 * t * t : ℝ) : EReal) := by
    rw [ht]
    exact toVal_shiftLeft_of_toVal (toVal_shiftLeft_of_toVal toVal_one' E) E
  obtain ⟨hi, hhi, hhi1, -⟩ := addCeiling_abs hh0 hd (p + zivGuardBits + 8)
  have hR1 := rounds_setPrecRound (isFinite_of_toVal_coe hlo)
  rw [fval_of_toVal_coe hlo] at hR1
  have hR2 := rounds_setPrecRound (isFinite_of_toVal_coe hhi)
  rw [fval_of_toVal_coe hhi] at hR2
  have hv1 : |v| ≤ 1 := by linarith
  have hlow : v < Real.exp v - 1 := by
    have := Real.add_one_lt_exp hv0; linarith
  have hup := (abs_le.mp (Real.abs_exp_sub_one_sub_id_le hv1)).2
  have hsq : v ^ 2 ≤ t * t := by
    rw [← sq_abs, sq]
    exact mul_le_mul hE.le hE.le (abs_nonneg v) ht0.le
  exact roundingPossible_eq' p mode hR1 hR2 (by linarith) (by linarith)
    (Or.inl fun hEq => absurd hEq (by linarith)) h

theorem expM1Tiny?_eq {pos : Bool} {xlo xhi : AzFloat} {L : AzFloat × AzFloat} {E : AzInt}
    {p : ℕ} [NeZero p] {mode : RoundingMode} {r : AzFloat × Ordering} {x lam xl xh ll lh : ℝ}
    (hxl : xlo.toVal = some (xl : EReal)) (hxh : xhi.toVal = some (xh : EReal))
    (hLl : L.1.toVal = some (ll : EReal)) (hLh : L.2.toVal = some (lh : EReal))
    (hx1 : xl ≤ x) (hx2 : x ≤ xh) (hpos : pos = true → 0 ≤ xl) (hneg : pos = false → xh ≤ 0)
    (hl0 : 0 < ll) (hl1 : ll ≤ lam) (hl2 : lam ≤ lh) (hx0 : x ≠ 0)
    (hE : |x * lam| < (2 : ℝ) ^ E.toInt) (h : expM1Tiny? pos xlo xhi L E p mode = some r) :
    r = roundVal p mode (some ((Real.exp (x * lam) - 1 : ℝ) : EReal)) := by
  unfold expM1Tiny? at h
  dsimp only at h
  have : NeZero (p + zivGuardBits + 8) := ⟨by omega⟩
  have htoInt : E.toInt = if E.sign then (E.abs.toNat : ℤ) else -(E.abs.toNat : ℤ) := rfl
  have hlam0 : 0 < lam := by linarith
  have hv0 : x * lam ≠ 0 := mul_ne_zero hx0 hlam0.ne'
  split_ifs at h with hc hp
  all_goals
    have ht1 : (2 : ℝ) ^ E.toInt ≤ 1 := by
      rw [htoInt, hc.1]
      simp only [Bool.false_eq_true, ↓reduceIte]
      rw [zpow_neg, zpow_natCast]
      exact inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
  · have hxl0 := hpos hp
    obtain ⟨lo, hlo, hlo1, -⟩ := mulFloor_abs hxl hLl (p + zivGuardBits + 8)
    obtain ⟨h0, hh0, hh1, -⟩ := mulCeiling_abs hxh hLh (p + zivGuardBits + 8)
    exact expM1TinyCore_eq hlo hh0 (hlo1.trans (mul_le_mul hx1 hl1 hl0.le (by linarith)))
      (le_trans (mul_le_mul hx2 hl2 hlam0.le (by linarith)) hh1) rfl ht1 hE hv0 h
  · have hxh0 := hneg (by simpa using hp)
    obtain ⟨lo, hlo, hlo1, -⟩ := mulFloor_abs hxl hLh (p + zivGuardBits + 8)
    obtain ⟨h0, hh0, hh1, -⟩ := mulCeiling_abs hxh hLl (p + zivGuardBits + 8)
    refine expM1TinyCore_eq hlo hh0 (hlo1.trans ?_) (le_trans ?_ hh1) rfl ht1 hE hv0 h
    · nlinarith [mul_nonneg (sub_nonneg.mpr hx1) (by linarith : (0 : ℝ) ≤ lh),
        mul_nonneg (neg_nonneg.mpr (hx2.trans hxh0)) (sub_nonneg.mpr hl2)]
    · nlinarith [mul_nonneg (sub_nonneg.mpr hx2) hlam0.le,
        mul_nonneg (neg_nonneg.mpr hxh0) (sub_nonneg.mpr hl1)]

/-- A float `x`. -/
theorem expM1TinyFloat?_eq {s : Bool} {e : AzInt} {q : ℕ} {m : AzNat} (hv : FiniteValid q m)
    {L : AzFloat × AzFloat} {E : AzInt} {p : ℕ} [NeZero p] {mode : RoundingMode}
    {r : AzFloat × Ordering} {lam ll lh : ℝ} (hLl : L.1.toVal = some (ll : EReal))
    (hLh : L.2.toVal = some (lh : EReal)) (hl0 : 0 < ll) (hl1 : ll ≤ lam) (hl2 : lam ≤ lh)
    (hE : |finiteVal s e m * lam| < (2 : ℝ) ^ E.toInt)
    (h : expM1Tiny? s (finite s e q m hv) (finite s e q m hv) L E p mode = some r) :
    r = roundVal p mode (some ((Real.exp (finiteVal s e m * lam) - 1 : ℝ) : EReal)) := by
  have hsgn := finiteVal_sign_iff s e hv
  refine expM1Tiny?_eq (toVal_finite s e q m hv) (toVal_finite s e q m hv) hLl hLh le_rfl le_rfl
    (fun hs => (hsgn.mp hs).le) (fun hs => ?_) hl0 hl1 hl2 (finiteVal_ne_zero s e hv) hE h
  by_contra hcon
  push Not at hcon
  rw [hsgn.mpr hcon] at hs
  cases hs

/-- A rational `x = q`. -/
theorem expM1TinyRat?_eq {q : AzRat} {L : AzFloat × AzFloat} {E : AzInt} {p : ℕ} [NeZero p]
    {mode : RoundingMode} {r : AzFloat × Ordering} {lam ll lh : ℝ}
    (hLl : L.1.toVal = some (ll : EReal)) (hLh : L.2.toVal = some (lh : EReal))
    (hl0 : 0 < ll) (hl1 : ll ≤ lam) (hl2 : lam ≤ lh)
    (hE : |(AzRat.toRat q : ℝ) * lam| < (2 : ℝ) ^ E.toInt)
    (h : expM1TinyRat? q L E p mode = some r) :
    r = roundVal p mode (some ((Real.exp ((AzRat.toRat q : ℝ) * lam) - 1 : ℝ) : EReal)) := by
  unfold expM1TinyRat? at h
  split_ifs at h with h0
  have : NeZero (p + zivGuardBits + 8) := ⟨by omega⟩
  obtain ⟨xl, hxl, hxl1, hxl2⟩ := ofAzRatRound_floor_abs q (p + zivGuardBits + 8)
  obtain ⟨xh, hxh, hxh1, hxh2⟩ := ofAzRatRound_ceiling_abs q (p + zivGuardBits + 8)
  have hu : (1 / 2 : ℝ) ^ (p + zivGuardBits + 8) ≤ 1 / 2 := by
    calc (1 / 2 : ℝ) ^ (p + zivGuardBits + 8) ≤ (1 / 2 : ℝ) ^ 1 :=
          pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
      _ = 1 / 2 := by norm_num
  have hu0 : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ (p + zivGuardBits + 8) := by positivity
  have hsgn := toRat_sign_iff q h0
  have hq0 : (AzRat.toRat q : ℝ) ≠ 0 := fun hz => h0 ((AzRat.toRat_eq_zero_iff q).mp hz)
  refine expM1Tiny?_eq hxl hxh hLl hLh hxl1 hxh1 (fun hs => ?_) (fun hs => ?_) hl0 hl1 hl2 hq0
    hE h
  · have hpos := hsgn.mp hs
    rw [abs_of_pos hpos] at hxl2
    nlinarith
  · have hneg : (AzRat.toRat q : ℝ) < 0 := by
      rcases lt_or_gt_of_ne hq0 with h' | h'
      · exact h'
      · rw [hsgn.mpr h'] at hs; cases hs
    rw [abs_of_neg hneg] at hxh2
    nlinarith

/-- The bracket of `ln 2` for the tiny path. -/
theorem ln2Bracket_tiny_spec (p : ℕ) :
    ∃ ll lh : ℝ, (ln2Bracket (p + zivGuardBits + 8)).1.toVal = some (ll : EReal) ∧
      (ln2Bracket (p + zivGuardBits + 8)).2.toVal = some (lh : EReal) ∧ 0 < ll ∧
      ll ≤ Real.log 2 ∧ Real.log 2 ≤ lh := by
  have : NeZero (p + zivGuardBits + 8) := ⟨by omega⟩
  obtain ⟨lv, hv, hlv, hhv, h1, h2, -, h3⟩ := ln2Bracket_spec (p + zivGuardBits + 8)
  exact ⟨lv, hv, hlv, hhv, by linarith [h3 (by omega)], h1, h2⟩

end Azurite.AzFloat
