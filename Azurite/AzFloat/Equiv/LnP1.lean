/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.LnP1
import Azurite.AzFloat.Equiv.Ln

/-!
# Equivalence: `ln (1 + x)`

`lnP1PrecRound_eq_liftVal : lnP1PrecRound x p mode = liftVal (fun a => Spec.log (a + 1)) x p mode`:
`ln (1 + x)` is correctly rounded in every mode, with the exact comparison, and without fuel.
-/

namespace Azurite.AzFloat

/-- The tiny-argument path answers with the rounding of `ln (1 + x)`. -/
theorem lnP1Tiny?_eq {s : Bool} {e : AzInt} {q : ℕ} {m : AzNat} (hv : FiniteValid q m) (p : ℕ)
    [NeZero p] (mode : RoundingMode) {r : AzFloat × Ordering}
    (h : lnP1Tiny? (finite s e q m hv) e q p mode = some r) :
    r = roundVal p mode (some ((Real.log (1 + finiteVal s e m) : ℝ) : EReal)) := by
  unfold lnP1Tiny? at h
  dsimp only at h
  split_ifs at h with hc
  obtain ⟨hs, he⟩ := hc
  obtain ⟨r', hr', rfl⟩ := Option.map_eq_some_iff.mp h
  set w := max p q + zivGuardBits with hw
  have : NeZero (w + 8) := ⟨by omega⟩
  set xv := finiteVal s e m with hxv
  have hx : (finite s e q m hv).toVal = some (xv : EReal) := toVal_finite s e q m hv
  obtain ⟨hlt, h2e⟩ := abs_finiteVal_lt_of_tiny s hv hs he
  rw [← hxv] at hlt
  have h256 : (1 / 2 : ℝ) ^ (w + 8) ≤ 1 / 2 := by
    calc (1 / 2 : ℝ) ^ (w + 8) ≤ (1 / 2 : ℝ) ^ 1 :=
          pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
      _ = 1 / 2 := by norm_num
  set t := (2 : ℝ) ^ e.toInt with ht
  have ht0 : 0 < t := by positivity
  have hax := abs_nonneg xv
  have hxhalf : -1 / 2 ≤ xv := by
    have := neg_abs_le xv; linarith
  have hpos : 0 < 1 + xv := by linarith
  have hx0 : xv ≠ 0 := finiteVal_ne_zero s e hv
  have hirr := irrational_log_one_add_of_toVal hx hpos hx0
  have hnx : (-(finite s e q m hv)).toVal = some ((-xv : ℝ) : EReal) := by
    rw [toVal_neg, hx, Option.map_some, EReal.coe_neg]
  have habs : (finite s e q m hv).abs.toVal = some ((|xv| : ℝ) : EReal) := by
    rw [toVal_abs, hx, Option.map_some, ← EReal.coe_neg]
    congr 1
  have hd : ((((finite s e q m hv).abs <<< e) <<< AzInt.ofInt 1)).toVal
      = some ((2 * (|xv| * t) : ℝ) : EReal) := by
    rw [toVal_shiftLeft_of_toVal (toVal_shiftLeft_of_toVal habs e), AzInt.toInt_ofInt,
      zpow_one, mul_comm]
  obtain ⟨hi, hhi, hhi1, -⟩ := addCeiling_abs hnx hd (w + 8)
  have hsq : xv ^ 2 ≤ |xv| * t := by
    rw [← sq_abs, sq]; exact mul_le_mul_of_nonneg_left hlt.le hax
  have hlow := sub_two_mul_sq_le_log_one_add hxhalf
  have hup : Real.log (1 + xv) ≤ xv := by
    have := Real.log_le_sub_one_of_pos hpos; linarith
  have hR1 := rounds_setPrecRound (isFinite_of_toVal_coe hnx)
  rw [fval_of_toVal_coe hnx] at hR1
  have hR2 := rounds_setPrecRound (isFinite_of_toVal_coe hhi)
  rw [fval_of_toVal_coe hhi] at hR2
  have hr := roundingPossible_eq' p (-mode) (v := -Real.log (1 + xv)) hR1 hR2 (by linarith)
    (by linarith) (Or.inr (not_mem_floatSet_of_irrational p hirr.neg)) hr'
  rw [hr]
  have hneg := roundVal_neg p mode (-Real.log (1 + xv))
  rw [neg_neg] at hneg
  exact hneg.symm

/-- `lnP1PrecRoundCore A hA` is correctly rounded for every bracket function `A` with the
conclusion of `lnP1Approx_spec`. -/
theorem lnP1PrecRoundCore_eq_liftVal (A : AzFloat → ℕ → Roundable × Roundable) (hA)
    (hspec : ∀ {w : ℕ}, 64 ≤ w → ∀ {x : AzFloat} {xv : ℝ}, x.toVal = some (xv : EReal) →
      -1 < xv → xv ≠ 0 →
      ∃ lv hv : ℝ, Rounds (A x w).1 lv ∧ Rounds (A x w).2 hv ∧
        lv < Real.log (1 + xv) ∧ Real.log (1 + xv) < hv ∧
        hv - lv ≤ lnRatEps (⌊2 * |Real.log (1 + xv)|⌋₊ + 2) |Real.log (1 + xv)| w)
    (x : AzFloat) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    lnP1PrecRoundCore A hA x p mode = liftVal (fun a => Spec.log (a + 1)) x p mode := by
  unfold liftVal
  cases x with
  | nan => rfl
  | infinity s =>
    cases s
    · simp only [lnP1PrecRoundCore, toVal_infinity, Bool.false_eq_true, ↓reduceIte,
        Option.bind_some, EReal.bot_add, Spec.log_bot, roundVal_none]
    · simp only [lnP1PrecRoundCore, toVal_infinity, ↓reduceIte, Option.bind_some]
      rw [← EReal.coe_one, EReal.top_add_coe, Spec.log_top, roundVal_top]
  | zero =>
    simp only [lnP1PrecRoundCore, toVal_zero, Option.bind_some]
    rw [zero_add, ← EReal.coe_one, Spec.log_coe _ one_pos, Real.log_one, EReal.coe_zero,
      roundVal_zero]
  | finite s e q m hv =>
    cases s with
    | true =>
      have hpos := finiteVal_true_pos e hv
      simp only [lnP1PrecRoundCore, toVal_finite, Option.bind_some]
      split_ifs with hp
      · exact absurd hp (NeZero.ne p)
      rw [← EReal.coe_one, ← EReal.coe_add, Spec.log_coe _ (by linarith),
        add_comm (finiteVal true e m) 1]
      split
      · next r hT => exact lnP1Tiny?_eq hv p mode hT
      exact zivLoopCertified_eq_threshold p mode _ (Real.log (1 + finiteVal true e m)) _
        (by unfold zivGuardBits; omega)
        (fun w hw => by
          obtain ⟨lv, hv', hl, hh, hlo, hhi, -⟩ :=
            hspec (w := w) (by unfold zivGuardBits at hw; omega)
              (toVal_finite true e q m hv) (by linarith) hpos.ne'
          exact ⟨lv, hv', hl, hh, hlo.le, hhi.le, fun h => absurd h hlo.ne⟩) _
    | false =>
      simp only [lnP1PrecRoundCore, toVal_finite, Option.bind_some]
      split_ifs with hneg heq hp
      · -- `x = −1`
        obtain ⟨v, hx, h1⟩ := (eqIEEE_iff _ _).mp heq
        rw [toVal_finite] at hx
        rw [toVal_neg_one, ← hx, Option.some.injEq, EReal.coe_eq_coe_iff] at h1
        rw [← h1, ← EReal.coe_one, ← EReal.coe_add, neg_add_cancel, EReal.coe_zero, Spec.log_zero,
          roundVal_bot]
      · -- `x < −1`
        have hle := finiteVal_false_le_neg_one e hv hneg
        have hne : finiteVal false e m ≠ -1 := fun h => heq ((eqIEEE_iff _ _).mpr
          ⟨((-1 : ℝ) : EReal), by rw [toVal_finite, h], toVal_neg_one⟩)
        have hlt : finiteVal false e m + 1 < 0 := by
          rcases lt_or_eq_of_le hle with h | h
          · linarith
          · exact absurd h hne
        rw [← EReal.coe_one, ← EReal.coe_add, Spec.log_coe_neg _ hlt, roundVal_none]
      · exact absurd hp (NeZero.ne p)
      · have hgt := finiteVal_false_gt_neg_one e hv hneg
        rw [← EReal.coe_one, ← EReal.coe_add, Spec.log_coe _ (by linarith),
          add_comm (finiteVal false e m) 1]
        split
        · next r hT => exact lnP1Tiny?_eq hv p mode hT
        exact zivLoopCertified_eq_threshold p mode _ (Real.log (1 + finiteVal false e m)) _
          (by unfold zivGuardBits; omega)
          (fun w hw => by
            obtain ⟨lv, hv', hl, hh, hlo, hhi, -⟩ :=
              hspec (w := w) (by unfold zivGuardBits at hw; omega)
                (toVal_finite false e q m hv) hgt (finiteVal_false_ne_zero e hv)
            exact ⟨lv, hv', hl, hh, hlo.le, hhi.le, fun h => absurd h hlo.ne⟩) _

/-- **`ln (1 + x)` is correctly rounded.** -/
theorem lnP1PrecRound_eq_liftVal (x : AzFloat) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    lnP1PrecRound x p mode = liftVal (fun a => Spec.log (a + 1)) x p mode :=
  lnP1PrecRoundCore_eq_liftVal _ _ @lnP1Approx_spec x p mode

/-- **`ln (1 + x)` with precomputed constants is correctly rounded.** -/
theorem lnP1PrecRoundWith_eq_liftVal (c : LnConsts) (x : AzFloat) (p : ℕ) [NeZero p]
    (mode : RoundingMode) :
    lnP1PrecRoundWith c x p mode = liftVal (fun a => Spec.log (a + 1)) x p mode :=
  lnP1PrecRoundCore_eq_liftVal _ _ (@lnP1ApproxWith_spec c) x p mode

theorem lnP1PrecRoundWith_eq_lnP1PrecRound (c : LnConsts) (x : AzFloat) (p : ℕ)
    (mode : RoundingMode) : lnP1PrecRoundWith c x p mode = lnP1PrecRound x p mode := by
  rcases Nat.eq_zero_or_pos p with hp | hp
  · subst hp
    cases x with
    | finite s e q m hv => cases s <;> simp [lnP1PrecRoundWith, lnP1PrecRound, lnP1PrecRoundCore]
    | _ => rfl
  · have : NeZero p := ⟨hp.ne'⟩
    rw [lnP1PrecRoundWith_eq_liftVal, lnP1PrecRound_eq_liftVal]

theorem lnP1With_eq_lnP1 (c : LnConsts) (x : AzFloat) : lnP1With c x = lnP1 x := by
  unfold lnP1With lnP1
  rw [lnP1PrecRoundWith_eq_lnP1PrecRound]

end Azurite.AzFloat
