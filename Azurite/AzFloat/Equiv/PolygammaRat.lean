/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.PolygammaRat
import Azurite.AzFloat.Equiv.PolygammaRatCertificate
import Azurite.AzFloat.Equiv.Polygamma
import Azurite.AzFloat.Equiv.DigammaRat

/-!
# Equivalence: the polygamma functions of a rational

`polygammaRatPrecRound_eq_or`: `polygammaRatPrecRound n q p mode` is the correct rounding of
`Spec.polygamma n q` (`Equiv/Polygamma.lean`), or `(nan, .eq)` when the fuel of the Ziv loop
runs out.  The steps: `polygammaRatNegEncl_spec`, `polygammaRatEncl_spec`,
`polygammaRatTiny?_eq`.
-/

namespace Azurite.AzFloat

open Real Finset Nat

/-- A tiny rational is at most `1/4` in absolute value. -/
theorem abs_le_quarter_of_polygammaRatIsTiny {n : ℕ} {q : AzRat} {e : AzInt} {p : ℕ}
    (h : polygammaRatIsTiny n q e p = true) : |((AzRat.toRat q : ℚ) : ℝ)| ≤ 1 / 4 := by
  unfold polygammaRatIsTiny at h
  rw [Bool.and_eq_true, Bool.and_eq_true] at h
  obtain ⟨⟨-, hC⟩, hF⟩ := h
  obtain ⟨l, hl, hl1, -⟩ := ofAzRatRound_floor_abs q 64
  obtain ⟨c, hc, hc1, -⟩ := ofAzRatRound_ceiling_abs q 64
  have hq : (one <<< AzInt.ofInt (-2)).toVal = some (((1 / 4 : ℝ) : ℝ) : EReal) := by
    rw [toVal_shiftLeft_of_toVal toVal_one' (AzInt.ofInt (-2)), AzInt.toInt_ofInt]
    norm_num
  have hnq : (-(one <<< AzInt.ofInt (-2))).toVal = some (((-(1 / 4) : ℝ) : ℝ) : EReal) := by
    rw [toVal_neg, hq, Option.map_some, EReal.coe_neg]
  have h1 := (le_eq_true_iff hc hq).mp hC
  have h2 := (le_eq_true_iff hnq hl).mp hF
  rw [abs_le]
  constructor <;> linarith

/-- The tiny-argument path of `ψ⁽ⁿ⁾(q)` answers with the rounding of `ψ⁽ⁿ⁾(q)`. -/
theorem polygammaRatTiny?_eq {n : ℕ} (hn : 1 ≤ n) (q : AzRat) (h0 : q.num ≠ 0) (e : AzInt)
    (p : ℕ) [NeZero p] (mode : RoundingMode) {r : AzFloat × Ordering}
    (h : polygammaRatTiny? n q e p mode = some r) :
    r = roundVal p mode (some ((polygammaR n ((AzRat.toRat q : ℚ) : ℝ) : ℝ) : EReal)) := by
  unfold polygammaRatTiny? at h
  by_cases hc : polygammaRatIsTiny n q e p = true
  swap
  · rw [ite_eq_right hc] at h
    exact absurd h (by simp)
  rw [ite_eq_left hc] at h
  have hx0 : ((AzRat.toRat q : ℚ) : ℝ) ≠ 0 := fun h' =>
    h0 ((AzRat.toRat_eq_zero_iff q).mp (by exact_mod_cast h'))
  have hpos : q.sign = true → 0 < ((AzRat.toRat q : ℚ) : ℝ) := (toRat_sign_iff q h0).mp
  have hneg : q.sign = false → ((AzRat.toRat q : ℚ) : ℝ) < 0 := toRat_neg_of_sign_false q h0
  have hXa : IsEnclPos (lnGammaRatEncl (if q.sign then q else -q) (p + zivGuardBits + 8))
      |((AzRat.toRat q : ℚ) : ℝ)| := by
    cases hs : q.sign with
    | true =>
      rw [ite_eq_left rfl, abs_of_pos (hpos hs)]
      exact lnGammaRatEncl_spec q (hpos hs) _
    | false =>
      have hv : ((AzRat.toRat (-q) : ℚ) : ℝ) = -((AzRat.toRat q : ℚ) : ℝ) := by
        rw [AzRat.toRat_neg, Rat.cast_neg]
      rw [ite_eq_right (by simp), abs_of_neg (hneg hs), ← hv]
      exact lnGammaRatEncl_spec (-q) (by rw [hv]; linarith [hneg hs]) _
  exact polygammaTinyOf_eq hn hx0 hXa (abs_le_quarter_of_polygammaRatIsTiny hc) hpos hneg p mode h

/-- The bracket of `ψ⁽ⁿ⁾(q)` is valid, or rejected. -/
theorem polygammaRatApprox_valid_or_none {n : ℕ} (hn1 : 1 ≤ n) (q : AzRat) (h0 : q.num ≠ 0)
    (hpole : ¬ (q.den = 1 ∧ q.sign = false)) {w : ℕ} (hw : 64 ≤ w) (p : ℕ) [NeZero p]
    (mode : RoundingMode) :
    (∃ lv hv : ℝ, Rounds (polygammaRatApprox n q q.sign p w).1 lv ∧
        Rounds (polygammaRatApprox n q q.sign p w).2 hv ∧
        lv ≤ polygammaR n ((AzRat.toRat q : ℚ) : ℝ) ∧
        polygammaR n ((AzRat.toRat q : ℚ) : ℝ) ≤ hv ∧
        (lv = polygammaR n ((AzRat.toRat q : ℚ) : ℝ) →
          hv = polygammaR n ((AzRat.toRat q : ℚ) : ℝ))) ∨
      roundingPossible (polygammaRatApprox n q q.sign p w).1
        (polygammaRatApprox n q q.sign p w).2 p mode = none := by
  have hnp := gammaRat_not_pole h0 hpole
  exact lnAbsGammaApproxOf_valid_or_none
    (fun _ hc => enclRefine_spec (fun _ hw' _ hE =>
      polygammaRatEncl_spec hn1 q (fun hs => (toRat_sign_iff q h0).mp hs)
        (fun hs => ⟨toRat_neg_of_sign_false q h0 hs,
          fun k hk => hnp ⟨toRat_neg_of_sign_false q h0 hs, k, hk⟩⟩) hw' hE) p hw hc)
    w p mode

/-- **`ψ⁽ⁿ⁾` of a rational, `n ≥ 1`, is correctly rounded, or it is the loop with fuel** at an
argument that is not `0` or a pole, off the arguments with a known irrational value. -/
theorem polygammaRatPrecRoundFuel_eq_or_loop (fuel : ℕ) {n : ℕ} (hn : n ≠ 0) (q : AzRat)
    (p : ℕ) [NeZero p] (mode : RoundingMode) :
    polygammaRatPrecRoundFuel fuel n q p mode
        = roundVal p mode (Spec.polygamma n (((AzRat.toRat q : ℚ) : ℝ) : EReal)) ∨
      (q.num ≠ 0 ∧ ¬ (q.den = 1 ∧ q.sign = false) ∧ polygammaRatSpecial n q = false ∧
        polygammaRatPrecRoundFuel fuel n q p mode
          = zivLoop (polygammaRatApprox n q q.sign p) p mode fuel
            (polygammaStart n (gammaRatExp q) p)) := by
  have hp := NeZero.ne p
  unfold polygammaRatPrecRoundFuel
  have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
  rw [ite_eq_right hn]
  by_cases h0 : q.num = 0
  · left
    rw [dite_eq_left h0, coe_toRat_eq_zero_of_num_eq_zero q h0, Spec.polygamma_coe_zero hn]
    by_cases ho : n % 2 = 1
    · rw [ite_eq_left ho, roundVal_top]; simp [ho]
    · rw [ite_eq_right ho, roundVal_bot]; simp [ho]
  rw [dite_eq_right h0]
  have hx0 : ((AzRat.toRat q : ℚ) : ℝ) ≠ 0 := fun h' =>
    h0 ((AzRat.toRat_eq_zero_iff q).mp (by exact_mod_cast h'))
  by_cases hpole : q.den = 1 ∧ q.sign = false
  · left
    obtain ⟨hneg, hk⟩ := gammaRat_pole h0 hpole
    rw [dite_eq_left hpole, Spec.polygamma_coe_of_pole hn hneg hk]
    by_cases ho : n % 2 = 1
    · rw [ite_eq_left ho, ite_eq_left ho, roundVal_top]
    · rw [ite_eq_right ho, ite_eq_right ho, roundVal_none]
  have hnp := gammaRat_not_pole h0 hpole
  rw [dite_eq_right hpole, dite_eq_right hp, Spec.polygamma_coe hn hx0 hnp]
  split
  · rename_i r hr
    left
    exact polygammaRatTiny?_eq hn1 q h0 _ p mode hr
  · by_cases hc : polygammaRatSpecial n q = true
    · left
      rw [dite_eq_left hc]
      exact zivLoopBacked_eq p mode _
        (not_mem_floatSet_of_irrational p (irrational_polygamma_of_ratSpecial h0 hpole hc)) 64
        (fun w hw => (polygammaRatApprox_valid_or_none hn1 q h0 hpole hw p mode).imp_left
          fun ⟨lv, hv', h1, h2, h3, h4, _⟩ => ⟨lv, hv', h1, h2, h3, h4⟩)
        fuel _ (le_max_left _ _) (Nat.lt_of_lt_of_le (by norm_num) (le_max_left 64 _)) _
    · right
      rw [dite_eq_right hc]
      exact ⟨h0, hpole, by simpa using hc, rfl⟩

/-- **`ψ⁽ⁿ⁾` of a rational is correctly rounded, or the fuel ran out**, at every fuel. -/
theorem polygammaRatPrecRoundFuel_eq_or (fuel : ℕ) (n : ℕ) (q : AzRat) (p : ℕ) [NeZero p]
    (mode : RoundingMode) :
    polygammaRatPrecRoundFuel fuel n q p mode
        = roundVal p mode (Spec.polygamma n (((AzRat.toRat q : ℚ) : ℝ) : EReal)) ∨
      polygammaRatPrecRoundFuel fuel n q p mode = (nan, .eq) := by
  by_cases hn : n = 0
  · subst hn
    unfold polygammaRatPrecRoundFuel
    rw [ite_eq_left rfl, Spec.polygamma_zero]
    exact digammaRatPrecRoundFuel_eq_or fuel q p mode
  rcases polygammaRatPrecRoundFuel_eq_or_loop fuel hn q p mode with h | ⟨h0, hpole, -, h⟩
  · exact Or.inl h
  · rcases eq_or_ne (polygammaRatPrecRoundFuel fuel n q p mode) (nan, .eq) with hz | hz
    · exact Or.inr hz
    · left
      have hx0 : ((AzRat.toRat q : ℚ) : ℝ) ≠ 0 := fun h' =>
        h0 ((AzRat.toRat_eq_zero_iff q).mp (by exact_mod_cast h'))
      rw [h] at hz ⊢
      rw [Spec.polygamma_coe hn hx0 (gammaRat_not_pole h0 hpole)]
      exact zivLoop_eq_of_ne_nan_or_none p mode _ _ 64
        (fun w hw => polygammaRatApprox_valid_or_none (Nat.one_le_iff_ne_zero.mpr hn) q h0
          hpole hw p mode) _ _ (le_max_left _ _) hz

/-- **`ψ⁽ⁿ⁾` of a rational is correctly rounded unless the fuel runs out.** -/
theorem polygammaRatPrecRound_eq_or (n : ℕ) (q : AzRat) (p : ℕ) [NeZero p]
    (mode : RoundingMode) :
    polygammaRatPrecRound n q p mode
        = roundVal p mode (Spec.polygamma n (((AzRat.toRat q : ℚ) : ℝ) : EReal)) ∨
      polygammaRatPrecRound n q p mode = (nan, .eq) :=
  polygammaRatPrecRoundFuel_eq_or (lnGammaFuel p) n q p mode

/-- **The specification of `ψ⁽ⁿ⁾` for rationals, `n ≥ 1`** (`ZivSpec`): sound at every fuel;
complete in the limit of the fuel wherever the value is no rounding boundary; and correct at
every fuel at `0` and the poles and, for an odd `n`, at the positive integers and the
rationals of denominator `2`, where the value is irrational. -/
theorem polygammaRatPrecRoundFuel_zivSpec {n : ℕ} (hn : n ≠ 0) :
    ZivSpec (fun q : AzRat => Spec.polygamma n (((AzRat.toRat q : ℚ) : ℝ) : EReal))
      (fun fuel q p mode => polygammaRatPrecRoundFuel fuel n q p mode)
      {q | q.num = 0 ∨ (q.den = 1 ∧ q.sign = false)}
      {q | q.num ≠ 0 ∧ ¬ (q.den = 1 ∧ q.sign = false) ∧ polygammaRatSpecial n q = true} where
  sound := fun fuel q p _ mode => polygammaRatPrecRoundFuel_eq_or fuel n q p mode
  complete := fun q p _ mode hB => by
    by_cases hgen : q.num ≠ 0 ∧ ¬ (q.den = 1 ∧ q.sign = false)
    · obtain ⟨h0, hpole⟩ := hgen
      have hx0 : ((AzRat.toRat q : ℚ) : ℝ) ≠ 0 := fun h' =>
        h0 ((AzRat.toRat_eq_zero_iff q).mp (by exact_mod_cast h'))
      have hnp := gammaRat_not_pole h0 hpole
      have hval := Spec.polygamma_coe hn hx0 hnp
      have hB' := hB _ hval
      have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
      obtain ⟨F, hF⟩ := zivLoop_eventually_eq p mode (polygammaRatApprox n q q.sign p)
        (polygammaRatApprox_bracketConv hn1 q (fun hs => (toRat_sign_iff q h0).mp hs)
          (fun hs => ⟨toRat_neg_of_sign_false q h0 hs,
            fun k hk => hnp ⟨toRat_neg_of_sign_false q h0 hs, k, hk⟩⟩) p)
        (ne_zero_of_not_mem_floatSet hB') hB' (polygammaStart n (gammaRatExp q) p)
        (Nat.lt_of_lt_of_le (by norm_num) (le_max_left 64 _))
        (fun w hw => (polygammaRatApprox_valid_or_none hn1 q h0 hpole
          (le_trans (le_max_left _ _) hw) p mode).imp_left
            fun ⟨lv, hv', h1, h2, h3, h4, _⟩ => ⟨lv, hv', h1, h2, h3, h4⟩)
      refine ⟨F, fun fuel hfuel => ?_⟩
      rcases polygammaRatPrecRoundFuel_eq_or_loop fuel hn q p mode with h | ⟨-, -, -, h⟩
      · exact h
      · show polygammaRatPrecRoundFuel fuel n q p mode = _
        rw [h, hval]
        exact hF fuel hfuel
    · refine ⟨0, fun fuel _ => ?_⟩
      rcases polygammaRatPrecRoundFuel_eq_or_loop fuel hn q p mode with h | ⟨h0, hpole, -, -⟩
      · exact h
      · exact absurd ⟨h0, hpole⟩ hgen
  dyadic := fun q hq v hv => by
    exfalso
    rcases hq with h0 | hpole
    · rw [coe_toRat_eq_zero_of_num_eq_zero q h0, Spec.polygamma_coe_zero hn,
        Option.some.injEq] at hv
      split_ifs at hv
      · exact EReal.coe_ne_top v hv.symm
      · exact EReal.coe_ne_bot v hv.symm
    · by_cases h0 : q.num = 0
      · rw [coe_toRat_eq_zero_of_num_eq_zero q h0, Spec.polygamma_coe_zero hn,
          Option.some.injEq] at hv
        split_ifs at hv
        · exact EReal.coe_ne_top v hv.symm
        · exact EReal.coe_ne_bot v hv.symm
      · obtain ⟨hneg, hk⟩ := gammaRat_pole h0 hpole
        rw [Spec.polygamma_coe_of_pole hn hneg hk] at hv
        split_ifs at hv
        · rw [Option.some.injEq] at hv
          exact EReal.coe_ne_top v hv.symm
  nondyadic := fun q hq => by
    obtain ⟨h0, hpole, hc⟩ := hq
    have hx0 : ((AzRat.toRat q : ℚ) : ℝ) ≠ 0 := fun h' =>
      h0 ((AzRat.toRat_eq_zero_iff q).mp (by exact_mod_cast h'))
    exact ⟨_, Spec.polygamma_coe hn hx0 (gammaRat_not_pole h0 hpole),
      not_isDyadic_of_irrational (irrational_polygamma_of_ratSpecial h0 hpole hc)⟩
  correct := fun q hq fuel p _ mode => by
    rcases polygammaRatPrecRoundFuel_eq_or_loop fuel hn q p mode with h | ⟨h0, hpole, hc, -⟩
    · exact h
    · exfalso
      rcases hq with hD | hN
      · rcases hD with h | h
        · exact h0 h
        · exact hpole h
      · rw [hN.2.2] at hc
        exact Bool.noConfusion hc

end Azurite.AzFloat
