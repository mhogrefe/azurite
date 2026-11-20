/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.PochhammerRat
import Azurite.AzFloat.Equiv.PochhammerRatCertificate

/-!
# Equivalence: Pochhammer's symbol of a rational

`pochhammerRatPrecRound_eq_or`: `pochhammerRatPrecRound q n p mode` is the correct rounding of
`Spec.pochhammer n q` (`Equiv/Pochhammer.lean`), or `(nan, .eq)` when the fuel of the Ziv loop
runs out.  The steps: `pochRatHasZero_spec`, `pochRatSplit_le`, `pochRatCore_spec`.
-/

namespace Azurite.AzFloat

open Finset

/-- **The backed loop of `(q)ₙ` is correct** at the rationals recognized by
`pochRatSpecial`, at every fuel. -/
theorem pochRatBacked_eq {q : AzRat} {n : ℕ} (hn : n ≠ 0) (hc : pochRatSpecial q = true)
    (p : ℕ) [NeZero p] (mode : RoundingMode) (fuel : ℕ)
    (h : ∃ f : ℕ, (roundingPossible (pochRatApprox q n (max 64 (p + 32) * 2 ^ f)).1
      (pochRatApprox q n (max 64 (p + 32) * 2 ^ f)).2 p mode).isSome = true) :
    zivLoopBacked (pochRatApprox q n) p mode fuel (max 64 (p + 32)) h
      = roundVal p mode (some ((∏ j ∈ range n, (((AzRat.toRat q : ℚ) : ℝ) + j) : ℝ) : EReal)) :=
  zivLoopBacked_eq p mode _ (not_mem_floatSet_of_not_isDyadic p (not_isDyadic_pochRat hc hn)) 64
    (fun w hw => (gammaApproxOf_valid_or_none
      (fun _ _ hcw => pochRatCore_spec q hw hcw) w p mode).imp_left
        fun ⟨lv, hv', h1, h2, h3, h4, _⟩ => ⟨lv, hv', h1, h2, h3, h4⟩)
    fuel _ (le_max_left _ _) (Nat.lt_of_lt_of_le (by norm_num) (le_max_left 64 _)) h

/-- **Pochhammer's symbol of a rational is correctly rounded, or it is the loop with fuel**
off the zeros, `n ≥ 1`. -/
theorem pochhammerRatPrecRoundFuel_eq_or_loop (fuel : ℕ) (q : AzRat) (n p : ℕ) [NeZero p]
    (mode : RoundingMode) :
    pochhammerRatPrecRoundFuel fuel q n p mode
        = roundVal p mode (Spec.pochhammer n (((AzRat.toRat q : ℚ) : ℝ) : EReal)) ∨
      (n ≠ 0 ∧ pochRatHasZero q n = false ∧ pochRatSpecial q = false ∧
        pochhammerRatPrecRoundFuel fuel q n p mode
          = zivLoop (pochRatApprox q n) p mode fuel (max 64 (p + 32))) := by
  have hp := NeZero.ne p
  unfold pochhammerRatPrecRoundFuel
  by_cases hn : n = 0
  · left
    rw [dite_eq_left hn, ite_eq_right hp, hn, Spec.pochhammer_zero,
      setPrecRound_eq_roundVal toVal_one', EReal.coe_one]
  rw [dite_eq_right hn, Spec.pochhammer_coe hn]
  by_cases hz : pochRatHasZero q n = true
  · left
    rw [ite_eq_left hz, pochRatHasZero_spec hz, EReal.coe_zero, roundVal_zero]
  rw [ite_eq_right hz, dite_eq_right hp]
  split
  · next r hr =>
    left
    unfold pochRatExact? at hr
    split_ifs at hr
    rw [Option.some.injEq] at hr
    subst hr
    exact pochIntQuot_eq (by rw [AzRat.toInt_toAzInt']; exact_mod_cast den_pos_real q)
      (mkNorm_div_den_eq q) n p mode
  · by_cases hc : pochRatSpecial q = true
    · left
      rw [dite_eq_left hc]
      exact pochRatBacked_eq hn hc p mode fuel _
    · right
      rw [dite_eq_right hc]
      exact ⟨hn, by simpa using hz, by simpa using hc, rfl⟩

/-- The loop of `(q)ₙ` is correct when it does not give up. -/
theorem pochRatLoop_eq_of_ne_nan (q : AzRat) (n p : ℕ) [NeZero p] (mode : RoundingMode)
    (fuel : ℕ) (h : zivLoop (pochRatApprox q n) p mode fuel (max 64 (p + 32)) ≠ (nan, .eq)) :
    zivLoop (pochRatApprox q n) p mode fuel (max 64 (p + 32))
      = roundVal p mode (some ((∏ j ∈ range n, (((AzRat.toRat q : ℚ) : ℝ) + j) : ℝ) : EReal)) :=
  zivLoop_eq_of_ne_nan_or_none p mode _ _ 64
    (fun w hw => gammaApproxOf_valid_or_none (fun _ _ hc => pochRatCore_spec q hw hc) w p mode)
    _ _ (le_max_left _ _) h

/-- **Pochhammer's symbol of a rational is correctly rounded, or the fuel ran out**, at
every fuel. -/
theorem pochhammerRatPrecRoundFuel_eq_or (fuel : ℕ) (q : AzRat) (n p : ℕ) [NeZero p]
    (mode : RoundingMode) :
    pochhammerRatPrecRoundFuel fuel q n p mode
        = roundVal p mode (Spec.pochhammer n (((AzRat.toRat q : ℚ) : ℝ) : EReal)) ∨
      pochhammerRatPrecRoundFuel fuel q n p mode = (nan, .eq) := by
  rcases pochhammerRatPrecRoundFuel_eq_or_loop fuel q n p mode with h | ⟨hn, -, -, h⟩
  · exact Or.inl h
  · rw [h, Spec.pochhammer_coe hn]
    rcases eq_or_ne (zivLoop (pochRatApprox q n) p mode fuel (max 64 (p + 32)))
      (nan, .eq) with hzv | hzv
    · exact Or.inr hzv
    · exact Or.inl (pochRatLoop_eq_of_ne_nan q n p mode fuel hzv)

/-- **Pochhammer's symbol of a rational is correctly rounded, or the fuel ran out.** -/
theorem pochhammerRatPrecRound_eq_or (q : AzRat) (n p : ℕ) [NeZero p] (mode : RoundingMode) :
    pochhammerRatPrecRound q n p mode
        = roundVal p mode (Spec.pochhammer n (((AzRat.toRat q : ℚ) : ℝ) : EReal)) ∨
      pochhammerRatPrecRound q n p mode = (nan, .eq) :=
  pochhammerRatPrecRoundFuel_eq_or (gammaFuel p) q n p mode

/-! ### The specification -/

/-- **`pochhammerRatPrecRoundFuel` is exact or a convergent loop.** -/
theorem pochhammerRatPrecRoundFuel_zivCases (q : AzRat) (n p : ℕ) [NeZero p]
    (mode : RoundingMode) :
    ZivCases (fun fuel => pochhammerRatPrecRoundFuel fuel q n p mode)
      (Spec.pochhammer n (((AzRat.toRat q : ℚ) : ℝ) : EReal)) p mode := by
  have hp := NeZero.ne p
  by_cases hn : n = 0
  · refine Or.inl fun fuel => ?_
    show pochhammerRatPrecRoundFuel fuel q n p mode = _
    unfold pochhammerRatPrecRoundFuel
    rw [dite_eq_left hn, ite_eq_right hp, hn, Spec.pochhammer_zero,
      setPrecRound_eq_roundVal toVal_one', EReal.coe_one]
  rw [Spec.pochhammer_coe hn]
  by_cases hz : pochRatHasZero q n = true
  · refine Or.inl fun fuel => ?_
    show pochhammerRatPrecRoundFuel fuel q n p mode = _
    unfold pochhammerRatPrecRoundFuel
    rw [dite_eq_right hn, ite_eq_left hz, pochRatHasZero_spec hz, EReal.coe_zero, roundVal_zero]
  cases hr : pochRatExact? q n p mode with
  | some r =>
    refine Or.inl fun fuel => ?_
    show pochhammerRatPrecRoundFuel fuel q n p mode = _
    unfold pochhammerRatPrecRoundFuel
    rw [dite_eq_right hn, ite_eq_right hz, dite_eq_right hp, hr]
    unfold pochRatExact? at hr
    split_ifs at hr
    rw [Option.some.injEq] at hr
    subst hr
    exact pochIntQuot_eq (by rw [AzRat.toInt_toAzInt']; exact_mod_cast den_pos_real q)
      (mkNorm_div_den_eq q) n p mode
  | none =>
    by_cases hc : pochRatSpecial q = true
    · refine Or.inl fun fuel => ?_
      show pochhammerRatPrecRoundFuel fuel q n p mode = _
      unfold pochhammerRatPrecRoundFuel
      rw [dite_eq_right hn, ite_eq_right hz, dite_eq_right hp, hr]
      dsimp only
      rw [dite_eq_left hc]
      exact pochRatBacked_eq hn hc p mode fuel _
    · refine (ZivCases.of_core (pochRatCore_coreConv q (by simpa using hz))
        (fun w hw neg b hc => pochRatCore_spec q hw hc) p mode).congr fun fuel => ?_
      show pochhammerRatPrecRoundFuel fuel q n p mode = _
      unfold pochhammerRatPrecRoundFuel
      rw [dite_eq_right hn, ite_eq_right hz, dite_eq_right hp, hr]
      dsimp only
      rw [dite_eq_right hc]
      rfl

/-- The specification of Pochhammer's symbol of a rational without the non-dyadic values:
sound at every
fuel; complete in the limit of the fuel wherever the value is no rounding boundary; correct
at every fuel for `n = 0` and where a factor vanishes. -/
theorem pochhammerRatPrecRoundFuel_zivSpec_base :
    ZivSpec (fun qn : AzRat × ℕ =>
        Spec.pochhammer qn.2 ((((AzRat.toRat qn.1 : ℚ) : ℝ) : ℝ) : EReal))
      (fun fuel qn p mode => pochhammerRatPrecRoundFuel fuel qn.1 qn.2 p mode)
      {qn | qn.2 = 0 ∨ pochRatHasZero qn.1 qn.2 = true} ∅ where
  sound := fun fuel qn p _ mode => pochhammerRatPrecRoundFuel_eq_or fuel qn.1 qn.2 p mode
  complete := fun qn p _ mode hB => by
    by_cases hgen : qn.2 ≠ 0 ∧ pochRatHasZero qn.1 qn.2 = false
    · obtain ⟨hn, hz⟩ := hgen
      have hval := Spec.pochhammer_coe hn ((AzRat.toRat qn.1 : ℚ) : ℝ)
      have hB' := hB _ hval
      obtain ⟨F, hF⟩ := zivLoop_eventually_eq p mode (pochRatApprox qn.1 qn.2)
        (pochRatApprox_bracketConv qn.1 hz) (ne_zero_of_not_mem_floatSet hB') hB'
        (max 64 (p + 32)) (Nat.lt_of_lt_of_le (by norm_num) (le_max_left 64 _))
        (fun w hw => (gammaApproxOf_valid_or_none
          (fun _ _ hc => pochRatCore_spec qn.1 (le_trans (le_max_left _ _) hw) hc) w p
            mode).imp_left fun ⟨lv, hv', h1, h2, h3, h4, _⟩ => ⟨lv, hv', h1, h2, h3, h4⟩)
      refine ⟨F, fun fuel hfuel => ?_⟩
      rcases pochhammerRatPrecRoundFuel_eq_or_loop fuel qn.1 qn.2 p mode with h | ⟨-, -, -, h⟩
      · exact h
      · show pochhammerRatPrecRoundFuel fuel qn.1 qn.2 p mode = _
        rw [h, hval]
        exact hF fuel hfuel
    · refine ⟨0, fun fuel _ => ?_⟩
      rcases pochhammerRatPrecRoundFuel_eq_or_loop fuel qn.1 qn.2 p mode with h | ⟨hn, hz, -, -⟩
      · exact h
      · exact absurd ⟨hn, hz⟩ hgen
  dyadic := fun qn hqn v hv => by
    by_cases hn : qn.2 = 0
    · rw [hn, Spec.pochhammer_zero, Option.some.injEq] at hv
      have : v = 1 := by exact_mod_cast hv.symm
      rw [this]
      exact isDyadic_one
    · rw [Spec.pochhammer_coe hn, Option.some.injEq, EReal.coe_eq_coe_iff] at hv
      rcases hqn with h | h
      · exact absurd h hn
      · rw [pochRatHasZero_spec h] at hv
        rw [← hv]
        exact isDyadic_zero
  nondyadic := fun qn h => absurd h (Set.notMem_empty _)
  correct := fun qn hqn fuel p _ mode => by
    rcases pochhammerRatPrecRoundFuel_eq_or_loop fuel qn.1 qn.2 p mode with h | ⟨hn, hz, -, -⟩
    · exact h
    · exfalso
      rcases hqn with (h | h) | h
      · exact hn h
      · rw [hz] at h
        cases h
      · exact absurd h (Set.notMem_empty _)

/-- A specification with more arguments known to have non-dyadic values: those where the
function is correct at every fuel. -/
theorem ZivSpec.withN {α : Type*} {val : α → Option EReal}
    {f : ℕ → α → ℕ → RoundingMode → AzFloat × Ordering} {D N : Set α}
    (h : ZivSpec val f D ∅) (hN : ∀ x ∈ N, ∃ v : ℝ, val x = some (v : EReal) ∧ ¬ IsDyadic v)
    (hcorr : ∀ x ∈ N, ∀ (fuel : ℕ) (p : ℕ) [NeZero p] (mode : RoundingMode),
      f fuel x p mode = roundVal p mode (val x)) : ZivSpec val f D N where
  sound := h.sound
  complete := h.complete
  dyadic := h.dyadic
  nondyadic := hN
  correct := fun x hx fuel p _ mode => by
    rcases hx with hx | hx
    · exact h.correct x (Or.inl hx) fuel p mode
    · exact hcorr x hx fuel p mode

/-- **Pochhammer's symbol of a rational is correctly rounded at every fuel** when the
denominator is not a power of two. -/
theorem pochhammerRatPrecRoundFuel_eq_of_special (fuel : ℕ) {q : AzRat} (n : ℕ)
    (hc : pochRatSpecial q = true) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    pochhammerRatPrecRoundFuel fuel q n p mode
      = roundVal p mode (Spec.pochhammer n (((AzRat.toRat q : ℚ) : ℝ) : EReal)) := by
  rcases pochhammerRatPrecRoundFuel_eq_or_loop fuel q n p mode with h | ⟨-, -, hc', -⟩
  · exact h
  · rw [hc] at hc'
    cases hc'

/-- **The specification of Pochhammer's symbol of a rational** (`ZivSpec`): sound at every
fuel; complete in the limit of the fuel wherever the value is no rounding boundary; correct
at every fuel for `n = 0`, where a factor vanishes, and — the value being a fraction that is
not dyadic — wherever the denominator of `q` is not a power of two. -/
theorem pochhammerRatPrecRoundFuel_zivSpec :
    ZivSpec (fun qn : AzRat × ℕ =>
        Spec.pochhammer qn.2 ((((AzRat.toRat qn.1 : ℚ) : ℝ) : ℝ) : EReal))
      (fun fuel qn p mode => pochhammerRatPrecRoundFuel fuel qn.1 qn.2 p mode)
      {qn | qn.2 = 0 ∨ pochRatHasZero qn.1 qn.2 = true}
      {qn | qn.2 ≠ 0 ∧ pochRatSpecial qn.1 = true} :=
  pochhammerRatPrecRoundFuel_zivSpec_base.withN
    (fun _ hqn => ⟨_, Spec.pochhammer_coe hqn.1 _, not_isDyadic_pochRat hqn.2 hqn.1⟩)
    (fun qn hqn fuel p _ mode =>
      pochhammerRatPrecRoundFuel_eq_of_special fuel qn.2 hqn.2 p mode)

end Azurite.AzFloat
