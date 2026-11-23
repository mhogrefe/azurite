/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.BarnesGRat
import Azurite.AzFloat.Equiv.BarnesG
import Azurite.AzFloat.Equiv.BetaRat

/-!
# Equivalence: the Barnes `G`-function of a rational

`barnesArg_rat`: a rational is an argument of the bracket (`BarnesArg`: its enclosures, its
shift, the factors `|q + k|`), so the soundness and the convergence of the bracket
(`barnesGCoreOf_spec`, `barnesGCoreOf_coreConv`) hold for it; and
**`barnesGRatPrecRoundFuel_zivSpec`**: sound at every fuel, complete in the limit of the fuel
wherever the value is no rounding boundary, correct at every fuel on the zeros and the integers
up to `64`.  The corollary `barnesGRatPrecRound_eq_or`.
-/

namespace Azurite.AzFloat

open Finset DLMF
open scoped Nat

/-! ### A rational as the argument -/

theorem LEncl.llow {a : Encl} {x lam : ℝ} (h : LEncl a x lam) : LLow a.1 x lam := by
  obtain ⟨l, u, hl, -, h0, h1, h2, h3⟩ := h
  exact ⟨l, hl, h0, h1, h2.trans h3⟩

/-- `|q| < ⌊|q|⌋ + 1`. -/
theorem abs_coe_toRat_lt (q : AzRat) :
    |((AzRat.toRat q : ℚ) : ℝ)| < ((q.num / q.den).toNat : ℝ) + 1 := by
  have hden : (0 : ℝ) < q.den.toNat := den_pos_real q
  have hd : 0 < q.den.toNat := AzRat.den_toNat_pos q
  rw [abs_coe_toRat, AzNat.toNat_div, div_lt_iff₀ hden]
  have h1 := Nat.div_add_mod q.num.toNat q.den.toNat
  have h2 := Nat.mod_lt q.num.toNat hd
  have h3 : q.num.toNat < (q.num.toNat / q.den.toNat + 1) * q.den.toNat := by
    nlinarith
  exact_mod_cast h3

/-- `|q| < 2^(barnesRatExp q)`. -/
theorem abs_coe_toRat_lt_two_pow (q : AzRat) :
    |((AzRat.toRat q : ℚ) : ℝ)| < (2 : ℝ) ^ barnesRatExp q := by
  have hv : (ofAzNat (q.num / q.den + 1)).toVal
      = some ((((q.num / q.den).toNat : ℝ) + 1 : ℝ) : EReal) := by
    rw [toVal_ofAzNat, AzNat.toNat_add, AzNat.toNat_one]
    push_cast
    rfl
  have h1 := abs_lt_two_zpow_expOf hv
  have h2 := azIntPos_cast (expOf (ofAzNat (q.num / q.den + 1)))
  have h3 : (2 : ℝ) ^ (expOf (ofAzNat (q.num / q.den + 1))).toInt
      ≤ (2 : ℝ) ^ ((barnesRatExp q : ℕ) : ℤ) :=
    zpow_le_zpow_right₀ (by norm_num) (by
      unfold barnesRatExp
      rw [h2]
      exact le_max_left _ _)
  rw [zpow_natCast] at h3
  have h4 := abs_coe_toRat_lt q
  have h5 := le_abs_self (((q.num / q.den).toNat : ℝ) + 1)
  linarith

/-- The integer `N + k D` behind `q + k`. -/
theorem coe_toRat_add_nat (q : AzRat) (k : ℕ) :
    ((AzRat.toRat q : ℚ) : ℝ) + k
      = (((AzInt.mkNorm q.sign q.num + (AzNat.ofNat k).toAzInt * q.den.toAzInt).toInt : ℤ) : ℝ)
        / q.den.toNat := by
  have hden : (0 : ℝ) < q.den.toNat := den_pos_real q
  rw [coe_toRat_eq_mkNorm_div, AzInt.toInt_add, AzInt.toInt_mul, AzNat.toInt_toAzInt,
    AzNat.toInt_toAzInt, AzNat.toNat_ofNat]
  push_cast
  field_simp

/-- **A rational is an argument of the bracket.** -/
theorem barnesArg_rat (q : AzRat) : BarnesArg (barnesRatIn q) ((AzRat.toRat q : ℚ) : ℝ) where
  encl := fun V hV => by
    have : NeZero (V + barnesRatExp q + 32) := ⟨by omega⟩
    obtain ⟨l, hl, hl1, hl2⟩ := ofAzRatRound_floor_abs q (V + barnesRatExp q + 32)
    obtain ⟨u, hu, hu1, hu2⟩ := ofAzRatRound_ceiling_abs q (V + barnesRatExp q + 32)
    refine ⟨l, u, hl, hu, hl1, hu1, ?_⟩
    have hlt := abs_coe_toRat_lt_two_pow q
    have hpow : (1 / 2 : ℝ) ^ (V + barnesRatExp q + 32)
        = (1 / 2 : ℝ) ^ V * (1 / 2 : ℝ) ^ barnesRatExp q * (1 / 2 : ℝ) ^ 32 := by
      rw [pow_add, pow_add]
    have h1 : |((AzRat.toRat q : ℚ) : ℝ)| * (1 / 2 : ℝ) ^ barnesRatExp q ≤ 1 := by
      have h2 : (2 : ℝ) ^ barnesRatExp q * (1 / 2 : ℝ) ^ barnesRatExp q = 1 := by
        rw [← mul_pow]; norm_num
      have h3 := mul_le_mul_of_nonneg_right hlt.le
        (by positivity : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ barnesRatExp q)
      linarith
    have hV0 : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ V := by positivity
    have h4 : |((AzRat.toRat q : ℚ) : ℝ)| * (1 / 2 : ℝ) ^ (V + barnesRatExp q + 32)
        ≤ (1 / 2 : ℝ) ^ V * (1 / 2 : ℝ) ^ 32 := by
      rw [hpow]
      have := mul_le_mul_of_nonneg_left h1
        (by positivity : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ V * (1 / 2 : ℝ) ^ 32)
      linarith
    have h5 : (1 / 2 : ℝ) ^ V * (1 / 2 : ℝ) ^ 32 ≤ (1 / 2 : ℝ) ^ V / 4 := by
      have : (1 / 2 : ℝ) ^ 32 ≤ 1 / 4 := by norm_num
      nlinarith
    linarith
  shift_gt := fun n => by
    have hlt := abs_coe_toRat_lt q
    have hden : (0 : ℝ) < q.den.toNat := den_pos_real q
    show (n : ℝ) + 1 < _ + (barnesRatShift q n : ℝ)
    unfold barnesRatShift
    by_cases hs : q.sign = true
    · rw [ite_eq_left hs]
      have hq : (((q.num / q.den).toNat : ℕ) : ℝ) ≤ ((AzRat.toRat q : ℚ) : ℝ) := by
        rw [coe_toRat_eq_sign_mul, hs, AzNat.toNat_div, ite_eq_left rfl, one_mul,
          le_div_iff₀ hden]
        exact_mod_cast Nat.div_mul_le_self _ _
      have h := azIntPos_cast ((AzNat.ofNat (n + 2)).toAzInt - (q.num / q.den).toAzInt)
      rw [AzInt.toInt_sub, AzNat.toInt_toAzInt, AzNat.toInt_toAzInt, AzNat.toNat_ofNat] at h
      have h2 : ((n + 2 : ℕ) : ℤ) - ((q.num / q.den).toNat : ℤ)
          ≤ (azIntPos ((AzNat.ofNat (n + 2)).toAzInt - (q.num / q.den).toAzInt) : ℤ) := by
        rw [h]; exact le_max_left _ _
      have h3 : (((n + 2 : ℕ) : ℤ) - ((q.num / q.den).toNat : ℤ) : ℝ)
          ≤ ((azIntPos ((AzNat.ofNat (n + 2)).toAzInt - (q.num / q.den).toAzInt) : ℤ) : ℝ) := by
        exact_mod_cast h2
      push_cast at h3
      linarith
    · rw [ite_eq_right hs]
      have := (abs_lt.mp hlt).1
      push_cast
      linarith
  shift_le := ⟨3 + ((q.num / q.den).toNat : ℝ), fun n => by
    show (barnesRatShift q n : ℝ) ≤ _
    unfold barnesRatShift
    by_cases hs : q.sign = true
    · rw [ite_eq_left hs]
      have h := azIntPos_cast ((AzNat.ofNat (n + 2)).toAzInt - (q.num / q.den).toAzInt)
      rw [AzInt.toInt_sub, AzNat.toInt_toAzInt, AzNat.toInt_toAzInt, AzNat.toNat_ofNat] at h
      have h2 : (azIntPos ((AzNat.ofNat (n + 2)).toAzInt - (q.num / q.den).toAzInt) : ℤ)
          ≤ (n : ℤ) + 2 := by
        rw [h]; push_cast; omega
      have h3 : ((azIntPos ((AzNat.ofNat (n + 2)).toAzInt - (q.num / q.den).toAzInt) : ℤ) : ℝ)
          ≤ (((n : ℤ) + 2 : ℤ) : ℝ) := by exact_mod_cast h2
      push_cast at h3
      have : (0 : ℝ) ≤ ((q.num / q.den).toNat : ℝ) := Nat.cast_nonneg _
      linarith
    · rw [ite_eq_right hs]
      push_cast
      linarith⟩
  frac := fun V _ hu k hk => by
    have hden : (0 : ℝ) < q.den.toNat := den_pos_real q
    obtain ⟨t, ht⟩ : ∃ t : AzInt,
        t = AzInt.mkNorm q.sign q.num + (AzNat.ofNat k).toAzInt * q.den.toAzInt := ⟨_, rfl⟩
    have hval := coe_toRat_add_nat q k
    rw [← ht] at hval
    have ht0 : (t.toInt : ℝ) ≠ 0 := fun h => hk (by rw [hval, h, zero_div])
    have ht0' : t.toInt ≠ 0 := fun h => ht0 (by exact_mod_cast h)
    have habsN : ((t.abs.toNat : ℕ) : ℝ) = |(t.toInt : ℝ)| := by
      have := AzInt.abs_toNat_eq t
      rw [← Int.cast_abs, ← this]
      norm_cast
    have habs0 : t.abs ≠ 0 := fun h => by
      have h1 : ((t.abs.toNat : ℕ) : ℝ) = 0 := by rw [h, AzNat.toNat_zero]; simp
      rw [habsN] at h1
      exact ht0 (abs_eq_zero.mp h1)
    have hinv := ((LEncl.exact toVal_one' one_pos).div (w := V) hu
      (LEncl.exact (toVal_ofAzNat q.den) hden)).llow
    have hnum : LLow (ofAzNat t.abs) |(t.toInt : ℝ)| 0 := by
      have := LLow.exact (toVal_ofAzNat t.abs) (by rw [habsN]; exact abs_pos.mpr ht0)
      rwa [habsN] at this
    have hf := (hnum.mulFloor hu hinv).mono (lam' := 10 * (1 / 2 : ℝ) ^ V) (by
      have : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ V := by positivity
      linarith)
    have hq : |((AzRat.toRat q : ℚ) : ℝ) + k| = |(t.toInt : ℝ)| * (1 / (q.den.toNat : ℝ)) := by
      rw [hval, abs_div, abs_of_pos hden]
      ring
    refine ⟨!t.sign, (mulPrecRound (ofAzNat t.abs)
      (Encl.div V (Encl.exact one) (Encl.exact (ofAzNat q.den))).1 V .Floor).1, ?_, ?_, ?_⟩
    · show barnesRatFrac q V k = _
      unfold barnesRatFrac
      dsimp only
      rw [← ht, ite_eq_right habs0]
    · rw [hq]
      exact hf
    · rw [hval]
      by_cases hs : t.sign = true
      · have h0 : (0 : ℝ) ≤ (t.toInt : ℝ) := by
          exact_mod_cast (AzInt.sign_eq_true_iff t).mp hs
        simp only [hs, Bool.not_true, Bool.false_eq_true, ↓reduceIte, one_mul]
        rw [abs_of_nonneg (div_nonneg h0 hden.le)]
      · have h0 : (t.toInt : ℝ) < 0 := by
          have := (AzInt.sign_eq_true_iff t).not.mp hs
          exact_mod_cast (not_le.mp this)
        simp only [hs, Bool.not_false, ↓reduceIte, neg_one_mul]
        rw [abs_of_neg (div_neg_of_neg_of_pos h0 hden)]

/-! ### The function -/

/-- The bracket of `G(q)` is valid, or rejected. -/
theorem barnesGRatApprox_valid_or_none (q : AzRat)
    (hnz : ∀ m : ℕ, ((AzRat.toRat q : ℚ) : ℝ) ≠ -m) {w : ℕ} (hw : 64 ≤ w) (p : ℕ) [NeZero p]
    (mode : RoundingMode) :
    (∃ lv hv : ℝ, Rounds (barnesGApproxOf (barnesRatIn q) w).1 lv ∧
        Rounds (barnesGApproxOf (barnesRatIn q) w).2 hv ∧
        lv ≤ barnesGR ((AzRat.toRat q : ℚ) : ℝ) ∧ barnesGR ((AzRat.toRat q : ℚ) : ℝ) ≤ hv ∧
        (lv = barnesGR ((AzRat.toRat q : ℚ) : ℝ) → hv = barnesGR ((AzRat.toRat q : ℚ) : ℝ))) ∨
      roundingPossible (barnesGApproxOf (barnesRatIn q) w).1
        (barnesGApproxOf (barnesRatIn q) w).2 p mode = none :=
  gammaApproxOf_valid_or_none (fun _ _ hc => barnesGCoreOf_spec (barnesArg_rat q) hnz hw hc)
    w p mode

/-- **`G` of a rational is correctly rounded, or it is the loop with fuel** off the zeros and
the small integers. -/
theorem barnesGRatPrecRoundFuel_eq_or_loop (fuel : ℕ) (q : AzRat) (p : ℕ) [NeZero p]
    (mode : RoundingMode) :
    barnesGRatPrecRoundFuel fuel q p mode
        = roundVal p mode (some ((barnesGR ((AzRat.toRat q : ℚ) : ℝ) : ℝ) : EReal)) ∨
      ((∀ m : ℕ, ((AzRat.toRat q : ℚ) : ℝ) ≠ -m) ∧
        ¬ (∃ k : ℤ, ((AzRat.toRat q : ℚ) : ℝ) = k ∧ k ≤ 64) ∧
        barnesGRatPrecRoundFuel fuel q p mode
          = zivLoop (barnesGApproxOf (barnesRatIn q)) p mode fuel (max 64 (p + 32))) := by
  have hp := NeZero.ne p
  unfold barnesGRatPrecRoundFuel
  by_cases hd : q.den = 1
  · rw [ite_eq_left hd]
    have hv := coe_toRat_eq_mkNorm_of_den_one q hd
    rw [AzNat.toInt_mkNorm] at hv
    by_cases hz : q.num = 0 ∨ q.sign = false
    · left
      rw [ite_eq_left hz]
      have e : ((AzRat.toRat q : ℚ) : ℝ) = -((q.num.toNat : ℕ) : ℝ) := by
        rcases hz with h0 | hs
        · rw [hv, h0, AzNat.toNat_zero]; simp
        · rw [hv, hs]; simp
      rw [e, barnesGR_neg_nat, EReal.coe_zero, roundVal_zero]
    · rw [ite_eq_right hz, ite_eq_right hp]
      push Not at hz
      have hs : q.sign = true := by simpa using hz.2
      have hn0 : q.num.toNat ≠ 0 := fun h =>
        hz.1 (AzNat.toNat_injective (by rw [h, AzNat.toNat_zero]))
      have e : ((AzRat.toRat q : ℚ) : ℝ) = ((q.num.toNat : ℕ) : ℝ) := by
        rw [hv, hs]; simp
      by_cases hb : le (ofAzNat q.num) (ofAzNat (AzNat.ofNat (barnesGExactBound p))) = true
      · left
        rw [ite_eq_left hb, setPrecRound_eq_roundVal (toVal_ofAzNat _) p mode, toNat_barnesGNat, e,
          barnesGR_nat_eq (by omega)]
      · right
        rw [ite_eq_right hb]
        refine ⟨fun m h => ?_, ?_, rfl⟩
        · rw [e] at h
          have h1 : (0 : ℝ) < ((q.num.toNat : ℕ) : ℝ) := by
            exact_mod_cast Nat.pos_of_ne_zero hn0
          have h2 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
          linarith
        · rintro ⟨k, hk, hk64⟩
          refine hb ((le_eq_true_iff (toVal_ofAzNat _) (toVal_ofAzNat_ofNat _)).mpr ?_)
          have h1 : (k : ℝ) ≤ 64 := by exact_mod_cast hk64
          have h2 : (64 : ℝ) ≤ (barnesGExactBound p : ℕ) := by
            exact_mod_cast (le_max_left 64 _ : 64 ≤ barnesGExactBound p)
          rw [← e, hk]
          linarith
  · right
    rw [ite_eq_right hd, ite_eq_right hp]
    have hni := not_exists_int_of_den_ne_one q hd
    exact ⟨fun m h => hni ⟨-(m : ℤ), by push_cast; exact h⟩, fun ⟨k, hk, _⟩ => hni ⟨k, hk⟩, rfl⟩

/-- **The specification of `G` for a rational** (`ZivSpec`): sound at every fuel; complete in
the limit of the fuel wherever the value is no rounding boundary; correct at every fuel on the
zeros and the integers up to `64`. -/
theorem barnesGRatPrecRoundFuel_zivSpec :
    ZivSpec (fun q : AzRat => Spec.barnesG ((((AzRat.toRat q : ℚ) : ℝ) : ℝ) : EReal))
      (fun fuel q p mode => barnesGRatPrecRoundFuel fuel q p mode)
      {q | ∃ k : ℤ, ((AzRat.toRat q : ℚ) : ℝ) = k ∧ k ≤ 64} ∅ where
  sound := fun fuel q p _ mode => by
    rw [Spec.barnesG_coe]
    rcases barnesGRatPrecRoundFuel_eq_or_loop fuel q p mode with h | ⟨hnz, -, h⟩
    · exact Or.inl h
    · rcases eq_or_ne (barnesGRatPrecRoundFuel fuel q p mode) (nan, .eq) with hz | hz
      · exact Or.inr hz
      · left
        rw [h] at hz ⊢
        exact zivLoop_eq_of_ne_nan_or_none p mode _ _ 64
          (fun w hw => barnesGRatApprox_valid_or_none q hnz hw p mode) _ _
          (le_max_left _ _) hz
  complete := fun q p _ mode hB => by
    rw [Spec.barnesG_coe] at hB ⊢
    by_cases hnz : ∀ m : ℕ, ((AzRat.toRat q : ℚ) : ℝ) ≠ -m
    · have hB' := hB _ rfl
      obtain ⟨F, hF⟩ := zivLoop_eventually_eq p mode (barnesGApproxOf (barnesRatIn q))
        (gammaApproxOf_bracketConv (barnesGCoreOf_coreConv (barnesArg_rat q) hnz))
        (ne_zero_of_not_mem_floatSet hB') hB' (max 64 (p + 32)) (by omega)
        (fun w hw =>
          (barnesGRatApprox_valid_or_none q hnz (le_trans (le_max_left _ _) hw) p mode).imp_left
            fun ⟨lv, hv, h1, h2, h3, h4, _⟩ => ⟨lv, hv, h1, h2, h3, h4⟩)
      refine ⟨F, fun fuel hfuel => ?_⟩
      rcases barnesGRatPrecRoundFuel_eq_or_loop fuel q p mode with h | ⟨-, -, h⟩
      · exact h
      · rw [h]
        exact hF fuel hfuel
    · refine ⟨0, fun fuel _ => ?_⟩
      rcases barnesGRatPrecRoundFuel_eq_or_loop fuel q p mode with h | ⟨h, -, -⟩
      · exact h
      · exact absurd h hnz
  dyadic := fun q hq v hv => by
    rw [Spec.barnesG_coe, Option.some.injEq, EReal.coe_eq_coe_iff] at hv
    obtain ⟨k, hk, -⟩ := hq
    rw [← hv, hk]
    rcases le_or_gt k 0 with h0 | h0
    · have e : (k : ℝ) = -((-k).toNat : ℝ) := by
        have : ((-k).toNat : ℤ) = -k := Int.toNat_of_nonneg (by omega)
        have h2 : (((-k).toNat : ℤ) : ℝ) = ((-k : ℤ) : ℝ) := by rw [this]
        push_cast at h2
        linarith
      rw [e, barnesGR_neg_nat]
      exact isDyadic_zero
    · have e : (k : ℝ) = (k.toNat : ℝ) := by
        have : (k.toNat : ℤ) = k := Int.toNat_of_nonneg (by omega)
        exact_mod_cast this.symm
      rw [e, barnesGR_nat_eq (by omega)]
      exact isDyadic_natCast _
  nondyadic := fun q hq => absurd hq (Set.notMem_empty _)
  correct := fun q hq fuel p _ mode => by
    rw [Spec.barnesG_coe]
    rcases hq with hD | hN
    · rcases barnesGRatPrecRoundFuel_eq_or_loop fuel q p mode with h | ⟨-, h, -⟩
      · exact h
      · exact absurd hD h
    · exact absurd hN (Set.notMem_empty _)

/-- **`G` of a rational is correctly rounded, or the fuel ran out.** -/
theorem barnesGRatPrecRound_eq_or (q : AzRat) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    barnesGRatPrecRound q p mode
        = roundVal p mode (Spec.barnesG ((((AzRat.toRat q : ℚ) : ℝ) : ℝ) : EReal)) ∨
      barnesGRatPrecRound q p mode = (nan, .eq) :=
  barnesGRatPrecRoundFuel_zivSpec.sound (barnesGRatFuel q p) q p mode

end Azurite.AzFloat
