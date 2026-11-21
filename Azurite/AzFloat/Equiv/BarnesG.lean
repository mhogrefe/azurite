/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.BarnesG
import Azurite.AzFloat.Equiv.BarnesGWidth
import Azurite.AzFloat.Equiv.Beta

/-!
# Equivalence: the Barnes `G`-function

`Spec.barnesG` and **`barnesGPrecRoundFuel_zivSpec`**: `barnesGPrecRoundFuel` is sound at every
fuel, complete in the limit of the fuel wherever the value is no rounding boundary, and correct
at every fuel on the special values, the zeros `0, −1, −2, …` and the integers up to `64`
(whose values `∏ k!` are computed exactly: `toNat_barnesGNat`).  The corollary
`barnesGPrecRound_eq_or` at the default fuel.
-/

namespace Azurite.AzFloat

open Finset DLMF
open scoped Nat

namespace Spec

/-- `G` on the extended reals: `NaN` at `−∞`, `+∞` at `+∞`. -/
noncomputable def barnesG (a : EReal) : Option EReal :=
  if a = ⊥ then none else if a = ⊤ then some ⊤ else some ((barnesGR a.toReal : ℝ) : EReal)

theorem barnesG_coe (xv : ℝ) : barnesG (xv : EReal) = some ((barnesGR xv : ℝ) : EReal) := by
  unfold barnesG
  rw [ite_eq_right (EReal.coe_ne_bot _), ite_eq_right (EReal.coe_ne_top _), EReal.toReal_coe]

end Spec

/-! ### The integers -/

theorem toNat_barnesGNatAux : ∀ (s k : ℕ) (f g : AzNat), f.toNat = k ! →
    g.toNat = ∏ i ∈ Icc 1 k, i ! →
    (barnesGNatAux s k f g).toNat = ∏ i ∈ Icc 1 (k + s), i !
  | 0, k, f, g, _, hg => by rw [barnesGNatAux, hg, Nat.add_zero]
  | s + 1, k, f, g, hf, hg => by
    rw [barnesGNatAux]
    have hf' : (f.mulNat (k + 1)).toNat = (k + 1)! := by
      rw [AzNat.toNat_mulNat, hf, Nat.factorial_succ, mul_comm]
    rw [toNat_barnesGNatAux s (k + 1) _ _ hf' (by
      rw [AzNat.toNat_mul, hg, hf', prod_Icc_succ_top (by omega)]),
      show k + 1 + s = k + (s + 1) by ring]

/-- **`barnesGNat n` is `∏_{k=1}^{n−2} k!`.** -/
theorem toNat_barnesGNat (n : ℕ) : (barnesGNat n).toNat = ∏ i ∈ Icc 1 (n - 2), i ! := by
  unfold barnesGNat
  rw [toNat_barnesGNatAux (n - 2) 0 1 1 (by simp [AzNat.toNat_one]) (by simp [AzNat.toNat_one]),
    Nat.zero_add]

/-- `G(n) = ∏_{k=1}^{n−2} k!` for every `n ≥ 1`. -/
theorem barnesGR_nat_eq {n : ℕ} (hn : 1 ≤ n) :
    barnesGR n = ((∏ i ∈ Icc 1 (n - 2), i ! : ℕ) : ℝ) := by
  rcases Nat.lt_or_ge n 2 with h | h
  · obtain rfl : n = 1 := by omega
    simp [barnesGR_one]
  · rw [barnesGR_natCast h]
    push_cast
    rfl

/-! ### The loop -/

/-- The bracket of `G(x)` is valid, or rejected. -/
theorem barnesGApprox_valid_or_none {x : AzFloat} {xv : ℝ} (hx : x.toVal = some (xv : EReal))
    (hnz : ∀ m : ℕ, xv ≠ -m) {w : ℕ} (hw : 64 ≤ w) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    (∃ lv hv : ℝ, Rounds (barnesGApprox x w).1 lv ∧ Rounds (barnesGApprox x w).2 hv ∧
        lv ≤ barnesGR xv ∧ barnesGR xv ≤ hv ∧ (lv = barnesGR xv → hv = barnesGR xv)) ∨
      roundingPossible (barnesGApprox x w).1 (barnesGApprox x w).2 p mode = none :=
  gammaApproxOf_valid_or_none (fun _ _ hc => barnesGCore_spec hx hnz hw hc) w p mode

/-- **`G` on a finite argument is correctly rounded, or it is the loop with fuel** off the
zeros and the small integers. -/
theorem barnesGRealFuel_eq_or_loop (fuel : ℕ) {x : AzFloat} {xv : ℝ}
    (hx : x.toVal = some (xv : EReal)) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    barnesGRealFuel fuel x p mode = roundVal p mode (some ((barnesGR xv : ℝ) : EReal)) ∨
      ((∀ m : ℕ, xv ≠ -m) ∧ ¬ (∃ k : ℤ, xv = k ∧ k ≤ 64) ∧
        barnesGRealFuel fuel x p mode
          = zivLoop (barnesGApprox x) p mode fuel (max 64 (p + 32))) := by
  have hp := NeZero.ne p
  unfold barnesGRealFuel
  by_cases hint : isInteger x = true
  · rw [ite_eq_left hint]
    obtain ⟨k, hk⟩ := (isInteger_iff_of_toVal hx).mp hint
    by_cases hle : le x zero = true
    · left
      rw [ite_eq_left hle]
      have hle' := (le_eq_true_iff hx toVal_zero').mp hle
      have hk0 : k ≤ 0 := by exact_mod_cast (hk ▸ hle' : (k : ℝ) ≤ 0)
      have e : xv = -((-k).toNat : ℝ) := by
        rw [hk]
        have : ((-k).toNat : ℤ) = -k := Int.toNat_of_nonneg (by omega)
        have h2 : (((-k).toNat : ℤ) : ℝ) = ((-k : ℤ) : ℝ) := by rw [this]
        push_cast at h2
        linarith
      rw [e, barnesGR_neg_nat, EReal.coe_zero, roundVal_zero]
    · rw [ite_eq_right hle, ite_eq_right hp]
      have hpos : 0 < xv := by
        by_contra h
        exact hle ((le_eq_true_iff hx toVal_zero').mpr (not_lt.mp h))
      have hk1 : 1 ≤ k := by
        have : (0 : ℝ) < (k : ℝ) := hk ▸ hpos
        have : 0 < k := by exact_mod_cast this
        omega
      by_cases hb : le x (ofAzNat (AzNat.ofNat (barnesGExactBound p))) = true
      · left
        rw [ite_eq_left hb]
        obtain ⟨ht, -⟩ := truncToAzInt_spec hx
        have hkt : (truncToAzInt x).toInt = k := by
          rw [hk, ← Int.cast_sub, ← Int.cast_abs] at ht
          have : |(truncToAzInt x).toInt - k| < 1 := by exact_mod_cast ht
          have := abs_lt.mp this
          omega
        obtain ⟨n, hn⟩ : ∃ n : ℕ, n = (truncToAzInt x).abs.toNat := ⟨_, rfl⟩
        have hnk : (n : ℤ) = k := by rw [hn, AzInt.abs_toNat_eq, hkt, abs_of_pos (by omega)]
        have hxn : xv = (n : ℕ) := by rw [hk]; exact_mod_cast hnk.symm
        rw [← hn, setPrecRound_eq_roundVal (toVal_ofAzNat _) p mode, toNat_barnesGNat, hxn,
          barnesGR_nat_eq (by omega)]
      · right
        rw [ite_eq_right hb]
        refine ⟨fun m h => ?_, ?_, rfl⟩
        · have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
          linarith
        · rintro ⟨k', hk', hk64⟩
          refine hb ((le_eq_true_iff hx (toVal_ofAzNat_ofNat _)).mpr ?_)
          have h1 : (k' : ℝ) ≤ 64 := by exact_mod_cast hk64
          have h2 : (64 : ℝ) ≤ (barnesGExactBound p : ℕ) := by
            exact_mod_cast (le_max_left 64 _ : 64 ≤ barnesGExactBound p)
          rw [hk']
          linarith
  · right
    rw [ite_eq_right hint, ite_eq_right hp]
    have hni : ¬ ∃ k : ℤ, xv = k := fun h => hint ((isInteger_iff_of_toVal hx).mpr h)
    exact ⟨fun m h => hni ⟨-(m : ℤ), by push_cast; exact h⟩, fun ⟨k, hk, _⟩ => hni ⟨k, hk⟩, rfl⟩

/-- **The specification of `G`** (`ZivSpec`): sound at every fuel; complete in the limit of the
fuel wherever the value is no rounding boundary; and correct at every fuel on the special
values, the zeros and the integers up to `64`. -/
theorem barnesGPrecRoundFuel_zivSpec :
    ZivSpec (fun x : AzFloat => x.toVal.bind Spec.barnesG)
      (fun fuel x p mode => barnesGPrecRoundFuel fuel x p mode)
      {x | ∀ xv : ℝ, x.toVal = some (xv : EReal) → ∃ k : ℤ, xv = k ∧ k ≤ 64} ∅ := by
  -- the function on an argument with a real value
  have hreal : ∀ (fuel : ℕ) (x : AzFloat) (xv : ℝ), x.toVal = some (xv : EReal) → ∀ (p : ℕ)
      (mode : RoundingMode), barnesGPrecRoundFuel fuel x p mode
        = barnesGRealFuel fuel x p mode := by
    intro fuel x xv hx p mode
    cases x with
    | nan => simp at hx
    | infinity s => cases s <;> simp at hx
    | zero => rfl
    | finite s e q m hv => rfl
  have hval : ∀ (x : AzFloat) (xv : ℝ), x.toVal = some (xv : EReal) →
      (x.toVal.bind Spec.barnesG) = some ((barnesGR xv : ℝ) : EReal) := fun x xv hx => by
    rw [hx, Option.bind_some, Spec.barnesG_coe]
  -- the arguments without a real value
  have hnon : ∀ (fuel : ℕ) (x : AzFloat), (∀ xv : ℝ, x.toVal ≠ some (xv : EReal)) → ∀ (p : ℕ)
      [NeZero p] (mode : RoundingMode), barnesGPrecRoundFuel fuel x p mode
        = roundVal p mode (x.toVal.bind Spec.barnesG) := by
    intro fuel x hx p _ mode
    cases x with
    | nan => rfl
    | infinity s =>
      cases s
      · simp [barnesGPrecRoundFuel, Spec.barnesG]
      · simp [barnesGPrecRoundFuel, Spec.barnesG]
    | zero => exact absurd toVal_zero' (hx 0)
    | finite s e q m hv => exact absurd (toVal_finite s e q m hv) (hx _)
  have hcases : ∀ x : AzFloat, (∃ xv : ℝ, x.toVal = some (xv : EReal)) ∨
      ∀ xv : ℝ, x.toVal ≠ some (xv : EReal) := fun x => by
    by_cases h : ∃ xv : ℝ, x.toVal = some (xv : EReal)
    · exact Or.inl h
    · exact Or.inr fun xv hxv => h ⟨xv, hxv⟩
  refine ⟨fun fuel x p _ mode => ?_, fun x p _ mode hB => ?_, fun x hx v hv => ?_,
    fun x hx => absurd hx (Set.notMem_empty _), fun x hx fuel p _ mode => ?_⟩
  · rcases hcases x with ⟨xv, hxv⟩ | hno
    · rw [hreal fuel x xv hxv, hval x xv hxv]
      rcases barnesGRealFuel_eq_or_loop fuel hxv p mode with h | ⟨hnz, -, h⟩
      · exact Or.inl h
      · rcases eq_or_ne (barnesGRealFuel fuel x p mode) (nan, .eq) with hz | hz
        · exact Or.inr hz
        · left
          rw [h] at hz ⊢
          exact zivLoop_eq_of_ne_nan_or_none p mode _ _ 64
            (fun w hw => barnesGApprox_valid_or_none hxv hnz hw p mode) _ _
            (le_max_left _ _) hz
    · exact Or.inl (hnon fuel x hno p mode)
  · rcases hcases x with ⟨xv, hxv⟩ | hno
    · rw [hval x xv hxv] at hB ⊢
      by_cases hnz : ∀ m : ℕ, xv ≠ -m
      · have hB' := hB _ rfl
        obtain ⟨F, hF⟩ := zivLoop_eventually_eq p mode (barnesGApprox x)
          (gammaApproxOf_bracketConv (barnesGCore_coreConv hxv hnz))
          (ne_zero_of_not_mem_floatSet hB') hB' (max 64 (p + 32)) (by omega)
          (fun w hw =>
            (barnesGApprox_valid_or_none hxv hnz (le_trans (le_max_left _ _) hw) p mode).imp_left
              fun ⟨lv, hv, h1, h2, h3, h4, _⟩ => ⟨lv, hv, h1, h2, h3, h4⟩)
        refine ⟨F, fun fuel hfuel => ?_⟩
        rw [hreal fuel x xv hxv]
        rcases barnesGRealFuel_eq_or_loop fuel hxv p mode with h | ⟨-, -, h⟩
        · exact h
        · rw [h]
          exact hF fuel hfuel
      · refine ⟨0, fun fuel _ => ?_⟩
        rw [hreal fuel x xv hxv]
        rcases barnesGRealFuel_eq_or_loop fuel hxv p mode with h | ⟨h, -, -⟩
        · exact h
        · exact absurd h hnz
    · exact ⟨0, fun fuel _ => hnon fuel x hno p mode⟩
  · rcases hcases x with ⟨xv, hxv⟩ | hno
    · rw [hval x xv hxv, Option.some.injEq, EReal.coe_eq_coe_iff] at hv
      obtain ⟨k, hk, -⟩ := hx xv hxv
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
    · exfalso
      cases x with
      | nan => simp at hv
      | infinity s => cases s <;> simp [Spec.barnesG] at hv
      | zero => exact hno 0 toVal_zero'
      | finite s e q m hvv => exact hno _ (toVal_finite s e q m hvv)
  · rcases hx with hD | hN
    · rcases hcases x with ⟨xv, hxv⟩ | hno
      · rw [hreal fuel x xv hxv, hval x xv hxv]
        rcases barnesGRealFuel_eq_or_loop fuel hxv p mode with h | ⟨-, h, -⟩
        · exact h
        · exact absurd (hD xv hxv) h
      · exact hnon fuel x hno p mode
    · exact absurd hN (Set.notMem_empty _)

/-- **`G` is correctly rounded, or the fuel ran out.** -/
theorem barnesGPrecRound_eq_or (x : AzFloat) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    barnesGPrecRound x p mode = roundVal p mode (x.toVal.bind Spec.barnesG) ∨
      barnesGPrecRound x p mode = (nan, .eq) :=
  barnesGPrecRoundFuel_zivSpec.sound (barnesGFuel x p) x p mode

end Azurite.AzFloat
