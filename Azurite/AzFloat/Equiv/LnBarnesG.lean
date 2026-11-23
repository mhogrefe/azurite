/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.LnBarnesG
import Azurite.AzFloat.Equiv.BarnesGRat
import Azurite.AzFloat.Equiv.LnBeta
import Azurite.AzFloat.Equiv.BetaFloatRat

/-!
# Equivalence: `ln |G|` and `ln G` for the Barnes `G`-function

The pointwise theorems on a classified argument of the bracket (`BarnesKindSpec`):
`lnAbsBarnesGKind_exact` (the zeros and the integers up to `64`: the value, no fuel),
`lnAbsBarnesGKind_main` (the rounding of `ln |G|` with the sign of `G`, or `NaN`),
`lnAbsBarnesGKind_complete`.  From them the specifications
**`lnAbsBarnesGPrecRoundFuel_zivSpec`**, **`lnBarnesGPrecRoundFuel_zivSpec`** (floats) and
**`lnAbsBarnesGRatPrecRoundFuel_zivSpec`**, **`lnBarnesGRatPrecRoundFuel_zivSpec`**
(rationals), each correct at every fuel at the integers up to `64` — where the value is `−∞`,
`0` (`n = 1, 2, 3`) or the irrational `ln G(n)` —, and the sign theorems.
-/

namespace Azurite.AzFloat

open Finset DLMF
open scoped Nat

namespace Spec

/-- `ln |G|` on the extended reals. -/
noncomputable def lnAbsBarnesG (a : EReal) : Option EReal := (barnesG a).map lnAbsE

/-- `ln G` on the extended reals (`NaN` where `G < 0`). -/
noncomputable def lnBarnesG (a : EReal) : Option EReal := (barnesG a).bind log

theorem lnAbsBarnesG_coe (xv : ℝ) :
    lnAbsBarnesG (xv : EReal) = some (lnAbsE ((barnesGR xv : ℝ) : EReal)) := by
  rw [lnAbsBarnesG, barnesG_coe, Option.map_some]

theorem lnBarnesG_coe (xv : ℝ) : lnBarnesG (xv : EReal) = log ((barnesGR xv : ℝ) : EReal) := by
  rw [lnBarnesG, barnesG_coe, Option.bind_some]

/-- Where `v ≥ 0`, `ln v` is `ln |v|`. -/
theorem log_coe_of_nonneg {v : ℝ} (hv : 0 ≤ v) : log (v : EReal) = some (lnAbsE (v : EReal)) := by
  rcases hv.eq_or_lt with rfl | hpos
  · rw [lnAbsE_zero, EReal.coe_zero, log_zero]
  · rw [log_coe v hpos, lnAbsE_coe hpos.ne', abs_of_pos hpos]

end Spec

/-! ### The classes -/

/-- What a class says of the argument. -/
def BarnesKindSpec (k : Option (Option ℕ)) (xv : ℝ) : Prop :=
  match k with
  | some none => ∃ m : ℕ, xv = -m
  | some (some n) => 1 ≤ n ∧ n ≤ 64 ∧ xv = n
  | none => (∀ m : ℕ, xv ≠ -m) ∧ ¬ ∃ j : ℤ, xv = j ∧ j ≤ 64

theorem barnesKind_spec {x : AzFloat} {xv : ℝ} (hx : x.toVal = some (xv : EReal)) :
    BarnesKindSpec (barnesKind x) xv := by
  unfold barnesKind
  by_cases hint : isInteger x = true
  · rw [ite_eq_left hint]
    obtain ⟨k, hk⟩ := (isInteger_iff_of_toVal hx).mp hint
    by_cases hle : le x zero = true
    · rw [ite_eq_left hle]
      have hle' := (le_eq_true_iff hx toVal_zero').mp hle
      have hk0 : k ≤ 0 := by exact_mod_cast (hk ▸ hle' : (k : ℝ) ≤ 0)
      refine ⟨(-k).toNat, ?_⟩
      have : ((-k).toNat : ℤ) = -k := Int.toNat_of_nonneg (by omega)
      have h2 : (((-k).toNat : ℤ) : ℝ) = ((-k : ℤ) : ℝ) := by rw [this]
      push_cast at h2
      rw [hk]
      linarith
    · rw [ite_eq_right hle]
      have hpos : 0 < xv := by
        by_contra h
        exact hle ((le_eq_true_iff hx toVal_zero').mpr (not_lt.mp h))
      have hk1 : 1 ≤ k := by
        have : (0 : ℝ) < (k : ℝ) := hk ▸ hpos
        have : 0 < k := by exact_mod_cast this
        omega
      by_cases hb : le x (ofAzNat (AzNat.ofNat 64)) = true
      · rw [ite_eq_left hb]
        have hb' := (le_eq_true_iff hx (toVal_ofAzNat_ofNat 64)).mp hb
        obtain ⟨ht, -⟩ := truncToAzInt_spec hx
        have hkt : (truncToAzInt x).toInt = k := by
          rw [hk, ← Int.cast_sub, ← Int.cast_abs] at ht
          have : |(truncToAzInt x).toInt - k| < 1 := by exact_mod_cast ht
          have := abs_lt.mp this
          omega
        obtain ⟨n, hn⟩ : ∃ n : ℕ, n = (truncToAzInt x).abs.toNat := ⟨_, rfl⟩
        have hnk : (n : ℤ) = k := by rw [hn, AzInt.abs_toNat_eq, hkt, abs_of_pos (by omega)]
        have hxn : xv = (n : ℕ) := by rw [hk]; exact_mod_cast hnk.symm
        rw [← hn]
        have hk64 : k ≤ 64 := by
          have : (k : ℝ) ≤ 64 := by rw [← hk]; exact_mod_cast hb'
          exact_mod_cast this
        exact ⟨by omega, by omega, hxn⟩
      · rw [ite_eq_right hb]
        refine ⟨fun m h => ?_, ?_⟩
        · have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
          linarith
        · rintro ⟨j, hj, hj64⟩
          refine hb ((le_eq_true_iff hx (toVal_ofAzNat_ofNat 64)).mpr ?_)
          rw [hj]
          exact_mod_cast hj64
  · rw [ite_eq_right hint]
    have hni : ¬ ∃ k : ℤ, xv = k := fun h => hint ((isInteger_iff_of_toVal hx).mpr h)
    exact ⟨fun m h => hni ⟨-(m : ℤ), by push_cast; exact h⟩, fun ⟨k, hk, _⟩ => hni ⟨k, hk⟩⟩

theorem barnesRatKind_spec (q : AzRat) :
    BarnesKindSpec (barnesRatKind q) ((AzRat.toRat q : ℚ) : ℝ) := by
  unfold barnesRatKind
  by_cases hd : q.den = 1
  · rw [ite_eq_left hd]
    have hv := coe_toRat_eq_mkNorm_of_den_one q hd
    rw [AzNat.toInt_mkNorm] at hv
    by_cases hz : q.num = 0 ∨ q.sign = false
    · rw [ite_eq_left hz]
      refine ⟨q.num.toNat, ?_⟩
      rcases hz with h0 | hs
      · rw [hv, h0, AzNat.toNat_zero]; simp
      · rw [hv, hs]; simp
    · rw [ite_eq_right hz]
      push Not at hz
      have hs : q.sign = true := by simpa using hz.2
      have hn0 : q.num.toNat ≠ 0 := fun h =>
        hz.1 (AzNat.toNat_injective (by rw [h, AzNat.toNat_zero]))
      have e : ((AzRat.toRat q : ℚ) : ℝ) = ((q.num.toNat : ℕ) : ℝ) := by
        rw [hv, hs]; simp
      by_cases hb : le (ofAzNat q.num) (ofAzNat (AzNat.ofNat 64)) = true
      · rw [ite_eq_left hb]
        have hb' := (le_eq_true_iff (toVal_ofAzNat _) (toVal_ofAzNat_ofNat 64)).mp hb
        exact ⟨by omega, by exact_mod_cast hb', e⟩
      · rw [ite_eq_right hb]
        refine ⟨fun m h => ?_, ?_⟩
        · rw [e] at h
          have h1 : (0 : ℝ) < ((q.num.toNat : ℕ) : ℝ) := by
            exact_mod_cast Nat.pos_of_ne_zero hn0
          have h2 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
          linarith
        · rintro ⟨j, hj, hj64⟩
          refine hb ((le_eq_true_iff (toVal_ofAzNat _) (toVal_ofAzNat_ofNat 64)).mpr ?_)
          rw [← e, hj]
          exact_mod_cast hj64
  · rw [ite_eq_right hd]
    have hni := not_exists_int_of_den_ne_one q hd
    exact ⟨fun m h => hni ⟨-(m : ℤ), by push_cast; exact h⟩, fun ⟨k, hk, _⟩ => hni ⟨k, hk⟩⟩

/-! ### The pointwise theorems -/

/-- `G(n) ≥ 1` at a positive integer. -/
theorem one_le_prod_factorial (n : ℕ) : 1 ≤ ∏ i ∈ Icc 1 (n - 2), i ! :=
  Nat.one_le_iff_ne_zero.mpr (prod_ne_zero_iff.mpr fun i _ => Nat.factorial_ne_zero i)

/-- **The exact classes**: the value, at every fuel, and `G ≥ 0`. -/
theorem lnAbsBarnesGKind_exact {A : BarnesIn} {xv : ℝ} {c : Option ℕ}
    (hk : BarnesKindSpec (some c) xv) (fuel p : ℕ) [NeZero p] (mode : RoundingMode) :
    lnAbsBarnesGKind A (some c) fuel p mode
        = (roundVal p mode (some (Spec.lnAbsE ((barnesGR xv : ℝ) : EReal))), true) ∧
      0 ≤ barnesGR xv := by
  have hp := NeZero.ne p
  cases c with
  | none =>
    obtain ⟨m, rfl⟩ := hk
    rw [barnesGR_neg_nat]
    exact ⟨by rw [Spec.lnAbsE_zero, roundVal_bot]; rfl, le_rfl⟩
  | some n =>
    obtain ⟨hn1, -, rfl⟩ := hk
    have hg := one_le_prod_factorial n
    have hg' : (1 : ℝ) ≤ ((∏ i ∈ Icc 1 (n - 2), i ! : ℕ) : ℝ) := by exact_mod_cast hg
    rw [barnesGR_nat_eq hn1]
    refine ⟨?_, by linarith⟩
    show (if p = 0 then _ else _) = _
    rw [ite_eq_right hp, lnPrecRound_eq_liftVal, liftVal, toVal_ofAzNat, Option.bind_some,
      toNat_barnesGNat, Spec.log_coe_of_nonneg (by linarith)]

/-- The rounding of `ln |v|` is no `NaN`. -/
theorem roundVal_lnAbsE_ne_nan (p : ℕ) [NeZero p] (mode : RoundingMode) (v : ℝ) :
    roundVal p mode (some (Spec.lnAbsE (v : EReal))) ≠ (nan, .eq) := by
  by_cases hv : v = 0
  · rw [hv, Spec.lnAbsE_zero, roundVal_bot]
    simp
  · rw [Spec.lnAbsE_coe hv]
    exact roundVal_coe_ne_nan p mode _

/-- `G(x) ≠ 0` off the zeros. -/
theorem barnesGR_ne_zero {xv : ℝ} (hnz : ∀ m : ℕ, xv ≠ -m) : barnesGR xv ≠ 0 := by
  intro h0
  obtain ⟨N, hN⟩ := exists_nat_gt (-xv)
  have hs := barnesGR_eq_shift hnz N
  have hpos : 0 < barnesGR (xv + N) := barnesGR_pos (by linarith)
  have hΓ : Real.Gamma (xv + N) ≠ 0 :=
    Real.Gamma_ne_zero fun m h => hnz (m + N) (by push_cast; linarith)
  have hP : (∏ j ∈ range N, (xv + j) ^ (j + 1)) ≠ 0 :=
    prod_ne_zero_iff.mpr fun j _ => pow_ne_zero _ fun h => hnz j (by linarith)
  rw [h0] at hs
  exact (div_ne_zero (mul_ne_zero hpos.ne' hP) (pow_ne_zero _ hΓ)) hs.symm

/-- The general class is the loop. -/
theorem lnAbsBarnesGKind_none (A : BarnesIn) (fuel p : ℕ) [NeZero p] (mode : RoundingMode) :
    lnAbsBarnesGKind A none fuel p mode
      = lnAbsLoop (barnesGLnEnclOf A) p mode fuel (max 64 (p + 32)) := by
  show (if p = 0 then _ else _) = _
  rw [ite_eq_right (NeZero.ne p)]

/-- **`ln |G|` with the sign**: `NaN`, or the rounding of `ln |G(x)|` with `G(x) ≥ 0` as the
sign. -/
theorem lnAbsBarnesGKind_main {A : BarnesIn} {xv : ℝ} (hA : BarnesArg A xv)
    {k : Option (Option ℕ)} (hk : BarnesKindSpec k xv) (fuel p : ℕ) [NeZero p]
    (mode : RoundingMode) :
    (lnAbsBarnesGKind A k fuel p mode).1 = (nan, .eq) ∨
      ((lnAbsBarnesGKind A k fuel p mode).1
          = roundVal p mode (some (Spec.lnAbsE ((barnesGR xv : ℝ) : EReal))) ∧
        ((lnAbsBarnesGKind A k fuel p mode).2 = true ↔ 0 ≤ barnesGR xv)) := by
  have hp := NeZero.ne p
  cases k with
  | some c =>
    obtain ⟨h1, h2⟩ := lnAbsBarnesGKind_exact (A := A) hk fuel p mode
    right
    rw [h1]
    exact ⟨rfl, by simpa using h2⟩
  | none =>
    obtain ⟨hnz, -⟩ := hk
    rw [lnAbsBarnesGKind_none]
    have hG0 := barnesGR_ne_zero hnz
    rw [Spec.lnAbsE_coe hG0]
    rcases lnAbsLoop_spec (v := barnesGR xv) (w₀ := 64)
      (fun w hw neg L hc => barnesGLnEnclOf_spec hA hnz hw hc) p mode fuel _
      (le_max_left _ _) with h | ⟨h1, h2⟩
    · exact Or.inl h
    · exact Or.inr ⟨h1, h2.trans ⟨le_of_lt, fun h => lt_of_le_of_ne h (Ne.symm hG0)⟩⟩

/-- **`ln |G|` is correctly rounded for every large enough fuel** where the value is no
rounding boundary. -/
theorem lnAbsBarnesGKind_complete {A : BarnesIn} {xv : ℝ} (hA : BarnesArg A xv)
    {k : Option (Option ℕ)} (hk : BarnesKindSpec k xv) (p : ℕ) [NeZero p] (mode : RoundingMode)
    (hB : ∀ t : ℝ, Spec.lnAbsE ((barnesGR xv : ℝ) : EReal) = (t : EReal) →
      ((t : ℝ) : EReal) ∉ floatSet (p + 1)) :
    ∃ F : ℕ, ∀ fuel, F ≤ fuel → (lnAbsBarnesGKind A k fuel p mode).1
      = roundVal p mode (some (Spec.lnAbsE ((barnesGR xv : ℝ) : EReal))) := by
  have hp := NeZero.ne p
  cases k with
  | some c =>
    exact ⟨0, fun fuel _ => by rw [(lnAbsBarnesGKind_exact (A := A) hk fuel p mode).1]⟩
  | none =>
    obtain ⟨hnz, -⟩ := hk
    have hG0 := barnesGR_ne_zero hnz
    rw [Spec.lnAbsE_coe hG0] at hB ⊢
    obtain ⟨F, hF⟩ := lnAbsLoop_eventually (v := Real.log |barnesGR xv|) p mode
      (core := barnesGLnEnclOf A) (w₀ := max 64 (p + 32)) (by omega)
      (fun w hw neg L hc => by
        obtain ⟨hpos, hL⟩ := barnesGLnEnclOf_spec hA hnz (le_trans (le_max_left _ _) hw) hc
        rwa [sign_mul_eq_abs hpos] at hL)
      (barnesGLnEnclOf_conv hA hnz) (hB _ rfl)
    refine ⟨F, fun fuel hfuel => ?_⟩
    rw [lnAbsBarnesGKind_none]
    exact hF fuel hfuel

/-- `ln G` from `ln |G|` and the sign. -/
def lnOfAbs (r : (AzFloat × Ordering) × Bool) : AzFloat × Ordering :=
  if r.2 then r.1 else (nan, .eq)

/-- **`ln G`**: `NaN`, or the rounding of `ln G(x)` (`NaN` where `G(x) < 0`). -/
theorem lnBarnesGKind_main {A : BarnesIn} {xv : ℝ} (hA : BarnesArg A xv)
    {k : Option (Option ℕ)} (hk : BarnesKindSpec k xv) (fuel p : ℕ) [NeZero p]
    (mode : RoundingMode) :
    lnOfAbs (lnAbsBarnesGKind A k fuel p mode)
        = roundVal p mode (Spec.log ((barnesGR xv : ℝ) : EReal)) ∨
      lnOfAbs (lnAbsBarnesGKind A k fuel p mode) = (nan, .eq) := by
  unfold lnOfAbs
  rcases lnAbsBarnesGKind_main hA hk fuel p mode with h | ⟨h1, h2⟩
  · right
    split_ifs
    · exact h
    · rfl
  · by_cases hG : 0 ≤ barnesGR xv
    · left
      rw [ite_eq_left (h2.mpr hG), h1, Spec.log_coe_of_nonneg hG]
    · right
      rw [ite_eq_right fun h => hG (h2.mp h)]

/-- **`ln G` is correctly rounded for every large enough fuel** where the value is no rounding
boundary. -/
theorem lnBarnesGKind_complete {A : BarnesIn} {xv : ℝ} (hA : BarnesArg A xv)
    {k : Option (Option ℕ)} (hk : BarnesKindSpec k xv) (p : ℕ) [NeZero p] (mode : RoundingMode)
    (hB : ∀ t : ℝ, Spec.log ((barnesGR xv : ℝ) : EReal) = some (t : EReal) →
      ((t : ℝ) : EReal) ∉ floatSet (p + 1)) :
    ∃ F : ℕ, ∀ fuel, F ≤ fuel → lnOfAbs (lnAbsBarnesGKind A k fuel p mode)
      = roundVal p mode (Spec.log ((barnesGR xv : ℝ) : EReal)) := by
  by_cases hG : 0 ≤ barnesGR xv
  · rw [Spec.log_coe_of_nonneg hG] at hB ⊢
    obtain ⟨F, hF⟩ := lnAbsBarnesGKind_complete hA hk p mode
      (fun t ht => hB t (by rw [ht]))
    refine ⟨F, fun fuel hfuel => ?_⟩
    have h1 := hF fuel hfuel
    unfold lnOfAbs
    rcases lnAbsBarnesGKind_main hA hk fuel p mode with h | ⟨-, h2⟩
    · rw [h1] at h
      exact absurd h (roundVal_lnAbsE_ne_nan p mode _)
    · rw [ite_eq_left (h2.mpr hG), h1]
  · refine ⟨0, fun fuel _ => ?_⟩
    rw [Spec.log_coe_neg _ (not_le.mp hG), roundVal_none]
    unfold lnOfAbs
    rcases lnAbsBarnesGKind_main hA hk fuel p mode with h | ⟨-, h2⟩
    · split_ifs
      · exact h
      · rfl
    · rw [ite_eq_right fun h => hG (h2.mp h)]

/-! ### The values at the integers -/

theorem barnesGR_int_nonpos {j : ℤ} (hj : j ≤ 0) : barnesGR (j : ℝ) = 0 := by
  have e : (j : ℝ) = -((-j).toNat : ℝ) := by
    have : ((-j).toNat : ℤ) = -j := Int.toNat_of_nonneg (by omega)
    have h2 : (((-j).toNat : ℤ) : ℝ) = ((-j : ℤ) : ℝ) := by rw [this]
    push_cast at h2
    linarith
  rw [e, barnesGR_neg_nat]

theorem barnesGR_int_pos {j : ℤ} (hj : 1 ≤ j) :
    barnesGR (j : ℝ) = ((∏ i ∈ Icc 1 (j.toNat - 2), i ! : ℕ) : ℝ) := by
  have e : (j : ℝ) = (j.toNat : ℝ) := by
    have : (j.toNat : ℤ) = j := Int.toNat_of_nonneg (by omega)
    exact_mod_cast this.symm
  rw [e, barnesGR_nat_eq (by omega)]

theorem barnesGR_int_small {j : ℤ} (h1 : 1 ≤ j) (h3 : j ≤ 3) : barnesGR (j : ℝ) = 1 := by
  rw [barnesGR_int_pos h1]
  have : j.toNat = 1 ∨ j.toNat = 2 ∨ j.toNat = 3 := by omega
  rcases this with h | h | h <;> rw [h] <;> simp

/-- `G(n) ≥ 2` from `n = 4` on. -/
theorem two_le_prod_factorial {n : ℕ} (hn : 4 ≤ n) : 2 ≤ ∏ i ∈ Icc 1 (n - 2), i ! := by
  have hdvd : (2 : ℕ) ! ∣ ∏ i ∈ Icc 1 (n - 2), i ! :=
    dvd_prod_of_mem _ (mem_Icc.mpr ⟨by norm_num, by omega⟩)
  exact Nat.le_of_dvd (one_le_prod_factorial n) hdvd

/-- `ln G(n)` is irrational from `n = 4` on. -/
theorem irrational_log_barnesGR_int {j : ℤ} (h4 : 4 ≤ j) :
    Irrational (Real.log (barnesGR (j : ℝ))) := by
  rw [barnesGR_int_pos (by omega)]
  have h2 := two_le_prod_factorial (n := j.toNat) (by omega)
  have := irrational_log_rat (r := ((∏ i ∈ Icc 1 (j.toNat - 2), i ! : ℕ) : ℚ))
    (by exact_mod_cast (by omega : 0 < ∏ i ∈ Icc 1 (j.toNat - 2), i !))
    (by exact_mod_cast (by omega : (∏ i ∈ Icc 1 (j.toNat - 2), i !) ≠ 1))
  exact_mod_cast this

/-! ### The specifications, generically -/

/-- **The specification of a function that is `ln |G|` on its real arguments** (those with
`R`), exact elsewhere. -/
theorem lnAbsBarnesG_zivSpec_of {α : Type*} {val : α → Option EReal}
    {f : ℕ → α → ℕ → RoundingMode → AzFloat × Ordering} (R : α → Prop) (arg : α → BarnesIn)
    (kind : α → Option (Option ℕ)) (xr : α → ℝ) (hA : ∀ x, R x → BarnesArg (arg x) (xr x))
    (hk : ∀ x, R x → BarnesKindSpec (kind x) (xr x))
    (hval : ∀ x, R x → val x = Spec.lnAbsBarnesG ((xr x : ℝ) : EReal))
    (hf : ∀ fuel x p mode, R x →
      f fuel x p mode = (lnAbsBarnesGKind (arg x) (kind x) fuel p mode).1)
    (hnon : ∀ fuel x (p : ℕ) [NeZero p] mode, ¬ R x → f fuel x p mode = roundVal p mode (val x))
    (hnonv : ∀ x, ¬ R x → ∀ v : ℝ, val x ≠ some (v : EReal)) :
    ZivSpec val f {x | R x → ∃ j : ℤ, xr x = j ∧ j ≤ 3}
      {x | R x ∧ ∃ j : ℤ, xr x = j ∧ 4 ≤ j ∧ j ≤ 64} := by
  have hexact : ∀ x, R x → (∃ j : ℤ, xr x = j ∧ j ≤ 64) → ∀ fuel (p : ℕ) [NeZero p] mode,
      f fuel x p mode = roundVal p mode (val x) := by
    intro x hR hj fuel p _ mode
    rw [hf fuel x p mode hR, hval x hR, Spec.lnAbsBarnesG_coe]
    have hkx := hk x hR
    cases hkk : kind x with
    | none => rw [hkk] at hkx; exact absurd hj hkx.2
    | some c => rw [hkk] at hkx; rw [(lnAbsBarnesGKind_exact hkx fuel p mode).1]
  refine ⟨fun fuel x p _ mode => ?_, fun x p _ mode hB => ?_, fun x hx v hv => ?_,
    fun x hx => ?_, fun x hx fuel p _ mode => ?_⟩
  · by_cases hR : R x
    · rw [hf fuel x p mode hR, hval x hR, Spec.lnAbsBarnesG_coe]
      rcases lnAbsBarnesGKind_main (hA x hR) (hk x hR) fuel p mode with h | h
      · exact Or.inr h
      · exact Or.inl h.1
    · exact Or.inl (hnon fuel x p mode hR)
  · by_cases hR : R x
    · rw [hval x hR, Spec.lnAbsBarnesG_coe] at hB ⊢
      obtain ⟨F, hF⟩ := lnAbsBarnesGKind_complete (hA x hR) (hk x hR) p mode
        (fun t ht => hB t (by rw [ht]))
      exact ⟨F, fun fuel hfuel => by rw [hf fuel x p mode hR]; exact hF fuel hfuel⟩
    · exact ⟨0, fun fuel _ => hnon fuel x p mode hR⟩
  · by_cases hR : R x
    · obtain ⟨j, hj, hj3⟩ := hx hR
      rw [hval x hR, Spec.lnAbsBarnesG_coe, hj, Option.some.injEq] at hv
      rcases le_or_gt j 0 with h0 | h0
      · rw [barnesGR_int_nonpos h0, Spec.lnAbsE_zero] at hv
        exact absurd hv (by simp)
      · rw [barnesGR_int_small (by omega) hj3, Spec.lnAbsE_coe one_ne_zero, abs_one,
          Real.log_one, EReal.coe_eq_coe_iff] at hv
        rw [← hv]
        exact isDyadic_zero
    · exact absurd hv (hnonv x hR v)
  · obtain ⟨hR, j, hj, h4, -⟩ := hx
    have hirr := irrational_log_barnesGR_int h4
    have hpos : 0 < barnesGR (j : ℝ) := by
      rw [barnesGR_int_pos (by omega)]
      exact_mod_cast one_le_prod_factorial j.toNat
    refine ⟨_, ?_, not_isDyadic_of_irrational hirr⟩
    rw [hval x hR, Spec.lnAbsBarnesG_coe, hj, Spec.lnAbsE_coe hpos.ne', abs_of_pos hpos]
  · by_cases hR : R x
    · rcases hx with hD | hN
      · obtain ⟨j, hj, hj3⟩ := hD hR
        exact hexact x hR ⟨j, hj, by omega⟩ fuel p mode
      · obtain ⟨-, j, hj, -, h64⟩ := hN
        exact hexact x hR ⟨j, hj, h64⟩ fuel p mode
    · exact hnon fuel x p mode hR

/-- **The specification of a function that is `ln G` on its real arguments**, exact
elsewhere. -/
theorem lnBarnesG_zivSpec_of {α : Type*} {val : α → Option EReal}
    {f : ℕ → α → ℕ → RoundingMode → AzFloat × Ordering} (R : α → Prop) (arg : α → BarnesIn)
    (kind : α → Option (Option ℕ)) (xr : α → ℝ) (hA : ∀ x, R x → BarnesArg (arg x) (xr x))
    (hk : ∀ x, R x → BarnesKindSpec (kind x) (xr x))
    (hval : ∀ x, R x → val x = Spec.lnBarnesG ((xr x : ℝ) : EReal))
    (hf : ∀ fuel x p mode, R x →
      f fuel x p mode = lnOfAbs (lnAbsBarnesGKind (arg x) (kind x) fuel p mode))
    (hnon : ∀ fuel x (p : ℕ) [NeZero p] mode, ¬ R x → f fuel x p mode = roundVal p mode (val x))
    (hnonv : ∀ x, ¬ R x → ∀ v : ℝ, val x ≠ some (v : EReal)) :
    ZivSpec val f {x | R x → ∃ j : ℤ, xr x = j ∧ j ≤ 3}
      {x | R x ∧ ∃ j : ℤ, xr x = j ∧ 4 ≤ j ∧ j ≤ 64} := by
  have hexact : ∀ x, R x → (∃ j : ℤ, xr x = j ∧ j ≤ 64) → ∀ fuel (p : ℕ) [NeZero p] mode,
      f fuel x p mode = roundVal p mode (val x) := by
    intro x hR hj fuel p _ mode
    rw [hf fuel x p mode hR, hval x hR, Spec.lnBarnesG_coe]
    have hkx := hk x hR
    cases hkk : kind x with
    | none => rw [hkk] at hkx; exact absurd hj hkx.2
    | some c =>
      rw [hkk] at hkx
      obtain ⟨h1, h2⟩ := lnAbsBarnesGKind_exact (A := arg x) hkx fuel p mode
      rw [h1, Spec.log_coe_of_nonneg h2]
      rfl
  refine ⟨fun fuel x p _ mode => ?_, fun x p _ mode hB => ?_, fun x hx v hv => ?_,
    fun x hx => ?_, fun x hx fuel p _ mode => ?_⟩
  · by_cases hR : R x
    · rw [hf fuel x p mode hR, hval x hR, Spec.lnBarnesG_coe]
      exact lnBarnesGKind_main (hA x hR) (hk x hR) fuel p mode
    · exact Or.inl (hnon fuel x p mode hR)
  · by_cases hR : R x
    · rw [hval x hR, Spec.lnBarnesG_coe] at hB ⊢
      obtain ⟨F, hF⟩ := lnBarnesGKind_complete (hA x hR) (hk x hR) p mode hB
      exact ⟨F, fun fuel hfuel => by rw [hf fuel x p mode hR]; exact hF fuel hfuel⟩
    · exact ⟨0, fun fuel _ => hnon fuel x p mode hR⟩
  · by_cases hR : R x
    · obtain ⟨j, hj, hj3⟩ := hx hR
      rw [hval x hR, Spec.lnBarnesG_coe, hj] at hv
      rcases le_or_gt j 0 with h0 | h0
      · rw [barnesGR_int_nonpos h0, EReal.coe_zero, Spec.log_zero] at hv
        exact absurd hv (by simp)
      · rw [barnesGR_int_small (by omega) hj3, Spec.log_coe 1 one_pos, Real.log_one,
          Option.some.injEq, EReal.coe_eq_coe_iff] at hv
        rw [← hv]
        exact isDyadic_zero
    · exact absurd hv (hnonv x hR v)
  · obtain ⟨hR, j, hj, h4, -⟩ := hx
    have hirr := irrational_log_barnesGR_int h4
    have hpos : 0 < barnesGR (j : ℝ) := by
      rw [barnesGR_int_pos (by omega)]
      exact_mod_cast one_le_prod_factorial j.toNat
    refine ⟨_, ?_, not_isDyadic_of_irrational hirr⟩
    rw [hval x hR, Spec.lnBarnesG_coe, hj, Spec.log_coe _ hpos]
  · by_cases hR : R x
    · rcases hx with hD | hN
      · obtain ⟨j, hj, hj3⟩ := hD hR
        exact hexact x hR ⟨j, hj, by omega⟩ fuel p mode
      · obtain ⟨-, j, hj, -, h64⟩ := hN
        exact hexact x hR ⟨j, hj, h64⟩ fuel p mode
    · exact hnon fuel x p mode hR

/-! ### Rationals -/

/-- **The specification of `ln |G|` for a rational** (the value component). -/
theorem lnAbsBarnesGRatPrecRoundFuel_zivSpec :
    ZivSpec (fun q : AzRat => Spec.lnAbsBarnesG ((((AzRat.toRat q : ℚ) : ℝ) : ℝ) : EReal))
      (fun fuel q p mode => (lnAbsBarnesGRatPrecRoundFuel fuel q p mode).1)
      {q | ∃ j : ℤ, ((AzRat.toRat q : ℚ) : ℝ) = j ∧ j ≤ 3}
      {q | ∃ j : ℤ, ((AzRat.toRat q : ℚ) : ℝ) = j ∧ 4 ≤ j ∧ j ≤ 64} :=
  (lnAbsBarnesG_zivSpec_of (fun _ => True) barnesRatIn barnesRatKind
    (fun q => ((AzRat.toRat q : ℚ) : ℝ)) (fun q _ => barnesArg_rat q)
    (fun q _ => barnesRatKind_spec q) (fun _ _ => rfl) (fun _ _ _ _ _ => rfl)
    (fun _ _ _ _ _ h => absurd trivial h) (fun _ h => absurd trivial h)).mono
    (fun _ h _ => h) (fun _ h => ⟨trivial, h⟩)

/-- **The specification of `ln G` for a rational.** -/
theorem lnBarnesGRatPrecRoundFuel_zivSpec :
    ZivSpec (fun q : AzRat => Spec.lnBarnesG ((((AzRat.toRat q : ℚ) : ℝ) : ℝ) : EReal))
      (fun fuel q p mode => lnBarnesGRatPrecRoundFuel fuel q p mode)
      {q | ∃ j : ℤ, ((AzRat.toRat q : ℚ) : ℝ) = j ∧ j ≤ 3}
      {q | ∃ j : ℤ, ((AzRat.toRat q : ℚ) : ℝ) = j ∧ 4 ≤ j ∧ j ≤ 64} :=
  (lnBarnesG_zivSpec_of (fun _ => True) barnesRatIn barnesRatKind
    (fun q => ((AzRat.toRat q : ℚ) : ℝ)) (fun q _ => barnesArg_rat q)
    (fun q _ => barnesRatKind_spec q) (fun _ _ => rfl) (fun _ _ _ _ _ => rfl)
    (fun _ _ _ _ _ h => absurd trivial h) (fun _ h => absurd trivial h)).mono
    (fun _ h _ => h) (fun _ h => ⟨trivial, h⟩)

/-- **The sign component is the sign of `G(q)`** whenever the value is not `NaN`. -/
theorem lnAbsBarnesGRatPrecRoundFuel_sign (fuel : ℕ) (q : AzRat) (p : ℕ) [NeZero p]
    (mode : RoundingMode) (hne : (lnAbsBarnesGRatPrecRoundFuel fuel q p mode).1 ≠ (nan, .eq)) :
    (lnAbsBarnesGRatPrecRoundFuel fuel q p mode).2 = true
      ↔ 0 ≤ barnesGR ((AzRat.toRat q : ℚ) : ℝ) := by
  rcases lnAbsBarnesGKind_main (barnesArg_rat q) (barnesRatKind_spec q) fuel p mode with h | h
  · exact absurd h hne
  · exact h.2

/-! ### Floats -/

/-- The real value of a float, `0` when it has none. -/
noncomputable def floatReal (x : AzFloat) : ℝ := (x.toVal.getD 0).toReal

theorem floatReal_eq {x : AzFloat} {xv : ℝ} (hx : x.toVal = some (xv : EReal)) :
    floatReal x = xv := by
  unfold floatReal
  rw [hx, Option.getD_some, EReal.toReal_coe]

theorem lnAbsBarnesGPrecRoundFuel_eq_kind (fuel : ℕ) {x : AzFloat} {xv : ℝ}
    (hx : x.toVal = some (xv : EReal)) (p : ℕ) (mode : RoundingMode) :
    lnAbsBarnesGPrecRoundFuel fuel x p mode
      = lnAbsBarnesGKind (barnesIn x) (barnesKind x) fuel p mode := by
  cases x with
  | nan => simp at hx
  | infinity s => cases s <;> simp at hx
  | zero => rfl
  | finite s e q m hv => rfl

theorem exists_real_or_not (x : AzFloat) :
    (∃ xv : ℝ, x.toVal = some (xv : EReal)) ∨
      x = nan ∨ x = infinity true ∨ x = infinity false := by
  cases x with
  | nan => exact Or.inr (Or.inl rfl)
  | infinity s => cases s <;> simp
  | zero => exact Or.inl ⟨0, toVal_zero'⟩
  | finite s e q m hv => exact Or.inl ⟨_, toVal_finite s e q m hv⟩

/-- **The specification of `ln |G|`** (the value component; `ZivSpec`): sound at every fuel,
complete in the limit of the fuel wherever the value is no rounding boundary, and correct at
every fuel off the finite arguments and at the integers up to `64`. -/
theorem lnAbsBarnesGPrecRoundFuel_zivSpec :
    ZivSpec (fun x : AzFloat => x.toVal.bind Spec.lnAbsBarnesG)
      (fun fuel x p mode => (lnAbsBarnesGPrecRoundFuel fuel x p mode).1)
      {x | (∃ xv : ℝ, x.toVal = some (xv : EReal)) → ∃ j : ℤ, floatReal x = j ∧ j ≤ 3}
      {x | (∃ xv : ℝ, x.toVal = some (xv : EReal)) ∧
        ∃ j : ℤ, floatReal x = j ∧ 4 ≤ j ∧ j ≤ 64} :=
  lnAbsBarnesG_zivSpec_of (fun x => ∃ xv : ℝ, x.toVal = some (xv : EReal)) barnesIn barnesKind
    floatReal
    (fun x ⟨xv, hx⟩ => by rw [floatReal_eq hx]; exact barnesArg_float hx)
    (fun x ⟨xv, hx⟩ => by rw [floatReal_eq hx]; exact barnesKind_spec hx)
    (fun x ⟨xv, hx⟩ => by rw [floatReal_eq hx, hx, Option.bind_some])
    (fun fuel x p mode ⟨xv, hx⟩ => by rw [lnAbsBarnesGPrecRoundFuel_eq_kind fuel hx])
    (fun fuel x p _ mode hR => by
      rcases exists_real_or_not x with h | rfl | rfl | rfl
      · exact absurd h hR
      · rfl
      · simp [lnAbsBarnesGPrecRoundFuel, Spec.lnAbsBarnesG, Spec.barnesG, Spec.lnAbsE_top]
      · simp [lnAbsBarnesGPrecRoundFuel, Spec.lnAbsBarnesG, Spec.barnesG])
    (fun x hR v hv => by
      rcases exists_real_or_not x with h | rfl | rfl | rfl
      · exact hR h
      · simp at hv
      · simp [Spec.lnAbsBarnesG, Spec.barnesG, Spec.lnAbsE_top] at hv
      · simp [Spec.lnAbsBarnesG, Spec.barnesG] at hv)

/-- **The specification of `ln G`** (`ZivSpec`). -/
theorem lnBarnesGPrecRoundFuel_zivSpec :
    ZivSpec (fun x : AzFloat => x.toVal.bind Spec.lnBarnesG)
      (fun fuel x p mode => lnBarnesGPrecRoundFuel fuel x p mode)
      {x | (∃ xv : ℝ, x.toVal = some (xv : EReal)) → ∃ j : ℤ, floatReal x = j ∧ j ≤ 3}
      {x | (∃ xv : ℝ, x.toVal = some (xv : EReal)) ∧
        ∃ j : ℤ, floatReal x = j ∧ 4 ≤ j ∧ j ≤ 64} :=
  lnBarnesG_zivSpec_of (fun x => ∃ xv : ℝ, x.toVal = some (xv : EReal)) barnesIn barnesKind
    floatReal
    (fun x ⟨xv, hx⟩ => by rw [floatReal_eq hx]; exact barnesArg_float hx)
    (fun x ⟨xv, hx⟩ => by rw [floatReal_eq hx]; exact barnesKind_spec hx)
    (fun x ⟨xv, hx⟩ => by rw [floatReal_eq hx, hx, Option.bind_some])
    (fun fuel x p mode ⟨xv, hx⟩ => by
      show lnBarnesGPrecRoundFuel fuel x p mode = _
      unfold lnBarnesGPrecRoundFuel
      rw [lnAbsBarnesGPrecRoundFuel_eq_kind fuel hx]
      rfl)
    (fun fuel x p _ mode hR => by
      rcases exists_real_or_not x with h | rfl | rfl | rfl
      · exact absurd h hR
      · rfl
      · simp [lnBarnesGPrecRoundFuel, lnAbsBarnesGPrecRoundFuel, Spec.lnBarnesG, Spec.barnesG]
      · simp [lnBarnesGPrecRoundFuel, lnAbsBarnesGPrecRoundFuel, Spec.lnBarnesG, Spec.barnesG])
    (fun x hR v hv => by
      rcases exists_real_or_not x with h | rfl | rfl | rfl
      · exact hR h
      · simp at hv
      · simp [Spec.lnBarnesG, Spec.barnesG] at hv
      · simp [Spec.lnBarnesG, Spec.barnesG] at hv)

/-- **The sign component is the sign of `G(x)`** whenever the value is not `NaN`. -/
theorem lnAbsBarnesGPrecRoundFuel_sign (fuel : ℕ) {x : AzFloat} {xv : ℝ}
    (hx : x.toVal = some (xv : EReal)) (p : ℕ) [NeZero p] (mode : RoundingMode)
    (hne : (lnAbsBarnesGPrecRoundFuel fuel x p mode).1 ≠ (nan, .eq)) :
    (lnAbsBarnesGPrecRoundFuel fuel x p mode).2 = true ↔ 0 ≤ barnesGR xv := by
  rw [lnAbsBarnesGPrecRoundFuel_eq_kind fuel hx] at hne ⊢
  rcases lnAbsBarnesGKind_main (barnesArg_float hx) (barnesKind_spec hx) fuel p mode with h | h
  · exact absurd h hne
  · exact h.2

end Azurite.AzFloat
