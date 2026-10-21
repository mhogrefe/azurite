/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Float64Emulate
import Azurite.AzFloat.Equiv.Float64
import Azurite.AzNat.Equiv.ShiftRightNearestTernary

/-!
# Correctness of the `Float` emulation

`roundBinary64 v` is IEEE 754 round-to-nearest-ties-to-even to binary64, as a value: below
`2^-1022` the nearest multiple of `2^-1074`, otherwise the nearest 53-bit value, with `±∞` at
or beyond `±2^1024`.  The main theorem `toVal_emulateFinish_roundVal` says that `emulateFinish`
applied to the 53-bit nearest rounding of a real `v` together with its ternary (that is, to
`roundVal 53 .Nearest (some v)`, the specification of every `AzFloat` operation) produces a
`Float` whose value is `roundBinary64 v`.  Since every proven `fPrecRound` equals a `roundVal`,
every emulated `Float` function is correctly rounded (`toVal_sumFloat64` in `Equiv/Sum`, say).

The proof has two halves.  In the normal range the 53-bit value is already representable, so the
packed value is the 53-bit rounding itself; above `2^1024` it overflows to an infinity.  Below
the normal range the integer shift resolved by the ternary is a nearest integer to
`x / 2^-1074` with ties broken by the side of the exact value (`NearestTernary`), and
`toInt_round_nearest_of_ternary` shows that this is the nearest integer to the exact
`v / 2^-1074`: the 53-bit grid is finer than the subnormal grid and contains its midpoints, so
the 53-bit rounding is at least as close to `v` as any subnormal or any subnormal midpoint.
-/

namespace Azurite.AzFloat

open Float.Model (UnpackedFloat)
open Float.Model.UnpackedFloat (Sign)
open RoundingTarget

/-! ### The specification -/

/-- The 53-bit nearest rounding of a real, as a real. -/
noncomputable def roundNearest53 (v : ℝ) : ℝ :=
  ((round (precisionSet 2 53) .Nearest v).val).toReal

theorem coe_roundNearest53 (v : ℝ) :
    ((roundNearest53 v : ℝ) : EReal) = (round (precisionSet 2 53) .Nearest v).val := by
  obtain ⟨r, hr⟩ := precisionSet_exists_real (round (precisionSet 2 53) .Nearest v)
  unfold roundNearest53
  rw [← hr, EReal.toReal_coe]

/-- IEEE 754 round-to-nearest-ties-to-even to binary64, as a value in `EReal`: below `2^-1022`
the nearest multiple of `2^-1074` (ties to even), otherwise the nearest 53-bit value, becoming
`±∞` when that is at or beyond `±2^1024`. -/
noncomputable def roundBinary64 (v : ℝ) : EReal :=
  if |v| < (2 : ℝ) ^ (-1022 : ℤ) then
    (((toInt (round intSet .Nearest (v * (2 : ℝ) ^ (1074 : ℤ))) : ℝ)
      * (2 : ℝ) ^ (-1074 : ℤ) : ℝ) : EReal)
  else if (2 : ℝ) ^ (1024 : ℤ) ≤ roundNearest53 v then ⊤
  else if roundNearest53 v ≤ -(2 : ℝ) ^ (1024 : ℤ) then ⊥
  else ((roundNearest53 v : ℝ) : EReal)

/-! ### Integers and `NearestTernary` -/

theorem nearestTernary_intCast (R : ℤ) (o : Ordering) : NearestTernary (R : ℝ) R o := by
  unfold NearestTernary
  refine ⟨by rw [sub_self, abs_zero]; norm_num, fun h => ?_⟩
  rw [sub_self, abs_zero] at h
  norm_num at h

theorem eq_of_nearestTernary_intCast {n R : ℤ} {o : Ordering}
    (h : NearestTernary (n : ℝ) R o) : R = n := by
  have h1 := h.1
  have : |((n - R : ℤ) : ℝ)| ≤ 1 / 2 := by push_cast; exact h1
  have h2 : |n - R| ≤ 0 := by
    have : (|n - R| : ℤ) < 1 := by
      have : ((|n - R| : ℤ) : ℝ) < 1 := by rw [Int.cast_abs]; linarith
      exact_mod_cast this
    omega
  have := abs_nonpos_iff.mp h2
  omega

/-! ### The shift step -/

/-- The shift step of `toUnpackedTernary`: a nearest integer to `±n · 2^k` with ties resolved
by `o`. -/
theorem shift_ternary_spec (s : Bool) (n : AzNat) (hn : n ≠ 0) (k : AzInt) (o : Ordering) :
    NearestTernary ((if s then 1 else -1) * (n.toNat : ℝ) * (2 : ℝ) ^ k.toInt)
      (if k.sign then (AzInt.mkNorm s n).shiftLeft k.abs.toNat
        else AzInt.shiftRightNearestTernary (AzInt.mkNorm s n) o k.abs.toNat).toInt o := by
  have hz : ((AzInt.mkNorm s n).toInt : ℝ) = (if s then 1 else -1) * (n.toNat : ℝ) := by
    rcases Bool.eq_false_or_eq_true s with hs | hs <;>
      simp [hs, AzInt.toInt_mkNorm_true, AzInt.toInt_mkNorm_false n hn]
  have habs : (k.abs.toNat : ℤ) = |k.toInt| := AzInt.abs_toNat_eq k
  by_cases hsg : k.sign = true
  · have hk0 : 0 ≤ k.toInt := (AzInt.sign_eq_true_iff k).mp hsg
    rw [ite_eq_left hsg, AzInt.toInt_shiftLeft]
    have hk : ((k.abs.toNat : ℕ) : ℤ) = k.toInt := by rw [habs, abs_of_nonneg hk0]
    have : (if s then (1 : ℝ) else -1) * (n.toNat : ℝ) * (2 : ℝ) ^ k.toInt
        = (((AzInt.mkNorm s n).toInt * 2 ^ k.abs.toNat : ℤ) : ℝ) := by
      push_cast
      rw [hz, ← zpow_natCast, hk]
    rw [this]
    exact nearestTernary_intCast _ o
  · have hk0 : k.toInt < 0 := by
      have := (AzInt.sign_eq_true_iff k).not.mp hsg; push Not at this; exact this
    rw [ite_eq_right hsg]
    have h := AzInt.toInt_shiftRightNearestTernary (AzInt.mkNorm s n) o k.abs.toNat
    have hk : ((k.abs.toNat : ℕ) : ℤ) = -k.toInt := by rw [habs, abs_of_neg hk0]
    have heq : ((AzInt.mkNorm s n).toInt : ℝ) / (2 : ℝ) ^ k.abs.toNat
        = (if s then 1 else -1) * (n.toNat : ℝ) * (2 : ℝ) ^ k.toInt := by
      rw [hz, ← zpow_natCast, hk, zpow_neg, div_eq_mul_inv, inv_inv]
    rw [heq] at h
    exact h

/-- The finite case of `toUnpackedTernary`, packaged like `toUnpacked_finite`. -/
theorem toUnpackedTernary_finite (s : Bool) (e : AzInt) {p : ℕ} {m : AzNat}
    (hv : FiniteValid p m) (o : Ordering) :
    ∃ r t : AzInt, toUnpackedTernary (finite s e p m hv) o = finishUnpacked s r t .Nearest ∧
      t.toInt = max (e.toInt - 53) (-1074) ∧
      NearestTernary (finiteVal s e m / (2 : ℝ) ^ t.toInt) r.toInt o ∧
      (r.toInt ≠ 0 → (0 < r.toInt ↔ s = true)) := by
  unfold toUnpackedTernary
  simp only []
  set n := coreSignificand p m with hn
  have hn0 : n ≠ 0 := coreSignificand_ne_zero hv
  have hs : n.size = p := size_coreSignificand hv
  clear_value n
  set t : AzInt := max (e - (AzNat.ofNat 53).toAzInt) (azIntOfInt (-1074)) with ht_def
  have htI : t.toInt = max (e.toInt - 53) (-1074) := by
    rw [ht_def, AzInt.toInt_max, AzInt.toInt_sub, toInt_toAzInt, AzNat.toNat_ofNat,
      toInt_azIntOfInt]
    push_cast
    rfl
  clear_value t
  set k : AzInt := e - (AzNat.ofNat p).toAzInt - t with hk_def
  have hkI : k.toInt = e.toInt - p - t.toInt := by
    rw [hk_def, AzInt.toInt_sub, AzInt.toInt_sub, toInt_toAzInt, AzNat.toNat_ofNat]
  clear_value k
  have hval : finiteVal s e m / (2 : ℝ) ^ t.toInt
      = (if s then 1 else -1) * (n.toNat : ℝ) * (2 : ℝ) ^ k.toInt := by
    rw [finiteVal_eq_core s e hv, ← hn, finiteVal_sign, finiteVal_true_eq, hs, hkI]
    simp only [zpow_sub₀ (two_ne_zero : (2 : ℝ) ≠ 0)]
    ring
  refine ⟨_, t, rfl, htI, ?_, ?_⟩
  · rw [hval]
    exact shift_ternary_spec s n hn0 k o
  · intro hr0
    have hnt := shift_ternary_spec s n hn0 k o
    set r := (if k.sign then (AzInt.mkNorm s n).shiftLeft k.abs.toNat
      else AzInt.shiftRightNearestTernary (AzInt.mkNorm s n) o k.abs.toNat) with hr
    clear_value r
    have hNpos : (0 : ℝ) < (n.toNat : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero (toNat_ne_zero_of_ne_zero hn0)
    have h2k : (0 : ℝ) < (2 : ℝ) ^ k.toInt := zpow_pos (by norm_num) _
    have h1 := hnt.1
    have hr0' : (r.toInt : ℝ) ≠ 0 := by exact_mod_cast hr0
    have hhalf : (1 : ℝ) ≤ |(r.toInt : ℝ)| := by
      have : (1 : ℤ) ≤ |r.toInt| := Int.one_le_abs hr0
      exact_mod_cast this
    cases s with
    | true =>
      simp only [↓reduceIte, one_mul, iff_true] at h1 ⊢
      have hy : 0 < (n.toNat : ℝ) * (2 : ℝ) ^ k.toInt := mul_pos hNpos h2k
      by_contra hneg
      push Not at hneg
      have : (r.toInt : ℝ) ≤ -1 := by
        have : r.toInt ≤ -1 := by omega
        exact_mod_cast this
      have := abs_le.mp h1
      linarith [this.1, this.2]
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte, neg_one_mul, iff_false, not_lt] at h1 ⊢
      have hy : (n.toNat : ℝ) * (2 : ℝ) ^ k.toInt > 0 := mul_pos hNpos h2k
      by_contra hpos
      push Not at hpos
      have : (1 : ℝ) ≤ (r.toInt : ℝ) := by exact_mod_cast hpos
      have := abs_le.mp h1
      linarith [this.1, this.2]

/-! ### Overflow -/

/-- `finishUnpacked` in `Nearest` mode on an exponent beyond `971` is the infinity of sign
`s`. -/
theorem toVal_finishUnpacked_overflow (s : Bool) (r t : AzInt) (hr : r.abs ≠ 0)
    (ht : 971 < t.toInt) :
    (finishUnpacked s r t .Nearest).toVal = some (if s then ⊤ else ⊥) := by
  unfold finishUnpacked
  simp only []
  rw [ite_eq_right hr]
  have h1 : (1 : AzInt).toInt = 1 := rfl
  have hov : ∀ t' : AzInt, 971 < t'.toInt → azIntOfInt 971 < t' := fun t' h => by
    rw [AzInt.lt_iff_toInt_lt, toInt_azIntOfInt]; exact h
  have hsgn : (if signOfBool s = Sign.positive then (⊤ : EReal) else ⊥)
      = if s then ⊤ else ⊥ := by
    cases s <;> simp [signOfBool]
  by_cases hc : r.abs.size = 54
  · rw [ite_eq_left hc, ite_eq_left (hov _ (by rw [AzInt.toInt_add, h1]; omega))]
    simp only [overflowToInfinity, ↓reduceIte, UnpackedFloat.toVal, hsgn]
  · rw [ite_eq_right hc, ite_eq_left (hov _ ht)]
    simp only [overflowToInfinity, ↓reduceIte, UnpackedFloat.toVal, hsgn]

/-! ### Representability -/

/-- Every result of `toUnpackedTernary` is representable in binary64. -/
theorem toUnpackedTernary_binary64 (x : AzFloat) (o : Ordering) :
    (toUnpackedTernary x o).Binary64 := by
  cases x with
  | nan => trivial
  | infinity s => trivial
  | zero => trivial
  | finite s e p m hv =>
    obtain ⟨r, t, hx, htI, hr, -⟩ := toUnpackedTernary_finite s e hv o
    rw [hx]
    have hv0 : finiteVal s e m ≠ 0 := by
      rw [finiteVal_eq_core s e hv]
      exact finiteVal_ne_zero' s e _ (coreSignificand_ne_zero hv)
    obtain ⟨hvlo, hvhi⟩ := abs_finiteVal_bounds s e hv
    have habs : (r.abs.toNat : ℤ) = |r.toInt| := AzInt.abs_toNat_eq r
    have h2t : (0 : ℝ) < (2 : ℝ) ^ t.toInt := zpow_pos (by norm_num) _
    have hclose := hr.1
    rcases le_or_gt (-1021 : ℤ) e.toInt with hlo | hhi
    · -- normal range: `|x / 2^t| ∈ [2^52, 2^53)`, and the nearest integer is within `1/2`
      have ht : t.toInt = e.toInt - 53 := by rw [htI]; exact max_eq_left (by omega)
      have hX : |finiteVal s e m / (2 : ℝ) ^ t.toInt| < (2 : ℝ) ^ (53 : ℤ) ∧
          (2 : ℝ) ^ (52 : ℤ) ≤ |finiteVal s e m / (2 : ℝ) ^ t.toInt| := by
        rw [abs_div, abs_of_pos h2t, div_lt_iff₀ h2t, le_div_iff₀ h2t, ht,
          ← zpow_add₀ (two_ne_zero : (2 : ℝ) ≠ 0),
          ← zpow_add₀ (two_ne_zero : (2 : ℝ) ≠ 0)]
        constructor
        · convert hvhi using 2; ring
        · convert hvlo using 2; ring
      have hRlo : (2 : ℝ) ^ (52 : ℤ) - 1 / 2 ≤ |(r.toInt : ℝ)| := by
        have := abs_sub_abs_le_abs_sub (finiteVal s e m / (2 : ℝ) ^ t.toInt) (r.toInt : ℝ)
        linarith [hX.2]
      have hRhi : |(r.toInt : ℝ)| ≤ (2 : ℝ) ^ (53 : ℤ) + 1 / 2 := by
        have := abs_sub_abs_le_abs_sub (r.toInt : ℝ) (finiteVal s e m / (2 : ℝ) ^ t.toInt)
        rw [abs_sub_comm] at this
        linarith [hX.1]
      have hr53 : |r.toInt| ≤ 2 ^ 53 := by
        have : ((|r.toInt| : ℤ) : ℝ) < 2 ^ 53 + 1 := by
          rw [Int.cast_abs]; norm_num at hRhi ⊢; linarith
        have : (|r.toInt| : ℤ) < 2 ^ 53 + 1 := by exact_mod_cast this
        omega
      have hr52 : 2 ^ 52 ≤ |r.toInt| := by
        have : (2 ^ 52 - 1 : ℝ) < ((|r.toInt| : ℤ) : ℝ) := by
          rw [Int.cast_abs]; norm_num at hRlo ⊢; linarith
        have : (2 ^ 52 - 1 : ℤ) < |r.toInt| := by exact_mod_cast this
        omega
      apply finishUnpacked_binary64 s r t .Nearest
      · have : (r.abs.toNat : ℤ) ≤ ((2 ^ 53 : ℕ) : ℤ) := by rw [habs]; exact_mod_cast hr53
        exact_mod_cast this
      · omega
      · intro hlt
        exfalso
        have : ((2 ^ 52 : ℕ) : ℤ) ≤ (r.abs.toNat : ℤ) := by rw [habs]; exact_mod_cast hr52
        have : (2 ^ 52 : ℕ) ≤ r.abs.toNat := by exact_mod_cast this
        omega
    · -- subnormal range: `|x / 2^t| < 2^52`
      have ht : t.toInt = -1074 := by rw [htI]; exact max_eq_right (by omega)
      have hsmall : |finiteVal s e m / (2 : ℝ) ^ t.toInt| ≤ (2 : ℝ) ^ (52 : ℤ) := by
        apply le_of_lt
        rw [abs_div, abs_of_pos h2t, div_lt_iff₀ h2t, ht]
        calc |finiteVal s e m| < (2 : ℝ) ^ e.toInt := hvhi
          _ ≤ (2 : ℝ) ^ (-1022 : ℤ) := zpow_le_zpow_right₀ (by norm_num) (by omega)
          _ = (2 : ℝ) ^ (52 : ℤ) * (2 : ℝ) ^ (-1074 : ℤ) := by
            rw [← zpow_add₀ (two_ne_zero : (2 : ℝ) ≠ 0)]; norm_num
      have hRhi : |(r.toInt : ℝ)| ≤ (2 : ℝ) ^ (52 : ℤ) + 1 / 2 := by
        have := abs_sub_abs_le_abs_sub (r.toInt : ℝ) (finiteVal s e m / (2 : ℝ) ^ t.toInt)
        rw [abs_sub_comm] at this
        linarith
      have hr52 : |r.toInt| ≤ 2 ^ 52 := by
        have : ((|r.toInt| : ℤ) : ℝ) < 2 ^ 52 + 1 := by
          rw [Int.cast_abs]; norm_num at hRhi ⊢; linarith
        have : (|r.toInt| : ℤ) < 2 ^ 52 + 1 := by exact_mod_cast this
        omega
      have hr52' : r.abs.toNat ≤ 2 ^ 52 := by
        have : (r.abs.toNat : ℤ) ≤ 2 ^ 52 := by rw [habs]; exact hr52
        exact_mod_cast this
      exact finishUnpacked_binary64 s r t .Nearest (by omega) (by omega) (fun _ => ht)

/-! ### The main theorem -/

theorem compare_mul_pos_right (a b c : ℝ) (hc : 0 < c) :
    compare (a * c) (b * c) = compare a b := by
  rcases lt_trichotomy a b with h | h | h
  · rw [compare_lt_iff_lt.mpr h, compare_lt_iff_lt.mpr (mul_lt_mul_of_pos_right h hc)]
  · subst h; rw [compare_eq_iff_eq.mpr rfl, compare_eq_iff_eq.mpr rfl]
  · rw [compare_gt_iff_gt.mpr h, compare_gt_iff_gt.mpr (mul_lt_mul_of_pos_right h hc)]

theorem finiteVal_ne_zero_of_valid (s : Bool) (e : AzInt) {p : ℕ} {m : AzNat}
    (hv : FiniteValid p m) : finiteVal s e m ≠ 0 := by
  rw [finiteVal_eq_core s e hv]
  exact finiteVal_ne_zero' s e _ (coreSignificand_ne_zero hv)

/-- `toUnpackedTernary` on the 53-bit nearest rounding of a real `v` with its ternary is the
binary64 rounding of `v`. -/
theorem toVal_toUnpackedTernary_roundVal (v : ℝ) :
    (toUnpackedTernary (roundVal 53 .Nearest (some (v : EReal))).1
        (roundVal 53 .Nearest (some (v : EReal))).2).toVal = some (roundBinary64 v) := by
  obtain ⟨hx, ho⟩ := roundVal_coe 53 .Nearest v
  have hprec : (roundVal 53 .Nearest (some (v : EReal))).1.precision? = some 53 ∨
      (roundVal 53 .Nearest (some (v : EReal))).1.precision? = none :=
    (ofEReal_spec 53 .Nearest v).1
  set x := (roundVal 53 .Nearest (some (v : EReal))).1 with hx_def
  set o := (roundVal 53 .Nearest (some (v : EReal))).2 with ho_def
  rw [val_round_floatSet, ← coe_roundNearest53] at hx ho
  clear_value x o
  have h2 : (0 : ℝ) < 2 := by norm_num
  rcases eq_or_ne v 0 with hv0 | hv0
  · -- an exact zero
    subst hv0
    have h0 : roundNearest53 0 = 0 := by
      have : ((roundNearest53 0 : ℝ) : EReal) = ((0 : ℝ) : EReal) := by
        rw [coe_roundNearest53, val_round_of_mem _ _ (Or.inl (by simp))]
      exact EReal.coe_eq_coe_iff.mp this
    rw [h0] at hx
    have hR : roundBinary64 0 = 0 := by
      unfold roundBinary64
      rw [ite_eq_left (by rw [abs_zero]; exact zpow_pos h2 _), zero_mul,
        show (0 : ℝ) = ((0 : ℤ) : ℝ) from Int.cast_zero.symm, toInt_round_intCast]
      simp
    rw [hR]
    cases x with
    | nan => simp at hx
    | infinity s => cases s <;> simp at hx
    | zero => rfl
    | finite s e p m hv =>
      exfalso
      simp only [toVal_finite, Option.some.injEq, EReal.coe_eq_coe_iff] at hx
      exact finiteVal_ne_zero_of_valid s e hv hx
  -- the 53-bit rounding as an integer times the scale
  set σ := precScale 2 53 v with hσ_def
  have hσ : (0 : ℝ) < σ := zpow_pos (by norm_num) _
  set y := v / σ with hy
  set R := toInt (round intSet .Nearest y) with hR
  have hRσ : roundNearest53 v = (R : ℝ) * σ := by
    have := coe_roundNearest53 v
    rw [val_round_precisionSet .Nearest v hv0] at this
    exact EReal.coe_eq_coe_iff.mp this
  obtain ⟨hylo, hyhi⟩ := abs_div_precScale_bounds (b := 2) (p := 53) v hv0
  obtain ⟨hRlo, hRhi⟩ := abs_toInt_round_bounds 53 (by norm_num) .Nearest y
    (by simpa using hylo) (by simpa using hyhi)
  rw [← hR] at hRlo hRhi
  norm_num at hRlo hRhi
  have hR0 : R ≠ 0 := by intro h; rw [h, abs_zero] at hRlo; omega
  have hvy : v = y * σ := by rw [hy, div_mul_cancel₀ _ hσ.ne']
  set L := Int.log 2 |v| with hL
  have hσL : σ = (2 : ℝ) ^ (L - 52) := by
    rw [hσ_def]; unfold precScale; push_cast; congr 1; ring
  -- the float is finite of precision 53 with value `R · σ`
  rw [hRσ] at hx ho
  cases x with
  | nan => simp at hx
  | infinity s =>
    exfalso
    simp only [toVal_infinity, Option.some.injEq] at hx
    cases s
    · simp only [Bool.false_eq_true, ↓reduceIte] at hx; exact EReal.bot_ne_coe _ hx
    · simp only [↓reduceIte] at hx; exact EReal.top_ne_coe _ hx
  | zero =>
    exfalso
    simp only [toVal_zero, Option.some.injEq] at hx
    have : (R : ℝ) * σ = 0 := EReal.coe_eq_coe_iff.mp (by rw [EReal.coe_zero]; exact hx.symm)
    rcases mul_eq_zero.mp this with h | h
    · exact hR0 (by exact_mod_cast h)
    · exact hσ.ne' h
  | finite s e p m hv =>
  simp only [toVal_finite, Option.some.injEq, EReal.coe_eq_coe_iff] at hx
  have hp : p = 53 := by
    rcases hprec with h | h
    · exact Option.some.inj h
    · simp [precision?] at h
  subst hp
  rw [compare_coe_coe] at ho
  obtain ⟨r, t, hu, htI, hNT, hsign⟩ := toUnpackedTernary_finite s e hv o
  rw [hu]
  obtain ⟨hvlo, hvhi⟩ := abs_finiteVal_bounds s e hv
  rw [hx] at hvlo hvhi hNT
  have habs : (r.abs.toNat : ℤ) = |r.toInt| := AzInt.abs_toNat_eq r
  have hRσabs : |(R : ℝ) * σ| = |(R : ℝ)| * σ := by rw [abs_mul, abs_of_pos hσ]
  have hRabs : (2 : ℝ) ^ (52 : ℤ) ≤ |(R : ℝ)| ∧
      |(R : ℝ)| ≤ (2 : ℝ) ^ (53 : ℤ) := by
    constructor
    · have : ((2 ^ 52 : ℤ) : ℝ) ≤ ((|R| : ℤ) : ℝ) := by exact_mod_cast hRlo
      rw [Int.cast_abs] at this; norm_num at this ⊢; exact this
    · have : ((|R| : ℤ) : ℝ) ≤ ((2 ^ 53 : ℤ) : ℝ) := by exact_mod_cast hRhi
      rw [Int.cast_abs] at this; norm_num at this ⊢; exact this
  by_cases hsmall : |v| < (2 : ℝ) ^ (-1022 : ℤ)
  · -- subnormal range
    have hLlt : L < -1022 :=
      (Int.lt_zpow_iff_log_lt (by norm_num) (abs_pos.mpr hv0)).mp (by simpa using hsmall)
    have hσle : σ ≤ (2 : ℝ) ^ (-1075 : ℤ) := by
      rw [hσL]; exact zpow_le_zpow_right₀ (by norm_num) (by omega)
    have hfv : |(R : ℝ) * σ| ≤ (2 : ℝ) ^ (-1022 : ℤ) := by
      rw [hRσabs]
      calc |(R : ℝ)| * σ ≤ (2 : ℝ) ^ (53 : ℤ) * (2 : ℝ) ^ (-1075 : ℤ) :=
            mul_le_mul hRabs.2 hσle hσ.le (by positivity)
        _ = (2 : ℝ) ^ (-1022 : ℤ) := by
            rw [← zpow_add₀ (two_ne_zero : (2 : ℝ) ≠ 0)]; norm_num
    have he : e.toInt ≤ -1021 := by
      have : (2 : ℝ) ^ (e.toInt - 1) ≤ (2 : ℝ) ^ (-1022 : ℤ) := hvlo.trans hfv
      have := (zpow_le_zpow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).mp this
      omega
    have ht : t.toInt = -1074 := by rw [htI]; exact max_eq_right (by omega)
    -- the scaled quantities
    set X := (R : ℝ) * σ / (2 : ℝ) ^ t.toInt with hX
    set w := v * (2 : ℝ) ^ (1074 : ℤ) with hw
    have h2t : (2 : ℝ) ^ t.toInt = ((2 : ℝ) ^ (1074 : ℤ))⁻¹ := by
      rw [ht, zpow_neg]
    have hXw : X = (R : ℝ) * σ * (2 : ℝ) ^ (1074 : ℤ) := by rw [hX, h2t, div_inv_eq_mul]
    have hc : (0 : ℝ) < σ * (2 : ℝ) ^ (1074 : ℤ) := by positivity
    have hcmp : compare X w = o := by
      rw [ho, hXw, hw, compare_mul_pos_right _ _ _ (zpow_pos h2 _)]
    -- the grid: `2^-1075 = σ · 2^J`
    set J : ℕ := (-1023 - L).toNat with hJ
    have hJ' : (J : ℤ) = -1023 - L := by rw [hJ]; exact Int.toNat_of_nonneg (by omega)
    have hgrid : (2 : ℝ) ^ (-1075 : ℤ) = σ * (2 : ℝ) ^ J := by
      rw [hσL, ← zpow_natCast, ← zpow_add₀ (two_ne_zero : (2 : ℝ) ≠ 0), hJ']
      congr 1; ring
    -- the 53-bit rounding is at least as close to `v` as any half-integer multiple of `2^-1074`
    have key : ∀ n : ℤ, |X - w| ≤ |(n : ℝ) / 2 - w| := by
      intro n
      have h1 : X - w = (R - y) * (σ * (2 : ℝ) ^ (1074 : ℤ)) := by
        rw [hXw, hw, hvy]; ring
      have h2' : (n : ℝ) / 2 - w = ((n * 2 ^ J : ℤ) - y) * (σ * (2 : ℝ) ^ (1074 : ℤ)) := by
        have hpow : (2 : ℝ) ^ (-1075 : ℤ) * (2 : ℝ) ^ (1074 : ℤ) = 2⁻¹ := by
          rw [← zpow_add₀ (two_ne_zero : (2 : ℝ) ≠ 0)]; norm_num
        rw [show (n : ℝ) / 2 = n * ((2 : ℝ) ^ (-1075 : ℤ) * (2 : ℝ) ^ (1074 : ℤ)) by
          rw [hpow]; ring, hgrid, hw, hvy]
        push_cast; ring
      rw [h1, h2', abs_mul ((R : ℝ) - y), abs_mul (((n * 2 ^ J : ℤ) : ℝ) - y), abs_of_pos hc]
      apply mul_le_mul_of_nonneg_right _ hc.le
      rw [abs_sub_comm, abs_sub_comm ((n * 2 ^ J : ℤ) : ℝ)]
      exact abs_toInt_round_nearest_sub_le y _
    have hB : |w| < ((2 ^ 52 : ℤ) : ℝ) := by
      rw [hw, abs_mul, abs_of_pos (zpow_pos h2 _)]
      calc |v| * (2 : ℝ) ^ (1074 : ℤ) < (2 : ℝ) ^ (-1022 : ℤ) * (2 : ℝ) ^ (1074 : ℤ) :=
            mul_lt_mul_of_pos_right hsmall (zpow_pos h2 _)
        _ = ((2 ^ 52 : ℤ) : ℝ) := by
            rw [← zpow_add₀ (two_ne_zero : (2 : ℝ) ≠ 0)]; norm_num
    have hclose : ∀ m : ℤ, |m| ≤ 2 ^ 52 → |X - w| ≤ |(m : ℝ) - w| := by
      intro m _
      have := key (2 * m)
      push_cast at this
      rwa [mul_div_cancel_left₀ _ (two_ne_zero : (2 : ℝ) ≠ 0)] at this
    have hclose' : ∀ m : ℤ, -(2 ^ 52) ≤ m → m ≤ 2 ^ 52 - 1 →
        |X - w| ≤ |(m : ℝ) + 1 / 2 - w| := by
      intro m _ _
      have := key (2 * m + 1)
      push_cast at this
      rwa [show ((2 : ℝ) * m + 1) / 2 = m + 1 / 2 by ring] at this
    have hround : toInt (round intSet .Nearest w) = r.toInt := by
      rw [← hcmp] at hNT
      exact toInt_round_nearest_of_ternary hB hclose hclose' hNT
    have hr52 : r.abs.toNat ≤ 2 ^ 52 := by
      have := abs_toInt_round_le .Nearest w (2 ^ 52) hB.le
      rw [hround] at this
      have : (r.abs.toNat : ℤ) ≤ 2 ^ 52 := by rw [habs]; exact this
      exact_mod_cast this
    rw [toVal_finishUnpacked s r t .Nearest (by omega) hsign (by rw [ht]; split_ifs <;> omega)]
    unfold roundBinary64
    rw [ite_eq_left hsmall, ← hw, hround, ht]
  · -- normal range
    push Not at hsmall
    have hLge : -1022 ≤ L :=
      (Int.zpow_le_iff_le_log (by norm_num) (abs_pos.mpr hv0)).mp (by simpa using hsmall)
    have hσge : (2 : ℝ) ^ (-1074 : ℤ) ≤ σ := by
      rw [hσL]; exact zpow_le_zpow_right₀ (by norm_num) (by omega)
    have hfv : (2 : ℝ) ^ (-1022 : ℤ) ≤ |(R : ℝ) * σ| := by
      rw [hRσabs]
      calc (2 : ℝ) ^ (-1022 : ℤ) = (2 : ℝ) ^ (52 : ℤ) * (2 : ℝ) ^ (-1074 : ℤ) := by
            rw [← zpow_add₀ (two_ne_zero : (2 : ℝ) ≠ 0)]; norm_num
        _ ≤ |(R : ℝ)| * σ := mul_le_mul hRabs.1 hσge (by positivity) (abs_nonneg _)
    have he : -1021 ≤ e.toInt := by
      have : (2 : ℝ) ^ (-1022 : ℤ) < (2 : ℝ) ^ e.toInt := hfv.trans_lt hvhi
      have := (zpow_lt_zpow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).mp this
      omega
    have ht : t.toInt = e.toInt - 53 := by rw [htI]; exact max_eq_left (by omega)
    -- the shifted value is the signed core significand, an integer below `2^53`
    set n := coreSignificand 53 m with hn
    have hn0 : n ≠ 0 := coreSignificand_ne_zero hv
    have hs : n.size = 53 := size_coreSignificand hv
    have hnlt : n.toNat < 2 ^ 53 := by rw [← Nat.size_le, AzNat.size_toNat, hs]
    set N : ℤ := if s then (n.toNat : ℤ) else -(n.toNat : ℤ) with hN
    have hNval : (R : ℝ) * σ / (2 : ℝ) ^ t.toInt = (N : ℝ) := by
      rw [← hx, finiteVal_eq_core s e hv, ← hn, finiteVal_sign, finiteVal_true_eq, hs, ht, hN]
      push_cast
      cases s <;> simp [div_eq_iff (zpow_pos h2 _).ne']
    rw [hNval] at hNT
    have hrN : r.toInt = N := eq_of_nearestTernary_intCast hNT
    have hNabs : |N| = (n.toNat : ℤ) := by rw [hN]; cases s <;> simp
    have hrabs : r.abs.toNat = n.toNat := by
      have : (r.abs.toNat : ℤ) = (n.toNat : ℤ) := by rw [habs, hrN, hNabs]
      exact_mod_cast this
    have hval : ((r.toInt : ℝ) * (2 : ℝ) ^ t.toInt : ℝ) = (R : ℝ) * σ := by
      rw [hrN, ← hNval, div_mul_cancel₀ _ (zpow_pos h2 _).ne']
    have hn0' : n.toNat ≠ 0 := toNat_ne_zero_of_ne_zero hn0
    have hsgn : (0 < (R : ℝ) * σ ↔ s = true) := by
      rw [← hx, finiteVal_sign]
      have := finiteVal_true_pos' e m (fun h => by
        obtain ⟨hlo, -⟩ := toNat_bounds_of_valid hv
        rw [h, AzNat.toNat_zero] at hlo
        exact absurd hlo (not_le.mpr (Nat.two_pow_pos _)))
      cases s <;> simp <;> linarith
    unfold roundBinary64
    rw [ite_eq_right (not_lt.mpr hsmall), hRσ]
    by_cases hov : 1025 ≤ e.toInt
    · -- overflow
      have hr0 : r.abs ≠ 0 := by
        intro h
        have := congrArg AzNat.toNat h
        rw [AzNat.toNat_zero, hrabs] at this
        exact hn0' this
      rw [toVal_finishUnpacked_overflow s r t hr0 (by omega)]
      have hbig : (2 : ℝ) ^ (1024 : ℤ) ≤ |(R : ℝ) * σ| :=
        (zpow_le_zpow_right₀ (by norm_num) (by omega : (1024 : ℤ) ≤ e.toInt - 1)).trans hvlo
      cases s with
      | true =>
        have hpos : 0 < (R : ℝ) * σ := hsgn.mpr rfl
        rw [abs_of_pos hpos] at hbig
        rw [ite_eq_left hbig]; rfl
      | false =>
        have hneg : (R : ℝ) * σ < 0 := by
          have := hsgn.not.mpr (by decide); push Not at this
          exact lt_of_le_of_ne this (fun h => by
            rcases mul_eq_zero.mp h with h | h
            · exact hR0 (by exact_mod_cast h)
            · exact hσ.ne' h)
        rw [abs_of_neg hneg] at hbig
        have h2p : (0 : ℝ) < (2 : ℝ) ^ (1024 : ℤ) := zpow_pos h2 _
        rw [ite_eq_right (not_le.mpr (hneg.trans h2p)), ite_eq_left (le_neg.mp hbig)]
        rfl
    · push Not at hov
      have hlt : |(R : ℝ) * σ| < (2 : ℝ) ^ (1024 : ℤ) :=
        hvhi.trans_le (zpow_le_zpow_right₀ (by norm_num) (by omega))
      have hno : t.toInt + (if r.abs.toNat = 2 ^ 53 then 1 else 0) ≤ 971 := by
        rw [ite_eq_right (by rw [hrabs]; omega), ht]; omega
      rw [toVal_finishUnpacked s r t .Nearest (by rw [hrabs]; omega) hsign hno, hval]
      obtain ⟨h1, h2'⟩ := abs_lt.mp hlt
      rw [ite_eq_right (not_le.mpr h2'), ite_eq_right (not_le.mpr h1)]

/-! ### Through `Float` -/

/-- Unpacking the packed result of `emulateFinish` gives `toUnpackedTernary` back. -/
theorem unpack_emulateFinish (r : AzFloat × Ordering) :
    (emulateFinish r).toModel.unpack = toUnpackedTernary r.1 r.2 := by
  unfold emulateFinish
  rw [show (Float.ofModel (Float.Model.pack (toUnpackedTernary r.1 r.2))).toModel
    = Float.Model.pack (toUnpackedTernary r.1 r.2) from rfl,
    model_unpack_pack _ (toUnpackedTernary_binary64 _ _)]

open Classical in
/-- `roundBinary64` on specification values: `NaN` and the infinities pass through. -/
noncomputable def roundBinary64Val : Option EReal → Option EReal
  | none => none
  | some e =>
    if e = ⊤ then some ⊤ else if e = ⊥ then some ⊥ else some (roundBinary64 e.toReal)

@[simp] theorem roundBinary64Val_none : roundBinary64Val none = none := rfl

theorem roundBinary64Val_coe (v : ℝ) :
    roundBinary64Val (some (v : EReal)) = some (roundBinary64 v) := by
  show (if (v : EReal) = ⊤ then some ⊤ else if (v : EReal) = ⊥ then some ⊥
    else some (roundBinary64 (v : EReal).toReal)) = _
  rw [ite_eq_right (EReal.coe_ne_top v), ite_eq_right (EReal.coe_ne_bot v), EReal.toReal_coe]

/-- **The main theorem.**  `emulateFinish` on the 53-bit nearest rounding of a specification
value with its ternary (which is what every proven `AzFloat` operation computes) is a `Float`
whose value is the binary64 rounding of that specification value. -/
theorem toVal_emulateFinish_roundVal (w : Option EReal) :
    (emulateFinish (roundVal 53 .Nearest w)).toModel.unpack.toVal = roundBinary64Val w := by
  rw [unpack_emulateFinish]
  cases w with
  | none => rfl
  | some e =>
    induction e using EReal.rec with
    | bot =>
      rw [roundVal_of_toVal 53 .Nearest (infinity false) ⊥ (Or.inr rfl) rfl]
      show (toUnpackedTernary (infinity false) .eq).toVal
        = (if (⊥ : EReal) = ⊤ then some ⊤ else if (⊥ : EReal) = ⊥ then some ⊥
          else some (roundBinary64 (⊥ : EReal).toReal))
      rw [ite_eq_right bot_ne_top, ite_eq_left rfl]
      simp [toUnpackedTernary, UnpackedFloat.toVal, signOfBool]
    | coe v => rw [roundBinary64Val_coe]; exact toVal_toUnpackedTernary_roundVal v
    | top =>
      rw [roundVal_of_toVal 53 .Nearest (infinity true) ⊤ (Or.inr rfl) rfl]
      show (toUnpackedTernary (infinity true) .eq).toVal
        = (if (⊤ : EReal) = ⊤ then some ⊤ else if (⊤ : EReal) = ⊥ then some ⊥
          else some (roundBinary64 (⊤ : EReal).toReal))
      rw [ite_eq_left rfl]
      simp [toUnpackedTernary, UnpackedFloat.toVal, signOfBool]

/-- A one-argument wrapper of an operation specified by `liftVal f` computes the binary64
rounding of `f` of the `Float`'s value. -/
theorem toVal_emulate (g : AzFloat → ℕ → RoundingMode → AzFloat × Ordering)
    (f : EReal → Option EReal) (hg : ∀ x, g x 53 .Nearest = liftVal f x 53 .Nearest)
    (x : Float) :
    (emulate g x).toModel.unpack.toVal = roundBinary64Val (x.toModel.unpack.toVal.bind f) := by
  unfold emulate
  rw [hg, liftVal, toVal_emulateFinish_roundVal, toVal_ofFloat64]

/-- The two-argument version, for operations specified by `liftVal₂ f`. -/
theorem toVal_emulate₂ (g : AzFloat → AzFloat → ℕ → RoundingMode → AzFloat × Ordering)
    (f : EReal → EReal → Option EReal)
    (hg : ∀ x y, g x y 53 .Nearest = liftVal₂ f x y 53 .Nearest) (x y : Float) :
    (emulate₂ g x y).toModel.unpack.toVal
      = roundBinary64Val (x.toModel.unpack.toVal.bind fun a =>
          y.toModel.unpack.toVal.bind fun b => f a b) := by
  unfold emulate₂
  rw [hg, liftVal₂, toVal_emulateFinish_roundVal, toVal_ofFloat64, toVal_ofFloat64]

/-- The three-argument version, for operations specified by a `roundVal` of `f` over the three
values. -/
theorem toVal_emulate₃
    (g : AzFloat → AzFloat → AzFloat → ℕ → RoundingMode → AzFloat × Ordering)
    (f : EReal → EReal → EReal → Option EReal)
    (hg : ∀ x y z, g x y z 53 .Nearest = roundVal 53 .Nearest
      (x.toVal.bind fun a => y.toVal.bind fun b => z.toVal.bind fun c => f a b c))
    (x y z : Float) :
    (emulate₃ g x y z).toModel.unpack.toVal
      = roundBinary64Val (x.toModel.unpack.toVal.bind fun a =>
          y.toModel.unpack.toVal.bind fun b => z.toModel.unpack.toVal.bind fun c => f a b c) := by
  unfold emulate₃
  rw [hg, toVal_emulateFinish_roundVal, toVal_ofFloat64, toVal_ofFloat64, toVal_ofFloat64]

/-- The four-argument version, for operations specified by a `roundVal` of `f` over the four
values. -/
theorem toVal_emulate₄
    (g : AzFloat → AzFloat → AzFloat → AzFloat → ℕ → RoundingMode →
      AzFloat × Ordering)
    (f : EReal → EReal → EReal → EReal → Option EReal)
    (hg : ∀ x y z w, g x y z w 53 .Nearest = roundVal 53 .Nearest
      (x.toVal.bind fun a => y.toVal.bind fun b => z.toVal.bind fun c =>
        w.toVal.bind fun d => f a b c d))
    (x y z w : Float) :
    (emulate₄ g x y z w).toModel.unpack.toVal
      = roundBinary64Val (x.toModel.unpack.toVal.bind fun a =>
          y.toModel.unpack.toVal.bind fun b => z.toModel.unpack.toVal.bind fun c =>
            w.toModel.unpack.toVal.bind fun d => f a b c d) := by
  unfold emulate₄
  rw [hg, toVal_emulateFinish_roundVal, toVal_ofFloat64, toVal_ofFloat64, toVal_ofFloat64,
    toVal_ofFloat64]

/-- The two-floats-and-a-rational version, for operations specified by a `roundVal` of `f` over
the two float values and the rational. -/
theorem toVal_emulate₂Rat
    (g : AzFloat → AzFloat → AzRat → ℕ → RoundingMode → AzFloat × Ordering)
    (f : EReal → EReal → AzRat → Option EReal)
    (hg : ∀ x y z, g x y z 53 .Nearest = roundVal 53 .Nearest
      (x.toVal.bind fun a => y.toVal.bind fun b => f a b z))
    (x y : Float) (z : AzRat) :
    (emulate₂Rat g x y z).toModel.unpack.toVal
      = roundBinary64Val (x.toModel.unpack.toVal.bind fun a =>
          y.toModel.unpack.toVal.bind fun b => f a b z) := by
  unfold emulate₂Rat
  rw [hg, toVal_emulateFinish_roundVal, toVal_ofFloat64, toVal_ofFloat64]

/-- The three-floats-and-a-rational version. -/
theorem toVal_emulate₃Rat
    (g : AzFloat → AzFloat → AzFloat → AzRat → ℕ → RoundingMode → AzFloat × Ordering)
    (f : EReal → EReal → EReal → AzRat → Option EReal)
    (hg : ∀ x y z w, g x y z w 53 .Nearest = roundVal 53 .Nearest
      (x.toVal.bind fun a => y.toVal.bind fun b => z.toVal.bind fun c => f a b c w))
    (x y z : Float) (w : AzRat) :
    (emulate₃Rat g x y z w).toModel.unpack.toVal
      = roundBinary64Val (x.toModel.unpack.toVal.bind fun a =>
          y.toModel.unpack.toVal.bind fun b => z.toModel.unpack.toVal.bind fun c =>
            f a b c w) := by
  unfold emulate₃Rat
  rw [hg, toVal_emulateFinish_roundVal, toVal_ofFloat64, toVal_ofFloat64, toVal_ofFloat64]

/-- The rational-argument version, for operations specified by a `roundVal` of `f q`. -/
theorem toVal_emulateRat (g : AzRat → ℕ → RoundingMode → AzFloat × Ordering)
    (f : AzRat → Option EReal) (hg : ∀ q, g q 53 .Nearest = roundVal 53 .Nearest (f q))
    (q : AzRat) : (emulateRat g q).toModel.unpack.toVal = roundBinary64Val (f q) := by
  unfold emulateRat
  rw [hg, toVal_emulateFinish_roundVal]

/-- The list version, for operations specified by a `roundVal` of `f xs`. -/
theorem toVal_emulateList (g : List AzFloat → ℕ → RoundingMode → AzFloat × Ordering)
    (f : List AzFloat → Option EReal)
    (hg : ∀ xs, g xs 53 .Nearest = roundVal 53 .Nearest (f xs)) (xs : List Float) :
    (emulateList g xs).toModel.unpack.toVal = roundBinary64Val (f (xs.map ofFloat64)) := by
  unfold emulateList
  rw [hg, toVal_emulateFinish_roundVal]

end Azurite.AzFloat
