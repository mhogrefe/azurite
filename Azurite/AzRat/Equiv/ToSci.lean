/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzRat.ToSci
import Azurite.AzRat.Equiv.LogBase
import Azurite.AzRat.Equiv.LengthAfterPoint
import Azurite.AzInt.Equiv.DivRound
import Azurite.AzInt.Equiv.Conversion
import Azurite.AzNat.Equiv.LimbDigits
import Azurite.Rounding.Sci
import Azurite.Rounding.SciPrecision

/-!
# Correctness of `AzRat.toSciNumber`

The first stage of `toSci` produces a `SciNumber` whose `value` is the abstract rounding of
`toRat q` to the target chosen by the size option (`docs/to_sci_plan.md`):

* `toSciNumber_value_scale`: `scale s` rounds to `scaleSet b s`;
* `toSciNumber_value_complete`: `complete` is exact, and succeeds iff the expansion terminates.

Everything reduces to `AzInt.toInt_divRound` for the scaled rounding (`toInt_scaledRound`) and to
`Nat.ofDigits_digits` for the digits.
-/

namespace Azurite.AzRat

open RoundingTarget

/-- `toRat q` as a real quotient of the limb values with `q`'s sign. -/
lemma toRat_real_eq (q : AzRat) :
    (toRat q : ℝ) = (if q.sign then (q.num.toNat : ℝ) else -(q.num.toNat : ℝ)) / q.den.toNat := by
  have hnum : (toRat q).num = if q.sign then (q.num.toNat : ℤ) else -(q.num.toNat : ℤ) := rfl
  have hden : (toRat q).den = q.den.toNat := rfl
  rw [Rat.cast_def, hnum, hden]
  cases q.sign <;> push_cast <;> rfl

/-- The signed numerator built by `mkNorm` from `q`'s sign and a nonzero magnitude (or any
magnitude when the sign is positive). -/
private lemma toInt_mkNorm_sign (q : AzRat) (m : AzNat) (hm : q.sign = false → m ≠ 0) :
    ((AzInt.mkNorm q.sign m).toInt : ℝ) = (if q.sign then (m.toNat : ℝ) else -(m.toNat : ℝ)) := by
  cases hs : q.sign with
  | true => rw [AzInt.toInt_mkNorm_true]; simp
  | false => rw [AzInt.toInt_mkNorm_false m (hm hs)]; simp

/-- The denominator of `q` is nonzero as a real. -/
private lemma den_real_pos (q : AzRat) : (0 : ℝ) < q.den.toNat := by
  exact_mod_cast den_toNat_pos q

/-- **`scaledRound` rounds `toRat q · b^scale` to an integer.** -/
theorem toInt_scaledRound (q : AzRat) (b : UInt64) (hb : 0 < b.toNat) (scale : ℤ)
    (mode : RoundingMode) :
    (((scaledRound q b scale mode).1.toInt : ℝ) : EReal)
      = (RoundingTarget.round intSet mode ((toRat q : ℝ) * (b.toNat : ℝ) ^ scale)).val := by
  have hbR : (0 : ℝ) < b.toNat := by exact_mod_cast hb
  have hD := den_real_pos q
  have hnum0 : q.sign = false → q.num ≠ 0 := by
    intro hs h0
    have := q.zero_sign h0
    rw [hs] at this
    exact absurd this (by decide)
  unfold scaledRound
  cases scale with
  | ofNat s =>
    have hden_pos : 0 < (q.den.toAzInt).abs.toNat := by
      show 0 < q.den.toNat; exact den_toNat_pos q
    rw [AzInt.toInt_divRound _ _ mode hden_pos]
    congr 2
    rw [Azurite.AzNat.toInt_toAzInt, Int.cast_natCast]
    rw [toInt_mkNorm_sign q _ (fun hs => by
      intro h0
      have h := congrArg AzNat.toNat h0
      rw [AzNat.toNat_mul, AzNat.toNat_pow, AzNat.toNat_ofNat, AzNat.toNat_zero] at h
      rcases Nat.mul_eq_zero.mp h with h1 | h1
      · exact hnum0 hs (AzNat.toNat_injective (h1.trans AzNat.toNat_zero.symm))
      · exact absurd h1 (pow_ne_zero _ hb.ne'))]
    rw [AzNat.toNat_mul, AzNat.toNat_pow, AzNat.toNat_ofNat, toRat_real_eq, Int.ofNat_eq_natCast,
      zpow_natCast]
    push_cast
    cases q.sign <;> (try simp only [Bool.false_eq_true, ↓reduceIte]) <;> field_simp
  | negSucc s =>
    have hden_pos : 0 < ((q.den * (AzNat.ofNat b.toNat).pow (s + 1)).toAzInt).abs.toNat := by
      show 0 < (q.den * (AzNat.ofNat b.toNat).pow (s + 1)).toNat
      rw [AzNat.toNat_mul, AzNat.toNat_pow, AzNat.toNat_ofNat]
      exact Nat.mul_pos (den_toNat_pos q) (pow_pos hb _)
    rw [AzInt.toInt_divRound _ _ mode hden_pos]
    congr 2
    rw [Azurite.AzNat.toInt_toAzInt, Int.cast_natCast, AzNat.toNat_mul, AzNat.toNat_pow,
      AzNat.toNat_ofNat, toInt_mkNorm_sign q _ hnum0, toRat_real_eq, zpow_negSucc]
    push_cast
    cases q.sign <;> (try simp only [Bool.false_eq_true, ↓reduceIte]) <;> field_simp

/-- The tag of `scaledRound` compares the rounded integer with `toRat q · b^scale`. -/
theorem snd_scaledRound (q : AzRat) (b : UInt64) (hb : 0 < b.toNat) (scale : ℤ)
    (mode : RoundingMode) :
    (scaledRound q b scale mode).2
      = compare (((scaledRound q b scale mode).1.toInt : ℤ) : ℝ)
          ((toRat q : ℝ) * (b.toNat : ℝ) ^ scale) := by
  have hbR : (0 : ℝ) < b.toNat := by exact_mod_cast hb
  have hD := den_real_pos q
  have hnum0 : q.sign = false → q.num ≠ 0 := by
    intro hs h0
    have := q.zero_sign h0
    rw [hs] at this
    exact absurd this (by decide)
  unfold scaledRound
  cases scale with
  | ofNat s =>
    have hden_pos : 0 < (q.den.toAzInt).abs.toNat := by
      show 0 < q.den.toNat; exact den_toNat_pos q
    rw [AzInt.snd_divRound _ _ mode hden_pos]
    congr 1
    rw [Azurite.AzNat.toInt_toAzInt, Int.cast_natCast]
    rw [toInt_mkNorm_sign q _ (fun hs => by
      intro h0
      have h := congrArg AzNat.toNat h0
      rw [AzNat.toNat_mul, AzNat.toNat_pow, AzNat.toNat_ofNat, AzNat.toNat_zero] at h
      rcases Nat.mul_eq_zero.mp h with h1 | h1
      · exact hnum0 hs (AzNat.toNat_injective (h1.trans AzNat.toNat_zero.symm))
      · exact absurd h1 (pow_ne_zero _ hb.ne'))]
    rw [AzNat.toNat_mul, AzNat.toNat_pow, AzNat.toNat_ofNat, toRat_real_eq, Int.ofNat_eq_natCast,
      zpow_natCast]
    push_cast
    cases q.sign <;> (try simp only [Bool.false_eq_true, ↓reduceIte]) <;> field_simp
  | negSucc s =>
    have hden_pos : 0 < ((q.den * (AzNat.ofNat b.toNat).pow (s + 1)).toAzInt).abs.toNat := by
      show 0 < (q.den * (AzNat.ofNat b.toNat).pow (s + 1)).toNat
      rw [AzNat.toNat_mul, AzNat.toNat_pow, AzNat.toNat_ofNat]
      exact Nat.mul_pos (den_toNat_pos q) (pow_pos hb _)
    rw [AzInt.snd_divRound _ _ mode hden_pos]
    congr 1
    rw [Azurite.AzNat.toInt_toAzInt, Int.cast_natCast, AzNat.toNat_mul, AzNat.toNat_pow,
      AzNat.toNat_ofNat, toInt_mkNorm_sign q _ hnum0, toRat_real_eq, zpow_negSucc]
    push_cast
    cases q.sign <;> (try simp only [Bool.false_eq_true, ↓reduceIte]) <;> field_simp

/-! ### Digits -/

/-- Horner over a most-significant-first list is `Nat.ofDigits` of its reverse. -/
lemma foldl_horner_eq_ofDigits (b : ℕ) (l : List ℕ) :
    l.foldl (fun acc d => acc * b + d) 0 = Nat.ofDigits b l.reverse := by
  induction l using List.reverseRecOn with
  | nil => simp
  | append_singleton l d ih =>
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil, ih, List.reverse_append,
      List.reverse_singleton, List.singleton_append, Nat.ofDigits_cons]
    ring

/-- The mantissa of the digits of `n` (most significant first) is `n`. -/
lemma mantissa_digits (b : UInt64) (hb : 2 ≤ b.toNat) (n : AzNat) (neg : Bool) (sc : Int) :
    (SciNumber.mantissa ⟨neg, b, (n.limbDigits b).reverse, sc⟩) = n.toNat := by
  unfold SciNumber.mantissa
  simp only []
  rw [← Array.foldl_toList, Array.toList_reverse]
  have h : ((n.limbDigits b).toList.reverse).foldl (fun acc d => acc * b.toNat + d.toNat) 0
      = (((n.limbDigits b).toList.map UInt64.toNat).reverse).foldl
          (fun acc d => acc * b.toNat + d) 0 := by
    rw [← List.map_reverse, List.foldl_map]
  rw [h, foldl_horner_eq_ofDigits, List.reverse_reverse, AzNat.limbDigits_eq b hb,
    Nat.ofDigits_digits]

/-- The value of a `SciNumber` built from a rounded `AzInt`: `toInt · b^(−scale)`. -/
lemma value_of_azint (b : UInt64) (hb : 2 ≤ b.toNat) (r : AzInt) (sc : Int) :
    (SciNumber.value ⟨!r.sign, b, (r.abs.limbDigits b).reverse, sc⟩ : ℝ)
      = (r.toInt : ℝ) * (b.toNat : ℝ) ^ (-sc) := by
  unfold SciNumber.value
  rw [mantissa_digits b hb]
  simp only []
  push_cast
  unfold AzInt.toInt
  cases r.sign <;> simp


/-! ### The size options -/

/-- Valid options have a base in `[2, 36]`. -/
lemma valid_base {o : SciOptions} (hv : o.valid = true) : 2 ≤ o.base.toNat ∧ o.base.toNat ≤ 36 := by
  unfold SciOptions.valid at hv
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hv
  obtain ⟨⟨⟨h1, h2⟩, _⟩, _⟩ := hv
  rw [UInt64.le_iff_toNat_le] at h1 h2
  exact ⟨by simpa using h1, by simpa using h2⟩

/-- A `SciNumber` with no digits has value `0`. -/
lemma value_zero_digits (neg : Bool) (b : UInt64) (sc : Int) :
    (SciNumber.value ⟨neg, b, #[], sc⟩ : ℚ) = 0 := by
  unfold SciNumber.value SciNumber.mantissa
  simp

/-- `toInt` of an `AzInt` with zero magnitude is `0`. -/
private lemma toInt_eq_zero_of_abs {r : AzInt} (h : r.abs = 0) : r.toInt = 0 := by
  unfold AzInt.toInt
  rw [h, AzNat.toNat_zero]
  cases r.sign <;> simp

/-- `toRat q = 0` iff the numerator is zero. -/
lemma toRat_eq_zero_iff (q : AzRat) : (toRat q : ℝ) = 0 ↔ q.num = 0 := by
  rw [Rat.cast_eq_zero, Rat.zero_iff_num_zero]
  have hnum : (toRat q).num = if q.sign then (q.num.toNat : ℤ) else -(q.num.toNat : ℤ) := rfl
  rw [hnum]
  constructor
  · intro h
    have h' : q.num.toNat = 0 := by
      cases hs : q.sign
      · rw [hs] at h
        simp only [Bool.false_eq_true, ↓reduceIte, neg_eq_zero, Nat.cast_eq_zero] at h
        exact h
      · rw [hs] at h
        simp only [↓reduceIte, Nat.cast_eq_zero] at h
        exact h
    exact AzNat.toNat_injective (by rw [AzNat.toNat_zero]; exact h')
  · intro h
    rw [h, AzNat.toNat_zero]
    cases q.sign <;> simp

/-- **`scale s` rounds to `scaleSet b s`.** -/
theorem toSciNumber_value_scale (q : AzRat) (o : SciOptions) (hv : o.valid = true) (s : ℕ)
    (hs : o.size = .scale s) [NeZero o.base.toNat] :
    ∃ x, q.toSciNumber o = some x ∧
      ((x.value : ℝ) : EReal)
        = (RoundingTarget.round (scaleSet o.base.toNat s) o.mode (toRat q : ℝ)).val := by
  obtain ⟨hb2, _⟩ := valid_base hv
  have hb0 : 0 < o.base.toNat := by omega
  rw [val_round_scaleSet]
  have hbR : (0 : ℝ) < o.base.toNat := by exact_mod_cast hb0
  set y : ℝ := (toRat q : ℝ) * (o.base.toNat : ℝ) ^ s with hy
  -- the scaled rounding
  have hr := toInt_scaledRound q o.base hb0 (s : ℤ) o.mode
  rw [zpow_natCast, ← hy] at hr
  have hrI : toInt (RoundingTarget.round intSet o.mode y) = (scaledRound q o.base (s : ℤ) o.mode).1.toInt :=
    toInt_eq_of_val hr
  rw [hrI]
  unfold toSciNumber
  rw [hv]
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  by_cases h0 : q.num = 0
  · rw [ite_eq_left h0]
    refine ⟨_, rfl, ?_⟩
    rw [value_zero_digits]
    -- `q = 0`, so the scaled rounding is `0`
    have hq0 : (toRat q : ℝ) = 0 := (toRat_eq_zero_iff q).mpr h0
    have hy0 : y = 0 := by rw [hy, hq0, zero_mul]
    have hval := val_round_of_mem intSet o.mode (x := y) (by rw [hy0]; exact ⟨0, by simp⟩)
    have : toInt (RoundingTarget.round intSet o.mode y) = 0 := toInt_eq_of_val (by rw [hval, hy0]; simp)
    rw [hrI] at this
    rw [this]
    simp
  · rw [ite_eq_right h0]
    simp only [sizeScale, hs]
    set r := scaledRound q o.base (s : ℤ) o.mode with hr_def
    by_cases hn : r.1.abs = 0
    · rw [ite_eq_left hn]
      refine ⟨_, rfl, ?_⟩
      rw [value_zero_digits, toInt_eq_zero_of_abs hn]
      simp
    · rw [ite_eq_right hn]
      refine ⟨_, rfl, ?_⟩
      rw [value_of_azint o.base hb2]
      congr 1
      rw [zpow_neg, zpow_natCast, div_eq_mul_inv]

/-- Membership of `toRat q · b^L` in `intSet` when the denominator divides `b^L`. -/
private lemma scaled_mem_intSet (q : AzRat) (b : UInt64) (L : ℕ) (hdvd : q.den.toNat ∣ b.toNat ^ L) :
    (((toRat q : ℝ) * (b.toNat : ℝ) ^ L : ℝ) : EReal) ∈ intSet := by
  obtain ⟨k, hk⟩ := hdvd
  have hD := den_real_pos q
  refine ⟨(if q.sign then (q.num.toNat : ℤ) else -(q.num.toNat : ℤ)) * k, ?_⟩
  congr 1
  rw [toRat_real_eq]
  have hkR : (b.toNat : ℝ) ^ L = (q.den.toNat : ℝ) * k := by exact_mod_cast hk
  rw [hkR]
  push_cast
  cases q.sign <;> (try simp only [Bool.false_eq_true, ↓reduceIte]) <;> field_simp

/-- **`complete` is exact, and succeeds iff the expansion terminates.** -/
theorem toSciNumber_complete (q : AzRat) (o : SciOptions) (hv : o.valid = true)
    (hc : o.size = .complete) :
    (∀ x, q.toSciNumber o = some x → (x.value : ℝ) = toRat q) ∧
    ((q.toSciNumber o).isSome ↔ (lengthAfterPoint o.base q).isSome) := by
  obtain ⟨hb2, hb36⟩ := valid_base hv
  have hb0 : 0 < o.base.toNat := by omega
  unfold toSciNumber
  rw [hv]
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  by_cases h0 : q.num = 0
  · rw [ite_eq_left h0]
    constructor
    · intro x hx
      obtain rfl := Option.some.inj hx
      rw [value_zero_digits, (toRat_eq_zero_iff q).mpr h0]
      simp
    · -- `den = 1` divides `b^0`
      have hden : q.den.toNat = 1 := by
        have hcop := (AzNat.coprime_iff _ _).mp q.reduced
        rw [h0, AzNat.toNat_zero] at hcop
        exact (Nat.coprime_zero_left _).mp hcop
      have : lengthAfterPoint o.base q = some 0 :=
        (lengthAfterPoint_some_iff o.base ⟨hb2, hb36⟩ q 0).mpr
          ⟨by rw [hden]; exact one_dvd _, fun L' hL' => absurd hL' (Nat.not_lt_zero _)⟩
      simp [this]
  · rw [ite_eq_right h0]
    simp only [sizeScale, hc]
    rcases hlen : lengthAfterPoint o.base q with _ | L
    · simp
    · simp only [Option.map_some]
      have hdvd := ((lengthAfterPoint_some_iff o.base ⟨hb2, hb36⟩ q L).mp hlen).1
      set r := scaledRound q o.base (L : ℤ) o.mode with hr_def
      -- the scaled value is an integer, so the rounding is exact
      have hmem := scaled_mem_intSet q o.base L hdvd
      have hr := toInt_scaledRound q o.base hb0 (L : ℤ) o.mode
      rw [zpow_natCast, val_round_of_mem intSet o.mode hmem] at hr
      have hrR : (r.1.toInt : ℝ) = (toRat q : ℝ) * (o.base.toNat : ℝ) ^ L :=
        EReal.coe_eq_coe_iff.mp hr
      have hbR : (0 : ℝ) < o.base.toNat := by exact_mod_cast hb0
      constructor
      · intro x hx
        by_cases hn : r.1.abs = 0
        · rw [ite_eq_left hn] at hx
          rw [Option.some.inj hx |>.symm, value_zero_digits]
          -- `r = 0` forces `toRat q = 0`
          have : (toRat q : ℝ) * (o.base.toNat : ℝ) ^ L = 0 := by
            rw [← hrR, toInt_eq_zero_of_abs hn]; simp
          rcases mul_eq_zero.mp this with h | h
          · simp [h]
          · exact absurd h (pow_pos hbR _).ne'
        · rw [ite_eq_right hn] at hx
          rw [Option.some.inj hx |>.symm, value_of_azint o.base hb2, hrR]
          rw [zpow_neg, zpow_natCast, mul_assoc, mul_inv_cancel₀ (pow_pos hbR _).ne', mul_one]
      · constructor
        · intro _; simp
        · intro _
          by_cases hn : r.1.abs = 0
          · rw [ite_eq_left hn]; simp
          · rw [ite_eq_right hn]; simp


/-! ### `precision p` -/

/-- Rounding to the integers returns the floor or the ceiling. -/
lemma toInt_round_intSet_eq_floor_or_ceil (mode : RoundingMode) (y : ℝ) :
    toInt (RoundingTarget.round intSet mode y) = ⌊y⌋ ∨
    toInt (RoundingTarget.round intSet mode y) = ⌈y⌉ := by
  have hF : toInt (roundFloor intSet y) = ⌊y⌋ := toInt_eq_of_val (val_roundFloor_intSet y).symm
  have hC : toInt (roundCeiling intSet y) = ⌈y⌉ :=
    toInt_eq_of_val (val_roundCeiling_intSet y).symm
  cases mode with
  | Floor => exact Or.inl hF
  | Ceiling => exact Or.inr hC
  | Down =>
    unfold RoundingTarget.round
    split_ifs
    · exact Or.inl hF
    · exact Or.inr hC
  | Up =>
    unfold RoundingTarget.round
    split_ifs
    · exact Or.inr hC
    · exact Or.inl hF
  | Nearest =>
    unfold RoundingTarget.round
    simp only []
    split
    · exact Or.inl hF
    · exact Or.inr hC
    · rcases RoundingTarget.tiebreak_mem (roundFloor intSet y) (roundCeiling intSet y) with h | h
      · rw [h]; exact Or.inl hF
      · rw [h]; exact Or.inr hC

/-- `|⌊y⌋| ≤ B` and `|⌈y⌉| ≤ B` when `|y| < B` for an integer `B`. -/
lemma floor_ceil_abs_le (y : ℝ) (B : ℤ) (hy : |y| < (B : ℝ)) :
    |⌊y⌋| ≤ B ∧ |⌈y⌉| ≤ B := by
  rw [abs_lt] at hy
  constructor
  · rw [abs_le]
    constructor
    · exact Int.le_floor.mpr (by push_cast; exact hy.1.le)
    · exact Int.le_of_lt_add_one (Int.floor_lt.mpr (by linarith [hy.2]) |>.trans_le (by omega))
  · rw [abs_le]
    constructor
    · have : (-B : ℤ) < ⌈y⌉ := Int.lt_ceil.mpr (by push_cast; exact hy.1)
      omega
    · exact Int.ceil_le.mpr hy.2.le

/-- **`precision p` rounds to `precisionSet b p`.** -/
theorem toSciNumber_value_precision (q : AzRat) (o : SciOptions) (hv : o.valid = true) (p : ℕ)
    (hp : o.size = .precision p) [Fact (1 < o.base.toNat)] [NeZero p] :
    ∃ x, q.toSciNumber o = some x ∧
      ((x.value : ℝ) : EReal)
        = (RoundingTarget.round (precisionSet o.base.toNat p) o.mode (toRat q : ℝ)).val := by
  obtain ⟨hb2, _⟩ := valid_base hv
  have hb0 : 0 < o.base.toNat := by omega
  have hb1 : 1 < o.base.toNat := hb2
  have hbR : (1 : ℝ) < o.base.toNat := by exact_mod_cast hb1
  have hbR0 : (0 : ℝ) < o.base.toNat := by linarith
  have hp0 : 0 < p := Nat.pos_of_ne_zero (NeZero.ne p)
  unfold toSciNumber
  rw [hv]
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  by_cases h0 : q.num = 0
  · rw [ite_eq_left h0]
    refine ⟨_, rfl, ?_⟩
    have hq0 : (toRat q : ℝ) = 0 := (toRat_eq_zero_iff q).mpr h0
    rw [value_zero_digits, hq0,
      val_round_of_mem (precisionSet o.base.toNat p) o.mode (x := (0 : ℝ)) (Or.inl (by simp))]
    simp
  · rw [ite_eq_right h0]
    simp only [sizeScale, hp]
    set x : ℝ := (toRat q : ℝ) with hx_def
    have hx : x ≠ 0 := fun h => h0 ((toRat_eq_zero_iff q).mp h)
    rw [val_round_precisionSet o.mode x hx]
    set e := Int.log o.base.toNat |x| with he
    have hlog : floorLogBaseAbs o.base q = e := by
      rw [he, hx_def]; exact floorLogBaseAbs_eq o.base hb2 q h0
    rw [hlog]
    set u := precScale o.base.toNat p x with hu_def
    have hu : 0 < u := zpow_pos hbR0 _
    have hu_eq : u = (o.base.toNat : ℝ) ^ (e - p + 1) := by
      rw [hu_def]; unfold precScale; rw [← he]
    set sc : ℤ := (p : ℤ) - 1 - e with hsc
    have hpow : (o.base.toNat : ℝ) ^ sc = u⁻¹ := by
      rw [hu_eq, ← zpow_neg]; congr 1; rw [hsc]; ring
    have hr := toInt_scaledRound q o.base hb0 sc o.mode
    rw [hpow, ← div_eq_mul_inv, ← hx_def] at hr
    have hrI : toInt (RoundingTarget.round intSet o.mode (x / u))
        = (scaledRound q o.base sc o.mode).1.toInt := toInt_eq_of_val hr
    rw [hrI]
    set r := scaledRound q o.base sc o.mode with hr_def
    by_cases hn : r.1.abs = 0
    · rw [ite_eq_left hn]
      refine ⟨_, rfl, ?_⟩
      rw [value_zero_digits, toInt_eq_zero_of_abs hn]
      simp
    · rw [ite_eq_right hn]
      set ds := (r.1.abs.limbDigits o.base).reverse with hds
      by_cases hsz : ds.size = p + 1
      · rw [ite_eq_left hsz]
        refine ⟨_, rfl, ?_⟩
        -- `n` has `p + 1` digits, so `b^p ≤ n`; the rounding bounds give `n ≤ b^p`.
        set n := r.1.abs.toNat with hn_def
        have hnpos : n ≠ 0 := fun h => hn (AzNat.toNat_injective (by rw [← hn_def, h]; rfl))
        have hlen : (Nat.digits o.base.toNat n).length = p + 1 := by
          have := congrArg List.length (AzNat.limbDigits_eq o.base hb2 r.1.abs)
          rw [List.length_map, Array.length_toList] at this
          rw [hds, Array.size_reverse] at hsz
          rw [← this, hsz]
        rw [Nat.length_digits _ _ hb1 hnpos] at hlen
        have hlogn : Nat.log o.base.toNat n = p := by omega
        have hge : o.base.toNat ^ p ≤ n := by
          rw [← hlogn]; exact Nat.pow_log_le_self _ hnpos
        have hle : n ≤ o.base.toNat ^ p := by
          have habs : (n : ℤ) = |r.1.toInt| := by
            rw [hn_def]; unfold AzInt.toInt; cases r.1.sign <;> simp
          have hyb : |x / u| < (o.base.toNat : ℝ) ^ (p : ℤ) :=
            (abs_div_precScale_bounds (b := o.base.toNat) (p := p) x hx).2
          have hB : ((o.base.toNat ^ p : ℕ) : ℤ) = (o.base.toNat : ℤ) ^ p := by push_cast; rfl
          have hyb' : |x / u| < (((o.base.toNat ^ p : ℕ) : ℤ) : ℝ) := by
            rw [hB]; push_cast; rw [← zpow_natCast]; exact hyb
          obtain ⟨h1, h2⟩ := floor_ceil_abs_le (x / u) _ hyb'
          rcases toInt_round_intSet_eq_floor_or_ceil o.mode (x / u) with h | h <;> rw [hrI] at h
          · have : (n : ℤ) ≤ ((o.base.toNat ^ p : ℕ) : ℤ) := by rw [habs, h]; exact h1
            exact_mod_cast this
          · have : (n : ℤ) ≤ ((o.base.toNat ^ p : ℕ) : ℤ) := by rw [habs, h]; exact h2
            exact_mod_cast this
        have hn_eq : n = o.base.toNat ^ p := le_antisymm hle hge
        -- the digits of `b^p`
        have hdig : Nat.digits o.base.toNat n = List.replicate p 0 ++ [1] := by
          rw [hn_eq, ← mul_one (o.base.toNat ^ p), Nat.digits_base_pow_mul hb1 one_pos,
            Nat.digits_of_lt _ _ one_ne_zero hb1]
        -- the popped mantissa is `b^(p-1)`
        have hmant : SciNumber.mantissa ⟨!r.1.sign, o.base, ds.pop, sc - 1⟩
            = o.base.toNat ^ (p - 1) := by
          unfold SciNumber.mantissa
          simp only []
          rw [← Array.foldl_toList, Array.toList_pop, hds, Array.toList_reverse]
          set l := (r.1.abs.limbDigits o.base).toList with hl
          have hfold : (l.reverse.dropLast).foldl (fun acc d => acc * o.base.toNat + d.toNat) 0
              = ((l.reverse.dropLast).map UInt64.toNat).foldl
                  (fun acc d => acc * o.base.toNat + d) 0 := by
            rw [List.foldl_map]
          rw [hfold, foldl_horner_eq_ofDigits, ← List.map_reverse]
          have htail : l.reverse.dropLast.reverse = l.tail := by
            have := List.tail_reverse (l := l.reverse)
            rw [List.reverse_reverse] at this
            exact this.symm
          rw [htail, List.map_tail, hl, AzNat.limbDigits_eq o.base hb2, ← hn_def, hdig]
          obtain ⟨p', hp'⟩ : ∃ p', p = p' + 1 := ⟨p - 1, by omega⟩
          rw [hp', List.replicate_succ, List.cons_append, List.tail_cons, Nat.ofDigits_append,
            Nat.ofDigits_replicate_zero, Nat.ofDigits_singleton, List.length_replicate]
          simp
        -- assemble
        have hsign : (r.1.toInt : ℝ) = (if r.1.sign then (n : ℝ) else -(n : ℝ)) := by
          unfold AzInt.toInt; rw [hn_def]; cases r.1.sign <;> simp
        unfold SciNumber.value
        rw [hmant]
        simp only []
        congr 1
        push_cast
        rw [hsign, hn_eq, hu_eq]
        push_cast
        have hsc1 : -(sc - 1) = (e - p + 1) + 1 := by rw [hsc]; ring
        rw [hsc1, zpow_add_one₀ hbR0.ne']
        have hpp : ((o.base.toNat : ℝ) ^ (p - 1) : ℝ) * (o.base.toNat : ℝ)
            = (o.base.toNat : ℝ) ^ p := by
          rw [← pow_succ]; congr 1; omega
        rcases Bool.eq_false_or_eq_true r.1.sign with hs | hs
        · simp only [hs, Bool.not_true, Bool.false_eq_true, ↓reduceIte, Rat.cast_one]
          linear_combination ((o.base.toNat : ℝ) ^ (e - p + 1)) * hpp
        · simp only [hs, Bool.not_false, Bool.false_eq_true, ↓reduceIte, Rat.cast_one, Rat.cast_neg]
          linear_combination (-(o.base.toNat : ℝ) ^ (e - p + 1)) * hpp
      · rw [ite_eq_right hsz]
        refine ⟨_, rfl, ?_⟩
        rw [value_of_azint o.base hb2]
        congr 3
        rw [hsc]; ring


/-! ### Exactness -/

/-- A positive precision is part of validity. -/
lemma valid_precision {o : SciOptions} (hv : o.valid = true) {p : ℕ} (hp : o.size = .precision p) :
    0 < p := by
  unfold SciOptions.valid at hv
  simp only [Bool.and_eq_true] at hv
  have h := hv.2
  rw [hp] at h
  unfold SciSizeOptions.valid at h
  simp only [bne_iff_ne, ne_eq] at h
  omega

/-- Away from `complete`, the value produced is the rounded integer times `b^(−scale)`. -/
theorem toSciNumber_value_eq_scaledRound (q : AzRat) (o : SciOptions) (hv : o.valid = true)
    (h0 : q.num ≠ 0) (scale prec : ℤ)
    (hsz : sizeScale o.base q o.size (floorLogBaseAbs o.base q) = some (scale, prec))
    (hc : o.size ≠ .complete) :
    ∃ x, q.toSciNumber o = some x ∧
      (x.value : ℝ) = ((scaledRound q o.base scale o.mode).1.toInt : ℝ)
        * (o.base.toNat : ℝ) ^ (-scale) := by
  obtain ⟨hb2, _⟩ := valid_base hv
  have hb0 : 0 < o.base.toNat := by omega
  have hbR0 : (0 : ℝ) < o.base.toNat := by exact_mod_cast hb0
  have hx : (toRat q : ℝ) ≠ 0 := fun h => h0 ((toRat_eq_zero_iff q).mp h)
  rcases hsize : o.size with _ | p | s
  · exact absurd hsize hc
  · -- precision
    rw [hsize] at hsz
    simp only [sizeScale, Option.some.injEq, Prod.mk.injEq] at hsz
    obtain ⟨hscale, -⟩ := hsz
    have : Fact (1 < o.base.toNat) := ⟨hb2⟩
    have : NeZero p := ⟨(valid_precision hv hsize).ne'⟩
    obtain ⟨x, hx_eq, hval⟩ := toSciNumber_value_precision q o hv p hsize
    refine ⟨x, hx_eq, ?_⟩
    rw [val_round_precisionSet o.mode _ hx] at hval
    set e := Int.log o.base.toNat |(toRat q : ℝ)| with he
    have hlog : floorLogBaseAbs o.base q = e := floorLogBaseAbs_eq o.base hb2 q h0
    have hu_eq : precScale o.base.toNat p (toRat q : ℝ) = (o.base.toNat : ℝ) ^ (-scale) := by
      unfold precScale; rw [← he, ← hscale, hlog]; congr 1; ring
    have hpow : (o.base.toNat : ℝ) ^ scale = (precScale o.base.toNat p (toRat q : ℝ))⁻¹ := by
      rw [hu_eq, ← zpow_neg, neg_neg]
    have hr := toInt_scaledRound q o.base hb0 scale o.mode
    rw [hpow, ← div_eq_mul_inv] at hr
    have hrI := toInt_eq_of_val hr
    rw [hrI, hu_eq] at hval
    exact EReal.coe_eq_coe_iff.mp hval
  · -- scale
    rw [hsize] at hsz
    simp only [sizeScale, Option.some.injEq, Prod.mk.injEq] at hsz
    obtain ⟨hscale, -⟩ := hsz
    have : NeZero o.base.toNat := ⟨hb0.ne'⟩
    obtain ⟨x, hx_eq, hval⟩ := toSciNumber_value_scale q o hv s hsize
    refine ⟨x, hx_eq, ?_⟩
    rw [val_round_scaleSet] at hval
    have hr := toInt_scaledRound q o.base hb0 scale o.mode
    rw [← hscale, zpow_natCast] at hr
    have hrI := toInt_eq_of_val hr
    rw [hrI] at hval
    rw [← hscale, zpow_neg, zpow_natCast, div_eq_mul_inv] at *
    exact EReal.coe_eq_coe_iff.mp hval

/-- **`toSciExact q o` holds exactly when the printed value is `toRat q` itself.** -/
theorem toSciExact_iff (q : AzRat) (o : SciOptions) :
    q.toSciExact o = true ↔ ∃ x, q.toSciNumber o = some x ∧ (x.value : ℝ) = toRat q := by
  by_cases hv : o.valid = true
  swap
  · have hv' : o.valid = false := by simpa using hv
    unfold toSciExact toSciNumber
    rw [hv']
    simp
  obtain ⟨hb2, hb36⟩ := valid_base hv
  have hb0 : 0 < o.base.toNat := by omega
  have hbR0 : (0 : ℝ) < o.base.toNat := by exact_mod_cast hb0
  unfold toSciExact
  rw [hv, Bool.true_and, Bool.or_eq_true, decide_eq_true_eq]
  by_cases h0 : q.num = 0
  · simp only [h0, true_or, true_iff]
    refine ⟨⟨false, o.base, #[], zeroScale o.size⟩, ?_, ?_⟩
    · unfold toSciNumber
      rw [hv]
      simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, h0]
    · rw [value_zero_digits, (toRat_eq_zero_iff q).mpr h0]; simp
  · simp only [h0, false_or]
    rcases hsize : o.size with _ | p | s
    · -- complete
      obtain ⟨hval, hiff⟩ := toSciNumber_complete q o hv hsize
      simp only []
      constructor
      · intro h
        obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp (hiff.mpr h)
        exact ⟨x, hx, hval x hx⟩
      · rintro ⟨x, hx, _⟩
        exact hiff.mp (Option.isSome_iff_exists.mpr ⟨x, hx⟩)
    · -- precision
      simp only [sizeScale]
      obtain ⟨x, hx, hval⟩ := toSciNumber_value_eq_scaledRound q o hv h0
        ((p : ℤ) - 1 - floorLogBaseAbs o.base q) p (by rw [hsize]; rfl)
        (by rw [hsize]; exact SciSizeOptions.noConfusion)
      rw [snd_scaledRound q o.base hb0 _ o.mode, beq_iff_eq, compare_eq_iff_eq]
      constructor
      · intro h
        refine ⟨x, hx, ?_⟩
        rw [hval, h, mul_assoc, ← zpow_add₀ hbR0.ne', add_neg_cancel, zpow_zero, mul_one]
      · rintro ⟨y, hy, hyv⟩
        rw [hx] at hy
        obtain rfl := Option.some.inj hy
        rw [hval] at hyv
        rw [← hyv, mul_assoc, ← zpow_add₀ hbR0.ne', neg_add_cancel, zpow_zero, mul_one]
    · -- scale
      simp only [sizeScale]
      obtain ⟨x, hx, hval⟩ := toSciNumber_value_eq_scaledRound q o hv h0 (s : ℤ)
        ((s : ℤ) + floorLogBaseAbs o.base q + 1) (by rw [hsize]; rfl)
        (by rw [hsize]; exact SciSizeOptions.noConfusion)
      rw [snd_scaledRound q o.base hb0 (s : ℤ) o.mode, beq_iff_eq, compare_eq_iff_eq]
      constructor
      · intro h
        refine ⟨x, hx, ?_⟩
        rw [hval, h, mul_assoc, ← zpow_add₀ hbR0.ne', add_neg_cancel, zpow_zero, mul_one]
      · rintro ⟨y, hy, hyv⟩
        rw [hx] at hy
        obtain rfl := Option.some.inj hy
        rw [hval] at hyv
        rw [← hyv, mul_assoc, ← zpow_add₀ hbR0.ne', neg_add_cancel, zpow_zero, mul_one]


/-! ### Well-formedness of the digits -/

/-- Every digit produced by `limbDigits` (reversed) is below the base. -/
lemma digits_rev_lt_base (b : UInt64) (hb : 2 ≤ b.toNat) (n : AzNat) :
    ∀ d ∈ (n.limbDigits b).reverse, d.toNat < b.toNat := by
  intro d hd
  rw [Array.mem_def, Array.toList_reverse, List.mem_reverse] at hd
  have : d.toNat ∈ (n.limbDigits b).toList.map UInt64.toNat := List.mem_map_of_mem hd
  rw [AzNat.limbDigits_eq b hb] at this
  exact Nat.digits_lt_base hb this

/-- The leading digit of a nonzero number is nonzero. -/
lemma digits_rev_head_ne_zero (b : UInt64) (hb : 2 ≤ b.toNat) (n : AzNat) (hn : n ≠ 0)
    (h : 0 < (n.limbDigits b).reverse.size) : ((n.limbDigits b).reverse)[0]'h ≠ 0 := by
  have hnN : n.toNat ≠ 0 := fun hz => hn (AzNat.toNat_injective (by rw [hz]; rfl))
  have hlen : (n.limbDigits b).toList.length = (n.limbDigits b).size := Array.length_toList
  have hpos : 0 < (n.limbDigits b).toList.length := by
    rw [hlen]; rwa [Array.size_reverse] at h
  have hne : (n.limbDigits b).toList ≠ [] := List.ne_nil_of_length_pos hpos
  -- the head of the reversed array is the last entry of the list
  have hget : ((n.limbDigits b).reverse)[0]'h = (n.limbDigits b).toList.getLast hne := by
    rw [Array.getElem_reverse, List.getLast_eq_getElem, ← Array.getElem_toList]
    congr 1
  rw [hget]
  intro h0
  have hlast := Nat.getLast_digit_ne_zero b.toNat hnN
  have hne' : (n.limbDigits b).toList.map UInt64.toNat ≠ [] := by simpa using hne
  have hne'' : Nat.digits b.toNat n.toNat ≠ [] := by
    rw [← AzNat.limbDigits_eq b hb n]; exact hne'
  have hcongr := List.getLast_congr hne' hne'' (AzNat.limbDigits_eq b hb n)
  rw [← hcongr, List.getLast_map, h0] at hlast
  exact hlast rfl

/-- **Well-formedness of `toSciNumber`**: the base is the requested one, every digit is below
the base, and the leading digit is nonzero. -/
theorem toSciNumber_wellFormed (q : AzRat) (o : SciOptions) (x : SciNumber)
    (hx : q.toSciNumber o = some x) :
    x.base = o.base ∧ (∀ d ∈ x.digits, d.toNat < o.base.toNat) ∧
      (∀ h : 0 < x.digits.size, x.digits[0]'h ≠ 0) := by
  by_cases hv : o.valid = true
  swap
  · have hv' : o.valid = false := by simpa using hv
    unfold toSciNumber at hx
    rw [hv'] at hx
    simp at hx
  obtain ⟨hb2, _⟩ := valid_base hv
  unfold toSciNumber at hx
  rw [hv] at hx
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hx
  -- the three shapes of a result
  have zero_case : ∀ (neg : Bool) (sc : Int),
      x = ⟨neg, o.base, #[], sc⟩ → x.base = o.base ∧ (∀ d ∈ x.digits, d.toNat < o.base.toNat) ∧
        (∀ h : 0 < x.digits.size, x.digits[0]'h ≠ 0) := by
    rintro neg sc rfl
    refine ⟨rfl, ?_, ?_⟩
    · intro d hd; simp at hd
    · intro h; simp at h
  have digits_case : ∀ (r : AzInt) (sc : Int), r.abs ≠ 0 →
      x = ⟨!r.sign, o.base, (r.abs.limbDigits o.base).reverse, sc⟩ →
      x.base = o.base ∧ (∀ d ∈ x.digits, d.toNat < o.base.toNat) ∧
        (∀ h : 0 < x.digits.size, x.digits[0]'h ≠ 0) := by
    rintro r sc hr rfl
    exact ⟨rfl, digits_rev_lt_base o.base hb2 r.abs, digits_rev_head_ne_zero o.base hb2 r.abs hr⟩
  have pop_case : ∀ (r : AzInt) (sc : Int) (p : ℕ), r.abs ≠ 0 →
      (r.abs.limbDigits o.base).reverse.size = p + 1 →
      x = ⟨!r.sign, o.base, (r.abs.limbDigits o.base).reverse.pop, sc⟩ →
      x.base = o.base ∧ (∀ d ∈ x.digits, d.toNat < o.base.toNat) ∧
        (∀ h : 0 < x.digits.size, x.digits[0]'h ≠ 0) := by
    rintro r sc p hr hsz rfl
    refine ⟨rfl, ?_, ?_⟩
    · intro d hd
      apply digits_rev_lt_base o.base hb2 r.abs d
      rw [Array.mem_def, Array.toList_pop] at hd
      rw [Array.mem_def]
      exact List.mem_of_mem_dropLast hd
    · intro h
      rw [Array.getElem_pop]
      exact digits_rev_head_ne_zero o.base hb2 r.abs hr _
  by_cases h0 : q.num = 0
  · rw [ite_eq_left h0] at hx
    exact zero_case _ _ (Option.some.inj hx).symm
  · rw [ite_eq_right h0] at hx
    rcases hsz : sizeScale o.base q o.size (floorLogBaseAbs o.base q) with _ | ⟨scale, prec⟩
    · rw [hsz] at hx; simp at hx
    · rw [hsz] at hx
      simp only [] at hx
      by_cases hn : (scaledRound q o.base scale o.mode).1.abs = 0
      · rw [ite_eq_left hn] at hx
        exact zero_case _ _ (Option.some.inj hx).symm
      · rw [ite_eq_right hn] at hx
        revert hx
        rcases hsize : o.size with _ | p | s <;> intro hx <;> (try simp only [] at hx)
        · exact digits_case _ _ hn (Option.some.inj hx).symm
        · by_cases hp : ((scaledRound q o.base scale o.mode).1.abs.limbDigits o.base).reverse.size
              = p + 1
          · rw [ite_eq_left hp] at hx
            exact pop_case _ _ p hn hp (Option.some.inj hx).symm
          · rw [ite_eq_right hp] at hx
            exact digits_case _ _ hn (Option.some.inj hx).symm
        · exact digits_case _ _ hn (Option.some.inj hx).symm

end Azurite.AzRat
