/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Equiv.Conversion

/-!
# The floats of a fixed precision as a rounding target

`floatSet p` is the set of values of the non-`NaN` floats of precision `p` (zero and the
infinities included).  It equals `precisionSet 2 p ∪ {⊤, ⊥}` (`floatSet_eq`), which makes it a
`RoundingTarget` whose rounding of a real agrees with `precisionSet 2 p`'s
(`val_round_floatSet`).

`ofEReal p mode x` is the (noncomputable) float of precision `p` whose value is `x` rounded
with `mode`; `ofVal` extends it to `Option EReal` with `none ↦ nan`.  Since the representation
of a given value at a given precision is unique (`toVal_injective`), this pins down the
computable conversions: `ofAzRatRound_eq_ofEReal`, and `ofVal_toVal` says rounding a float's
own value gives the float back.
-/

namespace Azurite.AzFloat

open RoundingTarget

/-! ### The set -/

/-- The values of the non-`NaN` floats of precision `p`, zero and `±∞` included. -/
def floatSet (p : ℕ) : Set EReal :=
  {e | ∃ x : AzFloat, (x.precision? = some p ∨ x.precision? = none) ∧ x.toVal = some e}

/-- A valid significand lies in `[2^(B−1), 2^B)` for `B = alignedBits p`. -/
theorem toNat_bounds_of_valid {p : ℕ} {m : AzNat} (hv : FiniteValid p m) :
    2 ^ (alignedBits p - 1) ≤ m.toNat ∧ m.toNat < 2 ^ alignedBits p := by
  have hs := hv.size_eq
  have hB : 0 < alignedBits p := lt_of_lt_of_le hv.pos (le_alignedBits p)
  rw [← AzNat.size_toNat] at hs
  constructor
  · rw [← Nat.lt_size, hs]; omega
  · rw [← Nat.size_le, hs]

theorem floatSet_eq (p : ℕ) [NeZero p] : floatSet p = precisionSet 2 p ∪ {⊤, ⊥} := by
  have hp : 0 < p := Nat.pos_of_ne_zero (NeZero.ne p)
  ext v
  constructor
  · rintro ⟨x, hprec, hval⟩
    cases x with
    | nan => simp at hval
    | infinity s =>
      simp only [toVal_infinity, Option.some.injEq] at hval
      cases s <;> simp [← hval]
    | zero =>
      simp only [toVal_zero, Option.some.injEq] at hval
      exact Or.inl (Or.inl hval.symm)
    | finite s e p' m hv =>
      simp only [precision?, Option.some.injEq, reduceCtorEq, or_false] at hprec
      rw [hprec] at hv
      simp only [toVal_finite, Option.some.injEq] at hval
      rw [← hval]
      refine Or.inl (Or.inr ?_)
      obtain ⟨c, hc⟩ := hv.dvd
      obtain ⟨hlo, hhi⟩ := toNat_bounds_of_valid hv
      have hB := le_alignedBits p
      have hcpos : c ≠ 0 := by
        rintro rfl
        rw [mul_zero] at hc
        have : 0 < m.toNat := lt_of_lt_of_le (Nat.two_pow_pos _) hlo
        omega
      have hclt : c < 2 ^ p := by
        have h1 : 2 ^ (alignedBits p - p) * c < 2 ^ alignedBits p := hc ▸ hhi
        have h2 : (2 : ℕ) ^ alignedBits p = 2 ^ (alignedBits p - p) * 2 ^ p := by
          rw [← pow_add]; congr 1; omega
        rw [h2] at h1
        exact lt_of_mul_lt_mul_left h1 (Nat.zero_le _)
      refine ⟨if s then (c : ℤ) else -(c : ℤ), e.toInt - p, ?_, ?_, ?_⟩
      · cases s <;> simp [hcpos]
      · cases s <;> simp only [Bool.false_eq_true, ↓reduceIte, abs_neg, Nat.abs_cast] <;>
          exact_mod_cast hclt
      · unfold finiteVal
        rw [hv.size_eq, hc]
        have h2 : (2 : ℝ) ^ (e.toInt - p)
            = 2 ^ (e.toInt - alignedBits p) * 2 ^ ((alignedBits p - p : ℕ) : ℤ) := by
          rw [← zpow_add₀ (by norm_num)]; congr 1; rw [Nat.cast_sub hB]; ring
        apply congrArg
        push_cast
        rw [h2, zpow_natCast]
        cases s <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> ring
  · rintro (h | h)
    · rcases h with h0 | ⟨m, k, hm, hlt, hv⟩
      · exact ⟨zero, Or.inr rfl, by rw [toVal_zero, h0]⟩
      · -- the float `sign m, exponent k + |m|.size, significand |m|`
        have hsz : (AzNat.ofNat m.natAbs).size ≤ p := by
          rw [AzNat.size_ofNat, Nat.size_le]
          have : (m.natAbs : ℤ) < (2 : ℤ) ^ p := by rw [Int.natCast_natAbs]; exact hlt
          exact_mod_cast this
        have hne : AzNat.ofNat m.natAbs ≠ 0 := by
          intro h
          have := congrArg AzNat.toNat h
          rw [AzNat.toNat_ofNat, AzNat.toNat_zero] at this
          exact hm (Int.natAbs_eq_zero.mp this)
        refine ⟨mkFinite (decide (0 ≤ m)) (AzInt.ofInt (k + (AzNat.ofNat m.natAbs).size)) p
          (AzNat.ofNat m.natAbs), Or.inl (precision?_mkFinite _ _ _ _ hne hsz), ?_⟩
        rw [toVal_mkFinite _ _ _ _ hne, ← hv]
        congr 2
        unfold finiteVal
        rw [AzInt.toInt_ofInt, AzNat.toNat_ofNat, add_sub_cancel_right]
        congr 1
        rcases le_or_gt 0 m with hm0 | hm0
        · rw [ite_eq_left (decide_eq_true hm0), Nat.cast_natAbs,
            abs_of_nonneg (by exact_mod_cast hm0), one_mul]
        · rw [ite_eq_right (by simpa using hm0.not_ge), Nat.cast_natAbs,
            abs_of_neg (by exact_mod_cast hm0)]
          push_cast
          ring
    · rcases h with rfl | rfl
      · exact ⟨infinity true, Or.inr rfl, rfl⟩
      · exact ⟨infinity false, Or.inr rfl, rfl⟩

/-! ### Adjoining the infinities to a target -/

theorem isLeast_union_top_bot {S : Set EReal} {x : ℝ} {m : EReal}
    (h : IsLeast {s | s ∈ S ∧ (x : EReal) ≤ s} m) :
    IsLeast {s | s ∈ S ∪ {⊤, ⊥} ∧ (x : EReal) ≤ s} m := by
  refine ⟨⟨Or.inl h.1.1, h.1.2⟩, ?_⟩
  rintro s ⟨hs | hs, hxs⟩
  · exact h.2 ⟨hs, hxs⟩
  · rcases hs with rfl | rfl
    · exact le_top
    · exact absurd hxs (by simp)

theorem isGreatest_union_top_bot {S : Set EReal} {x : ℝ} {m : EReal}
    (h : IsGreatest {s | s ∈ S ∧ s ≤ (x : EReal)} m) :
    IsGreatest {s | s ∈ S ∪ {⊤, ⊥} ∧ s ≤ (x : EReal)} m := by
  refine ⟨⟨Or.inl h.1.1, h.1.2⟩, ?_⟩
  rintro s ⟨hs | hs, hsx⟩
  · exact h.2 ⟨hs, hsx⟩
  · rcases hs with rfl | rfl
    · exact absurd hsx (by simp)
    · exact bot_le

theorem mem_floatSet_of_mem_precisionSet (p : ℕ) [NeZero p] {e : EReal}
    (h : e ∈ precisionSet 2 p) : e ∈ floatSet p := by
  rw [floatSet_eq]; exact Or.inl h

theorem eq_top_or_bot_of_not_mem (p : ℕ) [NeZero p] {e : EReal} (he : e ∈ floatSet p)
    (h : e ∉ precisionSet 2 p) : e = ⊤ ∨ e = ⊥ := by
  rw [floatSet_eq] at he
  rcases he with he | he
  · exact absurd he h
  · simpa using he

theorem top_not_mem_precisionSet (p : ℕ) [NeZero p] : (⊤ : EReal) ∉ precisionSet 2 p := by
  intro h
  obtain ⟨r, hr⟩ := precisionSet_exists_real ⟨⊤, h⟩
  exact EReal.coe_ne_top r hr

theorem bot_not_mem_precisionSet (p : ℕ) [NeZero p] : (⊥ : EReal) ∉ precisionSet 2 p := by
  intro h
  obtain ⟨r, hr⟩ := precisionSet_exists_real ⟨⊥, h⟩
  exact EReal.coe_ne_bot r hr

theorem neg_mem_precisionSet_iff (p : ℕ) [NeZero p] (e : EReal) :
    -e ∈ precisionSet 2 p ↔ e ∈ precisionSet 2 p :=
  ⟨fun h => by simpa using precisionSet_neg_mem h, precisionSet_neg_mem⟩

theorem floatSet_neg_mem (p : ℕ) [NeZero p] {e : EReal} (h : e ∈ floatSet p) : -e ∈ floatSet p := by
  rw [floatSet_eq] at h ⊢
  rcases h with h | h
  · exact Or.inl (precisionSet_neg_mem h)
  · rcases h with rfl | rfl <;> simp

open Classical in
/-- The tiebreak: `precisionSet`'s on two finite candidates; a finite candidate beats an
infinite one; two infinite candidates give the first.  Infinities never tie, so only the first
clause matters for rounding; the others make the rule commute with negation. -/
noncomputable def floatTiebreak (p : ℕ) [NeZero p] (a c : ↥(floatSet p)) : ↥(floatSet p) :=
  if ha : a.val ∈ precisionSet 2 p then
    if hc : c.val ∈ precisionSet 2 p then
      ⟨(precTiebreak ⟨a.val, ha⟩ ⟨c.val, hc⟩).val,
        mem_floatSet_of_mem_precisionSet p (precTiebreak ⟨a.val, ha⟩ ⟨c.val, hc⟩).property⟩
    else a
  else if c.val ∈ precisionSet 2 p then c
  else a

noncomputable instance floatRoundingTarget (p : ℕ) [NeZero p] : RoundingTarget (floatSet p) where
  existsLeastGE x := by
    obtain ⟨m, hm⟩ := existsLeastGE (S := precisionSet 2 p) x
    refine ⟨m, ?_⟩
    rw [floatSet_eq]
    exact isLeast_union_top_bot hm
  existsGreatestLE x := by
    obtain ⟨m, hm⟩ := existsGreatestLE (S := precisionSet 2 p) x
    refine ⟨m, ?_⟩
    rw [floatSet_eq]
    exact isGreatest_union_top_bot hm
  tiebreak := floatTiebreak p
  tiebreak_mem a c := by
    unfold floatTiebreak
    split_ifs with ha hc hc
    · rcases tiebreak_mem (S := precisionSet 2 p) ⟨a.val, ha⟩ ⟨c.val, hc⟩ with h | h
      · left
        apply Subtype.ext
        have h' : precTiebreak ⟨a.val, ha⟩ ⟨c.val, hc⟩ = ⟨a.val, ha⟩ := h
        show (precTiebreak ⟨a.val, ha⟩ ⟨c.val, hc⟩).val = a.val
        rw [h']
      · right
        apply Subtype.ext
        have h' : precTiebreak ⟨a.val, ha⟩ ⟨c.val, hc⟩ = ⟨c.val, hc⟩ := h
        show (precTiebreak ⟨a.val, ha⟩ ⟨c.val, hc⟩).val = c.val
        rw [h']
    · exact Or.inl rfl
    · exact Or.inr rfl
    · exact Or.inl rfl

/-- `floatSet p` is symmetric: `0 ∈ floatSet p`, it is closed under negation, and the tiebreak
commutes with negation.  Hence `round_neg` applies: rounding `-x` with a mode is the negation
of rounding `x` with the negated mode. -/
noncomputable instance floatSymmetricRoundingTarget (p : ℕ) [NeZero p] :
    SymmetricRoundingTarget (floatSet p) where
  zero_mem := ⟨zero, Or.inr rfl, rfl⟩
  neg_mem := floatSet_neg_mem p
  tiebreak_neg a c hne := by
    show (floatTiebreak p ⟨-a.val, floatSet_neg_mem p a.property⟩
        ⟨-c.val, floatSet_neg_mem p c.property⟩).val = -(floatTiebreak p c a).val
    unfold floatTiebreak
    by_cases ha : a.val ∈ precisionSet 2 p
    · have ha' : -a.val ∈ precisionSet 2 p := precisionSet_neg_mem ha
      by_cases hc : c.val ∈ precisionSet 2 p
      · have hc' : -c.val ∈ precisionSet 2 p := precisionSet_neg_mem hc
        simp only [ha', hc', ha, hc, ↓reduceDIte]
        exact SymmetricRoundingTarget.tiebreak_neg (S := precisionSet 2 p) ⟨a.val, ha⟩
          ⟨c.val, hc⟩ hne
      · have hc' : -c.val ∉ precisionSet 2 p := fun h => hc ((neg_mem_precisionSet_iff p _).mp h)
        simp only [ha', hc', ha, hc, ↓reduceDIte, ↓reduceIte]
    · have ha' : -a.val ∉ precisionSet 2 p := fun h => ha ((neg_mem_precisionSet_iff p _).mp h)
      by_cases hc : c.val ∈ precisionSet 2 p
      · have hc' : -c.val ∈ precisionSet 2 p := precisionSet_neg_mem hc
        simp only [ha', hc', ha, hc, ↓reduceDIte, ↓reduceIte]
      · have hc' : -c.val ∉ precisionSet 2 p := fun h => hc ((neg_mem_precisionSet_iff p _).mp h)
        simp only [ha', hc', ha, hc, ↓reduceDIte, ↓reduceIte]
        -- both infinite and not opposite: equal
        rcases eq_top_or_bot_of_not_mem p a.property ha with hat | hab <;>
          rcases eq_top_or_bot_of_not_mem p c.property hc with hct | hcb
        · rw [hat, hct]
        · exact absurd (by rw [hat, hcb]; simp) hne
        · exact absurd (by rw [hab, hct]; simp) hne
        · rw [hab, hcb]

/-! ### Rounding agrees with `precisionSet 2 p` -/

theorem val_roundFloor_floatSet (p : ℕ) [NeZero p] (x : ℝ) :
    (roundFloor (floatSet p) x).val = (roundFloor (precisionSet 2 p) x).val := by
  apply (isGreatest_roundFloor (floatSet p) x).unique
  have := isGreatest_union_top_bot (isGreatest_roundFloor (precisionSet 2 p) x)
  rwa [← floatSet_eq] at this

theorem val_roundCeiling_floatSet (p : ℕ) [NeZero p] (x : ℝ) :
    (roundCeiling (floatSet p) x).val = (roundCeiling (precisionSet 2 p) x).val := by
  apply (isLeast_roundCeiling (floatSet p) x).unique
  have := isLeast_union_top_bot (isLeast_roundCeiling (precisionSet 2 p) x)
  rwa [← floatSet_eq] at this

theorem val_round_floatSet (p : ℕ) [NeZero p] (mode : RoundingMode) (x : ℝ) :
    (RoundingTarget.round (floatSet p) mode x).val
      = (RoundingTarget.round (precisionSet 2 p) mode x).val := by
  have hF := val_roundFloor_floatSet p x
  have hC := val_roundCeiling_floatSet p x
  cases mode with
  | Floor => exact hF
  | Ceiling => exact hC
  | Down => unfold RoundingTarget.round; split_ifs <;> assumption
  | Up => unfold RoundingTarget.round; split_ifs <;> assumption
  | Nearest =>
    unfold RoundingTarget.round
    simp only [hF, hC]
    cases h : compare ((x : EReal) - (roundFloor (precisionSet 2 p) x).val)
        ((roundCeiling (precisionSet 2 p) x).val - (x : EReal))
    · exact hF
    · -- tie
      have hFm : (roundFloor (floatSet p) x).val ∈ precisionSet 2 p := by
        rw [hF]; exact (roundFloor (precisionSet 2 p) x).property
      have hCm : (roundCeiling (floatSet p) x).val ∈ precisionSet 2 p := by
        rw [hC]; exact (roundCeiling (precisionSet 2 p) x).property
      show (floatTiebreak p _ _).val = (precTiebreak _ _).val
      unfold floatTiebreak
      rw [dite_eq_left hFm, dite_eq_left hCm]
      have e1 : (⟨(roundFloor (floatSet p) x).val, hFm⟩ : ↥(precisionSet 2 p))
          = roundFloor (precisionSet 2 p) x := Subtype.ext hF
      have e2 : (⟨(roundCeiling (floatSet p) x).val, hCm⟩ : ↥(precisionSet 2 p))
          = roundCeiling (precisionSet 2 p) x := Subtype.ext hC
      show (precTiebreak ⟨(roundFloor (floatSet p) x).val, hFm⟩
        ⟨(roundCeiling (floatSet p) x).val, hCm⟩).val = _
      rw [e1, e2]
    · exact hC

/-! ### The noncomputable conversions -/

open Classical in
/-- The float of precision `p` whose value is `x` rounded with `mode` (`±∞` stay). -/
noncomputable def ofEReal (p : ℕ) [NeZero p] (mode : RoundingMode) (x : EReal) : AzFloat :=
  if hx : ∃ r : ℝ, (r : EReal) = x then
    Classical.choose (RoundingTarget.round (floatSet p) mode hx.choose).property
  else if x = ⊤ then infinity true else infinity false

/-- `ofEReal` on `Option EReal`, with `none ↦ nan`. -/
noncomputable def ofVal (p : ℕ) [NeZero p] (mode : RoundingMode) : Option EReal → AzFloat
  | none => nan
  | some x => ofEReal p mode x

theorem ofEReal_spec (p : ℕ) [NeZero p] (mode : RoundingMode) (r : ℝ) :
    ((ofEReal p mode r).precision? = some p ∨ (ofEReal p mode r).precision? = none) ∧
      (ofEReal p mode r).toVal = some (RoundingTarget.round (floatSet p) mode r).val := by
  unfold ofEReal
  have hx : ∃ r' : ℝ, (r' : EReal) = (r : EReal) := ⟨r, rfl⟩
  rw [dite_eq_left hx]
  have hr : hx.choose = r := EReal.coe_eq_coe_iff.mp hx.choose_spec
  obtain ⟨h1, h2⟩ :=
    Classical.choose_spec (RoundingTarget.round (floatSet p) mode hx.choose).property
  refine ⟨h1, ?_⟩
  rw [h2, hr]

theorem toVal_ofEReal_coe (p : ℕ) [NeZero p] (mode : RoundingMode) (r : ℝ) :
    (ofEReal p mode r).toVal = some (RoundingTarget.round (precisionSet 2 p) mode r).val := by
  rw [(ofEReal_spec p mode r).2, val_round_floatSet]

@[simp] theorem ofEReal_top (p : ℕ) [NeZero p] (mode : RoundingMode) :
    ofEReal p mode ⊤ = infinity true := by
  unfold ofEReal
  rw [dite_eq_right (by rintro ⟨r, hr⟩; exact EReal.coe_ne_top r hr), ite_eq_left rfl]

@[simp] theorem ofEReal_bot (p : ℕ) [NeZero p] (mode : RoundingMode) :
    ofEReal p mode ⊥ = infinity false := by
  unfold ofEReal
  rw [dite_eq_right (by rintro ⟨r, hr⟩; exact EReal.coe_ne_bot r hr), ite_eq_right (by simp)]

@[simp] theorem ofVal_none (p : ℕ) [NeZero p] (mode : RoundingMode) : ofVal p mode none = nan := rfl

@[simp] theorem ofVal_some (p : ℕ) [NeZero p] (mode : RoundingMode) (x : EReal) :
    ofVal p mode (some x) = ofEReal p mode x := rfl

/-! ### Uniqueness of the representation -/

theorem finiteVal_pos_iff (s : Bool) (e : AzInt) (m : AzNat) (hm : m ≠ 0) :
    0 < finiteVal s e m ↔ s = true := by
  unfold finiteVal
  have h2 : (0 : ℝ) < (2 : ℝ) ^ (e.toInt - m.size) := zpow_pos (by norm_num) _
  have hm' : (0 : ℝ) < m.toNat := by exact_mod_cast Nat.pos_of_ne_zero (toNat_ne_zero_of_ne_zero hm)
  cases s
  · simp only [Bool.false_eq_true, ↓reduceIte, iff_false, not_lt]
    nlinarith
  · simp only [↓reduceIte, one_mul, iff_true]
    positivity

theorem abs_finiteVal_bounds (s : Bool) (e : AzInt) {p : ℕ} {m : AzNat} (hv : FiniteValid p m) :
    (2 : ℝ) ^ (e.toInt - 1) ≤ |finiteVal s e m| ∧ |finiteVal s e m| < (2 : ℝ) ^ e.toInt := by
  obtain ⟨hlo, hhi⟩ := toNat_bounds_of_valid hv
  have hB : 0 < alignedBits p := lt_of_lt_of_le hv.pos (le_alignedBits p)
  have habs : |finiteVal s e m| = (m.toNat : ℝ) * (2 : ℝ) ^ (e.toInt - alignedBits p) := by
    unfold finiteVal
    rw [hv.size_eq]
    have h2 : (0 : ℝ) < (2 : ℝ) ^ (e.toInt - alignedBits p) := zpow_pos (by norm_num) _
    cases s <;> simp [abs_mul, abs_of_pos h2]
  rw [habs]
  have h2 : (0 : ℝ) < (2 : ℝ) ^ (e.toInt - alignedBits p) := zpow_pos (by norm_num) _
  constructor
  · have hlo' : (2 : ℝ) ^ (alignedBits p - 1) ≤ m.toNat := by exact_mod_cast hlo
    calc (2 : ℝ) ^ (e.toInt - 1)
        = (2 : ℝ) ^ ((alignedBits p - 1 : ℕ) : ℤ) * 2 ^ (e.toInt - alignedBits p) := by
          rw [← zpow_add₀ (by norm_num)]; congr 1; rw [Nat.cast_sub hB]; ring
      _ ≤ (m.toNat : ℝ) * 2 ^ (e.toInt - alignedBits p) := by
          rw [zpow_natCast]; exact mul_le_mul_of_nonneg_right hlo' h2.le
  · have hhi' : (m.toNat : ℝ) < (2 : ℝ) ^ alignedBits p := by exact_mod_cast hhi
    calc (m.toNat : ℝ) * 2 ^ (e.toInt - alignedBits p)
        < (2 : ℝ) ^ alignedBits p * 2 ^ (e.toInt - alignedBits p) :=
          mul_lt_mul_of_pos_right hhi' h2
      _ = (2 : ℝ) ^ e.toInt := by
          rw [← zpow_natCast, ← zpow_add₀ (by norm_num)]; congr 1; ring

/-- Two valid finite representations of the same value at the same precision coincide. -/
theorem finite_eq_of_finiteVal_eq {s₁ s₂ : Bool} {e₁ e₂ : AzInt} {p : ℕ} {m₁ m₂ : AzNat}
    (h₁ : FiniteValid p m₁) (h₂ : FiniteValid p m₂)
    (h : finiteVal s₁ e₁ m₁ = finiteVal s₂ e₂ m₂) : s₁ = s₂ ∧ e₁ = e₂ ∧ m₁ = m₂ := by
  have hm₁ : m₁ ≠ 0 := ne_zero_of_size_pos (by
    rw [h₁.size_eq]; exact lt_of_lt_of_le h₁.pos (le_alignedBits p))
  have hm₂ : m₂ ≠ 0 := ne_zero_of_size_pos (by
    rw [h₂.size_eq]; exact lt_of_lt_of_le h₂.pos (le_alignedBits p))
  have hs : s₁ = s₂ := by
    have := finiteVal_pos_iff s₁ e₁ m₁ hm₁
    rw [h, finiteVal_pos_iff s₂ e₂ m₂ hm₂] at this
    cases s₁ <;> cases s₂ <;> simp_all
  subst hs
  obtain ⟨hlo₁, hhi₁⟩ := abs_finiteVal_bounds s₁ e₁ h₁
  obtain ⟨hlo₂, hhi₂⟩ := abs_finiteVal_bounds s₁ e₂ h₂
  rw [h] at hlo₁ hhi₁
  have he : e₁.toInt = e₂.toInt := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · have : (2 : ℝ) ^ e₁.toInt ≤ (2 : ℝ) ^ (e₂.toInt - 1) :=
        zpow_le_zpow_right₀ (by norm_num) (by omega)
      linarith
    · have : (2 : ℝ) ^ e₂.toInt ≤ (2 : ℝ) ^ (e₁.toInt - 1) :=
        zpow_le_zpow_right₀ (by norm_num) (by omega)
      linarith
  have he' : e₁ = e₂ := by
    rw [← AzInt.ofInt_toInt e₁, ← AzInt.ofInt_toInt e₂, he]
  subst he'
  refine ⟨rfl, rfl, ?_⟩
  unfold finiteVal at h
  rw [h₁.size_eq, h₂.size_eq] at h
  have h2 : (0 : ℝ) < (2 : ℝ) ^ (e₁.toInt - alignedBits p) := zpow_pos (by norm_num) _
  have hsign : (if s₁ then (1 : ℝ) else -1) ≠ 0 := by cases s₁ <;> simp
  have : (m₁.toNat : ℝ) = m₂.toNat := by
    have h' := mul_right_cancel₀ h2.ne' h
    exact mul_left_cancel₀ hsign h'
  exact AzNat.toNat_injective (by exact_mod_cast this)

/-- The representation of a value at a given precision is unique: two floats whose precisions
are `p` (or absent: `NaN`, `±∞`, zero) and whose values agree are equal. -/
theorem toVal_injective (p : ℕ) {x y : AzFloat} (hx : x.precision? = some p ∨ x.precision? = none)
    (hy : y.precision? = some p ∨ y.precision? = none) (h : x.toVal = y.toVal) : x = y := by
  cases x with
  | nan =>
    cases y with
    | nan => rfl
    | infinity _ => simp at h
    | zero => simp at h
    | finite _ _ _ _ _ => simp at h
  | infinity s =>
    cases y with
    | nan => simp at h
    | infinity t =>
      simp only [toVal_infinity, Option.some.injEq] at h
      cases s <;> cases t <;> simp_all
    | zero =>
      simp only [toVal_infinity, toVal_zero, Option.some.injEq] at h
      cases s <;> simp at h
    | finite _ _ _ _ _ =>
      simp only [toVal_infinity, toVal_finite, Option.some.injEq] at h
      cases s
      · exact absurd h.symm (EReal.coe_ne_bot _)
      · exact absurd h.symm (EReal.coe_ne_top _)
  | zero =>
    cases y with
    | nan => simp at h
    | infinity t =>
      simp only [toVal_infinity, toVal_zero, Option.some.injEq] at h
      cases t <;> simp at h
    | zero => rfl
    | finite t e q m hv =>
      simp only [toVal_zero, toVal_finite, Option.some.injEq] at h
      have hm : m ≠ 0 := ne_zero_of_size_pos (by
        rw [hv.size_eq]; exact lt_of_lt_of_le hv.pos (le_alignedBits q))
      have := (abs_finiteVal_bounds t e hv).1
      have h0 : finiteVal t e m = 0 := EReal.coe_eq_zero.mp h.symm
      rw [h0, abs_zero] at this
      have h2 : (0 : ℝ) < (2 : ℝ) ^ (e.toInt - 1) := zpow_pos (by norm_num) _
      linarith
  | finite s e q m hv =>
    cases y with
    | nan => simp at h
    | infinity t =>
      simp only [toVal_infinity, toVal_finite, Option.some.injEq] at h
      cases t
      · exact absurd h (EReal.coe_ne_bot _)
      · exact absurd h (EReal.coe_ne_top _)
    | zero =>
      simp only [toVal_zero, toVal_finite, Option.some.injEq] at h
      have := (abs_finiteVal_bounds s e hv).1
      have h0 : finiteVal s e m = 0 := EReal.coe_eq_zero.mp h
      rw [h0, abs_zero] at this
      have h2 : (0 : ℝ) < (2 : ℝ) ^ (e.toInt - 1) := zpow_pos (by norm_num) _
      linarith
    | finite t f q' m' hv' =>
      simp only [precision?, Option.some.injEq, reduceCtorEq, or_false] at hx hy
      subst hx hy
      simp only [toVal_finite, Option.some.injEq, EReal.coe_eq_coe_iff] at h
      obtain ⟨rfl, rfl, rfl⟩ := finite_eq_of_finiteVal_eq hv hv' h
      rfl

/-! ### The computable conversions agree with `ofEReal` -/

theorem precision?_ofAzRatRound' (p : ℕ) [NeZero p] (q : AzRat) (mode : RoundingMode) :
    (ofAzRatRound q p mode).1.precision? = some p ∨
      (ofAzRatRound q p mode).1.precision? = none := by
  have hp : 0 < p := Nat.pos_of_ne_zero (NeZero.ne p)
  by_cases h0 : q.num = 0
  · unfold ofAzRatRound
    rw [ite_eq_right hp.ne', ite_eq_left h0]
    exact Or.inr rfl
  · exact Or.inl (precision?_ofAzRatRound q p hp mode h0)

/-- Rounding a rational computably is rounding its value. -/
theorem ofAzRatRound_eq_ofEReal (p : ℕ) [NeZero p] (q : AzRat) (mode : RoundingMode) :
    (ofAzRatRound q p mode).1 = ofEReal p mode (AzRat.toRat q : ℝ) :=
  toVal_injective p (precision?_ofAzRatRound' p q mode) (ofEReal_spec p mode _).1
    (by rw [toVal_ofAzRatRound, toVal_ofEReal_coe])

/-- Rounding a float's own value at its precision gives the float back. -/
theorem ofVal_toVal (p : ℕ) [NeZero p] (mode : RoundingMode) (x : AzFloat)
    (hx : x.precision? = some p ∨ x.precision? = none) : ofVal p mode x.toVal = x := by
  cases hv : x.toVal with
  | none =>
    cases x <;> simp at hv
    rfl
  | some v =>
    rw [ofVal_some]
    have hmem : v ∈ floatSet p := ⟨x, hx, hv⟩
    rw [floatSet_eq] at hmem
    rcases hmem with hmem | hmem
    · obtain ⟨r, hr⟩ := precisionSet_exists_real ⟨v, hmem⟩
      simp only at hr
      rw [← hr]
      refine toVal_injective p (ofEReal_spec p mode r).1 hx ?_
      rw [toVal_ofEReal_coe, hv, ← hr, val_round_of_mem _ mode (hr ▸ hmem)]
    · rcases hmem with rfl | rfl
      · rw [ofEReal_top]
        cases x <;> simp at hv
        rename_i s
        cases s <;> simp_all
      · rw [ofEReal_bot]
        cases x <;> simp at hv
        rename_i s
        cases s <;> simp_all

/-! ### Lifting real functions to floats -/

/-- Round a specification value to a float of precision `p`, with the comparison of the result
against it (`.eq` for `NaN` and the infinities, which are exact). -/
noncomputable def roundVal (p : ℕ) [NeZero p] (mode : RoundingMode) (v : Option EReal) :
    AzFloat × Ordering :=
  let x := ofVal p mode v
  (x, match x.toVal, v with
    | some a, some b => compare a b
    | _, _ => .eq)

open Classical in
/-- Apply a real function to an extended real; `±∞` go to the given values (`NaN` by
default). -/
noncomputable def applyReal (f : ℝ → ℝ) (top bot : Option EReal) (v : EReal) : Option EReal :=
  if v = ⊤ then top else if v = ⊥ then bot else some (f v.toReal)

/-- Lift a function on specification values (`none` is `NaN`) to floats: the value of `x` is
mapped through `f` and the result rounded to precision `p` with `mode`; the `Ordering` compares
the rounded result with the exact one.  Every `AzFloat` operation is specified as a computable
implementation of such a lift. -/
noncomputable def liftVal (f : EReal → Option EReal) (x : AzFloat) (p : ℕ) [NeZero p]
    (mode : RoundingMode) : AzFloat × Ordering :=
  roundVal p mode (x.toVal.bind f)

/-- Lift a real function to floats (`±∞ ↦ NaN` unless `top`/`bot` say otherwise). -/
noncomputable def lift (f : ℝ → ℝ) (top bot : Option EReal := none) (x : AzFloat) (p : ℕ)
    [NeZero p] (mode : RoundingMode) : AzFloat × Ordering :=
  liftVal (applyReal f top bot) x p mode

/-- Lift a total function on extended reals (never `NaN` on a non-`NaN` input): `EReal`'s own
conventions decide the infinities, as for negation. -/
noncomputable def liftE (f : EReal → EReal) (x : AzFloat) (p : ℕ) [NeZero p]
    (mode : RoundingMode) : AzFloat × Ordering :=
  liftVal (fun v => some (f v)) x p mode

/-- Lift a binary function on specification values to floats. -/
noncomputable def liftVal₂ (f : EReal → EReal → Option EReal) (x y : AzFloat) (p : ℕ)
    [NeZero p] (mode : RoundingMode) : AzFloat × Ordering :=
  roundVal p mode (x.toVal.bind fun a => y.toVal.bind fun b => f a b)

open Classical in
/-- Lift a binary real function to floats (any infinity gives `NaN`; arithmetic with its own
rules for the infinities goes through `liftVal₂`). -/
noncomputable def lift₂ (f : ℝ → ℝ → ℝ) (x y : AzFloat) (p : ℕ) [NeZero p]
    (mode : RoundingMode) : AzFloat × Ordering :=
  liftVal₂ (fun a b => if a = ⊤ ∨ a = ⊥ ∨ b = ⊤ ∨ b = ⊥ then none
    else some (f a.toReal b.toReal)) x y p mode

@[simp] theorem roundVal_none (p : ℕ) [NeZero p] (mode : RoundingMode) :
    roundVal p mode none = (nan, .eq) := rfl

theorem fst_roundVal (p : ℕ) [NeZero p] (mode : RoundingMode) (v : Option EReal) :
    (roundVal p mode v).1 = ofVal p mode v := rfl

/-- Rounding a real value: the result's value is the rounding and the tag compares it with the
exact value. -/
theorem roundVal_coe (p : ℕ) [NeZero p] (mode : RoundingMode) (r : ℝ) :
    (roundVal p mode (some (r : EReal))).1.toVal
        = some (RoundingTarget.round (floatSet p) mode r).val ∧
      (roundVal p mode (some (r : EReal))).2
        = compare (RoundingTarget.round (floatSet p) mode r).val (r : EReal) := by
  refine ⟨(ofEReal_spec p mode r).2, ?_⟩
  show (match (ofEReal p mode r).toVal, some (r : EReal) with
    | some a, some b => compare a b
    | _, _ => .eq) = _
  rw [(ofEReal_spec p mode r).2]

/-- Rounding a value already representable at precision `p` returns its float, exactly. -/
theorem roundVal_of_toVal (p : ℕ) [NeZero p] (mode : RoundingMode) (x : AzFloat) (v : EReal)
    (hx : x.precision? = some p ∨ x.precision? = none) (hv : x.toVal = some v) :
    roundVal p mode (some v) = (x, .eq) := by
  have h1 : ofVal p mode (some v) = x := by rw [← hv]; exact ofVal_toVal p mode x hx
  unfold roundVal
  simp only [h1, hv, compare_eq_iff_eq.mpr rfl]

@[simp] theorem liftVal_nan (f : EReal → Option EReal) (p : ℕ) [NeZero p]
    (mode : RoundingMode) : liftVal f nan p mode = (nan, .eq) := rfl

theorem applyReal_coe (f : ℝ → ℝ) (top bot : Option EReal) (r : ℝ) :
    applyReal f top bot r = some ((f r : ℝ) : EReal) := by
  unfold applyReal
  rw [ite_eq_right (EReal.coe_ne_top r), ite_eq_right (EReal.coe_ne_bot r), EReal.toReal_coe]

/-- On a finite float, `lift f` rounds `f` of its value. -/
theorem lift_coe (f : ℝ → ℝ) (top bot : Option EReal) (x : AzFloat) (p : ℕ) [NeZero p]
    (mode : RoundingMode) (r : ℝ) (hx : x.toVal = some (r : EReal)) :
    lift f top bot x p mode = roundVal p mode (some ((f r : ℝ) : EReal)) := by
  unfold lift liftVal
  rw [hx, Option.bind_some, applyReal_coe]

theorem precision?_neg (x : AzFloat) : (-x).precision? = x.precision? := by
  cases x <;> rfl

/-- Negation is the lift of `EReal` negation (so `-(±∞) = ∓∞` comes from `EReal`) at the
float's own precision, exact. -/
theorem neg_eq_lift (p : ℕ) [NeZero p] (mode : RoundingMode) (x : AzFloat)
    (hx : x.precision? = some p ∨ x.precision? = none) :
    liftE (fun v => -v) x p mode = (-x, .eq) := by
  have hx' : (-x).precision? = some p ∨ (-x).precision? = none := by rwa [precision?_neg]
  have h : x.toVal.bind (fun v => some (-v)) = (-x).toVal := by
    rw [toVal_neg]
    cases x.toVal <;> rfl
  unfold liftE liftVal
  rw [h]
  cases hv : (-x).toVal with
  | none =>
    cases x <;> simp [toVal_neg] at hv
    rfl
  | some v => exact roundVal_of_toVal p mode (-x) v hx' hv

end Azurite.AzFloat
