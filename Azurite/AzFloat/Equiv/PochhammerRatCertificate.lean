/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.PochhammerRatBracket
import Azurite.AzFloat.Equiv.PochhammerWidth
import Azurite.AzFloat.Equiv.PochhammerDyadic
import Azurite.AzFloat.Equiv.BetaRat
import Azurite.AzNat.Equiv.Compare
import Azurite.AzNat.Equiv.Pow2

/-!
# The Ziv certificate of Pochhammer's symbol of a rational

`pochRatApprox_cert`: at a rational `q` whose denominator is not a power of two
(`pochRatSpecial`) and `n ≥ 1`, some level of the bracket `pochRatApprox q n` is accepted by
`roundingPossible`.  Two ingredients: the bracket converges (`pochRatApprox_bracketConv`, from
`pochCoreOf_coreConv` and the right split `pochRatSplit_facts`), and the value is not dyadic
(`not_isDyadic_prod_rat`, `Equiv/PochhammerDyadic.lean`), hence no rounding boundary.

This file does not import the function it certifies: `AzFloat/PochhammerRat.lean` imports it.
-/

namespace Azurite.AzFloat

open Finset

/-- A vanishing factor. -/
theorem pochRatHasZero_spec {q : AzRat} {n : ℕ} (h : pochRatHasZero q n = true) :
    ∏ j ∈ range n, (((AzRat.toRat q : ℚ) : ℝ) + j) = 0 := by
  unfold pochRatHasZero at h
  rw [Bool.and_eq_true, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true,
    decide_eq_true_eq, Bool.not_eq_true', beq_iff_eq, AzNat.compare_eq_compare_toNat,
    AzNat.toNat_ofNat, Nat.compare_eq_lt] at h
  obtain ⟨⟨hd, hs⟩, hlt⟩ := h
  have hval : ((AzRat.toRat q : ℚ) : ℝ) = -(q.num.toNat : ℝ) := by
    rcases hs with h0 | hs
    · rw [coe_toRat_eq_zero_of_num_eq_zero q h0, h0, AzNat.toNat_zero]
      simp
    · rw [coe_toRat_eq_mkNorm_of_den_one q hd, AzNat.toInt_mkNorm, hs]
      simp
  refine prod_eq_zero (i := q.num.toNat) (mem_range.mpr hlt) ?_
  rw [hval]
  ring

theorem pochRatSplit_le (q : AzRat) (n : ℕ) : pochRatSplit q n ≤ n := by
  unfold pochRatSplit
  split_ifs <;> first | exact Nat.zero_le n | exact le_rfl | exact min_le_left _ _

/-- **`pochRatCore` answers with the sign and a positive enclosure of `|(q)ₙ|`.** -/
theorem pochRatCore_spec (q : AzRat) {n w : ℕ} (hw : 64 ≤ w) {neg : Bool} {r : Encl}
    (h : pochRatCore q n w = some (neg, r)) :
    IsEnclPos r ((if neg then -1 else 1) * ∏ j ∈ range n, (((AzRat.toRat q : ℚ) : ℝ) + j)) :=
  pochCoreOf_spec (fun V _ => lnGammaRatEncl_isEncl q V) (pochRatSplit_le q n) hw h

/-- The enclosures of a rational have widths `O(2^(−V))`. -/
theorem lnGammaRatEncl_level (q : AzRat) (V : ℕ) :
    AEncl (lnGammaRatEncl q V) ((AzRat.toRat q : ℚ) : ℝ)
      (4 * |((AzRat.toRat q : ℚ) : ℝ)| * (1 / 2 : ℝ) ^ V) := by
  have : NeZero (V + 32) := ⟨by omega⟩
  obtain ⟨l, hl, hl1, hl2⟩ := ofAzRatRound_floor_abs q (V + 32)
  obtain ⟨u, hu, hu1, hu2⟩ := ofAzRatRound_ceiling_abs q (V + 32)
  refine ⟨l, u, hl, hu, hl1, hu1, ?_⟩
  have hpow : (1 / 2 : ℝ) ^ (V + 32) ≤ (1 / 2 : ℝ) ^ V :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.le_add_right _ _)
  have := mul_le_mul_of_nonneg_left hpow (abs_nonneg ((AzRat.toRat q : ℚ) : ℝ))
  linarith

theorem pochRatHasZero_iff (q : AzRat) (n : ℕ) :
    pochRatHasZero q n = true ↔
      (q.den = 1 ∧ (q.num = 0 ∨ q.sign = false)) ∧ q.num.toNat < n := by
  unfold pochRatHasZero
  rw [Bool.and_eq_true, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true,
    decide_eq_true_eq, Bool.not_eq_true', beq_iff_eq, AzNat.compare_eq_compare_toNat,
    AzNat.toNat_ofNat, Nat.compare_eq_lt]

theorem azNat_le_iff (a b : AzNat) : a ≤ b ↔ a.toNat ≤ b.toNat := by
  change AzNat.compare a b ≠ Ordering.gt ↔ _
  rw [AzNat.compare_eq_compare_toNat]
  constructor
  · intro h
    exact not_lt.mp fun hlt => h (compare_gt_iff_gt.mpr hlt)
  · intro h hgt
    exact absurd (compare_gt_iff_gt.mp hgt) (not_lt.mpr h)

/-- **The split of `(q)ₙ` is right**: off the zeros, both rising factorials have a positive
first factor. -/
theorem pochRatSplit_facts (q : AzRat) {n : ℕ} (hz : pochRatHasZero q n = false) :
    (pochRatSplit q n ≠ 0 → 0 < 1 - ((AzRat.toRat q : ℚ) : ℝ) - (pochRatSplit q n : ℕ)) ∧
      (n - pochRatSplit q n ≠ 0 → 0 < ((AzRat.toRat q : ℚ) : ℝ) + (pochRatSplit q n : ℕ)) := by
  have hz' : ¬ ((q.den = 1 ∧ (q.num = 0 ∨ q.sign = false)) ∧ q.num.toNat < n) := by
    rw [← pochRatHasZero_iff, hz]
    simp
  have hd := den_pos_real q
  unfold pochRatSplit
  by_cases hs : q.sign = true
  · rw [ite_eq_left hs]
    refine ⟨fun h => absurd rfl h, fun h => ?_⟩
    have hn : 0 < n := by omega
    rw [Nat.cast_zero, add_zero]
    by_cases h0 : q.num = 0
    · exfalso
      refine hz' ⟨⟨?_, Or.inl h0⟩, by rw [h0, AzNat.toNat_zero]; exact hn⟩
      by_contra hden
      exact not_exists_int_of_den_ne_one q hden
        ⟨0, by rw [coe_toRat_eq_zero_of_num_eq_zero q h0]; simp⟩
    · exact (toRat_sign_iff q h0).mp hs
  rw [ite_eq_right hs]
  have hsf : q.sign = false := by simpa using hs
  have h0 : q.num ≠ 0 := fun h => hs (q.zero_sign h)
  have hneg := toRat_neg_of_sign_false q h0 hsf
  have habs := abs_coe_toRat q
  rw [abs_of_neg hneg] at habs
  obtain ⟨a, ha⟩ : ∃ a : ℕ, a = q.num.toNat := ⟨_, rfl⟩
  obtain ⟨d, hdd⟩ : ∃ d : ℕ, d = q.den.toNat := ⟨_, rfl⟩
  rw [← ha, ← hdd] at habs
  rw [← hdd] at hd
  have hd0 : 0 < d := by exact_mod_cast hd
  have hqv : ((AzRat.toRat q : ℚ) : ℝ) = -((a : ℝ) / d) := by linarith
  by_cases c : AzNat.ofNat n * q.den ≤ q.num
  · rw [ite_eq_left c]
    rw [azNat_le_iff, AzNat.toNat_mul, AzNat.toNat_ofNat, ← ha, ← hdd] at c
    have hc : (n : ℝ) ≤ (a : ℝ) / d := by
      rw [le_div_iff₀ hd]
      exact_mod_cast c
    exact ⟨fun _ => by linarith, fun h => absurd (Nat.sub_self n) h⟩
  rw [ite_eq_right c]
  rw [azNat_le_iff, AzNat.toNat_mul, AzNat.toNat_ofNat, ← ha, ← hdd, not_le] at c
  rw [AzNat.toNat_div, ← ha, ← hdd]
  have hfloor : ((a / d : ℕ) : ℝ) ≤ (a : ℝ) / d := Nat.cast_div_le
  have hceil : (a : ℝ) / d < ((a / d : ℕ) : ℝ) + 1 := by
    rw [div_lt_iff₀ hd]
    have h1 := Nat.lt_div_mul_add hd0 (a := a)
    have h2 : (a : ℝ) < ((a / d : ℕ) : ℝ) * d + d := by exact_mod_cast h1
    rw [show (((a / d : ℕ) : ℝ) + 1) * (d : ℝ) = ((a / d : ℕ) : ℝ) * d + d by ring]
    exact h2
  by_cases hden : q.den = 1
  · exfalso
    refine hz' ⟨⟨hden, Or.inr hsf⟩, ?_⟩
    have : d = 1 := by rw [hdd, hden, AzNat.toNat_one]
    rw [← ha]
    rw [this] at c
    omega
  rw [ite_eq_right hden]
  have hni := not_exists_int_of_den_ne_one q hden
  have hlt : ((a / d : ℕ) : ℝ) < (a : ℝ) / d :=
    lt_of_le_of_ne hfloor fun h => hni ⟨-((a / d : ℕ) : ℤ), by rw [hqv, ← h]; push_cast; rfl⟩
  obtain ⟨k, hk⟩ : ∃ k : ℕ, k = min n (a / d + 1) := ⟨_, rfl⟩
  rw [← hk]
  have hk1 : (k : ℝ) ≤ ((a / d : ℕ) : ℝ) + 1 := by
    have : k ≤ a / d + 1 := by omega
    exact_mod_cast this
  constructor
  · intro _
    linarith
  · intro h
    have hk2 : k = a / d + 1 := by omega
    rw [hk2]
    push_cast
    linarith

/-- **The core of `(q)ₙ` converges** off the zeros. -/
theorem pochRatCore_coreConv (q : AzRat) {n : ℕ} (hz : pochRatHasZero q n = false) :
    CoreConv (pochRatCore q n) (∏ j ∈ range n, (((AzRat.toRat q : ℚ) : ℝ) + j)) := by
  obtain ⟨h1, h2⟩ := pochRatSplit_facts q hz
  exact pochCoreOf_coreConv (fun V _ => lnGammaRatEncl_level q V) (pochRatSplit_le q n) h1 h2 _

/-- **The bracket of `(q)ₙ` converges** off the zeros. -/
theorem pochRatApprox_bracketConv (q : AzRat) {n : ℕ} (hz : pochRatHasZero q n = false) :
    BracketConv (pochRatApprox q n) (∏ j ∈ range n, (((AzRat.toRat q : ℚ) : ℝ) + j)) :=
  gammaApproxOf_bracketConv (pochRatCore_coreConv q hz)

/-! ### The certificate -/

/-- What `pochRatSpecial` says. -/
theorem pochRatSpecial_spec {q : AzRat} (h : pochRatSpecial q = true) :
    ¬ ∃ k : ℕ, (AzRat.toRat q).den = 2 ^ k := by
  rintro ⟨k, hk⟩
  have hden : (AzRat.toRat q).den = q.den.toNat := rfl
  have : q.den.isPowerOfTwo = true := (AzNat.isPowerOfTwo_iff _).mpr ⟨k, by rw [← hden, hk]⟩
  simp [pochRatSpecial, this] at h

/-- No factor vanishes when the denominator is not a power of two. -/
theorem pochRatHasZero_of_special {q : AzRat} (h : pochRatSpecial q = true) (n : ℕ) :
    pochRatHasZero q n = false := by
  rcases Bool.eq_false_or_eq_true (pochRatHasZero q n) with hz | hz
  · exfalso
    obtain ⟨⟨hd, -⟩, -⟩ := (pochRatHasZero_iff q n).mp hz
    refine pochRatSpecial_spec h ⟨0, ?_⟩
    show q.den.toNat = 2 ^ 0
    rw [hd, AzNat.toNat_one, pow_zero]
  · exact hz

/-- **`(q)ₙ` is not dyadic** at the rationals recognized by `pochRatSpecial`, `n ≥ 1`. -/
theorem not_isDyadic_pochRat {q : AzRat} (h : pochRatSpecial q = true) {n : ℕ} (hn : n ≠ 0) :
    ¬ IsDyadic (∏ j ∈ range n, (((AzRat.toRat q : ℚ) : ℝ) + j)) :=
  not_isDyadic_prod_rat (AzRat.toRat q) (pochRatSpecial_spec h) hn

/-- **The Ziv certificate of `(q)ₙ` at the rationals recognized by `pochRatSpecial`**: some
level `w₀ 2^f` is accepted. -/
theorem pochRatApprox_cert {q : AzRat} {n : ℕ} (hn : n ≠ 0) (hc : pochRatSpecial q = true)
    (p : ℕ) [NeZero p] (mode : RoundingMode) (w₀ : ℕ) (hw₀ : 0 < w₀) :
    ∃ f : ℕ, (roundingPossible (pochRatApprox q n (w₀ * 2 ^ f)).1
      (pochRatApprox q n (w₀ * 2 ^ f)).2 p mode).isSome = true := by
  have hnd := not_isDyadic_pochRat hc hn
  exact (pochRatApprox_bracketConv q (pochRatHasZero_of_special hc n)).exists_isSome
    (fun h0 => hnd (h0 ▸ isDyadic_zero)) p (not_mem_floatSet_of_not_isDyadic p hnd) mode w₀ hw₀

end Azurite.AzFloat
