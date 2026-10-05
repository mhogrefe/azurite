/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Equiv.Add
import Azurite.AzFloat.Equiv.Compare
import Azurite.AzFloat.Equiv.Conversion
import Azurite.AzFloat.Equiv.Precision
import Azurite.AzFloat.Ziv

/-!
# Correctness of Ziv's loop

The boundaries of rounding to precision `p` are the values of `floatSet (p + 1)`: the floats
of precision `p` and the midpoints between neighbors.  `roundVal_congr_of_no_boundary`
specializes the cell lemma `roundVal_congr_cell`: two reals with no boundary between them
(inclusive) have the same `roundVal`.  `roundingPossible_eq` is then the correctness of MCA
Algorithm 3.1 in its bracket form, and `zivLoop_eq` the correctness of the loop: whenever every
approximation brackets the exact value (`Rounds` says that a `Roundable` is the rounding
procedure of a given real), and rounding is possible from some working precision `W` on that
the fuel reaches, the loop returns `roundVal` of the exact value.

The approximations come from truncations, whose error is one ulp of the result:
`lt_add_ulp_of_floor` (a float whose value is the floor of `x` at its precision lies less than
one of its ulps below `x`), `sub_roundFloor_lt_precScale` (the error is below the local scale
of `x`), `eq_zero_of_roundFloor_eq_zero` (only `0` truncates to `0` — the exponent is
unbounded), and `truncError_spec` packaging the facts the operations need about `truncError`,
including that the truncation plus its error is again a float of the working precision.
`ofAzRatRound_eq_roundVal` is the pair form of `ofAzRatRound_eq_ofEReal`, the first
approximation of every operation with a rational.

The termination arguments of the operations share the arithmetic of boundaries: a nonzero
boundary is `M · 2^k` with `k ≥ ⌊log₂ |b|⌋ − p` (`boundary_repr`), two dyadic numbers differ by
a multiple of `2^-a` once `a` dominates both exponents (`exists_int_mul_sub_dyadic`), and a
real whose product with `D` is a nonzero integer has magnitude at least `1/D`
(`one_div_le_abs_of_mul_eq_int`).  They also share the geometry: the boundaries adjacent to a
non-boundary `v` have at least its binade (`adjacent_boundaries`), a bracket of `v` narrower
than the distance to them contains no boundary (`no_boundary_of_dist`), and such a bracket is
accepted (`roundingPossible_isSome_of_no_boundary`).
-/

namespace Azurite.AzFloat

open RoundingTarget

/-! ### Boundaries -/

/-- `k · 2^j` with `|k| ≤ 2^p` is a float of precision `p`. -/
theorem mem_floatSet_mul_zpow (p : ℕ) [NeZero p] (k j : ℤ) (hk : |k| ≤ 2 ^ p) :
    (((k : ℝ) * (2 : ℝ) ^ j : ℝ) : EReal) ∈ floatSet p := by
  have hp : 0 < p := Nat.pos_of_ne_zero (NeZero.ne p)
  rcases eq_or_ne k 0 with hk0 | hk0
  · subst hk0
    simp only [Int.cast_zero, zero_mul, EReal.coe_zero]
    exact ⟨zero, Or.inr rfl, rfl⟩
  apply mem_floatSet_of_mem_precisionSet
  rcases lt_or_eq_of_le hk with hlt | heq
  · exact Or.inr ⟨k, j, hk0, hlt, by push_cast; ring_nf⟩
  · -- `k = ±2^p`: one bit at a higher exponent
    have hsign : k = 2 ^ p ∨ k = -(2 ^ p) := by
      rcases abs_eq (by positivity : (0 : ℤ) ≤ 2 ^ p) |>.mp heq with h | h
      · exact Or.inl h
      · exact Or.inr h
    have h1 : |(1 : ℤ)| < (2 : ℤ) ^ p := by
      rw [abs_one]; exact one_lt_pow₀ (by norm_num) hp.ne'
    have hm1 : |(-1 : ℤ)| < (2 : ℤ) ^ p := by
      rw [abs_neg]; exact h1
    have hsplit : ((2 : ℕ) : ℝ) ^ (j + p) = (2 : ℝ) ^ p * (2 : ℝ) ^ j := by
      rw [Nat.cast_ofNat, zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_natCast, mul_comm]
    rcases hsign with h | h
    · refine Or.inr ⟨1, j + p, one_ne_zero, h1, ?_⟩
      rw [h, hsplit, Int.cast_one, one_mul, Int.cast_pow, Int.cast_ofNat]
    · refine Or.inr ⟨-1, j + p, by norm_num, hm1, ?_⟩
      rw [h, hsplit, Int.cast_neg, Int.cast_one, neg_one_mul, Int.cast_neg, Int.cast_pow,
        Int.cast_ofNat, neg_mul]

/-- Two reals with no boundary between them (inclusive) round the same way: the specialization
of the cell lemma to the cells cut out by the floats of precision `p + 1`. -/
theorem roundVal_congr_of_no_boundary (p : ℕ) [NeZero p] (mode : RoundingMode) (v v' : ℝ)
    (hle : v ≤ v')
    (h : ∀ b : ℝ, ((b : ℝ) : EReal) ∈ floatSet (p + 1) → ¬ (v ≤ b ∧ b ≤ v')) :
    roundVal p mode (some (v : EReal)) = roundVal p mode (some (v' : EReal)) := by
  have h0 : ((0 : ℝ) : EReal) ∈ floatSet (p + 1) := ⟨zero, Or.inr rfl, by simp⟩
  have hv'0 : v' ≠ 0 := by
    rintro rfl
    exact h 0 h0 ⟨hle, le_rfl⟩
  set L := Int.log 2 |v'| with hL
  set j := L - p with hj
  have h2j : (0 : ℝ) < 2 ^ j := zpow_pos (by norm_num) _
  set k := ⌊v' / 2 ^ j⌋ with hk
  have hk1 : (k : ℝ) * 2 ^ j ≤ v' := by
    have := Int.floor_le (v' / 2 ^ j)
    calc (k : ℝ) * 2 ^ j ≤ v' / 2 ^ j * 2 ^ j := mul_le_mul_of_nonneg_right this h2j.le
      _ = v' := div_mul_cancel₀ v' h2j.ne'
  have hk2 : v' < ((k : ℝ) + 1) * 2 ^ j := by
    have := Int.lt_floor_add_one (v' / 2 ^ j)
    calc v' = v' / 2 ^ j * 2 ^ j := (div_mul_cancel₀ v' h2j.ne').symm
      _ < ((k : ℝ) + 1) * 2 ^ j := mul_lt_mul_of_pos_right this h2j
  have habs : |v'| < (2 : ℝ) ^ (L + 1) := Int.lt_zpow_succ_log_self (by norm_num) |v'|
  have hlow : (2 : ℝ) ^ L ≤ |v'| := Int.zpow_log_le_self (by norm_num) (abs_pos.mpr hv'0)
  have hLj : (2 : ℝ) ^ (L + 1) = 2 ^ (p + 1) * 2 ^ j := by
    rw [← zpow_natCast, ← zpow_add₀ (by norm_num)]
    congr 1
    push_cast
    omega
  have hLj' : (2 : ℝ) ^ L = 2 ^ (p : ℕ) * 2 ^ j := by
    rw [← zpow_natCast, ← zpow_add₀ (by norm_num)]
    congr 1
    omega
  -- `|k| ≤ 2^(p+1)`
  have hkabs : |k| ≤ 2 ^ (p + 1) := by
    have hdiv : |v' / 2 ^ j| < 2 ^ (p + 1) := by
      rw [abs_div, abs_of_pos h2j, div_lt_iff₀ h2j, ← hLj]
      exact habs
    rw [abs_lt] at hdiv
    rw [abs_le]
    constructor
    · have : (-(2 : ℝ) ^ (p + 1)) ≤ v' / 2 ^ j := hdiv.1.le
      have := Int.le_floor.mpr (by push_cast; exact this : ((-(2 ^ (p + 1)) : ℤ) : ℝ) ≤ v' / 2 ^ j)
      exact this
    · have := (Int.floor_le (v' / 2 ^ j)).trans hdiv.2.le
      exact_mod_cast this
  have hkmem : (((k : ℝ) * 2 ^ j : ℝ) : EReal) ∈ floatSet (p + 1) :=
    mem_floatSet_mul_zpow (p + 1) k j hkabs
  have hkv : (k : ℝ) * 2 ^ j < v := by
    by_contra hcon
    push Not at hcon
    exact h _ hkmem ⟨hcon, hk1⟩
  -- same binade
  have hlog : Int.log 2 |v| = L := by
    have hv0 : v ≠ 0 := by
      rintro rfl
      exact h 0 h0 ⟨le_rfl, by simpa using hle⟩
    apply le_antisymm
    · apply Int.lt_add_one_iff.mp
      apply (Int.lt_zpow_iff_log_lt (b := 2) (by norm_num) (abs_pos.mpr hv0)).mp
      push_cast
      rcases lt_or_gt_of_ne hv'0 with hneg | hpos
      · -- negative: `|v| = -v < -k·2^j ≤ 2^(p+1)·2^j`
        have hvneg : v < 0 := lt_of_le_of_lt hle hneg
        rw [abs_of_neg hvneg, hLj]
        have : (-(k : ℝ)) ≤ 2 ^ (p + 1) := by
          have := (abs_le.mp hkabs).1
          have : ((-(2 ^ (p + 1)) : ℤ) : ℝ) ≤ k := by exact_mod_cast this
          push_cast at this
          linarith
        nlinarith
      · have hk0 : (0 : ℝ) ≤ k := by
          exact_mod_cast Int.floor_nonneg.mpr (div_nonneg hpos.le h2j.le)
        have hvpos : (0 : ℝ) < v := lt_of_le_of_lt (mul_nonneg hk0 h2j.le) hkv
        rw [abs_of_pos hvpos]
        rw [abs_of_pos hpos] at habs
        exact lt_of_le_of_lt hle habs
    · apply (Int.zpow_le_iff_le_log (b := 2) (by norm_num) (abs_pos.mpr hv0)).mp
      push_cast
      rcases lt_or_gt_of_ne hv'0 with hneg | hpos
      · have hvneg : v < 0 := lt_of_le_of_lt hle hneg
        rw [abs_of_neg hvneg]
        rw [abs_of_neg hneg] at hlow
        linarith
      · -- positive: `k ≥ 2^p`, so `v > k·2^j ≥ 2^L`
        rw [abs_of_pos hpos] at hlow
        have hkge : (2 : ℤ) ^ p ≤ k := by
          apply Int.le_floor.mpr
          rw [le_div_iff₀ h2j]
          push_cast
          rw [← hLj']
          exact hlow
        have hkge' : (2 : ℝ) ^ (p : ℕ) ≤ k := by exact_mod_cast hkge
        have hpos' : (0 : ℝ) < v :=
          lt_trans (mul_pos (lt_of_lt_of_le (by positivity) hkge') h2j) hkv
        rw [abs_of_pos hpos', hLj']
        nlinarith
  refine roundVal_congr_cell p mode j k v v' ⟨hkv, lt_of_le_of_lt hle hk2⟩
    ⟨hk1.lt_of_ne ?_, hk2⟩ (by rw [hlog]) (by rw [hlog])
  intro heq
  exact h _ hkmem ⟨by rw [heq]; exact hle, heq.le⟩

/-! ### `roundingPossible` and `zivLoop` -/

/-- A `Roundable` is the rounding procedure of the real `v`. -/
def Rounds (r : Roundable) (v : ℝ) : Prop :=
  ∀ (p : ℕ) [NeZero p] (mode : RoundingMode), r p mode = roundVal p mode (some (v : EReal))

/-- When `roundingPossible` answers, it answers with the rounding of the exact value, which
lies in `(l, h]` or is `l = h`. -/
theorem roundingPossible_eq (p : ℕ) [NeZero p] (mode : RoundingMode) {l h : Roundable}
    {lv hv v : ℝ} (hl : Rounds l lv) (hh : Rounds h hv) (h₁ : lv ≤ v) (h₂ : v ≤ hv)
    (h₃ : lv = v → hv = v) {r : AzFloat × Ordering}
    (hr : roundingPossible l h p mode = some r) :
    r = roundVal p mode (some (v : EReal)) := by
  unfold roundingPossible at hr
  split_ifs at hr with heq
  rw [Option.some.injEq] at hr
  rw [← hr, hh]
  by_cases hveq : v = hv
  · rw [hveq]
  have hlt : v < hv := lt_of_le_of_ne h₂ hveq
  have hlv : lv < v := by
    rcases lt_or_eq_of_le h₁ with h' | h'
    · exact h'
    · exact absurd (h₃ h').symm hveq
  -- the `(p+1)`-bit floors of the two ends agree
  rw [hl, hh] at heq
  have hval := congrArg toVal heq
  rw [fst_roundVal, fst_roundVal] at hval
  change (ofEReal (p + 1) .Floor (lv : EReal)).toVal
    = (ofEReal (p + 1) .Floor (hv : EReal)).toVal at hval
  rw [(ofEReal_spec (p + 1) .Floor lv).2, (ofEReal_spec (p + 1) .Floor hv).2,
    Option.some.injEq] at hval
  have hfl : ∀ x : ℝ, (round (floatSet (p + 1)) .Floor x).val
      = (roundFloor (floatSet (p + 1)) x).val := fun _ => rfl
  rw [hfl, hfl] at hval
  symm
  apply roundVal_congr_of_no_boundary p mode v hv hlt.le
  intro b hb ⟨hvb, hbh⟩
  have h1 : (b : EReal) ≤ (roundFloor (floatSet (p + 1)) hv).val :=
    (isGreatest_roundFloor (floatSet (p + 1)) hv).2 ⟨hb, EReal.coe_le_coe_iff.mpr hbh⟩
  have h2 : (roundFloor (floatSet (p + 1)) lv).val ≤ (lv : EReal) :=
    (isGreatest_roundFloor (floatSet (p + 1)) lv).1.2
  rw [← hval] at h1
  have := EReal.coe_le_coe_iff.mp (le_trans h1 h2)
  linarith

/-- Correctness of Ziv's loop: if every approximation at a positive working precision brackets
the exact value `v`, rounding is possible from working precision `W` on, and the fuel reaches
`W`, the loop returns the rounding of `v`. -/
theorem zivLoop_eq (p : ℕ) [NeZero p] (mode : RoundingMode)
    (approx : Nat → Roundable × Roundable) (v : ℝ)
    (happrox : ∀ w, 0 < w → ∃ lv hv : ℝ, Rounds (approx w).1 lv ∧ Rounds (approx w).2 hv ∧
      lv ≤ v ∧ v ≤ hv ∧ (lv = v → hv = v))
    (W : ℕ) (hW : ∀ w, W ≤ w → (roundingPossible (approx w).1 (approx w).2 p mode).isSome) :
    ∀ (fuel w : Nat), 0 < w → W ≤ w * 2 ^ fuel →
      zivLoop approx p mode fuel w = roundVal p mode (some (v : EReal))
  | fuel, w, hw, hfuel => by
    obtain ⟨lv, hv, hl, hh, h₁, h₂, h₃⟩ := happrox w hw
    rw [zivLoop.eq_def]
    split
    · rename_i r hr
      exact roundingPossible_eq p mode hl hh h₁ h₂ h₃ hr
    · rename_i hr
      cases fuel with
      | zero =>
        exfalso
        have := hW w (by simpa using hfuel)
        rw [hr] at this
        exact absurd this (by simp)
      | succ fuel =>
        show zivLoop approx p mode fuel (2 * w) = _
        exact zivLoop_eq p mode approx v happrox W hW fuel (2 * w) (by omega)
          (by rw [pow_succ] at hfuel; linarith)

/-- The fuel `zivFuel W` reaches `W` from any positive start. -/
theorem le_mul_two_pow_zivFuel (W w : ℕ) (hw : 0 < w) : W ≤ w * 2 ^ zivFuel W := by
  have h : W < 2 ^ zivFuel W := by
    unfold zivFuel
    have h2 : (AzNat.ofNat W).size = W.size := by rw [← AzNat.size_toNat, AzNat.toNat_ofNat]
    rw [h2]
    exact Nat.lt_size_self W
  calc W ≤ 2 ^ zivFuel W := h.le
    _ ≤ w * 2 ^ zivFuel W := Nat.le_mul_of_pos_left _ hw

/-! ### Arithmetic of boundaries -/

/-- `|r| ≥ 1/D` when `r · D` is a nonzero integer. -/
theorem one_div_le_abs_of_mul_eq_int (r D : ℝ) (hD : 0 < D) (z : ℤ) (hz : r * D = z)
    (h0 : r ≠ 0) : 1 / D ≤ |r| := by
  have hz0 : z ≠ 0 := by
    rintro rfl
    simp only [Int.cast_zero] at hz
    rcases mul_eq_zero.mp hz with h | h
    · exact h0 h
    · exact hD.ne' h
  have h1 : (1 : ℝ) ≤ |(z : ℝ)| := by exact_mod_cast Int.one_le_abs hz0
  rw [← hz, abs_mul, abs_of_pos hD] at h1
  rw [div_le_iff₀ hD]
  exact h1

/-- Two dyadic numbers differ by an integer multiple of `2^-a` once `a` dominates both
exponents. -/
theorem exists_int_mul_sub_dyadic (c₁ c₂ k₁ k₂ : ℤ) (a : ℕ) (h₁ : -k₁ ≤ a) (h₂ : -k₂ ≤ a) :
    ∃ N : ℤ, ((c₁ : ℝ) * 2 ^ k₁ - c₂ * 2 ^ k₂) * 2 ^ a = N := by
  have key : ∀ k : ℤ, -k ≤ a → (2 : ℝ) ^ k * 2 ^ a = ((2 : ℤ) ^ (k + a).toNat : ℤ) := by
    intro k hk
    push_cast
    rw [← zpow_natCast (2 : ℝ) (k + a).toNat, Int.toNat_of_nonneg (by omega),
      zpow_add₀ (by norm_num), zpow_natCast]
  refine ⟨c₁ * 2 ^ (k₁ + a).toNat - c₂ * 2 ^ (k₂ + a).toNat, ?_⟩
  rw [sub_mul, mul_assoc, mul_assoc, key k₁ h₁, key k₂ h₂]
  push_cast
  ring

/-- A nonzero boundary of rounding to `p` bits is `M · 2^k` with `k ≥ ⌊log₂ |b|⌋ − p`. -/
theorem boundary_repr (p : ℕ) [NeZero p] (b : ℝ) (hb : ((b : ℝ) : EReal) ∈ floatSet (p + 1))
    (hb0 : b ≠ 0) : ∃ M k : ℤ, b = M * 2 ^ k ∧ Int.log 2 |b| - p ≤ k := by
  rw [floatSet_eq] at hb
  rcases hb with hb | hb
  · rcases hb with hb | ⟨M, k, hM, hlt, hMk⟩
    · exact absurd (EReal.coe_eq_zero.mp hb) hb0
    · have hb' : b = M * 2 ^ k := by
        have := EReal.coe_eq_coe_iff.mp hMk
        rw [← this, Nat.cast_ofNat]
      refine ⟨M, k, hb', ?_⟩
      have hpos : 0 < |b| := abs_pos.mpr hb0
      have hlt' : |b| < (2 : ℝ) ^ ((p : ℤ) + 1 + k) := by
        rw [hb', abs_mul, abs_of_pos (zpow_pos (by norm_num) k : (0 : ℝ) < 2 ^ k),
          zpow_add₀ (by norm_num)]
        apply mul_lt_mul_of_pos_right _ (zpow_pos (by norm_num) k)
        have : |(M : ℝ)| < (2 : ℝ) ^ (p + 1) := by exact_mod_cast hlt
        rw [show ((p : ℤ) + 1) = ((p + 1 : ℕ) : ℤ) by push_cast; ring, zpow_natCast]
        exact this
      have := (Int.lt_zpow_iff_log_lt (b := 2) (by norm_num) hpos).mp (by push_cast; exact hlt')
      omega
  · exfalso
    rcases hb with hb | hb <;> simp at hb

/-- Rounding a rational computably is `roundVal` of its value, tag included. -/
theorem ofAzRatRound_eq_roundVal (q : AzRat) (p : ℕ) [NeZero p] (mode : RoundingMode) :
    ofAzRatRound q p mode = roundVal p mode (some ((AzRat.toRat q : ℝ) : EReal)) := by
  have hp : 0 < p := Nat.pos_of_ne_zero (NeZero.ne p)
  refine Prod.ext ?_ ?_
  · rw [fst_roundVal]
    exact ofAzRatRound_eq_ofEReal p q mode
  · obtain ⟨v, hv, ht⟩ := snd_ofAzRatRound q p hp mode
    rw [ht, (roundVal_coe p mode _).2]
    have hval : ((v : ℝ) : EReal) = (round (floatSet p) mode (AzRat.toRat q : ℝ)).val := by
      have h1 := (ofEReal_spec p mode (AzRat.toRat q : ℝ)).2
      rw [← ofAzRatRound_eq_ofEReal p q mode, hv, Option.some.injEq] at h1
      exact h1
    rw [← hval, compare_coe_coe]

/-! ### Termination: brackets away from the boundaries -/

/-- The boundaries adjacent to a real `v ≠ 0` that is not a boundary itself: the greatest below
and the least above `v`, which have at least the binade of `v` (unless `0`). -/
theorem adjacent_boundaries (p : ℕ) [NeZero p] (v : ℝ) (hv0 : v ≠ 0)
    (hvB : ((v : ℝ) : EReal) ∉ floatSet (p + 1)) :
    ∃ bm bp : ℝ, ((bm : ℝ) : EReal) ∈ floatSet (p + 1) ∧ ((bp : ℝ) : EReal) ∈ floatSet (p + 1) ∧
      bm < v ∧ v < bp ∧
      (∀ b : ℝ, ((b : ℝ) : EReal) ∈ floatSet (p + 1) → b ≤ v → b ≤ bm) ∧
      (∀ b : ℝ, ((b : ℝ) : EReal) ∈ floatSet (p + 1) → v ≤ b → bp ≤ b) ∧
      (bm = 0 ∨ Int.log 2 |v| ≤ Int.log 2 |bm|) ∧ (bp = 0 ∨ Int.log 2 |v| ≤ Int.log 2 |bp|) := by
  set L := Int.log 2 |v| with hL
  obtain ⟨bmv, hbm⟩ : ∃ r : ℝ, ((r : ℝ) : EReal) = (roundFloor (floatSet (p + 1)) v).val := by
    rw [val_roundFloor_floatSet]; exact precisionSet_exists_real _
  obtain ⟨bpv, hbp⟩ : ∃ r : ℝ, ((r : ℝ) : EReal) = (roundCeiling (floatSet (p + 1)) v).val := by
    rw [val_roundCeiling_floatSet]; exact precisionSet_exists_real _
  have hbm_mem : ((bmv : ℝ) : EReal) ∈ floatSet (p + 1) := hbm ▸ (roundFloor _ _).property
  have hbp_mem : ((bpv : ℝ) : EReal) ∈ floatSet (p + 1) := hbp ▸ (roundCeiling _ _).property
  have hbm_le : bmv ≤ v := by
    have := (isGreatest_roundFloor (floatSet (p + 1)) v).1.2
    rw [← hbm] at this; exact EReal.coe_le_coe_iff.mp this
  have hbp_ge : v ≤ bpv := by
    have := (isLeast_roundCeiling (floatSet (p + 1)) v).1.2
    rw [← hbp] at this; exact EReal.coe_le_coe_iff.mp this
  have hbm_ne : bmv ≠ v := fun h => hvB (h ▸ hbm_mem)
  have hbp_ne : bpv ≠ v := fun h => hvB (h ▸ hbp_mem)
  have hgreatest : ∀ b : ℝ, ((b : ℝ) : EReal) ∈ floatSet (p + 1) → b ≤ v → b ≤ bmv := by
    intro b hb hbv
    have := (isGreatest_roundFloor (floatSet (p + 1)) v).2 ⟨hb, EReal.coe_le_coe_iff.mpr hbv⟩
    rw [← hbm] at this
    exact EReal.coe_le_coe_iff.mp this
  have hleast : ∀ b : ℝ, ((b : ℝ) : EReal) ∈ floatSet (p + 1) → v ≤ b → bpv ≤ b := by
    intro b hb hbv
    have := (isLeast_roundCeiling (floatSet (p + 1)) v).2 ⟨hb, EReal.coe_le_coe_iff.mpr hbv⟩
    rw [← hbp] at this
    exact EReal.coe_le_coe_iff.mp this
  have h2L : (2 : ℝ) ^ L ≤ |v| := Int.zpow_log_le_self (by norm_num) (abs_pos.mpr hv0)
  have h2Lpos : (0 : ℝ) < 2 ^ L := zpow_pos (by norm_num) _
  have hmemL : ∀ c : ℤ, |c| ≤ 1 → (((c : ℝ) * 2 ^ L : ℝ) : EReal) ∈ floatSet (p + 1) :=
    fun c hc => mem_floatSet_mul_zpow (p + 1) c L (le_trans hc (one_le_pow₀ (by norm_num)))
  refine ⟨bmv, bpv, hbm_mem, hbp_mem, lt_of_le_of_ne hbm_le hbm_ne,
    lt_of_le_of_ne hbp_ge hbp_ne.symm, hgreatest, hleast, Or.inr ?_, Or.inr ?_⟩
  · rcases lt_or_gt_of_ne hv0 with hneg | hpos
    · have hbneg : bmv < 0 := lt_of_le_of_lt hbm_le hneg
      apply (Int.zpow_le_iff_le_log (b := 2) (by norm_num) (abs_pos.mpr hbneg.ne)).mp
      push_cast
      rw [abs_of_neg hbneg]
      rw [abs_of_neg hneg] at h2L
      linarith
    · have hmem := hmemL 1 (by simp)
      simp only [Int.cast_one, one_mul] at hmem
      rw [abs_of_pos hpos] at h2L
      have hle := hgreatest _ hmem h2L
      apply (Int.zpow_le_iff_le_log (b := 2) (by norm_num)
        (abs_pos.mpr (lt_of_lt_of_le h2Lpos hle).ne')).mp
      push_cast
      rw [abs_of_pos (lt_of_lt_of_le h2Lpos hle)]
      exact hle
  · rcases lt_or_gt_of_ne hv0 with hneg | hpos
    · have hmem := hmemL (-1) (by simp)
      simp only [Int.cast_neg, Int.cast_one, neg_one_mul] at hmem
      rw [abs_of_neg hneg] at h2L
      have hle := hleast _ hmem (by linarith)
      have hbneg : bpv < 0 := lt_of_le_of_lt hle (by linarith)
      apply (Int.zpow_le_iff_le_log (b := 2) (by norm_num) (abs_pos.mpr hbneg.ne)).mp
      push_cast
      rw [abs_of_neg hbneg]
      linarith
    · rw [abs_of_pos hpos] at h2L
      have hbpos : 0 < bpv := lt_of_lt_of_le hpos hbp_ge
      apply (Int.zpow_le_iff_le_log (b := 2) (by norm_num) (abs_pos.mpr hbpos.ne')).mp
      push_cast
      rw [abs_of_pos hbpos]
      linarith

/-- No boundary lies in a bracket `(lv, hv]` of `v` narrower than the distance from `v` to its
adjacent boundaries. -/
theorem no_boundary_of_dist (p : ℕ) [NeZero p] (v lv hv D : ℝ) (hv0 : v ≠ 0)
    (hvB : ((v : ℝ) : EReal) ∉ floatSet (p + 1)) (hl : lv ≤ v) (hh : v ≤ hv)
    (hdist : ∀ b : ℝ, ((b : ℝ) : EReal) ∈ floatSet (p + 1) → b ≠ v →
      (b = 0 ∨ Int.log 2 |v| ≤ Int.log 2 |b|) → D ≤ |v - b|)
    (hwidth : hv - lv < D) :
    ∀ b : ℝ, ((b : ℝ) : EReal) ∈ floatSet (p + 1) → ¬ (lv < b ∧ b ≤ hv) := by
  obtain ⟨bm, bp, hbm_mem, hbp_mem, hbm_lt, hbp_gt, hgreatest, hleast, hLbm, hLbp⟩ :=
    adjacent_boundaries p v hv0 hvB
  have hDm : D ≤ v - bm := by
    have h := hdist bm hbm_mem hbm_lt.ne hLbm
    rwa [abs_of_pos (sub_pos.mpr hbm_lt)] at h
  have hDp : D ≤ bp - v := by
    have h := hdist bp hbp_mem hbp_gt.ne' hLbp
    rw [abs_of_neg (sub_neg.mpr hbp_gt)] at h
    linarith
  intro b hb ⟨hb1, hb2⟩
  rcases le_or_gt b v with hbv | hbv
  · have := hgreatest b hb hbv
    linarith
  · have := hleast b hb hbv.le
    linarith

/-- `roundingPossible` accepts a bracket that contains no boundary. -/
theorem roundingPossible_isSome_of_no_boundary (p : ℕ) [NeZero p] (mode : RoundingMode)
    {l h : Roundable} {lv hv : ℝ} (hl : Rounds l lv) (hh : Rounds h hv) (hle : lv ≤ hv)
    (hnob : ∀ b : ℝ, ((b : ℝ) : EReal) ∈ floatSet (p + 1) → ¬ (lv < b ∧ b ≤ hv)) :
    (roundingPossible l h p mode).isSome = true := by
  unfold roundingPossible
  rw [hl (p + 1) .Floor, hh (p + 1) .Floor]
  suffices hsuff : (roundFloor (floatSet (p + 1)) lv).val
      = (roundFloor (floatSet (p + 1)) hv).val by
    have heq : (roundVal (p + 1) .Floor (some (lv : EReal))).1
        = (roundVal (p + 1) .Floor (some (hv : EReal))).1 := by
      rw [fst_roundVal, fst_roundVal]
      change ofEReal (p + 1) .Floor (lv : EReal) = ofEReal (p + 1) .Floor (hv : EReal)
      exact toVal_injective (p + 1) (ofEReal_spec (p + 1) .Floor _).1
        (ofEReal_spec (p + 1) .Floor _).1
        (by rw [(ofEReal_spec (p + 1) .Floor _).2, (ofEReal_spec (p + 1) .Floor _).2]
            exact congrArg some hsuff)
    rw [heq]
    simp
  obtain ⟨fh, hfh⟩ : ∃ r : ℝ, ((r : ℝ) : EReal) = (roundFloor (floatSet (p + 1)) hv).val := by
    rw [val_roundFloor_floatSet]; exact precisionSet_exists_real _
  have hfh_mem : ((fh : ℝ) : EReal) ∈ floatSet (p + 1) := hfh ▸ (roundFloor _ _).property
  have hfh_le : fh ≤ hv := by
    have := (isGreatest_roundFloor (floatSet (p + 1)) hv).1.2
    rw [← hfh] at this; exact EReal.coe_le_coe_iff.mp this
  have hfh_le' : fh ≤ lv := by
    by_contra hcon
    push Not at hcon
    exact hnob fh hfh_mem ⟨hcon, hfh_le⟩
  apply le_antisymm
  · exact (isGreatest_roundFloor (floatSet (p + 1)) hv).2
      ⟨(roundFloor _ _).property,
        le_trans (isGreatest_roundFloor (floatSet (p + 1)) lv).1.2
          (EReal.coe_le_coe_iff.mpr hle)⟩
  · rw [← hfh]
    exact (isGreatest_roundFloor (floatSet (p + 1)) lv).2
      ⟨hfh_mem, EReal.coe_le_coe_iff.mpr hfh_le'⟩

/-- `2^(−ds − a) < 1/(d · 2^a)` when `d < 2^ds`. -/
theorem two_zpow_lt_one_div (d : ℕ) (hd : 0 < d) (ds : ℕ) (hds : d < 2 ^ ds) (a : ℕ) :
    (2 : ℝ) ^ (-(ds : ℤ) - a) < 1 / ((d : ℝ) * 2 ^ a) := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hds' : (d : ℝ) < 2 ^ ds := by exact_mod_cast hds
  calc (2 : ℝ) ^ (-(ds : ℤ) - a) = 1 / (2 ^ ds * 2 ^ a) := by
        rw [zpow_sub₀ (by norm_num), zpow_neg, zpow_natCast, zpow_natCast]
        field_simp
    _ < 1 / ((d : ℝ) * 2 ^ a) := by
        apply one_div_lt_one_div_of_lt (by positivity)
        exact mul_lt_mul_of_pos_right hds' (by positivity)

/-- A real of magnitude at least `1/(d · 2^a)` with `d < 2^ds` has `⌊log₂ |v|⌋ ≥ −ds − a`. -/
theorem neg_le_log_of_one_div_le (v : ℝ) (hv0 : v ≠ 0) (d : ℕ) (hd : 0 < d) (ds : ℕ)
    (hds : d < 2 ^ ds) (a : ℕ) (h : 1 / ((d : ℝ) * 2 ^ a) ≤ |v|) :
    -(ds : ℤ) - a ≤ Int.log 2 |v| := by
  apply (Int.zpow_le_iff_le_log (b := 2) (by norm_num) (abs_pos.mpr hv0)).mp
  push_cast
  exact le_trans (two_zpow_lt_one_div d hd ds hds a).le h

/-! ### The error of a truncation -/

/-- The truncation error is below the local scale of `x`. -/
theorem sub_roundFloor_lt_precScale (p : ℕ) [NeZero p] (x : ℝ) (hx : x ≠ 0) (r : ℝ)
    (h : ((r : ℝ) : EReal) = (roundFloor (precisionSet 2 p) x).val) :
    x < r + precScale 2 p x := by
  rw [val_roundFloor_precision x hx, EReal.coe_eq_coe_iff] at h
  set u := precScale 2 p x with hu
  have hu0 : 0 < u := by
    rw [hu]; unfold precScale; positivity
  have hlt := Int.lt_floor_add_one (x / u)
  rw [h]
  calc x = x / u * u := (div_mul_cancel₀ x hu0.ne').symm
    _ < ((⌊x / u⌋ : ℝ) + 1) * u := mul_lt_mul_of_pos_right hlt hu0
    _ = (⌊x / u⌋ : ℝ) * u + u := by ring

/-- A float whose value is the floor of `x ≠ 0` at the float's precision lies less than one of
its ulps below `x`. -/
theorem lt_add_ulp_of_floor (s : Bool) (e : AzInt) {p : ℕ} [NeZero p] {m : AzNat}
    (hv : FiniteValid p m) (x : ℝ) (hx : x ≠ 0)
    (h : ((finiteVal s e m : ℝ) : EReal) = (roundFloor (precisionSet 2 p) x).val) :
    x < finiteVal s e m + (2 : ℝ) ^ (e.toInt - p) := by
  have hle : finiteVal s e m ≤ x :=
    EReal.coe_le_coe_iff.mp (h ▸ (isGreatest_roundFloor (precisionSet 2 p) x).1.2)
  have hfv0 := finiteVal_ne_zero s e hv
  have h1 := sub_roundFloor_lt_precScale p x hx _ h
  -- `u ≤ 2^(e − p)`, the scale of the float's own binade
  have h2 : precScale 2 p x ≤ (2 : ℝ) ^ (e.toInt - p) := by
    rw [← precScale_finiteVal s e hv p]
    unfold precScale
    apply zpow_le_zpow_right₀ (by norm_num)
    have hlog : Int.log 2 |x| ≤ Int.log 2 |finiteVal s e m| := by
      apply (Int.zpow_le_iff_le_log (b := 2) (by norm_num) (abs_pos.mpr hfv0)).mp
      push_cast
      set L := Int.log 2 |x| with hL
      have hpow : (2 : ℝ) ^ L ≤ |x| := Int.zpow_log_le_self (by norm_num) (abs_pos.mpr hx)
      rcases lt_or_gt_of_ne hx with hneg | hpos
      · rw [abs_of_neg hneg] at hpow
        rw [abs_of_neg (lt_of_le_of_lt hle hneg)]
        linarith
      · -- `2^⌊log₂ x⌋` is in the set and below `x`, so below the floor
        rw [abs_of_pos hpos] at hpow
        have hmem : (((2 : ℝ) ^ L : ℝ) : EReal) ∈ precisionSet 2 p := by
          refine Or.inr ⟨1, L, one_ne_zero, ?_, ?_⟩
          · rw [abs_one]
            exact one_lt_pow₀ (by norm_num) (NeZero.ne p)
          · simp
        have hfl := (isGreatest_precision (b := 2) (p := p) x hx).2
          ⟨hmem, EReal.coe_le_coe_iff.mpr hpow⟩
        rw [← val_roundFloor_precision x hx, ← h] at hfl
        have hfl' := EReal.coe_le_coe_iff.mp hfl
        rw [abs_of_pos (lt_of_lt_of_le (zpow_pos (by norm_num) _) hfl')]
        exact hfl'
    omega
  linarith

/-- Only `0` has floor `0` at a positive precision: the exponent is unbounded. -/
theorem eq_zero_of_roundFloor_eq_zero (p : ℕ) [NeZero p] (x : ℝ)
    (h : (roundFloor (precisionSet 2 p) x).val = 0) : x = 0 := by
  have hp : 0 < p := Nat.pos_of_ne_zero (NeZero.ne p)
  by_contra hx
  rw [val_roundFloor_precision x hx] at h
  set u := precScale 2 p x with hu
  have hu0 : 0 < u := by
    rw [hu]; unfold precScale; positivity
  have h' : (⌊x / u⌋ : ℝ) * u = 0 := EReal.coe_eq_zero.mp h
  have hfl : ⌊x / u⌋ = 0 := by
    rcases mul_eq_zero.mp h' with h0 | h0
    · exact_mod_cast h0
    · exact absurd h0 hu0.ne'
  obtain ⟨h0, h1⟩ := Int.floor_eq_zero_iff.mp hfl
  have hb := (abs_div_precScale_bounds (b := 2) (p := p) x hx).1
  have hone : (1 : ℝ) ≤ (2 : ℝ) ^ ((p : ℤ) - 1) := one_le_zpow₀ (by norm_num) (by omega)
  rw [abs_of_nonneg h0] at hb
  push_cast at hb
  linarith

/-- The truncation of `x` at precision `p` (with its tag) and its `truncError` bracket `x`:
the result `y` and the bound `ε` are reals with `y ≤ x ≤ y + ε`, `ε = 0` when the truncation
was exact, and otherwise `ε` is the ulp `2^(e − p)` of the result, whose exponent is `e`; and
`y + ε`, the next float up, is again a float of precision `p`. -/
theorem truncError_spec (p : ℕ) [NeZero p] (x : ℝ) :
    ∃ yv εv : ℝ, (roundVal p .Floor (some (x : EReal))).1.toVal = some (yv : EReal) ∧
      (truncError (roundVal p .Floor (some (x : EReal)))).toVal = some (εv : EReal) ∧
      yv ≤ x ∧ x ≤ yv + εv ∧ (yv = x → εv = 0) ∧ 0 ≤ εv ∧
      (εv ≠ 0 → ∃ e : ℤ, εv = (2 : ℝ) ^ (e - p) ∧
        (2 : ℝ) ^ (e - 1) ≤ |yv| ∧ |yv| < (2 : ℝ) ^ e) ∧
      ((yv + εv : ℝ) : EReal) ∈ floatSet p := by
  have hpair : roundVal p .Floor (some (x : EReal))
      = (ofEReal p .Floor x, compare (round (floatSet p) .Floor x).val (x : EReal)) :=
    Prod.ext rfl (roundVal_coe p .Floor x).2
  rw [hpair]
  simp only
  obtain ⟨hprec, hval⟩ := ofEReal_spec p .Floor x
  have hfl : (round (floatSet p) .Floor x).val = (roundFloor (precisionSet 2 p) x).val := by
    rw [val_round_floatSet]; rfl
  rw [hfl] at hval ⊢
  have hle : (roundFloor (precisionSet 2 p) x).val ≤ (x : EReal) :=
    (isGreatest_roundFloor (precisionSet 2 p) x).1.2
  generalize hf : ofEReal p .Floor x = f at hprec hval
  cases f with
  | nan => simp at hval
  | infinity s =>
    exfalso
    obtain ⟨r, hr⟩ := precisionSet_exists_real (roundFloor (precisionSet 2 p) x)
    rw [toVal_infinity, ← hr, Option.some.injEq] at hval
    cases s <;> simp at hval
  | zero =>
    rw [toVal_zero, Option.some.injEq] at hval
    have hx0 : x = 0 := eq_zero_of_roundFloor_eq_zero p x hval.symm
    subst hx0
    refine ⟨0, 0, by simp, ?_, le_rfl, by simp, fun _ => rfl, le_rfl, fun h => absurd rfl h, ?_⟩
    · simp [truncError, ← hval]
    · exact ⟨zero, Or.inr rfl, by simp⟩
  | finite s e q m hv =>
    rw [toVal_finite, Option.some.injEq] at hval
    have hq : q = p := by
      rcases hprec with hprec | hprec <;> simp [precision?] at hprec
      exact hprec
    subst hq
    have hyx : finiteVal s e m ≤ x := EReal.coe_le_coe_iff.mp (hval ▸ hle)
    have hmem : ((finiteVal s e m : ℝ) : EReal) ∈ floatSet q :=
      ⟨finite s e q m hv, Or.inl rfl, rfl⟩
    by_cases hex : finiteVal s e m = x
    · refine ⟨finiteVal s e m, 0, rfl, ?_, hyx, by simp [hex], fun _ => rfl, le_rfl,
        fun h => absurd rfl h, by simpa using hmem⟩
      simp [truncError, ← hval, hex]
    · obtain ⟨y, hy, hyv, _⟩ := ulp?_spec s e q m hv
      have hx : x ≠ 0 := by
        rintro rfl
        have h0 : (roundFloor (precisionSet 2 q) (0 : ℝ)).val = 0 :=
          val_roundFloor_of_mem _ (Or.inl (by simp))
        rw [h0] at hval
        exact finiteVal_ne_zero s e hv (EReal.coe_eq_zero.mp hval)
      have hne : compare (((finiteVal s e m : ℝ) : EReal)) (x : EReal) ≠ .eq := by
        rw [compare_coe_coe]
        exact fun h => hex (compare_eq_iff_eq.mp h)
      -- the next float up: `(±c + 1) · 2^(e − q)` with `c` the core, `|±c + 1| ≤ 2^q`
      have hsucc : ((finiteVal s e m + (2 : ℝ) ^ (e.toInt - q) : ℝ) : EReal) ∈ floatSet q := by
        rw [finiteVal_eq_core s e hv]
        set c := coreSignificand q m with hc
        have hcs : c.size = q := size_coreSignificand hv
        have hclt : c.toNat < 2 ^ q := by
          have := Nat.lt_size_self c.toNat
          rwa [AzNat.size_toNat, hcs] at this
        have hcpos : 0 < c.toNat := by
          have := Nat.lt_size.mp (show 0 < c.toNat.size by rw [AzNat.size_toNat, hcs]; exact hv.pos)
          simp at this
          omega
        have hclt' : (c.toNat : ℤ) < 2 ^ q := by exact_mod_cast hclt
        have hcpos' : (1 : ℤ) ≤ c.toNat := by exact_mod_cast hcpos
        have hval' : finiteVal s e c
            = (((if s then (c.toNat : ℤ) else -(c.toNat : ℤ)) : ℤ) : ℝ) * 2 ^ (e.toInt - q) := by
          unfold finiteVal
          rw [hcs]
          cases s
          · simp only [Bool.false_eq_true, ↓reduceIte, Int.cast_neg, Int.cast_natCast]; ring
          · simp only [↓reduceIte, Int.cast_natCast]; ring
        rw [hval']
        have : (((if s then (c.toNat : ℤ) else -(c.toNat : ℤ)) : ℤ) : ℝ) * 2 ^ (e.toInt - q)
            + (2 : ℝ) ^ (e.toInt - q)
            = (((if s then (c.toNat : ℤ) else -(c.toNat : ℤ)) + 1 : ℤ) : ℝ)
              * 2 ^ (e.toInt - q) := by
          push_cast; ring
        rw [this]
        apply mem_floatSet_mul_zpow
        cases s
        · simp only [Bool.false_eq_true, ↓reduceIte]
          rw [abs_le]
          constructor <;> omega
        · simp only [↓reduceIte]
          rw [abs_le]
          constructor <;> omega
      refine ⟨finiteVal s e m, (2 : ℝ) ^ (e.toInt - q), rfl, ?_, hyx,
        (lt_add_ulp_of_floor s e hv x hx hval).le, fun h => absurd h hex, by positivity,
        fun _ => ⟨e.toInt, rfl, ?_, ?_⟩, hsucc⟩
      · simp only [truncError, ← hval, hne, ↓reduceIte, hy, Option.getD_some, hyv]
      · exact (abs_finiteVal_bounds s e hv).1
      · exact (abs_finiteVal_bounds s e hv).2

end Azurite.AzFloat
