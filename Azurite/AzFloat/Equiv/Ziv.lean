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
Algorithm 3.1 in its truncation form, and `zivLoop_eq` the correctness of the loop: whenever
every approximation brackets the exact value, and rounding is possible from some working
precision `W` on that the fuel reaches, the loop returns `roundVal` of the exact value.

The approximations are truncations, whose error is one ulp of the result: `lt_add_ulp_of_floor`
(a float whose value is the floor of `x` at its precision lies less than one of its ulps below
`x`), `sub_roundFloor_lt_precScale` (the error is below the local scale of `x`),
`eq_zero_of_roundFloor_eq_zero` (only `0` truncates to `0` — the exponent is unbounded), and
`truncError_spec` packaging the facts the operations need about `truncError`.
`ofAzRatRound_eq_roundVal` is the pair form of `ofAzRatRound_eq_ofEReal`, the first
approximation of every operation with a rational.

The termination arguments of the operations share the arithmetic of boundaries: a nonzero
boundary is `M · 2^k` with `k ≥ ⌊log₂ |b|⌋ − p` (`boundary_repr`), two dyadic numbers differ by
a multiple of `2^-a` once `a` dominates both exponents (`exists_int_mul_sub_dyadic`), and a
real whose product with `D` is a nonzero integer has magnitude at least `1/D`
(`one_div_le_abs_of_mul_eq_int`).
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

/-- More precision, more floats. -/
theorem floatSet_mono {p p' : ℕ} [NeZero p] [NeZero p'] (h : p ≤ p') :
    floatSet p ⊆ floatSet p' := by
  rw [floatSet_eq, floatSet_eq]
  intro e he
  rcases he with he | he
  · left
    rcases he with he | ⟨m, k, hm, hlt, rfl⟩
    · exact Or.inl he
    · refine Or.inr ⟨m, k, hm, lt_of_lt_of_le hlt ?_, rfl⟩
      exact pow_le_pow_right₀ (by norm_num) h
  · exact Or.inr he

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

/-- When `roundingPossible` answers, it answers with the rounding of the exact value, which
lies in `(y, y + ε]` or is `y` with `ε = 0`. -/
theorem roundingPossible_eq (p : ℕ) [NeZero p] (mode : RoundingMode) {y ε : AzFloat}
    {yv εv v : ℝ} (hy : y.toVal = some (yv : EReal)) (hε : ε.toVal = some (εv : EReal))
    (h₁ : yv ≤ v) (h₂ : v ≤ yv + εv) (h₃ : yv = v → εv = 0) {r : AzFloat × Ordering}
    (h : roundingPossible y ε p mode = some r) :
    r = roundVal p mode (some (v : EReal)) := by
  unfold roundingPossible at h
  split_ifs at h with hle
  rw [Option.some.injEq] at h
  have hadd : ∀ (p' : ℕ) [NeZero p'] (m : RoundingMode),
      addPrecRound y ε p' m = roundVal p' m (some ((yv + εv : ℝ) : EReal)) := by
    intro p' _ m
    rw [addPrecRound_eq_liftVal₂]
    unfold liftVal₂
    rw [hy, hε, Option.bind_some, Option.bind_some, Spec.add_coe_coe]
  rw [← h, hadd]
  by_cases hv : v = yv + εv
  · rw [hv]
  have hlt : v < yv + εv := lt_of_le_of_ne h₂ hv
  have hyv : yv < v := by
    rcases lt_or_eq_of_le h₁ with h' | h'
    · exact h'
    · exact absurd (by rw [h₃ h', add_zero]; exact h'.symm) hv
  -- the `(p+1)`-bit floor of `y + ε` is at most `y`
  rw [hadd] at hle
  obtain ⟨hb1, _⟩ := roundVal_coe (p + 1) .Floor (yv + εv)
  have hfl : (round (floatSet (p + 1)) .Floor (yv + εv)).val
      = (roundFloor (floatSet (p + 1)) (yv + εv)).val := rfl
  rw [hfl] at hb1
  obtain ⟨bv, hbv⟩ :
      ∃ bv : ℝ, ((bv : ℝ) : EReal) = (roundFloor (floatSet (p + 1)) (yv + εv)).val := by
    rw [val_roundFloor_floatSet]
    exact precisionSet_exists_real _
  have hble : bv ≤ yv := by
    unfold le at hle
    rw [partialCompare_eq, hb1, hy, ← hbv] at hle
    simp only [compare_coe_coe] at hle
    by_contra hcon
    push Not at hcon
    rw [compare_gt_iff_gt.mpr hcon] at hle
    simp at hle
  symm
  apply roundVal_congr_of_no_boundary p mode v (yv + εv) hlt.le
  intro b hb ⟨hvb, hb'⟩
  have : (b : EReal) ≤ (roundFloor (floatSet (p + 1)) (yv + εv)).val :=
    (isGreatest_roundFloor (floatSet (p + 1)) (yv + εv)).2 ⟨hb, EReal.coe_le_coe_iff.mpr hb'⟩
  rw [← hbv] at this
  have := EReal.coe_le_coe_iff.mp this
  linarith

/-- Correctness of Ziv's loop: if every approximation at a positive working precision brackets
the exact value `v`, rounding is possible from working precision `W` on, and the fuel reaches
`W`, the loop returns the rounding of `v`. -/
theorem zivLoop_eq (p : ℕ) [NeZero p] (mode : RoundingMode) (approx : Nat → AzFloat × AzFloat)
    (v : ℝ)
    (happrox : ∀ w, 0 < w → ∃ yv εv : ℝ, yv ≤ v ∧ v ≤ yv + εv ∧ (yv = v → εv = 0) ∧
      (approx w).1.toVal = some (yv : EReal) ∧ (approx w).2.toVal = some (εv : EReal))
    (W : ℕ) (hW : ∀ w, W ≤ w → (roundingPossible (approx w).1 (approx w).2 p mode).isSome) :
    ∀ (fuel w : Nat), 0 < w → W ≤ w * 2 ^ fuel →
      zivLoop approx p mode fuel w = roundVal p mode (some (v : EReal))
  | fuel, w, hw, hfuel => by
    obtain ⟨yv, εv, h₁, h₂, h₃, hy, hε⟩ := happrox w hw
    rw [zivLoop.eq_def]
    split
    · rename_i r hr
      exact roundingPossible_eq p mode hy hε h₁ h₂ h₃ hr
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
was exact, and otherwise `ε` is the ulp `2^(e − p)` of the result, whose exponent is `e`. -/
theorem truncError_spec (p : ℕ) [NeZero p] (x : ℝ) :
    ∃ yv εv : ℝ, (roundVal p .Floor (some (x : EReal))).1.toVal = some (yv : EReal) ∧
      (truncError (roundVal p .Floor (some (x : EReal)))).toVal = some (εv : EReal) ∧
      yv ≤ x ∧ x ≤ yv + εv ∧ (yv = x → εv = 0) ∧ 0 ≤ εv ∧
      (εv ≠ 0 → ∃ e : ℤ, εv = (2 : ℝ) ^ (e - p) ∧
        (2 : ℝ) ^ (e - 1) ≤ |yv| ∧ |yv| < (2 : ℝ) ^ e) := by
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
    refine ⟨0, 0, by simp, ?_, le_rfl, by simp, fun _ => rfl, le_rfl, fun h => absurd rfl h⟩
    simp [truncError, ← hval]
  | finite s e q m hv =>
    rw [toVal_finite, Option.some.injEq] at hval
    have hq : q = p := by
      rcases hprec with hprec | hprec <;> simp [precision?] at hprec
      exact hprec
    subst hq
    have hyx : finiteVal s e m ≤ x := EReal.coe_le_coe_iff.mp (hval ▸ hle)
    by_cases hex : finiteVal s e m = x
    · refine ⟨finiteVal s e m, 0, rfl, ?_, hyx, by simp [hex], fun _ => rfl, le_rfl,
        fun h => absurd rfl h⟩
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
      refine ⟨finiteVal s e m, (2 : ℝ) ^ (e.toInt - q), rfl, ?_, hyx,
        (lt_add_ulp_of_floor s e hv x hx hval).le, fun h => absurd h hex, by positivity,
        fun _ => ⟨e.toInt, rfl, ?_, ?_⟩⟩
      · simp only [truncError, ← hval, hne, ↓reduceIte, hy, Option.getD_some, hyv]
      · exact (abs_finiteVal_bounds s e hv).1
      · exact (abs_finiteVal_bounds s e hv).2

end Azurite.AzFloat
