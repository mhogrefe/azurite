/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.Rounding.Sci
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Data.Int.Log

/-!
# The precision rounding target

`precisionSet b p`: the numbers with at most `p` significant base-`b` digits,
`{0} ∪ { m · b^k : m, k ∈ ℤ, 0 < |m| < b^p }`.  Away from `0` it is locally the lattice of
multiples of `u = b^(⌊log_b |x|⌋ − p + 1)`, which is why it is a `RoundingTarget`:
`val_round_precisionSet` says rounding `x ≠ 0` to it is rounding `x / u` to an integer and
scaling back (the tiebreak is the integer tiebreak on those coordinates).  This is the target
of `toSci`'s `precision p` option (`docs/to_sci_plan.md`).
-/

namespace Azurite

namespace RoundingTarget

/-- The numbers with at most `p` significant base-`b` digits, in `EReal`. -/
def precisionSet (b p : ℕ) : Set EReal :=
  {e | e = 0 ∨ ∃ (m k : ℤ), m ≠ 0 ∧ |m| < (b : ℤ) ^ p ∧ (((m : ℝ) * (b : ℝ) ^ k : ℝ) : EReal) = e}

variable {b p : ℕ}

/-- The scale at which `precisionSet b p` is a lattice near `x`: `b^(⌊log_b |x|⌋ − p + 1)`. -/
noncomputable def precScale (b p : ℕ) (x : ℝ) : ℝ :=
  (b : ℝ) ^ (Int.log b |x| - p + 1)

/-- Membership of a nonzero multiple `m · b^k` with `|m| < b^p`. -/
private lemma mem_of_coord (m k : ℤ) (hm : m ≠ 0) (hlt : |m| < (b : ℤ) ^ p) :
    (((m : ℝ) * (b : ℝ) ^ k : ℝ) : EReal) ∈ precisionSet b p :=
  Or.inr ⟨m, k, hm, hlt, rfl⟩

/-- Every element of the set is a real number. -/
lemma precisionSet_exists_real (a : ↥(precisionSet b p)) : ∃ r : ℝ, ((r : ℝ) : EReal) = a.val := by
  rcases a.property with h | ⟨m, k, _, _, h⟩
  · exact ⟨0, by rw [h]; rfl⟩
  · exact ⟨_, h⟩

/-- The real value of an element. Noncomputable. -/
noncomputable def precToReal (a : ↥(precisionSet b p)) : ℝ :=
  Classical.choose (precisionSet_exists_real a)

lemma precToReal_spec (a : ↥(precisionSet b p)) : ((precToReal a : ℝ) : EReal) = a.val :=
  Classical.choose_spec (precisionSet_exists_real a)

lemma precToReal_eq_of_val {a : ↥(precisionSet b p)} {r : ℝ} (h : ((r : ℝ) : EReal) = a.val) :
    precToReal a = r :=
  EReal.coe_eq_coe_iff.mp ((precToReal_spec a).trans h.symm)

private lemma hb1 (b : ℕ) [Fact (1 < b)] : 1 < b := Fact.out
private lemma hbR (b : ℕ) [Fact (1 < b)] : (1 : ℝ) < b := by exact_mod_cast hb1 b
private lemma hb0R (b : ℕ) [Fact (1 < b)] : (0 : ℝ) < b := lt_trans one_pos (hbR b)
private lemma hp0 (p : ℕ) [NeZero p] : 0 < p := Nat.pos_of_ne_zero (NeZero.ne p)

section
variable [Fact (1 < b)] [NeZero p]

omit [NeZero p] in
private lemma precScale_pos (x : ℝ) : 0 < precScale b p x := zpow_pos (hb0R b) _

omit [NeZero p] in
/-- `y = x / u` lies in `[b^(p−1), b^p)` for `x > 0`. -/
private lemma y_bounds (x : ℝ) (hx : 0 < x) :
    (b : ℝ) ^ ((p : ℤ) - 1) ≤ x / precScale b p x ∧ x / precScale b p x < (b : ℝ) ^ (p : ℤ) := by
  have hu : (0 : ℝ) < (b : ℝ) ^ (Int.log b x - p + 1) := zpow_pos (hb0R b) _
  have hlog_le : (b : ℝ) ^ Int.log b x ≤ x := Int.zpow_log_le_self (hb1 b) hx
  have hlog_lt : x < (b : ℝ) ^ (Int.log b x + 1) := Int.lt_zpow_succ_log_self (hb1 b) x
  unfold precScale
  rw [abs_of_pos hx]
  constructor
  · rw [le_div_iff₀ hu, ← zpow_add₀ (hb0R b).ne']
    rw [show (p : ℤ) - 1 + (Int.log b x - p + 1) = Int.log b x from by ring]
    exact hlog_le
  · rw [div_lt_iff₀ hu, ← zpow_add₀ (hb0R b).ne']
    rw [show (p : ℤ) + (Int.log b x - p + 1) = Int.log b x + 1 from by ring]
    exact hlog_lt

/-- `b^(p−1) ≥ 1`. -/
private lemma one_le_b_pow_pm1 : (1 : ℝ) ≤ (b : ℝ) ^ ((p : ℤ) - 1) :=
  one_le_zpow₀ (hbR b).le (by have := hp0 p; omega)

omit [NeZero p] in
/-- `|x / u|` lies in `[b^(p−1), b^p)` for `x ≠ 0`, where `u = precScale b p x`. -/
lemma abs_div_precScale_bounds (x : ℝ) (hx : x ≠ 0) :
    (b : ℝ) ^ ((p : ℤ) - 1) ≤ |x / precScale b p x| ∧
      |x / precScale b p x| < (b : ℝ) ^ (p : ℤ) := by
  have hu := precScale_pos (b := b) (p := p) x
  have h := y_bounds (b := b) (p := p) |x| (abs_pos.mpr hx)
  rw [show precScale b p |x| = precScale b p x from by unfold precScale; rw [abs_abs]] at h
  rwa [abs_div, abs_of_pos hu]

/-- For `x > 0`, the greatest element `≤ x` is `⌊x / u⌋ · u`. -/
lemma isGreatest_precision_pos (x : ℝ) (hx : 0 < x) :
    IsGreatest {s | s ∈ precisionSet b p ∧ s ≤ (x : EReal)}
      ((((⌊x / precScale b p x⌋ : ℝ) * precScale b p x : ℝ) : EReal)) := by
  set u := precScale b p x with hu_def
  have hu := precScale_pos (b := b) (p := p) x
  set y := x / u with hy_def
  obtain ⟨hy1, hy2⟩ := y_bounds (b := b) (p := p) x hx
  rw [← hy_def] at hy1 hy2
  have hfloor_pos : (0 : ℤ) < ⌊y⌋ := by
    have : (1 : ℝ) ≤ y := le_trans one_le_b_pow_pm1 hy1
    exact Int.floor_pos.mpr this
  have hfloor_lt : ⌊y⌋ < (b : ℤ) ^ p := by
    have h1 : (⌊y⌋ : ℝ) ≤ y := Int.floor_le y
    have h2 : (⌊y⌋ : ℝ) < ((b : ℤ) ^ p : ℤ) := by
      push_cast; rw [← zpow_natCast]; exact lt_of_le_of_lt h1 hy2
    exact_mod_cast h2
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · -- membership: `m = ⌊y⌋`, `k = log − p + 1`
    have := mem_of_coord (b := b) (p := p) ⌊y⌋ (Int.log b |x| - p + 1) hfloor_pos.ne'
      (by rw [abs_of_pos hfloor_pos]; exact hfloor_lt)
    exact this
  · -- `⌊y⌋ u ≤ x`
    apply EReal.coe_le_coe_iff.mpr
    rw [← le_div_iff₀ hu, ← hy_def]
    exact Int.floor_le y
  · -- greatest
    rintro s ⟨hs, hsx⟩
    rcases hs with h0 | ⟨m, k, hm, hmlt, rfl⟩
    · rw [h0]
      exact EReal.coe_le_coe_iff.mpr (by positivity)
    · apply EReal.coe_le_coe_iff.mpr
      have hsx' : (m : ℝ) * (b : ℝ) ^ k ≤ x := EReal.coe_le_coe_iff.mp hsx
      rcases lt_or_gt_of_ne hm with hmneg | hmpos
      · -- negative elements are below
        have : (m : ℝ) * (b : ℝ) ^ k < 0 :=
          mul_neg_of_neg_of_pos (by exact_mod_cast hmneg) (zpow_pos (hb0R b) _)
        have : (0 : ℝ) ≤ (⌊y⌋ : ℝ) * u := by positivity
        linarith
      · by_cases hk : Int.log b |x| - p + 1 ≤ k
        · -- a multiple of `u`
          obtain ⟨d, hd⟩ : ∃ d : ℕ, k = (Int.log b |x| - p + 1) + d :=
            ⟨(k - (Int.log b |x| - p + 1)).toNat, by omega⟩
          have hs_eq : (m : ℝ) * (b : ℝ) ^ k = ((m * (b : ℤ) ^ d : ℤ) : ℝ) * u := by
            rw [hd, zpow_add₀ (hb0R b).ne', hu_def]; unfold precScale; push_cast
            rw [zpow_natCast]; ring
          rw [hs_eq] at hsx' ⊢
          rw [← le_div_iff₀ hu, ← hy_def] at hsx'
          have : (m * (b : ℤ) ^ d : ℤ) ≤ ⌊y⌋ := Int.le_floor.mpr hsx'
          exact mul_le_mul_of_nonneg_right (by exact_mod_cast this) hu.le
        · -- below the lattice: `s < b^(p+k) ≤ b^log ≤ ⌊y⌋ u`
          push Not at hk
          have hmR : (m : ℝ) < (b : ℝ) ^ (p : ℤ) := by
            have : m < (b : ℤ) ^ p := lt_of_le_of_lt (le_abs_self m) hmlt
            have h' : (m : ℝ) < ((b : ℤ) ^ p : ℤ) := by exact_mod_cast this
            push_cast at h'; rw [← zpow_natCast] at h'; exact h'
          have h1 : (m : ℝ) * (b : ℝ) ^ k < (b : ℝ) ^ ((p : ℤ) + k) := by
            rw [zpow_add₀ (hb0R b).ne']
            exact mul_lt_mul_of_pos_right hmR (zpow_pos (hb0R b) _)
          have h2 : (b : ℝ) ^ ((p : ℤ) + k) ≤ (b : ℝ) ^ Int.log b |x| :=
            zpow_le_zpow_right₀ (hbR b).le (by omega)
          have h3 : (b : ℝ) ^ Int.log b |x| = (b : ℝ) ^ ((p : ℤ) - 1) * u := by
            rw [hu_def]; unfold precScale; rw [← zpow_add₀ (hb0R b).ne']; congr 1; ring
          have h4 : (b : ℝ) ^ ((p : ℤ) - 1) * u ≤ (⌊y⌋ : ℝ) * u := by
            apply mul_le_mul_of_nonneg_right _ hu.le
            have : (b : ℝ) ^ ((p : ℤ) - 1) ≤ y := hy1
            -- `b^(p-1)` is an integer, so it is `≤ ⌊y⌋`
            have hint : ((b : ℤ) ^ (p - 1) : ℤ) ≤ ⌊y⌋ := by
              apply Int.le_floor.mpr
              have hcast : (((b : ℤ) ^ (p - 1) : ℤ) : ℝ) = (b : ℝ) ^ ((p : ℤ) - 1) := by
                push_cast
                rw [← zpow_natCast]
                congr 1
                have := hp0 p; omega
              rw [hcast]; exact this
            have hcast : (((b : ℤ) ^ (p - 1) : ℤ) : ℝ) = (b : ℝ) ^ ((p : ℤ) - 1) := by
              push_cast
              rw [← zpow_natCast]
              congr 1
              have := hp0 p; omega
            rw [← hcast]; exact_mod_cast hint
          linarith

/-- For `x > 0`, the least element `≥ x` is `⌈x / u⌉ · u`. -/
lemma isLeast_precision_pos (x : ℝ) (hx : 0 < x) :
    IsLeast {s | s ∈ precisionSet b p ∧ (x : EReal) ≤ s}
      ((((⌈x / precScale b p x⌉ : ℝ) * precScale b p x : ℝ) : EReal)) := by
  set u := precScale b p x with hu_def
  have hu := precScale_pos (b := b) (p := p) x
  set y := x / u with hy_def
  obtain ⟨hy1, hy2⟩ := y_bounds (b := b) (p := p) x hx
  rw [← hy_def] at hy1 hy2
  have hy_pos : 0 < y := lt_of_lt_of_le (lt_of_lt_of_le one_pos one_le_b_pow_pm1) hy1
  have hceil_pos : (0 : ℤ) < ⌈y⌉ := Int.ceil_pos.mpr hy_pos
  have hceil_le : ⌈y⌉ ≤ (b : ℤ) ^ p := by
    apply Int.ceil_le.mpr
    push_cast; rw [← zpow_natCast]; exact hy2.le
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · -- membership: either `⌈y⌉ < b^p`, or `⌈y⌉ = b^p` and the value is `1 · b^(log+1)`
    rcases lt_or_eq_of_le hceil_le with hlt | heq
    · exact mem_of_coord (b := b) (p := p) ⌈y⌉ (Int.log b |x| - p + 1) hceil_pos.ne'
        (by rw [abs_of_pos hceil_pos]; exact hlt)
    · have hval : ((⌈y⌉ : ℝ) * u : ℝ) = ((1 : ℤ) : ℝ) * (b : ℝ) ^ (Int.log b |x| + 1) := by
        rw [heq, hu_def]; unfold precScale; push_cast
        rw [← zpow_natCast, ← zpow_add₀ (hb0R b).ne', one_mul]; congr 1; ring
      rw [hval]
      exact mem_of_coord (b := b) (p := p) 1 _ one_ne_zero (by
        rw [abs_one]; exact_mod_cast Nat.one_lt_pow (hp0 p).ne' (hb1 b))
  · apply EReal.coe_le_coe_iff.mpr
    rw [← div_le_iff₀ hu, ← hy_def]
    exact Int.le_ceil y
  · rintro s ⟨hs, hxs⟩
    rcases hs with h0 | ⟨m, k, hm, hmlt, rfl⟩
    · rw [h0] at hxs
      have : x ≤ 0 := EReal.coe_le_coe_iff.mp (by simpa using hxs)
      linarith
    · apply EReal.coe_le_coe_iff.mpr
      have hxs' : x ≤ (m : ℝ) * (b : ℝ) ^ k := EReal.coe_le_coe_iff.mp hxs
      have hmpos : 0 < m := by
        rcases lt_or_gt_of_ne hm with hmneg | hmpos
        · have : (m : ℝ) * (b : ℝ) ^ k < 0 :=
            mul_neg_of_neg_of_pos (by exact_mod_cast hmneg) (zpow_pos (hb0R b) _)
          linarith
        · exact hmpos
      by_cases hk : Int.log b |x| - p + 1 ≤ k
      · obtain ⟨d, hd⟩ : ∃ d : ℕ, k = (Int.log b |x| - p + 1) + d :=
          ⟨(k - (Int.log b |x| - p + 1)).toNat, by omega⟩
        have hs_eq : (m : ℝ) * (b : ℝ) ^ k = ((m * (b : ℤ) ^ d : ℤ) : ℝ) * u := by
          rw [hd, zpow_add₀ (hb0R b).ne', hu_def]; unfold precScale; push_cast
          rw [zpow_natCast]; ring
        rw [hs_eq] at hxs' ⊢
        rw [← div_le_iff₀ hu, ← hy_def] at hxs'
        have : ⌈y⌉ ≤ (m * (b : ℤ) ^ d : ℤ) := Int.ceil_le.mpr hxs'
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast this) hu.le
      · push Not at hk
        have hmR : (m : ℝ) < (b : ℝ) ^ (p : ℤ) := by
          have : m < (b : ℤ) ^ p := lt_of_le_of_lt (le_abs_self m) hmlt
          have h' : (m : ℝ) < ((b : ℤ) ^ p : ℤ) := by exact_mod_cast this
          push_cast at h'; rw [← zpow_natCast] at h'; exact h'
        have h1 : (m : ℝ) * (b : ℝ) ^ k < (b : ℝ) ^ ((p : ℤ) + k) := by
          rw [zpow_add₀ (hb0R b).ne']
          exact mul_lt_mul_of_pos_right hmR (zpow_pos (hb0R b) _)
        have h2 : (b : ℝ) ^ ((p : ℤ) + k) ≤ (b : ℝ) ^ Int.log b |x| :=
          zpow_le_zpow_right₀ (hbR b).le (by omega)
        have h3 : (b : ℝ) ^ Int.log b |x| ≤ x := by
          rw [abs_of_pos hx]; exact Int.zpow_log_le_self (hb1 b) hx
        linarith


omit [Fact (1 < b)] [NeZero p] in
/-- `precisionSet` is closed under negation. -/
lemma precisionSet_neg_mem {e : EReal} (h : e ∈ precisionSet b p) : -e ∈ precisionSet b p := by
  rcases h with h0 | ⟨m, k, hm, hlt, rfl⟩
  · left; rw [h0]; simp
  · right
    refine ⟨-m, k, neg_ne_zero.mpr hm, by rwa [abs_neg], ?_⟩
    rw [← EReal.coe_neg]; congr 1; push_cast; ring

omit [Fact (1 < b)] [NeZero p] in
/-- `precScale` only depends on `|x|`. -/
lemma precScale_neg (x : ℝ) : precScale b p (-x) = precScale b p x := by
  unfold precScale; rw [abs_neg]

omit [Fact (1 < b)] [NeZero p] in
/-- Reflect a least-upper characterization at `−x` to a greatest-lower one at `x`. -/
private lemma isGreatest_of_isLeast_neg (x L : ℝ)
    (h : IsLeast {s | s ∈ precisionSet b p ∧ ((-x : ℝ) : EReal) ≤ s} ((L : ℝ) : EReal)) :
    IsGreatest {s | s ∈ precisionSet b p ∧ s ≤ (x : EReal)} (((-L : ℝ) : EReal)) := by
  obtain ⟨⟨hmem, hle⟩, hleast⟩ := h
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [EReal.coe_neg]; exact precisionSet_neg_mem hmem
  · rw [EReal.coe_neg]
    have := EReal.coe_le_coe_iff.mp hle
    exact EReal.coe_le_coe_iff.mpr (by linarith)
  · rintro s ⟨hs, hsx⟩
    have hs' : -s ∈ precisionSet b p := precisionSet_neg_mem hs
    have hsx' : ((-x : ℝ) : EReal) ≤ -s := by
      rw [EReal.coe_neg]; exact EReal.neg_le_neg_iff.mpr hsx
    have := hleast ⟨hs', hsx'⟩
    rw [EReal.coe_neg]
    have h2 : -(-s) ≤ -((L : ℝ) : EReal) := EReal.neg_le_neg_iff.mpr this
    rwa [neg_neg] at h2

omit [Fact (1 < b)] [NeZero p] in
/-- Reflect a greatest-lower characterization at `−x` to a least-upper one at `x`. -/
private lemma isLeast_of_isGreatest_neg (x G : ℝ)
    (h : IsGreatest {s | s ∈ precisionSet b p ∧ s ≤ ((-x : ℝ) : EReal)} ((G : ℝ) : EReal)) :
    IsLeast {s | s ∈ precisionSet b p ∧ (x : EReal) ≤ s} (((-G : ℝ) : EReal)) := by
  obtain ⟨⟨hmem, hle⟩, hgreatest⟩ := h
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [EReal.coe_neg]; exact precisionSet_neg_mem hmem
  · rw [EReal.coe_neg]
    have := EReal.coe_le_coe_iff.mp hle
    exact EReal.coe_le_coe_iff.mpr (by linarith)
  · rintro s ⟨hs, hxs⟩
    have hs' : -s ∈ precisionSet b p := precisionSet_neg_mem hs
    have hxs' : -s ≤ ((-x : ℝ) : EReal) := by
      rw [EReal.coe_neg]; exact EReal.neg_le_neg_iff.mpr hxs
    have := hgreatest ⟨hs', hxs'⟩
    rw [EReal.coe_neg]
    have h2 : -((G : ℝ) : EReal) ≤ -(-s) := EReal.neg_le_neg_iff.mpr this
    rwa [neg_neg] at h2

/-- The floor in `precisionSet b p` of `x ≠ 0` is `⌊x / u⌋ · u`. -/
lemma isGreatest_precision (x : ℝ) (hx : x ≠ 0) :
    IsGreatest {s | s ∈ precisionSet b p ∧ s ≤ (x : EReal)}
      ((((⌊x / precScale b p x⌋ : ℝ) * precScale b p x : ℝ) : EReal)) := by
  rcases lt_or_gt_of_ne hx with hneg | hpos
  · have h := isLeast_precision_pos (b := b) (p := p) (-x) (neg_pos.mpr hneg)
    rw [precScale_neg] at h
    have h' := isGreatest_of_isLeast_neg (b := b) (p := p) x _ h
    rw [show (-((⌈-x / precScale b p x⌉ : ℝ) * precScale b p x) : ℝ)
        = (⌊x / precScale b p x⌋ : ℝ) * precScale b p x from by
      rw [neg_div, Int.ceil_neg]; push_cast; ring] at h'
    exact h'
  · exact isGreatest_precision_pos x hpos

/-- The ceiling in `precisionSet b p` of `x ≠ 0` is `⌈x / u⌉ · u`. -/
lemma isLeast_precision (x : ℝ) (hx : x ≠ 0) :
    IsLeast {s | s ∈ precisionSet b p ∧ (x : EReal) ≤ s}
      ((((⌈x / precScale b p x⌉ : ℝ) * precScale b p x : ℝ) : EReal)) := by
  rcases lt_or_gt_of_ne hx with hneg | hpos
  · have h := isGreatest_precision_pos (b := b) (p := p) (-x) (neg_pos.mpr hneg)
    rw [precScale_neg] at h
    have h' := isLeast_of_isGreatest_neg (b := b) (p := p) x _ h
    rw [show (-((⌊-x / precScale b p x⌋ : ℝ) * precScale b p x) : ℝ)
        = (⌈x / precScale b p x⌉ : ℝ) * precScale b p x from by
      rw [neg_div, Int.floor_neg]; push_cast; ring] at h'
    exact h'
  · exact isLeast_precision_pos x hpos

/-- The tiebreak: the integer tiebreak on the coordinates at the local scale (the scale of
the candidate closer to `0`). -/
noncomputable def precTiebreak (a c : ↥(precisionSet b p)) : ↥(precisionSet b p) :=
  if Even ⌊precToReal a / precScale b p (min |precToReal a| |precToReal c|)⌋ then a else c

noncomputable instance precisionRoundingTarget : RoundingTarget (precisionSet b p) where
  existsLeastGE x := by
    rcases eq_or_ne x 0 with h0 | hx
    · refine ⟨0, ⟨Or.inl rfl, by rw [h0]; rfl⟩, ?_⟩
      rintro s ⟨_, hs⟩
      rw [h0] at hs
      exact hs
    · exact ⟨_, isLeast_precision x hx⟩
  existsGreatestLE x := by
    rcases eq_or_ne x 0 with h0 | hx
    · refine ⟨0, ⟨Or.inl rfl, by rw [h0]; rfl⟩, ?_⟩
      rintro s ⟨_, hs⟩
      rw [h0] at hs
      exact hs
    · exact ⟨_, isGreatest_precision x hx⟩
  tiebreak := precTiebreak
  tiebreak_mem a c := by
    unfold precTiebreak
    split_ifs
    · exact Or.inl rfl
    · exact Or.inr rfl

/-- The floor of `x ≠ 0` in `precisionSet b p`. -/
lemma val_roundFloor_precision (x : ℝ) (hx : x ≠ 0) :
    (roundFloor (precisionSet b p) x).val
      = (((⌊x / precScale b p x⌋ : ℝ) * precScale b p x : ℝ) : EReal) :=
  (isGreatest_roundFloor (precisionSet b p) x).unique (isGreatest_precision x hx)

/-- The ceiling of `x ≠ 0` in `precisionSet b p`. -/
lemma val_roundCeiling_precision (x : ℝ) (hx : x ≠ 0) :
    (roundCeiling (precisionSet b p) x).val
      = (((⌈x / precScale b p x⌉ : ℝ) * precScale b p x : ℝ) : EReal) :=
  (isLeast_roundCeiling (precisionSet b p) x).unique (isLeast_precision x hx)

/-- The candidate closer to zero lies in `[b^e, b^(e+1))`, so its local scale is `u`. -/
private lemma precScale_min_floor_ceil (x : ℝ) (hx : x ≠ 0) :
    precScale b p (min |(⌊x / precScale b p x⌋ : ℝ) * precScale b p x|
      |(⌈x / precScale b p x⌉ : ℝ) * precScale b p x|) = precScale b p x := by
  set u := precScale b p x with hu_def
  have hu := precScale_pos (b := b) (p := p) x
  set e := Int.log b |x| with he
  -- it suffices that the minimum `m` satisfies `b^e ≤ m < b^(e+1)`
  suffices h : (b : ℝ) ^ e ≤ min |(⌊x / u⌋ : ℝ) * u| |(⌈x / u⌉ : ℝ) * u| ∧
      min |(⌊x / u⌋ : ℝ) * u| |(⌈x / u⌉ : ℝ) * u| < (b : ℝ) ^ (e + 1) by
    have hmin_pos : 0 < min |(⌊x / u⌋ : ℝ) * u| |(⌈x / u⌉ : ℝ) * u| :=
      lt_of_lt_of_le (zpow_pos (hb0R b) _) h.1
    have hlog : Int.log b (min |(⌊x / u⌋ : ℝ) * u| |(⌈x / u⌉ : ℝ) * u|) = e := by
      apply le_antisymm
      · exact Int.lt_add_one_iff.mp ((Int.lt_zpow_iff_log_lt (hb1 b) hmin_pos).mp h.2)
      · exact (Int.zpow_le_iff_le_log (hb1 b) hmin_pos).mp h.1
    unfold precScale
    rw [abs_of_nonneg (le_min (abs_nonneg _) (abs_nonneg _)), hlog, hu_def]
    unfold precScale
    rw [← he]
  have hbe : (b : ℝ) ^ e = (b : ℝ) ^ ((p : ℤ) - 1) * u := by
    rw [hu_def]; unfold precScale; rw [← zpow_add₀ (hb0R b).ne', ← he]; congr 1; ring
  rcases lt_or_gt_of_ne hx with hneg | hpos
  · -- `x < 0`: the candidates are `≤ 0`; the closer one is `⌈x/u⌉ u = -(⌊z/u⌋ u)`, `z = -x`
    set z := -x with hz
    have hz_pos : 0 < z := by rw [hz]; exact neg_pos.mpr hneg
    obtain ⟨hy1, hy2⟩ := y_bounds (b := b) (p := p) z hz_pos
    rw [show precScale b p z = u from by rw [hz, precScale_neg]] at hy1 hy2
    have hfloor_ge : (b : ℝ) ^ ((p : ℤ) - 1) ≤ (⌊z / u⌋ : ℝ) := by
      have hcast : (((b : ℤ) ^ (p - 1) : ℤ) : ℝ) = (b : ℝ) ^ ((p : ℤ) - 1) := by
        push_cast; rw [← zpow_natCast]; congr 1; have := hp0 p; omega
      have hint : ((b : ℤ) ^ (p - 1) : ℤ) ≤ ⌊z / u⌋ :=
        Int.le_floor.mpr (by rw [hcast]; exact hy1)
      have hR : (((b : ℤ) ^ (p - 1) : ℤ) : ℝ) ≤ ((⌊z / u⌋ : ℤ) : ℝ) := by exact_mod_cast hint
      rwa [hcast] at hR
    have hC : (⌈x / u⌉ : ℝ) * u = -((⌊z / u⌋ : ℝ) * u) := by
      rw [hz, neg_div, Int.floor_neg]; push_cast; ring
    have hF : (⌊x / u⌋ : ℝ) * u = -((⌈z / u⌉ : ℝ) * u) := by
      rw [hz, neg_div, Int.ceil_neg]; push_cast; ring
    have hfl_pos : 0 ≤ (⌊z / u⌋ : ℝ) * u :=
      mul_nonneg (le_trans (le_trans zero_le_one one_le_b_pow_pm1) hfloor_ge) hu.le
    have hfc : (⌊z / u⌋ : ℝ) * u ≤ (⌈z / u⌉ : ℝ) * u :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast Int.floor_le_ceil _) hu.le
    rw [hC, hF, abs_neg, abs_neg, abs_of_nonneg hfl_pos, abs_of_nonneg (le_trans hfl_pos hfc),
      min_eq_right hfc, hbe]
    constructor
    · exact mul_le_mul_of_nonneg_right hfloor_ge hu.le
    · have : (⌊z / u⌋ : ℝ) * u ≤ z := by
        rw [← le_div_iff₀ hu]; exact Int.floor_le _
      have hz_lt : z < (b : ℝ) ^ (e + 1) := by
        have h := Int.lt_zpow_succ_log_self (hb1 b) z
        rwa [he, show |x| = z from by rw [hz, abs_of_neg hneg]]
      linarith
  · obtain ⟨hy1, hy2⟩ := y_bounds (b := b) (p := p) x hpos
    rw [← hu_def] at hy1 hy2
    have hfloor_ge : (b : ℝ) ^ ((p : ℤ) - 1) ≤ (⌊x / u⌋ : ℝ) := by
      have hcast : (((b : ℤ) ^ (p - 1) : ℤ) : ℝ) = (b : ℝ) ^ ((p : ℤ) - 1) := by
        push_cast; rw [← zpow_natCast]; congr 1; have := hp0 p; omega
      have hint : ((b : ℤ) ^ (p - 1) : ℤ) ≤ ⌊x / u⌋ :=
        Int.le_floor.mpr (by rw [hcast]; exact hy1)
      have hR : (((b : ℤ) ^ (p - 1) : ℤ) : ℝ) ≤ ((⌊x / u⌋ : ℤ) : ℝ) := by exact_mod_cast hint
      rwa [hcast] at hR
    have hfl_pos : 0 ≤ (⌊x / u⌋ : ℝ) * u :=
      mul_nonneg (le_trans (le_trans zero_le_one one_le_b_pow_pm1) hfloor_ge) hu.le
    have hfc : (⌊x / u⌋ : ℝ) * u ≤ (⌈x / u⌉ : ℝ) * u :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast Int.floor_le_ceil _) hu.le
    rw [abs_of_nonneg hfl_pos, abs_of_nonneg (le_trans hfl_pos hfc), min_eq_left hfc, hbe]
    constructor
    · exact mul_le_mul_of_nonneg_right hfloor_ge hu.le
    · have : (⌊x / u⌋ : ℝ) * u ≤ x := by
        rw [← le_div_iff₀ hu]; exact Int.floor_le _
      have hx_lt : x < (b : ℝ) ^ (e + 1) := by
        have := Int.lt_zpow_succ_log_self (hb1 b) x
        rwa [he, abs_of_pos hpos]
      linarith

/-- `compare` on real coercions into `EReal` is `compare` on the reals. -/
private lemma compare_coe_coe (u v : ℝ) :
    compare ((u : ℝ) : EReal) ((v : ℝ) : EReal) = compare u v := by
  rcases lt_trichotomy u v with h | h | h
  · rw [compare_lt_iff_lt.mpr h, compare_lt_iff_lt.mpr (EReal.coe_lt_coe_iff.mpr h)]
  · rw [h, compare_eq_iff_eq.mpr rfl, compare_eq_iff_eq.mpr rfl]
  · rw [compare_gt_iff_gt.mpr h, compare_gt_iff_gt.mpr (EReal.coe_lt_coe_iff.mpr h)]

/-- `compare` is invariant under scaling both sides by a positive constant. -/
private lemma compare_mul_right (u v c : ℝ) (hc : 0 < c) :
    compare (u * c) (v * c) = compare u v := by
  rcases lt_trichotomy u v with h | h | h
  · rw [compare_lt_iff_lt.mpr h, compare_lt_iff_lt.mpr (mul_lt_mul_of_pos_right h hc)]
  · rw [h, compare_eq_iff_eq.mpr rfl, compare_eq_iff_eq.mpr rfl]
  · rw [compare_gt_iff_gt.mpr h, compare_gt_iff_gt.mpr (mul_lt_mul_of_pos_right h hc)]

/-- The integer tiebreak on two consecutive (or equal) integers picks the even one. -/
private lemma toInt_intTiebreak_consecutive (n m : ℤ) (h : m = n ∨ m = n + 1) :
    toInt (intTiebreak (ofIntSet n) (ofIntSet m)) = if Even n then n else m := by
  unfold intTiebreak
  simp only [toInt_ofIntSet]
  rcases h with rfl | rfl
  · split_ifs <;> simp_all
  · by_cases hn : Even n
    · have h1 : Even n ∧ ¬ Even (n + 1) := ⟨hn, by rw [Int.even_add_one]; exact not_not.mpr hn⟩
      rw [ite_eq_left h1, ite_eq_left hn, toInt_ofIntSet]
    · have h1 : ¬ (Even n ∧ ¬ Even (n + 1)) := fun h => hn h.1
      have h2 : Even (n + 1) ∧ ¬ Even n := ⟨Int.even_add_one.mpr hn, hn⟩
      rw [ite_eq_right h1, ite_eq_left h2, ite_eq_right hn, toInt_ofIntSet]

/-- **Rounding `x ≠ 0` to `precisionSet b p` is integer rounding at the local scale.** -/
theorem val_round_precisionSet (mode : RoundingMode) (x : ℝ) (hx : x ≠ 0) :
    (round (precisionSet b p) mode x).val
      = (((toInt (round intSet mode (x / precScale b p x)) : ℝ) * precScale b p x : ℝ) : EReal) := by
  set u := precScale b p x with hu_def
  have hu : 0 < u := precScale_pos (b := b) (p := p) x
  set y := x / u with hy
  have hF := val_roundFloor_precision (b := b) (p := p) x hx
  have hC := val_roundCeiling_precision (b := b) (p := p) x hx
  rw [← hu_def, ← hy] at hF hC
  have hFi : toInt (roundFloor intSet y) = ⌊y⌋ := toInt_eq_of_val (val_roundFloor_intSet y).symm
  have hCi : toInt (roundCeiling intSet y) = ⌈y⌉ :=
    toInt_eq_of_val (val_roundCeiling_intSet y).symm
  have h0 : (0 ≤ x) ↔ (0 ≤ y) := by
    rw [hy]; constructor
    · intro h; exact div_nonneg h hu.le
    · intro h; exact (div_nonneg_iff.mp h).elim (fun h => h.1) (fun h => by
        have := h.2; linarith)
  cases mode with
  | Floor => rw [show round (precisionSet b p) .Floor x = roundFloor (precisionSet b p) x from rfl,
      show round intSet .Floor y = roundFloor intSet y from rfl, hF, hFi]
  | Ceiling => rw [show round (precisionSet b p) .Ceiling x
        = roundCeiling (precisionSet b p) x from rfl,
      show round intSet .Ceiling y = roundCeiling intSet y from rfl, hC, hCi]
  | Down =>
    show (if 0 ≤ x then roundFloor (precisionSet b p) x else roundCeiling (precisionSet b p) x).val
      = (((toInt (if 0 ≤ y then roundFloor intSet y else roundCeiling intSet y) : ℝ) * u : ℝ)
        : EReal)
    by_cases hx0 : 0 ≤ x
    · rw [ite_eq_left hx0, ite_eq_left (h0.mp hx0), hF, hFi]
    · rw [ite_eq_right hx0, ite_eq_right (fun h => hx0 (h0.mpr h)), hC, hCi]
  | Up =>
    show (if 0 ≤ x then roundCeiling (precisionSet b p) x else roundFloor (precisionSet b p) x).val
      = (((toInt (if 0 ≤ y then roundCeiling intSet y else roundFloor intSet y) : ℝ) * u : ℝ)
        : EReal)
    by_cases hx0 : 0 ≤ x
    · rw [ite_eq_left hx0, ite_eq_left (h0.mp hx0), hC, hCi]
    · rw [ite_eq_right hx0, ite_eq_right (fun h => hx0 (h0.mpr h)), hF, hFi]
  | Nearest =>
    show (let F := roundFloor (precisionSet b p) x
          let C := roundCeiling (precisionSet b p) x
          let dF : EReal := ((x : ℝ) : EReal) - F.val
          let dC : EReal := C.val - ((x : ℝ) : EReal)
          match compare dF dC with
          | .lt => F
          | .gt => C
          | .eq => tiebreak F C).val
      = (((toInt (let F := roundFloor intSet y
          let C := roundCeiling intSet y
          let dF : EReal := ((y : ℝ) : EReal) - F.val
          let dC : EReal := C.val - ((y : ℝ) : EReal)
          match compare dF dC with
          | .lt => F
          | .gt => C
          | .eq => tiebreak F C) : ℝ) * u : ℝ) : EReal)
    simp only []
    rw [hF, hC, val_roundFloor_intSet, val_roundCeiling_intSet]
    have hcmp : compare (((x : ℝ) : EReal) - (((⌊y⌋ : ℝ) * u : ℝ) : EReal))
        ((((⌈y⌉ : ℝ) * u : ℝ) : EReal) - ((x : ℝ) : EReal))
        = compare (((y : ℝ) : EReal) - ((⌊y⌋ : ℝ) : EReal))
          (((⌈y⌉ : ℝ) : EReal) - ((y : ℝ) : EReal)) := by
      rw [← EReal.coe_sub, ← EReal.coe_sub, ← EReal.coe_sub, ← EReal.coe_sub,
        compare_coe_coe, compare_coe_coe]
      conv_rhs => rw [← compare_mul_right _ _ _ hu]
      rw [sub_mul, sub_mul, hy, div_mul_cancel₀ _ hu.ne']
    rw [hcmp]
    rcases h : compare (((y : ℝ) : EReal) - ((⌊y⌋ : ℝ) : EReal))
        (((⌈y⌉ : ℝ) : EReal) - ((y : ℝ) : EReal)) with _ | _ | _
    · simp only []; rw [hF, hFi]
    · simp only []
      show (precTiebreak (roundFloor (precisionSet b p) x) (roundCeiling (precisionSet b p) x)).val
        = (((toInt (intTiebreak (roundFloor intSet y) (roundCeiling intSet y)) : ℝ) * u : ℝ) : EReal)
      have hFr : precToReal (roundFloor (precisionSet b p) x) = (⌊y⌋ : ℝ) * u :=
        precToReal_eq_of_val hF.symm
      have hCr : precToReal (roundCeiling (precisionSet b p) x) = (⌈y⌉ : ℝ) * u :=
        precToReal_eq_of_val hC.symm
      have hFe : ofIntSet ⌊y⌋ = roundFloor intSet y :=
        Subtype.ext (val_roundFloor_intSet y).symm
      have hCe : ofIntSet ⌈y⌉ = roundCeiling intSet y :=
        Subtype.ext (val_roundCeiling_intSet y).symm
      rw [← hFe, ← hCe, toInt_intTiebreak_consecutive ⌊y⌋ ⌈y⌉ (by
        have h1 := Int.floor_le_ceil y
        have h2 := Int.ceil_le_floor_add_one y
        omega)]
      unfold precTiebreak
      simp only [hFr, hCr]
      have hscale := precScale_min_floor_ceil (b := b) (p := p) x hx
      rw [← hu_def, ← hy] at hscale
      rw [hscale, mul_div_cancel_right₀ _ hu.ne', Int.floor_intCast]
      split_ifs with heven
      · exact hF
      · exact hC
    · simp only []; rw [hC, hCi]

end

end RoundingTarget

end Azurite
