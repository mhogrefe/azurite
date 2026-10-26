/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzNat.ExpSplit
import Azurite.AzNat.Equiv.AtanhSplit
import Azurite.AzNat.Equiv.ShiftLeft
import Mathlib.Data.Nat.Factorial.BigOperators

/-!
# Correctness of the binary splitting for the exponential series

`expNumDen_eq : num / (den · 2^(sN)) = ∑_{m≤N} (p/2^s)^m / m!`, through the invariant `Spec`
(`T / (B · 2^(s n))` is the normalized range sum, `P = p^n`, `B = ∏ (l+i+1)`), preserved by
`expMerge`.
-/

namespace Azurite.AzNat

open Finset

/-- The range `[l, l+n)` of the normalized series: `∑_{k<n} ∏_{i≤k} x/(l+i+1)`. -/
noncomputable def expPartial (x : ℝ) (l n : ℕ) : ℝ :=
  ∑ k ∈ range n, ∏ i ∈ range (k + 1), x / ((l + i + 1 : ℕ) : ℝ)

/-- The state `(P, B, T)` represents the range `[l, l+n)` for `x = p/2^s`. -/
def ExpSpec (p : AzNat) (s l n : ℕ) (st : SplitState) : Prop :=
  st.1.toNat = p.toNat ^ n ∧ st.2.1.toNat = ∏ i ∈ range n, (l + i + 1) ∧
    (st.2.2.toNat : ℝ) / (st.2.1.toNat * 2 ^ (s * n)) = expPartial ((p.toNat : ℝ) / 2 ^ s) l n

/-- The product of the ratios over a range. -/
theorem prod_ratio (p : AzNat) (s l m : ℕ) :
    ∏ i ∈ range m, ((p.toNat : ℝ) / 2 ^ s) / ((l + i + 1 : ℕ) : ℝ)
      = (p.toNat : ℝ) ^ m / ((∏ i ∈ range m, (l + i + 1) : ℕ) * 2 ^ (s * m)) := by
  rw [prod_div_distrib, prod_const, card_range, div_pow, ← pow_mul, Nat.cast_prod]
  rw [div_div, mul_comm]

theorem expSpec_empty (p : AzNat) (s l : ℕ) : ExpSpec p s l 0 expEmpty := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [expEmpty, expPartial]

theorem expSpec_leaf (p : AzNat) (s l : ℕ) : ExpSpec p s l 1 (expLeaf p l) := by
  refine ⟨?_, ?_, ?_⟩
  · simp [expLeaf]
  · simp [expLeaf, toNat_ofNat]
  · simp only [expLeaf, toNat_ofNat, expPartial, sum_range_one, zero_add, prod_range_one, mul_one]
    push_cast
    field_simp
    ring

/-- The merge: `[l, l+m)` followed by `[l+m, l+m+n)` represents `[l, l+m+n)`. -/
theorem expSpec_merge (p : AzNat) {s l m n : ℕ} {x y : SplitState} (hx : ExpSpec p s l m x)
    (hy : ExpSpec p s (l + m) n y) : ExpSpec p s l (m + n) (expMerge s n x y) := by
  obtain ⟨hxP, hxB, hxT⟩ := hx
  obtain ⟨hyP, hyB, hyT⟩ := hy
  have hB1 : (0 : ℝ) < x.2.1.toNat := by
    rw [hxB]; exact_mod_cast prod_pos fun k _ => by omega
  have hB2 : (0 : ℝ) < y.2.1.toNat := by
    rw [hyB]; exact_mod_cast prod_pos fun k _ => by omega
  refine ⟨?_, ?_, ?_⟩
  · simp only [expMerge, toNat_mul, hxP, hyP, pow_add]
  · simp only [expMerge, toNat_mul, hxB, hyB, prod_range_add]
    congr 1
    exact prod_congr rfl fun k _ => by ring_nf
  · -- the second range's terms carry the factor `P₁/(B₁ 2^(s m))`
    have hsplit : expPartial ((p.toNat : ℝ) / 2 ^ s) l (m + n)
        = expPartial ((p.toNat : ℝ) / 2 ^ s) l m
          + (x.1.toNat : ℝ) / (x.2.1.toNat * 2 ^ (s * m))
            * expPartial ((p.toNat : ℝ) / 2 ^ s) (l + m) n := by
      unfold expPartial
      rw [sum_range_add, mul_sum]
      congr 1
      refine sum_congr rfl fun k _ => ?_
      rw [show m + k + 1 = m + (k + 1) by ring, prod_range_add]
      congr 1
      · rw [prod_ratio, hxP, hxB]
        push_cast
        ring
      · exact prod_congr rfl fun i _ => by rw [show l + (m + i) + 1 = l + m + i + 1 by ring]
    simp only [expMerge, toNat_add, toNat_mul, toNat_hShiftLeft, Nat.shiftLeft_eq]
    push_cast
    rw [hsplit, ← hxT, ← hyT, show s * (m + n) = s * m + s * n by ring, pow_add]
    have hB1' := hB1.ne'
    have hB2' := hB2.ne'
    field_simp

/-- The sequential fallback represents its range. -/
theorem expSpec_seq (p : AzNat) (s : ℕ) : ∀ n l, ExpSpec p s l n (expSeq p s l n)
  | 0, l => expSpec_empty p s l
  | n + 1, l => by
    rw [expSeq, show n + 1 = 1 + n by ring]
    exact expSpec_merge p (expSpec_leaf p s l) (expSpec_seq p s n (l + 1))

/-- The splitting represents its range, for every fuel. -/
theorem expSpec_splitFuel (p : AzNat) (s : ℕ) :
    ∀ fuel l n, ExpSpec p s l n (expSplitFuel p s fuel l n)
  | 0, l, n => by rw [expSplitFuel]; exact expSpec_seq p s n l
  | _ + 1, l, 0 => by rw [expSplitFuel]; exact expSpec_empty p s l
  | _ + 1, l, 1 => by rw [expSplitFuel]; exact expSpec_leaf p s l
  | fuel + 1, l, n + 2 => by
    simp only [expSplitFuel]
    have hm : (n + 2) / 2 ≤ n + 2 := Nat.div_le_self _ _
    have h := expSpec_merge p (expSpec_splitFuel p s fuel l ((n + 2) / 2))
      (expSpec_splitFuel p s fuel (l + (n + 2) / 2) (n + 2 - (n + 2) / 2))
    rwa [Nat.add_sub_cancel' hm] at h

theorem expSpec_split (p : AzNat) (s l n : ℕ) : ExpSpec p s l n (expSplit p s l n) :=
  expSpec_splitFuel p s n l n

/-- The denominator `B` is positive. -/
theorem expNumDen_den_pos (p : AzNat) (s N : ℕ) : 0 < (expNumDen p s N).2.toNat := by
  obtain ⟨-, hB, -⟩ := expSpec_split p s 0 N
  simp only [expNumDen]
  rw [hB]
  exact prod_pos fun k _ => by omega

/-- The normalized range sum from `0` is the tail of the exponential series:
`∑_{k<N} ∏_{i≤k} x/(i+1) = ∑_{k<N} x^(k+1)/(k+1)!`. -/
theorem expPartial_zero (x : ℝ) (N : ℕ) :
    expPartial x 0 N = ∑ k ∈ range N, x ^ (k + 1) / ((k + 1).factorial : ℝ) := by
  unfold expPartial
  refine sum_congr rfl fun k _ => ?_
  simp only [zero_add]
  rw [prod_div_distrib, prod_const, card_range, ← Nat.cast_prod,
    Finset.prod_range_add_one_eq_factorial]

/-- **The binary splitting computes the exact partial sum**:
`num / (den · 2^(sN)) = ∑_{m≤N} (p/2^s)^m / m!`. -/
theorem expNumDen_eq (p : AzNat) (s N : ℕ) :
    ((expNumDen p s N).1.toNat : ℝ) / ((expNumDen p s N).2.toNat * 2 ^ (s * N))
      = ∑ m ∈ range (N + 1), ((p.toNat : ℝ) / 2 ^ s) ^ m / (m.factorial : ℝ) := by
  obtain ⟨-, hB, hT⟩ := expSpec_split p s 0 N
  have hB0 : (0 : ℝ) < (expSplit p s 0 N).2.1.toNat := by
    rw [hB]; exact_mod_cast prod_pos fun k _ => by omega
  simp only [expNumDen, toNat_add, toNat_hShiftLeft, Nat.shiftLeft_eq]
  push_cast
  rw [sum_range_succ', ← expPartial_zero, ← hT, add_div, pow_zero, Nat.factorial_zero,
    Nat.cast_one, div_one, div_self (by positivity), add_comm]

end Azurite.AzNat
