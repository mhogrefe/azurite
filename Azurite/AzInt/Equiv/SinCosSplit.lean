/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzInt.SinCosSplit
import Azurite.AzInt.Equiv.Add
import Azurite.AzInt.Equiv.Sub
import Azurite.AzInt.Equiv.Mul
import Azurite.AzInt.Equiv.ShiftLeft
import Azurite.AzNat.Equiv.Mul.Dispatch
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Correctness of the binary splitting for the sine and cosine series

`AltSpec`: the state `(P, B, T)` of the range `[l, l+n)` has `P = (−d₂)^n`,
`B = ∏_{i<n} altDen o (l+i)` and `T / (B · 2^(s n)) = altPartial (d₂/2^s) o l n`, preserved by
`altMerge` (`altSpec_split`).  `prod_altDen_zero`/`prod_altDen_one` identify the denominators
with `(2k)!` and `(2k+1)!`, and `one_add_altPartial_zero`/`_one` the range sums from `0` with the
partial sums of the cosine series and of `sin y / y` in the variable `x = y²`.
-/

namespace Azurite.AzInt

open Finset

/-- The range `[l, l+n)` of the normalized alternating series:
`∑_{k<n} ∏_{i≤k} (−x)/altDen o (l+i)`. -/
noncomputable def altPartial (x : ℝ) (o l n : ℕ) : ℝ :=
  ∑ k ∈ range n, ∏ i ∈ range (k + 1), -x / ((altDen o (l + i) : ℕ) : ℝ)

/-- The state `(P, B, T)` represents the range `[l, l+n)` for `x = d₂/2^s`. -/
def AltSpec (d2 : AzNat) (s o l n : ℕ) (st : AltSplitState) : Prop :=
  st.1.toInt = (-(d2.toNat : ℤ)) ^ n ∧ st.2.1.toNat = ∏ i ∈ range n, altDen o (l + i) ∧
    (st.2.2.toInt : ℝ) / (st.2.1.toNat * 2 ^ (s * n)) = altPartial ((d2.toNat : ℝ) / 2 ^ s) o l n

theorem altDen_pos (o l : ℕ) : 0 < altDen o l := by
  unfold altDen; positivity

theorem toInt_natToAzInt (n : AzNat) : n.toAzInt.toInt = n.toNat := rfl

/-- The product of the ratios over a range. -/
theorem prod_altRatio (d2 : AzNat) (s o l m : ℕ) :
    ∏ i ∈ range m, -((d2.toNat : ℝ) / 2 ^ s) / ((altDen o (l + i) : ℕ) : ℝ)
      = (-(d2.toNat : ℝ)) ^ m / ((∏ i ∈ range m, altDen o (l + i) : ℕ) * 2 ^ (s * m)) := by
  rw [prod_div_distrib, prod_const, card_range, ← neg_div, div_pow, ← pow_mul, Nat.cast_prod]
  rw [div_div, mul_comm]

theorem altSpec_empty (d2 : AzNat) (s o l : ℕ) : AltSpec d2 s o l 0 altEmpty := by
  have h1 : ((1 : AzInt)).toInt = 1 := rfl
  refine ⟨?_, ?_, ?_⟩
  · simp [altEmpty, h1]
  · simp [altEmpty]
  · have h0 : ((0 : AzInt)).toInt = 0 := rfl
    simp [altEmpty, altPartial, h0]

theorem altSpec_leaf (d2 : AzNat) (s o l : ℕ) : AltSpec d2 s o l 1 (altLeaf d2 o l) := by
  have hq : (0 : ℝ) < (altDen o l : ℕ) := by exact_mod_cast altDen_pos o l
  refine ⟨?_, ?_, ?_⟩
  · simp [altLeaf, toInt_natToAzInt]
  · simp [altLeaf, AzNat.toNat_ofNat]
  · simp only [altLeaf, AzNat.toNat_ofNat, altPartial, sum_range_one, zero_add, prod_range_one,
      mul_one, toInt_neg, toInt_natToAzInt, add_zero]
    push_cast
    field_simp

/-- The merge: `[l, l+m)` followed by `[l+m, l+m+n)` represents `[l, l+m+n)`. -/
theorem altSpec_merge (d2 : AzNat) {s o l m n : ℕ} {x y : AltSplitState}
    (hx : AltSpec d2 s o l m x) (hy : AltSpec d2 s o (l + m) n y) :
    AltSpec d2 s o l (m + n) (altMerge s n x y) := by
  obtain ⟨hxP, hxB, hxT⟩ := hx
  obtain ⟨hyP, hyB, hyT⟩ := hy
  have hB1 : (0 : ℝ) < x.2.1.toNat := by
    rw [hxB]; exact_mod_cast prod_pos fun k _ => altDen_pos _ _
  have hB2 : (0 : ℝ) < y.2.1.toNat := by
    rw [hyB]; exact_mod_cast prod_pos fun k _ => altDen_pos _ _
  refine ⟨?_, ?_, ?_⟩
  · simp only [altMerge, toInt_mul, hxP, hyP, pow_add]
  · simp only [altMerge, AzNat.toNat_mul, hxB, hyB, prod_range_add]
    congr 1
    exact prod_congr rfl fun k _ => by rw [Nat.add_assoc]
  · have hsplit : altPartial ((d2.toNat : ℝ) / 2 ^ s) o l (m + n)
        = altPartial ((d2.toNat : ℝ) / 2 ^ s) o l m
          + (x.1.toInt : ℝ) / (x.2.1.toNat * 2 ^ (s * m))
            * altPartial ((d2.toNat : ℝ) / 2 ^ s) o (l + m) n := by
      unfold altPartial
      rw [sum_range_add, mul_sum]
      congr 1
      refine sum_congr rfl fun k _ => ?_
      rw [show m + k + 1 = m + (k + 1) by ring, prod_range_add]
      congr 1
      · rw [prod_altRatio, hxP, hxB]
        push_cast
        ring
      · exact prod_congr rfl fun i _ => by rw [Nat.add_assoc]
    simp only [altMerge, toInt_add, toInt_mul, toInt_hShiftLeft, toInt_natToAzInt,
      AzNat.toNat_mul]
    push_cast
    rw [hsplit, ← hxT, ← hyT, show s * (m + n) = s * m + s * n by ring, pow_add]
    have hB1' := hB1.ne'
    have hB2' := hB2.ne'
    field_simp

/-- The sequential fallback represents its range. -/
theorem altSpec_seq (d2 : AzNat) (s o : ℕ) : ∀ n l, AltSpec d2 s o l n (altSeq d2 s o l n)
  | 0, l => altSpec_empty d2 s o l
  | n + 1, l => by
    rw [altSeq, show n + 1 = 1 + n by ring]
    exact altSpec_merge d2 (altSpec_leaf d2 s o l) (altSpec_seq d2 s o n (l + 1))

/-- The splitting represents its range, for every fuel. -/
theorem altSpec_splitFuel (d2 : AzNat) (s o : ℕ) :
    ∀ fuel l n, AltSpec d2 s o l n (altSplitFuel d2 s o fuel l n)
  | 0, l, n => by rw [altSplitFuel]; exact altSpec_seq d2 s o n l
  | _ + 1, l, 0 => by rw [altSplitFuel]; exact altSpec_empty d2 s o l
  | _ + 1, l, 1 => by rw [altSplitFuel]; exact altSpec_leaf d2 s o l
  | fuel + 1, l, n + 2 => by
    simp only [altSplitFuel]
    have hm : (n + 2) / 2 ≤ n + 2 := Nat.div_le_self _ _
    have h := altSpec_merge d2 (altSpec_splitFuel d2 s o fuel l ((n + 2) / 2))
      (altSpec_splitFuel d2 s o fuel (l + (n + 2) / 2) (n + 2 - (n + 2) / 2))
    rwa [Nat.add_sub_cancel' hm] at h

theorem altSpec_split (d2 : AzNat) (s o l n : ℕ) : AltSpec d2 s o l n (altSplit d2 s o l n) :=
  altSpec_splitFuel d2 s o n l n

/-- `∏_{i<k} (2i+1)(2i+2) = (2k)!`. -/
theorem prod_altDen_zero (k : ℕ) : ∏ i ∈ range k, altDen 0 (0 + i) = (2 * k).factorial := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [prod_range_succ, ih, show 2 * (k + 1) = 2 * k + 1 + 1 by ring, Nat.factorial_succ,
      Nat.factorial_succ]
    unfold altDen
    ring

/-- `∏_{i<k} (2i+2)(2i+3) = (2k+1)!`. -/
theorem prod_altDen_one (k : ℕ) : ∏ i ∈ range k, altDen 1 (0 + i) = (2 * k + 1).factorial := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [prod_range_succ, ih, show 2 * (k + 1) + 1 = 2 * k + 1 + 1 + 1 by ring,
      Nat.factorial_succ (2 * k + 1 + 1), Nat.factorial_succ (2 * k + 1)]
    unfold altDen
    ring

/-- The range sum from `0` with offset `0` is the cosine series in `x = y²` without its first
term: `1 + ∑_{k<N} ∏_{i≤k} (−x)/((2i+1)(2i+2)) = ∑_{k≤N} (−1)^k x^k/(2k)!`. -/
theorem one_add_altPartial_zero (x : ℝ) (N : ℕ) :
    1 + altPartial x 0 0 N = ∑ k ∈ range (N + 1), (-1) ^ k * (x ^ k / ((2 * k).factorial : ℝ)) := by
  rw [sum_range_succ', pow_zero, pow_zero, mul_zero, Nat.factorial_zero, Nat.cast_one, div_one,
    mul_one, add_comm]
  congr 1
  unfold altPartial
  refine sum_congr rfl fun k _ => ?_
  rw [prod_div_distrib, prod_const, card_range, ← Nat.cast_prod, prod_altDen_zero, neg_pow]
  ring

/-- The range sum from `0` with offset `1` is the series of `sin y / y` in `x = y²` without its
first term: `1 + ∑_{k<N} ∏_{i≤k} (−x)/((2i+2)(2i+3)) = ∑_{k≤N} (−1)^k x^k/(2k+1)!`. -/
theorem one_add_altPartial_one (x : ℝ) (N : ℕ) :
    1 + altPartial x 1 0 N
      = ∑ k ∈ range (N + 1), (-1) ^ k * (x ^ k / ((2 * k + 1).factorial : ℝ)) := by
  rw [sum_range_succ', pow_zero, pow_zero, mul_zero, zero_add, Nat.factorial_one, Nat.cast_one,
    div_one, mul_one, add_comm]
  congr 1
  unfold altPartial
  refine sum_congr rfl fun k _ => ?_
  rw [prod_div_distrib, prod_const, card_range, ← Nat.cast_prod, prod_altDen_one, neg_pow]
  ring

end Azurite.AzInt
