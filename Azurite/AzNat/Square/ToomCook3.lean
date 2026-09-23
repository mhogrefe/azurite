/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzNat.Mul.ToomCook3
import Azurite.AzNat.Square.Karatsuba

/-!
# Toom-Cook 3-way squaring for AzNat

Specialization of `toomCook3MulLimbsRec` to the squaring case: when both
operands are equal, the 5 sub-products become 5 sub-squarings, the sign
bit of `v_{-1}` is always positive (since `v_{-1} = (a₀ − a₁ + a₂)² ≥ 0`),
and the inner Karatsuba fallback is replaced by Karatsuba squaring.

The interpolation helper `toomCook3Interpolate` from `AzNat.Mul.ToomCook3`
is reused as-is — it takes the five `v_j` values and a sign bit, and is
agnostic to whether they came from multiplications or squarings.
-/

namespace Azurite.AzNat

/-- Recursive Toom-Cook 3-way squaring of an equal-length slice.
    Falls back to `karatsubaSquareLimbs` when `len < toomThreshold`. -/
def toomCook3SquareLimbsRec (toomThreshold karaThreshold : Nat) (a : Array UInt64)
    (loA len : Nat) (hA : loA + len ≤ a.size) :
    { c : Array UInt64 // c.size = 2 * len } :=
  if h_base : len < toomThreshold ∨ len < 3 then
    ⟨karatsubaSquareLimbs karaThreshold a loA len hA, by
      rw [karatsubaSquareLimbs_size]⟩
  else
    have hlen : 3 ≤ len := by omega
    let k := (len + 2) / 3
    let m := len - 2 * k
    have hk_pos : 0 < k := by show 0 < (len + 2) / 3; omega
    have hk_lt : k < len := by show (len + 2) / 3 < len; omega
    have hk1_lt : k + 1 < len := by show (len + 2) / 3 + 1 < len; omega
    have h2k_le : 2 * k ≤ len := by show 2 * ((len + 2) / 3) ≤ len; omega
    have hm_le_k : m ≤ k := by show len - 2 * ((len + 2) / 3) ≤ (len + 2) / 3; omega
    have hm_lt : m < len := by show len - 2 * ((len + 2) / 3) < len; omega
    -- Slice bounds for the recursive calls.
    have hA0 : loA + k ≤ a.size := by omega
    have hA2 : (loA + 2 * k) + m ≤ a.size := by omega
    -- v_0 = a_0², v_∞ = a_2²
    let v0 := toomCook3SquareLimbsRec toomThreshold karaThreshold a loA k hA0
    let vinf := toomCook3SquareLimbsRec toomThreshold karaThreshold a
                  (loA + 2 * k) m hA2
    -- Evaluation sums (k+1 limbs each); reuse mul-side helpers.
    let s0 := sum012 a loA k m
    let s2 := sum124 a loA k m
    let da := diffM1 a loA k m
    have hs0_sz : 0 + (k + 1) ≤ s0.size := by
      show 0 + (k + 1) ≤ (sum012 a loA k m).size
      unfold sum012; rw [truncatePad_size]; omega
    have hs2_sz : 0 + (k + 1) ≤ s2.size := by
      show 0 + (k + 1) ≤ (sum124 a loA k m).size
      unfold sum124; rw [truncatePad_size]; omega
    have hda_sz : 0 + (k + 1) ≤ da.1.size := diffM1_size_ge _ _ _ _
    -- v_1 = (a₀ + a₁ + a₂)², v_2 = (a₀ + 2a₁ + 4a₂)², v_{-1} = |a₀ − a₁ + a₂|²
    let v1 := toomCook3SquareLimbsRec toomThreshold karaThreshold s0 0 (k + 1) hs0_sz
    let v2 := toomCook3SquareLimbsRec toomThreshold karaThreshold s2 0 (k + 1) hs2_sz
    let vm1 := toomCook3SquareLimbsRec toomThreshold karaThreshold da.1 0 (k + 1) hda_sz
    -- Interpolation reuses `toomCook3Interpolate`.  Squaring's `vm1` is the
    -- square of an integer and therefore always non-negative, so
    -- `vm1_sign = true` unconditionally.
    let result := toomCook3Interpolate (ofLimbs v0.1) (ofLimbs v1.1) (ofLimbs v2.1)
                    (ofLimbs vm1.1) (ofLimbs vinf.1) true k
    ⟨truncatePad result.limbs (2 * len), truncatePad_size _ _⟩
  termination_by len
  decreasing_by
    all_goals simp_wf
    all_goals omega

/-- Toom-Cook 3-way squaring, mirroring the signature of
    `karatsubaSquareLimbs`. -/
def toomCook3SquareLimbs (toomThreshold karaThreshold : Nat) (a : Array UInt64)
    (loA len : Nat) (hA : loA + len ≤ a.size) : Array UInt64 :=
  (toomCook3SquareLimbsRec toomThreshold karaThreshold a loA len hA).1

theorem toomCook3SquareLimbs_size (toomThreshold karaThreshold : Nat) (a : Array UInt64)
    (loA len : Nat) (hA : loA + len ≤ a.size) :
    (toomCook3SquareLimbs toomThreshold karaThreshold a loA len hA).size = 2 * len :=
  (toomCook3SquareLimbsRec toomThreshold karaThreshold a loA len hA).2

end Azurite.AzNat
