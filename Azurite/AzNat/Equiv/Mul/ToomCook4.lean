/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzNat.Mul.ToomCook4
import Azurite.AzNat.Equiv.Mul.ToomEval
import Azurite.AzInt.Equiv.ShiftLeft
import Azurite.AzInt.Equiv.ShiftRight

/-!
# Correctness of Toom–Cook 4-way multiplication

`toomCook4MulLimbs_toNat`: the `2·len`-limb result is the product of the two slices.

The proof has three layers.  `toomCook4Interpolate_toInt` is the algebra: if the seven inputs
are the values of `Σ c_i x^i` at the seven points, the outputs are `c_0, …, c_6` (each step is a
`ring` identity plus the exactness of one division).  `toomCook4_core_toNat` is array-free: for
eight block values below `β^k` and any magnitude multiplier correct on `(k + 1)`-limb buffers,
the assembled interpolation of the seven signed products is the product of the two block
polynomials.  The main theorem supplies the recursive call as the multiplier (the induction
hypothesis at `k + 1 < len`) and the block decomposition of the slices.
-/

namespace Azurite.AzNat

/-! ### Literal casts -/

lemma int64_toInt_zero : (0 : Int64).toInt = 0 := by decide
lemma int64_toInt_one : (1 : Int64).toInt = 1 := by decide
lemma int64_toInt_neg_one : (-1 : Int64).toInt = -1 := by decide
lemma int64_toInt_two : (2 : Int64).toInt = 2 := by decide
lemma int64_toInt_neg_two : (-2 : Int64).toInt = -2 := by decide
lemma uint64_toNat_3 : ((3 : UInt64).toNat : Int) = 3 := by decide
lemma uint64_toNat_5 : ((5 : UInt64).toNat : Int) = 5 := by decide
lemma uint64_toNat_9 : ((9 : UInt64).toNat : Int) = 9 := by decide
lemma uint64_toNat_17 : ((17 : UInt64).toNat : Int) = 17 := by decide

/-- Right shift as integer division by `2^sh`. -/
lemma toInt_hShiftRight_pow (z : AzInt) (sh : Nat) :
    (z >>> sh).toInt = z.toInt / (2 ^ sh : Int) := by
  rw [AzInt.toInt_hShiftRight, Int.shiftRight_eq_div_pow]
  push_cast
  rfl

/-! ### The interpolation -/

/-- **Toom-4 interpolation is exact**: from the values of `C = Σ c_i x^i` at `0, ±1, ±2, 1/2, ∞`
(the `1/2` value scaled by `2^6`), `toomCook4Interpolate` returns `[c_0, …, c_6]`. -/
theorem toomCook4Interpolate_toInt (v0 v1 vm1 v2 vm2 vh vinf : AzInt) (c0 c1 c2 c3 c4 c5 c6 : Int)
    (hv0 : v0.toInt = c0)
    (hv1 : v1.toInt = c0 + c1 + c2 + c3 + c4 + c5 + c6)
    (hvm1 : vm1.toInt = c0 - c1 + c2 - c3 + c4 - c5 + c6)
    (hv2 : v2.toInt = c0 + 2 * c1 + 4 * c2 + 8 * c3 + 16 * c4 + 32 * c5 + 64 * c6)
    (hvm2 : vm2.toInt = c0 - 2 * c1 + 4 * c2 - 8 * c3 + 16 * c4 - 32 * c5 + 64 * c6)
    (hvh : vh.toInt = 64 * c0 + 32 * c1 + 16 * c2 + 8 * c3 + 4 * c4 + 2 * c5 + c6)
    (hvinf : vinf.toInt = c6) :
    (toomCook4Interpolate v0 v1 vm1 v2 vm2 vh vinf).map AzInt.toInt
      = [c0, c1, c2, c3, c4, c5, c6] := by
  unfold toomCook4Interpolate
  simp only [List.map_cons, List.map_nil]
  set e1 := ((v1 + vm1) >>> 1) - v0 - vinf with he1def
  set o1 := (v1 - vm1) >>> 1 with ho1def
  set e2 := ((v2 + vm2) >>> 1) - v0 - (vinf <<< 6) with he2def
  set o2 := (v2 - vm2) >>> 2 with ho2def
  have he1 : e1.toInt = c2 + c4 := by
    rw [he1def, AzInt.toInt_sub, AzInt.toInt_sub, toInt_hShiftRight_pow, AzInt.toInt_add, hv1, hvm1,
      hv0, hvinf, show c0 + c1 + c2 + c3 + c4 + c5 + c6 + (c0 - c1 + c2 - c3 + c4 - c5 + c6)
        = 2 ^ 1 * (c0 + c2 + c4 + c6) by ring, Int.mul_ediv_cancel_left _ (by norm_num)]
    ring
  have ho1 : o1.toInt = c1 + c3 + c5 := by
    rw [ho1def, toInt_hShiftRight_pow, AzInt.toInt_sub, hv1, hvm1,
      show c0 + c1 + c2 + c3 + c4 + c5 + c6 - (c0 - c1 + c2 - c3 + c4 - c5 + c6)
        = 2 ^ 1 * (c1 + c3 + c5) by ring, Int.mul_ediv_cancel_left _ (by norm_num)]
  have he2 : e2.toInt = 4 * c2 + 16 * c4 := by
    rw [he2def, AzInt.toInt_sub, AzInt.toInt_sub, toInt_hShiftRight_pow, AzInt.toInt_add, hv2, hvm2,
      hv0, AzInt.toInt_hShiftLeft, hvinf,
      show c0 + 2 * c1 + 4 * c2 + 8 * c3 + 16 * c4 + 32 * c5 + 64 * c6
          + (c0 - 2 * c1 + 4 * c2 - 8 * c3 + 16 * c4 - 32 * c5 + 64 * c6)
        = 2 ^ 1 * (c0 + 4 * c2 + 16 * c4 + 64 * c6) by ring, Int.mul_ediv_cancel_left _ (by norm_num)]
    ring
  have ho2 : o2.toInt = c1 + 4 * c3 + 16 * c5 := by
    rw [ho2def, toInt_hShiftRight_pow, AzInt.toInt_sub, hv2, hvm2,
      show c0 + 2 * c1 + 4 * c2 + 8 * c3 + 16 * c4 + 32 * c5 + 64 * c6
          - (c0 - 2 * c1 + 4 * c2 - 8 * c3 + 16 * c4 - 32 * c5 + 64 * c6)
        = 2 ^ 2 * (c1 + 4 * c3 + 16 * c5) by ring, Int.mul_ediv_cancel_left _ (by norm_num)]
  set c4' := AzInt.exactDivOdd 3 inv3 ((e2 - (e1 <<< 2)) >>> 2) with hc4def
  have hnum4 : ((e2 - (e1 <<< 2)) >>> 2).toInt = 3 * c4 := by
    rw [toInt_hShiftRight_pow, AzInt.toInt_sub, AzInt.toInt_hShiftLeft, he2, he1,
      show 4 * c2 + 16 * c4 - (c2 + c4) * 2 ^ 2 = 2 ^ 2 * (3 * c4) by ring,
      Int.mul_ediv_cancel_left _ (by norm_num)]
  have hc4 : c4'.toInt = c4 := by
    rw [hc4def, AzInt.toInt_exactDivOdd 3 inv3 mul_inv3 _ (by rw [hnum4, uint64_toNat_3]; exact Dvd.intro _ rfl),
      hnum4, uint64_toNat_3, Int.mul_ediv_cancel_left _ (by norm_num)]
  set c2' := e1 - c4' with hc2def
  have hc2 : c2'.toInt = c2 := by
    rw [hc2def, AzInt.toInt_sub, he1, hc4]; ring
  set h := (vh - (v0 <<< 6) - vinf - (c2' <<< 4) - (c4' <<< 2)) >>> 1 with hhdef
  have hh : h.toInt = 16 * c1 + 4 * c3 + c5 := by
    rw [hhdef, toInt_hShiftRight_pow, AzInt.toInt_sub, AzInt.toInt_sub, AzInt.toInt_sub,
      AzInt.toInt_sub, AzInt.toInt_hShiftLeft, AzInt.toInt_hShiftLeft, AzInt.toInt_hShiftLeft,
      hvh, hv0, hvinf, hc2, hc4,
      show 64 * c0 + 32 * c1 + 16 * c2 + 8 * c3 + 4 * c4 + 2 * c5 + c6 - c0 * 2 ^ 6 - c6
          - c2 * 2 ^ 4 - c4 * 2 ^ 2 = 2 ^ 1 * (16 * c1 + 4 * c3 + c5) by ring,
      Int.mul_ediv_cancel_left _ (by norm_num)]
  set c3' := AzInt.exactDivOdd 9 inv9 (o1.mulUInt64 17 - o2 - h) with hc3def
  have hnum3 : (o1.mulUInt64 17 - o2 - h).toInt = 9 * c3 := by
    rw [AzInt.toInt_sub, AzInt.toInt_sub, AzInt.toInt_mulUInt64, ho1, ho2, hh, uint64_toNat_17]
    ring
  have hc3 : c3'.toInt = c3 := by
    rw [hc3def, AzInt.toInt_exactDivOdd 9 inv9 mul_inv9 _ (by rw [hnum3, uint64_toNat_9]; exact Dvd.intro _ rfl),
      hnum3, uint64_toNat_9, Int.mul_ediv_cancel_left _ (by norm_num)]
  have hp : (AzInt.exactDivOdd 3 inv3 (o2 - o1)).toInt = c3 + 5 * c5 := by
    have hn : (o2 - o1).toInt = 3 * (c3 + 5 * c5) := by rw [AzInt.toInt_sub, ho2, ho1]; ring
    rw [AzInt.toInt_exactDivOdd 3 inv3 mul_inv3 _ (by rw [hn, uint64_toNat_3]; exact Dvd.intro _ rfl),
      hn, uint64_toNat_3, Int.mul_ediv_cancel_left _ (by norm_num)]
  have hr : (AzInt.exactDivOdd 3 inv3 (h - o1)).toInt = 5 * c1 + c3 := by
    have hn : (h - o1).toInt = 3 * (5 * c1 + c3) := by rw [AzInt.toInt_sub, hh, ho1]; ring
    rw [AzInt.toInt_exactDivOdd 3 inv3 mul_inv3 _ (by rw [hn, uint64_toNat_3]; exact Dvd.intro _ rfl),
      hn, uint64_toNat_3, Int.mul_ediv_cancel_left _ (by norm_num)]
  have hc5 : (AzInt.exactDivOdd 5 inv5 (AzInt.exactDivOdd 3 inv3 (o2 - o1) - c3')).toInt = c5 := by
    have hn : (AzInt.exactDivOdd 3 inv3 (o2 - o1) - c3').toInt = 5 * c5 := by
      rw [AzInt.toInt_sub, hp, hc3]; ring
    rw [AzInt.toInt_exactDivOdd 5 inv5 mul_inv5 _ (by rw [hn, uint64_toNat_5]; exact Dvd.intro _ rfl),
      hn, uint64_toNat_5, Int.mul_ediv_cancel_left _ (by norm_num)]
  have hc1 : (AzInt.exactDivOdd 5 inv5 (AzInt.exactDivOdd 3 inv3 (h - o1) - c3')).toInt = c1 := by
    have hn : (AzInt.exactDivOdd 3 inv3 (h - o1) - c3').toInt = 5 * c1 := by
      rw [AzInt.toInt_sub, hr, hc3]; ring
    rw [AzInt.toInt_exactDivOdd 5 inv5 mul_inv5 _ (by rw [hn, uint64_toNat_5]; exact Dvd.intro _ rfl),
      hn, uint64_toNat_5, Int.mul_ediv_cancel_left _ (by norm_num)]
  rw [hv0, hc1, hc2, hc3, hc4, hc5, hvinf]

/-! ### The array-free core -/

/-- A Horner value at `|c| ≤ 2` of four blocks below `β^k` fits in `k + 1` limbs. -/
theorem hornerInt64_four_abs_lt (k : Nat) (c : Int64) (hc : c.toInt.natAbs ≤ 2)
    (b0 b1 b2 b3 : AzInt) (h0 : b0.abs.toNat < 2 ^ (64 * k)) (h1 : b1.abs.toNat < 2 ^ (64 * k))
    (h2 : b2.abs.toNat < 2 ^ (64 * k)) (h3 : b3.abs.toNat < 2 ^ (64 * k)) :
    (hornerInt64 c [b0, b1, b2, b3]).abs.toNat < 2 ^ (64 * (k + 1)) := by
  rw [← AzInt.natAbs_toInt, toInt_hornerInt64]
  refine lt_of_le_of_lt (natAbs_polyEvalInt_le _ _) ?_
  simp only [List.map_cons, List.map_nil, polyEvalNat_cons, polyEvalNat_nil, AzInt.natAbs_toInt]
  have hpow : 2 ^ (64 * (k + 1)) = 2 ^ (64 * k) * 2 ^ 64 := by
    rw [show 64 * (k + 1) = 64 * k + 64 by ring, pow_add]
  rw [hpow]
  have hB : 0 < 2 ^ (64 * k) := pow_pos (by norm_num) _
  have hc' : c.toInt.natAbs = 0 ∨ c.toInt.natAbs = 1 ∨ c.toInt.natAbs = 2 := by omega
  rcases hc' with h | h | h <;> rw [h] <;> omega

/-- The four blocks of a slice as an explicit list. -/
theorem blocks_four (a : Array UInt64) (lo len k : Nat) :
    blocks a lo len k 4 = [(block a lo len k 0).toAzInt, (block a lo len k 1).toAzInt,
      (block a lo len k 2).toAzInt, (block a lo len k 3).toAzInt] := rfl

/-- **The algebra of Toom-4**, with no arrays or multipliers in sight: if the seven `AzInt`s are
the pointwise products of the Horner evaluations of two block lists, assembling their
interpolation gives the product of the two block polynomials. -/
theorem toomCook4_assemble_toNat (k : Nat) (a0 a1 a2 a3 b0 b1 b2 b3 : AzNat)
    (v0 v1 vm1 v2 vm2 vh vinf : AzInt)
    (hv0 : v0.toInt = (hornerInt64 0 [a0.toAzInt, a1.toAzInt, a2.toAzInt, a3.toAzInt]).toInt
      * (hornerInt64 0 [b0.toAzInt, b1.toAzInt, b2.toAzInt, b3.toAzInt]).toInt)
    (hv1 : v1.toInt = (hornerInt64 1 [a0.toAzInt, a1.toAzInt, a2.toAzInt, a3.toAzInt]).toInt
      * (hornerInt64 1 [b0.toAzInt, b1.toAzInt, b2.toAzInt, b3.toAzInt]).toInt)
    (hvm1 : vm1.toInt = (hornerInt64 (-1) [a0.toAzInt, a1.toAzInt, a2.toAzInt, a3.toAzInt]).toInt
      * (hornerInt64 (-1) [b0.toAzInt, b1.toAzInt, b2.toAzInt, b3.toAzInt]).toInt)
    (hv2 : v2.toInt = (hornerInt64 2 [a0.toAzInt, a1.toAzInt, a2.toAzInt, a3.toAzInt]).toInt
      * (hornerInt64 2 [b0.toAzInt, b1.toAzInt, b2.toAzInt, b3.toAzInt]).toInt)
    (hvm2 : vm2.toInt = (hornerInt64 (-2) [a0.toAzInt, a1.toAzInt, a2.toAzInt, a3.toAzInt]).toInt
      * (hornerInt64 (-2) [b0.toAzInt, b1.toAzInt, b2.toAzInt, b3.toAzInt]).toInt)
    (hvh : vh.toInt = (hornerInt64 2 [a3.toAzInt, a2.toAzInt, a1.toAzInt, a0.toAzInt]).toInt
      * (hornerInt64 2 [b3.toAzInt, b2.toAzInt, b1.toAzInt, b0.toAzInt]).toInt)
    (hvinf : vinf.toInt = (hornerInt64 0 [a3.toAzInt, a2.toAzInt, a1.toAzInt, a0.toAzInt]).toInt
      * (hornerInt64 0 [b3.toAzInt, b2.toAzInt, b1.toAzInt, b0.toAzInt]).toInt) :
    (assemble k ((toomCook4Interpolate v0 v1 vm1 v2 vm2 vh vinf).map AzInt.abs)).toNat
      = polyEvalNat (2 ^ (64 * k)) [a0.toNat, a1.toNat, a2.toNat, a3.toNat]
        * polyEvalNat (2 ^ (64 * k)) [b0.toNat, b1.toNat, b2.toNat, b3.toNat] := by
  -- the evaluations as polynomials in the block values
  have hev : ∀ (c : Int64) (x0 x1 x2 x3 : AzNat),
      (hornerInt64 c [x0.toAzInt, x1.toAzInt, x2.toAzInt, x3.toAzInt]).toInt
        = (((x3.toNat : Int) * c.toInt + (x2.toNat : Int)) * c.toInt + (x1.toNat : Int)) * c.toInt
          + (x0.toNat : Int) := by
    intro c x0 x1 x2 x3
    simp only [toInt_hornerInt64, List.map_cons, List.map_nil, polyEvalInt_cons, polyEvalInt_nil,
      Azurite.AzNat.toInt_toAzInt, zero_mul, zero_add]
  rw [hev, hev] at hv0 hv1 hvm1 hv2 hvm2 hvh hvinf
  -- the interpolation recovers the product polynomial's coefficients
  have hinterp := toomCook4Interpolate_toInt v0 v1 vm1 v2 vm2 vh vinf
    ((a0.toNat : Int) * (b0.toNat : Int)) ((a0.toNat : Int) * (b1.toNat : Int) + (a1.toNat : Int) * (b0.toNat : Int)) ((a0.toNat : Int) * (b2.toNat : Int) + (a1.toNat : Int) * (b1.toNat : Int) + (a2.toNat : Int) * (b0.toNat : Int)) ((a0.toNat : Int) * (b3.toNat : Int) + (a1.toNat : Int) * (b2.toNat : Int) + (a2.toNat : Int) * (b1.toNat : Int) + (a3.toNat : Int) * (b0.toNat : Int)) ((a1.toNat : Int) * (b3.toNat : Int) + (a2.toNat : Int) * (b2.toNat : Int) + (a3.toNat : Int) * (b1.toNat : Int)) ((a2.toNat : Int) * (b3.toNat : Int) + (a3.toNat : Int) * (b2.toNat : Int)) ((a3.toNat : Int) * (b3.toNat : Int))
    (by rw [hv0, int64_toInt_zero]; ring)
    (by rw [hv1, int64_toInt_one]; ring)
    (by rw [hvm1, int64_toInt_neg_one]; ring)
    (by rw [hv2, int64_toInt_two]; ring)
    (by rw [hvm2, int64_toInt_neg_two]; ring)
    (by rw [hvh, int64_toInt_two]; ring)
    (by rw [hvinf, int64_toInt_zero]; ring)
  obtain ⟨e0, e1, e2, e3, e4, e5, e6, hcs⟩ : ∃ e0 e1 e2 e3 e4 e5 e6 : AzInt,
      toomCook4Interpolate v0 v1 vm1 v2 vm2 vh vinf = [e0, e1, e2, e3, e4, e5, e6] :=
    ⟨_, _, _, _, _, _, _, rfl⟩
  rw [hcs] at hinterp ⊢
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hinterp
  obtain ⟨h0, h1, h2, h3, h4, h5, h6⟩ := hinterp
  -- the magnitudes of the coefficients are the coefficients
  have hE0 : (e0.abs.toNat : Int) = (a0.toNat : Int) * (b0.toNat : Int) := by
    rw [← AzInt.natAbs_toInt, h0, Int.natAbs_of_nonneg (by positivity)]
  have hE1 : (e1.abs.toNat : Int) = (a0.toNat : Int) * (b1.toNat : Int) + (a1.toNat : Int) * (b0.toNat : Int) := by
    rw [← AzInt.natAbs_toInt, h1, Int.natAbs_of_nonneg (by positivity)]
  have hE2 : (e2.abs.toNat : Int) = (a0.toNat : Int) * (b2.toNat : Int) + (a1.toNat : Int) * (b1.toNat : Int) + (a2.toNat : Int) * (b0.toNat : Int) := by
    rw [← AzInt.natAbs_toInt, h2, Int.natAbs_of_nonneg (by positivity)]
  have hE3 : (e3.abs.toNat : Int) = (a0.toNat : Int) * (b3.toNat : Int) + (a1.toNat : Int) * (b2.toNat : Int) + (a2.toNat : Int) * (b1.toNat : Int) + (a3.toNat : Int) * (b0.toNat : Int) := by
    rw [← AzInt.natAbs_toInt, h3, Int.natAbs_of_nonneg (by positivity)]
  have hE4 : (e4.abs.toNat : Int) = (a1.toNat : Int) * (b3.toNat : Int) + (a2.toNat : Int) * (b2.toNat : Int) + (a3.toNat : Int) * (b1.toNat : Int) := by
    rw [← AzInt.natAbs_toInt, h4, Int.natAbs_of_nonneg (by positivity)]
  have hE5 : (e5.abs.toNat : Int) = (a2.toNat : Int) * (b3.toNat : Int) + (a3.toNat : Int) * (b2.toNat : Int) := by
    rw [← AzInt.natAbs_toInt, h5, Int.natAbs_of_nonneg (by positivity)]
  have hE6 : (e6.abs.toNat : Int) = (a3.toNat : Int) * (b3.toNat : Int) := by
    rw [← AzInt.natAbs_toInt, h6, Int.natAbs_of_nonneg (by positivity)]
  -- assemble and compare over `ℤ`
  rw [toNat_assemble]
  apply Int.natCast_inj.mp
  rw [Nat.cast_mul, polyEvalInt_natCast, polyEvalInt_natCast, polyEvalInt_natCast]
  simp only [List.map_cons, List.map_nil, polyEvalInt_cons, polyEvalInt_nil]
  rw [hE0, hE1, hE2, hE3, hE4, hE5, hE6]
  push_cast
  ring

/-- Every Horner evaluation used by Toom-4 fits in `k + 1` limbs. -/
theorem toomCook4_eval_abs_lt (k : Nat) (x0 x1 x2 x3 : AzNat)
    (h0 : x0.toNat < 2 ^ (64 * k)) (h1 : x1.toNat < 2 ^ (64 * k))
    (h2 : x2.toNat < 2 ^ (64 * k)) (h3 : x3.toNat < 2 ^ (64 * k))
    (c : Int64) (hc : c.toInt.natAbs ≤ 2) :
    (hornerInt64 c [x0.toAzInt, x1.toAzInt, x2.toAzInt, x3.toAzInt]).abs.toNat
      < 2 ^ (64 * (k + 1)) :=
  hornerInt64_four_abs_lt k c hc _ _ _ _ h0 h1 h2 h3

lemma int64_natAbs_le_two_zero : (0 : Int64).toInt.natAbs ≤ 2 := by decide
lemma int64_natAbs_le_two_one : (1 : Int64).toInt.natAbs ≤ 2 := by decide
lemma int64_natAbs_le_two_neg_one : (-1 : Int64).toInt.natAbs ≤ 2 := by decide
lemma int64_natAbs_le_two_two : (2 : Int64).toInt.natAbs ≤ 2 := by decide
lemma int64_natAbs_le_two_neg_two : (-2 : Int64).toInt.natAbs ≤ 2 := by decide

/-- **The core of Toom-4 multiplication**: for block values below `β^k` and a multiplier
`mulK1` correct on `(k + 1)`-limb buffers, the seven signed products interpolate and assemble
to the product of the two block polynomials. -/
theorem toomCook4_core_toNat (k : Nat)
    (mulK1 : (x y : Array UInt64) → 0 + (k + 1) ≤ x.size → 0 + (k + 1) ≤ y.size → Array UInt64)
    (hmul : ∀ x y hx hy,
      toNatLimbsList (mulK1 x y hx hy).toList = sliceVal x 0 (k + 1) * sliceVal y 0 (k + 1))
    (a0 a1 a2 a3 b0 b1 b2 b3 : AzNat)
    (ha0 : a0.toNat < 2 ^ (64 * k)) (ha1 : a1.toNat < 2 ^ (64 * k))
    (ha2 : a2.toNat < 2 ^ (64 * k)) (ha3 : a3.toNat < 2 ^ (64 * k))
    (hb0 : b0.toNat < 2 ^ (64 * k)) (hb1 : b1.toNat < 2 ^ (64 * k))
    (hb2 : b2.toNat < 2 ^ (64 * k)) (hb3 : b3.toNat < 2 ^ (64 * k)) :
    let bsA := [a0.toAzInt, a1.toAzInt, a2.toAzInt, a3.toAzInt]
    let bsB := [b0.toAzInt, b1.toAzInt, b2.toAzInt, b3.toAzInt]
    let v0 := signedMulWith (k + 1) mulK1 (hornerInt64 0 bsA) (hornerInt64 0 bsB)
    let v1 := signedMulWith (k + 1) mulK1 (hornerInt64 1 bsA) (hornerInt64 1 bsB)
    let vm1 := signedMulWith (k + 1) mulK1 (hornerInt64 (-1) bsA) (hornerInt64 (-1) bsB)
    let v2 := signedMulWith (k + 1) mulK1 (hornerInt64 2 bsA) (hornerInt64 2 bsB)
    let vm2 := signedMulWith (k + 1) mulK1 (hornerInt64 (-2) bsA) (hornerInt64 (-2) bsB)
    let vh := signedMulWith (k + 1) mulK1 (hornerInt64 2 bsA.reverse) (hornerInt64 2 bsB.reverse)
    let vinf := signedMulWith (k + 1) mulK1 (hornerInt64 0 bsA.reverse) (hornerInt64 0 bsB.reverse)
    (assemble k ((toomCook4Interpolate v0 v1 vm1 v2 vm2 vh vinf).map AzInt.abs)).toNat
      = polyEvalNat (2 ^ (64 * k)) [a0.toNat, a1.toNat, a2.toNat, a3.toNat]
        * polyEvalNat (2 ^ (64 * k)) [b0.toNat, b1.toNat, b2.toNat, b3.toNat] := by
  intro bsA bsB v0 v1 vm1 v2 vm2 vh vinf
  have hA : ∀ (c : Int64), c.toInt.natAbs ≤ 2 →
      (hornerInt64 c [a0.toAzInt, a1.toAzInt, a2.toAzInt, a3.toAzInt]).abs.toNat
        < 2 ^ (64 * (k + 1)) :=
    fun c hc => toomCook4_eval_abs_lt k _ _ _ _ ha0 ha1 ha2 ha3 c hc
  have hB : ∀ (c : Int64), c.toInt.natAbs ≤ 2 →
      (hornerInt64 c [b0.toAzInt, b1.toAzInt, b2.toAzInt, b3.toAzInt]).abs.toNat
        < 2 ^ (64 * (k + 1)) :=
    fun c hc => toomCook4_eval_abs_lt k _ _ _ _ hb0 hb1 hb2 hb3 c hc
  have hA' : ∀ (c : Int64), c.toInt.natAbs ≤ 2 →
      (hornerInt64 c [a3.toAzInt, a2.toAzInt, a1.toAzInt, a0.toAzInt]).abs.toNat
        < 2 ^ (64 * (k + 1)) :=
    fun c hc => toomCook4_eval_abs_lt k _ _ _ _ ha3 ha2 ha1 ha0 c hc
  have hB' : ∀ (c : Int64), c.toInt.natAbs ≤ 2 →
      (hornerInt64 c [b3.toAzInt, b2.toAzInt, b1.toAzInt, b0.toAzInt]).abs.toNat
        < 2 ^ (64 * (k + 1)) :=
    fun c hc => toomCook4_eval_abs_lt k _ _ _ _ hb3 hb2 hb1 hb0 c hc
  have hrevA : bsA.reverse = [a3.toAzInt, a2.toAzInt, a1.toAzInt, a0.toAzInt] := rfl
  have hrevB : bsB.reverse = [b3.toAzInt, b2.toAzInt, b1.toAzInt, b0.toAzInt] := rfl
  have hv0 : v0.toInt = (hornerInt64 0 bsA).toInt * (hornerInt64 0 bsB).toInt :=
    toInt_signedMulWith _ _ hmul _ _ (hA 0 int64_natAbs_le_two_zero) (hB 0 int64_natAbs_le_two_zero)
  have hv1 : v1.toInt = (hornerInt64 1 bsA).toInt * (hornerInt64 1 bsB).toInt :=
    toInt_signedMulWith _ _ hmul _ _ (hA 1 int64_natAbs_le_two_one) (hB 1 int64_natAbs_le_two_one)
  have hvm1 : vm1.toInt = (hornerInt64 (-1) bsA).toInt * (hornerInt64 (-1) bsB).toInt :=
    toInt_signedMulWith _ _ hmul _ _ (hA (-1) int64_natAbs_le_two_neg_one)
      (hB (-1) int64_natAbs_le_two_neg_one)
  have hv2 : v2.toInt = (hornerInt64 2 bsA).toInt * (hornerInt64 2 bsB).toInt :=
    toInt_signedMulWith _ _ hmul _ _ (hA 2 int64_natAbs_le_two_two) (hB 2 int64_natAbs_le_two_two)
  have hvm2 : vm2.toInt = (hornerInt64 (-2) bsA).toInt * (hornerInt64 (-2) bsB).toInt :=
    toInt_signedMulWith _ _ hmul _ _ (hA (-2) int64_natAbs_le_two_neg_two)
      (hB (-2) int64_natAbs_le_two_neg_two)
  have hvh : vh.toInt = (hornerInt64 2 bsA.reverse).toInt * (hornerInt64 2 bsB.reverse).toInt := by
    rw [hrevA, hrevB] at *
    exact toInt_signedMulWith _ _ hmul _ _ (hA' 2 int64_natAbs_le_two_two)
      (hB' 2 int64_natAbs_le_two_two)
  have hvinf : vinf.toInt
      = (hornerInt64 0 bsA.reverse).toInt * (hornerInt64 0 bsB.reverse).toInt := by
    rw [hrevA, hrevB] at *
    exact toInt_signedMulWith _ _ hmul _ _ (hA' 0 int64_natAbs_le_two_zero)
      (hB' 0 int64_natAbs_le_two_zero)
  rw [hrevA, hrevB] at hvh hvinf
  exact toomCook4_assemble_toNat k a0 a1 a2 a3 b0 b1 b2 b3 v0 v1 vm1 v2 vm2 vh vinf
    hv0 hv1 hvm1 hv2 hvm2 hvh hvinf

/-! ### The recursion -/

/-- The block polynomial of a slice, in `ℕ`, is the slice. -/
theorem polyEvalNat_blocks_four (a : Array UInt64) (lo len k : Nat) (hr : len ≤ 4 * k)
    (hA : lo + len ≤ a.size) :
    polyEvalNat (2 ^ (64 * k)) [(block a lo len k 0).toNat, (block a lo len k 1).toNat,
      (block a lo len k 2).toNat, (block a lo len k 3).toNat] = sliceVal a lo len := by
  apply Int.natCast_inj.mp
  rw [polyEvalInt_natCast, sliceVal_eq_polyEval_blocks a lo len k 4 (by omega) hA, blocks_four]
  simp only [List.map_cons, List.map_nil, Azurite.AzNat.toInt_toAzInt]
  push_cast
  rfl

/-- **Correctness of the Toom-4 recursion.** -/
theorem toomCook4MulLimbsRec_toNat (toom4Threshold toom3Threshold karaThreshold : Nat) :
    ∀ (len : Nat) (a b : Array UInt64) (loA loB : Nat)
      (hA : loA + len ≤ a.size) (hB : loB + len ≤ b.size),
    toNatLimbsList (toomCook4MulLimbsRec toom4Threshold toom3Threshold karaThreshold
        a b loA loB len hA hB).val.toList
      = sliceVal a loA len * sliceVal b loB len := by
  intro len
  induction len using Nat.strong_induction_on with
  | _ len ih =>
    intro a b loA loB hA hB
    unfold toomCook4MulLimbsRec
    by_cases h_base : len < toom4Threshold ∨ len < 4
    · simp only [h_base, ↓reduceDIte]
      exact toomCook3MulLimbs_toNat toom3Threshold karaThreshold a b loA loB len hA hB
    · simp only [h_base, ↓reduceDIte]
      have hk1_lt : (len + 3) / 4 + 1 < len := by omega
      have hlen_le : len ≤ 4 * ((len + 3) / 4) := by omega
      -- the induction hypothesis is the multiplier specification at `k + 1` limbs
      have hmul : ∀ (x y : Array UInt64) (hx : 0 + ((len + 3) / 4 + 1) ≤ x.size)
          (hy : 0 + ((len + 3) / 4 + 1) ≤ y.size),
          toNatLimbsList (toomCook4MulLimbsRec toom4Threshold toom3Threshold karaThreshold
              x y 0 0 ((len + 3) / 4 + 1) hx hy).1.toList
            = sliceVal x 0 ((len + 3) / 4 + 1) * sliceVal y 0 ((len + 3) / 4 + 1) :=
        fun x y hx hy => ih _ hk1_lt x y 0 0 hx hy
      have hcore := toomCook4_core_toNat ((len + 3) / 4)
        (fun x y hx hy => (toomCook4MulLimbsRec toom4Threshold toom3Threshold karaThreshold
          x y 0 0 ((len + 3) / 4 + 1) hx hy).1) hmul
        (block a loA len _ 0) (block a loA len _ 1) (block a loA len _ 2) (block a loA len _ 3)
        (block b loB len _ 0) (block b loB len _ 1) (block b loB len _ 2) (block b loB len _ 3)
        (toNat_block_lt _ _ _ _ _) (toNat_block_lt _ _ _ _ _) (toNat_block_lt _ _ _ _ _)
        (toNat_block_lt _ _ _ _ _) (toNat_block_lt _ _ _ _ _) (toNat_block_lt _ _ _ _ _)
        (toNat_block_lt _ _ _ _ _) (toNat_block_lt _ _ _ _ _)
      rw [polyEvalNat_blocks_four a loA len _ hlen_le hA,
        polyEvalNat_blocks_four b loB len _ hlen_le hB] at hcore
      rw [blocks_four, blocks_four, truncatePad_toNat]
      · exact hcore
      · change AzNat.toNat _ < _
        rw [hcore, show 64 * (2 * len) = 64 * len + 64 * len by ring, pow_add]
        exact Nat.mul_lt_mul'' (sliceVal_lt_pow _ _ _) (sliceVal_lt_pow _ _ _)

/-- Correctness of `toomCook4MulLimbs`. -/
theorem toomCook4MulLimbs_toNat (toom4Threshold toom3Threshold karaThreshold : Nat)
    (a b : Array UInt64) (loA loB len : Nat)
    (hA : loA + len ≤ a.size) (hB : loB + len ≤ b.size) :
    toNatLimbsList (toomCook4MulLimbs toom4Threshold toom3Threshold karaThreshold
        a b loA loB len hA hB).toList
      = sliceVal a loA len * sliceVal b loB len :=
  toomCook4MulLimbsRec_toNat toom4Threshold toom3Threshold karaThreshold len a b loA loB hA hB

/-- `AzNat`-level correctness of `mulToomCook4`. -/
theorem toNat_mulToomCook4 (toom4Threshold toom3Threshold karaThreshold : Nat) (a b : AzNat) :
    (mulToomCook4 toom4Threshold toom3Threshold karaThreshold a b).toNat = a.toNat * b.toNat := by
  unfold mulToomCook4
  rw [toNat_ofLimbs, toomCook4MulLimbs_toNat, sliceVal_self _ _ (truncatePad_size _ _),
    sliceVal_self _ _ (truncatePad_size _ _), truncatePad_toNat, truncatePad_toNat]
  · rfl
  · exact lt_of_lt_of_le (toNat_lt_pow b) (Nat.pow_le_pow_right (by norm_num)
      (Nat.mul_le_mul_left _ (Nat.le_max_right _ _)))
  · exact lt_of_lt_of_le (toNat_lt_pow a) (Nat.pow_le_pow_right (by norm_num)
      (Nat.mul_le_mul_left _ (Nat.le_max_left _ _)))

end Azurite.AzNat
