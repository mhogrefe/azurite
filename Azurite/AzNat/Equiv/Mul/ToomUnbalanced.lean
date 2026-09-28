/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzNat.Mul.ToomUnbalanced
import Azurite.AzNat.Equiv.Mul.ToomCook4

/-!
# Correctness of the unbalanced multiplications

`toom32MulLimbs_toNat`, `toom42MulLimbs_toNat` and `mulChunksLimbs_toNat`, each assuming the
balanced multiplier is correct on every size (`hbal`).  The structure is that of Toom-4: an
interpolation lemma, an array-free algebra lemma, bounds, and the block decomposition.
-/

namespace Azurite.AzNat

lemma uint64_toNat_2 : ((2 : UInt64).toNat : Int) = 2 := by decide

/-! ### Bounds for Horner evaluations of any length -/

theorem polyEvalNat_le_of_lt (c : Nat) (hc : c ≤ 2) (B : Nat) (l : List Nat)
    (hl : ∀ x ∈ l, x < B) : polyEvalNat c l ≤ (2 ^ l.length - 1) * (B - 1) := by
  induction l with
  | nil => simp
  | cons b l ih =>
    have hb : b < B := hl b (List.mem_cons_self ..)
    have ih' := ih (fun x hx => hl x (List.mem_cons_of_mem _ hx))
    have h1 : 1 ≤ 2 ^ l.length := Nat.one_le_two_pow
    have h2 : 2 ^ (b :: l).length - 1 = 2 * (2 ^ l.length - 1) + 1 := by
      rw [List.length_cons, pow_succ]; omega
    rw [polyEvalNat_cons, h2]
    calc polyEvalNat c l * c + b ≤ (2 ^ l.length - 1) * (B - 1) * 2 + (B - 1) :=
          Nat.add_le_add (Nat.mul_le_mul ih' hc) (by omega)
      _ = (2 * (2 ^ l.length - 1) + 1) * (B - 1) := by ring

/-- A Horner value at `|c| ≤ 2` of at most `64` blocks below `β^k` fits in `k + 1` limbs. -/
theorem hornerInt64_abs_lt (k : Nat) (c : Int64) (hc : c.toInt.natAbs ≤ 2) (bs : List AzInt)
    (hlen : bs.length ≤ 64) (hb : ∀ b ∈ bs, b.abs.toNat < 2 ^ (64 * k)) :
    (hornerInt64 c bs).abs.toNat < 2 ^ (64 * (k + 1)) := by
  rw [← AzInt.natAbs_toInt, toInt_hornerInt64]
  refine lt_of_le_of_lt (natAbs_polyEvalInt_le _ _) ?_
  have hmap : (bs.map AzInt.toInt).map Int.natAbs = bs.map fun b => b.abs.toNat := by
    rw [List.map_map]; exact List.map_congr_left fun b _ => AzInt.natAbs_toInt b
  rw [hmap]
  have hB : 0 < 2 ^ (64 * k) := pow_pos (by norm_num) _
  have hpow : 2 ^ (64 * (k + 1)) = 2 ^ (64 * k) * 2 ^ 64 := by
    rw [show 64 * (k + 1) = 64 * k + 64 by ring, pow_add]
  have hle := polyEvalNat_le_of_lt c.toInt.natAbs hc (2 ^ (64 * k)) (bs.map fun b => b.abs.toNat)
    (by intro x hx; obtain ⟨b, hb', rfl⟩ := List.mem_map.mp hx; exact hb b hb')
  rw [List.length_map] at hle
  have hlen2 : 2 ^ bs.length ≤ 2 ^ 64 := Nat.pow_le_pow_right (by norm_num) hlen
  have h1 : 1 ≤ 2 ^ bs.length := Nat.one_le_two_pow
  rw [hpow]
  calc polyEvalNat c.toInt.natAbs (bs.map fun b => b.abs.toNat)
      ≤ (2 ^ bs.length - 1) * (2 ^ (64 * k) - 1) := hle
    _ ≤ (2 ^ bs.length - 1) * 2 ^ (64 * k) := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
    _ < 2 ^ bs.length * 2 ^ (64 * k) := Nat.mul_lt_mul_of_pos_right (by omega) hB
    _ ≤ 2 ^ (64 * k) * 2 ^ 64 := by rw [Nat.mul_comm]; exact Nat.mul_le_mul_left _ hlen2

/-! ### Interpolations -/

/-- **Four-point interpolation is exact.** -/
theorem toomInterp4_toInt (v0 v1 vm1 vinf : AzInt) (c0 c1 c2 c3 : Int)
    (hv0 : v0.toInt = c0) (hv1 : v1.toInt = c0 + c1 + c2 + c3)
    (hvm1 : vm1.toInt = c0 - c1 + c2 - c3) (hvinf : vinf.toInt = c3) :
    (toomInterp4 v0 v1 vm1 vinf).map AzInt.toInt = [c0, c1, c2, c3] := by
  unfold toomInterp4
  simp only [List.map_cons, List.map_nil]
  set e := (v1 + vm1) >>> 1 with he_def
  set o := (v1 - vm1) >>> 1 with ho_def
  have he : e.toInt = c0 + c2 := by
    rw [he_def, toInt_hShiftRight_pow, AzInt.toInt_add, hv1, hvm1,
      show c0 + c1 + c2 + c3 + (c0 - c1 + c2 - c3) = 2 ^ 1 * (c0 + c2) by ring,
      Int.mul_ediv_cancel_left _ (by norm_num)]
  have ho : o.toInt = c1 + c3 := by
    rw [ho_def, toInt_hShiftRight_pow, AzInt.toInt_sub, hv1, hvm1,
      show c0 + c1 + c2 + c3 - (c0 - c1 + c2 - c3) = 2 ^ 1 * (c1 + c3) by ring,
      Int.mul_ediv_cancel_left _ (by norm_num)]
  have h1 : (o - vinf).toInt = c1 := by rw [AzInt.toInt_sub, ho, hvinf]; ring
  have h2 : (e - v0).toInt = c2 := by rw [AzInt.toInt_sub, he, hv0]; ring
  rw [hv0, h1, h2, hvinf]

/-- **Five-point interpolation is exact** (the Toom-3 formulas). -/
theorem toomInterp5_toInt (v0 v1 vm1 v2 vinf : AzInt) (c0 c1 c2 c3 c4 : Int)
    (hv0 : v0.toInt = c0) (hv1 : v1.toInt = c0 + c1 + c2 + c3 + c4)
    (hvm1 : vm1.toInt = c0 - c1 + c2 - c3 + c4)
    (hv2 : v2.toInt = c0 + 2 * c1 + 4 * c2 + 8 * c3 + 16 * c4) (hvinf : vinf.toInt = c4) :
    (toomInterp5 v0 v1 vm1 v2 vinf).map AzInt.toInt = [c0, c1, c2, c3, c4] := by
  unfold toomInterp5
  simp only [List.map_cons, List.map_nil]
  set t2 := (v1 + vm1) >>> 1 with ht2_def
  have ht2 : t2.toInt = c0 + c2 + c4 := by
    rw [ht2_def, toInt_hShiftRight_pow, AzInt.toInt_add, hv1, hvm1,
      show c0 + c1 + c2 + c3 + c4 + (c0 - c1 + c2 - c3 + c4) = 2 ^ 1 * (c0 + c2 + c4) by ring,
      Int.mul_ediv_cancel_left _ (by norm_num)]
  have hnum : ((v0.mulUInt64 3 + v2 + vm1.mulUInt64 2) >>> 1).toInt = 3 * (c0 + c2 + c3 + 3 * c4) := by
    rw [toInt_hShiftRight_pow, AzInt.toInt_add, AzInt.toInt_add, AzInt.toInt_mulUInt64,
      AzInt.toInt_mulUInt64, hv0, hv2, hvm1, uint64_toNat_3, uint64_toNat_2,
      show c0 * 3 + (c0 + 2 * c1 + 4 * c2 + 8 * c3 + 16 * c4) + (c0 - c1 + c2 - c3 + c4) * 2
        = 2 ^ 1 * (3 * (c0 + c2 + c3 + 3 * c4)) by ring, Int.mul_ediv_cancel_left _ (by norm_num)]
  set t1 := AzInt.exactDivOdd 3 inv3 ((v0.mulUInt64 3 + v2 + vm1.mulUInt64 2) >>> 1) - (vinf <<< 1)
    with ht1_def
  have ht1 : t1.toInt = c0 + c2 + c3 + c4 := by
    rw [ht1_def, AzInt.toInt_sub, AzInt.toInt_hShiftLeft, hvinf,
      AzInt.toInt_exactDivOdd 3 inv3 mul_inv3 _ (by rw [hnum, uint64_toNat_3]; exact Dvd.intro _ rfl),
      hnum, uint64_toNat_3, Int.mul_ediv_cancel_left _ (by norm_num)]
    ring
  have h1 : (v1 - t1).toInt = c1 := by rw [AzInt.toInt_sub, hv1, ht1]; ring
  have h2 : (t2 - v0 - vinf).toInt = c2 := by
    rw [AzInt.toInt_sub, AzInt.toInt_sub, ht2, hv0, hvinf]; ring
  have h3 : (t1 - t2).toInt = c3 := by rw [AzInt.toInt_sub, ht1, ht2]; ring
  rw [hv0, h1, h2, h3, hvinf]

/-! ### The algebra -/

theorem hornerInt64_three_toInt (c : Int64) (x0 x1 x2 : AzNat) :
    (hornerInt64 c [x0.toAzInt, x1.toAzInt, x2.toAzInt]).toInt
      = ((x2.toNat : Int) * c.toInt + (x1.toNat : Int)) * c.toInt + (x0.toNat : Int) := by
  simp only [toInt_hornerInt64, List.map_cons, List.map_nil, polyEvalInt_cons, polyEvalInt_nil,
    Azurite.AzNat.toInt_toAzInt, zero_mul, zero_add]

theorem hornerInt64_two_toInt (c : Int64) (x0 x1 : AzNat) :
    (hornerInt64 c [x0.toAzInt, x1.toAzInt]).toInt
      = (x1.toNat : Int) * c.toInt + (x0.toNat : Int) := by
  simp only [toInt_hornerInt64, List.map_cons, List.map_nil, polyEvalInt_cons, polyEvalInt_nil,
    Azurite.AzNat.toInt_toAzInt, zero_mul, zero_add]

theorem hornerInt64_four_toInt (c : Int64) (x0 x1 x2 x3 : AzNat) :
    (hornerInt64 c [x0.toAzInt, x1.toAzInt, x2.toAzInt, x3.toAzInt]).toInt
      = (((x3.toNat : Int) * c.toInt + (x2.toNat : Int)) * c.toInt + (x1.toNat : Int)) * c.toInt
        + (x0.toNat : Int) := by
  simp only [toInt_hornerInt64, List.map_cons, List.map_nil, polyEvalInt_cons, polyEvalInt_nil,
    Azurite.AzNat.toInt_toAzInt, zero_mul, zero_add]

/-- **The algebra of Toom-(3,2)**. -/
theorem toom32_assemble_toNat (k : Nat) (a0 a1 a2 b0 b1 : AzNat) (v0 v1 vm1 vinf : AzInt)
    (hv0 : v0.toInt = (hornerInt64 0 [a0.toAzInt, a1.toAzInt, a2.toAzInt]).toInt
      * (hornerInt64 0 [b0.toAzInt, b1.toAzInt]).toInt)
    (hv1 : v1.toInt = (hornerInt64 1 [a0.toAzInt, a1.toAzInt, a2.toAzInt]).toInt
      * (hornerInt64 1 [b0.toAzInt, b1.toAzInt]).toInt)
    (hvm1 : vm1.toInt = (hornerInt64 (-1) [a0.toAzInt, a1.toAzInt, a2.toAzInt]).toInt
      * (hornerInt64 (-1) [b0.toAzInt, b1.toAzInt]).toInt)
    (hvinf : vinf.toInt = (hornerInt64 0 [a2.toAzInt, a1.toAzInt, a0.toAzInt]).toInt
      * (hornerInt64 0 [b1.toAzInt, b0.toAzInt]).toInt) :
    (assemble k ((toomInterp4 v0 v1 vm1 vinf).map AzInt.abs)).toNat
      = polyEvalNat (2 ^ (64 * k)) [a0.toNat, a1.toNat, a2.toNat]
        * polyEvalNat (2 ^ (64 * k)) [b0.toNat, b1.toNat] := by
  rw [hornerInt64_three_toInt, hornerInt64_two_toInt] at hv0 hv1 hvm1 hvinf
  have hinterp := toomInterp4_toInt v0 v1 vm1 vinf ((a0.toNat : Int) * (b0.toNat : Int)) ((a0.toNat : Int) * (b1.toNat : Int) + (a1.toNat : Int) * (b0.toNat : Int)) ((a1.toNat : Int) * (b1.toNat : Int) + (a2.toNat : Int) * (b0.toNat : Int)) ((a2.toNat : Int) * (b1.toNat : Int))
    (by rw [hv0, int64_toInt_zero]; ring) (by rw [hv1, int64_toInt_one]; ring)
    (by rw [hvm1, int64_toInt_neg_one]; ring) (by rw [hvinf, int64_toInt_zero]; ring)
  obtain ⟨e0, e1, e2, e3, hcs⟩ : ∃ e0 e1 e2 e3 : AzInt,
      toomInterp4 v0 v1 vm1 vinf = [e0, e1, e2, e3] := ⟨_, _, _, _, rfl⟩
  rw [hcs] at hinterp ⊢
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hinterp
  obtain ⟨h0, h1, h2, h3⟩ := hinterp
  have hE0 : (e0.abs.toNat : Int) = (a0.toNat : Int) * (b0.toNat : Int) := by
    rw [← AzInt.natAbs_toInt, h0, Int.natAbs_of_nonneg (by positivity)]
  have hE1 : (e1.abs.toNat : Int) = (a0.toNat : Int) * (b1.toNat : Int) + (a1.toNat : Int) * (b0.toNat : Int) := by
    rw [← AzInt.natAbs_toInt, h1, Int.natAbs_of_nonneg (by positivity)]
  have hE2 : (e2.abs.toNat : Int) = (a1.toNat : Int) * (b1.toNat : Int) + (a2.toNat : Int) * (b0.toNat : Int) := by
    rw [← AzInt.natAbs_toInt, h2, Int.natAbs_of_nonneg (by positivity)]
  have hE3 : (e3.abs.toNat : Int) = (a2.toNat : Int) * (b1.toNat : Int) := by
    rw [← AzInt.natAbs_toInt, h3, Int.natAbs_of_nonneg (by positivity)]
  rw [toNat_assemble]
  apply Int.natCast_inj.mp
  rw [Nat.cast_mul, polyEvalInt_natCast, polyEvalInt_natCast, polyEvalInt_natCast]
  simp only [List.map_cons, List.map_nil, polyEvalInt_cons, polyEvalInt_nil]
  rw [hE0, hE1, hE2, hE3]
  push_cast
  ring

/-- **The algebra of Toom-(4,2)**. -/
theorem toom42_assemble_toNat (k : Nat) (a0 a1 a2 a3 b0 b1 : AzNat) (v0 v1 vm1 v2 vinf : AzInt)
    (hv0 : v0.toInt = (hornerInt64 0 [a0.toAzInt, a1.toAzInt, a2.toAzInt, a3.toAzInt]).toInt
      * (hornerInt64 0 [b0.toAzInt, b1.toAzInt]).toInt)
    (hv1 : v1.toInt = (hornerInt64 1 [a0.toAzInt, a1.toAzInt, a2.toAzInt, a3.toAzInt]).toInt
      * (hornerInt64 1 [b0.toAzInt, b1.toAzInt]).toInt)
    (hvm1 : vm1.toInt = (hornerInt64 (-1) [a0.toAzInt, a1.toAzInt, a2.toAzInt, a3.toAzInt]).toInt
      * (hornerInt64 (-1) [b0.toAzInt, b1.toAzInt]).toInt)
    (hv2 : v2.toInt = (hornerInt64 2 [a0.toAzInt, a1.toAzInt, a2.toAzInt, a3.toAzInt]).toInt
      * (hornerInt64 2 [b0.toAzInt, b1.toAzInt]).toInt)
    (hvinf : vinf.toInt = (hornerInt64 0 [a3.toAzInt, a2.toAzInt, a1.toAzInt, a0.toAzInt]).toInt
      * (hornerInt64 0 [b1.toAzInt, b0.toAzInt]).toInt) :
    (assemble k ((toomInterp5 v0 v1 vm1 v2 vinf).map AzInt.abs)).toNat
      = polyEvalNat (2 ^ (64 * k)) [a0.toNat, a1.toNat, a2.toNat, a3.toNat]
        * polyEvalNat (2 ^ (64 * k)) [b0.toNat, b1.toNat] := by
  rw [hornerInt64_four_toInt, hornerInt64_two_toInt] at hv0 hv1 hvm1 hv2 hvinf
  have hinterp := toomInterp5_toInt v0 v1 vm1 v2 vinf ((a0.toNat : Int) * (b0.toNat : Int)) ((a0.toNat : Int) * (b1.toNat : Int) + (a1.toNat : Int) * (b0.toNat : Int)) ((a1.toNat : Int) * (b1.toNat : Int) + (a2.toNat : Int) * (b0.toNat : Int)) ((a2.toNat : Int) * (b1.toNat : Int) + (a3.toNat : Int) * (b0.toNat : Int)) ((a3.toNat : Int) * (b1.toNat : Int))
    (by rw [hv0, int64_toInt_zero]; ring) (by rw [hv1, int64_toInt_one]; ring)
    (by rw [hvm1, int64_toInt_neg_one]; ring) (by rw [hv2, int64_toInt_two]; ring)
    (by rw [hvinf, int64_toInt_zero]; ring)
  obtain ⟨e0, e1, e2, e3, e4, hcs⟩ : ∃ e0 e1 e2 e3 e4 : AzInt,
      toomInterp5 v0 v1 vm1 v2 vinf = [e0, e1, e2, e3, e4] := ⟨_, _, _, _, _, rfl⟩
  rw [hcs] at hinterp ⊢
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hinterp
  obtain ⟨h0, h1, h2, h3, h4⟩ := hinterp
  have hE0 : (e0.abs.toNat : Int) = (a0.toNat : Int) * (b0.toNat : Int) := by
    rw [← AzInt.natAbs_toInt, h0, Int.natAbs_of_nonneg (by positivity)]
  have hE1 : (e1.abs.toNat : Int) = (a0.toNat : Int) * (b1.toNat : Int) + (a1.toNat : Int) * (b0.toNat : Int) := by
    rw [← AzInt.natAbs_toInt, h1, Int.natAbs_of_nonneg (by positivity)]
  have hE2 : (e2.abs.toNat : Int) = (a1.toNat : Int) * (b1.toNat : Int) + (a2.toNat : Int) * (b0.toNat : Int) := by
    rw [← AzInt.natAbs_toInt, h2, Int.natAbs_of_nonneg (by positivity)]
  have hE3 : (e3.abs.toNat : Int) = (a2.toNat : Int) * (b1.toNat : Int) + (a3.toNat : Int) * (b0.toNat : Int) := by
    rw [← AzInt.natAbs_toInt, h3, Int.natAbs_of_nonneg (by positivity)]
  have hE4 : (e4.abs.toNat : Int) = (a3.toNat : Int) * (b1.toNat : Int) := by
    rw [← AzInt.natAbs_toInt, h4, Int.natAbs_of_nonneg (by positivity)]
  rw [toNat_assemble]
  apply Int.natCast_inj.mp
  rw [Nat.cast_mul, polyEvalInt_natCast, polyEvalInt_natCast, polyEvalInt_natCast]
  simp only [List.map_cons, List.map_nil, polyEvalInt_cons, polyEvalInt_nil]
  rw [hE0, hE1, hE2, hE3, hE4]
  push_cast
  ring

/-! ### Blocks -/

theorem blocks_two (a : Array UInt64) (lo len k : Nat) :
    blocks a lo len k 2 = [(block a lo len k 0).toAzInt, (block a lo len k 1).toAzInt] := rfl

theorem blocks_three (a : Array UInt64) (lo len k : Nat) :
    blocks a lo len k 3 = [(block a lo len k 0).toAzInt, (block a lo len k 1).toAzInt,
      (block a lo len k 2).toAzInt] := rfl

theorem polyEvalNat_blocks_two (a : Array UInt64) (lo len k : Nat) (hr : len ≤ 2 * k)
    (hA : lo + len ≤ a.size) :
    polyEvalNat (2 ^ (64 * k)) [(block a lo len k 0).toNat, (block a lo len k 1).toNat]
      = sliceVal a lo len := by
  apply Int.natCast_inj.mp
  rw [polyEvalInt_natCast, sliceVal_eq_polyEval_blocks a lo len k 2 (by omega) hA, blocks_two]
  simp only [List.map_cons, List.map_nil, Azurite.AzNat.toInt_toAzInt]
  push_cast
  rfl

theorem polyEvalNat_blocks_three (a : Array UInt64) (lo len k : Nat) (hr : len ≤ 3 * k)
    (hA : lo + len ≤ a.size) :
    polyEvalNat (2 ^ (64 * k)) [(block a lo len k 0).toNat, (block a lo len k 1).toNat,
      (block a lo len k 2).toNat] = sliceVal a lo len := by
  apply Int.natCast_inj.mp
  rw [polyEvalInt_natCast, sliceVal_eq_polyEval_blocks a lo len k 3 (by omega) hA, blocks_three]
  simp only [List.map_cons, List.map_nil, Azurite.AzNat.toInt_toAzInt]
  push_cast
  rfl

/-- The value of an extracted slice. -/
theorem toNatLimbsList_extract (a : Array UInt64) (lo n : Nat) :
    toNatLimbsList (a.extract lo (lo + n)).toList = sliceVal a lo n := by
  unfold sliceVal
  rw [Array.toList_extract, List.extract_eq_take_drop, Nat.add_sub_cancel_left]

/-! ### The variants -/

/-- Bounds for the evaluations of an explicit block list. -/
theorem eval_abs_lt_of_blocks (k : Nat) (c : Int64) (hc : c.toInt.natAbs ≤ 2) (l : List AzNat)
    (hlen : l.length ≤ 64) (hl : ∀ x ∈ l, x.toNat < 2 ^ (64 * k)) :
    (hornerInt64 c (l.map AzNat.toAzInt)).abs.toNat < 2 ^ (64 * (k + 1)) := by
  refine hornerInt64_abs_lt k c hc _ (by rw [List.length_map]; exact hlen) ?_
  intro b hb
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hb
  exact hl x hx

/-- **Correctness of Toom-(3,2).** -/
theorem toom32MulLimbs_toNat (mulBal : BalancedMul)
    (hbal : ∀ n x y hx hy, toNatLimbsList (mulBal n x y hx hy).toList = sliceVal x 0 n * sliceVal y 0 n)
    (a b : Array UInt64) (loA lenA loB lenB : Nat) (hA : loA + lenA ≤ a.size)
    (hB : loB + lenB ≤ b.size) :
    toNatLimbsList (toom32MulLimbs mulBal a b loA lenA loB lenB hA hB).toList
      = sliceVal a loA lenA * sliceVal b loB lenB := by
  unfold toom32MulLimbs
  simp only []
  set k := max ((lenA + 2) / 3) ((lenB + 1) / 2) with hk
  have hkA : lenA ≤ 3 * k := by omega
  have hkB : lenB ≤ 2 * k := by omega
  rw [blocks_three, blocks_two]
  simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
  have hbnd : ∀ (l : List AzNat), l.length ≤ 64 → (∀ x ∈ l, x.toNat < 2 ^ (64 * k)) →
      ∀ (c : Int64), c.toInt.natAbs ≤ 2 →
      (hornerInt64 c (l.map AzNat.toAzInt)).abs.toNat < 2 ^ (64 * (k + 1)) :=
    fun l hlen hl c hc => eval_abs_lt_of_blocks k c hc l hlen hl
  have hA3 : ∀ x ∈ [block a loA lenA k 0, block a loA lenA k 1, block a loA lenA k 2],
      x.toNat < 2 ^ (64 * k) := by
    intro x hx; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl <;> exact toNat_block_lt _ _ _ _ _
  have hA3' : ∀ x ∈ [block a loA lenA k 2, block a loA lenA k 1, block a loA lenA k 0],
      x.toNat < 2 ^ (64 * k) := by
    intro x hx; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl <;> exact toNat_block_lt _ _ _ _ _
  have hB2 : ∀ x ∈ [block b loB lenB k 0, block b loB lenB k 1], x.toNat < 2 ^ (64 * k) := by
    intro x hx; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl <;> exact toNat_block_lt _ _ _ _ _
  have hB2' : ∀ x ∈ [block b loB lenB k 1, block b loB lenB k 0], x.toNat < 2 ^ (64 * k) := by
    intro x hx; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl <;> exact toNat_block_lt _ _ _ _ _
  have hcore := toom32_assemble_toNat k (block a loA lenA k 0) (block a loA lenA k 1)
    (block a loA lenA k 2) (block b loB lenB k 0) (block b loB lenB k 1) _ _ _ _
    (toInt_signedMulWith (k + 1) (mulBal (k + 1)) (hbal (k + 1)) _ _
      (hbnd [_, _, _] (by simp) hA3 0 int64_natAbs_le_two_zero)
      (hbnd [_, _] (by simp) hB2 0 int64_natAbs_le_two_zero))
    (toInt_signedMulWith (k + 1) (mulBal (k + 1)) (hbal (k + 1)) _ _
      (hbnd [_, _, _] (by simp) hA3 1 int64_natAbs_le_two_one)
      (hbnd [_, _] (by simp) hB2 1 int64_natAbs_le_two_one))
    (toInt_signedMulWith (k + 1) (mulBal (k + 1)) (hbal (k + 1)) _ _
      (hbnd [_, _, _] (by simp) hA3 (-1) int64_natAbs_le_two_neg_one)
      (hbnd [_, _] (by simp) hB2 (-1) int64_natAbs_le_two_neg_one))
    (toInt_signedMulWith (k + 1) (mulBal (k + 1)) (hbal (k + 1)) _ _
      (hbnd [_, _, _] (by simp) hA3' 0 int64_natAbs_le_two_zero)
      (hbnd [_, _] (by simp) hB2' 0 int64_natAbs_le_two_zero))
  rw [polyEvalNat_blocks_three a loA lenA k hkA hA, polyEvalNat_blocks_two b loB lenB k hkB hB]
    at hcore
  rw [truncatePad_toNat]
  · exact hcore
  · change AzNat.toNat _ < _
    rw [hcore, show 64 * (lenA + lenB) = 64 * lenA + 64 * lenB by ring, pow_add]
    exact Nat.mul_lt_mul'' (sliceVal_lt_pow _ _ _) (sliceVal_lt_pow _ _ _)

/-- **Correctness of Toom-(4,2).** -/
theorem toom42MulLimbs_toNat (mulBal : BalancedMul)
    (hbal : ∀ n x y hx hy, toNatLimbsList (mulBal n x y hx hy).toList = sliceVal x 0 n * sliceVal y 0 n)
    (a b : Array UInt64) (loA lenA loB lenB : Nat) (hA : loA + lenA ≤ a.size)
    (hB : loB + lenB ≤ b.size) :
    toNatLimbsList (toom42MulLimbs mulBal a b loA lenA loB lenB hA hB).toList
      = sliceVal a loA lenA * sliceVal b loB lenB := by
  unfold toom42MulLimbs
  simp only []
  set k := max ((lenA + 3) / 4) ((lenB + 1) / 2) with hk
  have hkA : lenA ≤ 4 * k := by omega
  have hkB : lenB ≤ 2 * k := by omega
  rw [blocks_four, blocks_two]
  simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
  have hbnd : ∀ (l : List AzNat), l.length ≤ 64 → (∀ x ∈ l, x.toNat < 2 ^ (64 * k)) →
      ∀ (c : Int64), c.toInt.natAbs ≤ 2 →
      (hornerInt64 c (l.map AzNat.toAzInt)).abs.toNat < 2 ^ (64 * (k + 1)) :=
    fun l hlen hl c hc => eval_abs_lt_of_blocks k c hc l hlen hl
  have hA4 : ∀ x ∈ [block a loA lenA k 0, block a loA lenA k 1, block a loA lenA k 2,
      block a loA lenA k 3], x.toNat < 2 ^ (64 * k) := by
    intro x hx; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> exact toNat_block_lt _ _ _ _ _
  have hA4' : ∀ x ∈ [block a loA lenA k 3, block a loA lenA k 2, block a loA lenA k 1,
      block a loA lenA k 0], x.toNat < 2 ^ (64 * k) := by
    intro x hx; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> exact toNat_block_lt _ _ _ _ _
  have hB2 : ∀ x ∈ [block b loB lenB k 0, block b loB lenB k 1], x.toNat < 2 ^ (64 * k) := by
    intro x hx; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl <;> exact toNat_block_lt _ _ _ _ _
  have hB2' : ∀ x ∈ [block b loB lenB k 1, block b loB lenB k 0], x.toNat < 2 ^ (64 * k) := by
    intro x hx; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl <;> exact toNat_block_lt _ _ _ _ _
  have hcore := toom42_assemble_toNat k (block a loA lenA k 0) (block a loA lenA k 1)
    (block a loA lenA k 2) (block a loA lenA k 3) (block b loB lenB k 0) (block b loB lenB k 1)
    _ _ _ _ _
    (toInt_signedMulWith (k + 1) (mulBal (k + 1)) (hbal (k + 1)) _ _
      (hbnd [_, _, _, _] (by simp) hA4 0 int64_natAbs_le_two_zero)
      (hbnd [_, _] (by simp) hB2 0 int64_natAbs_le_two_zero))
    (toInt_signedMulWith (k + 1) (mulBal (k + 1)) (hbal (k + 1)) _ _
      (hbnd [_, _, _, _] (by simp) hA4 1 int64_natAbs_le_two_one)
      (hbnd [_, _] (by simp) hB2 1 int64_natAbs_le_two_one))
    (toInt_signedMulWith (k + 1) (mulBal (k + 1)) (hbal (k + 1)) _ _
      (hbnd [_, _, _, _] (by simp) hA4 (-1) int64_natAbs_le_two_neg_one)
      (hbnd [_, _] (by simp) hB2 (-1) int64_natAbs_le_two_neg_one))
    (toInt_signedMulWith (k + 1) (mulBal (k + 1)) (hbal (k + 1)) _ _
      (hbnd [_, _, _, _] (by simp) hA4 2 int64_natAbs_le_two_two)
      (hbnd [_, _] (by simp) hB2 2 int64_natAbs_le_two_two))
    (toInt_signedMulWith (k + 1) (mulBal (k + 1)) (hbal (k + 1)) _ _
      (hbnd [_, _, _, _] (by simp) hA4' 0 int64_natAbs_le_two_zero)
      (hbnd [_, _] (by simp) hB2' 0 int64_natAbs_le_two_zero))
  rw [polyEvalNat_blocks_four a loA lenA k hkA hA, polyEvalNat_blocks_two b loB lenB k hkB hB]
    at hcore
  rw [truncatePad_toNat]
  · exact hcore
  · change AzNat.toNat _ < _
    rw [hcore, show 64 * (lenA + lenB) = 64 * lenA + 64 * lenB by ring, pow_add]
    exact Nat.mul_lt_mul'' (sliceVal_lt_pow _ _ _) (sliceVal_lt_pow _ _ _)

/-! ### The chunk loop -/

theorem polyEvalInt_map_mul (c m : Int) (l : List Int) :
    polyEvalInt c (l.map (· * m)) = polyEvalInt c l * m := by
  induction l with
  | nil => simp
  | cons b l ih => simp only [List.map_cons, polyEvalInt_cons, ih]; ring

/-- **Correctness of the chunk loop.** -/
theorem mulChunksLimbs_toNat (mulBal : BalancedMul)
    (hbal : ∀ n x y hx hy, toNatLimbsList (mulBal n x y hx hy).toList = sliceVal x 0 n * sliceVal y 0 n)
    (a b : Array UInt64) (loA lenA loB lenB : Nat) (hA : loA + lenA ≤ a.size)
    (hB : loB + lenB ≤ b.size) :
    toNatLimbsList (mulChunksLimbs mulBal a b loA lenA loB lenB hA hB).toList
      = sliceVal a loA lenA * sliceVal b loB lenB := by
  unfold mulChunksLimbs
  split_ifs with h0
  · subst h0
    rw [Array.toList_replicate]
    have : toNatLimbsList (List.replicate (lenA + 0) (0 : UInt64)) = 0 := by
      have := toNatLimbsList_append_zeros [] (lenA + 0)
      rwa [List.nil_append] at this
    rw [this]
    show 0 = _ * toNatLimbsList (List.take 0 _)
    rw [List.take_zero]
    rfl
  · simp only []
    set r := (lenA + lenB - 1) / lenB with hr_def
    have hlenB : 0 < lenB := Nat.pos_of_ne_zero h0
    have hr : lenA ≤ r * lenB := by
      have h1 := Nat.div_add_mod (lenA + lenB - 1) lenB
      have h2 := Nat.mod_lt (lenA + lenB - 1) hlenB
      rw [← hr_def] at h1
      rw [Nat.mul_comm]
      omega
    set bz := (ofLimbs (b.extract loB (loB + lenB))).toAzInt with hbz_def
    have hbzI : bz.toInt = (sliceVal b loB lenB : Int) := by
      rw [hbz_def, Azurite.AzNat.toInt_toAzInt, toNat_ofLimbs, toNatLimbsList_extract]
    have hbz_abs : bz.abs.toNat < 2 ^ (64 * lenB) := by
      show (ofLimbs (b.extract loB (loB + lenB))).toNat < _
      rw [toNat_ofLimbs, toNatLimbsList_extract]; exact sliceVal_lt_pow _ _ _
    have hAdec := sliceVal_eq_polyEval_blocks a loA lenA lenB r hr hA
    -- each product
    have hprod : ∀ aj ∈ blocks a loA lenA lenB r,
        ((signedMulWith lenB (mulBal lenB) aj bz).abs.toNat : Int) = aj.toInt * bz.toInt := by
      intro aj haj
      obtain ⟨j, _, rfl⟩ := List.mem_map.mp haj
      rw [← AzInt.natAbs_toInt, toInt_signedMulWith lenB (mulBal lenB) (hbal lenB) _ _ (toNat_block_lt _ _ _ _ _) hbz_abs,
        Int.natAbs_of_nonneg (mul_nonneg (by rw [Azurite.AzNat.toInt_toAzInt]; exact Int.natCast_nonneg _)
          (by rw [hbzI]; exact Int.natCast_nonneg _))]
    have hval : (assemble lenB (List.map AzInt.abs (List.map
        (fun aj => signedMulWith lenB (mulBal lenB) aj bz) (blocks a loA lenA lenB r)))).toNat
          = sliceVal a loA lenA * sliceVal b loB lenB := by
      rw [toNat_assemble]
      apply Int.natCast_inj.mp
      rw [Nat.cast_mul, polyEvalInt_natCast, hAdec, ← hbzI, ← polyEvalInt_map_mul]
      congr 1
      simp only [List.map_map]
      refine List.map_congr_left fun aj haj => ?_
      exact hprod aj haj
    rw [truncatePad_toNat]
    · exact hval
    · change AzNat.toNat _ < _
      rw [hval, show 64 * (lenA + lenB) = 64 * lenA + 64 * lenB by ring, pow_add]
      exact Nat.mul_lt_mul'' (sliceVal_lt_pow _ _ _) (sliceVal_lt_pow _ _ _)

end Azurite.AzNat
