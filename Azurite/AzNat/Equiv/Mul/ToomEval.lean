/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzNat.Mul.ToomEval
import Azurite.AzNat.Equiv.ExactDivOdd
import Azurite.AzNat.Equiv.Mul.ToomCook3
import Azurite.AzInt.Equiv.MulSmall
import Azurite.AzInt.Equiv.Sub
import Azurite.AzInt.Equiv.Conversion

/-!
# Correctness of the Toom–Cook evaluation framework

Each piece of `AzNat/Mul/ToomEval.lean` is related to its integer specification:

* `polyEvalInt c l = Σ l[i] · c^i` and `toInt_hornerInt64`;
* `natAbs_polyEvalInt_le`, the bound used to show evaluations fit in `n` limbs;
* `toInt_signedMulWith`, given a specification of the magnitude multiplier;
* `AzInt.toInt_exactDivOdd`;
* `toNat_assemble` and `sliceVal_eq_polyEval_blocks`, relating the block decomposition of a
  slice to its value.

A Toom–Cook variant is then correct once its interpolation formula is a polynomial identity
between `polyEvalInt` values, which `ring` decides.
-/

namespace Azurite.AzNat

/-- `Σ l[i] · c^i` over `ℤ` (`l[0]` is the constant term). -/
def polyEvalInt (c : Int) (l : List Int) : Int :=
  l.foldr (fun b acc => acc * c + b) 0

/-- `Σ l[i] · c^i` over `ℕ`. -/
def polyEvalNat (c : Nat) (l : List Nat) : Nat :=
  l.foldr (fun b acc => acc * c + b) 0

@[simp] lemma polyEvalInt_nil (c : Int) : polyEvalInt c [] = 0 := rfl
@[simp] lemma polyEvalInt_cons (c b : Int) (l : List Int) :
    polyEvalInt c (b :: l) = polyEvalInt c l * c + b := rfl
@[simp] lemma polyEvalNat_nil (c : Nat) : polyEvalNat c [] = 0 := rfl
@[simp] lemma polyEvalNat_cons (c b : Nat) (l : List Nat) :
    polyEvalNat c (b :: l) = polyEvalNat c l * c + b := rfl

lemma polyEvalInt_natCast (c : Nat) (l : List Nat) :
    (polyEvalNat c l : Int) = polyEvalInt (c : Int) (l.map (fun n : Nat => (n : Int))) := by
  induction l with
  | nil => rfl
  | cons b l ih => simp [polyEvalNat_cons, polyEvalInt_cons, ih]

/-- **Horner evaluation is polynomial evaluation.** -/
theorem toInt_hornerInt64 (c : Int64) (bs : List AzInt) :
    (hornerInt64 c bs).toInt = polyEvalInt c.toInt (bs.map AzInt.toInt) := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    show (( hornerInt64 c bs).mulInt64 c + b).toInt = _
    rw [AzInt.toInt_add, AzInt.toInt_mulInt64, ih]
    rfl

/-- The triangle bound `|Σ l[i] c^i| ≤ Σ |l[i]| |c|^i`. -/
theorem natAbs_polyEvalInt_le (c : Int) (l : List Int) :
    (polyEvalInt c l).natAbs ≤ polyEvalNat c.natAbs (l.map Int.natAbs) := by
  induction l with
  | nil => simp
  | cons b l ih =>
    simp only [polyEvalInt_cons, List.map_cons, polyEvalNat_cons]
    calc (polyEvalInt c l * c + b).natAbs
        ≤ (polyEvalInt c l * c).natAbs + b.natAbs := Int.natAbs_add_le _ _
      _ = (polyEvalInt c l).natAbs * c.natAbs + b.natAbs := by rw [Int.natAbs_mul]
      _ ≤ polyEvalNat c.natAbs (l.map Int.natAbs) * c.natAbs + b.natAbs :=
          Nat.add_le_add_right (Nat.mul_le_mul_right _ ih) _

/-- `toInt` of `mkNorm` for any sign (the zero case is normalized). -/
theorem _root_.Azurite.AzInt.toInt_mkNorm (s : Bool) (a : AzNat) :
    (AzInt.mkNorm s a).toInt = if s then (a.toNat : Int) else -(a.toNat : Int) := by
  cases s
  · by_cases h : a = 0
    · subst h
      simp [AzInt.mkNorm, AzInt.toInt]
    · simp only [Bool.false_eq_true, ↓reduceIte]
      exact AzInt.toInt_mkNorm_false a h
  · simp only [↓reduceIte]
    exact AzInt.toInt_mkNorm_true a

/-- `z.toInt` in terms of the sign and magnitude. -/
theorem _root_.Azurite.AzInt.toInt_eq (z : AzInt) :
    z.toInt = if z.sign then (z.abs.toNat : Int) else -(z.abs.toNat : Int) := rfl

theorem _root_.Azurite.AzInt.natAbs_toInt (z : AzInt) : z.toInt.natAbs = z.abs.toNat := by
  rw [AzInt.toInt_eq]
  split_ifs <;> simp

/-- The value of an `n`-limb buffer as a slice of itself. -/
lemma sliceVal_self (x : Array UInt64) (n : Nat) (h : x.size = n) :
    sliceVal x 0 n = toNatLimbsList x.toList := by
  unfold sliceVal
  rw [List.drop_zero, List.take_of_length_le (by simp [h])]

/-- **Signed products**: if `mulN` multiplies `n`-limb buffers and both magnitudes fit in `n`
limbs, `signedMulWith` is the product. -/
theorem toInt_signedMulWith (n : Nat)
    (mulN : (x y : Array UInt64) → 0 + n ≤ x.size → 0 + n ≤ y.size → Array UInt64)
    (hmul : ∀ x y hx hy, toNatLimbsList (mulN x y hx hy).toList = sliceVal x 0 n * sliceVal y 0 n)
    (u v : AzInt) (hu : u.abs.toNat < 2 ^ (64 * n)) (hv : v.abs.toNat < 2 ^ (64 * n)) :
    (signedMulWith n mulN u v).toInt = u.toInt * v.toInt := by
  unfold signedMulWith
  rw [AzInt.toInt_mkNorm, toNat_ofLimbs, hmul,
    sliceVal_self _ _ (truncatePad_size _ _), sliceVal_self _ _ (truncatePad_size _ _),
    truncatePad_toNat _ _ hu, truncatePad_toNat _ _ hv]
  rw [AzInt.toInt_eq u, AzInt.toInt_eq v]
  show (if (u.sign == v.sign) = true then _ else _) = _
  cases u.sign <;> cases v.sign <;> simp [toNat]

/-- **Signed squares**: if `sqN` squares `n`-limb buffers and the magnitude fits in `n` limbs,
`signedSquareWith` is the square. -/
theorem toInt_signedSquareWith (n : Nat)
    (sqN : (x : Array UInt64) → 0 + n ≤ x.size → Array UInt64)
    (hsq : ∀ x hx, toNatLimbsList (sqN x hx).toList = sliceVal x 0 n * sliceVal x 0 n)
    (u : AzInt) (hu : u.abs.toNat < 2 ^ (64 * n)) :
    (signedSquareWith n sqN u).toInt = u.toInt * u.toInt := by
  unfold signedSquareWith
  rw [Azurite.AzNat.toInt_toAzInt, toNat_ofLimbs, hsq, sliceVal_self _ _ (truncatePad_size _ _),
    truncatePad_toNat _ _ hu, AzInt.toInt_eq u]
  cases u.sign <;> simp [toNat]

/-- **Exact division of a signed value.** -/
theorem _root_.Azurite.AzInt.toInt_exactDivOdd (d dinv : UInt64) (hinv : d * dinv = 1)
    (z : AzInt) (hd : (d.toNat : Int) ∣ z.toInt) :
    (AzInt.exactDivOdd d dinv z).toInt = z.toInt / (d.toNat : Int) := by
  have hdn : d.toNat ∣ z.abs.toNat := by
    have := Int.natAbs_dvd_natAbs.mpr hd
    rwa [Int.natAbs_natCast, AzInt.natAbs_toInt] at this
  unfold AzInt.exactDivOdd
  rw [AzInt.toInt_mkNorm, AzNat.exactDivOdd_toNat d dinv hinv _ hdn, AzInt.toInt_eq z]
  cases z.sign
  · simp only [Bool.false_eq_true, ↓reduceIte]
    rw [Int.neg_ediv_of_dvd (by exact_mod_cast hdn), Int.natCast_ediv]
  · simp only [↓reduceIte]
    exact Int.natCast_ediv _ _

/-- **Assembly**: `Σ cs[i] · β^(k·i)`. -/
theorem toNat_assemble (k : Nat) (cs : List AzNat) :
    (assemble k cs).toNat = polyEvalNat (2 ^ (64 * k)) (cs.map toNat) := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    show (c + (assemble k cs <<< (64 * k))).toNat = _
    rw [toNat_add, toNat_hShiftLeft, Nat.shiftLeft_eq, ih]
    simp only [List.map_cons, polyEvalNat_cons]
    ring

/-- The value of one block. -/
theorem toNat_block (a : Array UInt64) (lo len k j : Nat) :
    (block a lo len k j).toNat
      = sliceVal a (lo + j * k) (min (lo + (j + 1) * k) (lo + len) - (lo + j * k)) := by
  unfold block sliceVal
  rw [toNat_ofLimbs, Array.toList_extract, List.extract_eq_take_drop]

/-- Shifting the slice by one block shifts the block index. -/
theorem block_succ (a : Array UInt64) (lo len k j : Nat) (hk : k ≤ len) :
    block a lo len k (j + 1) = block a (lo + k) (len - k) k j := by
  unfold block
  rw [show lo + (j + 1) * k = lo + k + j * k by ring,
    show lo + (j + 1 + 1) * k = lo + k + (j + 1) * k by ring,
    show lo + len = lo + k + (len - k) by omega]

theorem blocks_succ (a : Array UInt64) (lo len k r : Nat) (hk : k ≤ len) :
    blocks a lo len k (r + 1)
      = (block a lo len k 0).toAzInt :: blocks a (lo + k) (len - k) k r := by
  unfold blocks
  rw [List.range_succ_eq_map, List.map_cons, List.map_map]
  congr 1
  refine List.map_congr_left fun j _ => ?_
  show (block a lo len k (j + 1)).toAzInt = (block a (lo + k) (len - k) k j).toAzInt
  rw [block_succ a lo len k j hk]

/-- The unconditional shape of `blocks (r + 1)`. -/
theorem blocks_cons (a : Array UInt64) (lo len k r : Nat) :
    blocks a lo len k (r + 1)
      = (block a lo len k 0).toAzInt
        :: (List.range r).map fun j => (block a lo len k (j + 1)).toAzInt := by
  unfold blocks
  rw [List.range_succ_eq_map, List.map_cons, List.map_map]
  rfl

/-- A slice's value is below `2^(64·len)` (no bounds needed: `take` cannot lengthen a list). -/
theorem sliceVal_lt_pow (a : Array UInt64) (lo len : Nat) :
    sliceVal a lo len < 2 ^ (64 * len) := by
  unfold sliceVal
  have h1 := toNatLimbsList_lt_pow ((a.toList.drop lo).take len)
  have h2 : ((a.toList.drop lo).take len).length ≤ len := List.length_take_le _ _
  exact lt_of_lt_of_le h1 (Nat.pow_le_pow_right (by norm_num) (by omega))

/-- Every block fits in `k` limbs. -/
theorem toNat_block_lt (a : Array UInt64) (lo len k j : Nat) :
    (block a lo len k j).toNat < 2 ^ (64 * k) := by
  rw [toNat_block]
  refine lt_of_lt_of_le (sliceVal_lt_pow _ _ _) (Nat.pow_le_pow_right (by norm_num) ?_)
  have : min (lo + (j + 1) * k) (lo + len) - (lo + j * k) ≤ k := by
    rw [Nat.add_mul, Nat.one_mul, Nat.min_def]; split_ifs <;> omega
  omega

/-- Blocks beyond the slice are zero. -/
theorem toNat_block_of_le (a : Array UInt64) (lo len k j : Nat) (h : len ≤ j * k) :
    (block a lo len k j).toNat = 0 := by
  rw [toNat_block]
  have : min (lo + (j + 1) * k) (lo + len) - (lo + j * k) = 0 := by
    rw [Nat.add_mul, Nat.one_mul, Nat.min_def]; split_ifs <;> omega
  rw [this]
  rfl

theorem polyEvalInt_eq_zero_of_forall (c : Int) (l : List Int) (h : ∀ x ∈ l, x = 0) :
    polyEvalInt c l = 0 := by
  induction l with
  | nil => rfl
  | cons b l ih =>
    rw [polyEvalInt_cons, ih (fun x hx => h x (List.mem_cons_of_mem _ hx)),
      h b (List.mem_cons_self ..)]
    ring

/-- **Block decomposition**: with `len ≤ r · k`, the slice is the base-`β^k` polynomial with
the blocks as coefficients. -/
theorem sliceVal_eq_polyEval_blocks (a : Array UInt64) (lo len k r : Nat) (hr : len ≤ r * k)
    (hA : lo + len ≤ a.size) :
    (sliceVal a lo len : Int)
      = polyEvalInt (2 ^ (64 * k)) ((blocks a lo len k r).map AzInt.toInt) := by
  induction r generalizing lo len with
  | zero =>
    have hlen : len = 0 := by simpa using hr
    subst hlen
    simp [blocks, sliceVal, polyEvalInt, toNatLimbsList_nil]
  | succ r ih =>
    rw [blocks_cons, List.map_cons, polyEvalInt_cons, Azurite.AzNat.toInt_toAzInt, toNat_block]
    by_cases hk : k ≤ len
    · -- a full first block followed by the remaining slice
      have hmin : min (lo + (0 + 1) * k) (lo + len) - (lo + 0 * k) = k := by
        rw [Nat.min_def]; split_ifs <;> omega
      rw [hmin, Nat.zero_mul, Nat.add_zero]
      have hsplit := toNatLimbsList_drop_take_split a lo len k hk hA
      have htail : ((List.range r).map fun j => (block a lo len k (j + 1)).toAzInt)
          = blocks a (lo + k) (len - k) k r := by
        unfold blocks
        refine List.map_congr_left fun j _ => ?_
        rw [block_succ a lo len k j hk]
      rw [htail, ← ih (lo + k) (len - k) (by rw [Nat.succ_mul] at hr; omega) (by omega)]
      unfold sliceVal
      rw [hsplit]
      push_cast
      ring
    · -- the slice is shorter than one block: it is block `0`, and the rest are zero
      have hmin : min (lo + (0 + 1) * k) (lo + len) - (lo + 0 * k) = len := by
        rw [Nat.min_def]; split_ifs <;> omega
      rw [hmin, Nat.zero_mul, Nat.add_zero, polyEvalInt_eq_zero_of_forall]
      · ring
      · intro x hx
        rw [List.mem_map] at hx
        obtain ⟨z, hz, rfl⟩ := hx
        rw [List.mem_map] at hz
        obtain ⟨j, _, rfl⟩ := hz
        rw [Azurite.AzNat.toInt_toAzInt, toNat_block_of_le a lo len k (j + 1) (by nlinarith)]
        rfl

end Azurite.AzNat
