/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzNat.MulModPow2.ToomCook3
import Azurite.AzNat.Equiv.MulModPow2.Schoolbook
import Azurite.AzNat.Equiv.Mul.ToomCook3
import Azurite.AzNat.Equiv.AddModPow2
import Azurite.AzNat.Equiv.ShiftRight
import Mathlib.Data.Nat.GCD.Basic

/-!
## Correctness of `AzNat.mulToomCook3ModPow2`

`(mulToomCook3ModPow2 toomThreshold karaThreshold a b k).toNat = (a.toNat * b.toNat) % 2 ^ k`.

Identical short-product invariant to the Karatsuba-low proof (the dropped
`A₁·B₁·β^(2k)` term is `≡ 0`, the cross products agree modulo `2 ^ (64·m)`), only
the corner full product is full Toom-Cook 3 and the split is Toom-tuned.
-/

namespace Azurite.AzNat

private lemma toNatLimbsList_replicate_zero' (n : Nat) :
    toNatLimbsList (List.replicate n (0 : UInt64)) = 0 := by
  induction n with
  | zero => rfl
  | succ p ih => rw [List.replicate_succ, toNatLimbsList_cons, ih]; simp

/-- **Short-product recursion correctness.** `toomCook3MulLowLimbs` computes the
    two slices' product truncated to `2 ^ (64·len)`. -/
theorem toomCook3MulLowLimbs_modEq (toomThreshold karaThreshold : Nat) :
    ∀ (len : Nat) (a b : Array UInt64) (loA loB : Nat)
      (hA : loA + len ≤ a.size) (hB : loB + len ≤ b.size),
      (toomCook3MulLowLimbs toomThreshold karaThreshold a b loA loB len hA hB).toNat
        ≡ toNatLimbsList ((a.toList.drop loA).take len)
          * toNatLimbsList ((b.toList.drop loB).take len) [MOD 2 ^ (64 * len)] := by
  intro len
  induction len using Nat.strong_induction_on with
  | _ len ih =>
  intro a b loA loB hA hB
  by_cases h_base : len < 2 ∨ len < toomThreshold
  · rw [toomCook3MulLowLimbs, dite_eq_left h_base, toNat_ofLimbs]
    exact schoolbookMulLowLimbs_modEq a b loA len loB len len hA hB
  · have hlen : 2 ≤ len := by omega
    set k := min ((4 * len + 4) / 5) (len - 1) with hk_def
    set m := len - k with hm_def
    have hk_pos : 0 < k := by rw [hk_def]; omega
    have hm_pos : 0 < m := by rw [hm_def, hk_def]; omega
    have hm_le : m ≤ k := by rw [hm_def, hk_def]; omega
    have hkm : k + m = len := by rw [hm_def]; omega
    have hm_lt : m < len := by rw [hm_def]; omega
    have hk_le : k ≤ len := by omega
    have hA0 : loA + k ≤ a.size := by omega
    have hB0 : loB + k ≤ b.size := by omega
    have hMidA_a : loA + m ≤ a.size := by omega
    have hMidA_b : loB + k + m ≤ b.size := by omega
    have hMidB_a : loA + k + m ≤ a.size := by omega
    have hMidB_b : loB + m ≤ b.size := by omega
    set C0 := ofLimbs (toomCook3MulLimbs toomThreshold karaThreshold a b loA loB k hA0 hB0)
      with hC0_def
    set midA := toomCook3MulLowLimbs toomThreshold karaThreshold a b loA (loB + k) m hMidA_a hMidA_b
      with hmidA_def
    set midB := toomCook3MulLowLimbs toomThreshold karaThreshold a b (loA + k) loB m hMidB_a hMidB_b
      with hmidB_def
    set middle := addModPow2 midA midB (64 * m) with hmiddle_def
    set shifted := ofLimbs (Array.replicate k 0 ++ middle.limbs) with hshifted_def
    have heq : toomCook3MulLowLimbs toomThreshold karaThreshold a b loA loB len hA hB
        = addModPow2 C0 shifted (64 * len) := by
      rw [toomCook3MulLowLimbs]
      split
      · rename_i hcontra; exact absurd hcontra h_base
      · rfl
    rw [heq, toNat_addModPow2]
    -- Piece values.
    have hC0 : C0.toNat = toNatLimbsList ((a.toList.drop loA).take k)
        * toNatLimbsList ((b.toList.drop loB).take k) := by
      rw [hC0_def, toNat_ofLimbs, toomCook3MulLimbs_toNat]
    have hshift : shifted.toNat = middle.toNat * 2 ^ (64 * k) := by
      rw [hshifted_def, toNat_ofLimbs, Array.toList_append, Array.toList_replicate,
        toNatLimbsList_append, toNatLimbsList_replicate_zero', List.length_replicate,
        Nat.add_zero]
      rfl
    have hmiddle : middle.toNat = (midA.toNat + midB.toNat) % 2 ^ (64 * m) := by
      rw [hmiddle_def, toNat_addModPow2]
    have hmidA : midA.toNat ≡ toNatLimbsList ((a.toList.drop loA).take m)
        * toNatLimbsList ((b.toList.drop (loB + k)).take m) [MOD 2 ^ (64 * m)] := by
      rw [hmidA_def]; exact ih m hm_lt a b loA (loB + k) hMidA_a hMidA_b
    have hmidB : midB.toNat ≡ toNatLimbsList ((a.toList.drop (loA + k)).take m)
        * toNatLimbsList ((b.toList.drop loB).take m) [MOD 2 ^ (64 * m)] := by
      rw [hmidB_def]; exact ih m hm_lt a b (loA + k) loB hMidB_a hMidB_b
    have hAS : toNatLimbsList ((a.toList.drop loA).take len)
        = toNatLimbsList ((a.toList.drop loA).take k)
          + toNatLimbsList ((a.toList.drop (loA + k)).take m) * 2 ^ (64 * k) := by
      have h := toNatLimbsList_drop_take_split a loA len k hk_le hA
      rwa [show len - k = m from hm_def.symm] at h
    have hBS : toNatLimbsList ((b.toList.drop loB).take len)
        = toNatLimbsList ((b.toList.drop loB).take k)
          + toNatLimbsList ((b.toList.drop (loB + k)).take m) * 2 ^ (64 * k) := by
      have h := toNatLimbsList_drop_take_split b loB len k hk_le hB
      rwa [show len - k = m from hm_def.symm] at h
    have hA0mod : toNatLimbsList ((a.toList.drop loA).take k)
        ≡ toNatLimbsList ((a.toList.drop loA).take m) [MOD 2 ^ (64 * m)] := by
      have h := toNatLimbsList_drop_take_split a loA k m hm_le hA0
      rw [h]; unfold Nat.ModEq; rw [Nat.add_mul_mod_self_right]
    have hB0mod : toNatLimbsList ((b.toList.drop loB).take k)
        ≡ toNatLimbsList ((b.toList.drop loB).take m) [MOD 2 ^ (64 * m)] := by
      have h := toNatLimbsList_drop_take_split b loB k m hm_le hB0
      rw [h]; unfold Nat.ModEq; rw [Nat.add_mul_mod_self_right]
    -- Shorten the slice values.
    set A0 := toNatLimbsList ((a.toList.drop loA).take k) with hA0v
    set A1 := toNatLimbsList ((a.toList.drop (loA + k)).take m) with hA1v
    set B0 := toNatLimbsList ((b.toList.drop loB).take k) with hB0v
    set B1 := toNatLimbsList ((b.toList.drop (loB + k)).take m) with hB1v
    set A0lo := toNatLimbsList ((a.toList.drop loA).take m) with hA0lov
    set B0lo := toNatLimbsList ((b.toList.drop loB).take m) with hB0lov
    set AS := toNatLimbsList ((a.toList.drop loA).take len) with hASv
    set BS := toNatLimbsList ((b.toList.drop loB).take len) with hBSv
    -- middle ≡ A0·B1 + A1·B0.
    have hmid_val : middle.toNat ≡ A0 * B1 + A1 * B0 [MOD 2 ^ (64 * m)] := by
      rw [hmiddle]
      refine (Nat.mod_modEq _ _).trans ?_
      exact Nat.ModEq.add (hmidA.trans (Nat.ModEq.mul_right B1 hA0mod.symm))
        (hmidB.trans (Nat.ModEq.mul_left A1 hB0mod.symm))
    -- Scale by β^k (the modulus grows to β^len).
    have hpow_split : (2 : ℕ) ^ (64 * len) = 2 ^ (64 * m) * 2 ^ (64 * k) := by
      rw [← Nat.pow_add]; congr 1; omega
    have hscale : middle.toNat * 2 ^ (64 * k)
        ≡ (A0 * B1 + A1 * B0) * 2 ^ (64 * k) [MOD 2 ^ (64 * len)] := by
      unfold Nat.ModEq at hmid_val ⊢
      rw [hpow_split, Nat.mul_mod_mul_right, Nat.mul_mod_mul_right, hmid_val]
    rw [hC0, hshift]
    -- Final assembly modulo β^len.
    have hfinal : A0 * B0 + middle.toNat * 2 ^ (64 * k) ≡ AS * BS [MOD 2 ^ (64 * len)] := by
      refine (Nat.ModEq.add_left _ hscale).trans ?_
      rw [hAS, hBS]
      have hexp : (A0 + A1 * 2 ^ (64 * k)) * (B0 + B1 * 2 ^ (64 * k))
          = (A0 * B0 + (A0 * B1 + A1 * B0) * 2 ^ (64 * k))
            + A1 * B1 * (2 ^ (64 * k) * 2 ^ (64 * k)) := by ring
      rw [hexp]
      have hzero : A1 * B1 * (2 ^ (64 * k) * 2 ^ (64 * k)) ≡ 0 [MOD 2 ^ (64 * len)] := by
        have hdvd : 2 ^ (64 * len) ∣ 2 ^ (64 * k) * 2 ^ (64 * k) := by
          rw [← Nat.pow_add]; exact Nat.pow_dvd_pow 2 (by omega)
        obtain ⟨c, hc⟩ := hdvd
        unfold Nat.ModEq
        rw [hc, show A1 * B1 * (2 ^ (64 * len) * c) = A1 * B1 * c * 2 ^ (64 * len) from by ring,
          Nat.mul_mod_left, Nat.zero_mod]
      have hcollapse : A0 * B0 + (A0 * B1 + A1 * B0) * 2 ^ (64 * k)
          + A1 * B1 * (2 ^ (64 * k) * 2 ^ (64 * k))
          ≡ A0 * B0 + (A0 * B1 + A1 * B0) * 2 ^ (64 * k) [MOD 2 ^ (64 * len)] := by
        calc A0 * B0 + (A0 * B1 + A1 * B0) * 2 ^ (64 * k)
              + A1 * B1 * (2 ^ (64 * k) * 2 ^ (64 * k))
            ≡ A0 * B0 + (A0 * B1 + A1 * B0) * 2 ^ (64 * k) + 0 [MOD 2 ^ (64 * len)] :=
              Nat.ModEq.add_left _ hzero
          _ = A0 * B0 + (A0 * B1 + A1 * B0) * 2 ^ (64 * k) := by rw [Nat.add_zero]
      exact hcollapse.symm
    exact (Nat.mod_modEq _ _).trans hfinal

/-- Truncating a limb list to its low `L` limbs changes the value only by a
    multiple of `2 ^ (64·L)`. -/
private lemma toNatLimbsList_take_modEq' (l : List UInt64) (L : Nat) :
    toNatLimbsList (l.take L) ≡ toNatLimbsList l [MOD 2 ^ (64 * L)] := by
  by_cases h : L ≤ l.length
  · have hsplit := toNatLimbsList_take_drop l L h
    unfold Nat.ModEq
    rw [hsplit, Nat.add_comm (toNatLimbsList (l.drop L) * 2 ^ (64 * L)) (toNatLimbsList (l.take L)),
      Nat.add_mul_mod_self_right]
  · rw [List.take_of_length_le (by omega)]

/-- **Correctness of `mulToomCook3ModPow2`.** -/
theorem toNat_mulToomCook3ModPow2 (toomThreshold karaThreshold : Nat) (a b : AzNat) (k : Nat) :
    (mulToomCook3ModPow2 toomThreshold karaThreshold a b k).toNat = (a.toNat * b.toNat) % 2 ^ k := by
  unfold mulToomCook3ModPow2
  rw [toNat_modPow2]
  set L := (k + 63) / 64 with hLdef
  set aPad : Array UInt64 := a.limbs ++ Array.replicate (L - a.limbs.size) 0 with haPad
  set bPad : Array UInt64 := b.limbs ++ Array.replicate (L - b.limbs.size) 0 with hbPad
  have hbndA : 0 + L ≤ aPad.size := by rw [haPad, Array.size_append, Array.size_replicate]; omega
  have hbndB : 0 + L ≤ bPad.size := by rw [hbPad, Array.size_append, Array.size_replicate]; omega
  have hmod := toomCook3MulLowLimbs_modEq toomThreshold karaThreshold L aPad bPad 0 0 hbndA hbndB
  rw [List.drop_zero, List.drop_zero] at hmod
  have hpada : toNatLimbsList (aPad.toList.take L) ≡ a.toNat [MOD 2 ^ (64 * L)] := by
    have h1 : aPad.toList = a.limbs.toList ++ List.replicate (L - a.limbs.size) 0 := by
      rw [haPad, Array.toList_append, Array.toList_replicate]
    rw [h1]
    refine (toNatLimbsList_take_modEq' _ L).trans ?_
    rw [toNatLimbsList_append, toNatLimbsList_replicate_zero', Nat.zero_mul, Nat.zero_add]
    exact Nat.ModEq.refl _
  have hpadb : toNatLimbsList (bPad.toList.take L) ≡ b.toNat [MOD 2 ^ (64 * L)] := by
    have h1 : bPad.toList = b.limbs.toList ++ List.replicate (L - b.limbs.size) 0 := by
      rw [hbPad, Array.toList_append, Array.toList_replicate]
    rw [h1]
    refine (toNatLimbsList_take_modEq' _ L).trans ?_
    rw [toNatLimbsList_append, toNatLimbsList_replicate_zero', Nat.zero_mul, Nat.zero_add]
    exact Nat.ModEq.refl _
  have hprod := hmod.trans (Nat.ModEq.mul hpada hpadb)
  have hdvd : (2 : ℕ) ^ k ∣ 2 ^ (64 * L) := Nat.pow_dvd_pow 2 (by rw [hLdef]; omega)
  unfold Nat.ModEq at hprod
  rw [← Nat.mod_mod_of_dvd _ hdvd, hprod, Nat.mod_mod_of_dvd _ hdvd]

end Azurite.AzNat
