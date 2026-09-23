/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzNat.SquareModPow2.Karatsuba
import Azurite.AzNat.Equiv.Square.Karatsuba
import Azurite.AzNat.Equiv.MulModPow2.Karatsuba
import Azurite.AzNat.Equiv.AddModPow2
import Azurite.AzNat.Equiv.ShiftRight
import Mathlib.Data.Nat.GCD.Basic

/-!
## Correctness of `AzNat.squareKaratsubaModPow2`

`(squareKaratsubaModPow2 t a k).toNat = a.toNat ^ 2 % 2 ^ k`.

A direct assembly modulo `2 ^ (64·L)`: the full-square corner gives `A₀²`, the
doubled low cross product gives `2·A₀·A₁·βˢ`, and `A₁²·β^{2s} ≡ 0` (`2s ≥ L`)
recovers `(A₀ + A₁βˢ)² = a²` modulo `βᴸ`.
-/

namespace Azurite.AzNat

private lemma toNatLimbsList_replicate_zero'' (n : Nat) :
    toNatLimbsList (List.replicate n (0 : UInt64)) = 0 := by
  induction n with
  | zero => rfl
  | succ p ih => rw [List.replicate_succ, toNatLimbsList_cons, ih]; simp

private lemma toNatLimbsList_take_modEq'' (l : List UInt64) (L : Nat) :
    toNatLimbsList (l.take L) ≡ toNatLimbsList l [MOD 2 ^ (64 * L)] := by
  by_cases h : L ≤ l.length
  · have hsplit := toNatLimbsList_take_drop l L h
    unfold Nat.ModEq
    rw [hsplit, Nat.add_comm (toNatLimbsList (l.drop L) * 2 ^ (64 * L)) (toNatLimbsList (l.take L)),
      Nat.add_mul_mod_self_right]
  · rw [List.take_of_length_le (by omega)]

/-- **Correctness of `squareKaratsubaModPow2`.** -/
theorem toNat_squareKaratsubaModPow2 (threshold : Nat) (a : AzNat) (k : Nat) :
    (squareKaratsubaModPow2 threshold a k).toNat = a.toNat ^ 2 % 2 ^ k := by
  simp only [squareKaratsubaModPow2]
  set L := (k + 63) / 64 with hLdef
  set aPad : Array UInt64 := a.limbs ++ Array.replicate (L - a.limbs.size) 0 with haPad
  have hbnd : 0 + L ≤ aPad.size := by rw [haPad, Array.size_append, Array.size_replicate]; omega
  -- `aPad`'s low-`L` value is `a.toNat` modulo `β^L`.
  have hpada : toNatLimbsList (aPad.toList.take L) ≡ a.toNat [MOD 2 ^ (64 * L)] := by
    have h1 : aPad.toList = a.limbs.toList ++ List.replicate (L - a.limbs.size) 0 := by
      show (a.limbs ++ Array.replicate (L - a.limbs.size) 0).toList = _
      rw [Array.toList_append, Array.toList_replicate]
    rw [h1]
    refine (toNatLimbsList_take_modEq'' _ L).trans ?_
    rw [toNatLimbsList_append, toNatLimbsList_replicate_zero'', Nat.zero_mul, Nat.zero_add]
    exact Nat.ModEq.refl _
  -- Masking a value `≡ a.toNat² (mod β^L)` gives `a.toNat² % 2^k`.
  have hdvd : (2 : ℕ) ^ k ∣ 2 ^ (64 * L) := Nat.pow_dvd_pow 2 (by show k ≤ 64 * L; omega)
  have hreduce : ∀ X : AzNat, X.toNat ≡ a.toNat ^ 2 [MOD 2 ^ (64 * L)] →
      (modPow2 X k).toNat = a.toNat ^ 2 % 2 ^ k := by
    intro X hX
    rw [toNat_modPow2]
    unfold Nat.ModEq at hX
    rw [← Nat.mod_mod_of_dvd _ hdvd, hX, Nat.mod_mod_of_dvd _ hdvd]
  split
  · -- Base: full schoolbook square, masked.
    apply hreduce
    rw [toNat_ofLimbs, schoolbookSquareLimbs_toNat, List.drop_zero]
    exact (hpada.pow 2)
  · -- Recursive: full-square corner + doubled low cross.
    rename_i h
    set s := min ((11 * L + 15) / 16) (L - 1) with hsdef
    set m := L - s with hmdef
    have hsm : s + m = L := by omega
    have hs_lb : L ≤ 2 * s := by rw [hsdef]; omega
    have hm_le_s : m ≤ s := by omega
    have hbA : (0 : Nat) + s ≤ aPad.size := by omega
    have hbC1 : (0 : Nat) + m ≤ aPad.size := by omega
    have hbC2 : s + m ≤ aPad.size := by omega
    set cornerFull := ofLimbs (karatsubaSquareLimbs threshold aPad 0 s hbA) with hcdef
    set cross := karatsubaMulLowLimbs threshold aPad aPad 0 s m hbC1 hbC2 with hcrdef
    set doubled := addModPow2 cross cross (64 * m) with hddef
    set shifted := ofLimbs (Array.replicate s 0 ++ doubled.limbs) with hshdef
    set A0 := toNatLimbsList ((aPad.toList.drop 0).take s) with hA0v
    set A1 := toNatLimbsList ((aPad.toList.drop s).take m) with hA1v
    set A0lo := toNatLimbsList ((aPad.toList.drop 0).take m) with hA0lov
    -- Piece values.
    have hcorner : cornerFull.toNat = A0 ^ 2 := by
      rw [hcdef, toNat_ofLimbs, karatsubaSquareLimbs_toNat]
    have hcross : cross.toNat ≡ A0lo * A1 [MOD 2 ^ (64 * m)] := by
      rw [hcrdef]; exact karatsubaMulLowLimbs_modEq threshold m aPad aPad 0 s hbC1 hbC2
    have hdoubled : doubled.toNat = (cross.toNat + cross.toNat) % 2 ^ (64 * m) := by
      rw [hddef, toNat_addModPow2]
    have hshift : shifted.toNat = doubled.toNat * 2 ^ (64 * s) := by
      rw [hshdef, toNat_ofLimbs, Array.toList_append, Array.toList_replicate, toNatLimbsList_append,
        toNatLimbsList_replicate_zero'', List.length_replicate, Nat.add_zero]
      rfl
    -- `A0lo ≡ A0 (mod β^m)`.
    have hA0mod : A0lo ≡ A0 [MOD 2 ^ (64 * m)] := by
      have hsplit := toNatLimbsList_drop_take_split aPad 0 s m hm_le_s (by omega)
      rw [← hA0v, ← hA0lov] at hsplit
      unfold Nat.ModEq
      rw [hsplit, Nat.add_mul_mod_self_right]
    -- `aPad.take L = A0 + A1·β^s`.
    have hAsplit : toNatLimbsList (aPad.toList.take L) = A0 + A1 * 2 ^ (64 * s) := by
      have hsplit := toNatLimbsList_drop_take_split aPad 0 L s (by omega) (by omega)
      rw [Nat.zero_add, show L - s = m from by omega, ← hA0v, ← hA1v, List.drop_zero] at hsplit
      exact hsplit
    -- Scaling `β^m → β^L`.
    have hpow_split : (2 : ℕ) ^ (64 * L) = 2 ^ (64 * m) * 2 ^ (64 * s) := by
      rw [← Nat.pow_add]; congr 1; omega
    have hscale : ∀ x y : ℕ, x ≡ y [MOD 2 ^ (64 * m)] →
        x * 2 ^ (64 * s) ≡ y * 2 ^ (64 * s) [MOD 2 ^ (64 * L)] := by
      intro x y hxy
      unfold Nat.ModEq at hxy ⊢
      rw [hpow_split, Nat.mul_mod_mul_right, Nat.mul_mod_mul_right, hxy]
    apply hreduce
    show (addModPow2 cornerFull shifted (64 * L)).toNat ≡ a.toNat ^ 2 [MOD 2 ^ (64 * L)]
    rw [toNat_addModPow2]
    refine (Nat.mod_modEq _ _).trans ?_
    rw [hcorner, hshift]
    -- `shifted ≡ 2·A0·A1·β^s (mod β^L)`.
    have hshift_val : doubled.toNat * 2 ^ (64 * s)
        ≡ 2 * (A0 * A1) * 2 ^ (64 * s) [MOD 2 ^ (64 * L)] := by
      refine (hscale _ _ ?_)
      rw [hdoubled]
      refine (Nat.mod_modEq _ _).trans ?_
      calc cross.toNat + cross.toNat
          ≡ A0lo * A1 + A0lo * A1 [MOD 2 ^ (64 * m)] := Nat.ModEq.add hcross hcross
        _ ≡ A0 * A1 + A0 * A1 [MOD 2 ^ (64 * m)] :=
            Nat.ModEq.add (hA0mod.mul_right A1) (hA0mod.mul_right A1)
        _ = 2 * (A0 * A1) := by ring
    -- `a.toNat² ≡ A0² + 2·A0·A1·β^s (mod β^L)`.
    have hexpand : a.toNat ^ 2 ≡ A0 ^ 2 + 2 * (A0 * A1) * 2 ^ (64 * s) [MOD 2 ^ (64 * L)] := by
      have hav : a.toNat ^ 2 ≡ (A0 + A1 * 2 ^ (64 * s)) ^ 2 [MOD 2 ^ (64 * L)] := by
        rw [← hAsplit]; exact (hpada.pow 2).symm
      refine hav.trans ?_
      have hexp : (A0 + A1 * 2 ^ (64 * s)) ^ 2
          = (A0 ^ 2 + 2 * (A0 * A1) * 2 ^ (64 * s)) + A1 ^ 2 * (2 ^ (64 * s) * 2 ^ (64 * s)) := by
        ring
      rw [hexp]
      have hzero : A1 ^ 2 * (2 ^ (64 * s) * 2 ^ (64 * s)) ≡ 0 [MOD 2 ^ (64 * L)] := by
        have hdvd2 : 2 ^ (64 * L) ∣ 2 ^ (64 * s) * 2 ^ (64 * s) := by
          rw [← Nat.pow_add]; exact Nat.pow_dvd_pow 2 (by omega)
        obtain ⟨c, hc⟩ := hdvd2
        unfold Nat.ModEq
        rw [hc, show A1 ^ 2 * (2 ^ (64 * L) * c) = A1 ^ 2 * c * 2 ^ (64 * L) from by ring,
          Nat.mul_mod_left, Nat.zero_mod]
      calc A0 ^ 2 + 2 * (A0 * A1) * 2 ^ (64 * s) + A1 ^ 2 * (2 ^ (64 * s) * 2 ^ (64 * s))
          ≡ A0 ^ 2 + 2 * (A0 * A1) * 2 ^ (64 * s) + 0 [MOD 2 ^ (64 * L)] :=
            Nat.ModEq.add_left _ hzero
        _ = A0 ^ 2 + 2 * (A0 * A1) * 2 ^ (64 * s) := by rw [Nat.add_zero]
    -- Assemble: `A0² + shifted ≡ A0² + 2A0A1β^s ≡ a.toNat²`.
    exact (Nat.ModEq.add_left (A0 ^ 2) hshift_val).trans hexpand.symm

end Azurite.AzNat
