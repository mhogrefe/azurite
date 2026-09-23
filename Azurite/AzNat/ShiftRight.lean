/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzNat.Basic
import Azurite.AzNat.OfLimbs
import Azurite.UInt64.Equiv.Basic

namespace Azurite.AzNat

/-- Recursive helper for `shiftLimbsRight`: processes positions `lo..i-1`
    from high to low, with an accumulated `carry`. -/
def shiftLimbsRightAux (lo sh : Nat) (a : Array UInt64) (i : Nat)
    (carry : UInt64) (h_i : i ≤ a.size) : Array UInt64 × UInt64 :=
  if h : lo < i then
    have h_im1_lt : i - 1 < a.size := by
      have : i - 1 < i := Nat.sub_lt (by omega) Nat.zero_lt_one
      omega
    let x := a[i - 1]
    let newCarry := x <<< UInt64.ofNat (64 - sh)
    let newVal := (x >>> UInt64.ofNat sh) ||| carry
    shiftLimbsRightAux lo sh (a.set (i - 1) newVal) (i - 1) newCarry
      (by rw [Array.size_set]; omega)
  else
    (a, carry)
  termination_by i

/-- Shift the subrange `a[lo:hi)` right by `sh` bits, where `1 ≤ sh ≤ 63`.
    Writes the shifted limbs back into the same slots and returns the
    modified array together with the carry limb (the bits shifted off the
    bottom of limb `lo`, positioned in the top `sh` bits of the carry). -/
def shiftLimbsRight (a : Array UInt64) (lo hi sh : Nat)
    (_hlo : lo ≤ hi) (hhi : hi ≤ a.size)
    (_hsh_lb : 1 ≤ sh) (_hsh_ub : sh ≤ 63) :
    Array UInt64 × UInt64 :=
  shiftLimbsRightAux lo sh a hi 0 hhi

/-- Size preservation of `shiftLimbsRightAux`. -/
theorem shiftLimbsRightAux_size (lo sh : Nat) (a : Array UInt64) (i : Nat)
    (carry : UInt64) (h_i : i ≤ a.size) :
    (shiftLimbsRightAux lo sh a i carry h_i).1.size = a.size := by
  induction i using Nat.strong_induction_on generalizing a carry with
  | _ i ih =>
    rw [shiftLimbsRightAux]
    by_cases hlt : lo < i
    · simp only [hlt, dite_eq_left]
      have h_dec : i - 1 < i := Nat.sub_lt (by omega) Nat.zero_lt_one
      rw [ih (i - 1) h_dec _ _ (by rw [Array.size_set]; omega)]
      rw [Array.size_set]
    · simp [hlt]

/-- Size preservation of `shiftLimbsRight`. -/
theorem shiftLimbsRight_size (a : Array UInt64) (lo hi sh : Nat)
    (hlo : lo ≤ hi) (hhi : hi ≤ a.size)
    (hsh_lb : 1 ≤ sh) (hsh_ub : sh ≤ 63) :
    (shiftLimbsRight a lo hi sh hlo hhi hsh_lb hsh_ub).1.size = a.size :=
  shiftLimbsRightAux_size lo sh a hi 0 hhi

/-- Right-shift a limb array by `sh` bits, returning the result (not
    trimmed).  Decomposes into whole-limb drop + sub-limb shift. -/
def shrLimbs (a : Array UInt64) (sh : Nat) : Array UInt64 :=
  let wholeLimbs := sh / 64
  let smallShift := sh % 64
  if wholeLimbs ≥ a.size then #[]
  else
    let dropped := a.extract wholeLimbs a.size
    if h_ss : smallShift = 0 then dropped
    else
      have h_ss_lb : 1 ≤ smallShift := by omega
      have h_ss_ub : smallShift ≤ 63 := by
        have : sh % 64 < 64 := Nat.mod_lt _ (by omega)
        omega
      (shiftLimbsRight dropped 0 dropped.size smallShift
        (Nat.zero_le _) (Nat.le_refl _) h_ss_lb h_ss_ub).1

/-- Shift right by a multiple of 64 bits: drop `k` limbs from the bottom.
    If `k ≥ a.limbs.size`, returns zero. -/
def shiftRightMul64 (a : AzNat) (k : Nat) : AzNat :=
  ofLimbs (a.limbs.extract k a.limbs.size)

/-- Limbs array for the general right-shift case (non-multiple-of-64 shift).
    Shifts the limbs of `a` right by `sh` bits. -/
def shiftRightGeneralLimbs (a : AzNat) (sh : Nat)
    (hsm : ¬ sh % 64 = 0) : AzNat :=
  let bigShift := sh / 64
  let smallShift := sh % 64
  if h : bigShift ≥ a.limbs.size then 0
  else
    have hsh_lb : 1 ≤ smallShift := by omega
    have hsh_ub : smallShift ≤ 63 := by
      have : sh % 64 < 64 := Nat.mod_lt _ (by omega)
      omega
    let shifted := (shiftLimbsRight a.limbs bigShift a.limbs.size smallShift
      (by omega) (Nat.le_refl _) hsh_lb hsh_ub).1
    ofLimbs (shifted.extract bigShift shifted.size)

/-- Right shift: `a >>> sh`.  Drops `sh / 64` limbs from the bottom, then
    shifts the remaining limbs right by `sh % 64` bits.  Multiple-of-64
    shifts are delegated to `shiftRightMul64`. -/
def shiftRight (a : AzNat) (sh : Nat) : AzNat :=
  if a.limbs.size = 0 then a
  else if hsm : sh % 64 = 0 then
    shiftRightMul64 a (sh / 64)
  else
    shiftRightGeneralLimbs a sh hsm

instance : HShiftRight AzNat Nat AzNat := ⟨shiftRight⟩

end Azurite.AzNat
