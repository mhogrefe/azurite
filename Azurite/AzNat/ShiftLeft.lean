/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzNat.Basic
import Azurite.UInt64.Equiv.Basic

namespace Azurite.AzNat

/-- Shift the subrange `a[lo:hi)` left by `sh` bits, where `1 ≤ sh ≤ 63`.
    Writes the shifted limbs back into the same slots and returns the
    modified array together with the carry limb (the bits shifted off the top). -/
def shiftLimbsLeft (a : Array UInt64) (lo hi sh : Nat)
    (_hlo : lo ≤ hi) (hhi : hi ≤ a.size)
    (_hsh_lb : 1 ≤ sh) (_hsh_ub : sh ≤ 63) :
    Array UInt64 × UInt64 :=
  go a lo 0 hhi
where
  go (a : Array UInt64) (i : Nat) (carry : UInt64) (h_size : hi ≤ a.size) :
      Array UInt64 × UInt64 :=
    if h : i < hi then
      have h_i_size : i < a.size := Nat.lt_of_lt_of_le h h_size
      let x := a[i]
      let newCarry := x >>> UInt64.ofNat (64 - sh)
      let newVal := (x <<< UInt64.ofNat sh) ||| carry
      go (a.set i newVal) (i + 1) newCarry
        (by rw [Array.size_set]; exact h_size)
    else
      (a, carry)
  termination_by hi - i

/-- Size preservation of `shiftLimbsLeft.go`. -/
theorem shiftLimbsLeft.go_size (hi sh : Nat) (a : Array UInt64) (i : Nat)
    (carry : UInt64) (h_size : hi ≤ a.size) :
    (shiftLimbsLeft.go hi sh a i carry h_size).1.size = a.size := by
  induction hi_sub_i : hi - i generalizing a i carry with
  | zero =>
    have h_ge : hi ≤ i := by omega
    rw [shiftLimbsLeft.go]
    simp [Nat.not_lt.mpr h_ge]
  | succ n ih =>
    have h_lt : i < hi := by omega
    rw [shiftLimbsLeft.go]
    simp only [h_lt, dite_eq_left]
    have h_rec : hi - (i + 1) = n := by omega
    rw [ih _ _ _ _ h_rec]
    rw [Array.size_set]

/-- Size preservation of `shiftLimbsLeft`. -/
theorem shiftLimbsLeft_size (a : Array UInt64) (lo hi sh : Nat)
    (hlo : lo ≤ hi) (hhi : hi ≤ a.size)
    (hsh_lb : 1 ≤ sh) (hsh_ub : sh ≤ 63) :
    (shiftLimbsLeft a lo hi sh hlo hhi hsh_lb hsh_ub).1.size = a.size :=
  shiftLimbsLeft.go_size hi sh a lo 0 hhi

/-- Shift left by a multiple of 64 bits: prepend `k` zero limbs.  For the zero
    AzNat (empty `limbs`), return `a` unchanged. -/
def shiftLeftMul64 (a : AzNat) (k : Nat) : AzNat :=
  if hz : a.limbs.size = 0 then a
  else
    { limbs := Array.replicate k 0 ++ a.limbs
      last_ne_zero := by
        have h_limbs_ne : a.limbs ≠ #[] := by
          intro h
          apply hz
          rw [h]; rfl
        rw [Array.back?_append]
        -- a.limbs is nonempty, so a.limbs.back? = some v for some v ≠ 0
        cases hb : a.limbs.back? with
        | none =>
          rw [Array.back?_eq_none_iff] at hb
          exact absurd hb h_limbs_ne
        | some v =>
          intro h_eq
          exact a.last_ne_zero (hb.trans h_eq) }

/-- Key UInt64 fact: if `x ≠ 0` and shifting right by `64 - sh` yields zero, then
    shifting left by `sh` is nonzero. -/
private theorem shl_ne_zero_of_shr_eq_zero (x : UInt64) (sh : Nat)
    (hsh_lb : 1 ≤ sh) (hsh_ub : sh ≤ 63)
    (hx : x ≠ 0) (hshr : x >>> UInt64.ofNat (64 - sh) = 0) :
    x <<< UInt64.ofNat sh ≠ 0 := by
  have hsh_lt : sh < 64 := by omega
  have h_sub_lt : 64 - sh < 64 := by omega
  have h_ofNat_sh : (UInt64.ofNat sh).toNat = sh := by
    show sh % 2 ^ 64 = sh; exact Nat.mod_eq_of_lt (by omega)
  have h_ofNat_sub : (UInt64.ofNat (64 - sh)).toNat = 64 - sh := by
    show (64 - sh) % 2 ^ 64 = 64 - sh; exact Nat.mod_eq_of_lt (by omega)
  have h_sub_mod : (64 - sh) % 64 = 64 - sh := Nat.mod_eq_of_lt h_sub_lt
  have h_sh_mod : sh % 64 = sh := Nat.mod_eq_of_lt hsh_lt
  have hx_nat : x.toNat ≠ 0 := by
    intro h
    apply hx
    apply UInt64.eq_of_toNat_eq
    rw [h]; rfl
  have hx_lt : x.toNat < 2 ^ 64 := UInt64.toNat_lt _
  have h_shr_nat : (x >>> UInt64.ofNat (64 - sh)).toNat = x.toNat / 2 ^ (64 - sh) := by
    rw [UInt64.toNat_shiftRight, h_ofNat_sub, h_sub_mod, Nat.shiftRight_eq_div_pow]
  have h_shr_zero : x.toNat / 2 ^ (64 - sh) = 0 := by
    rw [← h_shr_nat, hshr]; rfl
  have h_x_lt : x.toNat < 2 ^ (64 - sh) := by
    by_contra hge
    have hge' : 2 ^ (64 - sh) ≤ x.toNat := Nat.le_of_not_lt hge
    have h1 : 1 ≤ x.toNat / 2 ^ (64 - sh) :=
      (Nat.one_le_div_iff (Nat.two_pow_pos _)).mpr hge'
    omega
  have h_pow_eq : 2 ^ (64 - sh) * 2 ^ sh = 2 ^ 64 := by
    rw [← Nat.pow_add]; congr 1; omega
  have h_prod_lt : x.toNat * 2 ^ sh < 2 ^ 64 := by
    calc x.toNat * 2 ^ sh < 2 ^ (64 - sh) * 2 ^ sh :=
            (Nat.mul_lt_mul_right (Nat.two_pow_pos _)).mpr h_x_lt
      _ = 2 ^ 64 := h_pow_eq
  have h_shl_nat : (x <<< UInt64.ofNat sh).toNat = x.toNat * 2 ^ sh := by
    rw [UInt64.toNat_shiftLeft, h_ofNat_sh, h_sh_mod, Nat.shiftLeft_eq,
        Nat.mod_eq_of_lt h_prod_lt]
  intro h
  have h0 : (x <<< UInt64.ofNat sh).toNat = 0 := by rw [h]; rfl
  rw [h_shl_nat] at h0
  have hpos : 0 < 2 ^ sh := Nat.two_pow_pos _
  have : x.toNat = 0 := by
    rcases Nat.mul_eq_zero.mp h0 with h | h
    · exact h
    · omega
  exact hx_nat this

/-- If `x ||| y = 0` in UInt64, the left operand is zero. -/
private theorem lor_eq_zero_left_uint64 (x y : UInt64) (h : x ||| y = 0) :
    x = 0 := by
  apply UInt64.eq_of_toNat_eq
  have hor : (x ||| y).toNat = 0 := by rw [h]; rfl
  rw [UInt64.toNat_or] at hor
  apply Nat.eq_of_testBit_eq
  intro j
  have hj : (x.toNat ||| y.toNat).testBit j = false := by rw [hor]; exact Nat.zero_testBit j
  rw [Nat.testBit_or] at hj
  have hx : x.toNat.testBit j = false := (Bool.or_eq_false_iff.mp hj).1
  rw [hx]
  show false = (0 : UInt64).toNat.testBit j
  rw [show (0 : UInt64).toNat = 0 from rfl, Nat.zero_testBit]

/-- Limbs array for the general left-shift case (non-multiple-of-64 shift).
    Shifts the limbs of `a` left by `sh` bits, returning the resulting limb array. -/
def shiftLeftGeneralLimbs (a : AzNat) (sh : Nat)
    (hz : ¬ a.limbs.size = 0) (hsm : ¬ sh % 64 = 0) : Array UInt64 :=
  let bigShift := sh / 64
  let smallShift := sh % 64
  have hsh_lb : 1 ≤ smallShift := by omega
  have hsh_ub : smallShift ≤ 63 := by
    have : sh % 64 < 64 := Nat.mod_lt _ (by omega)
    omega
  let combined : Array UInt64 := Array.replicate bigShift 0 ++ a.limbs
  have hcs : combined.size = bigShift + a.limbs.size := by
    simp [combined, Array.size_append, Array.size_replicate]
  let prefixResult := shiftLimbsLeft combined bigShift (bigShift + a.limbs.size - 1)
    smallShift (by omega) (by omega) hsh_lb hsh_ub
  let prefixShifted := prefixResult.1
  let prevCarry := prefixResult.2
  have h_psize : prefixShifted.size = bigShift + a.limbs.size := by
    show (shiftLimbsLeft _ _ _ _ _ _ _ _).1.size = _
    rw [shiftLimbsLeft_size]; exact hcs
  have h_last_idx : bigShift + a.limbs.size - 1 < prefixShifted.size := by
    rw [h_psize]; omega
  let last_orig : UInt64 := a.limbs[a.limbs.size - 1]'
    (Nat.sub_lt (Nat.pos_of_ne_zero hz) Nat.zero_lt_one)
  let new_last : UInt64 := (last_orig <<< UInt64.ofNat smallShift) ||| prevCarry
  let top_carry : UInt64 := last_orig >>> UInt64.ofNat (64 - smallShift)
  let withLast := prefixShifted.set (bigShift + a.limbs.size - 1) new_last h_last_idx
  if top_carry = 0 then withLast else withLast.push top_carry

/-- The last limb of `shiftLeftGeneralLimbs` is nonzero. -/
theorem shiftLeftGeneralLimbs_last_ne_zero (a : AzNat) (sh : Nat)
    (hz : ¬ a.limbs.size = 0) (hsm : ¬ sh % 64 = 0) :
    (shiftLeftGeneralLimbs a sh hz hsm).back? ≠ some 0 := by
  have hsh_lb : 1 ≤ sh % 64 := by omega
  have hsh_ub : sh % 64 ≤ 63 := by
    have : sh % 64 < 64 := Nat.mod_lt _ (by omega)
    omega
  have hn_pos : 0 < a.limbs.size := Nat.pos_of_ne_zero hz
  have h_last_idx_lt : a.limbs.size - 1 < a.limbs.size := Nat.sub_lt hn_pos Nat.zero_lt_one
  have h_last_orig_ne : a.limbs[a.limbs.size - 1]'h_last_idx_lt ≠ 0 := by
    intro h_eq
    apply a.last_ne_zero
    rw [Array.back?_eq_getElem?, Array.getElem?_eq_getElem h_last_idx_lt]
    exact congrArg some h_eq
  unfold shiftLeftGeneralLimbs
  extract_lets bigShift smallShift _ _ combined _ prefixResult prefixShifted prevCarry
    h_psize h_last_idx last_orig new_last top_carry withLast
  by_cases htc : top_carry = 0
  · simp only [htc, ite_true]
    have h_wsize : withLast.size = bigShift + a.limbs.size := by
      show (prefixShifted.set _ _ _).size = _
      rw [Array.size_set]; exact h_psize
    have h_idx_lt : bigShift + a.limbs.size - 1 < withLast.size := by rw [h_wsize]; omega
    have h_get_self : withLast[bigShift + a.limbs.size - 1]'h_idx_lt = new_last :=
      Array.getElem_set_self h_last_idx
    have h_back : withLast.back? = some new_last := by
      rw [Array.back?_eq_getElem?]
      have h1 : withLast.size - 1 = bigShift + a.limbs.size - 1 := by rw [h_wsize]
      rw [h1, Array.getElem?_eq_getElem h_idx_lt, h_get_self]
    rw [h_back]
    intro h
    have hnl : new_last = 0 := Option.some.inj h
    have hshl : last_orig <<< UInt64.ofNat smallShift = 0 :=
      lor_eq_zero_left_uint64 _ _ hnl
    exact shl_ne_zero_of_shr_eq_zero last_orig smallShift hsh_lb hsh_ub
      h_last_orig_ne htc hshl
  · simp only [htc, ite_false]
    rw [Array.back?_push]
    intro h
    exact htc (Option.some.inj h)

/-- Left shift: `a <<< sh`.  Writes `sh / 64` zero limbs at the bottom, then
    shifts the original limbs left by `sh % 64` bits within the combined array.
    Multiple-of-64 shifts are delegated to `shiftLeftMul64`. -/
def shiftLeft (a : AzNat) (sh : Nat) : AzNat :=
  if hz : a.limbs.size = 0 then a
  else if hsm : sh % 64 = 0 then
    shiftLeftMul64 a (sh / 64)
  else
    ⟨shiftLeftGeneralLimbs a sh hz hsm,
      shiftLeftGeneralLimbs_last_ne_zero a sh hz hsm⟩

instance : HShiftLeft AzNat Nat AzNat := ⟨shiftLeft⟩

/-- Shifting left preserves the zero/nonzero distinction. -/
theorem shiftLeft_eq_zero {a : AzNat} {sh : Nat} (h : a <<< sh = 0) : a = 0 := by
  show a = ⟨#[], by simp⟩
  have h_eq : a <<< sh = shiftLeft a sh := rfl
  rw [h_eq] at h
  unfold shiftLeft at h
  by_cases hz : a.limbs.size = 0
  · -- a.limbs.size = 0 → a = 0
    rw [dite_eq_left hz] at h
    exact h
  · exfalso
    rw [dite_eq_right hz] at h
    by_cases hsm : sh % 64 = 0
    · rw [dite_eq_left hsm] at h
      have h_eq_zero : shiftLeftMul64 a (sh / 64) = ⟨#[], by simp⟩ := h
      unfold shiftLeftMul64 at h_eq_zero
      rw [dite_eq_right hz] at h_eq_zero
      have h_limbs : (Array.replicate (sh / 64) 0 ++ a.limbs : Array UInt64) = #[] := by
        have := congrArg AzNat.limbs h_eq_zero
        exact this
      have h_size : (Array.replicate (sh / 64) 0 ++ a.limbs).size = 0 := by
        rw [h_limbs]; rfl
      rw [Array.size_append, Array.size_replicate] at h_size
      omega
    · rw [dite_eq_right hsm] at h
      have h_limbs : shiftLeftGeneralLimbs a sh hz hsm = #[] := by
        have := congrArg AzNat.limbs h
        exact this
      -- shiftLeftGeneralLimbs builds an array with size ≥ bigShift + a.limbs.size > 0
      unfold shiftLeftGeneralLimbs at h_limbs
      simp only at h_limbs
      have hn_pos : 0 < a.limbs.size := Nat.pos_of_ne_zero hz
      set bigShift := sh / 64
      set smallShift := sh % 64
      have hsh_lb : 1 ≤ smallShift := by omega
      have hsh_ub : smallShift ≤ 63 := by
        have : sh % 64 < 64 := Nat.mod_lt _ (by omega)
        omega
      set combined : Array UInt64 := Array.replicate bigShift 0 ++ a.limbs
      have hcs : combined.size = bigShift + a.limbs.size := by
        simp [combined, Array.size_append, Array.size_replicate]
      set prefixResult := shiftLimbsLeft combined bigShift (bigShift + a.limbs.size - 1)
        smallShift (by omega) (by omega) hsh_lb hsh_ub
      have h_psize : prefixResult.1.size = bigShift + a.limbs.size := by
        show (shiftLimbsLeft _ _ _ _ _ _ _ _).1.size = _
        rw [shiftLimbsLeft_size]; exact hcs
      have h_last_idx : bigShift + a.limbs.size - 1 < prefixResult.1.size := by
        rw [h_psize]; omega
      set new_last_arr := prefixResult.1.set (bigShift + a.limbs.size - 1)
        ((a.limbs[a.limbs.size - 1]'(Nat.sub_lt hn_pos Nat.zero_lt_one)
          <<< UInt64.ofNat smallShift) ||| prefixResult.2) h_last_idx
      have h_size_pos : 0 < new_last_arr.size := by
        show 0 < (prefixResult.1.set _ _ _).size
        rw [Array.size_set]; rw [h_psize]; omega
      split_ifs at h_limbs with htc
      · have h0 : new_last_arr.size = 0 := by rw [h_limbs]; rfl
        omega
      · have h_push_size :
            (new_last_arr.push (a.limbs[a.limbs.size - 1]'
              (Nat.sub_lt hn_pos Nat.zero_lt_one)
              >>> UInt64.ofNat (64 - smallShift))).size = 0 := by
          rw [h_limbs]; rfl
        rw [Array.size_push] at h_push_size
        omega

end Azurite.AzNat
