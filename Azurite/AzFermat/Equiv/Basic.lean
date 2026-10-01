/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFermat.Basic
import Azurite.BrentZimmermann.Chapter2.FFTMulMod
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.LinearCombination

/-!
# `AzFermat N ↔ ZMod (2^N + 1)`

`toZMod` sends a canonical residue to `ZMod (2^N + 1)`; it is injective (`toZMod_injective`) and
turns every operation of `AzFermat/Basic.lean` into the corresponding ring operation:
`toZMod_add`, `toZMod_sub`, `toZMod_neg`, `toZMod_mulWith`, `toZMod_reduceSplit`, `toZMod_reduceAny`,
`toZMod_mulPow2` (`= toZMod a * 2^t`), `toZMod_divPow2_mul_two_pow`
(`toZMod (divPow2 t a) * 2^t = toZMod a`).  The two facts about the modulus are `two_pow_eq_neg_one`
(`2^N = −1`) and `two_pow_two_mul_eq_one` (`2^{2N} = 1`).
-/

namespace Azurite.AzFermat

variable {N : Nat}

instance : NeZero (2 ^ N + 1) := ⟨Nat.succ_ne_zero _⟩

/-- The residue in `ZMod (2^N + 1)`. -/
def toZMod (a : AzFermat N) : ZMod (2 ^ N + 1) := (a.val.toNat : ZMod (2 ^ N + 1))

theorem toZMod_val (a : AzFermat N) : (toZMod a).val = a.val.toNat := by
  rw [toZMod, ZMod.val_natCast, Nat.mod_eq_of_lt (Nat.lt_succ_of_le a.isLe)]

theorem toZMod_injective : Function.Injective (toZMod (N := N)) := fun a b h => by
  apply ext
  apply AzNat.toNat_injective
  rw [← toZMod_val, ← toZMod_val, h]

theorem two_pow_eq_neg_one : (2 : ZMod (2 ^ N + 1)) ^ N = -1 := BZ.two_pow_eq_neg_one_zmod N

theorem two_pow_two_mul_eq_one : (2 : ZMod (2 ^ N + 1)) ^ (2 * N) = 1 := by
  rw [pow_mul', two_pow_eq_neg_one]
  norm_num

theorem toZMod_mk (v : AzNat) (h : v.toNat ≤ 2 ^ N) :
    toZMod (⟨v, h⟩ : AzFermat N) = (v.toNat : ZMod (2 ^ N + 1)) := rfl

@[simp] theorem toZMod_zero : toZMod (0 : AzFermat N) = 0 := by
  rw [toZMod, val_zero, AzNat.toNat_zero, Nat.cast_zero]

theorem toZMod_add' (a b : AzFermat N) : toZMod (add a b) = toZMod a + toZMod b := by
  unfold add
  dsimp only
  split_ifs with h h2
  · rw [toZMod_mk, AzNat.toNat_add, Nat.cast_add]
    rfl
  · rw [toZMod_mk, AzNat.toNat_add, Nat.cast_add]
    rfl
  · have hlt := two_pow_lt_toNat_of_not (a.val + b.val) h h2
    simp only [toZMod, AzNat.toNat_subUInt64, AzNat.toNat_sub, AzNat.toNat_pow2, UInt64.toNat_one]
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega), AzNat.toNat_add]
    push_cast
    rw [two_pow_eq_neg_one]
    ring

theorem toZMod_add (a b : AzFermat N) : toZMod (a + b) = toZMod a + toZMod b := toZMod_add' a b

theorem toZMod_sub' (a b : AzFermat N) : toZMod (sub a b) = toZMod a - toZMod b := by
  unfold sub
  split_ifs with h
  · rw [AzNat.le_iff_toNat_le] at h
    rw [toZMod_mk, AzNat.toNat_sub, Nat.cast_sub h]
    rfl
  · rw [AzNat.le_iff_toNat_le] at h
    have hb := b.isLe
    simp only [toZMod, AzNat.toNat_addUInt64, AzNat.toNat_sub, AzNat.toNat_add, AzNat.toNat_pow2,
      UInt64.toNat_one]
    rw [Nat.cast_add, Nat.cast_sub (by omega)]
    push_cast
    rw [two_pow_eq_neg_one]
    ring

theorem toZMod_sub (a b : AzFermat N) : toZMod (a - b) = toZMod a - toZMod b := toZMod_sub' a b

theorem toZMod_neg' (a : AzFermat N) : toZMod (neg a) = -toZMod a := by
  rw [neg, toZMod_sub', toZMod_zero, zero_sub]

theorem toZMod_neg (a : AzFermat N) : toZMod (-a) = -toZMod a := toZMod_neg' a

theorem toZMod_lowPart (p : AzNat) : toZMod (lowPart p) = ((p.toNat % 2 ^ N : ℕ) : ZMod (2 ^ N + 1)) := by
  unfold lowPart
  split_ifs with h64
  · rw [toZMod_mk, AzNat.toNat_ofLimbs, toNatLimbsList_extract', List.drop_zero,
      AzNat.toNatLimbsList_take, show 64 * (N / 64) = N by omega]
    rfl
  · rw [toZMod_mk, AzNat.toNat_modPow2]

theorem toZMod_highPart (p : AzNat) (hp : p.toNat / 2 ^ N ≤ 2 ^ N) :
    toZMod (highPart p hp) = ((p.toNat / 2 ^ N : ℕ) : ZMod (2 ^ N + 1)) := by
  unfold highPart
  split_ifs with h64
  · rw [toZMod_mk, AzNat.toNat_ofLimbs, toNatLimbsList_extract',
      List.take_of_length_le (by rw [List.length_drop, Array.length_toList]; omega),
      AzNat.toNatLimbsList_drop, show 64 * (N / 64) = N by omega]
    rfl
  · rw [toZMod_mk, AzNat.toNat_hShiftRight, Nat.shiftRight_eq_div_pow]

/-- `reduceSplit` is reduction: `hi · 2^N + lo ≡ lo − hi` because `2^N ≡ −1`, negated when asked. -/
theorem toZMod_reduceSplit (negate : Bool) (p : AzNat) (hp : p.toNat / 2 ^ N ≤ 2 ^ N) :
    toZMod (reduceSplit negate p hp)
      = if negate then -(p.toNat : ZMod (2 ^ N + 1)) else (p.toNat : ZMod (2 ^ N + 1)) := by
  have h := Nat.div_add_mod p.toNat (2 ^ N)
  have hc : ((2 ^ N * (p.toNat / 2 ^ N) + p.toNat % 2 ^ N : ℕ) : ZMod (2 ^ N + 1))
      = (p.toNat : ZMod (2 ^ N + 1)) := by rw [h]
  push_cast at hc
  rw [two_pow_eq_neg_one] at hc
  unfold reduceSplit
  split_ifs with hneg
  · rw [toZMod_sub', toZMod_highPart, toZMod_lowPart]
    linear_combination -hc
  · rw [toZMod_sub', toZMod_lowPart, toZMod_highPart]
    linear_combination hc

theorem toZMod_reduceAny [NeZero N] (p : AzNat) :
    toZMod (reduceAny p) = (p.toNat : ZMod (2 ^ N + 1)) := by
  induction p using reduceAny.induct (N := N) with
  | case1 p h =>
    rw [reduceAny, dite_eq_left h, toZMod_reduceSplit]
    rfl
  | case2 p h ih =>
    rw [reduceAny, dite_eq_right h, toZMod_sub', toZMod_mk, ih, AzNat.toNat_modPow2,
      AzNat.toNat_hShiftRight, Nat.shiftRight_eq_div_pow]
    have hd := Nat.div_add_mod p.toNat (2 ^ N)
    have hc : ((2 ^ N * (p.toNat / 2 ^ N) + p.toNat % 2 ^ N : ℕ) : ZMod (2 ^ N + 1))
        = (p.toNat : ZMod (2 ^ N + 1)) := by rw [hd]
    push_cast at hc
    rw [two_pow_eq_neg_one] at hc
    linear_combination hc

theorem toZMod_ofAzNat [NeZero N] (n : AzNat) :
    toZMod (ofAzNat N n) = (n.toNat : ZMod (2 ^ N + 1)) := toZMod_reduceAny n

/-- `mulWith mulFn` multiplies, for any correct multiplier. -/
theorem toZMod_mulWith [NeZero N] (mulFn : AzNat → AzNat → AzNat) (a b : AzFermat N)
    (hmul : (mulFn a.val b.val).toNat = a.val.toNat * b.val.toNat) :
    toZMod (mulWith mulFn a b) = toZMod a * toZMod b := by
  rw [mulWith, toZMod_reduceAny, hmul, Nat.cast_mul]
  rfl

theorem toZMod_mulPow2Le (t : Nat) (ht : t ≤ N) (negate : Bool) (a : AzFermat N) :
    toZMod (mulPow2Le t ht negate a)
      = if negate then -(toZMod a * 2 ^ t) else toZMod a * 2 ^ t := by
  rw [mulPow2Le, toZMod_reduceSplit, AzNat.toNat_hShiftLeft, Nat.shiftLeft_eq]
  push_cast
  rfl

/-- `mulPow2 t` multiplies by `2^t`. -/
theorem toZMod_mulPow2 [NeZero N] (t : Nat) (a : AzFermat N) :
    toZMod (mulPow2 t a) = toZMod a * 2 ^ t := by
  have ht2 : (2 : ZMod (2 ^ N + 1)) ^ t = 2 ^ (t % (2 * N)) :=
    pow_eq_pow_mod t two_pow_two_mul_eq_one
  unfold mulPow2
  dsimp only
  split_ifs with h0 h
  · rw [ht2, h0, pow_zero, mul_one]
  · rw [toZMod_mulPow2Le, ht2]
    rfl
  · rw [toZMod_mulPow2Le, ht2]
    set t' := t % (2 * N) with ht'
    have hsplit : (2 : ZMod (2 ^ N + 1)) ^ t' = -(2 ^ (t' - N)) := by
      rw [show t' = N + (t' - N) by omega, pow_add, two_pow_eq_neg_one, Nat.add_sub_cancel_left]
      ring
    rw [hsplit]
    simp only [↓reduceIte]
    ring

/-- `mulPow2Split t` is `2^t` up to the returned sign. -/
theorem toZMod_mulPow2Split [NeZero N] (t : Nat) (a : AzFermat N) :
    toZMod (mulPow2Split t a).1
      = if (mulPow2Split t a).2 then -(toZMod a * 2 ^ t) else toZMod a * 2 ^ t := by
  have ht2 : (2 : ZMod (2 ^ N + 1)) ^ t = 2 ^ (t % (2 * N)) :=
    pow_eq_pow_mod t two_pow_two_mul_eq_one
  unfold mulPow2Split
  dsimp only
  by_cases h0 : t % (2 * N) = 0
  · rw [ite_eq_left h0]
    dsimp only
    rw [ht2, h0, pow_zero, mul_one]
    simp
  · rw [ite_eq_right h0]
    by_cases h : t % (2 * N) ≤ N
    · rw [dite_eq_left h]
      dsimp only
      rw [toZMod_mulPow2Le, ht2]
    · rw [dite_eq_right h]
      dsimp only
      rw [toZMod_mulPow2Le, ht2]
      simp only [Bool.false_eq_true, ↓reduceIte]
      have hsplit : (2 : ZMod (2 ^ N + 1)) ^ (t % (2 * N)) = -(2 ^ (t % (2 * N) - N)) := by
        rw [show t % (2 * N) = N + (t % (2 * N) - N) by omega, pow_add, two_pow_eq_neg_one,
          Nat.add_sub_cancel_left]
        ring
      rw [hsplit]
      ring

/-- **The butterfly**: `(b + 2^t c, b − 2^t c)`. -/
theorem toZMod_butterfly_fst [NeZero N] (t : Nat) (b c : AzFermat N) :
    toZMod (butterfly t b c).1 = toZMod b + toZMod c * 2 ^ t := by
  unfold butterfly
  dsimp only
  have h := toZMod_mulPow2Split t c
  split_ifs with hs
  · rw [toZMod_sub', h, ite_eq_left hs]
    ring
  · rw [toZMod_add', h, ite_eq_right hs]

theorem toZMod_butterfly_snd [NeZero N] (t : Nat) (b c : AzFermat N) :
    toZMod (butterfly t b c).2 = toZMod b - toZMod c * 2 ^ t := by
  unfold butterfly
  dsimp only
  have h := toZMod_mulPow2Split t c
  split_ifs with hs
  · rw [toZMod_add', h, ite_eq_left hs]
    ring
  · rw [toZMod_sub', h, ite_eq_right hs]

/-- `divPow2 t` divides by `2^t`. -/
theorem toZMod_divPow2_mul_two_pow [NeZero N] (t : Nat) (a : AzFermat N) :
    toZMod (divPow2 t a) * 2 ^ t = toZMod a := by
  rw [divPow2, toZMod_mulPow2, mul_assoc, ← pow_add]
  have hlt := Nat.mod_lt t (Nat.mul_pos two_pos (NeZero.pos N))
  have hmd := Nat.mod_add_div t (2 * N)
  rw [show 2 * N - t % (2 * N) + t = 2 * N + 2 * N * (t / (2 * N)) by omega, pow_add,
    two_pow_two_mul_eq_one, one_mul, pow_mul, two_pow_two_mul_eq_one, one_pow, mul_one]

end Azurite.AzFermat
