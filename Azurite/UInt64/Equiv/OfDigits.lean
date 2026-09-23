/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.UInt64.Equiv.Digits
import Azurite.UInt64.OfDigits
import Mathlib.Data.Nat.Digits.Lemmas

namespace UInt64

/-- Key recurrence for the generic Horner reconstruction over a list. -/
private lemma horner_eq (b : UInt64) :
    ∀ (L : List UInt64),
    (L.foldr (fun d acc => acc * b + d) 0).toNat
      = Nat.ofDigits b.toNat (L.map UInt64.toNat) % 2 ^ 64 := by
  intro L
  induction L with
  | nil =>
    show (0 : UInt64).toNat = Nat.ofDigits b.toNat [] % 2 ^ 64
    rfl
  | cons a as ih =>
    show ((List.foldr (fun d acc => acc * b + d) 0 as) * b + a).toNat
        = Nat.ofDigits b.toNat (a.toNat :: as.map UInt64.toNat) % 2 ^ 64
    set acc := List.foldr (fun d acc => acc * b + d) 0 as with hacc
    rw [UInt64.toNat_add, UInt64.toNat_mul]
    show (acc.toNat * b.toNat % 2 ^ 64 + a.toNat) % 2 ^ 64
        = (a.toNat + b.toNat * Nat.ofDigits b.toNat (as.map UInt64.toNat)) % 2 ^ 64
    rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
    rw [ih]
    conv_lhs => rw [Nat.add_mod, Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, ← Nat.add_mod]
    ring_nf

/-- Key recurrence for the power-of-2 Horner reconstruction over a list. -/
private lemma horner_pow2_eq (k : Nat) (hk : k < 64) :
    ∀ (L : List UInt64),
    (L.foldr (fun d acc => (acc <<< UInt64.ofNat k) + d) 0).toNat
      = Nat.ofDigits (2 ^ k) (L.map UInt64.toNat) % 2 ^ 64 := by
  intro L
  induction L with
  | nil =>
    show (0 : UInt64).toNat = Nat.ofDigits (2 ^ k) [] % 2 ^ 64
    rfl
  | cons a as ih =>
    show ((List.foldr (fun d acc => (acc <<< UInt64.ofNat k) + d) 0 as) <<<
            UInt64.ofNat k + a).toNat
        = Nat.ofDigits (2 ^ k) (a.toNat :: as.map UInt64.toNat) % 2 ^ 64
    set acc := List.foldr (fun d acc => (acc <<< UInt64.ofNat k) + d) 0 as with hacc
    rw [UInt64.toNat_add, UInt64.toNat_shiftLeft]
    have h_shift : (UInt64.ofNat k).toNat % 64 = k := by
      have h_eq : (UInt64.ofNat k).toNat = k := Nat.mod_eq_of_lt (by omega)
      rw [h_eq, Nat.mod_eq_of_lt hk]
    rw [h_shift, Nat.shiftLeft_eq]
    show (acc.toNat * 2 ^ k % 2 ^ 64 + a.toNat) % 2 ^ 64
        = (a.toNat + 2 ^ k * Nat.ofDigits (2 ^ k) (as.map UInt64.toNat)) % 2 ^ 64
    rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
    rw [ih]
    conv_lhs => rw [Nat.add_mod, Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, ← Nat.add_mod]
    ring_nf

/-- **Correctness of `ofDigitsGeneric`.** Modular Horner-fold reconstruction. -/
theorem ofDigitsGeneric_eq (b : UInt64) (ds : Array UInt64) :
    (ofDigitsGeneric b ds).toNat
      = Nat.ofDigits b.toNat (ds.toList.map UInt64.toNat) % 2 ^ 64 := by
  unfold ofDigitsGeneric
  rw [← Array.foldr_toList]
  exact horner_eq b ds.toList

/-- **Correctness of `ofDigitsPow2`.** Modular shift-Horner reconstruction
    for power-of-2 bases. Requires `k < 64`. -/
theorem ofDigitsPow2_eq (k : Nat) (hk : k < 64) (ds : Array UInt64) :
    (ofDigitsPow2 k ds).toNat
      = Nat.ofDigits (2 ^ k) (ds.toList.map UInt64.toNat) % 2 ^ 64 := by
  unfold ofDigitsPow2
  rw [← Array.foldr_toList]
  exact horner_pow2_eq k hk ds.toList

/-- **Correctness of `ofDigits`.** The function inverts `digits` modulo
    `2^64`: applying `ofDigits b` to any digit array recovers the value
    `Nat.ofDigits` would compute, taken modulo the `UInt64` range. -/
theorem ofDigits_eq (b : UInt64) (ds : Array UInt64) :
    (ofDigits b ds).toNat
      = Nat.ofDigits b.toNat (ds.toList.map UInt64.toNat) % 2 ^ 64 := by
  unfold ofDigits
  by_cases hpow : b.isPowerOfTwo
  · rw [ite_eq_left hpow]
    have h_b_ne : b ≠ 0 := by
      intro he
      unfold UInt64.isPowerOfTwo at hpow
      rw [he] at hpow; simp at hpow
    have h_bv_ne : b.toBitVec ≠ 0#64 := fun hb =>
      h_b_ne (UInt64.eq_of_toBitVec_eq hb)
    have h_ctz_lt : b.toBitVec.ctz.toNat < 64 := by
      have h := BitVec.ctz_lt_iff_ne_zero.mpr h_bv_ne
      rw [BitVec.lt_def] at h
      have h64 : ((↑(64 : Nat) : BitVec 64)).toNat = 64 := by decide
      omega
    have h_b_eq : b.toNat = 2 ^ b.toBitVec.ctz.toNat := toNat_eq_two_pow_ctz b hpow
    rw [ofDigitsPow2_eq _ h_ctz_lt, h_b_eq]
  · rw [ite_eq_right hpow]
    exact ofDigitsGeneric_eq b ds

/-- **Round-trip.** For `b.toNat ≥ 2`, `ofDigits b (digits b u) = u`.
    The wrap-mod is automatic since `Nat.ofDigits b (Nat.digits b u) = u < 2^64`. -/
theorem ofDigits_digits (b u : UInt64) (hb : 2 ≤ b.toNat) :
    ofDigits b (digits b u) = u := by
  apply UInt64.toNat.inj
  rw [ofDigits_eq, digits_eq b u hb, Nat.ofDigits_digits]
  exact Nat.mod_eq_of_lt (UInt64.toNat_lt u)

end UInt64
