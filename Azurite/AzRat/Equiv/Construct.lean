/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzRat.Construct
import Azurite.AzRat.Equiv.Basic
import Azurite.AzInt.Equiv.Basic
import Azurite.AzNat.Equiv.Div.DivMod
import Mathlib.Data.Rat.Lemmas
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Tactic.Ring

/-!
# Correctness of the `AzRat` pair constructors

`toRat_ofAzNats` and `toRat_ofAzInts`: the pair constructors compute exactly the field
division of the converted operands, `toRat (ofAzNats n d) = n.toNat / d.toNat` and
`toRat (ofAzInts n d) = n.toInt / d.toInt` in `ℚ`. The statements need no nonzero
hypotheses: the constructors map a zero denominator to `0` (the `mkRat` convention),
matching field division's `x / 0 = 0`.

Both reduce to `toRat_ofSignAzNats` for the shared sign-aware core, whose proof rewrites
`Rat.mk'` to field division (`Rat.mk_eq_divInt`, `Rat.divInt_eq_div`) and cancels the
gcd with `Rat.natCast_div` and `div_div_div_cancel_right₀`.
-/

namespace Azurite.AzRat

@[simp] theorem toRat_zero : toRat (0 : AzRat) = 0 := rfl

@[simp] theorem toRat_one : toRat (1 : AzRat) = 1 := rfl

@[simp] theorem default_eq_zero : (default : AzRat) = 0 := rfl

@[simp] theorem ofRat_zero : ofRat 0 = 0 :=
  toRat_injective (by rw [toRat_ofRat, toRat_zero])

@[simp] theorem ofRat_one : ofRat 1 = 1 :=
  toRat_injective (by rw [toRat_ofRat, toRat_one])

theorem toRat_ofSignAzNats (s : Bool) (n d : AzNat) :
    toRat (ofSignAzNats s n d) =
      (if s then 1 else -1) * ((n.toNat : ℚ) / (d.toNat : ℚ)) := by
  by_cases hd : d = 0
  · simp [ofSignAzNats, hd]
  · by_cases hn : n = 0
    · simp [ofSignAzNats, hd, hn]
    · -- general case: reduced fraction
      have hd' : d.toNat ≠ 0 :=
        fun h => hd (AzNat.toNat_injective (h.trans AzNat.toNat_zero.symm))
      have hg : 0 < Nat.gcd n.toNat d.toNat :=
        Nat.gcd_pos_of_pos_right _ (Nat.pos_of_ne_zero hd')
      have hgQ : (Nat.gcd n.toNat d.toNat : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hg)
      rw [ofSignAzNats, dite_eq_right hd, dite_eq_right hn]
      rw [toRat, Rat.mk_eq_divInt, Rat.divInt_eq_div]
      simp only [AzNat.toNat_div, AzNat.toNat_gcd]
      cases s with
      | true =>
        rw [ite_eq_left rfl, ite_eq_left rfl]
        simp only [Int.cast_natCast]
        rw [Rat.natCast_div _ _ (Nat.gcd_dvd_left _ _),
            Rat.natCast_div _ _ (Nat.gcd_dvd_right _ _),
            div_div_div_cancel_right₀ hgQ, one_mul]
      | false =>
        rw [ite_eq_right Bool.false_ne_true, ite_eq_right Bool.false_ne_true]
        simp only [Int.cast_neg, Int.cast_natCast]
        rw [Rat.natCast_div _ _ (Nat.gcd_dvd_left _ _),
            Rat.natCast_div _ _ (Nat.gcd_dvd_right _ _),
            neg_div, div_div_div_cancel_right₀ hgQ, neg_one_mul]

theorem toRat_ofAzNats (n d : AzNat) :
    toRat (ofAzNats n d) = (n.toNat : ℚ) / (d.toNat : ℚ) := by
  rw [ofAzNats, toRat_ofSignAzNats]
  simp

/-- `ofSignAzNats` is the identity on an already-canonical triple: rebuilding an
`AzRat` from its own `sign`/`num`/`den` fields gives back the same `AzRat`.
(The fields are reduced and zero-canonical by the `AzRat` invariants, so the
gcd is `1` and the zero branch agrees.) Used by the parse round-trip. -/
theorem ofSignAzNats_self (q : AzRat) : ofSignAzNats q.sign q.num q.den = q := by
  have hcop : Nat.Coprime q.num.toNat q.den.toNat := (AzNat.coprime_iff _ _).mp q.reduced
  rw [ofSignAzNats, dite_eq_right q.den_nz]
  by_cases hn : q.num = 0
  · rw [dite_eq_left hn]
    -- `q` is the canonical zero: `num = 0` forces `sign = true` and (by
    -- coprimality) `den = 1`.
    have hsign : q.sign = true := q.zero_sign hn
    have hden : q.den = 1 := by
      apply AzNat.toNat_injective
      rw [AzNat.toNat_one]
      have h0 : q.num.toNat = 0 := by rw [hn, AzNat.toNat_zero]
      rw [h0] at hcop
      exact Nat.coprime_zero_left _ |>.mp hcop
    exact AzRat.ext hsign.symm hn.symm hden.symm
  · rw [dite_eq_right hn]
    have hg1 : Nat.gcd q.num.toNat q.den.toNat = 1 := hcop
    refine AzRat.ext rfl ?_ ?_
    · apply AzNat.toNat_injective
      rw [AzNat.toNat_div, AzNat.toNat_gcd, hg1, Nat.div_one]
    · apply AzNat.toNat_injective
      rw [AzNat.toNat_div, AzNat.toNat_gcd, hg1, Nat.div_one]

theorem toRat_ofAzInts (n d : AzInt) :
    toRat (ofAzInts n d) = (n.toInt : ℚ) / (d.toInt : ℚ) := by
  rw [ofAzInts, toRat_ofSignAzNats]
  cases hn : n.sign <;> cases hd : d.sign <;>
    simp [AzInt.toInt, hn, hd, neg_div, div_neg, neg_neg]

end Azurite.AzRat
