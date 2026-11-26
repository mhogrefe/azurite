/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.ECPP.Check
import Azurite.ECPP.Equiv.Curve
import Azurite.ECPP.Theory.Soundness
import Azurite.AzNat.Equiv.IsPrimeAprcl
import Azurite.AzNat.Equiv.Gcd
import Azurite.AzNat.Equiv.SqrtRem
import Azurite.AzNat.Equiv.Sub
import Azurite.AzNat.Equiv.Compare

/-!
# Soundness of the checker of elliptic curve primality certificates

**`check_prime`**: `check n cert = true → Nat.Prime n.toNat`.

`checkStep_sound`: a step that passes gives `EcppStep n.toNat q.toNat`
(`ecppStep_of_ladder`, through `jacMul_map`); `check_sound`: a certificate that passes
gives an `EcppProof`, which proves primality by the criterion of Goldwasser and Kilian and
the Hasse bound (`EcppProof.isPrime`, `Theory/Soundness.lean`).
-/

namespace Azurite.ECPP

open AzZMod

/-- A residue whose canonical representative is coprime to `n` is a unit. -/
theorem isUnit_toZMod_of_gcd {n : AzNat} [NeZero n.toNat] {x : AzZMod n}
    (h : AzNat.gcd x.val n = AzNat.ofNat 1) : IsUnit (toZMod x) := by
  have hc : Nat.gcd x.val.toNat n.toNat = 1 := by
    rw [← AzNat.toNat_gcd, h, AzNat.toNat_ofNat]
  exact (ZMod.isUnit_iff_coprime _ _).mpr hc

/-- **A step that passes the check is a step of a proof.** -/
theorem checkStep_sound {n : AzNat} {c : StepCert} (h : checkStep n c = true) :
    EcppStep n.toNat c.q.toNat := by
  unfold checkStep at h
  split at h
  · next hn =>
    have : NeZero n.toNat := ⟨by omega⟩
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨⟨⟨h6, hs1⟩, hs2⟩, hd⟩, hE⟩, hm⟩ := h
    split at hm
    · exact absurd hm (by simp)
    · next V hl =>
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hm
      obtain ⟨⟨hu, hx⟩, hy⟩ := hm
      -- the conditions on the sizes
      have h6' : Nat.Coprime n.toNat 6 := by
        have := congrArg AzNat.toNat h6
        rwa [AzNat.toNat_gcd, AzNat.toNat_ofNat, AzNat.toNat_ofNat] at this
      have hs1' : Nat.sqrt n.toNat + 1 < c.q.toNat := by
        have := (AzNat.lt_iff_toNat_lt _ _).mp hs1
        rwa [AzNat.toNat_add, AzNat.toNat_sqrt, AzNat.toNat_ofNat] at this
      have hs2' : 4 * Nat.sqrt n.toNat < (c.q.toNat - Nat.sqrt n.toNat - 1) ^ 2 := by
        have := (AzNat.lt_iff_toNat_lt _ _).mp hs2
        rw [AzNat.toNat_mul, AzNat.toNat_mul, AzNat.toNat_sub, AzNat.toNat_sub,
          AzNat.toNat_sqrt, AzNat.toNat_ofNat, AzNat.toNat_ofNat] at this
        rwa [pow_two]
      -- the curve and the point
      have hdisc : IsUnit (4 * toZMod (ofAzNat n c.a) ^ 3 + 27 * toZMod (ofAzNat n c.b) ^ 2) := by
        have := isUnit_toZMod_of_gcd hd
        simp only [toZMod_add, toZMod_mul, toZMod_square] at this
        convert this using 1
        ring
      have hE' : toZMod (ofAzNat n c.v) ^ 2 = toZMod (ofAzNat n c.u) ^ 3
          + toZMod (ofAzNat n c.a) * toZMod (ofAzNat n c.u) + toZMod (ofAzNat n c.b) := by
        have := congrArg toZMod hE
        simp only [toZMod_add, toZMod_mul, toZMod_square] at this
        linear_combination this
      -- the ladder
      have hl' := jacMul_map (ofAzNat n c.a) (ofAzNat n c.u) (ofAzNat n c.v)
        (c.q.size + 1) (c.q - AzNat.ofNat 1)
      rw [hl, Option.map_some, AzNat.toNat_sub, AzNat.toNat_ofNat] at hl'
      have hunit : IsUnit (mapPt V).2.2 := isUnit_toZMod_of_gcd hu
      have hx' : (mapPt V).1 = toZMod (ofAzNat n c.u) * (mapPt V).2.2 ^ 2 := by
        have := congrArg toZMod hx
        simp only [toZMod_mul, toZMod_square] at this
        show toZMod V.1 = _ * toZMod V.2.2 ^ 2
        rw [this]
        ring
      have hy' : (mapPt V).2.1 = -toZMod (ofAzNat n c.v) * (mapPt V).2.2 ^ 3 := by
        have := congrArg toZMod hy
        simp only [toZMod_mul, toZMod_square, toZMod_neg] at this
        show toZMod V.2.1 = -_ * toZMod V.2.2 ^ 3
        rw [this]
        ring
      exact ecppStep_of_ladder hn h6' hs1' hs2' hdisc hE' hl'.symm hunit hx' hy'
  · exact absurd h (by simp)

/-- **A certificate that passes the check is a proof by elliptic curves.** -/
theorem check_sound : ∀ (cs : List StepCert) (n : AzNat), check n cs = true →
    EcppProof n.toNat
  | [], n, h => EcppProof.base ((AzNat.isPrimeAprcl_eq_true_iff n).mp h)
  | c :: cs, n, h => by
    rw [check, Bool.and_eq_true] at h
    exact EcppProof.step (checkStep_sound h.1) (check_sound cs c.q h.2)

/-- **Soundness of the checker**: a number with a certificate that passes is prime. -/
theorem check_prime {n : AzNat} {cs : List StepCert} (h : check n cs = true) :
    Nat.Prime n.toNat :=
  (check_sound cs n h).isPrime

end Azurite.ECPP
