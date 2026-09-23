/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzNat.SubModPow2
import Azurite.AzNat.Equiv.Basic
import Azurite.AzNat.Equiv.Size
import Azurite.AzNat.Equiv.Compare
import Azurite.AzNat.Equiv.ModPow2
import Azurite.UInt64.Equiv.SubWithBorrow
import Mathlib.Tactic.LinearCombination
import Mathlib.Data.Nat.GCD.Basic

/-!
## Correctness of `AzNat.subModPow2`

`(subModPow2 a b k).toNat + b.toNat ≡ a.toNat [MOD 2 ^ k]`.
-/

namespace Azurite.AzNat

/-- Padded chunk: the value of limbs `[i, L)` of `arr`, reading `0` past the end.
    (Mirror of the local definition used for `addModPow2`.) -/
private def chunkPSub (arr : Array UInt64) (i L : Nat) : Nat :=
  if i < L then (arr[i]?.getD 0).toNat + chunkPSub arr (i + 1) L * 2 ^ 64 else 0
termination_by L - i

/-- `chunkPSub` reads the low `[i, L)` limbs, i.e. it is the value of the
    corresponding `take`/`drop` slice. -/
private lemma chunkPSub_eq_slice (arr : Array UInt64) (i L : Nat) :
    chunkPSub arr i L = toNatLimbsList ((arr.toList.drop i).take (L - i)) := by
  induction h_sub : L - i generalizing i with
  | zero =>
    have h_ge : L ≤ i := by omega
    rw [chunkPSub]; simp only [Nat.not_lt.mpr h_ge, ↓reduceIte]
    simp [List.take_zero, toNatLimbsList]
  | succ n ih =>
    have h_lt : i < L := by omega
    rw [chunkPSub]; simp only [h_lt, ↓reduceIte]
    rw [ih (i + 1) (by omega)]
    by_cases hi : i < arr.size
    · have hlt : i < arr.toList.length := by rwa [Array.length_toList]
      rw [List.drop_eq_getElem_cons hlt, List.take_succ_cons, toNatLimbsList_cons]
      rw [Array.getElem?_eq_getElem hi]
      rw [show arr.toList[i] = arr[i] from (Array.getElem_toList hi).symm]
      simp only [Option.getD_some]
      ring
    · rw [Array.getElem?_eq_none (by omega)]
      have hd : arr.toList.drop i = [] := by
        rw [List.drop_eq_nil_iff]; rw [Array.length_toList]; omega
      have hd1 : arr.toList.drop (i + 1) = [] := by
        rw [List.drop_eq_nil_iff]; rw [Array.length_toList]; omega
      simp [hd, hd1, toNatLimbsList]

/-- `chunkPSub arr 0 L` truncates `arr` to its low `L` limbs, i.e. `arr.toNat`
    reduced mod `2 ^ (64 * L)`. -/
private lemma chunkPSub_zero (arr : Array UInt64) (L : Nat) :
    chunkPSub arr 0 L = toNatLimbsList arr.toList % 2 ^ (64 * L) := by
  rw [chunkPSub_eq_slice, Nat.sub_zero, List.drop_zero]
  by_cases hL : L ≤ arr.toList.length
  · have h_td := toNatLimbsList_take_drop arr.toList L hL
    have h_lt : toNatLimbsList (arr.toList.take L) < 2 ^ (64 * L) := by
      have := toNatLimbsList_lt_pow (arr.toList.take L)
      rwa [List.length_take, Nat.min_eq_left hL] at this
    rw [h_td, Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt h_lt]
  · rw [List.take_of_length_le (by omega)]
    rw [Nat.mod_eq_of_lt]
    have := toNatLimbsList_lt_pow arr.toList
    calc toNatLimbsList arr.toList < 2 ^ (64 * arr.toList.length) := this
      _ ≤ 2 ^ (64 * L) := Nat.pow_le_pow_right (by decide) (by omega)

/-- The number of limbs produced by `lowDiffLimbs`: one per iteration. -/
private lemma lowDiffLimbs_size (a b : Array UInt64) (L i : Nat) (borrow : Bool)
    (acc : Array UInt64) :
    (lowDiffLimbs a b L i borrow acc).size = acc.size + (L - i) := by
  induction h_sub : L - i generalizing i borrow acc with
  | zero =>
    have h_ge : L ≤ i := by omega
    rw [lowDiffLimbs]; simp [Nat.not_lt.mpr h_ge]
  | succ n ih =>
    have h_lt : i < L := by omega
    rw [lowDiffLimbs]
    simp only [h_lt, ↓reduceIte]
    rw [ih (i + 1) _ _ (by omega)]
    rw [Array.size_push]
    omega

/-- The go-loop invariant for `lowDiffLimbs`.  `acc` already holds the low limbs;
    the remaining limbs `[i, L)` of `a` and `b` plus the incoming borrow produce
    the rest.  Stated as the borrow-conservation identity: there is a final
    borrow-out `c` with
    `result + (b over [i,L)) + borrowIn = acc + (a over [i,L)) + c·2^(top)`
    (all scaled by `2^(64·acc.size)`). -/
private lemma lowDiffLimbs_correct (a b : Array UInt64) (L i : Nat) (borrow : Bool)
    (acc : Array UInt64) :
    ∃ c : Bool,
      toNatLimbsList (lowDiffLimbs a b L i borrow acc).toList
          + chunkPSub b i L * 2 ^ (64 * acc.size)
          + borrow.toNat * 2 ^ (64 * acc.size)
        = toNatLimbsList acc.toList
          + chunkPSub a i L * 2 ^ (64 * acc.size)
          + c.toNat * 2 ^ (64 * (acc.size + (L - i))) := by
  induction h_sub : L - i generalizing i borrow acc with
  | zero =>
    have h_ge : L ≤ i := by omega
    rw [lowDiffLimbs]; simp only [Nat.not_lt.mpr h_ge, ↓reduceIte]
    have hCA : chunkPSub a i L = 0 := by rw [chunkPSub]; simp [Nat.not_lt.mpr h_ge]
    have hCB : chunkPSub b i L = 0 := by rw [chunkPSub]; simp [Nat.not_lt.mpr h_ge]
    refine ⟨borrow, ?_⟩
    rw [hCA, hCB]
    simp only [Nat.add_zero, Nat.zero_mul]
  | succ n ih =>
    have h_lt : i < L := by omega
    rw [lowDiffLimbs]
    simp only [h_lt, ↓reduceIte, Array.getD_eq_getD_getElem?]
    set swb := UInt64.subWithBorrow (a[i]?.getD 0) (b[i]?.getD 0) borrow with hswb
    have h_rec : L - (i + 1) = n := by omega
    obtain ⟨c, hc⟩ := ih (i + 1) swb.2 (acc.push swb.1) h_rec
    refine ⟨c, ?_⟩
    -- The per-limb subtract equation.
    have h_swb := UInt64.subWithBorrow_eq (a[i]?.getD 0) (b[i]?.getD 0) borrow
    rw [← hswb] at h_swb
    -- Expand chunkPSub at i.
    have hCA : chunkPSub a i L = (a[i]?.getD 0).toNat + chunkPSub a (i + 1) L * 2 ^ 64 := by
      rw [chunkPSub]; simp only [h_lt, ↓reduceIte]
    have hCB : chunkPSub b i L = (b[i]?.getD 0).toNat + chunkPSub b (i + 1) L * 2 ^ 64 := by
      rw [chunkPSub]; simp only [h_lt, ↓reduceIte]
    rw [hCA, hCB]
    -- acc.push: toNatLimbsList and size in the hypothesis `hc`.
    rw [show (acc.push swb.1).toList = acc.toList ++ [swb.1] from Array.toList_push] at hc
    rw [toNatLimbsList_append_singleton, Array.length_toList, Array.size_push] at hc
    rw [show acc.size + 1 + n = acc.size + (n + 1) from by omega] at hc
    -- Align the top modulus.
    rw [show acc.size + (n + 1) = acc.size + (L - i) from by omega] at hc
    -- Powers.
    have h_pow : (2 : Nat) ^ (64 * (acc.size + 1)) = 2 ^ (64 * acc.size) * 2 ^ 64 := by
      rw [show 64 * (acc.size + 1) = 64 * acc.size + 64 from by ring, Nat.pow_add]
    rw [h_pow] at hc
    set M := (2 : Nat) ^ (64 * (acc.size + (L - i))) with hM
    set P := (2 : Nat) ^ (64 * acc.size) with hP
    set aR := (a[i]?.getD 0).toNat with haR
    set bR := (b[i]?.getD 0).toNat with hbR
    set CA := chunkPSub a (i + 1) L with hCAd
    set CB := chunkPSub b (i + 1) L with hCBd
    set Res := toNatLimbsList (lowDiffLimbs a b L (i + 1) swb.2 (acc.push swb.1)).toList with hRes
    set ACC := toNatLimbsList acc.toList with hACC
    have h_bT : (if borrow then 1 else 0) = borrow.toNat := by cases borrow <;> simp
    have h_nT : (if swb.2 then 1 else 0) = swb.2.toNat := by cases swb.2 <;> simp
    rw [h_bT, h_nT] at h_swb
    -- key per-limb conservation: result-limb + bR + borrow = aR + newBorrow·2^64
    have key : swb.1.toNat + bR + borrow.toNat = aR + swb.2.toNat * 2 ^ 64 := h_swb
    -- hc currently:
    --   Res + (CB * 2^64) * P + c.toNat * M = (ACC + swb.1.toNat * P) + (swb.2.toNat + CB) * (P * 2^64)
    -- wait: hc top has chunkPSub b (i+1) L * P ; the pushed limb sits at position acc.size.
    -- Goal: Res + (bR + CB*2^64)*P + c.toNat*M = ACC + (borrow.toNat + (aR + CA*2^64))*P
    -- Use hc and key.  Reduce both to a Nat identity via linear_combination.
    rw [show acc.size + (n + 1) = acc.size + (L - i) from by omega, ← hM]
    linear_combination hc + (P : ℕ) * key

/-- **Spec of `subModPow2` as a congruence.** Adding `b` back recovers `a`
    modulo `2 ^ k`. -/
theorem subModPow2_modEq (a b : AzNat) (k : Nat) :
    (AzNat.subModPow2 a b k).toNat + b.toNat ≡ a.toNat [MOD 2 ^ k] := by
  set L := (k + 63) / 64 with hL
  set r := lowDiffLimbs a.limbs b.limbs L 0 false (Array.emptyWithCapacity L) with hr
  obtain ⟨c, hinv⟩ := lowDiffLimbs_correct a.limbs b.limbs L 0 false (Array.emptyWithCapacity L)
  rw [← hr] at hinv
  have h_empty : toNatLimbsList (Array.emptyWithCapacity L : Array UInt64).toList = 0 := by
    rw [Array.emptyWithCapacity_eq]; simp [toNatLimbsList]
  have h_size0 : (Array.emptyWithCapacity L : Array UInt64).size = 0 := by
    rw [Array.emptyWithCapacity_eq]; exact Array.size_empty
  rw [h_empty, h_size0, Nat.sub_zero, Nat.zero_add] at hinv
  simp only [Nat.mul_zero, Nat.pow_zero, Nat.mul_one] at hinv
  rw [show (false : Bool).toNat = 0 from rfl, Nat.add_zero] at hinv
  rw [show (0 + L) = L from Nat.zero_add L] at hinv
  -- chunkPSub at 0 = truncations.
  rw [chunkPSub_zero a.limbs L, chunkPSub_zero b.limbs L] at hinv
  -- hinv : r.toNat-ish + (b.toNat % 2^(64L)) + c.toNat * 2^(64L) = (a.toNat % 2^(64L))
  set RN := toNatLimbsList r.toList with hRN
  set A := toNatLimbsList a.limbs.toList with hA
  set B := toNatLimbsList b.limbs.toList with hB
  -- `(subModPow2 a b k).toNat = RN % 2^k`.
  have hsub : (subModPow2 a b k).toNat = RN % 2 ^ k := by
    show (modPow2 (ofLimbs r) k).toNat = RN % 2 ^ k
    rw [toNat_modPow2, toNat_ofLimbs]
  rw [hsub]
  -- Set up divisibility: 2^k ∣ 2^(64L).
  have hkL : k ≤ 64 * L := by rw [hL]; omega
  have hdvd : (2 : Nat) ^ k ∣ 2 ^ (64 * L) := Nat.pow_dvd_pow 2 hkL
  have hAtoNat : A = a.toNat := rfl
  have hBtoNat : B = b.toNat := rfl
  -- hinv : RN + B % M = A % M + c.toNat * M, with M := 2^(64L).
  set M := (2 : Nat) ^ (64 * L) with hM
  -- All four reductions mod 2^k, since 2^k ∣ M.
  -- `x % M ≡ x [MOD 2^k]`  via  `Nat.mod_mod_of_dvd`.
  have hredB : B % M % 2 ^ k = B % 2 ^ k := Nat.mod_mod_of_dvd B hdvd
  have hredA : A % M % 2 ^ k = A % 2 ^ k := Nat.mod_mod_of_dvd A hdvd
  -- `c.toNat * M ≡ 0 [MOD 2^k]`.
  have hcM : c.toNat * M % 2 ^ k = 0 := by
    obtain ⟨t, ht⟩ := hdvd
    rw [ht]; rw [show c.toNat * (2 ^ k * t) = (c.toNat * t) * 2 ^ k from by ring]
    exact Nat.mul_mod_left _ _
  -- From `hinv`, take `% 2^k` of both sides and simplify.
  have key : (RN + B) % 2 ^ k = A % 2 ^ k := by
    have h : (RN + B % M) % 2 ^ k = (A % M + c.toNat * M) % 2 ^ k := by rw [hinv]
    -- h : (RN + B % M) % 2^k = (A % M + c.toNat * M) % 2^k
    -- LHS: (RN + B % M) % 2^k = (RN + B) % 2^k
    rw [Nat.add_mod RN (B % M), hredB, ← Nat.add_mod] at h
    -- RHS: (A % M + c.toNat * M) % 2^k = A % 2^k
    rw [Nat.add_mod (A % M) (c.toNat * M), hcM, Nat.add_zero, Nat.mod_mod, hredA] at h
    exact h
  -- Goal: RN % 2^k + B ≡ A [MOD 2^k].  Note B = b.toNat, A = a.toNat.
  show RN % 2 ^ k + b.toNat ≡ a.toNat [MOD 2 ^ k]
  rw [← hBtoNat, ← hAtoNat]
  -- `RN % 2^k + B ≡ RN + B ≡ A [MOD 2^k]`.
  have h1 : RN % 2 ^ k + B ≡ RN + B [MOD 2 ^ k] :=
    Nat.ModEq.add_right B (Nat.mod_modEq RN (2 ^ k))
  exact h1.trans key

end Azurite.AzNat
