/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzNat.Kronecker
import Azurite.AzNat.Equiv.Mul.ToomCook3
import Azurite.AzNat.Equiv.ShiftRight
import Azurite.AzNat.Equiv.ModPow2
import Azurite.AzNat.Equiv.Mul.Dispatch
import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Coeff

/-!
# Kronecker packing: the values

* `Nat.ofDigits_div_pow_mod`: a digit of `Nat.ofDigits B L` when all the entries are below
  `B`.
* `kroneckerPack_toNat`: `(kroneckerPack w a).toNat = Nat.ofDigits (2^(64 w)) (a.map toNat)`
  for coefficients below `2^(64 w)`.
* `kroneckerCoeff_toNat`: `(kroneckerCoeff w x k).toNat = x / 2^(64 w k) % 2^(64 w)`.
-/

/-- The `k`-th digit of `Nat.ofDigits B L`, when every entry is below `B`. -/
theorem Nat.ofDigits_div_pow_mod (B : ℕ) (L : List ℕ) (hL : ∀ x ∈ L, x < B) (k : ℕ) :
    Nat.ofDigits B L / B ^ k % B = L.getD k 0 := by
  induction L generalizing k with
  | nil => simp
  | cons c L ih =>
    have hc := hL c (by simp)
    have hB : 0 < B := by omega
    rw [Nat.ofDigits_cons]
    cases k with
    | zero => simp [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hc]
    | succ k =>
      rw [pow_succ', ← Nat.div_div_eq_div_mul, Nat.add_mul_div_left _ _ hB,
        Nat.div_eq_of_lt hc, zero_add]
      simpa using ih (fun x hx => hL x (by simp [hx])) k

namespace Azurite.AzNat

theorem toNatLimbsList_foldl_pack (w : Nat) (L : List AzNat)
    (hL : ∀ c ∈ L, c.toNat < 2 ^ (64 * w)) (out : Array UInt64) :
    toNatLimbsList (L.foldl (fun out c => out ++ truncatePad c.limbs w) out).toList =
      toNatLimbsList out.toList +
        2 ^ (64 * out.size) * Nat.ofDigits (2 ^ (64 * w)) (L.map toNat) := by
  induction L generalizing out with
  | nil => simp
  | cons c L ih =>
    have hc : toNatLimbsList c.limbs.toList < 2 ^ (64 * w) := hL c (by simp)
    rw [List.foldl_cons, ih (fun x hx => hL x (by simp [hx])), Array.toList_append,
      toNatLimbsList_append, truncatePad_toNat _ _ hc, Array.size_append, truncatePad_size,
      List.map_cons, Nat.ofDigits_cons, Array.length_toList]
    show toNatLimbsList c.limbs.toList * 2 ^ (64 * out.size) + _ + _ =
      _ + 2 ^ (64 * out.size) * (toNatLimbsList c.limbs.toList + _)
    rw [Nat.mul_add 64, pow_add]
    ring

/-- The value of a packed array of coefficients below `2^(64 w)`. -/
theorem kroneckerPack_toNat (w : Nat) (a : Array AzNat)
    (ha : ∀ c ∈ a, c.toNat < 2 ^ (64 * w)) :
    (kroneckerPack w a).toNat = Nat.ofDigits (2 ^ (64 * w)) (a.toList.map toNat) := by
  unfold kroneckerPack kroneckerLimbs
  rw [toNat_ofLimbs, ← Array.foldl_toList,
    toNatLimbsList_foldl_pack w a.toList (fun c hc => ha c (by simpa using hc))]
  simp [toNatLimbsList]

/-- The value of a block of `w` limbs. -/
theorem kroneckerCoeff_toNat (w : Nat) (x : AzNat) (k : Nat) :
    (kroneckerCoeff w x k).toNat = x.toNat / 2 ^ (64 * (k * w)) % 2 ^ (64 * w) := by
  unfold kroneckerCoeff
  rw [toNat_ofLimbs, Array.toList_extract]
  show toNatLimbsList ((x.limbs.toList.drop (k * w)).take (k * w + w - k * w)) = _
  rw [Nat.add_sub_cancel_left, toNatLimbsList_take, toNatLimbsList_drop]
  rfl

/-! ### Products through polynomials over `ℕ` -/

open Polynomial

/-- The polynomial over `ℕ` with the given coefficients. -/
noncomputable def natPoly : List ℕ → ℕ[X]
  | [] => 0
  | c :: L => Polynomial.C c + Polynomial.X * natPoly L

theorem natPoly_eval (B : ℕ) (L : List ℕ) : (natPoly L).eval B = Nat.ofDigits B L := by
  induction L with
  | nil => simp [natPoly]
  | cons c L ih => simp [natPoly, ih, Nat.ofDigits_cons]

theorem natPoly_coeff (L : List ℕ) (k : ℕ) : (natPoly L).coeff k = L.getD k 0 := by
  induction L generalizing k with
  | nil => simp [natPoly]
  | cons c L ih =>
    cases k with
    | zero => simp [natPoly]
    | succ k => simp [natPoly, ih]

/-- The digits of the value at `B` of a polynomial over `ℕ` with coefficients below `B`. -/
theorem eval_div_pow_mod (R : ℕ[X]) (B N : ℕ) (hdeg : ∀ i, N ≤ i → R.coeff i = 0)
    (hB : ∀ i, i < N → R.coeff i < B) (k : ℕ) :
    R.eval B / B ^ k % B = R.coeff k := by
  have hR : R = natPoly ((List.range N).map R.coeff) := by
    ext i
    rw [natPoly_coeff]
    by_cases hi : i < N
    · simp [List.getD, hi]
    · simp [List.getD, hi, hdeg i (by omega)]
  have hdig := Nat.ofDigits_div_pow_mod B ((List.range N).map R.coeff)
    (by
      intro x hx
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
      exact hB i (List.mem_range.mp hi)) k
  rw [← natPoly_eval, ← hR] at hdig
  rw [hdig]
  by_cases hk : k < N
  · simp [List.getD, hk]
  · simp [List.getD, hk, hdeg k (by omega)]

theorem natPoly_mul_coeff (L₁ L₂ : List ℕ) (k : ℕ) :
    (natPoly L₁ * natPoly L₂).coeff k =
      ∑ i ∈ Finset.range (k + 1), L₁.getD i 0 * L₂.getD (k - i) 0 := by
  rw [Polynomial.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i j => (natPoly L₁).coeff i * (natPoly L₂).coeff j)]
  simp only [natPoly_coeff]

theorem natPoly_mul_coeff_eq_zero (L₁ L₂ : List ℕ) (k : ℕ)
    (hk : L₁.length + L₂.length - 1 ≤ k) : (natPoly L₁ * natPoly L₂).coeff k = 0 := by
  rw [natPoly_mul_coeff]
  apply Finset.sum_eq_zero
  intro i hi
  rw [Finset.mem_range] at hi
  by_cases h1 : L₁.length ≤ i
  · rw [List.getD_eq_default _ _ h1, Nat.zero_mul]
  · rw [List.getD_eq_default L₂ _ (by omega), Nat.mul_zero]

theorem getD_le_of_forall_le (L : List ℕ) (M : ℕ) (hL : ∀ x ∈ L, x ≤ M) (i : ℕ) :
    L.getD i 0 ≤ M := by
  by_cases h : i < L.length
  · rw [List.getD_eq_getElem _ _ h]
    exact hL _ (List.getElem_mem h)
  · rw [List.getD_eq_default _ _ (by omega)]
    exact Nat.zero_le _

theorem natPoly_mul_coeff_le (L₁ L₂ : List ℕ) (M₁ M₂ : ℕ) (h₁ : ∀ x ∈ L₁, x ≤ M₁)
    (h₂ : ∀ x ∈ L₂, x ≤ M₂) (k : ℕ) :
    (natPoly L₁ * natPoly L₂).coeff k ≤ (k + 1) * (M₁ * M₂) := by
  rw [natPoly_mul_coeff]
  have h := Finset.sum_le_card_nsmul (Finset.range (k + 1))
    (fun i => L₁.getD i 0 * L₂.getD (k - i) 0) (M₁ * M₂) fun i _ =>
      Nat.mul_le_mul (getD_le_of_forall_le L₁ M₁ h₁ i) (getD_le_of_forall_le L₂ M₂ h₂ (k - i))
  rwa [Finset.card_range, smul_eq_mul] at h

/-- The value of a packed array as the value of a polynomial at `2^(64 w)`. -/
theorem kroneckerPack_toNat_eval (w : Nat) (a : Array AzNat)
    (ha : ∀ c ∈ a, c.toNat < 2 ^ (64 * w)) :
    (kroneckerPack w a).toNat = (natPoly (a.toList.map toNat)).eval (2 ^ (64 * w)) := by
  rw [natPoly_eval, kroneckerPack_toNat w a ha]

/-- **The coefficients of a packed product.**  For entries of `a` at most `M₁`, of `b` at
most `M₂`, and `(len a + len b) · M₁ M₂ < 2^(64 w)`, the `k`-th block of the product of the
packed numbers is the `k`-th coefficient of the product of the polynomials. -/
theorem kroneckerCoeff_mul_toNat (w : Nat) (a b : Array AzNat) (M₁ M₂ : ℕ)
    (ha : ∀ c ∈ a, c.toNat ≤ M₁) (hb : ∀ c ∈ b, c.toNat ≤ M₂)
    (hM₁ : M₁ < 2 ^ (64 * w)) (hM₂ : M₂ < 2 ^ (64 * w))
    (hB : (a.size + b.size) * (M₁ * M₂) < 2 ^ (64 * w)) (k : ℕ) :
    (kroneckerCoeff w (kroneckerPack w a * kroneckerPack w b) k).toNat =
      ∑ i ∈ Finset.range (k + 1),
        (a.toList.map toNat).getD i 0 * (b.toList.map toNat).getD (k - i) 0 := by
  have hLa : ∀ x ∈ a.toList.map toNat, x ≤ M₁ := by
    intro x hx
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hx
    exact ha c (by simpa using hc)
  have hLb : ∀ x ∈ b.toList.map toNat, x ≤ M₂ := by
    intro x hx
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hx
    exact hb c (by simpa using hc)
  rw [kroneckerCoeff_toNat, toNat_mul,
    kroneckerPack_toNat_eval w a (fun c hc => lt_of_le_of_lt (ha c hc) hM₁),
    kroneckerPack_toNat_eval w b (fun c hc => lt_of_le_of_lt (hb c hc) hM₂), ← eval_mul,
    show (2 : ℕ) ^ (64 * (k * w)) = (2 ^ (64 * w)) ^ k by rw [← pow_mul]; congr 1; ring,
    eval_div_pow_mod _ _ (a.size + b.size - 1)
      (fun i hi => natPoly_mul_coeff_eq_zero _ _ i (by simpa using hi))
      (fun i hi => lt_of_le_of_lt (natPoly_mul_coeff_le _ _ M₁ M₂ hLa hLb i)
        (lt_of_le_of_lt (Nat.mul_le_mul_right _ (by omega)) hB)),
    natPoly_mul_coeff]

theorem le_maxLimbs_foldl (L : List AzNat) (s : Nat) :
    s ≤ L.foldl (fun s c => max s c.limbs.size) s ∧
      ∀ c ∈ L, c.limbs.size ≤ L.foldl (fun s c => max s c.limbs.size) s := by
  induction L generalizing s with
  | nil => simp
  | cons d L ih =>
    obtain ⟨h1, h2⟩ := ih (max s d.limbs.size)
    refine ⟨Nat.le_trans (Nat.le_max_left _ _) h1, ?_⟩
    intro c hc
    rcases List.mem_cons.mp hc with rfl | hc
    · exact Nat.le_trans (Nat.le_max_right _ _) h1
    · exact h2 c hc

theorem limbs_size_le_maxLimbs (a : Array AzNat) (c : AzNat) (hc : c ∈ a) :
    c.limbs.size ≤ maxLimbs a := by
  unfold maxLimbs
  rw [← Array.foldl_toList]
  exact (le_maxLimbs_foldl a.toList 0).2 c (by simpa using hc)

theorem toNat_lt_pow_maxLimbs (a : Array AzNat) (c : AzNat) (hc : c ∈ a) :
    c.toNat < 2 ^ (64 * maxLimbs a) :=
  lt_of_lt_of_le (toNat_lt_pow c)
    (Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_left _ (limbs_size_le_maxLimbs a c hc)))

end Azurite.AzNat
