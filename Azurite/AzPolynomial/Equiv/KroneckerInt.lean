/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzPolynomial.Equiv.Kronecker
import Azurite.AzInt.Equiv.RingEquiv
import Azurite.AzInt.Equiv.Sub
import Azurite.AzInt.Equiv.Mul
import Azurite.AzNat.Equiv.Pow2
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Kronecker multiplication over `AzInt` is multiplication

`mulKroneckerInt_eq_mulBasecase`, hence `toPoly_mulKroneckerInt`.

A factor is the polynomial `P = P⁺ − P⁻` over `ℤ` (`signedPoly`); the signed packed numbers
are `P(B)`, `Q(B)` with `B = 2^(64 w)`, their product is `(PQ)(B) = ∑ cₖ Bᵏ` with
`|cₖ| < B/2`.  After adding `∑ (B/2) Bᵏ` the number is `∑ (cₖ + B/2) Bᵏ` with all blocks in
`[0, B)`, so the blocks are its base-`B` digits (`sum_div_pow_mod`).
-/

open Polynomial

namespace Azurite.AzPolynomial

open AzNat (natPoly natPoly_eval natPoly_coeff eval_div_pow_mod)

/-- The base-`B` digits of `∑ gᵢ Bⁱ` for `gᵢ < B`. -/
theorem sum_div_pow_mod (B N : ℕ) (g : ℕ → ℕ) (hg : ∀ i, i < N → g i < B) (k : ℕ)
    (hk : k < N) : (∑ i ∈ Finset.range N, g i * B ^ i) / B ^ k % B = g k := by
  let R : ℕ[X] := ∑ i ∈ Finset.range N, Polynomial.monomial i (g i)
  have hc : ∀ i, R.coeff i = if i < N then g i else 0 := by
    intro i
    simp [R, Polynomial.coeff_monomial]
  have he : R.eval B = ∑ i ∈ Finset.range N, g i * B ^ i := by
    simp [R, Polynomial.eval_finsetSum]
  rw [← he, eval_div_pow_mod R B N
    (fun i hi => by rw [hc]; simp; omega)
    (fun i hi => by rw [hc]; simp [hi, hg i hi]), hc]
  simp [hk]

theorem ofDigits_replicate (B h N : ℕ) :
    Nat.ofDigits B (List.replicate N h) = ∑ i ∈ Finset.range N, h * B ^ i := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [List.replicate_succ, Nat.ofDigits_cons, ih, Finset.sum_range_succ', Finset.mul_sum]
    simp only [pow_succ, pow_zero, mul_one]
    rw [add_comm]
    congr 1
    exact Finset.sum_congr rfl fun i _ => by ring

/-- The lifts of the positive and of the negative coefficients. -/
def posList (a : Array AzInt) : List ℕ := (posParts a).toList.map AzNat.toNat
def negList (a : Array AzInt) : List ℕ := (negParts a).toList.map AzNat.toNat

theorem toInt_toAzInt (n : AzNat) : n.toAzInt.toInt = n.toNat := by
  simp [AzNat.toAzInt, AzInt.toInt]

theorem posNeg_getD (a : Array AzInt) (i : ℕ) :
    ((posList a).getD i 0 : ℤ) - ((negList a).getD i 0 : ℤ) = (a[i]?.getD 0).toInt := by
  unfold posList negList posParts negParts
  by_cases hi : i < a.size
  · simp only [List.getD, Array.toList_map, List.map_map, List.getElem?_map,
      Array.getElem?_toList, Array.getElem?_eq_getElem hi, Option.map_some, Option.getD_some,
      Function.comp]
    by_cases hs : a[i].sign
    · simp [hs, AzInt.toInt]
    · simp [hs, AzInt.toInt]
  · simp [List.getD, hi]

/-- `P = P⁺ − P⁻` over `ℤ`. -/
noncomputable def signedPoly (a : Array AzInt) : ℤ[X] :=
  (natPoly (posList a)).map (Nat.castRingHom ℤ) - (natPoly (negList a)).map (Nat.castRingHom ℤ)

theorem signedPoly_coeff (a : Array AzInt) (i : ℕ) :
    (signedPoly a).coeff i = (a[i]?.getD 0).toInt := by
  rw [← posNeg_getD]
  simp [signedPoly, natPoly_coeff]

theorem abs_toInt (c : AzInt) : |c.toInt| = c.abs.toNat := by
  unfold AzInt.toInt
  split <;> simp

/-- The bound on the coefficients: the limbs of the absolute values. -/
theorem abs_toInt_le (a : Array AzInt) (i : ℕ) :
    |(a[i]?.getD 0).toInt| ≤ ((2 ^ (64 * AzNat.maxLimbs (a.map AzInt.abs)) : ℕ) : ℤ) := by
  by_cases hi : i < a.size
  · rw [Array.getElem?_eq_getElem hi, Option.getD_some, abs_toInt]
    exact_mod_cast (AzNat.toNat_lt_pow_maxLimbs (a.map AzInt.abs) a[i].abs
      (Array.mem_map.mpr ⟨a[i], Array.getElem_mem hi, rfl⟩)).le
  · rw [Array.getElem?_eq_none (by omega)]
    simp

theorem parts_lt (a : Array AzInt) (w : ℕ) (hw : AzNat.maxLimbs (a.map AzInt.abs) ≤ w) :
    (∀ c ∈ posParts a, c.toNat < 2 ^ (64 * w)) ∧ ∀ c ∈ negParts a, c.toNat < 2 ^ (64 * w) := by
  have key : ∀ x ∈ a, x.abs.toNat < 2 ^ (64 * w) := fun x hx =>
    lt_of_lt_of_le (AzNat.toNat_lt_pow_maxLimbs (a.map AzInt.abs) x.abs
      (Array.mem_map.mpr ⟨x, hx, rfl⟩))
      (Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_left _ hw))
  have h0 : (0 : AzNat).toNat < 2 ^ (64 * w) := by
    rw [show (0 : AzNat).toNat = 0 from rfl]
    positivity
  constructor
  · intro c hc
    obtain ⟨x, hx, rfl⟩ := Array.mem_map.mp hc
    split
    · exact key x hx
    · exact h0
  · intro c hc
    obtain ⟨x, hx, rfl⟩ := Array.mem_map.mp hc
    split
    · exact h0
    · exact key x hx

/-- The signed packed number is the value of `signedPoly` at `2^(64 w)`. -/
theorem kroneckerPackInt_toInt (a : Array AzInt) (w : ℕ)
    (hw : AzNat.maxLimbs (a.map AzInt.abs) ≤ w) :
    (kroneckerPackInt w a).toInt = (signedPoly a).eval (((2 ^ (64 * w) : ℕ) : ℤ)) := by
  obtain ⟨hp, hn⟩ := parts_lt a w hw
  unfold kroneckerPackInt signedPoly
  rw [AzInt.toInt_sub, toInt_toAzInt, toInt_toAzInt, AzNat.kroneckerPack_toNat_eval _ _ hp,
    AzNat.kroneckerPack_toNat_eval _ _ hn, eval_sub, eval_natCast_map, eval_natCast_map]
  rfl

theorem toNat_abs_of_toInt (z : AzInt) (N : ℕ) (h : z.toInt = N) : z.abs.toNat = N := by
  have := abs_toInt z
  rw [h] at this
  simpa using this.symm

theorem mulKroneckerInt_eq_mulBasecase (p q : AzPolynomial AzInt) :
    mulKroneckerInt p q = mulBasecase p q := by
  unfold mulKroneckerInt mulBasecase
  split
  · rfl
  · next hne =>
    simp only [Bool.or_eq_true, beq_iff_eq, not_or] at hne
    obtain ⟨hp, hq⟩ := hne
    dsimp only
    congr 1
    congr 1
    funext k
    obtain ⟨k, hk0⟩ := k
    dsimp only
    obtain ⟨n, hn⟩ : ∃ n, n = p.coeffs.size + q.coeffs.size := ⟨_, rfl⟩
    have hk : k < n - 1 := hn ▸ hk0
    rw [← hn]
    obtain ⟨s₁, hs₁⟩ : ∃ s, s = AzNat.maxLimbs (p.coeffs.map AzInt.abs) := ⟨_, rfl⟩
    obtain ⟨s₂, hs₂⟩ : ∃ s, s = AzNat.maxLimbs (q.coeffs.map AzInt.abs) := ⟨_, rfl⟩
    rw [← hs₁, ← hs₂]
    obtain ⟨e, he⟩ : ∃ e, e = (n.log2 + 2 + 63) / 64 := ⟨_, rfl⟩
    rw [← he]
    obtain ⟨w, hw⟩ : ∃ w, w = s₁ + s₂ + e := ⟨_, rfl⟩
    rw [← hw]
    obtain ⟨half, hhalf⟩ : ∃ h : ℕ, h = 2 ^ (64 * w - 1) := ⟨_, rfl⟩
    obtain ⟨B, hBdef⟩ : ∃ B : ℕ, B = 2 ^ (64 * w) := ⟨_, rfl⟩
    have he1 : 1 ≤ e := by omega
    have hB2 : B = 2 * half := by
      rw [hBdef, hhalf, ← pow_succ']
      congr 1
      omega
    -- the bound `n · M₁ M₂ < half`
    obtain ⟨hb1, hb2⟩ := kronecker_width_bound s₁ s₂ e n (n.log2 + 1) Nat.lt_log2_self
      (by omega)
    have hbound : n * (2 ^ (64 * s₁) * 2 ^ (64 * s₂)) < half := by
      refine lt_of_lt_of_le hb1 ?_
      rw [hhalf]
      exact Nat.pow_le_pow_right (by norm_num) (by omega)
    -- the product polynomial
    obtain ⟨R, hR⟩ : ∃ R : ℤ[X], R = signedPoly p.coeffs * signedPoly q.coeffs := ⟨_, rfl⟩
    have hcoeff : ∀ i, R.coeff i =
        ∑ j ∈ Finset.range (i + 1), (p.coeff j).toInt * (q.coeff (i - j)).toInt := by
      intro i
      rw [hR, Polynomial.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
        (fun a b => (signedPoly p.coeffs).coeff a * (signedPoly q.coeffs).coeff b)]
      simp only [signedPoly_coeff]
      rfl
    have hzero : ∀ i, n - 1 ≤ i → R.coeff i = 0 := by
      intro i hi
      rw [hcoeff]
      apply Finset.sum_eq_zero
      intro j hj
      rw [Finset.mem_range] at hj
      by_cases hjp : p.coeffs.size ≤ j
      · have : p.coeff j = 0 := by
          unfold coeff
          rw [Array.getElem?_eq_none hjp]
          rfl
        rw [this]
        simp
      · have : q.coeff (i - j) = 0 := by
          unfold coeff
          rw [Array.getElem?_eq_none (by omega)]
          rfl
        rw [this]
        simp
    have habs : ∀ i, i < n - 1 → |R.coeff i| < (half : ℤ) := by
      intro i hi
      rw [hcoeff]
      have h1 : |∑ j ∈ Finset.range (i + 1), (p.coeff j).toInt * (q.coeff (i - j)).toInt| ≤
          ∑ j ∈ Finset.range (i + 1), |(p.coeff j).toInt * (q.coeff (i - j)).toInt| :=
        Finset.abs_sum_le_sum_abs _ _
      have h2 : ∑ j ∈ Finset.range (i + 1), |(p.coeff j).toInt * (q.coeff (i - j)).toInt| ≤
          (Finset.range (i + 1)).card •
            (((2 ^ (64 * s₁) : ℕ) : ℤ) * ((2 ^ (64 * s₂) : ℕ) : ℤ)) := by
        refine Finset.sum_le_card_nsmul _ _ _ fun j _ => ?_
        rw [abs_mul]
        exact mul_le_mul (hs₁ ▸ abs_toInt_le p.coeffs j) (hs₂ ▸ abs_toInt_le q.coeffs (i - j))
          (abs_nonneg _) (by positivity)
      rw [Finset.card_range, nsmul_eq_mul] at h2
      have h3 : ((i + 1 : ℕ) : ℤ) * (((2 ^ (64 * s₁) : ℕ) : ℤ) * ((2 ^ (64 * s₂) : ℕ) : ℤ)) <
          (half : ℤ) := by
        have : (i + 1) * (2 ^ (64 * s₁) * 2 ^ (64 * s₂)) < half :=
          lt_of_le_of_lt (Nat.mul_le_mul_right _ (by omega)) hbound
        exact_mod_cast this
      linarith
    -- the value of the signed product
    have hX : (kroneckerPackInt w p.coeffs * kroneckerPackInt w q.coeffs).toInt =
        ∑ i ∈ Finset.range (n - 1), R.coeff i * (B : ℤ) ^ i := by
      rw [AzInt.toInt_mul, kroneckerPackInt_toInt _ _ (by omega),
        kroneckerPackInt_toInt _ _ (by omega), ← eval_mul, ← hR, ← hBdef]
      refine eval_eq_sum_range' ?_ _
      have : R.natDegree ≤ n - 2 :=
        Polynomial.natDegree_le_iff_coeff_eq_zero.mpr fun N hN => hzero N (by omega)
      omega
    -- the offset
    have hhalf_lt : half < B := by omega
    have hoff : (AzNat.kroneckerPack w (Array.replicate (n - 1) (AzNat.pow2 (64 * w - 1)))).toNat =
        ∑ i ∈ Finset.range (n - 1), half * B ^ i := by
      rw [AzNat.kroneckerPack_toNat, Array.toList_replicate, List.map_replicate,
        AzNat.toNat_pow2, ← hhalf, ← hBdef, ofDigits_replicate]
      intro c hc
      rw [(Array.mem_replicate.mp hc).2, AzNat.toNat_pow2, ← hhalf, ← hBdef]
      exact hhalf_lt
    -- the digits
    obtain ⟨g, hg⟩ : ∃ g : ℕ → ℕ, g = fun i => (R.coeff i + half).toNat := ⟨_, rfl⟩
    have hgi : ∀ i, i < n - 1 → ((g i : ℕ) : ℤ) = R.coeff i + half := by
      intro i hi
      rw [hg]
      have := abs_lt.mp (habs i hi)
      exact Int.toNat_of_nonneg (by linarith)
    have hgB : ∀ i, i < n - 1 → g i < B := by
      intro i hi
      have h1 := hgi i hi
      have := abs_lt.mp (habs i hi)
      have : ((g i : ℕ) : ℤ) < (B : ℤ) := by rw [h1, hB2]; push_cast; linarith
      exact_mod_cast this
    have hY : ((kroneckerPackInt w p.coeffs * kroneckerPackInt w q.coeffs +
        (AzNat.kroneckerPack w
          (Array.replicate (n - 1) (AzNat.pow2 (64 * w - 1)))).toAzInt).abs).toNat
        = ∑ i ∈ Finset.range (n - 1), g i * B ^ i := by
      apply toNat_abs_of_toInt
      rw [AzInt.toInt_add, hX, toInt_toAzInt, hoff]
      push_cast
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [hgi i (Finset.mem_range.mp hi)]
      ring
    apply AzInt.ringEquivInt.injective
    show AzInt.toInt _ = AzInt.toInt _
    rw [AzInt.toInt_sub, toInt_toAzInt, toInt_toAzInt, AzNat.kroneckerCoeff_toNat, hY,
      AzNat.toNat_pow2, ← hhalf,
      show (2 : ℕ) ^ (64 * (k * w)) = B ^ k by rw [hBdef, ← pow_mul]; congr 1; ring,
      ← hBdef, sum_div_pow_mod B (n - 1) g hgB k hk, hgi k hk, add_sub_cancel_right, hcoeff]
    change _ = AzInt.toIntRingHom _
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul]
    rfl

@[simp] theorem toPoly_mulKroneckerInt (p q : AzPolynomial AzInt) :
    AzPolynomial.toPoly (mulKroneckerInt p q) =
      AzPolynomial.toPoly p * AzPolynomial.toPoly q := by
  rw [mulKroneckerInt_eq_mulBasecase, toPoly_mulBasecase]

end Azurite.AzPolynomial
