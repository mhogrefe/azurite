/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzPolynomial.Kronecker
import Azurite.AzPolynomial.Equiv.Mul
import Azurite.AzNat.Equiv.Kronecker
import Azurite.AzNat.Equiv.LogBase2
import Azurite.AzNat.Equiv.Mul.Dispatch
import Azurite.AzZMod.Equiv.RingEquiv
import Azurite.AzNat.Equiv.RingEquiv
import Mathlib.Algebra.Polynomial.Eval.Defs

/-!
# Kronecker multiplication over `ℤ/m` is multiplication

`mulKronecker_eq_mulBasecase`, hence `toPoly_mulKronecker` and `mulKronecker_eq_mul`.

The lifts of the two factors are polynomials `P`, `Q` over `ℕ` (`natPoly`); the packed
numbers are `P(B)`, `Q(B)` with `B = 2^(64 w)`, their product is `(PQ)(B)`, and as the
coefficients of `PQ` are below `B` they are the base-`B` digits of that number.
-/

open Polynomial

namespace Azurite.AzPolynomial

open AzNat (natPoly natPoly_eval natPoly_coeff eval_div_pow_mod)

variable {m : AzNat} [NeZero m.toNat]

/-- The lifts of the coefficients. -/
def liftList (p : AzPolynomial (AzZMod m)) : List ℕ :=
  (p.coeffs.map (·.val)).toList.map AzNat.toNat

theorem liftList_getD (p : AzPolynomial (AzZMod m)) (i : ℕ) :
    (liftList p).getD i 0 = (p.coeff i).val.toNat := by
  unfold liftList coeff
  by_cases hi : i < p.coeffs.size
  · simp [List.getD, hi]
  · simp [List.getD, hi]

theorem liftList_lt (p : AzPolynomial (AzZMod m)) (i : ℕ) :
    (liftList p).getD i 0 < m.toNat := by
  rw [liftList_getD]
  exact (p.coeff i).isLt

theorem kroneckerWidth_spec (n : ℕ) :
    n * (m.toNat * m.toNat) < 2 ^ (64 * kroneckerWidth m n) := by
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact NeZero.ne (0 : AzNat).toNat (by decide)
  have hm := (AzNat.size_bounds m hm0).2
  have hn : n < 2 ^ (n.log2 + 1) := Nat.lt_log2_self
  have hle : 2 * m.size + n.log2 + 1 ≤ 64 * kroneckerWidth m n := by
    unfold kroneckerWidth
    omega
  calc n * (m.toNat * m.toNat)
      < 2 ^ (n.log2 + 1) * (2 ^ m.size * 2 ^ m.size) := by
        have h1 : m.toNat * m.toNat ≤ 2 ^ m.size * 2 ^ m.size :=
          Nat.mul_le_mul hm.le hm.le
        have h2 : 0 < m.toNat * m.toNat :=
          Nat.mul_pos (Nat.pos_of_ne_zero (NeZero.ne _)) (Nat.pos_of_ne_zero (NeZero.ne _))
        calc n * (m.toNat * m.toNat) < 2 ^ (n.log2 + 1) * (m.toNat * m.toNat) :=
              Nat.mul_lt_mul_of_pos_right hn h2
          _ ≤ _ := Nat.mul_le_mul_left _ h1
    _ = 2 ^ (2 * m.size + n.log2 + 1) := by ring
    _ ≤ _ := Nat.pow_le_pow_right (by norm_num) hle

theorem packLift_toNat (p : AzPolynomial (AzZMod m)) (w : ℕ) (hw : m.toNat ≤ 2 ^ (64 * w)) :
    (AzNat.kroneckerPack w (p.coeffs.map (·.val))).toNat =
      (natPoly (liftList p)).eval (2 ^ (64 * w)) := by
  rw [natPoly_eval, AzNat.kroneckerPack_toNat]
  · rfl
  · intro c hc
    obtain ⟨a, _, rfl⟩ := Array.mem_map.mp hc
    exact lt_of_lt_of_le a.isLt hw

/-- A coefficient of the product of the lifts. -/
theorem liftProd_coeff (p q : AzPolynomial (AzZMod m)) (k : ℕ) :
    (natPoly (liftList p) * natPoly (liftList q)).coeff k =
      ∑ i ∈ Finset.range (k + 1), (p.coeff i).val.toNat * (q.coeff (k - i)).val.toNat := by
  rw [Polynomial.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i j => (natPoly (liftList p)).coeff i * (natPoly (liftList q)).coeff j)]
  simp only [natPoly_coeff, liftList_getD]

theorem liftCoeff_eq_zero_of_size_le (p : AzPolynomial (AzZMod m)) (i : ℕ)
    (h : p.coeffs.size ≤ i) : (p.coeff i).val.toNat = 0 := by
  unfold coeff
  rw [Array.getElem?_eq_none h]
  rfl

theorem mulKronecker_eq_mulBasecase (p q : AzPolynomial (AzZMod m)) :
    mulKronecker p q = mulBasecase p q := by
  unfold mulKronecker mulBasecase
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
    obtain ⟨N, hN⟩ : ∃ N, N = p.coeffs.size + q.coeffs.size := ⟨_, rfl⟩
    have hk : k < N - 1 := hN ▸ hk0
    rw [← hN]
    obtain ⟨w, hw⟩ : ∃ w, w = kroneckerWidth m N := ⟨_, rfl⟩
    rw [← hw]
    obtain ⟨B, hBdef⟩ : ∃ B, B = 2 ^ (64 * w) := ⟨_, rfl⟩
    have hspec : N * (m.toNat * m.toNat) < B := by
      rw [hBdef, hw]
      exact kroneckerWidth_spec N
    have hm : 0 < m.toNat := Nat.pos_of_ne_zero (NeZero.ne _)
    have hmB : m.toNat ≤ 2 ^ (64 * w) := by
      have h1 : m.toNat ≤ m.toNat * m.toNat := Nat.le_mul_self _
      have h2 : m.toNat * m.toNat ≤ N * (m.toNat * m.toNat) :=
        Nat.le_mul_of_pos_left _ (by omega)
      omega
    set R := natPoly (liftList p) * natPoly (liftList q) with hR
    have hdeg : ∀ i, N - 1 ≤ i → R.coeff i = 0 := by
      intro i hi
      rw [hR, liftProd_coeff]
      apply Finset.sum_eq_zero
      intro j hj
      rw [Finset.mem_range] at hj
      by_cases hjp : p.coeffs.size ≤ j
      · rw [liftCoeff_eq_zero_of_size_le p j hjp, Nat.zero_mul]
      · rw [liftCoeff_eq_zero_of_size_le q (i - j) (by omega), Nat.mul_zero]
    have hlt : ∀ i, i < N - 1 → R.coeff i < B := by
      intro i hi
      rw [hR, liftProd_coeff]
      have hle : ∑ j ∈ Finset.range (i + 1),
          (p.coeff j).val.toNat * (q.coeff (i - j)).val.toNat ≤
          (Finset.range (i + 1)).card • (m.toNat * m.toNat) :=
        Finset.sum_le_card_nsmul _ _ _ fun j _ =>
          Nat.mul_le_mul (p.coeff j).isLt.le (q.coeff (i - j)).isLt.le
      rw [Finset.card_range, smul_eq_mul] at hle
      have : (i + 1) * (m.toNat * m.toNat) ≤ N * (m.toNat * m.toNat) :=
        Nat.mul_le_mul_right _ (by omega)
      omega
    have hx : (AzNat.kroneckerPack w (p.coeffs.map (·.val)) *
        AzNat.kroneckerPack w (q.coeffs.map (·.val))).toNat = R.eval B := by
      rw [AzNat.toNat_mul, packLift_toNat p w hmB, packLift_toNat q w hmB, hR, eval_mul,
        hBdef]
    apply AzZMod.toZMod_injective
    rw [AzZMod.toZMod_ofAzNat, AzNat.kroneckerCoeff_toNat, hx]
    have hpow : (2 : ℕ) ^ (64 * (k * w)) = B ^ k := by
      rw [hBdef, ← pow_mul]
      congr 1
      ring
    rw [hpow, ← hBdef, eval_div_pow_mod R B (N - 1) hdeg hlt, hR, liftProd_coeff]
    change _ = AzZMod.toZModRingHom _
    rw [map_sum]
    push_cast
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul]
    rfl

@[simp] theorem toPoly_mulKronecker (p q : AzPolynomial (AzZMod m)) :
    AzPolynomial.toPoly (mulKronecker p q) = AzPolynomial.toPoly p * AzPolynomial.toPoly q := by
  rw [mulKronecker_eq_mulBasecase, toPoly_mulBasecase]

/-! ### Natural-number coefficients -/

/-- `n · 2^(64 s₁) · 2^(64 s₂) < 2^(64 (s₁ + s₂ + e))` when `n < 2^(64 e − c)`. -/
theorem kronecker_width_bound (s₁ s₂ e n t : ℕ) (hn : n < 2 ^ t) (ht : t ≤ 64 * e) :
    n * (2 ^ (64 * s₁) * 2 ^ (64 * s₂)) < 2 ^ (t + 64 * (s₁ + s₂)) ∧
      2 ^ (t + 64 * (s₁ + s₂)) ≤ 2 ^ (64 * (s₁ + s₂ + e)) := by
  constructor
  · rw [Nat.mul_add 64, pow_add, pow_add]
    exact Nat.mul_lt_mul_of_pos_right hn (by positivity)
  · exact Nat.pow_le_pow_right (by norm_num) (by omega)

theorem natList_getD (p : AzPolynomial AzNat) (i : ℕ) :
    (p.coeffs.toList.map AzNat.toNat).getD i 0 = (p.coeff i).toNat := by
  unfold coeff
  by_cases hi : i < p.coeffs.size
  · simp [List.getD, hi]
  · simp [List.getD, hi]

theorem mulKroneckerNat_eq_mulBasecase (p q : AzPolynomial AzNat) :
    mulKroneckerNat p q = mulBasecase p q := by
  unfold mulKroneckerNat mulBasecase
  split
  · rfl
  · next hne =>
    simp only [Bool.or_eq_true, beq_iff_eq, not_or] at hne
    obtain ⟨hp, hq⟩ := hne
    dsimp only
    congr 1
    congr 1
    funext k
    obtain ⟨k, -⟩ := k
    dsimp only
    obtain ⟨n, hn⟩ : ∃ n, n = p.coeffs.size + q.coeffs.size := ⟨_, rfl⟩
    rw [← hn]
    obtain ⟨hb1, hb2⟩ := kronecker_width_bound (AzNat.maxLimbs p.coeffs)
      (AzNat.maxLimbs q.coeffs) ((n.log2 + 1 + 63) / 64) n (n.log2 + 1) Nat.lt_log2_self
      (by omega)
    apply AzNat.toNat_injective
    rw [AzNat.kroneckerCoeff_mul_toNat _ p.coeffs q.coeffs (2 ^ (64 * AzNat.maxLimbs p.coeffs))
      (2 ^ (64 * AzNat.maxLimbs q.coeffs))
      (fun c hc => (AzNat.toNat_lt_pow_maxLimbs _ c hc).le)
      (fun c hc => (AzNat.toNat_lt_pow_maxLimbs _ c hc).le)
      (Nat.pow_lt_pow_right (by norm_num) (by omega))
      (Nat.pow_lt_pow_right (by norm_num) (by omega))
      (hn ▸ lt_of_lt_of_le hb1 hb2)]
    change _ = AzNat.toNatRingHom _
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, natList_getD, natList_getD]
    rfl

@[simp] theorem toPoly_mulKroneckerNat (p q : AzPolynomial AzNat) :
    AzPolynomial.toPoly (mulKroneckerNat p q) =
      AzPolynomial.toPoly p * AzPolynomial.toPoly q := by
  rw [mulKroneckerNat_eq_mulBasecase, toPoly_mulBasecase]

end Azurite.AzPolynomial
