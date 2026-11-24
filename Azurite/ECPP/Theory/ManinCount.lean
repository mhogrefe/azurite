/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.ECPP.Theory.ManinCurve
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.FieldTheory.Finite.Basic

/-!
# Manin's proof of the Hasse bound: the count of points

After Knapp, *Elliptic Curves*, §X.3, Lemma 10.7.  Over `𝔽_p`, with `f = x³ + ax + b`, the
`X`-coordinate of `(x^p, f^((p−1)/2)) − (x, 1)` is (10.16)

  `X_{−1} = N/(x^p − x)²`,  `N = f (f^((p−1)/2) + 1)² − (x^p + x)(x^p − x)²` (`countNum`),

and `x^p − x = ∏_j (x − j)`.  The factor `x − j` cancels from the denominator twice, once or
not at all as `f(j)` is a non-residue, `0` or a non-zero residue (`expG`), and it stays with
the multiplicity `expR j = 2 − expG j`, the number of `y` with `y² = f(j)`.

`rfHeight_countNum`: the height of `X_{−1}` is `∑_j expR j + 1`.
-/

namespace Azurite.ECPP.Manin

open Polynomial Finset

variable {p : ℕ} [Fact p.Prime] (a b : ZMod p)

/-- `f = x³ + ax + b` as a polynomial. -/
noncomputable def cubic : (ZMod p)[X] := X ^ 3 + C a * X + C b

/-- `f(j) = j³ + aj + b`. -/
def cubicVal (j : ZMod p) : ZMod p := j ^ 3 + a * j + b

theorem eval_cubic (j : ZMod p) : (cubic a b).eval j = cubicVal a b j := by
  simp [cubic, cubicVal]

/-- The numerator `N` of `X_{−1}` over the denominator `(x^p − x)²`. -/
noncomputable def countNum : (ZMod p)[X] :=
  cubic a b * (cubic a b ^ (p / 2) + 1) ^ 2 - (X ^ p + X) * (X ^ p - X) ^ 2

/-- The multiplicity with which `x − j` cancels: `1` at a root of `f`, `0` at a non-zero
residue, `2` at a non-residue. -/
def expG (j : ZMod p) : ℕ :=
  if cubicVal a b j = 0 then 1 else if cubicVal a b j ^ (p / 2) = 1 then 0 else 2

/-- The multiplicity with which `x − j` stays in the denominator. -/
def expR (j : ZMod p) : ℕ := 2 - expG a b j

theorem expG_add_expR (j : ZMod p) : expG a b j + expR a b j = 2 := by
  unfold expR expG
  split_ifs <;> rfl

omit [Fact p.Prime] in
theorem half_ne_zero (hp : 2 ≤ p) : p / 2 ≠ 0 := by omega

theorem X_sub_C_dvd_X_pow_sub_X (j : ZMod p) : (X - C j) ∣ (X ^ p - X : (ZMod p)[X]) := by
  rw [dvd_iff_isRoot, IsRoot.def]
  simp [ZMod.pow_card]

theorem eval_countNum (j : ZMod p) :
    (countNum a b).eval j = cubicVal a b j * (cubicVal a b j ^ (p / 2) + 1) ^ 2 := by
  simp [countNum, eval_cubic, ZMod.pow_card]

/-- `(x − j)^(expG j)` divides `N`. -/
theorem pow_expG_dvd (j : ZMod p) : (X - C j) ^ expG a b j ∣ countNum a b := by
  unfold expG
  split_ifs with h0 h1
  · rw [pow_one, dvd_iff_isRoot, IsRoot.def, eval_countNum, h0, zero_mul]
  · rw [pow_zero]
    exact one_dvd _
  · have hm1 : cubicVal a b j ^ (p / 2) = -1 :=
      (ZMod.pow_div_two_eq_neg_one_or_one p h0).resolve_left h1
    have hd : (X - C j) ∣ cubic a b ^ (p / 2) + 1 := by
      rw [dvd_iff_isRoot, IsRoot.def]
      simp [eval_cubic, hm1]
    exact dvd_sub (dvd_mul_of_dvd_right (pow_dvd_pow_of_dvd hd 2) _)
      (dvd_mul_of_dvd_right (pow_dvd_pow_of_dvd (X_sub_C_dvd_X_pow_sub_X j) 2) _)

/-- Where `x − j` stays in the denominator, `N` is divisible by no higher power of it. -/
theorem not_pow_succ_dvd (h2 : (2 : ZMod p) ≠ 0) (hΔ : 4 * a ^ 3 + 27 * b ^ 2 ≠ 0) (j : ZMod p)
    (hR : 0 < expR a b j) : ¬ (X - C j) ^ (expG a b j + 1) ∣ countNum a b := by
  have hp2 : p / 2 ≠ 0 := half_ne_zero (Fact.out : p.Prime).two_le
  unfold expR expG at hR
  unfold expG
  split_ifs at hR ⊢ with h0 h1
  · -- a root of `f`: it is simple
    intro hdvd
    have h1 : (X - C j) ^ 2 ∣ cubic a b * (cubic a b ^ (p / 2) + 1) ^ 2 := by
      have := dvd_add hdvd
        (dvd_mul_of_dvd_right (pow_dvd_pow_of_dvd (X_sub_C_dvd_X_pow_sub_X j) 2) (X ^ p + X))
      rwa [countNum, sub_add_cancel] at this
    have hnd : ¬ (X - C j) ∣ cubic a b ^ (p / 2) + 1 := by
      rw [dvd_iff_isRoot, IsRoot.def]
      simp [eval_cubic, h0, hp2]
    have hc : IsCoprime (X - C j) (cubic a b ^ (p / 2) + 1) :=
      (irreducible_X_sub_C j).coprime_iff_not_dvd.mpr hnd
    obtain ⟨g, hg⟩ : (X - C j) ^ 2 ∣ cubic a b :=
      (hc.pow (m := 2) (n := 2)).dvd_of_dvd_mul_right h1
    have hd : (derivative (cubic a b)).eval j = 0 := by
      rw [hg]
      simp [derivative_mul, derivative_X_sub_C_sq]
    have hd' : 3 * j ^ 2 + a = 0 := by
      have := hd
      simp [cubic] at this
      linear_combination this
    have ha : a = -3 * j ^ 2 := by linear_combination hd'
    have hb : b = 2 * j ^ 3 := by
      have := h0
      rw [cubicVal, ha] at this
      linear_combination this
    apply hΔ
    rw [ha, hb]
    ring
  · -- a non-zero residue: `N(j) = 4 f(j) ≠ 0`
    intro hdvd
    rw [zero_add, pow_one, dvd_iff_isRoot, IsRoot.def, eval_countNum, h1] at hdvd
    rcases mul_eq_zero.mp hdvd with h | h
    · exact h0 h
    · have : (1 + 1 : ZMod p) = 2 := by norm_num
      rw [this] at h
      exact h2 (pow_eq_zero_iff (by norm_num) |>.mp h)
  · omega

/-- `x^p − x = ∏_j (x − j)`. -/
theorem prod_X_sub_C_eq : ∏ j : ZMod p, (X - C j) = (X ^ p - X : (ZMod p)[X]) := by
  have hp := (Fact.out : p.Prime).one_lt
  have hmon : (∏ j : ZMod p, (X - C j)).Monic := monic_prod_of_monic _ _ fun j _ => monic_X_sub_C j
  have hmon2 : (X ^ p - X : (ZMod p)[X]).Monic := by
    apply monic_X_pow_sub
    rw [degree_X]
    exact_mod_cast hp
  have hdvd : ∏ j : ZMod p, (X - C j) ∣ (X ^ p - X : (ZMod p)[X]) :=
    Finset.prod_dvd_of_coprime
      (fun _ _ _ _ hik => pairwise_coprime_X_sub_C (s := id) Function.injective_id hik)
      (fun j _ => X_sub_C_dvd_X_pow_sub_X j)
  have hdeg : (X ^ p - X : (ZMod p)[X]).natDegree ≤ (∏ j : ZMod p, (X - C j)).natDegree := by
    rw [natDegree_prod_of_monic _ _ fun j _ => monic_X_sub_C j,
      FiniteField.X_pow_card_sub_X_natDegree_eq _ hp]
    simp [ZMod.card]
  exact (eq_of_monic_of_dvd_of_natDegree_le hmon hmon2 hdvd hdeg).symm

/-- The product of the cancelling factors. -/
noncomputable def prodG : (ZMod p)[X] := ∏ j : ZMod p, (X - C j) ^ expG a b j

/-- The product of the factors that stay: the denominator of `X_{−1}` in lowest terms. -/
noncomputable def prodR : (ZMod p)[X] := ∏ j : ZMod p, (X - C j) ^ expR a b j

theorem prodG_mul_prodR : prodG a b * prodR a b = (X ^ p - X) ^ 2 := by
  rw [prodG, prodR, ← prod_mul_distrib, ← prod_X_sub_C_eq, ← prod_pow]
  refine prod_congr rfl fun j _ => ?_
  rw [← pow_add, expG_add_expR]

theorem prodG_ne_zero : prodG a b ≠ 0 :=
  (monic_prod_of_monic _ _ fun j _ => (monic_X_sub_C j).pow _).ne_zero

theorem prodR_ne_zero : prodR a b ≠ 0 :=
  (monic_prod_of_monic _ _ fun j _ => (monic_X_sub_C j).pow _).ne_zero

theorem natDegree_prodG : (prodG a b).natDegree = ∑ j : ZMod p, expG a b j := by
  rw [prodG, natDegree_prod_of_monic _ _ fun j _ => (monic_X_sub_C j).pow _]
  refine sum_congr rfl fun j _ => ?_
  rw [(monic_X_sub_C j).natDegree_pow, natDegree_X_sub_C, mul_one]

theorem natDegree_prodR : (prodR a b).natDegree = ∑ j : ZMod p, expR a b j := by
  rw [prodR, natDegree_prod_of_monic _ _ fun j _ => (monic_X_sub_C j).pow _]
  refine sum_congr rfl fun j _ => ?_
  rw [(monic_X_sub_C j).natDegree_pow, natDegree_X_sub_C, mul_one]

theorem sum_expG_add_sum_expR :
    ∑ j : ZMod p, expG a b j + ∑ j : ZMod p, expR a b j = 2 * p := by
  rw [← sum_add_distrib, sum_congr rfl fun j _ => expG_add_expR a b j, sum_const, card_univ,
    ZMod.card, smul_eq_mul, mul_comm]

theorem prodG_dvd_countNum : prodG a b ∣ countNum a b :=
  Finset.prod_dvd_of_coprime
    (fun _ _ _ _ hik =>
      (pairwise_coprime_X_sub_C (s := id) Function.injective_id hik).pow)
    (fun j _ => pow_expG_dvd a b j)

/-- Frobenius on `f`: `f^p = x^(3p) + a x^p + b`. -/
theorem cubic_pow_card : cubic a b ^ p = (X ^ p) ^ 3 + C a * X ^ p + C b := by
  have h := ZMod.expand_card (cubic a b)
  rw [← h]
  simp [cubic]

theorem two_mul_half_add_one (hp5 : 5 ≤ p) : 2 * (p / 2) + 1 = p := by
  rcases (Fact.out : p.Prime).eq_two_or_odd with h | h
  · omega
  · omega

/-- The numerator `N` has degree `2p + 1`. -/
theorem natDegree_countNum (hp5 : 5 ≤ p) : (countNum a b).natDegree = 2 * p + 1 := by
  have hodd := two_mul_half_add_one hp5
  have hL : cubic a b * (cubic a b ^ (p / 2)) ^ 2 = cubic a b ^ p := by
    calc cubic a b * (cubic a b ^ (p / 2)) ^ 2 = cubic a b ^ (2 * (p / 2) + 1) := by ring
      _ = cubic a b ^ p := by rw [hodd]
  have hexp := cubic_pow_card a b
  have e : countNum a b = X ^ (2 * p + 1)
      + (C a * X ^ p + C b + 2 * cubic a b ^ (p / 2 + 1) + cubic a b + X ^ (p + 2) - X ^ 3) := by
    unfold countNum
    linear_combination hL + hexp
  have hrest : (C a * X ^ p + C b + 2 * cubic a b ^ (p / 2 + 1) + cubic a b + X ^ (p + 2)
      - X ^ 3 : (ZMod p)[X]).natDegree ≤ 2 * p := by
    unfold cubic
    compute_degree
    omega
  rw [e, natDegree_add_eq_left_of_natDegree_lt (by rw [natDegree_X_pow]; omega),
    natDegree_X_pow]

/-- **The height of `N/(x^p − x)²`** is `∑_j expR j + 1`. -/
theorem rfHeight_countNum (h2 : (2 : ZMod p) ≠ 0) (hΔ : 4 * a ^ 3 + 27 * b ^ 2 ≠ 0)
    (hp5 : 5 ≤ p) :
    rfHeight (algebraMap (ZMod p)[X] (RatFunc (ZMod p)) (countNum a b)
        / algebraMap (ZMod p)[X] (RatFunc (ZMod p)) ((X ^ p - X) ^ 2))
      = ∑ j : ZMod p, expR a b j + 1 := by
  obtain ⟨N', hN'⟩ := prodG_dvd_countNum a b
  have hG0 := prodG_ne_zero a b
  have hR0 := prodR_ne_zero a b
  -- `N′` is coprime to the product of the factors that stay
  have hcop : IsCoprime N' (prodR a b) := by
    refine IsCoprime.prod_right fun j _ => ?_
    by_cases hR : expR a b j = 0
    · rw [hR, pow_zero]
      exact isCoprime_one_right
    · refine IsCoprime.pow_right ?_
      refine ((irreducible_X_sub_C j).coprime_iff_not_dvd.mpr fun hd => ?_).symm
      refine not_pow_succ_dvd a b h2 hΔ j (Nat.pos_of_ne_zero hR) ?_
      have hsplit : prodG a b = (X - C j) ^ expG a b j
          * ∏ i ∈ univ.erase j, (X - C i) ^ expG a b i :=
        (mul_prod_erase univ (fun i => (X - C i) ^ expG a b i) (mem_univ j)).symm
      rw [hN', hsplit, pow_succ, mul_assoc]
      exact mul_dvd_mul_left _ (hd.mul_left _)
  -- the fraction in lowest terms
  have hfrac : algebraMap (ZMod p)[X] (RatFunc (ZMod p)) (countNum a b)
        / algebraMap (ZMod p)[X] (RatFunc (ZMod p)) ((X ^ p - X) ^ 2)
      = algebraMap (ZMod p)[X] (RatFunc (ZMod p)) N'
        / algebraMap (ZMod p)[X] (RatFunc (ZMod p)) (prodR a b) := by
    rw [hN', ← prodG_mul_prodR a b, map_mul, map_mul,
      mul_div_mul_left _ _ (RatFunc.algebraMap_ne_zero hG0)]
  rw [hfrac, rfHeight_div_of_coprime hcop hR0, natDegree_prodR]
  -- the degree of `N′`
  have hN0 : N' ≠ 0 := by
    rintro rfl
    have := natDegree_countNum a b hp5
    rw [hN', mul_zero, natDegree_zero] at this
    omega
  have hdeg : (prodG a b).natDegree + N'.natDegree = 2 * p + 1 := by
    rw [← natDegree_mul hG0 hN0, ← hN', natDegree_countNum a b hp5]
  rw [natDegree_prodG] at hdeg
  have hsum := sum_expG_add_sum_expR a b
  omega

end Azurite.ECPP.Manin
