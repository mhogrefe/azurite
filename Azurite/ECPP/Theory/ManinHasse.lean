/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.ECPP.Theory.ManinCount
import Azurite.ECPP.Theory.Manin
import Mathlib.Algebra.Field.ZMod

/-!
# The Hasse bound over the prime fields

**`hasseBound : HasseBound`** — for `p ≥ 5` and `E : y² = x³ + ax + b` over `𝔽_p` with
`4a³ + 27b² ≠ 0`, `(#E(𝔽_p) − (p + 1))² ≤ 4p`.  Manin's proof, after Knapp, *Elliptic
Curves*, §X.3 (Theorem 10.5), and Chahal–Osserman, Amer. Math. Monthly 115 (2008).

On the twisted curve over `𝔽_p(x)` (`Theory/ManinCurve.lean`) take
`Z_n = (x^p, f^((p−1)/2)) + n (x, 1)` (`startPt`, `basePt`) and `d_n` its height.  Then

* `d_{n−1} + d_{n+1} = 2 d_n + 2` (`ptHeight_sub_add`);
* `d_0 = p` (`ptHeight_startPt`) and `d_{−1} = N_p + 1` (`ptHeight_startPt_sub`,
  `rfHeight_countNum`), `N_p` the number of affine points (`card_point`);

so `d_n = n² − (N_p − p) n + p ≥ 0` for every integer `n`, and `(N_p − p)² ≤ 4p`
(`sq_le_of_degree`).
-/

namespace Azurite.ECPP.Manin

open Polynomial Finset WeierstrassCurve

open Classical

variable {p : ℕ} [Fact p.Prime] {a b : ZMod p}

theorem lam_eq_cubic : lam a b = algebraMap (ZMod p)[X] (RatFunc (ZMod p)) (cubic a b) :=
  lam_eq a b

/-- Frobenius on `λ`: `λ^p = x^(3p) + a x^p + b`. -/
theorem lam_pow_card :
    lam a b ^ p = (RatFunc.X ^ p) ^ 3 + RatFunc.C a * RatFunc.X ^ p + RatFunc.C b := by
  rw [lam_eq_cubic, ← map_pow, cubic_pow_card]
  simp only [map_add, map_mul, map_pow, RatFunc.algebraMap_X, RatFunc.algebraMap_C]

/-- The point `(x^p, λ^((p−1)/2))` satisfies the equation. -/
theorem startPt_equation (hp5 : 5 ≤ p) : (twist a b).toAffine.Equation
    (lam a b * RatFunc.X ^ p) (lam a b ^ 2 * lam a b ^ (p / 2)) := by
  rw [twist_equation_iff]
  have hodd := two_mul_half_add_one hp5
  have hL : lam a b * (lam a b ^ (p / 2)) ^ 2 = lam a b ^ p := by
    calc lam a b * (lam a b ^ (p / 2)) ^ 2 = lam a b ^ (2 * (p / 2) + 1) := by ring
      _ = lam a b ^ p := by rw [hodd]
  have hlp := lam_pow_card (a := a) (b := b)
  linear_combination (lam a b) ^ 3 * hL + (lam a b) ^ 3 * hlp

theorem zmod_two_ne_zero (hp5 : 5 ≤ p) : (2 : ZMod p) ≠ 0 := by
  have : (2 : ZMod p) = ((2 : ℕ) : ZMod p) := by norm_num
  rw [this, Ne, ZMod.natCast_eq_zero_iff]
  intro h
  have := Nat.le_of_dvd (by norm_num) h
  omega

variable (h2 : (2 : ZMod p) ≠ 0) (hΔ : 4 * a ^ 3 + 27 * b ^ 2 ≠ 0) (hp5 : 5 ≤ p)

/-- **The point `(x^p, λ^((p−1)/2))`** of the twisted curve. -/
noncomputable def startPt : (twist a b).toAffine.Point :=
  .some (lam a b * RatFunc.X ^ p) (lam a b ^ 2 * lam a b ^ (p / 2))
    (twist_nonsingular h2 hΔ (startPt_equation hp5))

include h2 hΔ hp5

/-- `d_0 = p`. -/
theorem ptHeight_startPt : ptHeight (startPt h2 hΔ hp5) = p := by
  show rfHeight (lam a b * RatFunc.X ^ p / lam a b) = p
  rw [mul_div_cancel_left₀ _ (lam_ne_zero a b)]
  have : (RatFunc.X ^ p : RatFunc (ZMod p))
      = algebraMap (ZMod p)[X] (RatFunc (ZMod p)) (X ^ p) := by
    simp only [map_pow, RatFunc.algebraMap_X]
  rw [this]
  unfold rfHeight
  rw [RatFunc.num_algebraMap, RatFunc.denom_algebraMap]
  simp

/-- `d_{−1} = N_p + 1` (Knapp, (10.15)–(10.16)). -/
theorem ptHeight_startPt_sub :
    ptHeight (startPt h2 hΔ hp5 - basePt h2 hΔ) = ∑ j : ZMod p, expR a b j + 1 := by
  have hl0 := lam_ne_zero a b
  have hXne : (RatFunc.X ^ p - RatFunc.X : RatFunc (ZMod p)) ≠ 0 := by
    have : (RatFunc.X ^ p - RatFunc.X : RatFunc (ZMod p))
        = algebraMap (ZMod p)[X] (RatFunc (ZMod p)) (X ^ p - X) := by
      simp only [map_sub, map_pow, RatFunc.algebraMap_X]
    rw [this]
    exact RatFunc.algebraMap_ne_zero
      (FiniteField.X_pow_card_sub_X_ne_zero _ (Fact.out : p.Prime).one_lt)
  have hx : lam a b * RatFunc.X ^ p ≠ lam a b * RatFunc.X := fun h =>
    hXne (by rw [mul_left_cancel₀ hl0 h, sub_self])
  have hnum : algebraMap (ZMod p)[X] (RatFunc (ZMod p)) (countNum a b)
      = lam a b * (lam a b ^ (p / 2) + 1) ^ 2
        - (RatFunc.X ^ p + RatFunc.X) * (RatFunc.X ^ p - RatFunc.X) ^ 2 := by
    simp only [countNum, map_sub, map_mul, map_pow, map_add, map_one, RatFunc.algebraMap_X,
      ← lam_eq_cubic]
  have hden : algebraMap (ZMod p)[X] (RatFunc (ZMod p)) ((X ^ p - X) ^ 2)
      = (RatFunc.X ^ p - RatFunc.X) ^ 2 := by
    simp only [map_sub, map_pow, RatFunc.algebraMap_X]
  rw [sub_eq_add_neg, neg_basePt]
  unfold startPt
  rw [ptHeight_add_negBasePt h2 hΔ _ hx, ← rfHeight_countNum a b h2 hΔ hp5, hnum, hden]
  congr 1
  have hd : lam a b * RatFunc.X ^ p - lam a b * RatFunc.X ≠ 0 := sub_ne_zero.mpr hx
  field_simp
  ring

omit hΔ hp5 in
/-- The number of square roots of `c` in `𝔽_p`. -/
theorem card_sq_eq (c : ZMod p) : (univ.filter fun y : ZMod p => y ^ 2 = c).card
    = if c = 0 then 1 else if c ^ (p / 2) = 1 then 2 else 0 := by
  split_ifs with h0 h1
  · rw [card_eq_one]
    refine ⟨0, ?_⟩
    ext y
    simp [h0]
  · obtain ⟨r, hr⟩ := (ZMod.euler_criterion p h0).mpr h1
    have hr0 : r ≠ 0 := by
      rintro rfl
      exact h0 (by rw [hr, mul_zero])
    have hne : r ≠ -r := by
      intro h
      have : 2 * r = 0 := by linear_combination h
      rcases mul_eq_zero.mp this with h' | h'
      · exact h2 h'
      · exact hr0 h'
    have hset : (univ.filter fun y : ZMod p => y ^ 2 = c) = {r, -r} := by
      ext y
      simp only [mem_filter, mem_univ, true_and, mem_insert, mem_singleton]
      rw [hr, ← sq, sq_eq_sq_iff_eq_or_eq_neg]
    rw [hset, card_pair hne]
  · rw [card_eq_zero, filter_eq_empty_iff]
    intro y _ hy
    exact h1 ((ZMod.euler_criterion p h0).mp ⟨y, by rw [← hy, sq]⟩)

omit hp5 in
/-- **The number of points of `E` over `𝔽_p`** is `∑_j expR j + 1`. -/
theorem card_point :
    Nat.card (shortW a b).toAffine.Point = ∑ j : ZMod p, expR a b j + 1 := by
  have hΔ' : (shortW a b).Δ ≠ 0 := by
    rw [shortW_Δ]
    have h16 : (-16 : ZMod p) ≠ 0 := by
      have : (-16 : ZMod p) = -(2 * 2 * 2 * 2) := by norm_num
      rw [this]
      exact neg_ne_zero.mpr (mul_ne_zero (mul_ne_zero (mul_ne_zero h2 h2) h2) h2)
    exact mul_ne_zero h16 hΔ
  have hns : ∀ x y : ZMod p, (shortW a b).toAffine.Nonsingular x y ↔ y ^ 2 = cubicVal a b x := by
    intro x y
    rw [← Affine.equation_iff_nonsingular_of_Δ_ne_zero hΔ', Affine.equation_iff]
    simp [shortW, cubicVal]
  let e : (shortW a b).toAffine.Point ≃
      Option {xy : ZMod p × ZMod p // (shortW a b).toAffine.Nonsingular xy.1 xy.2} :=
    { toFun := fun P => match P with
        | .zero => none
        | .some x y h => some ⟨(x, y), h⟩
      invFun := fun o => match o with
        | none => .zero
        | some xy => .some xy.1.1 xy.1.2 xy.2
      left_inv := by
        rintro (_ | ⟨x, y, h⟩) <;> rfl
      right_inv := by
        rintro (_ | ⟨⟨x, y⟩, h⟩) <;> rfl }
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_option, Fintype.card_subtype]
  congr 1
  have hfilter : (univ.filter fun xy : ZMod p × ZMod p =>
        (shortW a b).toAffine.Nonsingular xy.1 xy.2)
      = univ.filter fun xy : ZMod p × ZMod p => xy.2 ^ 2 = cubicVal a b xy.1 :=
    filter_congr fun xy _ => hns xy.1 xy.2
  rw [hfilter, card_filter, Fintype.sum_prod_type]
  refine sum_congr rfl fun x _ => ?_
  rw [← card_filter]
  refine (card_sq_eq h2 (cubicVal a b x)).trans ?_
  unfold expR expG
  split_ifs <;> rfl

/-- **The Hasse bound** for `y² = x³ + ax + b` over `𝔽_p`, `p ≥ 5`. -/
theorem hasse_short : ((Nat.card (shortW a b).toAffine.Point : ℤ) - (p + 1)) ^ 2 ≤ 4 * p := by
  obtain ⟨d, hd⟩ : ∃ d : ℤ → ℤ, d = fun n =>
      (ptHeight (startPt h2 hΔ hp5 + n • basePt h2 hΔ) : ℤ) := ⟨_, rfl⟩
  have hrec : ∀ n, d (n - 1) + d (n + 1) = 2 * d n + 2 := by
    intro n
    have h := ptHeight_sub_add h2 hΔ (startPt h2 hΔ hp5 + n • basePt h2 hΔ)
    have e1 : startPt h2 hΔ hp5 + (n - 1) • basePt h2 hΔ
        = startPt h2 hΔ hp5 + n • basePt h2 hΔ - basePt h2 hΔ := by
      rw [sub_zsmul, one_zsmul]
      abel
    have e2 : startPt h2 hΔ hp5 + (n + 1) • basePt h2 hΔ
        = startPt h2 hΔ hp5 + n • basePt h2 hΔ + basePt h2 hΔ := by
      rw [add_zsmul, one_zsmul]
      abel
    rw [hd]
    simp only
    rw [e1, e2]
    exact_mod_cast h
  have h0 : d 0 = p := by
    rw [hd]
    simp only
    rw [zero_zsmul, add_zero, ptHeight_startPt]
  have hm1 : d (-1) = (∑ j : ZMod p, expR a b j : ℕ) + 1 := by
    rw [hd]
    simp only
    rw [neg_zsmul, one_zsmul, ← sub_eq_add_neg, ptHeight_startPt_sub]
    push_cast
    rfl
  have hc : d (-1) - d 0 - 1 = (∑ j : ZMod p, expR a b j : ℕ) - (p : ℤ) := by
    rw [hm1, h0]
    ring
  have hp := (Fact.out : p.Prime)
  have key := sq_le_of_degree (d := d) (fun n => by rw [hd]; exact Int.natCast_nonneg _) hrec h0
    hc (prime_ne_mul_succ hp (by omega))
  rw [card_point h2 hΔ]
  have e : (((∑ j : ZMod p, expR a b j + 1 : ℕ) : ℤ) - (p + 1))
      = ((∑ j : ZMod p, expR a b j : ℕ) : ℤ) - p := by
    push_cast
    ring
  rw [e]
  exact key

end Azurite.ECPP.Manin

namespace Azurite.ECPP

/-- **The Hasse bound holds.** -/
theorem hasseBound : HasseBound := fun _ _ hp5 _ _ hΔ =>
  Manin.hasse_short (Manin.zmod_two_ne_zero hp5) hΔ hp5

end Azurite.ECPP
