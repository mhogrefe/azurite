/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter5.Section7
import Mathlib.Analysis.SpecialFunctions.Log.Summable

/-!
# DLMF §5.8: infinite products

Formalizations of <https://dlmf.nist.gov/5.8>.

* 5.8.1, `Γ(z) = lim_{k→∞} k! kᶻ / (z(z + 1)⋯(z + k))` (`dlmf_5_8_1`): Mathlib's
  `Complex.GammaSeq_tendsto_Gamma`. The reciprocal `1/Γ(z)` is the limit of the reciprocal
  sequence for every `z`, poles included (`tendsto_inv_GammaSeq`).
* 5.8.2, `1/Γ(z) = z e^{γz} ∏_{k≥1} (1 + z/k) e^{−z/k}` (`dlmf_5_8_2`): the partial products
  equal `(1/GammaSeq) · exp(z(γ − (Hₙ − ln n)))` (`weierstrass_partial_eq`); the product
  converges unconditionally (`multipliable_weierstrassFactor`, factors `1 + O(k⁻²)`).
* 5.8.3, `|Γ(x)/Γ(x + iy)|² = ∏_{k≥0} (1 + y²/(x + k)²)`, `x ≠ 0, −1, …` (`dlmf_5_8_3`).
* 5.8.4–5.8.5, if `∑ aᵢ = ∑ bᵢ` then
  `∏_{k≥0} ∏ᵢ (aᵢ + k)/(bᵢ + k) = ∏ᵢ Γ(bᵢ) / ∏ᵢ Γ(aᵢ)` (`dlmf_5_8_5`). DLMF assumes no `bᵢ` is a
  pole; with Mathlib's conventions (`Γ = 0` at the poles, `x/0 = 0`) the identity holds without
  that hypothesis. The factors are `1 + O(k⁻²)` by a second-order product estimate
  (`norm_prod_one_add_sub_one_sub_sum_le`).

Each product is stated both as the limit of its partial products and as an unconditionally
convergent `tprod`.
-/

open Complex Filter Topology Set Finset
open scoped Real Nat

namespace Azurite.DLMF

local notation "γ" => Real.eulerMascheroniConstant

/-! ### 5.8.1 -/

/-- DLMF 5.8.1 (Euler's limit formula). -/
theorem dlmf_5_8_1 (z : ℂ) :
    Tendsto (fun k : ℕ => (k ! : ℂ) * (k : ℂ) ^ z / ∏ j ∈ range (k + 1), (z + j)) atTop
      (𝓝 (Gamma z)) := by
  refine (GammaSeq_tendsto_Gamma z).congr fun k => ?_
  simp only [GammaSeq]
  ring

/-- The reciprocal of Euler's sequence tends to `1/Γ(z)` for every `z`, poles included. -/
theorem tendsto_inv_GammaSeq (z : ℂ) :
    Tendsto (fun n => (GammaSeq z n)⁻¹) atTop (𝓝 (Gamma z)⁻¹) := by
  by_cases h : Gamma z = 0
  · obtain ⟨m, rfl⟩ := (Gamma_eq_zero_iff z).mp h
    rw [h, inv_zero]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop m] with n hn
    have h0 : ∏ j ∈ range (n + 1), (-(m : ℂ) + j) = 0 :=
      prod_eq_zero (i := m) (mem_range.mpr (by omega)) (by ring)
    simp [GammaSeq, h0]
  · exact (GammaSeq_tendsto_Gamma z).inv₀ h

/-! ### 5.8.2 -/

/-- The factor `(1 + z/(k + 1)) e^{−z/(k + 1)}` of 5.8.2 (index shifted to start at `0`). -/
noncomputable def weierstrassFactor (z : ℂ) (k : ℕ) : ℂ :=
  (1 + z / ((k : ℂ) + 1)) * exp (-(z / ((k : ℂ) + 1)))

theorem prod_range_natCast_add_eq (z : ℂ) (n : ℕ) :
    ∏ k ∈ range n, (z + ((k : ℂ) + 1)) = (∏ k ∈ range n, (1 + z / ((k : ℂ) + 1))) * n ! := by
  rw [← prod_range_add_one_eq_factorial, Nat.cast_prod, ← prod_mul_distrib]
  refine prod_congr rfl fun k _ => ?_
  have hk : ((k : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
  push_cast
  field_simp
  ring

/-- The partial products of 5.8.2 in terms of Euler's sequence. -/
theorem weierstrass_partial_eq (z : ℂ) {n : ℕ} (hn : n ≠ 0) :
    z * exp (γ * z) * ∏ k ∈ range n, weierstrassFactor z k =
      (GammaSeq z n)⁻¹ * exp (z * (γ - ((harmonic n : ℝ) - Real.log n))) := by
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  have hfac : (n ! : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  have hlog : Complex.log (n : ℂ) = (Real.log n : ℂ) := by
    rw [ofReal_log (Nat.cast_nonneg n)]; rfl
  have hH : ∑ k ∈ range n, -(z / ((k : ℂ) + 1)) = -(z * (harmonic n : ℝ)) := by
    rw [harmonic, Rat.cast_sum, ofReal_sum, mul_sum, ← sum_neg_distrib]
    refine sum_congr rfl fun k _ => ?_
    push_cast
    ring
  simp only [weierstrassFactor, prod_mul_distrib, ← exp_sum, hH]
  rw [GammaSeq, inv_div, prod_range_succ']
  simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, add_zero]
  rw [prod_range_natCast_add_eq, cpow_def_of_ne_zero hn', hlog]
  set A := ∏ k ∈ range n, (1 + z / ((k : ℂ) + 1))
  have e1 : A * (n ! : ℂ) * z / (exp ((Real.log n : ℂ) * z) * n !) =
      z * A * exp (-((Real.log n : ℂ) * z)) := by
    rw [exp_neg]; field_simp
  rw [e1]
  have e2 : exp (γ * z) * exp (-(z * (harmonic n : ℝ))) =
      exp (-((Real.log n : ℂ) * z)) * exp (z * (γ - ((harmonic n : ℝ) - Real.log n))) := by
    rw [← exp_add, ← exp_add]; push_cast; ring_nf
  calc z * exp (γ * z) * (A * exp (-(z * (harmonic n : ℝ))))
      = z * A * (exp (γ * z) * exp (-(z * (harmonic n : ℝ)))) := by ring
    _ = _ := by rw [e2]; ring

/-- The partial products of 5.8.2 converge to `1/Γ(z)`. -/
theorem tendsto_weierstrass_partial (z : ℂ) :
    Tendsto (fun n => z * exp (γ * z) * ∏ k ∈ range n, weierstrassFactor z k) atTop
      (𝓝 (Gamma z)⁻¹) := by
  have hlim : Tendsto (fun n : ℕ => exp (z * (γ - ((harmonic n : ℝ) - Real.log n)))) atTop
      (𝓝 1) := by
    have h1 : Tendsto (fun n : ℕ => ((harmonic n : ℝ) - Real.log n : ℝ)) atTop (𝓝 γ) :=
      Real.tendsto_harmonic_sub_log
    have h2 := ((continuous_ofReal.tendsto _).comp h1)
    have h3 : Tendsto (fun n : ℕ => exp (z * (γ - (((harmonic n : ℝ) - Real.log n : ℝ) : ℂ))))
        atTop (𝓝 (exp (z * (γ - γ)))) :=
      ((continuous_exp.tendsto _).comp
        ((tendsto_const_nhds.sub h2).const_mul z))
    simpa using h3
  have := (tendsto_inv_GammaSeq z).mul hlim
  rw [mul_one] at this
  refine this.congr' ?_
  filter_upwards [eventually_ne_atTop 0] with n hn
  exact (weierstrass_partial_eq z hn).symm

theorem norm_weierstrassFactor_sub_one_le (z : ℂ) {k : ℕ} (hk : ‖z‖ ≤ (k : ℝ) + 1) :
    ‖weierstrassFactor z k - 1‖ ≤ Real.exp 1 * ‖z‖ ^ 2 * (1 / ((k : ℝ) + 1) ^ 2) := by
  set w := z / ((k : ℂ) + 1) with hw
  have hk0 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hnw : ‖w‖ = ‖z‖ / ((k : ℝ) + 1) := by
    rw [hw, norm_div]; congr 1; exact_mod_cast Complex.norm_natCast (k + 1)
  have hw1 : ‖w‖ ≤ 1 := by rw [hnw, div_le_one hk0]; exact hk
  have heq : weierstrassFactor z k - 1 = -(exp (-w) * (exp w - 1 - w)) := by
    simp only [weierstrassFactor, ← hw]
    have : exp (-w) * exp w = 1 := by rw [← exp_add]; simp
    linear_combination this
  rw [heq, norm_neg, norm_mul]
  have he : ‖exp (-w)‖ ≤ Real.exp 1 := by
    rw [norm_exp]
    exact Real.exp_le_exp.mpr ((re_le_norm _).trans (by rw [norm_neg]; exact hw1))
  calc ‖exp (-w)‖ * ‖exp w - 1 - w‖ ≤ Real.exp 1 * ‖w‖ ^ 2 :=
        mul_le_mul he (norm_exp_sub_one_sub_id_le hw1) (norm_nonneg _) (Real.exp_pos 1).le
    _ = _ := by rw [hnw, div_pow, one_div, div_eq_mul_inv]; ring

theorem summable_one_div_natCast_add_one_sq :
    Summable (fun k : ℕ => 1 / ((k : ℝ) + 1) ^ 2) := by
  have := (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr one_lt_two)
  simpa using this

theorem multipliable_weierstrassFactor (z : ℂ) : Multipliable (weierstrassFactor z) := by
  have hs : Summable (fun k => weierstrassFactor z k - 1) := by
    refine Summable.of_norm_bounded_eventually_nat
      (summable_one_div_natCast_add_one_sq.mul_left (Real.exp 1 * ‖z‖ ^ 2)) ?_
    obtain ⟨N, hN⟩ := exists_nat_ge ‖z‖
    filter_upwards [eventually_ge_atTop N] with k hk
    refine norm_weierstrassFactor_sub_one_le z ?_
    have : (N : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  simpa using Complex.multipliable_one_add_of_summable hs

/-- If a product converges unconditionally, its value is the limit of the partial products. -/
theorem tprod_eq_of_tendsto_prod_range {f : ℕ → ℂ} (hf : Multipliable f) {a : ℂ}
    (h : Tendsto (fun n => ∏ k ∈ range n, f k) atTop (𝓝 a)) : ∏' k, f k = a :=
  tendsto_nhds_unique hf.hasProd.tendsto_prod_nat h

/-- DLMF 5.8.2 (Weierstrass's product): `1/Γ(z) = z e^{γz} ∏_{k≥1} (1 + z/k) e^{−z/k}`, with
the product unconditionally convergent. -/
theorem dlmf_5_8_2 (z : ℂ) :
    Multipliable (fun k : ℕ => (1 + z / ((k : ℂ) + 1)) * exp (-(z / ((k : ℂ) + 1)))) ∧
      1 / Gamma z =
        z * exp (γ * z) * ∏' k : ℕ, (1 + z / ((k : ℂ) + 1)) * exp (-(z / ((k : ℂ) + 1))) := by
  refine ⟨multipliable_weierstrassFactor z, ?_⟩
  have hm := multipliable_weierstrassFactor z
  have h := hm.hasProd.tendsto_prod_nat.const_mul (z * exp (γ * z))
  rw [one_div]
  exact tendsto_nhds_unique (tendsto_weierstrass_partial z) h

/-! ### 5.8.3 -/

theorem ofReal_add_I_mul_ne_neg_nat {x : ℝ} (hx : ∀ m : ℕ, x ≠ -m) (y : ℝ) (m : ℕ) :
    (x : ℂ) + I * y ≠ -m := by
  intro h
  have hre := congrArg re h
  simp at hre
  exact hx m hre

theorem normSq_add_I_mul_div (a y : ℝ) (ha : a ≠ 0) :
    normSq ((a : ℂ) + I * y) / normSq (a : ℂ) = 1 + y ^ 2 / a ^ 2 := by
  simp only [normSq_apply, add_re, ofReal_re, mul_re, I_re, ofReal_im, I_im, add_im, ofReal_im,
    mul_im]
  field_simp
  ring

/-- The partial products of 5.8.3 in terms of Euler's sequence. -/
theorem partial_5_8_3_eq {x : ℝ} (hx : ∀ m : ℕ, x ≠ -m) (y : ℝ) {n : ℕ} (hn : n ≠ 0) :
    ∏ k ∈ range (n + 1), (1 + y ^ 2 / (x + k) ^ 2) =
      ‖GammaSeq (x : ℂ) n / GammaSeq ((x : ℂ) + I * y) n‖ ^ 2 := by
  have hn0 : 0 < n := Nat.pos_of_ne_zero hn
  have hxk : ∀ k : ℕ, (x : ℂ) + k ≠ 0 := fun k h => hx k (by
    have := congrArg re h; simp at this; linarith)
  have hxk' : ∀ k : ℕ, (x : ℝ) + k ≠ 0 := fun k h => hxk k (by exact_mod_cast h)
  have hzk : ∀ k : ℕ, (x : ℂ) + I * y + k ≠ 0 := fun k h =>
    ofReal_add_I_mul_ne_neg_nat hx y k (by linear_combination h)
  have hpx : (∏ j ∈ range (n + 1), ((x : ℂ) + j)) ≠ 0 := prod_ne_zero_iff.mpr fun k _ => hxk k
  have hpz : (∏ j ∈ range (n + 1), ((x : ℂ) + I * y + j)) ≠ 0 :=
    prod_ne_zero_iff.mpr fun k _ => hzk k
  have hcx : ((n : ℂ) ^ (x : ℂ)) ≠ 0 := by
    rw [← norm_ne_zero_iff, norm_natCast_cpow_of_pos hn0]; positivity
  have hcz : ((n : ℂ) ^ ((x : ℂ) + I * y)) ≠ 0 := by
    rw [← norm_ne_zero_iff, norm_natCast_cpow_of_pos hn0]; positivity
  have hnorm : ‖(n : ℂ) ^ (x : ℂ)‖ = ‖(n : ℂ) ^ ((x : ℂ) + I * y)‖ := by
    rw [norm_natCast_cpow_of_pos hn0, norm_natCast_cpow_of_pos hn0]; simp
  have hfac : (n ! : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  have hdiv : GammaSeq (x : ℂ) n / GammaSeq ((x : ℂ) + I * y) n =
      (n : ℂ) ^ (x : ℂ) / (n : ℂ) ^ ((x : ℂ) + I * y) *
        ((∏ j ∈ range (n + 1), ((x : ℂ) + I * y + j)) / ∏ j ∈ range (n + 1), ((x : ℂ) + j)) := by
    simp only [GammaSeq]
    field_simp
  rw [hdiv, norm_mul, norm_div _ ((n : ℂ) ^ ((x : ℂ) + I * y)), hnorm,
    div_self (norm_ne_zero_iff.mpr hcz), one_mul, ← normSq_eq_norm_sq, map_div₀,
    map_prod, map_prod, ← prod_div_distrib]
  refine prod_congr rfl fun k _ => ?_
  have := normSq_add_I_mul_div (x + k) y (hxk' k)
  push_cast at this
  rw [show (x : ℂ) + I * y + k = (x : ℂ) + k + I * y by ring, this]

/-- The partial products of 5.8.3 converge to `|Γ(x)/Γ(x + iy)|²`. -/
theorem tendsto_partial_5_8_3 {x : ℝ} (hx : ∀ m : ℕ, x ≠ -m) (y : ℝ) :
    Tendsto (fun n => ∏ k ∈ range n, (1 + y ^ 2 / (x + k) ^ 2)) atTop
      (𝓝 (‖Gamma x / Gamma ((x : ℂ) + I * y)‖ ^ 2)) := by
  have hG : Gamma ((x : ℂ) + I * y) ≠ 0 := Gamma_ne_zero (ofReal_add_I_mul_ne_neg_nat hx y)
  have h := ((GammaSeq_tendsto_Gamma (x : ℂ)).div (GammaSeq_tendsto_Gamma _) hG).norm.pow 2
  refine (tendsto_add_atTop_iff_nat 1).mp (h.congr' ?_)
  filter_upwards [eventually_ne_atTop 0] with n hn
  exact (partial_5_8_3_eq hx y hn).symm

theorem summable_5_8_3 {x : ℝ} (hx : ∀ m : ℕ, x ≠ -m) (y : ℝ) :
    Summable (fun k : ℕ => y ^ 2 / (x + k) ^ 2) := by
  have hx' : (x : ℂ) ∉ gammaPoles := by
    rw [not_mem_gammaPoles]
    intro m h
    exact hx m (by exact_mod_cast h)
  obtain ⟨r, hr, c, hc, hb⟩ := exists_norm_add_nat_ge hx'
  refine (summable_one_div_natCast_add_one_sq.mul_left (y ^ 2 / c ^ 2)).of_nonneg_of_le
    (fun k => by positivity) fun k => ?_
  have h1 := hb (x : ℂ) (Metric.mem_ball_self hr) k
  have h2 : ‖(x : ℂ) + k‖ = |x + k| := by
    rw [show (x : ℂ) + k = ((x + k : ℝ) : ℂ) by push_cast; ring, norm_real, Real.norm_eq_abs]
  rw [h2] at h1
  have hck : 0 < c * ((k : ℝ) + 1) := by positivity
  have h3 : (c * ((k : ℝ) + 1)) ^ 2 ≤ (x + k) ^ 2 := by
    rw [← sq_abs (x + k)]; exact pow_le_pow_left₀ hck.le h1 2
  calc y ^ 2 / (x + k) ^ 2 ≤ y ^ 2 / (c * ((k : ℝ) + 1)) ^ 2 :=
        div_le_div_of_nonneg_left (sq_nonneg y) (by positivity) h3
    _ = _ := by rw [mul_pow]; field_simp

/-- DLMF 5.8.3: `|Γ(x)/Γ(x + iy)|² = ∏_{k≥0} (1 + y²/(x + k)²)`, `x ≠ 0, −1, …`, with the
product unconditionally convergent. -/
theorem dlmf_5_8_3 {x : ℝ} (hx : ∀ m : ℕ, x ≠ -m) (y : ℝ) :
    Multipliable (fun k : ℕ => 1 + y ^ 2 / (x + k) ^ 2) ∧
      ‖Gamma x / Gamma ((x : ℂ) + I * y)‖ ^ 2 = ∏' k : ℕ, (1 + y ^ 2 / (x + k) ^ 2) := by
  have hm := Real.multipliable_one_add_of_summable (summable_5_8_3 hx y)
  exact ⟨hm, tendsto_nhds_unique (tendsto_partial_5_8_3 hx y) hm.hasProd.tendsto_prod_nat⟩

/-! ### 5.8.4–5.8.5 -/

/-- First-order estimate: `|∏(1 + uᵢ) − 1| ≤ e^T − 1`, `T = ∑ |uᵢ|` (Mathlib). The second-order
version: `|∏(1 + uᵢ) − 1 − ∑ uᵢ| ≤ e^T − 1 − T`. -/
theorem norm_prod_one_add_sub_one_sub_sum_le {ι : Type*} (s : Finset ι) (u : ι → ℂ) :
    ‖∏ i ∈ s, (1 + u i) - 1 - ∑ i ∈ s, u i‖ ≤
      Real.exp (∑ i ∈ s, ‖u i‖) - 1 - ∑ i ∈ s, ‖u i‖ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj IH =>
    rw [prod_insert hj, sum_insert hj, sum_insert hj, Real.exp_add]
    set P := ∏ i ∈ s, (1 + u i)
    set S := ∑ i ∈ s, u i
    set T := ∑ i ∈ s, ‖u i‖
    have h1 := s.norm_prod_one_add_sub_one_le u
    have heq : (1 + u j) * P - 1 - (u j + S) = (P - 1 - S) + u j * (P - 1) := by ring
    have ht : 1 + ‖u j‖ ≤ Real.exp ‖u j‖ := by linarith [Real.add_one_le_exp ‖u j‖]
    have hT : 1 ≤ Real.exp T := Real.one_le_exp (sum_nonneg fun i _ => norm_nonneg _)
    calc ‖(1 + u j) * P - 1 - (u j + S)‖ ≤ ‖P - 1 - S‖ + ‖u j‖ * ‖P - 1‖ := by
          rw [heq]; exact (norm_add_le _ _).trans (by rw [norm_mul])
      _ ≤ (Real.exp T - 1 - T) + ‖u j‖ * (Real.exp T - 1) := by
          gcongr
      _ ≤ Real.exp ‖u j‖ * Real.exp T - 1 - (‖u j‖ + T) := by
          nlinarith [norm_nonneg (u j)]

/-- The factors of 5.8.5. -/
noncomputable def ratioFactor {m : ℕ} (a b : Fin m → ℂ) (k : ℕ) : ℂ :=
  ∏ i, (a i + k) / (b i + k)

/-- The partial products of 5.8.5 in terms of Euler's sequence. -/
theorem ratio_partial_eq {m : ℕ} (a b : Fin m → ℂ) (h : ∑ i, a i = ∑ i, b i) {n : ℕ}
    (hn : n ≠ 0) :
    ∏ k ∈ range (n + 1), ratioFactor a b k = ∏ i, GammaSeq (b i) n * (GammaSeq (a i) n)⁻¹ := by
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  have hfac : (n ! : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  have hterm : ∀ i, GammaSeq (b i) n * (GammaSeq (a i) n)⁻¹ =
      exp (Complex.log n * (b i - a i)) *
        ((∏ k ∈ range (n + 1), (a i + k)) / ∏ k ∈ range (n + 1), (b i + k)) := by
    intro i
    simp only [GammaSeq, inv_div, cpow_def_of_ne_zero hn', mul_sub, exp_sub]
    have := exp_ne_zero (Complex.log n * a i)
    field_simp
  simp only [hterm, prod_mul_distrib, ← exp_sum, ← mul_sum, sum_sub_distrib, h, sub_self,
    mul_zero, exp_zero, one_mul, ratioFactor]
  rw [Finset.prod_comm]
  exact prod_congr rfl fun i _ => prod_div_distrib _ _

/-- The partial products of 5.8.5 converge. -/
theorem tendsto_ratio_partial {m : ℕ} (a b : Fin m → ℂ) (h : ∑ i, a i = ∑ i, b i) :
    Tendsto (fun n => ∏ k ∈ range n, ratioFactor a b k) atTop
      (𝓝 ((∏ i, Gamma (b i)) / ∏ i, Gamma (a i))) := by
  have hl : Tendsto (fun n => ∏ i, GammaSeq (b i) n * (GammaSeq (a i) n)⁻¹) atTop
      (𝓝 (∏ i, Gamma (b i) * (Gamma (a i))⁻¹)) :=
    tendsto_finsetProd _ fun i _ =>
      (GammaSeq_tendsto_Gamma (b i)).mul (tendsto_inv_GammaSeq (a i))
  rw [← prod_div_distrib]
  simp only [← div_eq_mul_inv] at hl
  refine (tendsto_add_atTop_iff_nat 1).mp (hl.congr' ?_)
  filter_upwards [eventually_ne_atTop 0] with n hn
  rw [ratio_partial_eq a b h hn]
  simp only [div_eq_mul_inv]

/-- The factors of 5.8.5 are `1 + O(k⁻²)`: with `M = ∑ |aᵢ − bᵢ|`, `B = ∑ |bᵢ|` and
`k ≥ max(1, 2B, 2M)`, `|∏ᵢ (aᵢ + k)/(bᵢ + k) − 1| ≤ (4M² + 2MB)/k²`. -/
theorem norm_ratioFactor_sub_one_le {m : ℕ} (a b : Fin m → ℂ) (h : ∑ i, a i = ∑ i, b i)
    {k : ℕ} (hk1 : 1 ≤ k) (hkb : 2 * (∑ i, ‖b i‖) ≤ k)
    (hkM : 2 * (∑ i, ‖a i - b i‖) ≤ k) :
    ‖ratioFactor a b k - 1‖ ≤
      (4 * (∑ i, ‖a i - b i‖) ^ 2 + 2 * (∑ i, ‖a i - b i‖) * ∑ i, ‖b i‖) *
        (1 / (k : ℝ) ^ 2) := by
  set M := ∑ i, ‖a i - b i‖ with hM
  set B := ∑ i, ‖b i‖ with hB
  set K : ℝ := (k : ℝ) with hKdef
  have hK : 0 < K := by rw [hKdef]; exact_mod_cast hk1
  have hB0 : 0 ≤ B := sum_nonneg fun i _ => norm_nonneg _
  have hM0 : 0 ≤ M := sum_nonneg fun i _ => norm_nonneg _
  have hbi : ∀ i, ‖b i‖ ≤ B := fun i =>
    single_le_sum (f := fun i => ‖b i‖) (fun i _ => norm_nonneg _) (mem_univ i)
  have hkn : ‖(k : ℂ)‖ = K := by rw [hKdef]; exact Complex.norm_natCast k
  have hbk : ∀ i, K / 2 ≤ ‖b i + k‖ := fun i => by
    have := norm_sub_le (b i + k) (b i)
    rw [add_sub_cancel_left, hkn] at this
    linarith [hbi i]
  have hne : ∀ i, b i + k ≠ 0 := fun i h0 => by
    have := hbk i; rw [h0, norm_zero] at this; linarith
  set u : Fin m → ℂ := fun i => (a i - b i) / (b i + k) with hu
  have hfac : ratioFactor a b k = ∏ i, (1 + u i) := by
    refine prod_congr rfl fun i _ => ?_
    have := hne i
    simp only [hu]
    field_simp
    ring
  have hun : ∀ i, ‖u i‖ ≤ ‖a i - b i‖ * (2 / K) := fun i => by
    simp only [hu, norm_div]
    rw [div_le_iff₀ (by linarith [hbk i])]
    have := hbk i
    have h2 : 0 ≤ ‖a i - b i‖ := norm_nonneg _
    calc ‖a i - b i‖ = ‖a i - b i‖ * (2 / K) * (K / 2) := by field_simp
      _ ≤ _ := by gcongr
  set T := ∑ i, ‖u i‖ with hT
  have hT0 : 0 ≤ T := sum_nonneg fun i _ => norm_nonneg _
  have hTle : T ≤ M * (2 / K) := by
    rw [hM, sum_mul]; exact sum_le_sum fun i _ => hun i
  have hT1 : T ≤ 1 := by
    refine hTle.trans ?_
    rw [mul_div_assoc', div_le_one hK]; linarith
  have hD : ∑ i, (a i - b i) = 0 := by rw [sum_sub_distrib, h, sub_self]
  have hsum : ∑ i, u i = ∑ i, (-((a i - b i) * b i) / ((k : ℂ) * (b i + k))) := by
    have hk0 : (k : ℂ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
    have : ∑ i, u i = ∑ i, u i - ∑ i, (a i - b i) / (k : ℂ) := by
      rw [← sum_div, hD, zero_div, sub_zero]
    rw [this, ← sum_sub_distrib]
    refine sum_congr rfl fun i _ => ?_
    have := hne i
    simp only [hu]
    field_simp
    ring
  have hsumn : ‖∑ i, u i‖ ≤ 2 * M * B * (1 / K ^ 2) := by
    rw [hsum]
    refine (norm_sum_le _ _).trans ?_
    have : ∀ i, ‖-((a i - b i) * b i) / ((k : ℂ) * (b i + k))‖ ≤
        ‖a i - b i‖ * (2 * B * (1 / K ^ 2)) := fun i => by
      rw [norm_div, norm_neg, norm_mul, norm_mul, hkn]
      have h1 := hbk i
      have h2 : 0 ≤ ‖a i - b i‖ := norm_nonneg _
      rw [div_le_iff₀ (mul_pos hK (by linarith))]
      calc ‖a i - b i‖ * ‖b i‖ ≤ ‖a i - b i‖ * B := by gcongr; exact hbi i
        _ = ‖a i - b i‖ * (2 * B * (1 / K ^ 2)) * (K * (K / 2)) := by field_simp
        _ ≤ _ := by gcongr
    refine (sum_le_sum fun i _ => this i).trans ?_
    rw [← sum_mul, ← hM]; ring_nf; rfl
  have h2 := norm_prod_one_add_sub_one_sub_sum_le univ u
  have h3 : Real.exp T - 1 - T ≤ T ^ 2 := by
    have := Real.abs_exp_sub_one_sub_id_le (x := T) (by rw [abs_of_nonneg hT0]; exact hT1)
    exact (le_abs_self _).trans this
  have h4 : T ^ 2 ≤ 4 * M ^ 2 * (1 / K ^ 2) := by
    calc T ^ 2 ≤ (M * (2 / K)) ^ 2 := pow_le_pow_left₀ hT0 hTle 2
      _ = _ := by field_simp; ring
  rw [hfac]
  calc ‖∏ i, (1 + u i) - 1‖ ≤ ‖∏ i, (1 + u i) - 1 - ∑ i, u i‖ + ‖∑ i, u i‖ := by
        have := norm_add_le (∏ i, (1 + u i) - 1 - ∑ i, u i) (∑ i, u i)
        rwa [sub_add_cancel] at this
    _ ≤ 4 * M ^ 2 * (1 / K ^ 2) + 2 * M * B * (1 / K ^ 2) := by
        rw [← hT] at h2; linarith
    _ = _ := by ring

theorem multipliable_ratioFactor {m : ℕ} (a b : Fin m → ℂ) (h : ∑ i, a i = ∑ i, b i) :
    Multipliable (ratioFactor a b) := by
  have hs : Summable (fun k => ratioFactor a b k - 1) := by
    refine Summable.of_norm_bounded_eventually_nat
      ((Real.summable_one_div_nat_pow.mpr one_lt_two).mul_left
        (4 * (∑ i, ‖a i - b i‖) ^ 2 + 2 * (∑ i, ‖a i - b i‖) * ∑ i, ‖b i‖)) ?_
    obtain ⟨N, hN⟩ := exists_nat_ge (1 + 2 * ∑ i, ‖b i‖ + 2 * ∑ i, ‖a i - b i‖)
    have hB0 : 0 ≤ ∑ i, ‖b i‖ := sum_nonneg fun i _ => norm_nonneg _
    have hM0 : 0 ≤ ∑ i, ‖a i - b i‖ := sum_nonneg fun i _ => norm_nonneg _
    filter_upwards [eventually_ge_atTop N] with k hk
    have hk' : (N : ℝ) ≤ k := by exact_mod_cast hk
    refine norm_ratioFactor_sub_one_le a b h ?_ (by linarith) (by linarith)
    exact_mod_cast (by linarith : (1 : ℝ) ≤ k)
  simpa using Complex.multipliable_one_add_of_summable hs

/-- DLMF 5.8.4–5.8.5: if `∑ᵢ aᵢ = ∑ᵢ bᵢ`, then
`∏_{k≥0} ∏ᵢ (aᵢ + k)/(bᵢ + k) = ∏ᵢ Γ(bᵢ) / ∏ᵢ Γ(aᵢ)`, with the product unconditionally
convergent. (DLMF's hypothesis that no `bᵢ` is a pole is not needed with Mathlib's conventions.) -/
theorem dlmf_5_8_5 {m : ℕ} (a b : Fin m → ℂ) (h : ∑ i, a i = ∑ i, b i) :
    Multipliable (fun k : ℕ => ∏ i, (a i + k) / (b i + k)) ∧
      ∏' k : ℕ, ∏ i, (a i + k) / (b i + k) = (∏ i, Gamma (b i)) / ∏ i, Gamma (a i) :=
  ⟨multipliable_ratioFactor a b h,
    tprod_eq_of_tendsto_prod_range (multipliable_ratioFactor a b h) (tendsto_ratio_partial a b h)⟩

end Azurite.DLMF
