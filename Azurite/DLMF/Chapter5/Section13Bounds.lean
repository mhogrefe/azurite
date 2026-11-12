/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter5.Section13Barnes
import Azurite.DLMF.Chapter5.Section6Ratio

/-!
# DLMF §5.13: uniform bounds for `1/(Γ(a + t)Γ(c − t))`, `t ∈ ℝ`

For Ramanujan's integral 5.13.4 we need `|1/(Γ(a + t)Γ(c − t))| ≤ M(1 + |t|)^{1−ℜ(a+c)+ρ}`
uniformly for `a` in a closed ball of radius `ρ` (`exists_bound_invGammaPair`).

* `Γ(v)/Γ(v + γ) = Γ(γ)⁻¹ ∫₀^∞ e^{−vu}(1 − e^{−u})^{γ−1} du` (`gamma_ratio_eq_integral'`) and
  `(1 − e^{−u})^{ℜγ−1} ≤ u^{ℜγ−1}eᵘ` give `|Γ(v)/Γ(v + γ)| ≤ |Γ(γ)⁻¹| Γ(ℜγ) (ℜv/2)^{−ℜγ}` for
  `ℜγ > 0`, `ℜv ≥ 2` (`norm_gamma_ratio_le'`).
* For general `γ` the ratio is shifted by `n` (`Gamma_add_nat_eq_prod`), giving
  `|Γ(x + α)/Γ(x + α + γ)| ≤ C(1 + x)^{−ℜγ}` uniformly (`norm_gamma_ratio_le_uniform`).
* Reflection turns `1/Γ(c − t)` into `Γ(1 − c + t) sin(π(c − t))/π` for large `t`
  (`inv_Gamma_eq_reflect`), and symmetrically for `t → −∞`.
-/

open Complex Filter Topology Set MeasureTheory
open scoped Real

namespace Azurite.DLMF

/-! ### The ratio for `ℜγ > 0` -/

/-- `Γ(v)/Γ(v + γ) = Γ(γ)⁻¹ ∫₀^∞ e^{−vu}(1 − e^{−u})^{γ−1} du`, `ℜv, ℜγ > 0`. -/
theorem gamma_ratio_eq_integral' {v γ : ℂ} (hv : 0 < v.re) (hγ : 0 < γ.re) :
    Gamma v / Gamma (v + γ) = (Gamma γ)⁻¹ *
      ∫ u in Ioi (0 : ℝ), cexp (-(v * u)) * ((1 - Real.exp (-u) : ℝ) : ℂ) ^ (γ - 1) := by
  have hbeta := Complex.Gamma_mul_Gamma_eq_betaIntegral hv hγ
  have hG0 : Gamma (v + γ) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by simp; linarith)
  have hGc : Gamma γ ≠ 0 := Complex.Gamma_ne_zero_of_re_pos hγ
  have hB : Complex.betaIntegral v γ = ∫ u in Ioi (0 : ℝ),
      cexp (-(v * u)) * ((1 - Real.exp (-u) : ℝ) : ℂ) ^ (γ - 1) := by
    rw [Complex.betaIntegral, intervalIntegral.integral_of_le zero_le_one,
      integral_Ioc_eq_integral_Ioo, integral_Ioo_eq_integral_exp_neg]
    refine setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
    simp only [Complex.real_smul]
    rw [cpow_pos_eq (Real.exp_pos _), Real.log_exp, ofReal_exp, ofReal_neg, ← mul_assoc,
      ← Complex.exp_add]
    push_cast
    congr 2
    ring
  rw [← hB, div_eq_iff hG0]
  field_simp
  linear_combination hbeta

theorem one_sub_exp_neg_bounds {u : ℝ} (hu : 0 < u) :
    u * Real.exp (-u) ≤ 1 - Real.exp (-u) ∧ 1 - Real.exp (-u) ≤ u := by
  constructor
  · have h := Real.add_one_le_exp u
    have he : Real.exp (-u) * Real.exp u = 1 := by rw [← Real.exp_add]; simp
    nlinarith [Real.exp_pos (-u)]
  · linarith [Real.add_one_le_exp (-u)]

/-- `(1 − e^{−u})^p ≤ u^p eᵘ` for `p > −1`. -/
theorem one_sub_exp_neg_rpow_le {u p : ℝ} (hu : 0 < u) (hp : -1 < p) :
    (1 - Real.exp (-u)) ^ p ≤ u ^ p * Real.exp u := by
  obtain ⟨h1, h2⟩ := one_sub_exp_neg_bounds hu
  have hpos : 0 < u * Real.exp (-u) := by positivity
  rcases le_total 0 p with hp0 | hp0
  · calc (1 - Real.exp (-u)) ^ p ≤ u ^ p := Real.rpow_le_rpow (hpos.le.trans h1) h2 hp0
      _ ≤ u ^ p * Real.exp u := le_mul_of_one_le_right (by positivity) (Real.one_le_exp hu.le)
  · calc (1 - Real.exp (-u)) ^ p ≤ (u * Real.exp (-u)) ^ p :=
          Real.rpow_le_rpow_of_nonpos hpos h1 hp0
      _ = u ^ p * Real.exp (-u * p) := by
          rw [Real.mul_rpow hu.le (Real.exp_pos _).le, ← Real.exp_mul]
      _ ≤ u ^ p * Real.exp u := by
          gcongr; nlinarith

/-- `|Γ(v)/Γ(v + γ)| ≤ |Γ(γ)⁻¹| Γ(ℜγ) (ℜv/2)^{−ℜγ}` for `ℜγ > 0`, `ℜv ≥ 2`. -/
theorem norm_gamma_ratio_le' {v γ : ℂ} (hv : 2 ≤ v.re) (hγ : 0 < γ.re) :
    ‖Gamma v / Gamma (v + γ)‖ ≤ ‖(Gamma γ)⁻¹‖ * Real.Gamma γ.re * (v.re / 2) ^ (-γ.re) := by
  have hv0 : 0 < v.re := by linarith
  have hX : 0 < v.re - 1 := by linarith
  rw [gamma_ratio_eq_integral' hv0 hγ, norm_mul, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  have hint : IntegrableOn (fun u : ℝ => u ^ (γ.re - 1) * Real.exp (-((v.re - 1) * u)))
      (Ioi 0) := by
    have h2 := integrableOn_rpow_mul_exp_neg_mul_rpow (s := γ.re - 1) (p := 1) (b := v.re - 1)
      (by linarith) (by norm_num) hX
    refine IntegrableOn.congr_fun h2 (fun u _ => ?_) measurableSet_Ioi
    simp only [Real.rpow_one]
    congr 2
    ring
  refine (norm_integral_le_of_norm_le hint (ae_restrict_of_forall_mem measurableSet_Ioi
    fun u hu => ?_)).trans ?_
  · have hu0 : 0 < u := hu
    have hr : 0 < 1 - Real.exp (-u) := by
      have : Real.exp (-u) < 1 := by
        calc Real.exp (-u) < Real.exp 0 := Real.exp_lt_exp.mpr (by linarith)
          _ = 1 := Real.exp_zero
      linarith
    rw [norm_mul, Complex.norm_exp, norm_cpow_eq_rpow_re_of_pos hr]
    simp only [neg_re, mul_re, ofReal_re, ofReal_im, mul_zero, sub_zero, sub_re, one_re]
    calc Real.exp (-(v.re * u)) * (1 - Real.exp (-u)) ^ (γ.re - 1)
        ≤ Real.exp (-(v.re * u)) * (u ^ (γ.re - 1) * Real.exp u) := by
          gcongr; exact one_sub_exp_neg_rpow_le hu0 (by linarith)
      _ = u ^ (γ.re - 1) * Real.exp (-((v.re - 1) * u)) := by
          rw [mul_left_comm, ← Real.exp_add]; congr 2; ring
  · rw [Real.integral_rpow_mul_exp_neg_mul_Ioi hγ hX, one_div, Real.inv_rpow hX.le,
      ← Real.rpow_neg hX.le, mul_comm]
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos (by linarith) (by linarith)
      (by linarith)) (Real.Gamma_pos_of_pos hγ).le

/-! ### Shifting -/

/-- `Γ(w + n) = Γ(w) ∏_{k<n} (w + k)` for `ℜw > 0`. -/
theorem Gamma_add_nat_eq_prod {w : ℂ} (hw : 0 < w.re) (n : ℕ) :
    Gamma (w + n) = Gamma w * ∏ k ∈ Finset.range n, (w + k) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h0 : w + n ≠ 0 := fun h => by
      have := congrArg re h; simp at this; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    rw [Nat.cast_succ, ← add_assoc, Complex.Gamma_add_one _ h0, ih, Finset.prod_range_succ]
    ring

/-- **Uniform ratio bound**: if `‖α‖, ‖γ‖ ≤ A`, `ℜγ + n ≥ 1`, and `B` bounds `|Γ(γ + n)⁻¹|` and
`Γ(ℜγ + n)`, then `|Γ(x + α)/Γ(x + α + γ)| ≤ B²4^{A+n}(2A + n + 1)ⁿ (1 + x)^{−ℜγ}` for
`x ≥ 2A + 2`. -/
theorem norm_gamma_ratio_le_uniform {α γ : ℂ} {A B : ℝ} {n : ℕ} (hα : ‖α‖ ≤ A) (hγ : ‖γ‖ ≤ A)
    (hn : 1 ≤ γ.re + n) (hB1 : ‖(Gamma (γ + n))⁻¹‖ ≤ B) (hB2 : Real.Gamma (γ.re + n) ≤ B)
    {x : ℝ} (hx : 2 * A + 2 ≤ x) :
    ‖Gamma (x + α) / Gamma (x + α + γ)‖ ≤
      B ^ 2 * 4 ^ (A + n) * (2 * A + n + 1) ^ n * (1 + x) ^ (-γ.re) := by
  have hA : 0 ≤ A := (norm_nonneg _).trans hα
  have hαre : -A ≤ α.re := by linarith [neg_abs_le α.re, abs_re_le_norm α]
  have hγre : |γ.re| ≤ A := (abs_re_le_norm γ).trans hγ
  have hx0 : 0 ≤ x := by linarith
  set v := (x : ℂ) + α
  have hvre : v.re = x + α.re := by simp [v]
  have hv2 : 2 ≤ v.re + γ.re := by rw [hvre]; linarith [neg_abs_le γ.re]
  set w := v + γ
  have hw : 0 < w.re := by simp only [w, add_re]; linarith
  have hshift := Gamma_add_nat_eq_prod hw n
  have hGw : Gamma w ≠ 0 := Complex.Gamma_ne_zero_of_re_pos hw
  -- the ratio with `γ + n`
  have hvv : 2 ≤ v.re := by rw [hvre]; linarith
  have hγn : 0 < (γ + n).re := by simp; linarith
  have hbase := norm_gamma_ratio_le' hvv hγn
  rw [show v + (γ + n) = w + n by simp only [w]; ring] at hbase
  have hratio : Gamma v / Gamma w = Gamma v / Gamma (w + n) * ∏ k ∈ Finset.range n, (w + k) := by
    rw [hshift]
    have hP : ∏ k ∈ Finset.range n, (w + k) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ h => by
      have := congrArg re h; simp at this; linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
    field_simp
  have hprod : ‖∏ k ∈ Finset.range n, (w + k)‖ ≤ ((2 * A + n + 1) * (1 + x)) ^ n := by
    rw [norm_prod]
    calc (∏ k ∈ Finset.range n, ‖w + k‖) ≤
          ∏ _k ∈ Finset.range n, ((2 * A + n + 1) * (1 + x)) := by
          refine Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun k hk => ?_
          have hk' : (k : ℝ) ≤ n := by exact_mod_cast (Finset.mem_range.mp hk).le
          calc ‖w + k‖ ≤ ‖(x : ℂ)‖ + ‖α‖ + ‖γ‖ + ‖(k : ℂ)‖ := by
                simp only [w, v]
                calc ‖(x : ℂ) + α + γ + k‖ ≤ ‖(x : ℂ) + α + γ‖ + ‖(k : ℂ)‖ := norm_add_le _ _
                  _ ≤ ‖(x : ℂ) + α‖ + ‖γ‖ + ‖(k : ℂ)‖ := by gcongr; exact norm_add_le _ _
                  _ ≤ ‖(x : ℂ)‖ + ‖α‖ + ‖γ‖ + ‖(k : ℂ)‖ := by gcongr; exact norm_add_le _ _
            _ ≤ x + A + A + n := by
                rw [norm_real, Real.norm_of_nonneg hx0, Complex.norm_natCast]; linarith
            _ ≤ (2 * A + n + 1) * (1 + x) := by nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
      _ = _ := by rw [Finset.prod_const, Finset.card_range]
  -- `(ℜv/2)^{−q} ≤ 4^q (1 + x)^{−q}`
  have hq : 0 < γ.re + n := by linarith
  have hvhalf : (1 + x) / 4 ≤ v.re / 2 := by rw [hvre]; linarith
  have hpow : (v.re / 2) ^ (-(γ.re + n)) ≤ 4 ^ (A + n) * (1 + x) ^ (-(γ.re + n)) := by
    calc (v.re / 2) ^ (-(γ.re + n)) ≤ ((1 + x) / 4) ^ (-(γ.re + n)) :=
          Real.rpow_le_rpow_of_nonpos (by positivity) hvhalf (by linarith)
      _ = 4 ^ (γ.re + n) * (1 + x) ^ (-(γ.re + n)) := by
          rw [Real.div_rpow (by positivity) (by norm_num),
            Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 4)]
          simp only [div_eq_mul_inv, inv_inv]
          ring
      _ ≤ 4 ^ (A + n) * (1 + x) ^ (-(γ.re + n)) := by
          gcongr
          · norm_num
          · linarith [le_abs_self γ.re]
  have hB0 : 0 ≤ B := (norm_nonneg _).trans hB1
  rw [hratio, norm_mul]
  have hb' : ‖Gamma v / Gamma (w + n)‖ ≤ B * B * (4 ^ (A + n) * (1 + x) ^ (-(γ.re + n))) := by
    refine hbase.trans ?_
    simp only [add_re, natCast_re] at hpow ⊢
    gcongr
  calc ‖Gamma v / Gamma (w + n)‖ * ‖∏ k ∈ Finset.range n, (w + k)‖
      ≤ (B * B * (4 ^ (A + n) * (1 + x) ^ (-(γ.re + n)))) * ((2 * A + n + 1) * (1 + x)) ^ n :=
        mul_le_mul hb' hprod (norm_nonneg _) (by positivity)
    _ = B ^ 2 * 4 ^ (A + n) * (2 * A + n + 1) ^ n *
        ((1 + x) ^ (-(γ.re + n)) * (1 + x) ^ (n : ℝ)) := by
        rw [mul_pow, Real.rpow_natCast]; ring
    _ = _ := by
        rw [← Real.rpow_add (by linarith)]; congr 2; ring

/-! ### Reflection -/

/-- `1/Γ(z) = Γ(1 − z) sin(πz)/π` unless `z = 1, 2, …`. -/
theorem inv_Gamma_eq_reflect {z : ℂ} (hz : ∀ n : ℕ, z ≠ n + 1) :
    (Gamma z)⁻¹ = Gamma (1 - z) * Complex.sin (π * z) / π := by
  have h := sin_mul_Gamma (b := 1 - z) fun n h => hz n (by linear_combination -h)
  rw [sub_sub_cancel, show (π : ℂ) * (1 - z) = π - π * z by ring, Complex.sin_pi_sub] at h
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  rw [mul_comm (Gamma (1 - z)), h]
  field_simp

theorem norm_sin_le_exp (z : ℂ) : ‖Complex.sin z‖ ≤ Real.exp |z.im| := by
  rw [Complex.sin, norm_div, norm_mul, norm_I, mul_one, Complex.norm_two]
  have h1 := norm_sub_le (cexp (-z * I)) (cexp (z * I))
  rw [Complex.norm_exp, Complex.norm_exp] at h1
  have e1 : (-z * I).re = z.im := by simp
  have e2 : (z * I).re = -z.im := by simp
  rw [e1, e2] at h1
  have h3 : Real.exp z.im ≤ Real.exp |z.im| := Real.exp_le_exp.mpr (le_abs_self _)
  have h4 : Real.exp (-z.im) ≤ Real.exp |z.im| := Real.exp_le_exp.mpr (neg_le_abs _)
  rw [div_le_iff₀ (by norm_num)]
  linarith

/-! ### The bound on `1/(Γ(a + t)Γ(c − t))` -/

/-- `1/(Γ(a + t)Γ(c − t))`. -/
noncomputable def invGammaPair (a c : ℂ) (t : ℝ) : ℂ := (Gamma (a + t))⁻¹ * (Gamma (c - t))⁻¹

theorem continuous_inv_Gamma : Continuous fun z : ℂ => (Gamma z)⁻¹ := by
  have : Differentiable ℂ fun z : ℂ => (Gamma z)⁻¹ := by
    simpa [one_div] using Complex.differentiable_one_div_Gamma
  exact this.continuous

theorem exists_bound_inv_Gamma_compact {K : Set ℂ} (hK : IsCompact K) :
    ∃ B : ℝ, ∀ z ∈ K, ‖(Gamma z)⁻¹‖ ≤ B :=
  hK.exists_bound_of_continuousOn continuous_inv_Gamma.continuousOn

theorem exists_bound_real_Gamma {L : ℝ} : ∃ B : ℝ, ∀ x ∈ Icc (1 : ℝ) L, Real.Gamma x ≤ B := by
  obtain ⟨B, hB⟩ := (isCompact_Icc (a := (1 : ℝ)) (b := L)).exists_bound_of_continuousOn
    (f := Real.Gamma) (fun x hx => (Real.differentiableAt_Gamma fun m h => by
      have := hx.1; rw [h] at this; linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]).continuousAt
      |>.continuousWithinAt)
  exact ⟨B, fun x hx => (le_abs_self _).trans (by simpa using hB x hx)⟩

/-- The tail `t ≥ T` (with `x = t`, `α`, `γ` as in `norm_gamma_ratio_le_uniform`):
`|Γ(x + α)/Γ(x + α + γ) · sin(π w)/π| ≤ C e^{π|ℑw|}(1 + x)^{−ℜγ}`. -/
theorem norm_ratio_sin_le {α γ w : ℂ} {A B : ℝ} {n : ℕ} (hα : ‖α‖ ≤ A) (hγ : ‖γ‖ ≤ A)
    (hn : 1 ≤ γ.re + n) (hB1 : ‖(Gamma (γ + n))⁻¹‖ ≤ B) (hB2 : Real.Gamma (γ.re + n) ≤ B)
    {x : ℝ} (hx : 2 * A + 2 ≤ x) :
    ‖Gamma (x + α) / Gamma (x + α + γ) * (Complex.sin (π * w) / π)‖ ≤
      B ^ 2 * 4 ^ (A + n) * (2 * A + n + 1) ^ n * (Real.exp (π * |w.im|) / π) *
        (1 + x) ^ (-γ.re) := by
  have h1 := norm_gamma_ratio_le_uniform hα hγ hn hB1 hB2 hx
  have h2 : ‖Complex.sin (π * w) / π‖ ≤ Real.exp (π * |w.im|) / π := by
    rw [norm_div, norm_real, Real.norm_of_nonneg Real.pi_pos.le]
    gcongr
    refine (norm_sin_le_exp _).trans (le_of_eq ?_)
    simp [abs_mul, abs_of_pos Real.pi_pos]
  rw [norm_mul]
  calc ‖Gamma (x + α) / Gamma (x + α + γ)‖ * ‖Complex.sin (π * w) / π‖
      ≤ (B ^ 2 * 4 ^ (A + n) * (2 * A + n + 1) ^ n * (1 + x) ^ (-γ.re)) *
        (Real.exp (π * |w.im|) / π) := mul_le_mul h1 h2 (norm_nonneg _) (by
          have : 0 ≤ 2 * A + n + 1 := by
            linarith [(norm_nonneg α).trans hα, (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
          have hx0 : 0 ≤ 1 + x := by linarith [(norm_nonneg α).trans hα]
          exact mul_nonneg (mul_nonneg (mul_nonneg (sq_nonneg B) (Real.rpow_nonneg (by norm_num) _))
            (pow_nonneg this n)) (Real.rpow_nonneg hx0 _))
    _ = _ := by ring

/-- **Uniform bound**: `|1/(Γ(a + t)Γ(c − t))| ≤ M(1 + |t|)^{1−ℜ(a₀+c)+ρ}` for `|a − a₀| ≤ ρ`. -/
theorem exists_bound_invGammaPair (a₀ c : ℂ) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ a ∈ Metric.closedBall a₀ ρ, ∀ t : ℝ,
      ‖invGammaPair a c t‖ ≤ M * (1 + |t|) ^ (1 - (a₀ + c).re + ρ) := by
  set A := ‖a₀‖ + ρ + ‖c‖ + 2
  have hA0 : 0 ≤ A := by positivity
  set n := Nat.ceil A + 1
  have hnA : A + 1 ≤ (n : ℝ) := by
    simp only [n]; push_cast; linarith [Nat.le_ceil A]
  set e := 1 - (a₀ + c).re + ρ
  set T := 2 * A + 2
  have hAdef : A = ‖a₀‖ + ρ + ‖c‖ + 2 := rfl
  have hTdef : T = 2 * A + 2 := rfl
  have hedef : e = 1 - (a₀ + c).re + ρ := rfl
  have hT : 0 < T := by positivity
  -- uniform constants for `γ = a + c − 1`
  have hKγ : IsCompact ((fun a => a + c - 1 + n) '' Metric.closedBall a₀ ρ) :=
    (isCompact_closedBall a₀ ρ).image (by fun_prop)
  obtain ⟨B₁, hB₁⟩ := exists_bound_inv_Gamma_compact hKγ
  obtain ⟨B₂, hB₂⟩ := exists_bound_real_Gamma (L := 2 * A + n)
  set B := max B₁ B₂
  have hball : ∀ a ∈ Metric.closedBall a₀ ρ, ‖a‖ ≤ ‖a₀‖ + ρ ∧ |a.re - a₀.re| ≤ ρ ∧
      |a.im| ≤ |a₀.im| + ρ := fun a ha => by
    have hd : ‖a - a₀‖ ≤ ρ := by rw [← dist_eq_norm]; exact Metric.mem_closedBall.mp ha
    refine ⟨by linarith [norm_le_insert' a a₀], ?_, ?_⟩
    · rw [← sub_re]; exact (abs_re_le_norm _).trans hd
    · have := (abs_im_le_norm (a - a₀)).trans hd
      rw [sub_im] at this; linarith [abs_sub_abs_le_abs_sub a.im a₀.im]
  have hγdata : ∀ a ∈ Metric.closedBall a₀ ρ, ‖a + c - 1‖ ≤ A ∧ 1 ≤ (a + c - 1).re + n ∧
      ‖(Gamma (a + c - 1 + n))⁻¹‖ ≤ B ∧ Real.Gamma ((a + c - 1).re + n) ≤ B := fun a ha => by
    obtain ⟨h1, -, -⟩ := hball a ha
    have hnorm : ‖a + c - 1‖ ≤ A := by
      calc ‖a + c - 1‖ ≤ ‖a‖ + ‖c‖ + 1 := by
            calc ‖a + c - 1‖ ≤ ‖a + c‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
              _ ≤ ‖a‖ + ‖c‖ + 1 := by rw [norm_one]; linarith [norm_add_le a c]
        _ ≤ A := by simp only [A]; linarith
    have hre : |(a + c - 1).re| ≤ A := (abs_re_le_norm _).trans hnorm
    refine ⟨hnorm, by linarith [neg_abs_le (a + c - 1).re], ?_, ?_⟩
    · exact (hB₁ _ ⟨a, ha, rfl⟩).trans (le_max_left _ _)
    · refine (hB₂ _ ⟨by linarith [neg_abs_le (a + c - 1).re], by
        linarith [le_abs_self (a + c - 1).re]⟩).trans (le_max_right _ _)
  -- the middle range `|t| ≤ T`
  have hK1 : IsCompact ((fun p : ℂ × ℝ => p.1 + p.2) '' (Metric.closedBall a₀ ρ ×ˢ Icc (-T) T)) :=
    ((isCompact_closedBall a₀ ρ).prod isCompact_Icc).image (by fun_prop)
  have hK2 : IsCompact ((fun t : ℝ => c - t) '' Icc (-T) T) := isCompact_Icc.image (by fun_prop)
  obtain ⟨B₃, hB₃⟩ := exists_bound_inv_Gamma_compact hK1
  obtain ⟨B₄, hB₄⟩ := exists_bound_inv_Gamma_compact hK2
  -- constants of the tails
  set Ci := B ^ 2 * 4 ^ (A + n) * (2 * A + n + 1) ^ n
  set Mpos := Ci * (Real.exp (π * |c.im|) / π)
  set Mneg := Ci * (Real.exp (π * (|a₀.im| + ρ)) / π)
  set Mmid := |B₃| * |B₄| * (1 + T) ^ |e|
  have hCi : 0 ≤ Ci := mul_nonneg (mul_nonneg (sq_nonneg B) (Real.rpow_nonneg (by norm_num) _))
    (pow_nonneg (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]) n)
  have hMpos : 0 ≤ Mpos := mul_nonneg hCi (div_nonneg (Real.exp_pos _).le Real.pi_pos.le)
  have hMneg : 0 ≤ Mneg := mul_nonneg hCi (div_nonneg (Real.exp_pos _).le Real.pi_pos.le)
  refine ⟨max (max Mpos Mneg) Mmid, le_max_of_le_right (mul_nonneg (mul_nonneg (abs_nonneg _)
    (abs_nonneg _)) (Real.rpow_nonneg (by linarith) _)), fun a ha t => ?_⟩
  obtain ⟨hnorm, hn1, hBa, hBb⟩ := hγdata a ha
  obtain ⟨ha1, ha2, ha3⟩ := hball a ha
  have h1t : (1 : ℝ) ≤ 1 + |t| := by linarith [abs_nonneg t]
  have hexp : (1 + |t|) ^ (-(a + c - 1).re) ≤ (1 + |t|) ^ e := by
    refine Real.rpow_le_rpow_of_exponent_le h1t ?_
    simp only [e, sub_re, add_re, one_re]
    linarith [(abs_le.mp ha2).1]
  have hαc : ‖1 - c‖ ≤ A := by
    calc ‖1 - c‖ ≤ ‖(1 : ℂ)‖ + ‖c‖ := norm_sub_le _ _
      _ ≤ A := by rw [norm_one]; simp only [A]; linarith [norm_nonneg a₀]
  have hαa : ‖1 - a‖ ≤ A := by
    calc ‖1 - a‖ ≤ ‖(1 : ℂ)‖ + ‖a‖ := norm_sub_le _ _
      _ ≤ A := by rw [norm_one]; simp only [A]; linarith [norm_nonneg c]
  rcases le_or_gt T t with ht | ht
  · -- `t ≥ T`
    have hz : ∀ m : ℕ, c - t ≠ m + 1 := fun m h => by
      have := congrArg re h; simp at this
      linarith [re_le_norm c, (Nat.cast_nonneg m : (0 : ℝ) ≤ m), norm_nonneg a₀]
    have heq : invGammaPair a c t = Gamma (t + (1 - c)) / Gamma (t + (1 - c) + (a + c - 1)) *
        (Complex.sin (π * (c - t)) / π) := by
      rw [invGammaPair, inv_Gamma_eq_reflect hz, show (t : ℂ) + (1 - c) + (a + c - 1) = a + t by
        ring, show (1 : ℂ) - (c - t) = t + (1 - c) by ring]
      ring
    have h := norm_ratio_sin_le (w := c - t) hαc hnorm hn1 hBa hBb ht
    rw [← heq] at h
    have him : (c - t).im = c.im := by simp
    rw [him] at h
    rw [abs_of_nonneg (show (0 : ℝ) ≤ t by linarith)] at hexp ⊢
    refine h.trans ?_
    calc Ci * (Real.exp (π * |c.im|) / π) * (1 + t) ^ (-(a + c - 1).re)
        ≤ Mpos * (1 + t) ^ e := mul_le_mul_of_nonneg_left hexp hMpos
      _ ≤ max (max Mpos Mneg) Mmid * (1 + t) ^ e :=
          mul_le_mul_of_nonneg_right (le_max_of_le_left (le_max_left _ _))
            (Real.rpow_nonneg (by linarith) _)
  rcases le_or_gt t (-T) with ht' | ht'
  · -- `t ≤ −T`
    set s := -t
    have hs : T ≤ s := by simp only [s]; linarith
    have hz : ∀ m : ℕ, a - s ≠ m + 1 := fun m h => by
      have := congrArg re h; simp at this
      linarith [re_le_norm a, (Nat.cast_nonneg m : (0 : ℝ) ≤ m), norm_nonneg c]
    have heq : invGammaPair a c t = Gamma (s + (1 - a)) / Gamma (s + (1 - a) + (a + c - 1)) *
        (Complex.sin (π * (a - s)) / π) := by
      rw [invGammaPair, show (a : ℂ) + t = a - s by simp only [s]; push_cast; ring,
        show (c : ℂ) - t = c + s by simp only [s]; push_cast; ring, inv_Gamma_eq_reflect hz,
        show (s : ℂ) + (1 - a) + (a + c - 1) = c + s by ring,
        show (1 : ℂ) - (a - s) = s + (1 - a) by ring]
      ring
    have h := norm_ratio_sin_le (w := a - s) hαa hnorm hn1 hBa hBb hs
    rw [← heq] at h
    have him : (a - s).im = a.im := by simp
    rw [him] at h
    have habs : |t| = s := by simp only [s]; rw [abs_of_neg (by linarith)]
    rw [habs] at hexp ⊢
    refine h.trans ?_
    have hsin : Real.exp (π * |a.im|) / π ≤ Real.exp (π * (|a₀.im| + ρ)) / π := by
      gcongr
    calc Ci * (Real.exp (π * |a.im|) / π) * (1 + s) ^ (-(a + c - 1).re)
        = Ci * ((Real.exp (π * |a.im|) / π) * (1 + s) ^ (-(a + c - 1).re)) := by ring
      _ ≤ Ci * ((Real.exp (π * (|a₀.im| + ρ)) / π) * (1 + s) ^ e) :=
          mul_le_mul_of_nonneg_left (mul_le_mul hsin hexp (Real.rpow_nonneg (by linarith) _)
            (div_nonneg (Real.exp_pos _).le Real.pi_pos.le)) hCi
      _ = Mneg * (1 + s) ^ e := by
          rw [show Mneg = Ci * (Real.exp (π * (|a₀.im| + ρ)) / π) from rfl]; ring
      _ ≤ max (max Mpos Mneg) Mmid * (1 + s) ^ e :=
          mul_le_mul_of_nonneg_right (le_max_of_le_left (le_max_right _ _))
            (Real.rpow_nonneg (by linarith) _)
  · -- `|t| < T`
    have htT : t ∈ Icc (-T) T := ⟨ht'.le, ht.le⟩
    have h1 := hB₃ (a + t) ⟨(a, t), ⟨ha, htT⟩, rfl⟩
    have h2 := hB₄ (c - t) ⟨t, htT, rfl⟩
    have hlow : 1 ≤ (1 + T) ^ |e| * (1 + |t|) ^ e := by
      rcases le_total 0 e with he | he
      · have := Real.one_le_rpow h1t he
        have := Real.one_le_rpow (show (1 : ℝ) ≤ 1 + T by linarith) (abs_nonneg e)
        nlinarith
      · rw [abs_of_nonpos he]
        have hle : 1 + |t| ≤ 1 + T := by linarith [abs_le.mpr ⟨ht'.le, ht.le⟩]
        have h3 := Real.rpow_le_rpow_of_nonpos (by linarith : (0 : ℝ) < 1 + |t|) hle he
        have h4 : (1 + T) ^ (-e) * (1 + T) ^ e = 1 := by
          rw [← Real.rpow_add (by linarith), neg_add_cancel, Real.rpow_zero]
        calc (1 : ℝ) = (1 + T) ^ (-e) * (1 + T) ^ e := h4.symm
          _ ≤ (1 + T) ^ (-e) * (1 + |t|) ^ e :=
              mul_le_mul_of_nonneg_left h3 (Real.rpow_nonneg (by linarith) _)
    rw [invGammaPair, norm_mul]
    calc ‖(Gamma (a + t))⁻¹‖ * ‖(Gamma (c - t))⁻¹‖ ≤ |B₃| * |B₄| :=
          mul_le_mul (h1.trans (le_abs_self _)) (h2.trans (le_abs_self _)) (norm_nonneg _)
            (abs_nonneg _)
      _ ≤ |B₃| * |B₄| * ((1 + T) ^ |e| * (1 + |t|) ^ e) :=
          le_mul_of_one_le_right (by positivity) hlow
      _ = Mmid * (1 + |t|) ^ e := by ring
      _ ≤ max (max Mpos Mneg) Mmid * (1 + |t|) ^ e := by gcongr; exact le_max_right _ _

end Azurite.DLMF
