/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter4.Section13Asymp
import Azurite.DLMF.Chapter4.Section13Lagrange

/-!
# DLMF §4.13: the asymptotic expansions 4.13.10–4.13.11

With `ξ = ln_k z`, `v = W − ξ + ln ξ`, `σ = 1/ξ`, `τ = ln ξ/ξ`: `u = 1 − W/ξ` satisfies
`u = τ − σ L(u)` with `L(u) = v` (`L(u) = −ln(1 − u)`), so the core expansion
`hasSum_lambertInner` gives the series of 4.13.10, absolutely convergent for large `|z|`, and its
inner sums are `O((|ln ξ|/|ξ|)ⁿ)`.

* 4.13.10: `dlmf_4_13_10`.
* 4.13.11: `dlmf_4_13_11`: for `W_{−1}(x + 0i) = W₁(x − 0i)` (`tendsto_lambertW_one_below`), real,
  with `η = ln(−1/x)`, `σ = −1/η`, `τ = −ln η/η`, `u = 1 + W/η`, as `x → 0−`.
-/

open Set Filter Topology Complex Finset Asymptotics
open scoped Real Nat

namespace Azurite.DLMF

/-! ### Eventual estimates as `|z| → ∞` -/

theorem tendsto_norm_lnk (k : ℤ) :
    Tendsto (fun z => ‖lnk k z‖) (Bornology.cobounded ℂ) atTop := by
  refine tendsto_atTop_mono (fun z => ?_) (Real.tendsto_log_atTop.comp
    tendsto_norm_cobounded_atTop)
  simp only [Function.comp_apply, ← lnk_re k z]
  exact (le_abs_self _).trans (abs_re_le_norm _)

theorem tendsto_norm_log_lnk_div (k : ℤ) :
    Tendsto (fun z => ‖log (lnk k z) / lnk k z‖) (Bornology.cobounded ℂ) (𝓝 0) := by
  have ht := tendsto_norm_lnk k
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_
    (tendsto_log_add_pi_div.comp ht)
  filter_upwards [ht.eventually_ge_atTop 1] with z hz
  have hw : 0 < ‖lnk k z‖ := by linarith
  rw [norm_div, Function.comp_apply, div_le_div_iff_of_pos_right hw]
  have := norm_clog_le_abs_log_add_pi (lnk k z)
  rwa [abs_of_nonneg (Real.log_nonneg hz)] at this

/-- The facts behind 4.13.10, for large `|z|`. -/
theorem eventually_lambert_core (k : ℤ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ z in Bornology.cobounded ℂ,
      ‖(lnk k z)⁻¹‖ ≤ ε ∧ ‖log (lnk k z) / lnk k z‖ ≤ ε ∧ ‖1 - lambertW k z / lnk k z‖ ≤ ε ∧
      1 ≤ ‖log (lnk k z)‖ ∧
      1 - lambertW k z / lnk k z =
        log (lnk k z) / lnk k z - (lnk k z)⁻¹ * lambertLogL (1 - lambertW k z / lnk k z) ∧
      lambertLogL (1 - lambertW k z / lnk k z) = lambertW k z - (lnk k z - log (lnk k z)) := by
  set g := fun z => log (lambertW k z) / lambertW k z
  have hg := tendsto_log_div_lambertW k
  have ht := tendsto_norm_lambertW k
  have hξ := tendsto_norm_lnk k
  have hu : Tendsto (fun z => (1 + g z)⁻¹) (Bornology.cobounded ℂ) (𝓝 1) := by
    have := (tendsto_const_nhds (x := (1 : ℂ))).add hg
    simpa using this.inv₀ (by norm_num)
  have h1 : (1 : ℂ) ∈ slitPlane := one_mem_slitPlane
  have hargu := ((continuousAt_arg h1).tendsto.comp hu).eventually
    (Metric.ball_mem_nhds (arg 1) (by positivity : (0 : ℝ) < π / 2))
  have hu1 := (tendsto_const_nhds (x := (1 : ℂ))).sub hu
  rw [sub_self] at hu1
  have hu2 := hu1.norm.eventually (gt_mem_nhds (by simpa using hε))
  have hinv : Tendsto (fun z => ‖(lnk k z)⁻¹‖) (Bornology.cobounded ℂ) (𝓝 0) := by
    refine (tendsto_inv_atTop_zero.comp hξ).congr fun z => ?_
    simp [norm_inv]
  filter_upwards [tendsto_norm_cobounded_atTop.eventually_gt_atTop 1, ht.eventually_ge_atTop 1,
    hargu, hu2, hinv.eventually (ge_mem_nhds hε),
    (tendsto_norm_log_lnk_div k).eventually (ge_mem_nhds hε),
    hξ.eventually_ge_atTop (Real.exp 1)] with z hz hw ha hu' hσ hτ hξe
  set w := lambertW k z
  have hw0 : w ≠ 0 := fun h => by simp [w, h] at hw; linarith
  set ξ := lnk k z
  have hadd : w + log w = ξ := lambertW_add_log k hz
  have hre : 0 ≤ ξ.re := by
    have : ξ.re = Real.log ‖z‖ := lnk_re k z
    rw [this]; exact (Real.log_pos hz).le
  have hξ0 : ξ ≠ 0 := fun h => by
    have h2 : ξ.re = Real.log ‖z‖ := lnk_re k z
    rw [h] at h2; simp at h2; linarith [Real.log_pos hz]
  have hξw : ξ = w * (1 + g z) := by
    rw [← hadd]; show w + log w = w * (1 + log w / w); field_simp
  have h1g : 1 + g z ≠ 0 := fun h => hξ0 (by rw [hξw, h, mul_zero])
  have hwξ : w / ξ = (1 + g z)⁻¹ := by rw [hξw]; field_simp
  simp only [Function.comp_apply, Real.dist_eq, arg_one, sub_zero] at ha
  have hargξ := abs_arg_le_pi_div_two_iff.mpr hre
  have hwξ0 : w / ξ ≠ 0 := by rw [hwξ]; exact inv_ne_zero h1g
  have hlog : log w = log ξ + log (w / ξ) := by
    have hmul := log_mul hξ0 hwξ0 (by
      rw [hwξ]
      constructor <;>
        linarith [(abs_le.mp hargξ).1, (abs_le.mp hargξ).2, (abs_lt.mp ha).1, (abs_lt.mp ha).2])
    rwa [show ξ * (w / ξ) = w by field_simp] at hmul
  have hL : lambertLogL (1 - w / ξ) = w - (ξ - log ξ) := by
    rw [lambertLogL, sub_sub_cancel]
    have : log (w / ξ) = log w - log ξ := by rw [hlog]; ring
    rw [this]
    linear_combination -hadd
  refine ⟨hσ, hτ, ?_, ?_, ?_, hL⟩
  · rw [hwξ]; exact hu'.le
  · have h3 : (log ξ).re = Real.log ‖ξ‖ := log_re ξ
    have h4 : 1 ≤ Real.log ‖ξ‖ := by
      rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) hξe
    exact h4.trans (h3 ▸ re_le_norm (log ξ))
  · rw [hL]; field_simp; ring

/-! ### 4.13.10 -/

/-- The `n`-th term `(−1)ⁿ ξ^{−n} ∑_{m=1}^{n} [n, n − m + 1] (−ln ξ)ᵐ/m!` of 4.13.10. -/
noncomputable def dlmfTerm10 (ξ : ℂ) (n : ℕ) : ℂ :=
  (-1) ^ n / ξ ^ n * ∑ m ∈ Finset.Icc 1 n, (Nat.stirlingFirst n (n - m + 1) : ℂ) *
    (-log ξ) ^ m / m !

theorem lambertInner_eq_dlmfTerm10 {ξ : ℂ} (hξ : ξ ≠ 0) (n : ℕ) :
    lambertInner ξ⁻¹ (log ξ / ξ) n = dlmfTerm10 ξ n := by
  rw [lambertInner, dlmfTerm10, mul_sum]
  refine sum_congr rfl fun m hm => ?_
  have hmn := (Finset.mem_Icc.mp hm).2
  have hp : ξ ^ n = ξ ^ m * ξ ^ (n - m) := by rw [← pow_add, Nat.add_sub_cancel' hmn]
  rw [div_pow, inv_pow, neg_pow (log ξ), pow_add, hp]
  have : (m ! : ℂ) ≠ 0 := by exact_mod_cast m.factorial_ne_zero
  field_simp

theorem two_mul_pow_le (n : ℕ) {x : ℝ} (hx : 0 ≤ x) : (n + 1) * x ^ n ≤ (2 * x) ^ n := by
  rw [mul_pow]
  have : ((n : ℝ) + 1) ≤ 2 ^ n := by exact_mod_cast Nat.lt_two_pow_self (n := n)
  exact mul_le_mul_of_nonneg_right this (by positivity)

/-- **DLMF 4.13.10**: for large `|z|` the series
`W_k(z) = ξ − ln ξ + ∑_{n ≥ 1} (−1)ⁿ ξ^{−n} ∑_{m=1}^{n} [n, n − m + 1] (−ln ξ)ᵐ/m!`
(`ξ = ln z + 2πik`) converges absolutely to `W_k(z)`, and it is an asymptotic expansion: the
remainder after `N` terms is `O((|ln ξ|/|ξ|)^{N+1})` as `|z| → ∞`. -/
theorem dlmf_4_13_10 (k : ℤ) :
    (∀ᶠ z in Bornology.cobounded ℂ,
      HasSum (fun n => dlmfTerm10 (lnk k z) (n + 1)) (lambertW k z - (lnk k z - log (lnk k z))) ∧
      Summable fun n => ‖dlmfTerm10 (lnk k z) (n + 1)‖) ∧
    ∀ N : ℕ, (fun z => lambertW k z - (lnk k z - log (lnk k z) +
        ∑ n ∈ Finset.Icc 1 N, dlmfTerm10 (lnk k z) n)) =O[Bornology.cobounded ℂ]
      fun z => (‖log (lnk k z)‖ / ‖lnk k z‖) ^ (N + 1) := by
  have hev := eventually_lambert_core k (ε := 1 / 16) (by norm_num)
  -- the core expansion, eventually
  have hcore : ∀ᶠ z in Bornology.cobounded ℂ,
      HasSum (dlmfTerm10 (lnk k z)) (lambertW k z - (lnk k z - log (lnk k z))) ∧
      ∀ n, ‖dlmfTerm10 (lnk k z) n‖ ≤
        (n + 1) * (4 * (‖log (lnk k z)‖ / ‖lnk k z‖)) ^ n := by
    filter_upwards [hev] with z ⟨hσ, hτ, hu, hl1, heq, hL⟩
    have hξ0 : lnk k z ≠ 0 := fun h => by rw [h, log_zero, norm_zero] at hl1; norm_num at hl1
    have h := hasSum_lambertInner (by linarith) (by linarith) (by linarith) heq
    rw [hL] at h
    refine ⟨?_, fun n => ?_⟩
    · convert h using 1
      funext n; rw [lambertInner_eq_dlmfTerm10 hξ0]
    · rw [← lambertInner_eq_dlmfTerm10 hξ0]
      refine (norm_lambertInner_le _ _ n).trans ?_
      gcongr
      refine max_le ?_ (by rw [norm_div])
      rw [norm_inv, ← one_div]
      exact div_le_div_of_nonneg_right hl1 (norm_nonneg _)
  refine ⟨?_, fun N => ?_⟩
  · filter_upwards [hev, hcore] with z ⟨hσ, hτ, _, _, _, _⟩ ⟨h, hb⟩
    have hρ : ‖log (lnk k z)‖ / ‖lnk k z‖ ≤ 1 / 16 := by rwa [← norm_div]
    refine ⟨?_, ?_⟩
    · have h0 : dlmfTerm10 (lnk k z) 0 = 0 := by simp [dlmfTerm10]
      have := (hasSum_nat_add_iff' 1).mpr h
      simpa [h0] using this
    · refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => (hb (n + 1)).trans
        (two_mul_pow_le (n + 1) (by positivity))) ?_
      have hx : 2 * (4 * (‖log (lnk k z)‖ / ‖lnk k z‖)) < 1 := by linarith
      exact (summable_geometric_of_lt_one (by positivity) hx).comp_injective
        (add_left_injective 1)
  · refine IsBigO.of_bound (2 * 8 ^ (N + 1)) ?_
    filter_upwards [hev, hcore] with z ⟨hσ, hτ, _, _, _, _⟩ ⟨h, hb⟩
    set ρ := ‖log (lnk k z)‖ / ‖lnk k z‖
    have hρ : ρ ≤ 1 / 16 := by simp only [ρ]; rwa [← norm_div]
    have hρ0 : 0 ≤ ρ := by positivity
    -- the remainder is the tail of the series
    have htail := (hasSum_nat_add_iff' (N + 1)).mpr h
    have hsplit : ∑ i ∈ range (N + 1), dlmfTerm10 (lnk k z) i =
        ∑ n ∈ Finset.Icc 1 N, dlmfTerm10 (lnk k z) n := by
      rw [sum_range_succ', ← Finset.Ico_add_one_right_eq_Icc, sum_Ico_eq_sum_range,
        Nat.add_sub_cancel]
      simp only [dlmfTerm10, pow_zero, Finset.Icc_eq_empty_of_lt one_pos,
        sum_empty, mul_zero, add_zero]
      refine sum_congr rfl fun i _ => by rw [add_comm 1 i]
    rw [hsplit] at htail
    have hgeo : HasSum (fun n : ℕ => (8 * ρ) ^ (n + (N + 1)))
        ((8 * ρ) ^ (N + 1) * (1 - 8 * ρ)⁻¹) := by
      have := (hasSum_geometric_of_lt_one (by positivity) (by linarith : 8 * ρ < 1)).mul_left
        ((8 * ρ) ^ (N + 1))
      convert this using 1; funext n; ring
    have hn := htail.norm_le_of_bounded hgeo fun n => by
      refine (hb (n + (N + 1))).trans ?_
      have := two_mul_pow_le (n + (N + 1)) (show 0 ≤ 4 * ρ by positivity)
      push_cast at this ⊢
      calc ((n : ℝ) + (N + 1) + 1) * (4 * ρ) ^ (n + (N + 1)) ≤ (2 * (4 * ρ)) ^ (n + (N + 1)) :=
            this
        _ = (8 * ρ) ^ (n + (N + 1)) := by ring_nf
    have hrem : lambertW k z - (lnk k z - log (lnk k z) +
        ∑ n ∈ Finset.Icc 1 N, dlmfTerm10 (lnk k z) n) =
        lambertW k z - (lnk k z - log (lnk k z)) -
          ∑ n ∈ Finset.Icc 1 N, dlmfTerm10 (lnk k z) n := by ring
    rw [hrem, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    refine hn.trans ?_
    have h1 : (1 - 8 * ρ)⁻¹ ≤ 2 := by
      rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
    calc (8 * ρ) ^ (N + 1) * (1 - 8 * ρ)⁻¹ ≤ (8 * ρ) ^ (N + 1) * 2 :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = 2 * 8 ^ (N + 1) * ρ ^ (N + 1) := by rw [mul_pow]; ring

/-! ### 4.13.11 -/

/-- `η = ln(−1/x)`. -/
noncomputable def eta11 (x : ℝ) : ℝ := Real.log (-1 / x)

theorem tendsto_eta11 : Tendsto eta11 (𝓝[<] 0) atTop := by
  have h : Tendsto (fun x : ℝ => -1 / x) (𝓝[<] 0) atTop := by
    have := tendsto_neg_atBot_atTop.comp (tendsto_inv_nhdsLT_zero (𝕜 := ℝ))
    refine this.congr fun x => ?_
    simp [Function.comp_apply, div_eq_mul_inv]
  exact Real.tendsto_log_atTop.comp h

/-- `ln y ≤ y/2` for `y ≥ 0`. -/
theorem log_le_half (y : ℝ) (hy : 0 < y) : Real.log y ≤ y / 2 := by
  have hq := Real.quadratic_le_exp_of_nonneg (by linarith : 0 ≤ y / 2)
  have : y ≤ Real.exp (y / 2) := by nlinarith [sq_nonneg (y / 2 - 1)]
  calc Real.log y ≤ Real.log (Real.exp (y / 2)) := Real.log_le_log hy this
    _ = y / 2 := Real.log_exp _

theorem tendsto_log_div_atTop :
    Tendsto (fun r : ℝ => Real.log r / r) atTop (𝓝 0) :=
  Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero

/-- The real facts behind 4.13.11 for `x` near `0−`. -/
theorem eventually_lambert_core11 {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x in 𝓝[<] (0 : ℝ),
      -Real.exp (-1) < x ∧ x < 0 ∧ 0 < eta11 x ∧
      1 / eta11 x ≤ ε ∧ Real.log (eta11 x) / eta11 x ≤ ε ∧
      |1 + lambertWm1 x / eta11 x| ≤ ε ∧ 1 ≤ Real.log (eta11 x) ∧
      1 + lambertWm1 x / eta11 x = -Real.log (eta11 x) / eta11 x -
        (-1 / eta11 x) * (-Real.log (1 - (1 + lambertWm1 x / eta11 x))) ∧
      -Real.log (1 - (1 + lambertWm1 x / eta11 x)) =
        lambertWm1 x - (-eta11 x - Real.log (eta11 x)) := by
  have hη := tendsto_eta11
  have hA : Tendsto (fun x => (Real.log 2 + Real.log (eta11 x)) / eta11 x) (𝓝[<] 0) (𝓝 0) := by
    have h1 := tendsto_log_div_atTop.comp hη
    have h2 : Tendsto (fun x => Real.log 2 / eta11 x) (𝓝[<] 0) (𝓝 0) :=
      tendsto_const_nhds.div_atTop hη
    simpa [add_div] using h2.add h1
  have hneg : ∀ᶠ x in 𝓝[<] (0 : ℝ), -Real.exp (-1) < x ∧ x < 0 := by
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Ioi_mem_nhds
      (by linarith [Real.exp_pos (-1)] : -Real.exp (-1) < 0))] with x hx h2
    exact ⟨h2, hx⟩
  filter_upwards [hneg, hη.eventually_ge_atTop (Real.exp 1),
    (tendsto_inv_atTop_zero.comp hη).eventually (ge_mem_nhds hε),
    (tendsto_log_div_atTop.comp hη).eventually (ge_mem_nhds hε),
    hA.eventually (ge_mem_nhds hε)] with x ⟨hx1, hx0⟩ hηe hσ hτ hu
  simp only [Function.comp_apply] at hσ hτ hu
  set η := eta11 x
  have hη0 : 0 < η := lt_of_lt_of_le (Real.exp_pos 1) hηe
  have hlη : 1 ≤ Real.log η := by
    rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) hηe
  obtain ⟨hW1, hWx⟩ := lambertWm1_spec hx1.le hx0
  set W := lambertWm1 x
  set y := -W
  have hy1 : 1 ≤ y := by simp only [y]; linarith
  have hy0 : 0 < y := by linarith
  -- `y − ln y = η`
  have hyη : y - Real.log y = η := by
    have h1 : y * Real.exp (-y) = -x := by simp only [y, neg_neg]; linarith
    have h2 := congrArg Real.log h1
    rw [Real.log_mul hy0.ne' (Real.exp_pos _).ne', Real.log_exp] at h2
    have h3 : η = -Real.log (-x) := by
      simp only [η, eta11]; rw [show -1 / x = (-x)⁻¹ by field_simp, Real.log_inv]
    linarith
  have hyle : y ≤ 2 * η := by have := log_le_half y hy0; linarith
  have hu_eq : 1 + W / η = -(Real.log y / η) := by
    field_simp; linarith
  have h1u : 1 - (1 + W / η) = y / η := by simp only [y]; field_simp; ring
  have hL : -Real.log (1 - (1 + W / η)) = W - (-η - Real.log η) := by
    rw [h1u, Real.log_div hy0.ne' hη0.ne']; simp only [y] at hyη ⊢; linarith
  refine ⟨hx1, hx0, hη0, by rwa [one_div], hτ, ?_, hlη, ?_, hL⟩
  · rw [hu_eq, abs_neg, abs_of_nonneg (div_nonneg (Real.log_nonneg hy1) hη0.le)]
    refine le_trans ?_ hu
    gcongr
    calc Real.log y ≤ Real.log (2 * η) := Real.log_le_log hy0 hyle
      _ = Real.log 2 + Real.log η := Real.log_mul (by norm_num) hη0.ne'
  · rw [hL]; field_simp; ring

/-- The `n`-th term `η^{−n} ∑_{m=1}^{n} [n, n − m + 1] (−ln η)ᵐ/m!` of 4.13.11. -/
noncomputable def dlmfTerm11 (η : ℝ) (n : ℕ) : ℂ :=
  1 / (η : ℂ) ^ n * ∑ m ∈ Finset.Icc 1 n, (Nat.stirlingFirst n (n - m + 1) : ℂ) *
    (-(Real.log η : ℂ)) ^ m / m !

theorem lambertInner_eq_dlmfTerm11 {η : ℝ} (hη : η ≠ 0) (n : ℕ) :
    lambertInner ((-1 / η : ℝ) : ℂ) ((-Real.log η / η : ℝ) : ℂ) n = dlmfTerm11 η n := by
  rw [lambertInner, dlmfTerm11, mul_sum]
  refine sum_congr rfl fun m hm => ?_
  have hmn := (Finset.mem_Icc.mp hm).2
  have hη' : (η : ℂ) ≠ 0 := by exact_mod_cast hη
  have hp : (η : ℂ) ^ n = (η : ℂ) ^ m * (η : ℂ) ^ (n - m) := by
    rw [← pow_add, Nat.add_sub_cancel' hmn]
  have hs : ((-1 : ℂ) ^ (n + m)) * (-1) ^ (n - m) = 1 := by
    rw [← pow_add, show n + m + (n - m) = 2 * n by omega, pow_mul]; norm_num
  push_cast
  rw [div_pow, div_pow, neg_pow (Real.log η : ℂ), hp]
  have : (m ! : ℂ) ≠ 0 := by exact_mod_cast m.factorial_ne_zero
  linear_combination ((-1) ^ m * (Nat.stirlingFirst n (n - m + 1) : ℂ) * (Real.log η : ℂ) ^ m /
    ((η : ℂ) ^ m * (η : ℂ) ^ (n - m) * m !)) * hs

/-- **DLMF 4.13.11**: as `x → 0−`, with `η = ln(−1/x)`,
`W_{±1}(x ∓ 0i) = −η − ln η + ∑_{n ≥ 1} η^{−n} ∑_{m=1}^{n} [n, n − m + 1] (−ln η)ᵐ/m!`
(`W_{−1}(x + 0i)`, equal to `W₁(x − 0i)` by `tendsto_lambertW_one_below`): the series converges
(absolutely) near `0−`, and the remainder after `N` terms is `O((ln η/η)^{N+1})`. -/
theorem dlmf_4_13_11 :
    (∀ᶠ x in 𝓝[<] (0 : ℝ),
      HasSum (fun n => dlmfTerm11 (eta11 x) (n + 1))
        (lambertW (-1) x - (-(eta11 x : ℂ) - Real.log (eta11 x))) ∧
      Summable fun n => ‖dlmfTerm11 (eta11 x) (n + 1)‖) ∧
    ∀ N : ℕ, (fun x : ℝ => lambertW (-1) (x : ℂ) - (-(eta11 x : ℂ) - Real.log (eta11 x) +
        ∑ n ∈ Finset.Icc 1 N, dlmfTerm11 (eta11 x) n)) =O[𝓝[<] (0 : ℝ)]
      fun x => (Real.log (eta11 x) / eta11 x) ^ (N + 1) := by
  have hev := eventually_lambert_core11 (ε := 1 / 16) (by norm_num)
  have hcore : ∀ᶠ x in 𝓝[<] (0 : ℝ),
      HasSum (dlmfTerm11 (eta11 x)) (lambertW (-1) x - (-(eta11 x : ℂ) - Real.log (eta11 x))) ∧
      (∀ n, ‖dlmfTerm11 (eta11 x) n‖ ≤
        (n + 1) * (4 * (Real.log (eta11 x) / eta11 x)) ^ n) ∧
      Real.log (eta11 x) / eta11 x ≤ 1 / 16 ∧ 0 ≤ Real.log (eta11 x) / eta11 x := by
    filter_upwards [hev] with x ⟨hx1, hx0, hη0, hσ, hτ, hu, hl1, heq, hL⟩
    set η := eta11 x
    set W := lambertWm1 x
    set u : ℝ := 1 + W / η
    have hu1 : u < 1 := by have := (abs_le.mp hu).2; linarith
    have hρ : Real.log η / η ≤ 1 / 16 := hτ
    have hρ0 : 0 ≤ Real.log η / η := div_nonneg (by linarith) hη0.le
    have heqc : (u : ℂ) =
        ((-Real.log η / η : ℝ) : ℂ) - ((-1 / η : ℝ) : ℂ) * lambertLogL (u : ℂ) := by
      rw [lagL_ofReal hu1]; exact_mod_cast heq
    have hnσ : ‖((-1 / η : ℝ) : ℂ)‖ = 1 / η := by
      rw [norm_real, Real.norm_eq_abs, neg_div, abs_neg, abs_of_pos (by positivity)]
    have hnτ : ‖((-Real.log η / η : ℝ) : ℂ)‖ = Real.log η / η := by
      rw [norm_real, Real.norm_eq_abs, neg_div, abs_neg, abs_of_nonneg hρ0]
    have hnu : ‖(u : ℂ)‖ ≤ 1 / 16 := by rw [norm_real, Real.norm_eq_abs]; exact hu
    have h := hasSum_lambertInner (by rw [hnσ]; linarith) (by rw [hnτ]; linarith)
      (by linarith) heqc
    rw [lagL_ofReal hu1, hL] at h
    have hW : lambertW (-1) (x : ℂ) = (W : ℂ) := lambertW_neg_one_ofReal hx1.le hx0
    refine ⟨?_, fun n => ?_, hρ, hρ0⟩
    · rw [hW]
      convert h using 1
      · funext n; rw [lambertInner_eq_dlmfTerm11 hη0.ne']
      · push_cast; ring
    · rw [← lambertInner_eq_dlmfTerm11 hη0.ne']
      refine (norm_lambertInner_le _ _ n).trans ?_
      gcongr
      rw [hnσ, hnτ]
      refine max_le ?_ le_rfl
      exact div_le_div_of_nonneg_right hl1 hη0.le
  refine ⟨?_, fun N => ?_⟩
  · filter_upwards [hcore] with x ⟨h, hb, hρ, hρ0⟩
    refine ⟨?_, ?_⟩
    · have h0 : dlmfTerm11 (eta11 x) 0 = 0 := by simp [dlmfTerm11]
      have := (hasSum_nat_add_iff' 1).mpr h
      simpa [h0] using this
    · refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => (hb (n + 1)).trans
        (two_mul_pow_le (n + 1) (by positivity))) ?_
      have hx : 2 * (4 * (Real.log (eta11 x) / eta11 x)) < 1 := by linarith
      exact (summable_geometric_of_lt_one (by positivity) hx).comp_injective
        (add_left_injective 1)
  · refine IsBigO.of_bound (2 * 8 ^ (N + 1)) ?_
    filter_upwards [hcore] with x ⟨h, hb, hρ, hρ0⟩
    set ρ := Real.log (eta11 x) / eta11 x
    have htail := (hasSum_nat_add_iff' (N + 1)).mpr h
    have hsplit : ∑ i ∈ range (N + 1), dlmfTerm11 (eta11 x) i =
        ∑ n ∈ Finset.Icc 1 N, dlmfTerm11 (eta11 x) n := by
      rw [sum_range_succ', ← Finset.Ico_add_one_right_eq_Icc, sum_Ico_eq_sum_range,
        Nat.add_sub_cancel]
      simp only [dlmfTerm11, pow_zero, Finset.Icc_eq_empty_of_lt one_pos, sum_empty, mul_zero,
        add_zero]
      refine sum_congr rfl fun i _ => by rw [add_comm 1 i]
    rw [hsplit] at htail
    have hgeo : HasSum (fun n : ℕ => (8 * ρ) ^ (n + (N + 1)))
        ((8 * ρ) ^ (N + 1) * (1 - 8 * ρ)⁻¹) := by
      have := (hasSum_geometric_of_lt_one (by positivity) (by linarith : 8 * ρ < 1)).mul_left
        ((8 * ρ) ^ (N + 1))
      convert this using 1; funext n; ring
    have hn := htail.norm_le_of_bounded hgeo fun n => by
      refine (hb (n + (N + 1))).trans ?_
      have := two_mul_pow_le (n + (N + 1)) (show 0 ≤ 4 * ρ by positivity)
      push_cast at this ⊢
      calc ((n : ℝ) + (N + 1) + 1) * (4 * ρ) ^ (n + (N + 1)) ≤ (2 * (4 * ρ)) ^ (n + (N + 1)) :=
            this
        _ = (8 * ρ) ^ (n + (N + 1)) := by ring_nf
    have hrem : lambertW (-1) (x : ℂ) - (-(eta11 x : ℂ) - Real.log (eta11 x) +
        ∑ n ∈ Finset.Icc 1 N, dlmfTerm11 (eta11 x) n) =
        lambertW (-1) (x : ℂ) - (-(eta11 x : ℂ) - Real.log (eta11 x)) -
          ∑ n ∈ Finset.Icc 1 N, dlmfTerm11 (eta11 x) n := by ring
    rw [hrem, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    refine hn.trans ?_
    have h1 : (1 - 8 * ρ)⁻¹ ≤ 2 := by
      rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
    calc (8 * ρ) ^ (N + 1) * (1 - 8 * ρ)⁻¹ ≤ (8 * ρ) ^ (N + 1) * 2 :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = 2 * 8 ^ (N + 1) * ρ ^ (N + 1) := by rw [mul_pow]; ring

end Azurite.DLMF
