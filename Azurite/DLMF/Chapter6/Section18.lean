/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter6.Section16
import Azurite.DLMF.Chapter3.Section8Newton

/-!
# DLMF §6.18: methods of computation

Formalizations of <https://dlmf.nist.gov/6.18>.

## Main results

* §6.18(ii), Acton's recurrence: `actonA`, `actonB`, `actonC` (6.18.1), `acton_initial`
  (`f = B₀`, `g = A₀`, `C₀ = 1/z`), `dlmf_6_18_2` (the recurrences 6.18.2, `ℜz > 0`), by
  Laplace-transform integration by parts (`laplace_ibp`: `ℒ(q′) = z ℒ(q)`).  The convergence of
  Miller's algorithm for 6.18.2 is not formalized (DLMF asserts only that it can be used).
* §6.18(iii): `dlmf_6_18_iii` — Newton's rule (§3.8(ii)) from the 6.13.2 approximation
  `zeroAsymp α` converges quadratically to `c_k` and `s_k` for all large `k`:
  `|x_{j+1} − ζ| ≤ 3|x_j − ζ|²`, `x_j → ζ` (`newton_trig_zero`, `newton_iter_quadratic`).
* §6.18(i), (iv) are pointers to §§6.4, 6.6, 6.9, 6.10, 6.12, 3.5(v) and to the literature;
  see the ledger (`docs/dlmf_plan.md`) for the computational status of each method.
-/

open Complex Filter Topology Set MeasureTheory Metric
open scoped Real Nat

namespace Azurite.DLMF

/-! ### §6.18(ii): Acton's recurrence 6.18.1, 6.18.2 -/

/-- `u(t) = t²/(1 + t²)`. -/
noncomputable def actonU (t : ℝ) : ℝ := t ^ 2 / (1 + t ^ 2)

/-- **DLMF 6.18.1**: `Aₙ = ∫_0^∞ t e^{−zt}/(1 + t²) (t²/(1 + t²))ⁿ dt`. -/
noncomputable def actonA (n : ℕ) (z : ℂ) : ℂ :=
  ∫ t in Ioi (0 : ℝ), cexp (-(z * t)) * ((t / (1 + t ^ 2) * actonU t ^ n : ℝ) : ℂ)

/-- **DLMF 6.18.1**: `Bₙ = ∫_0^∞ e^{−zt}/(1 + t²) (t²/(1 + t²))ⁿ dt`. -/
noncomputable def actonB (n : ℕ) (z : ℂ) : ℂ :=
  ∫ t in Ioi (0 : ℝ), cexp (-(z * t)) * ((1 / (1 + t ^ 2) * actonU t ^ n : ℝ) : ℂ)

/-- **DLMF 6.18.1**: `Cₙ = ∫_0^∞ e^{−zt} (t²/(1 + t²))ⁿ dt`. -/
noncomputable def actonC (n : ℕ) (z : ℂ) : ℂ :=
  ∫ t in Ioi (0 : ℝ), cexp (-(z * t)) * ((actonU t ^ n : ℝ) : ℂ)

theorem one_add_sq_pos (t : ℝ) : 0 < 1 + t ^ 2 := by positivity

theorem actonU_nonneg (t : ℝ) : 0 ≤ actonU t := by unfold actonU; positivity

theorem actonU_le_one (t : ℝ) : actonU t ≤ 1 := by
  unfold actonU; rw [div_le_one (one_add_sq_pos t)]; linarith

theorem div_one_add_sq_le {t : ℝ} (ht : 0 ≤ t) : t / (1 + t ^ 2) ≤ 1 := by
  rw [div_le_one (one_add_sq_pos t)]; nlinarith

theorem one_div_one_add_sq_le (t : ℝ) : 1 / (1 + t ^ 2) ≤ 1 := by
  rw [div_le_one (one_add_sq_pos t)]; nlinarith

theorem hasDerivAt_actonU (t : ℝ) : HasDerivAt actonU (2 * t / (1 + t ^ 2) ^ 2) t := by
  have h := ((hasDerivAt_pow 2 t).div ((hasDerivAt_pow 2 t).const_add 1) (one_add_sq_pos t).ne')
  refine h.congr_deriv ?_
  have := (one_add_sq_pos t).ne'
  field_simp
  ring

theorem continuous_actonU : Continuous actonU := by
  unfold actonU
  exact (continuous_pow 2).div ((continuous_pow 2).const_add 1) fun t => (one_add_sq_pos t).ne'

theorem continuous_div_one_add_sq : Continuous fun t : ℝ => t / (1 + t ^ 2) :=
  continuous_id.div ((continuous_pow 2).const_add 1) fun t => (one_add_sq_pos t).ne'

theorem continuous_one_div_one_add_sq : Continuous fun t : ℝ => 1 / (1 + t ^ 2) :=
  continuous_const.div ((continuous_pow 2).const_add 1) fun t => (one_add_sq_pos t).ne'

/-- The Laplace transform `ℒψ(z) = ∫_0^∞ e^{−zt} ψ(t) dt` of a real function. -/
noncomputable def lapR (z : ℂ) (ψ : ℝ → ℝ) : ℂ := ∫ t in Ioi (0 : ℝ), cexp (-(z * t)) * (ψ t : ℂ)

theorem integrableOn_lapR {z : ℂ} (hz : 0 < z.re) {ψ : ℝ → ℝ} (hψ : Continuous ψ) {K : ℝ}
    (hb : ∀ t : ℝ, 0 ≤ t → |ψ t| ≤ K) :
    IntegrableOn (fun t : ℝ => cexp (-(z * t)) * (ψ t : ℂ)) (Ioi 0) :=
  integrableOn_cexp_mul_of_le hz (continuous_ofReal.comp hψ) (C := K) 0 fun t ht => by
    rw [pow_zero, mul_one, Complex.norm_real, Real.norm_eq_abs]; exact hb t ht.le

/-- Linearity of `ℒ` for continuous bounded functions. -/
theorem lapR_linear {z : ℂ} (hz : 0 < z.re) {ψ₁ ψ₂ : ℝ → ℝ} (h₁ : Continuous ψ₁)
    (h₂ : Continuous ψ₂) {K : ℝ} (hb₁ : ∀ t : ℝ, 0 ≤ t → |ψ₁ t| ≤ K)
    (hb₂ : ∀ t : ℝ, 0 ≤ t → |ψ₂ t| ≤ K) (a b : ℝ) :
    lapR z (fun t => a * ψ₁ t + b * ψ₂ t) = a * lapR z ψ₁ + b * lapR z ψ₂ := by
  rw [lapR, lapR, lapR, ← integral_const_mul, ← integral_const_mul, ← integral_add
    ((integrableOn_lapR hz h₁ hb₁).const_mul _) ((integrableOn_lapR hz h₂ hb₂).const_mul _)]
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  push_cast; ring

/-- Laplace-transform integration by parts: `ℒ(q′) = z ℒ(q)` for bounded `q` with `q(0) = 0` and
bounded continuous `q′`. -/
theorem laplace_ibp {z : ℂ} (hz : 0 < z.re) {q q' : ℝ → ℝ}
    (hd : ∀ t : ℝ, HasDerivAt q (q' t) t) (hc : Continuous q') (hq0 : q 0 = 0) {M : ℝ}
    (hb : ∀ t : ℝ, 0 ≤ t → |q t| ≤ M) (hb' : ∀ t : ℝ, 0 ≤ t → |q' t| ≤ M) :
    lapR z q' = z * lapR z q := by
  have hqc : Continuous q := continuous_iff_continuousAt.2 fun t => (hd t).continuousAt
  have hI1 := integrableOn_lapR hz hqc hb
  have hI2 := integrableOn_lapR hz hc hb'
  set Φ : ℝ → ℂ := fun t => cexp (-(z * t)) * (q t : ℂ)
  have hΦ : ∀ t : ℝ, HasDerivAt Φ
      (-z * (cexp (-(z * t)) * (q t : ℂ)) + cexp (-(z * t)) * (q' t : ℂ)) t := fun t => by
    have h1 : HasDerivAt (fun s : ℝ => cexp (-(z * s))) (-z * cexp (-(z * t))) t := by
      have := (((hasDerivAt_id (t : ℂ)).const_mul z).neg.cexp).comp_ofReal
      refine this.congr_deriv ?_
      simp only [id, mul_one, Pi.neg_apply]; ring
    have := h1.mul (hd t).ofReal_comp
    refine this.congr_deriv ?_
    ring
  have hlim : Tendsto Φ atTop (𝓝 0) := by
    have hl : Tendsto (fun t : ℝ => M * Real.exp (-z.re * t)) atTop (𝓝 0) := by
      have := (Real.tendsto_exp_atBot.comp
        (tendsto_id.const_mul_atTop_of_neg (by linarith : -z.re < 0))).const_mul M
      simpa using this
    refine squeeze_zero_norm' ?_ hl
    filter_upwards [eventually_ge_atTop 0] with t ht
    rw [norm_mul, norm_cexp_neg_mul, Complex.norm_real, Real.norm_eq_abs, mul_comm, neg_mul]
    exact mul_le_mul_of_nonneg_right (hb t ht) (Real.exp_pos _).le
  have hI := integral_Ioi_of_hasDerivAt_of_tendsto (hΦ 0).continuousAt.continuousWithinAt
    (fun t _ => hΦ t) ((hI1.const_mul (-z)).add hI2) hlim
  simp only [Φ, hq0, ofReal_zero, mul_zero, sub_zero] at hI
  rw [integral_add (hI1.const_mul (-z)) hI2, integral_const_mul] at hI
  rw [lapR, lapR]
  linear_combination hI

/-- **DLMF §6.18(ii)**: `f(z) = B₀`, `g(z) = A₀`, and `C₀ = 1/z`, `ℜz > 0`. -/
theorem acton_initial {z : ℂ} (hz : 0 < z.re) :
    auxF z = actonB 0 z ∧ auxG z = actonA 0 z ∧ actonC 0 z = 1 / z := by
  have hz0 : z ≠ 0 := fun h => by simp [h] at hz
  refine ⟨?_, ?_, ?_⟩
  · rw [← dlmf_6_7_13_second hz.le, actonB]
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    push_cast; ring
  · rw [← (dlmf_6_7_14_second hz.le hz0).2 hz, actonA]
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    push_cast; ring
  · have := integral_cexp_mul_pow hz 0
    simp only [pow_zero, mul_one, Nat.factorial_zero, Nat.cast_one, zero_add, pow_one] at this
    rw [actonC]
    simpa using this

/-- **DLMF 6.18.2**: `A_{n−1} = Aₙ + (z/(2n)) Cₙ`, `B_{n−1} = (2n Bₙ + z A_{n−1})/(2n − 1)`,
`C_{n−1} = Cₙ + B_{n−1}`, `n ≥ 1`, `ℜz > 0`. -/
theorem dlmf_6_18_2 {z : ℂ} (hz : 0 < z.re) {n : ℕ} (hn : 1 ≤ n) :
    actonA (n - 1) z = actonA n z + z / (2 * n) * actonC n z ∧
      actonB (n - 1) z = (2 * n * actonB n z + z * actonA (n - 1) z) / (2 * n - 1) ∧
      actonC (n - 1) z = actonC n z + actonB (n - 1) z := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  have hpow : ∀ t k, 0 ≤ actonU t ^ k ∧ actonU t ^ k ≤ 1 := fun t k =>
    ⟨pow_nonneg (actonU_nonneg t) k, pow_le_one₀ (actonU_nonneg t) (actonU_le_one t)⟩
  have hden := one_add_sq_pos
  set a : ℕ → ℝ → ℝ := fun k t => t / (1 + t ^ 2) * actonU t ^ k
  set b : ℕ → ℝ → ℝ := fun k t => 1 / (1 + t ^ 2) * actonU t ^ k
  set c : ℕ → ℝ → ℝ := fun k t => actonU t ^ k
  have hA : ∀ k, actonA k z = lapR z (a k) := fun k => rfl
  have hB : ∀ k, actonB k z = lapR z (b k) := fun k => rfl
  have hC : ∀ k, actonC k z = lapR z (c k) := fun k => rfl
  have ca : ∀ k, Continuous (a k) := fun k =>
    continuous_div_one_add_sq.mul (continuous_actonU.pow k)
  have cb : ∀ k, Continuous (b k) := fun k =>
    continuous_one_div_one_add_sq.mul (continuous_actonU.pow k)
  have cc : ∀ k, Continuous (c k) := fun k => continuous_actonU.pow k
  have ba : ∀ k t, 0 ≤ t → |a k t| ≤ 1 := fun k t ht => by
    simp only [a]
    rw [abs_of_nonneg (by have := (hpow t k).1; positivity)]
    exact (mul_le_mul (div_one_add_sq_le ht) (hpow t k).2 (hpow t k).1 zero_le_one).trans
      (by norm_num)
  have bb : ∀ k t, 0 ≤ t → |b k t| ≤ 1 := fun k t _ => by
    simp only [b]
    rw [abs_of_nonneg (by have := (hpow t k).1; positivity)]
    exact (mul_le_mul (one_div_one_add_sq_le t) (hpow t k).2 (hpow t k).1 zero_le_one).trans
      (by norm_num)
  have bc : ∀ k t, 0 ≤ t → |c k t| ≤ 1 := fun k t _ => by
    simp only [c]; rw [abs_of_nonneg (hpow t k).1]; exact (hpow t k).2
  refine ⟨?_, ?_, ?_⟩
  · -- `q = u^{m+1}`, `q′ = 2(m+1)(a_m − a_{m+1})`
    set q' : ℝ → ℝ := fun t => 2 * (m + 1) * a m t + (-(2 * (m + 1))) * a (m + 1) t
    have hd : ∀ t : ℝ, HasDerivAt (c (m + 1)) (q' t) t := fun t => by
      refine ((hasDerivAt_actonU t).pow (m + 1)).congr_deriv ?_
      have := (hden t).ne'
      simp only [q', a, Nat.add_sub_cancel]
      push_cast
      rw [pow_succ (actonU t) m]
      generalize actonU t ^ m = V
      simp only [actonU]
      field_simp
      ring
    have hibp := laplace_ibp hz hd ((continuous_const.mul (ca m)).add
      (continuous_const.mul (ca (m + 1)))) (by simp [c, actonU]) (M := 4 * (m + 1))
      (fun t ht => (bc (m + 1) t ht).trans (by nlinarith [(m.cast_nonneg : (0 : ℝ) ≤ m)]))
      (fun t ht => by
        simp only [q']
        have h1 := ba m t ht
        have h2 := ba (m + 1) t ht
        have hm : (0 : ℝ) ≤ m := m.cast_nonneg
        rw [abs_le] at h1 h2 ⊢
        constructor <;> nlinarith [h1.1, h1.2, h2.1, h2.2])
    rw [lapR_linear hz (ca m) (ca (m + 1)) (ba m) (ba (m + 1))] at hibp
    rw [hA, hA, hC]
    have hm : (2 * ((m : ℂ) + 1)) ≠ 0 := by norm_cast
    push_cast at hibp ⊢
    field_simp
    linear_combination hibp
  · -- `q = a_m`, `q′ = (2m+1)(b_m − b_{m+1}) − b_{m+1}`
    set q' : ℝ → ℝ := fun t => (2 * m + 1) * b m t + (-(2 * m + 2)) * b (m + 1) t
    have hd : ∀ t : ℝ, HasDerivAt (a m) (q' t) t := fun t => by
      have h1 : HasDerivAt (fun s : ℝ => s / (1 + s ^ 2)) ((1 - t ^ 2) / (1 + t ^ 2) ^ 2) t := by
        have := (hasDerivAt_id t).div ((hasDerivAt_pow 2 t).const_add 1) (hden t).ne'
        refine this.congr_deriv ?_
        have := (hden t).ne'
        simp only [id]; field_simp; ring
      refine (h1.mul ((hasDerivAt_actonU t).pow m)).congr_deriv ?_
      have := (hden t).ne'
      simp only [q', b]
      rcases Nat.eq_zero_or_pos m with rfl | hm
      · simp [actonU]; field_simp; ring
      · obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
        simp only [Nat.add_sub_cancel, Pi.pow_apply]
        push_cast
        rw [pow_succ (actonU t) (k + 1), pow_succ (actonU t) k]
        generalize actonU t ^ k = V
        simp only [actonU]
        field_simp
        ring
    have hibp := laplace_ibp hz hd ((continuous_const.mul (cb m)).add
      (continuous_const.mul (cb (m + 1)))) (by simp [a]) (M := 4 * (m + 1))
      (fun t ht => (ba m t ht).trans (by nlinarith [(m.cast_nonneg : (0 : ℝ) ≤ m)]))
      (fun t ht => by
        simp only [q']
        have h1 := bb m t ht
        have h2 := bb (m + 1) t ht
        have hm : (0 : ℝ) ≤ m := m.cast_nonneg
        rw [abs_le] at h1 h2 ⊢
        constructor <;> nlinarith [h1.1, h1.2, h2.1, h2.2])
    rw [lapR_linear hz (cb m) (cb (m + 1)) (bb m) (bb (m + 1))] at hibp
    rw [hB, hB, hA]
    have h2 : (2 * ((m : ℂ) + 1) - 1) ≠ 0 := by
      intro h
      have := congrArg Complex.re h
      simp at this
      linarith [m.cast_nonneg (α := ℝ)]
    push_cast at hibp ⊢
    rw [eq_div_iff h2]
    linear_combination hibp
  · -- `u^m = u^{m+1} + b_m`
    have e : c m = fun t => 1 * c (m + 1) t + 1 * b m t := funext fun t => by
      have := (hden t).ne'
      simp only [c, b, one_mul]
      rw [pow_succ]
      generalize actonU t ^ m = V
      simp only [actonU]; field_simp; ring
    rw [hC, hC, hB, e, lapR_linear hz (cc (m + 1)) (cb m) (bc (m + 1)) (bb m)]
    push_cast; ring

/-! ### §6.18(iii): Newton's rule for the zeros `c_k`, `s_k` -/

/-- Iterating a map with `|N(z) − ζ| ≤ K|z − ζ|²` on `|z − ζ| < ½` from `|x₀ − ζ| ≤ e₀`,
`e₀ < ½`, `K e₀ ≤ ½`: the errors halve and square. -/
theorem newton_iter_quadratic {N : ℝ → ℝ} {ζ K e₀ : ℝ} (hK : 0 ≤ K)
    (hN : ∀ z, |z - ζ| < 1 / 2 → |N z - ζ| ≤ K * |z - ζ| ^ 2) {x₀ : ℝ} (h0 : |x₀ - ζ| ≤ e₀)
    (he₀ : e₀ < 1 / 2) (hKe : K * e₀ ≤ 1 / 2) :
    ∀ j : ℕ, |N^[j] x₀ - ζ| ≤ e₀ / 2 ^ j ∧ |N^[j + 1] x₀ - ζ| ≤ K * |N^[j] x₀ - ζ| ^ 2 := by
  have he0 : 0 ≤ e₀ := (abs_nonneg _).trans h0
  have hstep : ∀ j : ℕ, |N^[j] x₀ - ζ| ≤ e₀ / 2 ^ j → |N^[j + 1] x₀ - ζ| ≤ K * |N^[j] x₀ - ζ| ^ 2 ∧
      |N^[j + 1] x₀ - ζ| ≤ e₀ / 2 ^ (j + 1) := by
    intro j hj
    have hp : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
    have hj' : |N^[j] x₀ - ζ| ≤ e₀ := hj.trans (div_le_self he0 hp)
    have h1 : |N^[j + 1] x₀ - ζ| ≤ K * |N^[j] x₀ - ζ| ^ 2 := by
      rw [Function.iterate_succ_apply']; exact hN _ (by linarith)
    refine ⟨h1, h1.trans ?_⟩
    calc K * |N^[j] x₀ - ζ| ^ 2 = (K * |N^[j] x₀ - ζ|) * |N^[j] x₀ - ζ| := by ring
      _ ≤ (K * e₀) * (e₀ / 2 ^ j) := by gcongr
      _ ≤ 1 / 2 * (e₀ / 2 ^ j) := by gcongr
      _ = e₀ / 2 ^ (j + 1) := by rw [pow_succ]; field_simp
  have hall : ∀ j : ℕ, |N^[j] x₀ - ζ| ≤ e₀ / 2 ^ j := by
    intro j
    induction j with
    | zero => simpa using h0
    | succ j ih => exact (hstep j ih).2
  exact fun j => ⟨hall j, (hstep j (hall j)).1⟩

theorem tendsto_of_iter_bound {x : ℕ → ℝ} {ζ e₀ : ℝ} (h : ∀ j : ℕ, |x j - ζ| ≤ e₀ / 2 ^ j) :
    Tendsto x atTop (𝓝 ζ) := by
  have hl : Tendsto (fun j : ℕ => e₀ / 2 ^ j) atTop (𝓝 0) := by
    have := (tendsto_pow_atTop_nhds_zero_of_lt_one (r := (1 / 2 : ℝ)) (by norm_num)
      (by norm_num)).const_mul e₀
    rw [mul_zero] at this
    exact this.congr fun j => by rw [one_div_pow]; ring
  refine tendsto_iff_norm_sub_tendsto_zero.2
    (squeeze_zero (fun _ => norm_nonneg _) (fun j => ?_) hl)
  rw [Real.norm_eq_abs]; exact h j

/-- Newton's rule near a zero `ζ ∈ (α, α + 4/α]` of a function with `f′(w) = s(w)/w`, where `s` is
`± cos(w − α)` up to sign: `|N(z) − ζ| ≤ 3|z − ζ|²` for `|z − ζ| < ½`, `α ≥ 100`. -/
theorem newton_trig_zero {α ζ : ℝ} (hα : 100 ≤ α) (hζ1 : α < ζ) (hζ2 : ζ ≤ α + 4 / α)
    {f s s' : ℝ → ℝ} (hf : ∀ w : ℝ, 0 < w → HasDerivAt f (s w / w) w)
    (hs : ∀ w, HasDerivAt s (s' w) w) (hs1 : ∀ w, |s w| ≤ 1) (hs'1 : ∀ w, |s' w| ≤ 1)
    (hsα : ∀ w, |Real.cos (w - α)| ≤ |s w|) (hf0 : f ζ = 0) :
    ∀ z, |z - ζ| < 1 / 2 → |newtonStep f z - ζ| ≤ 3 * |z - ζ| ^ 2 := by
  have h4 : 4 / α ≤ 1 / 25 := by rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
  have hball : ∀ w ∈ ball ζ 1, α - 1 < w := fun w hw => by
    rw [mem_ball, Real.dist_eq, abs_lt] at hw; linarith [hw.1]
  have hpos : ∀ w ∈ ball ζ 1, 0 < w := fun w hw => by linarith [hball w hw]
  set L := 2 / (α - 1)
  have hL0 : 0 ≤ L := div_nonneg (by norm_num) (by linarith)
  -- `f′ = s/w` is `L`-Lipschitz on the ball
  have hderiv : ∀ w ∈ ball ζ 1, deriv f w = s w / w := fun w hw => (hf w (hpos w hw)).deriv
  have hLip : ∀ w ∈ ball ζ 1, ∀ v ∈ ball ζ 1, ‖deriv f w - deriv f v‖ ≤ L * ‖w - v‖ := by
    intro w hw v hv
    rw [hderiv w hw, hderiv v hv]
    have hg : ∀ u ∈ ball ζ 1, HasDerivWithinAt (fun u => s u / u)
        ((s' u * u - s u * 1) / u ^ 2) (ball ζ 1) u := fun u hu =>
      ((hs u).div (hasDerivAt_id u) (hpos u hu).ne').hasDerivWithinAt
    have hb : ∀ u ∈ ball ζ 1, ‖(s' u * u - s u * 1) / u ^ 2‖ ≤ L := fun u hu => by
      have hu0 := hpos u hu
      have hu1 := hball u hu
      rw [Real.norm_eq_abs, abs_div, abs_of_pos (pow_pos hu0 2), div_le_iff₀ (pow_pos hu0 2)]
      have e1 : |s' u * u - s u * 1| ≤ u + 1 := by
        refine (abs_sub _ _).trans ?_
        rw [abs_mul, abs_mul, abs_of_pos hu0, abs_one, mul_one]
        nlinarith [hs'1 u, hs1 u, abs_nonneg (s' u)]
      have e2 : u + 1 ≤ L * u ^ 2 := by
        have h2 : 2 * u ≤ L * u ^ 2 := by
          simp only [L]
          rw [div_mul_eq_mul_div, le_div_iff₀ (by linarith)]
          nlinarith [mul_le_mul_of_nonneg_left hu1.le hu0.le]
        linarith
      linarith
    have := (convex_ball ζ 1).norm_image_sub_le_of_norm_hasDerivWithin_le hg hb hv hw
    simpa using this
  have hz := fun z (hz : |z - ζ| < 1 / 2) =>
    newton_sq_estimate (𝕜 := ℝ) hL0 (fun w hw => (hf w (hpos w hw)).differentiableAt) hLip hf0
      (r := 1) (z := z) (by rw [Real.norm_eq_abs]; linarith)
  intro z hzζ
  have hzb : z ∈ ball ζ 1 := by rw [mem_ball, Real.dist_eq]; linarith
  have hz0 := hpos z hzb
  have hzα : |z - α| ≤ 0.6 := by
    rw [abs_lt] at hzζ; rw [abs_le]; constructor <;> linarith [hzζ.1, hzζ.2]
  have hcos : 0.8 ≤ |s z| := by
    refine le_trans ?_ (hsα z)
    have := Real.one_sub_sq_div_two_le_cos (x := z - α)
    have hsq : (z - α) ^ 2 ≤ 0.36 := by
      have := sq_abs (z - α); nlinarith [abs_nonneg (z - α)]
    rw [abs_of_pos (by nlinarith)]
    nlinarith
  have hzu : z ≤ α + 1 := by rw [abs_le] at hzα; linarith [hzα.2]
  have hd : 0.8 / (α + 1) ≤ |deriv f z| := by
    rw [hderiv z hzb, abs_div, abs_of_pos hz0]
    exact (div_le_div_iff₀ (by linarith) hz0).2 (by nlinarith)
  have h := hz z hzζ
  simp only [Real.norm_eq_abs] at h
  have hm : 0 < 0.8 / (α + 1) := by positivity
  have hK : L / (0.8 / (α + 1)) ≤ 3 := by
    simp only [L]
    rw [div_div_eq_mul_div, div_le_iff₀ (by positivity)]
    rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
    nlinarith
  calc |newtonStep f z - ζ| ≤ L * |z - ζ| ^ 2 / (0.8 / (α + 1)) := by
        rw [le_div_iff₀ hm]
        exact (mul_le_mul_of_nonneg_left hd (abs_nonneg _)).trans h
    _ = L / (0.8 / (α + 1)) * |z - ζ| ^ 2 := by ring
    _ ≤ 3 * |z - ζ| ^ 2 := by gcongr

/-- **DLMF §6.18(iii)**: Newton's rule (§3.8(ii)) started at the asymptotic approximation 6.13.2
converges quadratically to `c_k` and to `s_k` for every `k ≥ 32`: with `x₀ = zeroAsymp α`,
`|x_{j+1} − c_k| ≤ 3|x_j − c_k|²` and `x_j → c_k` (and likewise for `s_k`, `si`). -/
theorem dlmf_6_18_iii_explicit {k : ℕ} (hk : 32 ≤ k) :
    ((∀ j : ℕ, |(newtonStep CiR)^[j + 1] (zeroAsymp (k * π)) - ciZero k| ≤
        3 * |(newtonStep CiR)^[j] (zeroAsymp (k * π)) - ciZero k| ^ 2) ∧
      Tendsto (fun j => (newtonStep CiR)^[j] (zeroAsymp (k * π))) atTop (𝓝 (ciZero k))) ∧
    ((∀ j : ℕ, |(newtonStep (fun x => SiR x - π / 2))^[j + 1] (zeroAsymp ((k + 1 / 2) * π)) -
        siZero k| ≤ 3 * |(newtonStep (fun x => SiR x - π / 2))^[j]
          (zeroAsymp ((k + 1 / 2) * π)) - siZero k| ^ 2) ∧
      Tendsto (fun j => (newtonStep (fun x => SiR x - π / 2))^[j]
        (zeroAsymp ((k + 1 / 2) * π))) atTop (𝓝 (siZero k))) := by
  set C := 4 * zeroK with hCdef
  have hk32 : 32 ≤ k := hk
  have hk' : (32 : ℝ) ≤ k := by exact_mod_cast hk32
  have hπ := Real.pi_gt_d2
  have hπ4 := Real.pi_lt_four
  obtain ⟨hcC, hsC⟩ := dlmf_6_13_2_explicit hk32
  -- `C/α⁹ ≤ 1/6` for `α ≥ k`
  have hsmall : ∀ α : ℝ, 100 ≤ α → C / α ^ 9 ≤ 1 / 6 := fun α hα => by
    have hα0 : 0 < α := by linarith
    have h9 : (100 : ℝ) ^ 9 ≤ α ^ 9 := pow_le_pow_left₀ (by norm_num) hα 9
    rw [div_le_iff₀ (by positivity), show C = 4 * 434831 by rw [hCdef, zeroK_eq]]
    norm_num at h9 ⊢
    linarith
  have hgen : ∀ (f s s' : ℝ → ℝ) (α ζ : ℝ), 100 ≤ α → (k : ℝ) ≤ α →
      ζ ∈ Ioo (α - π / 2) (α + π / 2) →
      fR ζ * Real.sin (ζ - α) - gR ζ * Real.cos (ζ - α) = 0 →
      (∀ w : ℝ, 0 < w → HasDerivAt f (s w / w) w) → (∀ w, HasDerivAt s (s' w) w) →
      (∀ w, |s w| ≤ 1) → (∀ w, |s' w| ≤ 1) → (∀ w, |Real.cos (w - α)| ≤ |s w|) → f ζ = 0 →
      |ζ - zeroAsymp α| ≤ C / α ^ 9 →
      (∀ j : ℕ, |(newtonStep f)^[j + 1] (zeroAsymp α) - ζ| ≤
        3 * |(newtonStep f)^[j] (zeroAsymp α) - ζ| ^ 2) ∧
      Tendsto (fun j => (newtonStep f)^[j] (zeroAsymp α)) atTop (𝓝 ζ) := by
    intro f s s' α ζ hα hkα hζ h0 hf hs hs1 hs'1 hsα hf0 hb
    obtain ⟨hζ1, hζ2⟩ := zero_location hα hζ h0
    have hN := newton_trig_zero hα hζ1 hζ2 hf hs hs1 hs'1 hsα hf0
    have he : |zeroAsymp α - ζ| ≤ 1 / 6 := by
      rw [abs_sub_comm]; exact hb.trans (hsmall α hα)
    have hit := newton_iter_quadratic (by norm_num) hN he (by norm_num) (by norm_num)
    exact ⟨fun j => (hit j).2, tendsto_of_iter_bound fun j => (hit j).1⟩
  constructor
  · have hα : 100 ≤ (k : ℝ) * π := by nlinarith
    have hmem := ciZero_mem (k := k) (by omega)
    have hzero : CiR (ciZero k) = 0 := by
      obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
      exact (ciZero_succ_spec n).2
    have hpos : 0 < ciZero k := by linarith [hmem.1]
    have h0 : fR (ciZero k) * Real.sin (ciZero k - k * π) -
        gR (ciZero k) * Real.cos (ciZero k - k * π) = 0 := by
      have := CiR_eq_psi hpos k
      rw [hzero] at this
      rcases neg_one_pow_eq_or ℝ k with h | h <;> rw [h] at this <;> linarith
    refine hgen CiR Real.cos (fun w => -Real.sin w) _ _ hα (by nlinarith) hmem h0
      (fun w hw => hasDerivAt_CiR hw) Real.hasDerivAt_cos Real.abs_cos_le_one
      (fun w => by rw [abs_neg]; exact Real.abs_sin_le_one w) (fun w => le_of_eq ?_) hzero hcC
    rw [show w - k * π = -(k * π - w) by ring, Real.cos_neg, Real.cos_nat_mul_pi_sub, abs_mul,
      abs_pow, abs_neg, abs_one, one_pow, one_mul]
  · have hα : 100 ≤ ((k : ℝ) + 1 / 2) * π := by nlinarith
    obtain ⟨⟨hm1, hm2⟩, hzero⟩ := siZero_spec k
    have hmem : siZero k ∈ Ioo ((k + 1 / 2) * π - π / 2) ((k + 1 / 2) * π + π / 2) :=
      ⟨by linarith, by linarith⟩
    have hpos : 0 < siZero k := by linarith [hmem.1, Real.pi_pos]
    have h0 : fR (siZero k) * Real.sin (siZero k - (k + 1 / 2) * π) -
        gR (siZero k) * Real.cos (siZero k - (k + 1 / 2) * π) = 0 := by
      have := siR_eq_psi hpos k
      rw [hzero, sub_self] at this
      rcases neg_one_pow_eq_or ℝ k with h | h <;> rw [h] at this <;> linarith
    refine hgen (fun x => SiR x - π / 2) Real.sin Real.cos _ _ hα (by nlinarith) hmem h0
      (fun w hw => (hasDerivAt_SiR' hw.ne').sub_const (π / 2)) Real.hasDerivAt_sin
      Real.abs_sin_le_one Real.abs_cos_le_one (fun w => le_of_eq ?_) (by simp [hzero]) hsC
    rw [show w - (k + 1 / 2) * π = (w - k * π) - π / 2 by ring, Real.cos_sub_pi_div_two,
      show w - k * π = -(k * π - w) by ring, Real.sin_neg, Real.sin_nat_mul_pi_sub, abs_neg,
      abs_neg, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]

end Azurite.DLMF

namespace Azurite.DLMF

/-- **DLMF §6.18(iii)** (existential form; `K₀ = 32`, `dlmf_6_18_iii_explicit`). -/
theorem dlmf_6_18_iii : ∃ K₀ : ℕ, ∀ k : ℕ, K₀ ≤ k →
    ((∀ j : ℕ, |(newtonStep CiR)^[j + 1] (zeroAsymp (k * π)) - ciZero k| ≤
        3 * |(newtonStep CiR)^[j] (zeroAsymp (k * π)) - ciZero k| ^ 2) ∧
      Tendsto (fun j => (newtonStep CiR)^[j] (zeroAsymp (k * π))) atTop (𝓝 (ciZero k))) ∧
    ((∀ j : ℕ, |(newtonStep (fun x => SiR x - π / 2))^[j + 1] (zeroAsymp ((k + 1 / 2) * π)) -
        siZero k| ≤ 3 * |(newtonStep (fun x => SiR x - π / 2))^[j]
          (zeroAsymp ((k + 1 / 2) * π)) - siZero k| ^ 2) ∧
      Tendsto (fun j => (newtonStep (fun x => SiR x - π / 2))^[j]
        (zeroAsymp ((k + 1 / 2) * π))) atTop (𝓝 (siZero k))) :=
  ⟨32, fun _ hk => dlmf_6_18_iii_explicit hk⟩

end Azurite.DLMF
