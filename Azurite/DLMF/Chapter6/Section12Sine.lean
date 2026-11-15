/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter6.Section12
import Azurite.DLMF.Chapter2.Section4Watson
import Azurite.DLMF.Chapter4.Section38
import Azurite.DLMF.Chapter5.Section10

/-!
# DLMF §6.12(ii): asymptotic expansions of the auxiliary functions `f`, `g`

Formalizations of <https://dlmf.nist.gov/6.12.ii>.  (The expansions of `Si`, `Ci` themselves are
6.2.19, 6.2.20 together with these.)

## Main results

* `fAsymp`, `gAsymp`: the partial sums of 6.12.3, 6.12.4 (6.12.5, 6.12.6).
* `dlmf_6_12_3`, `dlmf_6_12_4`: `f(z) − fAsymp n z = O(|z|^{−2n−1})`,
  `g(z) − gAsymp n z = O(|z|^{−2n−2})` as `z → ∞` in `|ph z| ≤ π − δ`, from 6.12.1 through
  `g ± i f = e^{∓iz}E₁(z e^{∓πi/2})` (`auxGF_asymp`; the even and odd terms of the two `E₁`
  expansions separate the `f` and `g` series, `e1AsympRot_even`, `e1AsympRot_odd`).
* `dlmf_6_12_7`, `dlmf_6_12_8`: the remainders as Laplace integrals, `ℜz > 0`.
* The remainder bounds: `dlmf_6_12_remainder_right` (`|ph z| ≤ π/4`: at most the first neglected
  terms), `dlmf_6_12_remainder_real` (`ph z = 0`: also of the same signs),
  `dlmf_6_12_remainder_left` (`π/4 ≤ |ph z| < π/2`: at most `csc(2|ph z|)` times them).  These
  rotate the Laplace integrals 6.12.7, 6.12.8 to the ray `t = z̄τ/|z|` (`auxF_sub_fAsymp_ray`,
  via the `E₁` lift `tendsto_integral_laplace_ray`), on which `e^{−zt} = e^{−|z|τ}` and
  `|t² + 1| ≥ 1` resp. `≥ sin(2|ph z|)` (`norm_ray_sq_add_one_ge`).
-/

open Complex Filter Topology Set MeasureTheory
open scoped Real Nat

namespace Azurite.DLMF

/-! ### The partial sums -/

/-- The partial sum `(1/z) ∑_{m<n} (−1)^m (2m)!/z^{2m}` of 6.12.3, 6.12.5. -/
noncomputable def fAsymp (n : ℕ) (z : ℂ) : ℂ :=
  1 / z * ∑ m ∈ Finset.range n, (-1) ^ m * ((2 * m) ! : ℂ) / z ^ (2 * m)

/-- The partial sum `(1/z²) ∑_{m<n} (−1)^m (2m+1)!/z^{2m}` of 6.12.4, 6.12.6. -/
noncomputable def gAsymp (n : ℕ) (z : ℂ) : ℂ :=
  1 / z ^ 2 * ∑ m ∈ Finset.range n, (-1) ^ m * ((2 * m + 1) ! : ℂ) / z ^ (2 * m)

theorem fAsymp_eq (n : ℕ) (z : ℂ) :
    fAsymp n z = ∑ m ∈ Finset.range n, (-1) ^ m * ((2 * m) ! : ℂ) / z ^ (2 * m + 1) := by
  rw [fAsymp, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [pow_succ]
  ring

theorem gAsymp_eq (n : ℕ) (z : ℂ) :
    gAsymp n z = ∑ m ∈ Finset.range n, (-1) ^ m * ((2 * m + 1) ! : ℂ) / z ^ (2 * m + 2) := by
  rw [gAsymp, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [pow_add]
  ring

/-- `e^{u} × (the partial sum of 6.12.1 at u) = ∑_{s<N} (−1)^s s!/u^{s+1}`. -/
theorem cexp_mul_e1Asymp (N : ℕ) (u : ℂ) :
    cexp u * e1Asymp N u = ∑ s ∈ Finset.range N, (-1) ^ s * (s ! : ℂ) / u ^ (s + 1) := by
  rw [e1Asymp, ← mul_assoc, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  calc cexp u * (cexp (-u) / u) * ((-1) ^ s * (s ! : ℂ) / u ^ s) =
      (cexp u * cexp (-u)) * ((-1) ^ s * (s ! : ℂ) / (u * u ^ s)) := by ring
    _ = _ := by rw [← exp_add, add_neg_cancel, exp_zero, one_mul, ← pow_succ']

/-- `∑_{s<N} (−1)^s s!/(σiz)^{s+1}`, the partial sums of `e^{σiz}E₁(σiz)`. -/
noncomputable def e1AsympRot (σ : ℂ) (N : ℕ) (z : ℂ) : ℂ :=
  ∑ s ∈ Finset.range N, (-1) ^ s * (s ! : ℂ) / (σ * I * z) ^ (s + 1)

theorem I_pow_two_mul_add_two (m : ℕ) : I ^ (2 * m + 2) = (-1) ^ (m + 1) := by
  rw [show 2 * m + 2 = 2 * (m + 1) by ring, pow_mul, I_sq]

theorem term_even {z : ℂ} (hz : z ≠ 0) (m : ℕ) (c : ℂ) :
    (-1) ^ (2 * m) * c / ((-1) * I * z) ^ (2 * m + 1) -
        (-1) ^ (2 * m) * c / (1 * I * z) ^ (2 * m + 1) = 2 * I * ((-1) ^ m * c / z ^ (2 * m + 1)) ∧
      (-1) ^ (2 * m) * c / ((-1) * I * z) ^ (2 * m + 1) +
        (-1) ^ (2 * m) * c / (1 * I * z) ^ (2 * m + 1) = 0 := by
  set s : ℂ := (-1) ^ m
  set K := z ^ (2 * m + 1)
  have h1 : ((-1) * I * z) ^ (2 * m + 1) = -(s * I * K) := by
    rw [mul_pow, mul_pow, I_pow_two_mul_add_one, show ((-1 : ℂ)) ^ (2 * m + 1) = -1 by
      rw [pow_succ, pow_mul]; norm_num]
    ring
  have h2 : (1 * I * z) ^ (2 * m + 1) = s * I * K := by
    rw [one_mul, mul_pow, I_pow_two_mul_add_one]
  have hpm : s * s = 1 := by rw [← mul_pow]; norm_num
  have hs : s ≠ 0 := pow_ne_zero _ (by norm_num)
  have hK : K ≠ 0 := pow_ne_zero _ hz
  rw [h1, h2, pow_mul, neg_one_sq, one_pow, one_mul]
  clear_value s K
  constructor
  · rw [div_neg, ← neg_add', ← two_mul, eq_comm, ← sub_eq_zero]
    have : I * s * c / K + c / (s * I * K) = 0 := by
      field_simp
      linear_combination c * s ^ 2 * I_sq - c * hpm
    linear_combination 2 * this
  · rw [div_neg, neg_add_cancel]

theorem term_odd {z : ℂ} (hz : z ≠ 0) (m : ℕ) (c : ℂ) :
    (-1) ^ (2 * m + 1) * c / ((-1) * I * z) ^ (2 * m + 2) -
        (-1) ^ (2 * m + 1) * c / (1 * I * z) ^ (2 * m + 2) = 0 ∧
      (-1) ^ (2 * m + 1) * c / ((-1) * I * z) ^ (2 * m + 2) +
        (-1) ^ (2 * m + 1) * c / (1 * I * z) ^ (2 * m + 2) =
        2 * ((-1) ^ m * c / z ^ (2 * m + 2)) := by
  set s : ℂ := (-1) ^ m
  set K := z ^ (2 * m + 2)
  have h1 : ((-1) * I * z) ^ (2 * m + 2) = -(s * K) := by
    rw [mul_pow, mul_pow, I_pow_two_mul_add_two, show ((-1 : ℂ)) ^ (2 * m + 2) = 1 by
      rw [show 2 * m + 2 = 2 * (m + 1) by ring, pow_mul]; norm_num, pow_succ]
    ring
  have h2 : (1 * I * z) ^ (2 * m + 2) = -(s * K) := by
    rw [one_mul, mul_pow, I_pow_two_mul_add_two, pow_succ]; ring
  have hpm : s * s = 1 := by rw [← mul_pow]; norm_num
  have hs : s ≠ 0 := pow_ne_zero _ (by norm_num)
  have hK : K ≠ 0 := pow_ne_zero _ hz
  have hodd : ((-1 : ℂ)) ^ (2 * m + 1) = -1 := by rw [pow_succ, pow_mul]; norm_num
  rw [h1, h2, sub_self, hodd]
  clear_value s K
  refine ⟨rfl, ?_⟩
  field_simp
  linear_combination (-2 * c) * hpm

theorem e1AsympRot_even {z : ℂ} (hz : z ≠ 0) (n : ℕ) :
    e1AsympRot (-1) (2 * n) z - e1AsympRot 1 (2 * n) z = 2 * I * fAsymp n z ∧
      e1AsympRot (-1) (2 * n) z + e1AsympRot 1 (2 * n) z = 2 * gAsymp n z := by
  induction n with
  | zero => simp [e1AsympRot, fAsymp, gAsymp]
  | succ n ih =>
    rw [fAsymp_eq] at ih ⊢
    rw [gAsymp_eq] at ih ⊢
    simp only [e1AsympRot, show 2 * (n + 1) = 2 * n + 1 + 1 by ring, Finset.sum_range_succ]
      at ih ⊢
    obtain ⟨e1, e2⟩ := term_even hz n ((2 * n) ! : ℂ)
    obtain ⟨o1, o2⟩ := term_odd hz n ((2 * n + 1) ! : ℂ)
    constructor
    · linear_combination ih.1 + e1 + o1
    · linear_combination ih.2 + e2 + o2

theorem e1AsympRot_odd {z : ℂ} (hz : z ≠ 0) (n : ℕ) :
    e1AsympRot (-1) (2 * n + 1) z + e1AsympRot 1 (2 * n + 1) z = 2 * gAsymp n z := by
  have h := (e1AsympRot_even hz n).2
  simp only [e1AsympRot, Finset.sum_range_succ] at h ⊢
  have e2 := (term_even hz n ((2 * n) ! : ℂ)).2
  linear_combination h + e2

/-! ### 6.12.3, 6.12.4 -/

/-- `g ± i f = e^{∓iz}E₁(∓iz)`, expanded by 6.12.1 with `N` terms: error `O(|z|^{−N−1})`. -/
theorem auxGF_asymp (N : ℕ) {δ : ℝ} (hδ : 0 < δ) (hδ' : δ ≤ π) :
    ∃ C : ℝ, ∀ z ∈ slitPlane, |arg z| ≤ π - δ → 1 ≤ ‖z‖ →
      ‖auxG z + I * auxF z - e1AsympRot (-1) N z‖ ≤ C / ‖z‖ ^ (N + 1) ∧
        ‖auxG z - I * auxF z - e1AsympRot 1 N z‖ ≤ C / ‖z‖ ^ (N + 1) := by
  obtain ⟨C, hC⟩ := dlmf_6_12_1 N hδ hδ'
  refine ⟨C, fun z hz harg h1 => ?_⟩
  have hz0 := slitPlane_ne_zero hz
  obtain ⟨e1, e2⟩ := auxG_add_I_mul_auxF hz
  have hπ := Real.pi_pos
  have key : ∀ σ : ℂ, (σ = 1 ∨ σ = -1) →
      ‖cexp (σ * I * z) * E1Gen (log z + σ * (π / 2 * I)) - e1AsympRot σ N z‖ ≤
        C / ‖z‖ ^ (N + 1) := by
    intro σ hσ
    have hσn : ‖σ‖ = 1 := by rcases hσ with rfl | rfl <;> simp
    have hw := exp_log_add_half_pi hz0 σ hσ
    have him : |(log z + σ * (π / 2 * I)).im| ≤ 3 * π / 2 - δ := by
      rw [add_im, log_im]
      rcases hσ with rfl | rfl <;> simp <;> rw [abs_le] at harg ⊢ <;> constructor <;> linarith
    have hre : 0 ≤ (log z + σ * (π / 2 * I)).re := by
      rcases hσ with rfl | rfl <;> simp [log_re, Real.log_nonneg h1]
    have h := hC _ him hre
    rw [hw] at h
    have hnorm : ‖σ * I * z‖ = ‖z‖ := by rw [norm_mul, norm_mul, hσn, norm_I, one_mul, one_mul]
    have hexp : ‖cexp (σ * I * z)‖ * ‖cexp (-(σ * I * z))‖ = 1 := by
      rw [← norm_mul, ← exp_add, add_neg_cancel, exp_zero, norm_one]
    have he : e1AsympRot σ N z = cexp (σ * I * z) * e1Asymp N (σ * I * z) := by
      rw [cexp_mul_e1Asymp, e1AsympRot]
    rw [he, ← mul_sub, norm_mul]
    calc ‖cexp (σ * I * z)‖ * ‖E1Gen (log z + σ * (π / 2 * I)) - e1Asymp N (σ * I * z)‖
        ≤ ‖cexp (σ * I * z)‖ * (C * (‖cexp (-(σ * I * z))‖ / ‖σ * I * z‖ ^ (N + 1))) := by
          gcongr
      _ = (‖cexp (σ * I * z)‖ * ‖cexp (-(σ * I * z))‖) * C / ‖z‖ ^ (N + 1) := by
          rw [hnorm]; ring
      _ = C / ‖z‖ ^ (N + 1) := by rw [hexp, one_mul]
  refine ⟨?_, ?_⟩
  · have := key (-1) (Or.inr rfl)
    rwa [show (-1 : ℂ) * I * z = -I * z by ring, show (-1 : ℂ) * (π / 2 * I) = -(π / 2 * I) by
      ring, ← e1] at this
  · have := key 1 (Or.inl rfl)
    rwa [show (1 : ℂ) * I * z = I * z by ring, one_mul, ← e2] at this

/-- **DLMF 6.12.3**: `f(z) = (1/z) ∑_{m<n} (−1)^m (2m)!/z^{2m} + O(|z|^{−2n−1})` as `z → ∞` in
`|ph z| ≤ π − δ`. -/
theorem dlmf_6_12_3 (n : ℕ) {δ : ℝ} (hδ : 0 < δ) (hδ' : δ ≤ π) :
    ∃ C : ℝ, ∀ z ∈ slitPlane, |arg z| ≤ π - δ → 1 ≤ ‖z‖ →
      ‖auxF z - fAsymp n z‖ ≤ C / ‖z‖ ^ (2 * n + 1) := by
  obtain ⟨C, hC⟩ := auxGF_asymp (2 * n) hδ hδ'
  refine ⟨C, fun z hz harg h1 => ?_⟩
  obtain ⟨hP, hM⟩ := hC z hz harg h1
  have hz0 := slitPlane_ne_zero hz
  have e : auxF z - fAsymp n z = ((auxG z + I * auxF z - e1AsympRot (-1) (2 * n) z) -
      (auxG z - I * auxF z - e1AsympRot 1 (2 * n) z)) / (2 * I) := by
    have := (e1AsympRot_even hz0 n).1
    field_simp
    linear_combination this
  rw [e, norm_div, norm_mul, norm_I, mul_one, Complex.norm_two]
  have := norm_sub_le (auxG z + I * auxF z - e1AsympRot (-1) (2 * n) z)
    (auxG z - I * auxF z - e1AsympRot 1 (2 * n) z)
  rw [div_le_iff₀ two_pos]
  linarith

/-- **DLMF 6.12.4**: `g(z) = (1/z²) ∑_{m<n} (−1)^m (2m+1)!/z^{2m} + O(|z|^{−2n−2})` as `z → ∞`
in `|ph z| ≤ π − δ`. -/
theorem dlmf_6_12_4 (n : ℕ) {δ : ℝ} (hδ : 0 < δ) (hδ' : δ ≤ π) :
    ∃ C : ℝ, ∀ z ∈ slitPlane, |arg z| ≤ π - δ → 1 ≤ ‖z‖ →
      ‖auxG z - gAsymp n z‖ ≤ C / ‖z‖ ^ (2 * n + 2) := by
  obtain ⟨C, hC⟩ := auxGF_asymp (2 * n + 1) hδ hδ'
  refine ⟨C, fun z hz harg h1 => ?_⟩
  obtain ⟨hP, hM⟩ := hC z hz harg h1
  have hz0 := slitPlane_ne_zero hz
  have e : auxG z - gAsymp n z = ((auxG z + I * auxF z - e1AsympRot (-1) (2 * n + 1) z) +
      (auxG z - I * auxF z - e1AsympRot 1 (2 * n + 1) z)) / 2 := by
    have := e1AsympRot_odd hz0 n
    linear_combination this / 2
  rw [e, norm_div, Complex.norm_two]
  have := norm_add_le (auxG z + I * auxF z - e1AsympRot (-1) (2 * n + 1) z)
    (auxG z - I * auxF z - e1AsympRot 1 (2 * n + 1) z)
  rw [div_le_iff₀ two_pos]
  linarith

/-! ### Laplace integrals along rays -/

theorem ray_add_ne {ω : ℂ} (hω : 0 < ω.re) (σ : ℂ) (hσ : σ = 1 ∨ σ = -1) (τ : ℝ) :
    ω * τ + σ * I ≠ 0 := by
  intro h
  have h1 := congrArg Complex.re h
  have h2 := congrArg Complex.im h
  rcases hσ with rfl | rfl <;> simp at h1 h2 <;>
    rcases h1 with h1 | h1 <;> simp_all

theorem ray_sq_add_one_eq (ω : ℂ) (τ : ℝ) :
    (ω * τ) ^ 2 + 1 = (ω * τ + -1 * I) * (ω * τ + 1 * I) := by
  linear_combination I_sq

theorem ray_sq_add_one_ne {ω : ℂ} (hω : 0 < ω.re) (τ : ℝ) : (ω * τ) ^ 2 + 1 ≠ 0 := by
  rw [ray_sq_add_one_eq]
  exact mul_ne_zero (ray_add_ne hω _ (Or.inr rfl) τ) (ray_add_ne hω _ (Or.inl rfl) τ)

/-- Along the ray `t = ωτ` (`ℜz > 0`, `ℜω > 0`, `ℜ(zω) > 0`):
`∫_0^∞ e^{−zωτ} ω/(ωτ ± i) dτ = e^{±iz} E1Gen(ln z ± πi/2)` (improper). -/
theorem tendsto_integral_laplace_ray {z ω : ℂ} (hz : 0 < z.re) (hω : 0 < ω.re)
    (ha : 0 < (z * ω).re) (σ : ℂ) (hσ : σ = 1 ∨ σ = -1) :
    Tendsto (fun R => ∫ τ in (0 : ℝ)..R, cexp (-(z * ω * τ)) * ω / (ω * τ + σ * I)) atTop
      (𝓝 (cexp (σ * I * z) * E1Gen (log z + σ * (π / 2 * I)))) := by
  have hz0 : z ≠ 0 := fun h => by simp [h] at hz
  have hne := ray_add_ne hω σ hσ
  have hslit : ∀ τ : ℝ, 0 ≤ τ → ω * τ + σ * I ∈ slitPlane := fun τ hτ =>
    mem_slitPlane_of_re_nonneg (by
      rcases hσ with rfl | rfl <;> simp [mul_re] <;> positivity) (hne τ)
  set ℓ : ℝ → ℂ := fun τ => log z + log (ω * τ + σ * I) with hℓ
  have hℓd : ∀ τ : ℝ, 0 ≤ τ → HasDerivAt ℓ (z * ω / (z * ω * τ + z * (σ * I))) τ := by
    intro τ hτ
    have h1 : HasDerivAt (fun v : ℂ => log z + log (ω * v + σ * I))
        (ω * 1 / (ω * τ + σ * I)) τ := by
      have := (((hasDerivAt_id (τ : ℂ)).const_mul ω).add_const (σ * I)).clog (hslit τ hτ)
      simpa using this.const_add (log z)
    refine h1.comp_ofReal.congr_deriv ?_
    have := hne τ
    rw [show z * ω * τ + z * (σ * I) = z * (ω * τ + σ * I) by ring]
    field_simp
  have hexp : ∀ τ : ℝ, 0 ≤ τ → cexp (ℓ τ) = z * ω * τ + z * (σ * I) := fun τ hτ => by
    simp only [hℓ]
    rw [exp_add, exp_log hz0, exp_log (hne τ)]
    ring
  have hℓ0 : ℓ 0 = log z + σ * (π / 2 * I) := by
    simp only [hℓ, ofReal_zero, mul_zero, zero_add]
    rcases hσ with rfl | rfl
    · rw [one_mul, log_I]; ring
    · rw [neg_one_mul, log_neg_I]; ring
  have hstrip : ∀ R : ℝ, 0 < R → ℓ R ∈ logStrip := by
    intro R hR
    have h1 := abs_lt.mp (abs_arg_lt_pi_div_two_iff.mpr (Or.inl hz))
    have h2 := abs_le.mp (abs_arg_le_pi_div_two_iff.mpr (show 0 ≤ (ω * R + σ * I).re by
      rcases hσ with rfl | rfl <;> simp [mul_re] <;> positivity))
    show -π < (ℓ R).im ∧ (ℓ R).im < π
    simp only [hℓ, add_im, log_im]
    constructor <;> linarith
  set w : ℝ → ℂ := fun R => z * ω * R + z * (σ * I)
  set r₀ : ℝ := (z * (σ * I)).re
  have hwre : ∀ R : ℝ, (w R).re = (z * ω).re * R + r₀ := fun R => by
    simp [w, r₀, mul_re]
  have hlim : Tendsto (fun R => E1Gen (ℓ R)) atTop (𝓝 0) := by
    have heq : ∀ᶠ R : ℝ in atTop, E1Gen (ℓ R) = expIntE₁ (w R) := by
      filter_upwards [eventually_gt_atTop 0] with R hR
      rw [(dlmf_6_4_1).2.1 _ (hstrip R hR), hexp R hR.le]
    have hre : Tendsto (fun R => (w R).re) atTop atTop := by
      simp only [hwre]
      exact tendsto_atTop_add_const_right _ _ (tendsto_id.const_mul_atTop ha)
    refine (tendsto_expIntE₁_zero (w := w) (r₀ := r₀) ?_
      ((eventually_ge_atTop 0).mono fun R hR => ?_)
      (tendsto_atTop_mono (fun R => le_max_right _ _) hre)).congr'
      (heq.mono fun R h => h.symm)
    · filter_upwards [eventually_gt_atTop 0] with R hR
      show z * ω * R + z * (σ * I) ∈ slitPlane
      rw [← hexp R hR.le]
      exact exp_mem_slitPlane (hstrip R hR)
    · rw [hwre]; nlinarith
  have h := tendsto_integral_of_E1Gen_lift (z * ω) (z * (σ * I)) 0 hℓd hexp hlim
    (f := fun τ => cexp (-(z * ω * τ)) * ω / (ω * τ + σ * I)) (fun τ _ => by
      have := hne τ
      rw [show z * ω * τ + z * (σ * I) = z * (ω * τ + σ * I) by ring]
      field_simp)
  rw [hℓ0, show z * (σ * I) = σ * I * z by ring] at h
  exact h

theorem continuous_laplace_ray (z : ℂ) {ω : ℂ} (hω : 0 < ω.re) (σ : ℂ)
    (hσ : σ = 1 ∨ σ = -1) :
    Continuous fun τ : ℝ => cexp (-(z * ω * τ)) * ω / (ω * τ + σ * I) :=
  (by fun_prop : Continuous fun τ : ℝ => cexp (-(z * ω * τ)) * ω).div (by fun_prop)
    (ray_add_ne hω σ hσ)

/-- **6.7.13, 6.7.14 along the ray `t = ωτ`**: improper Laplace integrals of `1/(t² + 1)` and
`t/(t² + 1)`. -/
theorem tendsto_laplace_f_g_ray {z ω : ℂ} (hz : 0 < z.re) (hω : 0 < ω.re)
    (ha : 0 < (z * ω).re) :
    Tendsto (fun R => ∫ τ in (0 : ℝ)..R, cexp (-(z * ω * τ)) * ω / ((ω * τ) ^ 2 + 1)) atTop
        (𝓝 (auxF z)) ∧
      Tendsto (fun R => ∫ τ in (0 : ℝ)..R,
        ω * τ * (cexp (-(z * ω * τ)) * ω) / ((ω * τ) ^ 2 + 1)) atTop (𝓝 (auxG z)) := by
  have hz' : z ∈ slitPlane := mem_slitPlane_of_re_pos hz
  obtain ⟨e1, e2⟩ := auxG_add_I_mul_auxF hz'
  have hm := tendsto_integral_laplace_ray hz hω ha (-1) (Or.inr rfl)
  have hp := tendsto_integral_laplace_ray hz hω ha 1 (Or.inl rfl)
  rw [show (-1 : ℂ) * I * z = -I * z by ring, show (-1 : ℂ) * (π / 2 * I) = -(π / 2 * I) by ring,
    ← e1] at hm
  rw [show (1 : ℂ) * I * z = I * z by ring, show (1 : ℂ) * (π / 2 * I) = π / 2 * I by ring,
    ← e2] at hp
  have hc1 := continuous_laplace_ray z hω (-1) (Or.inr rfl)
  have hc2 := continuous_laplace_ray z hω 1 (Or.inl rfl)
  have hne1 := ray_add_ne hω (-1) (Or.inr rfl)
  have hne2 := ray_add_ne hω 1 (Or.inl rfl)
  constructor
  · have h := tendsto_integral_lin (κ₁ := 1 / (2 * I)) (κ₂ := -(1 / (2 * I))) hc1 hc2 hm hp
      (f := fun τ : ℝ => cexp (-(z * ω * τ)) * ω / ((ω * τ) ^ 2 + 1)) (fun τ => by
        rw [ray_sq_add_one_eq]
        exact pf_f (hne1 τ) (hne2 τ) (mul_ne_zero two_ne_zero I_ne_zero) (by ring))
    convert h using 2
    field_simp
    ring
  · have h := tendsto_integral_lin (κ₁ := 1 / 2) (κ₂ := 1 / 2) hc1 hc2 hm hp
      (f := fun τ : ℝ => ω * τ * (cexp (-(z * ω * τ)) * ω) / ((ω * τ) ^ 2 + 1)) (fun τ => by
        rw [ray_sq_add_one_eq]
        exact pf_g (hne1 τ) (hne2 τ) (by ring))
    convert h using 2
    ring

/-! ### The remainders 6.12.7, 6.12.8 -/

/-- `∫_0^∞ e^{−aτ} τ^k dτ = k!/a^{k+1}`, `ℜa > 0`. -/
theorem integral_cexp_mul_pow {a : ℂ} (ha : 0 < a.re) (k : ℕ) :
    ∫ τ in Ioi (0 : ℝ), cexp (-(a * τ)) * (τ : ℂ) ^ k = k ! / a ^ (k + 1) := by
  have h := integral_cpow_mul_cexp_neg_complex (a := (k : ℂ) + 1) (by simp; positivity) ha
  rw [show (k : ℂ) + 1 = ((k + 1 : ℕ) : ℂ) by push_cast; ring, cpow_natCast,
    show Complex.Gamma ((k + 1 : ℕ) : ℂ) = ((k ! : ℕ) : ℂ) by
      rw [Nat.cast_succ, Complex.Gamma_nat_eq_factorial]] at h
  have e : (k ! : ℂ) / a ^ (k + 1) = (1 / a) ^ (k + 1) * (k ! : ℂ) := by
    rw [one_div_pow]; ring
  rw [e, ← h]
  refine setIntegral_congr_fun measurableSet_Ioi fun τ _ => ?_
  rw [show ((k + 1 : ℕ) : ℂ) - 1 = (k : ℕ) by push_cast; ring, cpow_natCast, mul_comm]

/-- Integrability of `e^{−aτ} h(τ)` for continuous `h` with `|h(τ)| ≤ Cτ^k`. -/
theorem integrableOn_cexp_mul_of_le {a : ℂ} (ha : 0 < a.re) {h : ℝ → ℂ} (hh : Continuous h)
    {C : ℝ} (k : ℕ) (hb : ∀ τ : ℝ, 0 < τ → ‖h τ‖ ≤ C * τ ^ k) :
    IntegrableOn (fun τ : ℝ => cexp (-(a * τ)) * h τ) (Ioi 0) := by
  refine ((integrableOn_pow_mul_exp_neg_mul k ha).const_mul C).mono'
    ((by fun_prop : Continuous fun τ : ℝ => cexp (-(a * τ))).mul hh).aestronglyMeasurable
    ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun τ (hτ : 0 < τ) => ?_))
  rw [norm_mul, Complex.norm_exp, show (-(a * τ)).re = -(a.re * τ) by simp]
  calc Real.exp (-(a.re * τ)) * ‖h τ‖ ≤ Real.exp (-(a.re * τ)) * (C * τ ^ k) := by
        gcongr; exact hb τ hτ
    _ = _ := by ring

theorem geom_inv_sq_add_one {u : ℂ} (hu : u ^ 2 + 1 ≠ 0) (n : ℕ) :
    1 / (u ^ 2 + 1) = ∑ m ∈ Finset.range n, (-1) ^ m * u ^ (2 * m) +
      (-1) ^ n * (u ^ (2 * n) / (u ^ 2 + 1)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [ih, Finset.sum_range_succ, add_assoc]
    congr 1
    field_simp
    rw [show 2 * (n + 1) = 2 * n + 2 by ring, pow_add, pow_succ (-1 : ℂ)]
    ring

/-- The remainders along the ray `t = ωτ`, given `|(ωτ)² + 1| ≥ L > 0`: for `k ∈ {0, 1}`,
`∫ e^{−zωτ} ω (ωτ)^k/((ωτ)² + 1) = ∑_{m<n} (−1)^m (2m+k)!/z^{2m+k+1}
  + (−1)^n ∫ e^{−zωτ} ω (ωτ)^{2n+k}/((ωτ)² + 1)`. -/
theorem laplace_ray_expansion {z ω : ℂ} (hz0 : z ≠ 0) (hω : 0 < ω.re) (hω1 : ‖ω‖ = 1)
    (ha : 0 < (z * ω).re) {L : ℝ} (hL0 : 0 < L) (hL : ∀ τ : ℝ, L ≤ ‖(ω * τ) ^ 2 + 1‖)
    (k n : ℕ) :
    ∫ τ in Ioi (0 : ℝ), cexp (-(z * ω * τ)) * (ω * (ω * τ) ^ k / ((ω * τ) ^ 2 + 1)) =
      ∑ m ∈ Finset.range n, (-1) ^ m * ((2 * m + k) ! : ℂ) / z ^ (2 * m + k + 1) +
        (-1) ^ n * ∫ τ in Ioi (0 : ℝ),
          cexp (-(z * ω * τ)) * (ω * (ω * τ) ^ (2 * n + k) / ((ω * τ) ^ 2 + 1)) := by
  have hne := ray_sq_add_one_ne hω
  have hω0 : ω ≠ 0 := fun h => by simp [h] at hω
  -- integrability of the pieces
  have hpow : ∀ j : ℕ, IntegrableOn
      (fun τ : ℝ => cexp (-(z * ω * τ)) * (ω * (ω * τ) ^ j)) (Ioi 0) := fun j =>
    integrableOn_cexp_mul_of_le ha (C := 1) (by fun_prop) j fun τ hτ => by
      rw [norm_mul, norm_pow, norm_mul, hω1, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hτ, one_mul, one_mul, one_mul]
  have hrem : ∀ j : ℕ, IntegrableOn
      (fun τ : ℝ => cexp (-(z * ω * τ)) * (ω * (ω * τ) ^ j / ((ω * τ) ^ 2 + 1))) (Ioi 0) :=
    fun j => integrableOn_cexp_mul_of_le ha (C := L⁻¹)
      ((by fun_prop : Continuous fun τ : ℝ => ω * (ω * τ) ^ j).div (by fun_prop) hne) j
      fun τ hτ => by
        rw [norm_div, norm_mul, norm_pow, norm_mul, hω1, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos hτ, one_mul, one_mul, div_eq_mul_inv, mul_comm]
        gcongr
        exact hL τ
  -- the power moments
  have hmom : ∀ j : ℕ, ∫ τ in Ioi (0 : ℝ), cexp (-(z * ω * τ)) * (ω * (ω * τ) ^ j) =
      (j ! : ℂ) / z ^ (j + 1) := fun j => by
    have h := integral_cexp_mul_pow ha j
    have e : ∀ τ : ℝ, cexp (-(z * ω * τ)) * (ω * (ω * τ) ^ j) =
        ω ^ (j + 1) * (cexp (-(z * ω * τ)) * (τ : ℂ) ^ j) := fun τ => by ring
    simp only [e]
    rw [integral_const_mul, h, mul_pow]
    field_simp
  -- the algebraic identity, integrated
  have hpt : ∀ τ : ℝ, cexp (-(z * ω * τ)) * (ω * (ω * τ) ^ k / ((ω * τ) ^ 2 + 1)) =
      ∑ m ∈ Finset.range n, (-1) ^ m * (cexp (-(z * ω * τ)) * (ω * (ω * τ) ^ (2 * m + k))) +
        (-1) ^ n * (cexp (-(z * ω * τ)) * (ω * (ω * τ) ^ (2 * n + k) / ((ω * τ) ^ 2 + 1))) :=
    fun τ => by
      have g := geom_inv_sq_add_one (hne τ) n
      have e1 : ω * (ω * τ) ^ k / ((ω * τ) ^ 2 + 1) =
          ω * (ω * τ) ^ k * (1 / ((ω * τ) ^ 2 + 1)) := by ring
      rw [e1, g, mul_add, Finset.mul_sum, mul_add, Finset.mul_sum]
      congr 1
      · refine Finset.sum_congr rfl fun m _ => ?_
        rw [pow_add]; ring
      · rw [pow_add]; ring
  simp only [hpt]
  rw [integral_add (integrable_finsetSum _ fun m _ => (hpow _).const_mul _)
      ((hrem _).const_mul _), integral_finsetSum _ fun m _ => (hpow _).const_mul _,
    integral_const_mul]
  congr 1
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [integral_const_mul, hmom]
  ring

/-- `|∫ e^{−zωτ} ω (ωτ)^j/((ωτ)² + 1)| ≤ j!/(L ℜ(zω)^{j+1})`. -/
theorem norm_laplace_ray_rem_le {z ω : ℂ} (hω1 : ‖ω‖ = 1)
    (ha : 0 < (z * ω).re) {L : ℝ} (hL0 : 0 < L) (hL : ∀ τ : ℝ, L ≤ ‖(ω * τ) ^ 2 + 1‖) (j : ℕ) :
    ‖∫ τ in Ioi (0 : ℝ), cexp (-(z * ω * τ)) * (ω * (ω * τ) ^ j / ((ω * τ) ^ 2 + 1))‖ ≤
      j ! / (L * (z * ω).re ^ (j + 1)) := by
  set c := (z * ω).re
  have hint := (integrableOn_pow_mul_exp_neg_mul j ha).const_mul L⁻¹
  have hval : ∫ τ in Ioi (0 : ℝ), L⁻¹ * (τ ^ j * Real.exp (-(c * τ))) =
      j ! / (L * c ^ (j + 1)) := by
    rw [integral_const_mul]
    have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := (j : ℝ) + 1) (r := c) (by positivity)
      ha
    rw [show (j : ℝ) + 1 - 1 = (j : ℕ) by ring,
      show (j : ℝ) + 1 = ((j + 1 : ℕ) : ℝ) by push_cast; ring,
      Real.rpow_natCast, show Real.Gamma ((j + 1 : ℕ) : ℝ) = ((j ! : ℕ) : ℝ) by
        rw [Nat.cast_succ, Real.Gamma_nat_eq_factorial]] at h
    simp only [Real.rpow_natCast] at h
    rw [h, one_div_pow]
    field_simp
  rw [← hval]
  refine norm_integral_le_of_norm_le hint ((ae_restrict_iff' measurableSet_Ioi).2
    (Eventually.of_forall fun τ (hτ : 0 < τ) => ?_))
  rw [norm_mul, Complex.norm_exp, show (-(z * ω * τ)).re = -(c * τ) by simp [c, mul_re],
    norm_div, norm_mul, norm_pow, norm_mul, hω1, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hτ, one_mul, one_mul]
  have hLt := hL τ
  have hpos : 0 < ‖(ω * τ) ^ 2 + 1‖ := lt_of_lt_of_le hL0 hLt
  rw [div_eq_mul_inv]
  calc Real.exp (-(c * τ)) * (τ ^ j * ‖(ω * τ) ^ 2 + 1‖⁻¹) ≤
      Real.exp (-(c * τ)) * (τ ^ j * L⁻¹) := by gcongr
    _ = _ := by ring

theorem integrableOn_laplace_ray_rem {z ω : ℂ} (hω : 0 < ω.re) (hω1 : ‖ω‖ = 1)
    (ha : 0 < (z * ω).re) {L : ℝ} (hL0 : 0 < L) (hL : ∀ τ : ℝ, L ≤ ‖(ω * τ) ^ 2 + 1‖)
    (j : ℕ) : IntegrableOn
      (fun τ : ℝ => cexp (-(z * ω * τ)) * (ω * (ω * τ) ^ j / ((ω * τ) ^ 2 + 1))) (Ioi 0) :=
  integrableOn_cexp_mul_of_le ha (C := L⁻¹)
    ((by fun_prop : Continuous fun τ : ℝ => ω * (ω * τ) ^ j).div (by fun_prop)
      (ray_sq_add_one_ne hω)) j fun τ hτ => by
    rw [norm_div, norm_mul, norm_pow, norm_mul, hω1, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hτ, one_mul, one_mul, div_eq_mul_inv, mul_comm]
    gcongr
    exact hL τ

/-- `f` and `g` as Lebesgue integrals along the ray `t = ωτ`. -/
theorem auxF_auxG_ray {z ω : ℂ} (hz : 0 < z.re) (hω : 0 < ω.re) (hω1 : ‖ω‖ = 1)
    (ha : 0 < (z * ω).re) {L : ℝ} (hL0 : 0 < L) (hL : ∀ τ : ℝ, L ≤ ‖(ω * τ) ^ 2 + 1‖) :
    auxF z = ∫ τ in Ioi (0 : ℝ), cexp (-(z * ω * τ)) * (ω * (ω * τ) ^ 0 / ((ω * τ) ^ 2 + 1)) ∧
      auxG z = ∫ τ in Ioi (0 : ℝ),
        cexp (-(z * ω * τ)) * (ω * (ω * τ) ^ 1 / ((ω * τ) ^ 2 + 1)) := by
  obtain ⟨hf, hg⟩ := tendsto_laplace_f_g_ray hz hω ha
  constructor
  · refine (integral_Ioi_eq_of_tendsto (integrableOn_laplace_ray_rem hω hω1 ha hL0 hL 0)
      (hf.congr fun R => intervalIntegral.integral_congr fun τ _ => ?_)).symm
    simp only [pow_zero, mul_one]
    ring
  · refine (integral_Ioi_eq_of_tendsto (integrableOn_laplace_ray_rem hω hω1 ha hL0 hL 1)
      (hg.congr fun R => intervalIntegral.integral_congr fun τ _ => ?_)).symm
    simp only [pow_one]
    ring

/-- The remainder of 6.12.5 along the ray `t = ωτ`. -/
theorem auxF_sub_fAsymp_ray {z ω : ℂ} (hz : 0 < z.re) (hω : 0 < ω.re) (hω1 : ‖ω‖ = 1)
    (ha : 0 < (z * ω).re) {L : ℝ} (hL0 : 0 < L) (hL : ∀ τ : ℝ, L ≤ ‖(ω * τ) ^ 2 + 1‖) (n : ℕ) :
    auxF z - fAsymp n z = (-1) ^ n * ∫ τ in Ioi (0 : ℝ),
      cexp (-(z * ω * τ)) * (ω * (ω * τ) ^ (2 * n) / ((ω * τ) ^ 2 + 1)) := by
  have hz0 : z ≠ 0 := fun h => by simp [h] at hz
  rw [(auxF_auxG_ray hz hω hω1 ha hL0 hL).1, laplace_ray_expansion hz0 hω hω1 ha hL0 hL 0 n,
    fAsymp_eq]
  simp only [add_zero]
  ring

/-- The remainder of 6.12.6 along the ray `t = ωτ`. -/
theorem auxG_sub_gAsymp_ray {z ω : ℂ} (hz : 0 < z.re) (hω : 0 < ω.re) (hω1 : ‖ω‖ = 1)
    (ha : 0 < (z * ω).re) {L : ℝ} (hL0 : 0 < L) (hL : ∀ τ : ℝ, L ≤ ‖(ω * τ) ^ 2 + 1‖) (n : ℕ) :
    auxG z - gAsymp n z = (-1) ^ n * ∫ τ in Ioi (0 : ℝ),
      cexp (-(z * ω * τ)) * (ω * (ω * τ) ^ (2 * n + 1) / ((ω * τ) ^ 2 + 1)) := by
  have hz0 : z ≠ 0 := fun h => by simp [h] at hz
  rw [(auxF_auxG_ray hz hω hω1 ha hL0 hL).2, laplace_ray_expansion hz0 hω hω1 ha hL0 hL 1 n,
    gAsymp_eq]
  simp only [show ∀ m : ℕ, 2 * m + 1 + 1 = 2 * m + 2 from fun m => rfl]
  ring

theorem one_le_norm_sq_add_one (τ : ℝ) : 1 ≤ ‖((1 : ℂ) * τ) ^ 2 + 1‖ := by
  rw [one_mul, ← ofReal_pow, ← ofReal_one, ← ofReal_add, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (by positivity)]
  nlinarith [sq_nonneg τ]

/-- **DLMF 6.12.5, 6.12.7**: `f(z) = (1/z) ∑_{m<n} (−1)^m (2m)!/z^{2m} + R_n^{(f)}(z)` with
`R_n^{(f)}(z) = (−1)^n ∫_0^∞ e^{−zt} t^{2n}/(t² + 1) dt`, `ℜz > 0`. -/
theorem dlmf_6_12_7 {z : ℂ} (hz : 0 < z.re) (n : ℕ) :
    auxF z - fAsymp n z =
      (-1) ^ n * ∫ t in Ioi (0 : ℝ), cexp (-(z * t)) * (t : ℂ) ^ (2 * n) / ((t : ℂ) ^ 2 + 1) := by
  rw [auxF_sub_fAsymp_ray hz (ω := 1) (by simp) (by simp) (by simpa using hz) one_pos
    one_le_norm_sq_add_one n]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  simp only [one_mul, mul_one]
  ring

/-- **DLMF 6.12.6, 6.12.8**: `g(z) = (1/z²) ∑_{m<n} (−1)^m (2m+1)!/z^{2m} + R_n^{(g)}(z)` with
`R_n^{(g)}(z) = (−1)^n ∫_0^∞ e^{−zt} t^{2n+1}/(t² + 1) dt`, `ℜz > 0`. -/
theorem dlmf_6_12_8 {z : ℂ} (hz : 0 < z.re) (n : ℕ) :
    auxG z - gAsymp n z =
      (-1) ^ n * ∫ t in Ioi (0 : ℝ),
        cexp (-(z * t)) * (t : ℂ) ^ (2 * n + 1) / ((t : ℂ) ^ 2 + 1) := by
  rw [auxG_sub_gAsymp_ray hz (ω := 1) (by simp) (by simp) (by simpa using hz) one_pos
    one_le_norm_sq_add_one n]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  simp only [one_mul, mul_one]
  ring

/-! ### The remainder bounds -/

/-- The first neglected term of 6.12.3 has modulus `(2n)!/|z|^{2n+1}`. -/
theorem norm_fAsymp_succ_sub (n : ℕ) (z : ℂ) :
    ‖fAsymp (n + 1) z - fAsymp n z‖ = (2 * n) ! / ‖z‖ ^ (2 * n + 1) := by
  rw [fAsymp_eq, fAsymp_eq, Finset.sum_range_succ, add_sub_cancel_left, norm_div, norm_mul,
    norm_pow, norm_neg, norm_one, one_pow, one_mul, Complex.norm_natCast, norm_pow]

/-- The first neglected term of 6.12.4 has modulus `(2n+1)!/|z|^{2n+2}`. -/
theorem norm_gAsymp_succ_sub (n : ℕ) (z : ℂ) :
    ‖gAsymp (n + 1) z - gAsymp n z‖ = (2 * n + 1) ! / ‖z‖ ^ (2 * n + 2) := by
  rw [gAsymp_eq, gAsymp_eq, Finset.sum_range_succ, add_sub_cancel_left, norm_div, norm_mul,
    norm_pow, norm_neg, norm_one, one_pow, one_mul, Complex.norm_natCast, norm_pow]

/-- The direction `ω = z̄/|z|`, which turns `zt` into `|z|τ`. -/
noncomputable def rayDir (z : ℂ) : ℂ := ((‖z‖⁻¹ : ℝ) : ℂ) * (starRingEnd ℂ) z

theorem rayDir_props {z : ℂ} (hz : 0 < z.re) :
    0 < (rayDir z).re ∧ ‖rayDir z‖ = 1 ∧ z * rayDir z = (‖z‖ : ℂ) ∧
      ((rayDir z) ^ 2).re = Real.cos (2 * arg z) ∧
      ((rayDir z) ^ 2).im = -Real.sin (2 * arg z) := by
  have hz0 : z ≠ 0 := fun h => by simp [h] at hz
  have hn : 0 < ‖z‖ := norm_pos_iff.2 hz0
  have hc := Complex.cos_arg hz0
  have hs := Complex.sin_arg z
  have hsq : z.re ^ 2 + z.im ^ 2 = ‖z‖ ^ 2 := by
    rw [Complex.sq_norm, normSq_apply]; ring
  refine ⟨by simp [rayDir]; positivity, ?_, ?_, ?_, ?_⟩
  · rw [rayDir, norm_mul, Complex.norm_real, Complex.norm_conj, Real.norm_eq_abs,
      abs_of_pos (inv_pos.2 hn), inv_mul_cancel₀ hn.ne']
  · rw [rayDir, mul_left_comm, mul_conj, normSq_eq_norm_sq]
    push_cast
    field_simp
  · rw [Real.cos_two_mul, hc]
    simp only [rayDir, sq, mul_re, mul_im, ofReal_re, ofReal_im, conj_re, conj_im]
    field_simp
    nlinarith [hsq]
  · rw [Real.sin_two_mul, hc, hs]
    simp only [rayDir, sq, mul_re, mul_im, ofReal_re, ofReal_im, conj_re, conj_im]
    field_simp
    ring

/-- `|1 + τ²ω²| ≥ |ℑω²|`, and `≥ 1` when `ℜω² ≥ 0` (`|ω| = 1`). -/
theorem norm_ray_sq_add_one_ge {ω : ℂ} (hω1 : ‖ω‖ = 1) (τ : ℝ) :
    |(ω ^ 2).im| ≤ ‖(ω * τ) ^ 2 + 1‖ ∧ (0 ≤ (ω ^ 2).re → 1 ≤ ‖(ω * τ) ^ 2 + 1‖) := by
  set v := ω ^ 2 with hv
  have hv1 : v.re ^ 2 + v.im ^ 2 = 1 := by
    have : ‖v‖ ^ 2 = 1 := by rw [hv, norm_pow, hω1, one_pow, one_pow]
    rw [Complex.sq_norm, normSq_apply] at this
    nlinarith [this]
  have e : (ω * τ) ^ 2 + 1 = 1 + ((τ ^ 2 : ℝ) : ℂ) * v := by rw [hv]; push_cast; ring
  have hre : ((ω * τ) ^ 2 + 1).re = 1 + τ ^ 2 * v.re := by
    rw [e, add_re, one_re, re_ofReal_mul]
  have him : ((ω * τ) ^ 2 + 1).im = τ ^ 2 * v.im := by
    rw [e, add_im, one_im, im_ofReal_mul, zero_add]
  constructor
  · rw [← pow_le_pow_iff_left₀ (abs_nonneg _) (norm_nonneg _) two_ne_zero, sq_abs,
      Complex.sq_norm, normSq_apply, hre, him]
    nlinarith [sq_nonneg (τ ^ 2 + v.re), sq_nonneg τ]
  · intro h
    refine le_trans ?_ (re_le_norm _)
    rw [hre]
    nlinarith [sq_nonneg τ]

/-- **DLMF §6.12(ii)**: for `|ph z| ≤ π/4` the remainders of 6.12.3 and 6.12.4 are bounded in
magnitude by the first neglected terms. -/
theorem dlmf_6_12_remainder_right {z : ℂ} (hz0 : z ≠ 0) (harg : |arg z| ≤ π / 4) (n : ℕ) :
    ‖auxF z - fAsymp n z‖ ≤ ‖fAsymp (n + 1) z - fAsymp n z‖ ∧
      ‖auxG z - gAsymp n z‖ ≤ ‖gAsymp (n + 1) z - gAsymp n z‖ := by
  have hπ := Real.pi_pos
  have hz : 0 < z.re := by
    have := abs_arg_lt_pi_div_two_iff.1 (lt_of_le_of_lt harg (by linarith))
    exact this.resolve_right hz0
  obtain ⟨hω, hω1, hzω, hre, -⟩ := rayDir_props hz
  have hcos : 0 ≤ Real.cos (2 * arg z) := Real.cos_nonneg_of_mem_Icc
    ⟨by rw [abs_le] at harg; linarith, by rw [abs_le] at harg; linarith⟩
  have hL : ∀ τ : ℝ, 1 ≤ ‖(rayDir z * τ) ^ 2 + 1‖ := fun τ =>
    (norm_ray_sq_add_one_ge hω1 τ).2 (by rw [hre]; exact hcos)
  have ha : 0 < (z * rayDir z).re := by rw [hzω, ofReal_re]; exact norm_pos_iff.2 hz0
  have hc : (z * rayDir z).re = ‖z‖ := by rw [hzω, ofReal_re]
  constructor
  · rw [auxF_sub_fAsymp_ray hz hω hω1 ha one_pos hL n, norm_mul, norm_pow, norm_neg, norm_one,
      one_pow, one_mul, norm_fAsymp_succ_sub]
    refine (norm_laplace_ray_rem_le hω1 ha one_pos hL _).trans (le_of_eq ?_)
    rw [hc, one_mul]
  · rw [auxG_sub_gAsymp_ray hz hω hω1 ha one_pos hL n, norm_mul, norm_pow, norm_neg, norm_one,
      one_pow, one_mul, norm_gAsymp_succ_sub]
    refine (norm_laplace_ray_rem_le hω1 ha one_pos hL _).trans (le_of_eq ?_)
    rw [hc, one_mul]

theorem sin_two_mul_abs_eq {θ : ℝ} (h : |θ| ≤ π / 2) :
    Real.sin (2 * |θ|) = |Real.sin (2 * θ)| := by
  rcases abs_cases θ with ⟨e, h0⟩ | ⟨e, h0⟩
  · rw [e, abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith)
      (by rw [abs_le] at h; linarith))]
  · rw [e, show 2 * -θ = -(2 * θ) by ring, Real.sin_neg, abs_of_nonpos]
    have : 0 ≤ Real.sin (2 * -θ) :=
      Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by rw [abs_le] at h; linarith)
    rw [show 2 * -θ = -(2 * θ) by ring, Real.sin_neg] at this
    linarith

/-- **DLMF §6.12(ii)**: for `π/4 ≤ |ph z| < π/2` the remainders of 6.12.3 and 6.12.4 are bounded
in magnitude by `csc(2|ph z|)` times the first neglected terms. -/
theorem dlmf_6_12_remainder_left {z : ℂ} (hz0 : z ≠ 0) (h1 : π / 4 ≤ |arg z|)
    (h2 : |arg z| < π / 2) (n : ℕ) :
    ‖auxF z - fAsymp n z‖ ≤ (Real.sin (2 * |arg z|))⁻¹ * ‖fAsymp (n + 1) z - fAsymp n z‖ ∧
      ‖auxG z - gAsymp n z‖ ≤ (Real.sin (2 * |arg z|))⁻¹ * ‖gAsymp (n + 1) z - gAsymp n z‖ := by
  have hπ := Real.pi_pos
  have hz : 0 < z.re := (abs_arg_lt_pi_div_two_iff.1 h2).resolve_right hz0
  obtain ⟨hω, hω1, hzω, -, him⟩ := rayDir_props hz
  set L := Real.sin (2 * |arg z|)
  have hL0 : 0 < L := Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have hL : ∀ τ : ℝ, L ≤ ‖(rayDir z * τ) ^ 2 + 1‖ := fun τ => by
    refine le_trans (le_of_eq ?_) (norm_ray_sq_add_one_ge hω1 τ).1
    rw [him, abs_neg, ← sin_two_mul_abs_eq h2.le]
  have ha : 0 < (z * rayDir z).re := by rw [hzω, ofReal_re]; exact norm_pos_iff.2 hz0
  have hc : (z * rayDir z).re = ‖z‖ := by rw [hzω, ofReal_re]
  constructor
  · rw [auxF_sub_fAsymp_ray hz hω hω1 ha hL0 hL n, norm_mul, norm_pow, norm_neg, norm_one,
      one_pow, one_mul, norm_fAsymp_succ_sub]
    refine (norm_laplace_ray_rem_le hω1 ha hL0 hL _).trans (le_of_eq ?_)
    rw [hc]
    field_simp
  · rw [auxG_sub_gAsymp_ray hz hω hω1 ha hL0 hL n, norm_mul, norm_pow, norm_neg, norm_one,
      one_pow, one_mul, norm_gAsymp_succ_sub]
    refine (norm_laplace_ray_rem_le hω1 ha hL0 hL _).trans (le_of_eq ?_)
    rw [hc]
    field_simp

/-- A real Laplace integral `∫_0^∞ e^{−xt} t^k/(t² + 1) dt` (`x > 0`) is a positive real. -/
theorem laplace_rem_real_pos {x : ℝ} (hx : 0 < x) (k : ℕ) :
    ∃ J : ℝ, 0 < J ∧ ∫ t in Ioi (0 : ℝ), cexp (-((x : ℂ) * t)) * (t : ℂ) ^ k / ((t : ℂ) ^ 2 + 1) =
      (J : ℂ) := by
  set f : ℝ → ℝ := fun t => Real.exp (-(x * t)) * t ^ k / (t ^ 2 + 1) with hf
  have hfint : IntegrableOn f (Ioi 0) := by
    refine (integrableOn_pow_mul_exp_neg_mul k hx).mono'
      ((by fun_prop : Measurable f).aestronglyMeasurable)
      ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun t (ht : 0 < t) => ?_))
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), hf]
    simp only
    rw [div_le_iff₀ (by positivity)]
    nlinarith [mul_pos (Real.exp_pos (-(x * t))) (pow_pos ht k), sq_nonneg t]
  refine ⟨∫ t in Ioi (0 : ℝ), f t, ?_, ?_⟩
  · rw [setIntegral_pos_iff_support_of_nonneg_ae
      ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun t (ht : 0 < t) =>
        by positivity)) hfint]
    have : Ioi (0 : ℝ) ⊆ Function.support f ∩ Ioi 0 := fun t (ht : 0 < t) =>
      ⟨(by positivity : 0 < f t).ne', ht⟩
    exact lt_of_lt_of_le (by simp) (measure_mono this)
  · rw [← integral_complex_ofReal]
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    simp only [hf]
    push_cast
    ring_nf

/-- **DLMF §6.12(ii)**: for `ph z = 0` the remainders of 6.12.3 and 6.12.4 are real, bounded in
magnitude by the first neglected terms, and of the same signs `(−1)ⁿ`. -/
theorem dlmf_6_12_remainder_real {x : ℝ} (hx : 0 < x) (n : ℕ) :
    (∃ r : ℝ, auxF x - fAsymp n x = r ∧ 0 < (-1) ^ n * r ∧
        |r| ≤ ‖fAsymp (n + 1) x - fAsymp n x‖) ∧
      (∃ r : ℝ, auxG x - gAsymp n x = r ∧ 0 < (-1) ^ n * r ∧
        |r| ≤ ‖gAsymp (n + 1) x - gAsymp n x‖) := by
  have hx0 : (x : ℂ) ≠ 0 := ofReal_ne_zero.2 hx.ne'
  have harg : |arg (x : ℂ)| ≤ π / 4 := by
    rw [arg_ofReal_of_nonneg hx.le, abs_zero]; positivity
  have hb := dlmf_6_12_remainder_right hx0 harg n
  have hsq : ((-1 : ℝ) ^ n) * (-1) ^ n = 1 := by rw [← mul_pow]; norm_num
  have hre : 0 < (x : ℂ).re := by simpa using hx
  constructor
  · obtain ⟨J, hJ, hJe⟩ := laplace_rem_real_pos hx (2 * n)
    have e := dlmf_6_12_7 hre n
    rw [hJe] at e
    refine ⟨(-1) ^ n * J, by rw [e]; push_cast; ring, by rw [← mul_assoc, hsq, one_mul]; exact hJ,
      ?_⟩
    have := hb.1
    rw [e, show ((-1 : ℂ)) ^ n * (J : ℂ) = (((-1 : ℝ) ^ n * J : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs] at this
    exact this
  · obtain ⟨J, hJ, hJe⟩ := laplace_rem_real_pos hx (2 * n + 1)
    have e := dlmf_6_12_8 hre n
    rw [hJe] at e
    refine ⟨(-1) ^ n * J, by rw [e]; push_cast; ring, by rw [← mul_assoc, hsq, one_mul]; exact hJ,
      ?_⟩
    have := hb.2
    rw [e, show ((-1 : ℂ)) ^ n * (J : ℂ) = (((-1 : ℝ) ^ n * J : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs] at this
    exact this

end Azurite.DLMF
