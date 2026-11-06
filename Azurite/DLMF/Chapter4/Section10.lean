/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter1.Section4
import Azurite.DLMF.Chapter1.Section8
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.NumberTheory.ZetaValues

/-!
# DLMF §4.10: Integrals

Formalizations of <https://dlmf.nist.gov/4.10>. An indefinite integral `∫ f dz = F` is stated as
`F′ = f` (`HasDerivAt`) on the region where the principal branches involved are holomorphic.

* §4.10(i): 4.10.1–4.10.4 (`dlmf_4_10_1` … `dlmf_4_10_4`; 4.10.4 on `ℂ ∖ (−∞, 1]`);
  4.10.5 and 4.10.6 by term-by-term integration of the geometric series
  (`integral_pow_mul_log`: `∫₀¹ tⁿ ln t dt = −1/(n+1)²`, ζ(2) and its alternating version
  `hasSum_alt_inv_sq`); 4.10.7 (`li`: the principal value `⨍₀ˣ dt/ln t` exists for `x > 1`).
* §4.10(ii): 4.10.8–4.10.10 (antiderivatives), 4.10.11 (Gaussian, from Mathlib),
  4.10.12 (via `u = eˣ − 1` and the series of `ln(1+u)/u`), 4.10.13 (improper FTC).
* §4.10(iii) (compendia) is a reference only.
-/

open Complex Set Filter Topology MeasureTheory intervalIntegral
open scoped Real

namespace Azurite.DLMF

/-! ### §4.10(i) Logarithms: indefinite integrals -/

/-- **DLMF 4.10.1**: `∫ dz/z = ln z`: `(ln z)′ = 1/z` off the cut. -/
theorem dlmf_4_10_1 {z : ℂ} (hz : z ∈ slitPlane) : HasDerivAt log (1 / z) z := by
  simpa [one_div] using hasDerivAt_log hz

/-- **DLMF 4.10.2**: `∫ ln z dz = z ln z − z`. -/
theorem dlmf_4_10_2 {z : ℂ} (hz : z ∈ slitPlane) :
    HasDerivAt (fun z => z * log z - z) (log z) z := by
  have h : HasDerivAt (fun z => z * log z - z) (1 * log z + z * z⁻¹ - 1) z :=
    ((hasDerivAt_id' z).mul (hasDerivAt_log hz)).sub (hasDerivAt_id' z)
  exact h.congr_deriv (by rw [mul_inv_cancel₀ (slitPlane_ne_zero hz)]; ring)

/-- **DLMF 4.10.3**: `∫ zⁿ ln z dz = z^{n+1}/(n+1) ln z − z^{n+1}/(n+1)²`, `n ≠ −1`. -/
theorem dlmf_4_10_3 {z : ℂ} (hz : z ∈ slitPlane) {n : ℤ} (hn : n ≠ -1) :
    HasDerivAt (fun z => z ^ (n + 1) / (n + 1) * log z - z ^ (n + 1) / (n + 1) ^ 2)
      (z ^ n * log z) z := by
  have hz0 := slitPlane_ne_zero hz
  have hn1 : (n : ℂ) + 1 ≠ 0 := by
    intro h; apply hn; exact_mod_cast (by linear_combination h : (n : ℂ) = -1)
  have hp := hasDerivAt_zpow (n + 1) z (Or.inl hz0)
  have h := ((hp.div_const ((n : ℂ) + 1)).mul (hasDerivAt_log hz)).sub
    (hp.div_const (((n : ℂ) + 1) ^ 2))
  convert h using 1
  have hzn : z ^ (n + 1 - 1) = z ^ n := by rw [add_sub_cancel_right]
  have hzn1 : z ^ (n + 1) = z ^ n * z := by rw [zpow_add_one₀ hz0]
  rw [hzn, hzn1]
  push_cast
  field_simp
  ring

/-- **DLMF 4.10.4**: `∫ dz/(z ln z) = ln(ln z)`, valid off `(−∞, 1]` (where `ln z` is off the
cut). -/
theorem dlmf_4_10_4 {z : ℂ} (hz : ∀ x : ℝ, x ≤ 1 → z ≠ x) :
    HasDerivAt (fun z => log (log z)) (1 / (z * log z)) z := by
  have hz1 : z ∈ slitPlane := by
    rw [mem_slitPlane_iff]
    by_contra h
    push Not at h
    exact hz z.re (by linarith [h.1]) (Complex.ext rfl (by simpa using h.2))
  have hz2 : log z ∈ slitPlane := by
    rw [mem_slitPlane_iff]
    by_contra h
    push Not at h
    -- `log z` real and `≤ 0` forces `z = e^{log z} ∈ (0, 1]`
    have hre : (log z).re ≤ 0 := h.1
    have him : (log z).im = 0 := h.2
    have hz' : z = (Real.exp (log z).re : ℝ) := by
      conv_lhs => rw [← exp_log (slitPlane_ne_zero hz1)]
      rw [← re_add_im (log z), him]; push_cast; simp
    exact hz _ (by rw [Real.exp_le_one_iff]; exact hre) hz'
  have h := (hasDerivAt_log hz1).clog hz2
  convert h using 1
  field_simp

/-! ### §4.10(ii) Exponentials: indefinite integrals -/

/-- **DLMF 4.10.8**: `∫ e^{az} dz = e^{az}/a`, `a ≠ 0`. -/
theorem dlmf_4_10_8 {a : ℂ} (ha : a ≠ 0) (z : ℂ) :
    HasDerivAt (fun z => exp (a * z) / a) (exp (a * z)) z := by
  have h : HasDerivAt (fun z => exp (a * z) / a) (exp (a * z) * (a * 1) / a) z :=
    (((hasDerivAt_id' z).const_mul a).cexp).div_const a
  exact h.congr_deriv (by field_simp)

/-- **DLMF 4.10.9**: `∫ dz/(e^{az} + b) = (az − ln(e^{az} + b))/(ab)`, `a, b ≠ 0`, where
`e^{az} + b` is off the cut. -/
theorem dlmf_4_10_9 {a b z : ℂ} (ha : a ≠ 0) (hb : b ≠ 0) (hz : exp (a * z) + b ∈ slitPlane) :
    HasDerivAt (fun z => 1 / (a * b) * (a * z - log (exp (a * z) + b)))
      (1 / (exp (a * z) + b)) z := by
  have he : HasDerivAt (fun z => exp (a * z) + b) (exp (a * z) * (a * 1)) z :=
    (((hasDerivAt_id' z).const_mul a).cexp).add_const b
  have h : HasDerivAt (fun z => 1 / (a * b) * (a * z - log (exp (a * z) + b)))
      (1 / (a * b) * (a * 1 - exp (a * z) * (a * 1) / (exp (a * z) + b))) z :=
    (((hasDerivAt_id' z).const_mul a).sub (he.clog hz)).const_mul _
  have hD := slitPlane_ne_zero hz
  exact h.congr_deriv (by field_simp; ring)

/-- **DLMF 4.10.10**: `∫ (e^{az} − 1)/(e^{az} + 1) dz = (2/a) ln(e^{az/2} + e^{−az/2})`, `a ≠ 0`,
where `e^{az/2} + e^{−az/2}` is off the cut. -/
theorem dlmf_4_10_10 {a z : ℂ} (ha : a ≠ 0)
    (hz : exp (a * z / 2) + exp (-(a * z) / 2) ∈ slitPlane) :
    HasDerivAt (fun z => 2 / a * log (exp (a * z / 2) + exp (-(a * z) / 2)))
      ((exp (a * z) - 1) / (exp (a * z) + 1)) z := by
  have h1 : HasDerivAt (fun z => exp (a * z / 2)) (exp (a * z / 2) * (a * 1 / 2)) z :=
    (((hasDerivAt_id' z).const_mul a).div_const 2).cexp
  have h2 : HasDerivAt (fun z => exp (-(a * z) / 2)) (exp (-(a * z) / 2) * (-(a * 1) / 2)) z :=
    ((((hasDerivAt_id' z).const_mul a).neg).div_const 2).cexp
  have h : HasDerivAt (fun z => 2 / a * log (exp (a * z / 2) + exp (-(a * z) / 2)))
      (2 / a * ((exp (a * z / 2) * (a * 1 / 2) + exp (-(a * z) / 2) * (-(a * 1) / 2)) /
        (exp (a * z / 2) + exp (-(a * z) / 2)))) z :=
    ((h1.add h2).clog hz).const_mul _
  refine h.congr_deriv ?_
  have hD := slitPlane_ne_zero hz
  have he2 : exp (-(a * z) / 2) = (exp (a * z / 2))⁻¹ := by rw [← exp_neg]; ring_nf
  have hE : exp (a * z) = exp (a * z / 2) ^ 2 := by rw [← exp_nat_mul]; ring_nf
  have he1 := exp_ne_zero (a * z / 2)
  rw [he2] at hD ⊢
  rw [hE]
  generalize exp (a * z / 2) = e at hD he1 ⊢
  have hD' : e ^ 2 + 1 ≠ 0 := fun h0 => hD (by field_simp; linear_combination h0)
  field_simp
  ring

/-! ### Tools: bounded integrands and term-by-term integration on `[0, 1]` -/

theorem integral01_eq_Ioo (f : ℝ → ℝ) : ∫ t in (0 : ℝ)..1, f t = ∫ t in Ioo (0 : ℝ) 1, f t := by
  rw [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]

/-- Term-by-term integration on `[0, 1]` when `∑ ∫₀¹ |Fₙ| < ∞`. -/
theorem hasSum_integral01 {F : ℕ → ℝ → ℝ} {f : ℝ → ℝ}
    (hF : ∀ n, IntervalIntegrable (F n) volume 0 1)
    (hs : Summable fun n => ∫ t in (0 : ℝ)..1, |F n t|)
    (hpt : ∀ t ∈ Ioo (0 : ℝ) 1, HasSum (fun n => F n t) (f t)) :
    HasSum (fun n => ∫ t in (0 : ℝ)..1, F n t) (∫ t in (0 : ℝ)..1, f t) := by
  simp only [integral01_eq_Ioo] at hs ⊢
  have hint : ∀ n, Integrable (F n) (volume.restrict (Ioo (0 : ℝ) 1)) := fun n =>
    (hF n).1.mono_set Ioo_subset_Ioc_self
  have h := hasSum_integral_of_summable_integral_norm hint (by simpa [Real.norm_eq_abs] using hs)
  convert h using 1
  exact setIntegral_congr_fun measurableSet_Ioo fun t ht => (hpt t ht).tsum_eq.symm

/-- `∫₀¹ tⁿ ln t dt = −1/(n+1)²` (by 4.10.3). -/
theorem integral_pow_mul_log (n : ℕ) :
    ∫ t in (0 : ℝ)..1, t ^ n * Real.log t = -1 / ((n : ℝ) + 1) ^ 2 := by
  have hn : (n : ℝ) + 1 ≠ 0 := by positivity
  have hcont : ContinuousOn (fun t : ℝ => t ^ (n + 1) * Real.log t / (n + 1) -
      t ^ (n + 1) / ((n : ℝ) + 1) ^ 2) (Icc 0 1) := by
    have : Continuous fun t : ℝ => t ^ (n + 1) * Real.log t := by
      have h0 : Continuous fun t : ℝ => t ^ n * (t * Real.log t) :=
        (continuous_pow n).mul Real.continuous_mul_log
      exact h0.congr fun t => by ring
    exact ((this.div_const _).sub ((continuous_pow _).div_const _)).continuousOn
  have hderiv : ∀ t ∈ Ioo (0 : ℝ) 1, HasDerivAt (fun t : ℝ => t ^ (n + 1) * Real.log t / (n + 1) -
      t ^ (n + 1) / ((n : ℝ) + 1) ^ 2) (t ^ n * Real.log t) t := by
    intro t ht
    have h : HasDerivAt (fun t : ℝ => t ^ (n + 1) * Real.log t / (n + 1) -
        t ^ (n + 1) / ((n : ℝ) + 1) ^ 2)
        ((((n + 1 : ℕ) : ℝ) * t ^ (n + 1 - 1) * Real.log t + t ^ (n + 1) * t⁻¹) / (n + 1) -
          ((n + 1 : ℕ) : ℝ) * t ^ (n + 1 - 1) / ((n : ℝ) + 1) ^ 2) t :=
      (((hasDerivAt_pow (n + 1) t).mul (Real.hasDerivAt_log ht.1.ne')).div_const
        ((n : ℝ) + 1)).sub ((hasDerivAt_pow (n + 1) t).div_const (((n : ℝ) + 1) ^ 2))
    refine h.congr_deriv ?_
    have ht0 := ht.1.ne'
    simp only [Nat.add_sub_cancel]
    push_cast
    field_simp
    ring
  have hint : IntervalIntegrable (fun t : ℝ => t ^ n * Real.log t) volume 0 1 :=
    intervalIntegrable_log'.continuousOn_mul (continuous_pow n).continuousOn
  rw [integral_eq_sub_of_hasDerivAt_of_le zero_le_one hcont hderiv hint]
  simp
  field_simp

theorem hasSum_inv_sq_succ : HasSum (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 2) (π ^ 2 / 6) := by
  have h := (hasSum_nat_add_iff' 1).mpr hasSum_zeta_two
  simpa using h

/-- `∑ (−1)ⁿ/(n+1)² = π²/12`. -/
theorem hasSum_alt_inv_sq :
    HasSum (fun n : ℕ => (-1) ^ n / ((n : ℝ) + 1) ^ 2) (π ^ 2 / 12) := by
  set a : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1) ^ 2
  have ha : HasSum a (π ^ 2 / 6) := hasSum_inv_sq_succ
  -- the odd-indexed terms `1/(2k+2)²` sum to `π²/24`
  have hb : HasSum (fun k : ℕ => a (2 * k + 1)) (π ^ 2 / 24) := by
    have := ha.mul_left (1 / 4)
    convert this using 1
    · funext k; simp only [a]; push_cast; field_simp; ring
    · ring
  set g : ℕ → ℝ := fun n => if n % 2 = 1 then a n else 0
  have hg : HasSum g (π ^ 2 / 24) := by
    have hinj : Function.Injective (fun k : ℕ => 2 * k + 1) := fun i j h => by
      simp only at h; omega
    refine (hinj.hasSum_iff (fun n hn => ?_)).mp ?_
    · simp only [g]
      rw [ite_eq_right_iff]
      intro h1; exact absurd ⟨n / 2, by simp only; omega⟩ hn
    · convert hb using 1; funext k; simp [g, show (2 * k + 1) % 2 = 1 by omega]
  convert ha.sub (hg.mul_left 2) using 1
  · funext n
    simp only [g, a]
    rcases Nat.even_or_odd n with ⟨k, rfl⟩ | ⟨k, rfl⟩
    · rw [ite_eq_right_iff.mpr (fun h => absurd h (by omega)), show k + k = 2 * k by ring,
        pow_mul]
      norm_num
    · rw [ite_eq_left_iff.mpr (fun h => absurd (by omega) h), pow_succ, pow_mul]; norm_num; ring
  · ring

theorem integral_abs_pow_mul_log (n : ℕ) :
    ∫ t in (0 : ℝ)..1, |t ^ n * Real.log t| = 1 / ((n : ℝ) + 1) ^ 2 := by
  rw [intervalIntegral.integral_congr (g := fun t => -(t ^ n * Real.log t)) fun t ht => by
    rw [uIcc_of_le zero_le_one] at ht
    simp only
    rw [abs_of_nonpos (mul_nonpos_of_nonneg_of_nonpos (pow_nonneg ht.1 n)
      (Real.log_nonpos ht.1 ht.2))], intervalIntegral.integral_neg, integral_pow_mul_log]
  ring

/-! ### §4.10(i) Logarithms: definite integrals -/

/-- **DLMF 4.10.5**: `∫₀¹ ln t/(1 − t) dt = −π²/6`. -/
theorem dlmf_4_10_5 : ∫ t in (0 : ℝ)..1, Real.log t / (1 - t) = -(π ^ 2 / 6) := by
  have h := hasSum_integral01 (F := fun n t => t ^ n * Real.log t)
    (f := fun t => Real.log t / (1 - t))
    (fun n => intervalIntegrable_log'.continuousOn_mul (continuous_pow n).continuousOn)
    (by simp only [integral_abs_pow_mul_log]; exact hasSum_inv_sq_succ.summable)
    (fun t ht => by
      have := (hasSum_geometric_of_lt_one ht.1.le ht.2).mul_right (Real.log t)
      convert this using 1; field_simp)
  simp only [integral_pow_mul_log] at h
  refine h.unique ?_
  convert hasSum_inv_sq_succ.neg using 1
  funext n; ring

/-- **DLMF 4.10.6**: `∫₀¹ ln t/(1 + t) dt = −π²/12`. -/
theorem dlmf_4_10_6 : ∫ t in (0 : ℝ)..1, Real.log t / (1 + t) = -(π ^ 2 / 12) := by
  have h := hasSum_integral01 (F := fun n t => (-1) ^ n * (t ^ n * Real.log t))
    (f := fun t => Real.log t / (1 + t))
    (fun n => (intervalIntegrable_log'.continuousOn_mul
      (continuous_pow n).continuousOn).const_mul _)
    (by
      convert hasSum_inv_sq_succ.summable using 1
      funext n
      rw [← integral_abs_pow_mul_log n]
      congr 1; funext t
      rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul])
    (fun t ht => by
      have hn : ‖-t‖ < 1 := by rw [norm_neg, Real.norm_eq_abs, abs_of_pos ht.1]; exact ht.2
      have := (hasSum_geometric_of_norm_lt_one hn).mul_right (Real.log t)
      convert this using 1
      · funext n; rw [neg_pow]; ring
      · rw [sub_neg_eq_add]; field_simp)
  simp only [intervalIntegral.integral_const_mul, integral_pow_mul_log] at h
  refine h.unique ?_
  convert hasSum_alt_inv_sq.neg using 1
  funext n; ring

/-! ### 4.10.7: the logarithmic integral -/

/-- `1/ln t − 1/(t − 1)`, bounded on `(0, ∞)`. -/
noncomputable def liAux (t : ℝ) : ℝ := 1 / Real.log t - 1 / (t - 1)

theorem abs_liAux_le {t : ℝ} (ht : 0 < t) : |liAux t| ≤ 1 := by
  rcases eq_or_ne t 1 with rfl | ht1
  · simp [liAux]
  set L := Real.log t
  set d := t - 1
  have hd : d ≠ 0 := sub_ne_zero.mpr ht1
  have hL : L ≠ 0 := fun h => ht1 (Real.eq_one_of_pos_of_log_eq_zero ht h)
  have hLd : 0 < L * d := by
    rcases lt_or_gt_of_ne ht1 with h | h
    · exact mul_pos_of_neg_of_neg (Real.log_neg ht h) (by simp only [d]; linarith)
    · exact mul_pos (Real.log_pos h) (by simp only [d]; linarith)
  have h1 : L ≤ d := Real.log_le_sub_one_of_pos ht
  have h2 : d ≤ L * t := by
    have := Real.one_sub_inv_le_log_of_pos ht
    have h' : (1 - t⁻¹) * t = d := by simp only [d]; field_simp
    nlinarith
  have hg : liAux t = (d - L) / (L * d) := by
    have hL' : Real.log t ≠ 0 := hL
    have hd' : t - 1 ≠ 0 := hd
    simp only [liAux, L, d]; field_simp
  rw [hg, abs_of_nonneg (div_nonneg (by linarith) hLd.le), div_le_one hLd]
  have : L * t = L * d + L := by simp only [d]; ring
  linarith

theorem measurable_liAux : Measurable liAux :=
  (measurable_const.div Real.measurable_log).sub (measurable_const.div (measurable_id.sub_const 1))

/-- The logarithmic integral `li(x) = ⨍₀ˣ dt/ln t` (`x > 1`), in the closed form
`ln(x − 1) + ∫₀ˣ (1/ln t − 1/(t − 1)) dt` (see `dlmf_4_10_7`; §6.2(i)). -/
noncomputable def li (x : ℝ) : ℝ := Real.log (x - 1) + ∫ t in (0 : ℝ)..x, liAux t

/-- `∫₀^{1−ε} dt/(t − 1) + ∫_{1+ε}^x dt/(t − 1) = ln(x − 1)`. -/
theorem pv_inv_sub_one {x ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) (hεx : 1 + ε < x) :
    (∫ t in (0 : ℝ)..1 - ε, 1 / (t - 1)) + ∫ t in 1 + ε..x, 1 / (t - 1) = Real.log (x - 1) := by
  have e1 : (∫ t in (0 : ℝ)..1 - ε, 1 / (t - 1)) = ∫ u in (-1 : ℝ)..-ε, u⁻¹ := by
    rw [intervalIntegral.integral_comp_sub_right (fun u => 1 / u)]
    simp only [one_div]; congr 1 <;> ring
  have e2 : (∫ t in 1 + ε..x, 1 / (t - 1)) = ∫ u in ε..x - 1, u⁻¹ := by
    rw [intervalIntegral.integral_comp_sub_right (fun u => 1 / u)]
    simp only [one_div]; congr 1; ring
  rw [e1, e2, integral_inv (by rw [uIcc_of_le (by linarith)]; intro h; linarith [h.2]),
    integral_inv (by rw [uIcc_of_le (by linarith)]; intro h; linarith [h.1])]
  rw [neg_div_neg_eq, div_one, Real.log_div (by linarith) hε.ne']
  ring

/-- **DLMF 4.10.7**: for `x > 1` the principal value `⨍₀ˣ dt/ln t` exists and equals `li(x)`. -/
theorem dlmf_4_10_7 {x : ℝ} (hx : 1 < x) :
    HasPrincipalValue (fun t => 1 / Real.log t) 0 x 1 (li x) := by
  have hg : IntervalIntegrable liAux volume 0 x :=
    intervalIntegrable_of_abs_le (by linarith) measurable_liAux 1 fun t ht => abs_liAux_le ht.1
  have hpv := dlmf_1_4_24 (c := 1) ⟨one_pos, hx⟩ hg
  have hpv' := hpv.const_add (Real.log (x - 1))
  unfold HasPrincipalValue
  refine hpv'.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < min 1 (x - 1) by
    exact lt_min one_pos (by linarith))] with ε hε
  have hε1 : ε < 1 := hε.2.trans_le (min_le_left _ _)
  have hεx : 1 + ε < x := by linarith [hε.2.trans_le (min_le_right _ _)]
  have hc1 : IntervalIntegrable (fun t : ℝ => 1 / (t - 1)) volume 0 (1 - ε) :=
    ContinuousOn.intervalIntegrable (continuousOn_const.div
      (continuous_id.sub continuous_const).continuousOn
      fun t ht => by
        rw [uIcc_of_le (by linarith [hε.1])] at ht
        show t - 1 ≠ 0; exact sub_ne_zero.mpr (ne_of_lt (by linarith [ht.2, hε.1])))
  have hc2 : IntervalIntegrable (fun t : ℝ => 1 / (t - 1)) volume (1 + ε) x :=
    ContinuousOn.intervalIntegrable (continuousOn_const.div
      (continuous_id.sub continuous_const).continuousOn
      fun t ht => by
        rw [uIcc_of_le (by linarith [hε.1])] at ht
        show t - 1 ≠ 0; exact sub_ne_zero.mpr (ne_of_gt (by linarith [ht.1, hε.1])))
  have hg1 : IntervalIntegrable liAux volume 0 (1 - ε) :=
    hg.mono_set (by
      rw [uIcc_of_le (by linarith), uIcc_of_le (by linarith)]
      exact Icc_subset_Icc le_rfl (by linarith [hε.1]))
  have hg2 : IntervalIntegrable liAux volume (1 + ε) x :=
    hg.mono_set (by
      rw [uIcc_of_le (by linarith [hε.1]), uIcc_of_le (by linarith)]
      exact Icc_subset_Icc (by linarith [hε.1]) le_rfl)
  have hsplit : (fun t : ℝ => 1 / Real.log t) = fun t => 1 / (t - 1) + liAux t := by
    funext t; simp only [liAux]; ring
  rw [hsplit, intervalIntegral.integral_add hc1 hg1, intervalIntegral.integral_add hc2 hg2,
    ← pv_inv_sub_one hε.1 hε1 hεx]
  ring

/-! ### §4.10(ii) Exponentials: definite integrals -/

/-- **DLMF 4.10.11**: `∫_{−∞}^{∞} e^{−cx²} dx = √(π/c)`, `ℜc > 0` (principal square root). -/
theorem dlmf_4_10_11 {c : ℂ} (hc : 0 < c.re) :
    ∫ x : ℝ, exp (-c * (x : ℂ) ^ 2) = (π / c) ^ (1 / 2 : ℂ) :=
  integral_gaussian_complex hc

/-- `∫₀¹ ln(1 + u)/u du = π²/12`. -/
theorem integral_log_one_add_div : ∫ u in (0 : ℝ)..1, Real.log (1 + u) / u = π ^ 2 / 12 := by
  have hint : ∀ n : ℕ, ∫ u in (0 : ℝ)..1, (-1) ^ n * u ^ n / (n + 1) =
      (-1) ^ n / ((n : ℝ) + 1) ^ 2 := fun n => by
    simp only [mul_div_assoc, intervalIntegral.integral_const_mul, intervalIntegral.integral_div,
      integral_pow]
    have : (n : ℝ) + 1 ≠ 0 := by positivity
    field_simp
    simp
  have hab : ∀ n : ℕ, ∫ u in (0 : ℝ)..1, |(-1) ^ n * u ^ n / (n + 1)| =
      1 / ((n : ℝ) + 1) ^ 2 := fun n => by
    rw [intervalIntegral.integral_congr (g := fun u => u ^ n / (n + 1)) fun u hu => by
      rw [uIcc_of_le zero_le_one] at hu
      simp only
      rw [abs_div, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
        abs_of_nonneg (pow_nonneg hu.1 n), abs_of_pos (by positivity : (0 : ℝ) < n + 1)]]
    simp only [intervalIntegral.integral_div, integral_pow]
    have : (n : ℝ) + 1 ≠ 0 := by positivity
    field_simp
    simp
  have h := hasSum_integral01 (F := fun n u => (-1) ^ n * u ^ n / (n + 1))
    (f := fun u => Real.log (1 + u) / u)
    (fun n => (((continuous_const.mul (continuous_pow n)).div_const _)).intervalIntegrable _ _)
    (by simp only [hab]; exact hasSum_inv_sq_succ.summable)
    (fun u hu => by
      have h1 : |-u| < 1 := by rw [abs_neg, abs_of_pos hu.1]; exact hu.2
      have := (Real.hasSum_pow_div_log_of_abs_lt_one h1).mul_left (-1 / u)
      convert this using 1
      · funext n; have := hu.1.ne'; rw [neg_pow, pow_succ, neg_pow]; field_simp; ring
      · rw [sub_neg_eq_add]; have := hu.1.ne'; field_simp)
  simp only [hint] at h
  exact h.unique hasSum_alt_inv_sq

/-- **DLMF 4.10.12**: `∫₀^{ln 2} x eˣ/(eˣ − 1) dx = π²/12` (substitute `u = eˣ − 1`). -/
theorem dlmf_4_10_12 :
    ∫ x in (0 : ℝ)..Real.log 2, x * Real.exp x / (Real.exp x - 1) = π ^ 2 / 12 := by
  set g : ℝ → ℝ := fun u => Real.log (1 + u) / u
  set f : ℝ → ℝ := fun x => Real.exp x - 1
  have hl2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hgb : ∀ u, 0 ≤ u → |g u| ≤ 1 := fun u hu => by
    rcases hu.eq_or_lt with rfl | hu'
    · simp [g]
    have h1 : Real.log (1 + u) ≤ u := by
      have := Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < 1 + u); linarith
    have h0 : 0 ≤ Real.log (1 + u) := Real.log_nonneg (by linarith)
    simp only [g]
    rw [abs_of_nonneg (div_nonneg h0 hu), div_le_one hu']
    exact h1
  have hgm : Measurable g :=
    (Real.measurable_log.comp (measurable_const.add measurable_id)).div measurable_id
  have himg : ∀ x ∈ Icc (0 : ℝ) (Real.log 2), f x ∈ Icc (0 : ℝ) 1 := fun x hx => by
    simp only [f]
    constructor
    · linarith [Real.add_one_le_exp x, hx.1]
    · have := Real.exp_le_exp.mpr hx.2; rw [Real.exp_log (by norm_num)] at this; linarith
  have key := integral_comp_mul_deriv''' (a := 0) (b := Real.log 2) (f := f)
    (f' := Real.exp) (g := g)
    (by simp only [f]; exact (Real.continuous_exp.sub continuous_const).continuousOn)
    (fun x _ => ((Real.hasDerivAt_exp x).sub_const 1).hasDerivWithinAt)
    (by
      refine ContinuousOn.mono (s := Ioi 0) ?_ ?_
      · exact ((Real.continuousOn_log.comp (continuous_const.add continuous_id).continuousOn
          fun u hu => by
            simp only [mem_compl_iff, mem_singleton_iff]
            intro h; simp only [Pi.add_apply, id] at h; linarith [mem_Ioi.mp hu]).div
          continuousOn_id fun u hu => (mem_Ioi.mp hu).ne')
      · rintro _ ⟨x, hx, rfl⟩
        rw [min_eq_left hl2, max_eq_right hl2] at hx
        simp only [f, mem_Ioi]
        linarith [Real.add_one_lt_exp hx.1.ne', hx.1])
    (by
      refine IntegrableOn.mono_set (t := Icc 0 1) ?_ ?_
      · exact (intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one).mp
          (intervalIntegrable_of_abs_le zero_le_one hgm 1 fun u hu => hgb u hu.1.le)
      · rintro _ ⟨x, hx, rfl⟩
        rw [uIcc_of_le hl2] at hx
        exact himg x hx)
    (by
      rw [uIcc_of_le hl2]
      refine (intervalIntegrable_iff_integrableOn_Icc_of_le hl2).mp
        (intervalIntegrable_of_abs_le hl2 ((hgm.comp ((Real.measurable_exp).sub_const 1)).mul
          Real.measurable_exp) 2 fun x hx => ?_)
      have hx' : x ∈ Icc (0 : ℝ) (Real.log 2) := Ioc_subset_Icc_self hx
      have h1 := hgb (f x) (himg x hx').1
      have h2 : Real.exp x ≤ 2 := by
        have := Real.exp_le_exp.mpr hx'.2; rwa [Real.exp_log (by norm_num)] at this
      simp only [Function.comp]
      rw [abs_mul, abs_of_pos (Real.exp_pos x)]
      nlinarith [abs_nonneg (g (f x)), Real.exp_pos x])
  have hf0 : f 0 = 0 := by simp [f]
  have hf1 : f (Real.log 2) = 1 := by simp only [f]; rw [Real.exp_log (by norm_num)]; norm_num
  rw [hf0, hf1, integral_log_one_add_div] at key
  rw [← key]
  congr 1
  funext x
  simp only [Function.comp, g, f, add_sub_cancel, Real.log_exp]
  ring

/-- **DLMF 4.10.13**: `∫₀^∞ dx/(eˣ + 1) = ln 2`. -/
theorem dlmf_4_10_13 : ∫ x in Ioi (0 : ℝ), 1 / (Real.exp x + 1) = Real.log 2 := by
  have hderiv : ∀ x ∈ Ici (0 : ℝ), HasDerivAt (fun x => x - Real.log (Real.exp x + 1))
      (1 / (Real.exp x + 1)) x := fun x _ => by
    have hpos : 0 < Real.exp x + 1 := by positivity
    have h : HasDerivAt (fun x => x - Real.log (Real.exp x + 1))
        (1 - Real.exp x / (Real.exp x + 1)) x :=
      (hasDerivAt_id' x).sub (((Real.hasDerivAt_exp x).add_const 1).log hpos.ne')
    exact h.congr_deriv (by field_simp; ring)
  have hlim : Tendsto (fun x => x - Real.log (Real.exp x + 1)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun x : ℝ => 1 + Real.exp (-x)) atTop (𝓝 (1 + 0)) :=
      tendsto_const_nhds.add Real.tendsto_exp_neg_atTop_nhds_zero
    rw [add_zero] at h1
    have h2 := ((Real.continuousAt_log one_ne_zero).tendsto.comp h1).neg
    rw [Real.log_one, neg_zero] at h2
    refine h2.congr fun x => ?_
    simp only [Function.comp]
    have : Real.exp x + 1 = Real.exp x * (1 + Real.exp (-x)) := by
      rw [mul_add, ← Real.exp_add]; simp
    rw [this, Real.log_mul (Real.exp_pos x).ne' (by positivity), Real.log_exp]
    ring
  rw [integral_Ioi_of_hasDerivAt_of_nonneg' hderiv (fun x _ => by positivity) hlim]
  simp
  norm_num

end Azurite.DLMF
