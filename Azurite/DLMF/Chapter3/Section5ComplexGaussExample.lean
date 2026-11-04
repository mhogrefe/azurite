/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter3.Section5ComplexGauss
import Azurite.DLMF.Chapter1.Section14TableLaplace
import Azurite.BrentZimmermann.Chapter4.Bessel
import Mathlib.Analysis.Analytic.Binomial

/-!
# DLMF §3.5(viii), Example: Laplace transform inversion

* 3.5.38/3.5.39: the Laplace transform and its inversion are those of §1.14(iii) (`laplace`,
  `bromwichPartial`, `dlmf_2_4_3`).
* 3.5.40: `J₀` (`besselJ0`, the series 10.2.2 via `BZ.besselJNat 0`) and `G(p) = 1/√(p² + 1)`
  (`lapG`): `|J₀(t)| ≤ 1` (`abs_besselJ0_le_one`, energy `J₀² + J₀′²` decreasing by the Bessel
  equation `besselJ0_ode`); `ℒ[J₀](p) = G(p)` for real `p > 1` by termwise integration and the
  binomial series (`laplace_besselJ0_real`, `choose_neg_half`, `hasSum_one_add_rpow_neg_half`),
  then for `ℜp > 0` by analytic continuation (`laplace_besselJ0`); the inversion 3.5.39 holds for
  every `σ > 0` (`tendsto_bromwich_lapG`).
* The substitution `ζ = tp`, `c = tσ`, `f(ζ) = t^{−1} ζ^s G(ζ/t)` turns 3.5.39 into 3.5.35
  (`lapF`, `bromwichPartial_lapF`, `tendsto_cgI_lapF`, `cgI_lapF_besselJ0`); with `s = 1`,
  `f(ζ) = ζ/√(ζ² + t²)` (`lapF_lapG`), bounded at infinity (`norm_lapF_lapG_le`).
* 3.5.41: `J₀(t) = ∑ₖ wₖ ζₖ/√(ζₖ² + t²) + Eₙ(f)` (`lapApprox`, `dlmf_3_5_41`); `∑ₖ wₖ = 1/Γ(s)`
  (`sum_cgWeight`) and the value `1` at `t = 0` (`lapApprox_zero`).
-/

open Polynomial Finset Set Filter Topology MeasureTheory

namespace Azurite.DLMF

/-! ### The Bessel function `J₀` and `|J₀(t)| ≤ 1` -/

/-- The Bessel function `J₀(t) = ∑_j (−1)ʲ (t/2)^{2j}/(j!)²` (§10.2(ii)), the `n = 0` case of
`BZ.besselJNat`. -/
noncomputable def besselJ0 (t : ℝ) : ℝ := BZ.besselJNat 0 t

theorem besselJ0_eq_besselJ (t : ℝ) : besselJ0 t = BZ.besselJ 0 t := by
  rw [besselJ0, ← BZ.besselJ_natCast]; rfl

theorem hasDerivAt_besselJ0 (t : ℝ) : HasDerivAt besselJ0 (BZ.besselJNat' 0 t) t :=
  BZ.hasDerivAt_besselJNat 0 t

theorem besselJ0_zero : besselJ0 0 = 1 := by
  rw [besselJ0_eq_besselJ]; exact BZ.besselJ_zero_left

theorem besselJNat'_zero_zero : BZ.besselJNat' 0 0 = 0 := by
  rw [BZ.besselJNat']
  refine (tsum_congr fun j => ?_).trans tsum_zero
  rcases j with _ | j
  · simp
  · simp [show 2 * (j + 1) - 1 ≠ 0 by omega]

/-- `J₀` solves `t² y″ + t y′ + t² y = 0`. -/
theorem besselJ0_ode (t : ℝ) :
    t ^ 2 * BZ.besselJNat'' 0 t + t * BZ.besselJNat' 0 t + t ^ 2 * besselJ0 t = 0 := by
  have h := BZ.besselJNat_ode 0 t
  have hd : deriv (BZ.besselJNat 0) = BZ.besselJNat' 0 :=
    funext fun x => (BZ.hasDerivAt_besselJNat 0 x).deriv
  have hd' : deriv (BZ.besselJNat' 0) = BZ.besselJNat'' 0 :=
    funext fun x => (BZ.hasDerivAt_besselJNat' 0 x).deriv
  rw [hd, hd'] at h
  simp only [Nat.cast_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    sub_zero] at h
  rw [besselJ0]; linarith

/-- `|J₀(t)| ≤ 1` for `t ≥ 0`: the energy `J₀² + J₀′²` decreases from its value `1` at `0`. -/
theorem abs_besselJ0_le_one {t : ℝ} (ht : 0 ≤ t) : |besselJ0 t| ≤ 1 := by
  set E : ℝ → ℝ := fun x => besselJ0 x ^ 2 + BZ.besselJNat' 0 x ^ 2
  have hE : ∀ x, HasDerivAt E (2 * besselJ0 x * BZ.besselJNat' 0 x +
      2 * BZ.besselJNat' 0 x * BZ.besselJNat'' 0 x) x := fun x => by
    have h1 := (hasDerivAt_besselJ0 x).pow 2
    have h2 := (BZ.hasDerivAt_besselJNat' 0 x).pow 2
    convert h1.add h2 using 1
    push_cast; ring
  have hanti : AntitoneOn E (Ici 0) := by
    refine antitoneOn_of_deriv_nonpos (convex_Ici 0)
      (fun x _ => (hE x).continuousAt.continuousWithinAt)
      (fun x _ => (hE x).differentiableAt.differentiableWithinAt) fun x hx => ?_
    rw [interior_Ici] at hx
    have hx : 0 < x := hx
    rw [(hE x).deriv]
    have hode := besselJ0_ode x
    have hx0 : x ≠ 0 := hx.ne'
    have h1 : x * (x * BZ.besselJNat'' 0 x + BZ.besselJNat' 0 x + x * besselJ0 x) = 0 := by
      linear_combination hode
    have h1' := (mul_eq_zero.mp h1).resolve_left hx0
    have h2 : BZ.besselJNat'' 0 x = -(BZ.besselJNat' 0 x / x) - besselJ0 x := by
      field_simp; linear_combination h1'
    rw [h2]
    have : 0 ≤ BZ.besselJNat' 0 x ^ 2 / x := by positivity
    have e : 2 * besselJ0 x * BZ.besselJNat' 0 x + 2 * BZ.besselJNat' 0 x *
        (-(BZ.besselJNat' 0 x / x) - besselJ0 x) = -(2 * (BZ.besselJNat' 0 x ^ 2 / x)) := by ring
    rw [e]; linarith
  have h0 : E 0 = 1 := by simp [E, besselJ0_zero, besselJNat'_zero_zero]
  have hle := hanti Set.self_mem_Ici ht ht
  rw [h0] at hle
  have : besselJ0 t ^ 2 ≤ 1 := by
    have := sq_nonneg (BZ.besselJNat' 0 t)
    simp only [E] at hle; linarith
  exact (sq_le_one_iff_abs_le_one _).mp this

/-! ### The Laplace transform of `J₀` for real `p > 1` -/

theorem eval_descPochhammer_neg_half (n : ℕ) :
    (descPochhammer ℝ n).eval (-1 / 2 : ℝ) =
      (-1) ^ n * (2 * n).factorial / (4 ^ n * n.factorial) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [descPochhammer_succ_eval, ih, show 2 * (n + 1) = 2 * n + 1 + 1 by ring,
      Nat.factorial_succ (2 * n + 1), Nat.factorial_succ (2 * n), Nat.factorial_succ n]
    push_cast
    field_simp
    ring

/-- `binom(−1/2, n) = (−1)ⁿ (2n)!/(4ⁿ (n!)²)`. -/
theorem choose_neg_half (n : ℕ) :
    Ring.choose (-1 / 2 : ℝ) n =
      (-1) ^ n * (2 * n).factorial / (4 ^ n * (n.factorial : ℝ) ^ 2) := by
  rw [Ring.choose_eq_smul, ← aeval_eq_smeval, aeval_def, ← eval_map, descPochhammer_map,
    eval_descPochhammer_neg_half, smul_eq_mul]
  have : (n.factorial : ℝ) ≠ 0 := by positivity
  field_simp

/-- The binomial series `(1 + x)^{−1/2} = ∑ binom(−1/2, n) xⁿ`, `|x| < 1`. -/
theorem hasSum_one_add_rpow_neg_half {x : ℝ} (hx : |x| < 1) :
    HasSum (fun n : ℕ => Ring.choose (-1 / 2 : ℝ) n * x ^ n) ((1 + x) ^ (-1 / 2 : ℝ)) := by
  have hmem : x ∈ Metric.eball (0 : ℝ) 1 := by
    rw [Metric.mem_eball, edist_zero_right, ← ofReal_norm]
    exact ENNReal.ofReal_lt_one.mpr (by simpa using hx)
  have h := (Real.one_add_rpow_hasFPowerSeriesOnBall_zero (a := (-1 / 2 : ℝ))).hasSum_sub
    (show x ∈ Metric.eball (0 : ℝ) 1 from hmem)
  simp only [sub_zero, FormalMultilinearSeries.apply_eq_pow_smul_coeff, smul_eq_mul]
    at h
  convert h using 2 with n
  rw [binomialSeries, FormalMultilinearSeries.coeff_ofScalars, mul_comm]

/-- The terms of the Laplace transform of the series of `J₀`. -/
noncomputable def j0LapTerm (p : ℝ) (j : ℕ) (t : ℝ) : ℂ :=
  ((BZ.besselCoeff 0 j / 4 ^ j : ℝ) : ℂ) * ((t : ℂ) ^ (2 * j) * Complex.exp (-((p : ℂ) * t)))

theorem integral_pow_mul_exp_neg_real {p : ℝ} (hp : 0 < p) (n : ℕ) :
    ∫ t in Ioi (0 : ℝ), t ^ n * Real.exp (-(p * t)) = n.factorial / p ^ (n + 1) := by
  have h := integral_Ioi_pow_mul_cexp_neg (c := p) (by simpa using hp) n
  have e : ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ n * Complex.exp (-((p : ℂ) * t)) =
      ((∫ t in Ioi (0 : ℝ), t ^ n * Real.exp (-(p * t)) : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    push_cast; rfl
  rw [e] at h
  exact_mod_cast h

theorem laplace_besselJ0_real {p : ℝ} (hp : 1 < p) :
    laplace (fun t => (besselJ0 t : ℂ)) p = (((p ^ 2 + 1) ^ (-1 / 2 : ℝ) : ℝ) : ℂ) := by
  have hp0 : 0 < p := by linarith
  have hJ : ∀ t : ℝ, Complex.exp (-((p : ℂ) * t)) * (besselJ0 t : ℂ) = ∑' j, j0LapTerm p j t := by
    intro t
    rw [besselJ0, BZ.besselJNat, Complex.ofReal_tsum, ← tsum_mul_left]
    refine tsum_congr fun j => ?_
    simp only [j0LapTerm, add_zero]
    have h4 : ((t / 2 : ℝ) : ℂ) ^ (2 * j) = (t : ℂ) ^ (2 * j) / 4 ^ j := by
      push_cast; rw [div_pow, pow_mul (2 : ℂ)]; norm_num
    push_cast at h4 ⊢
    rw [h4]; ring
  have hint : ∀ j, Integrable (j0LapTerm p j) (volume.restrict (Ioi 0)) := fun j =>
    (integrableOn_Ioi_pow_mul_cexp_neg (c := p) (by simpa using hp0) (2 * j)).const_mul _
  have hval : ∀ j, ∫ t in Ioi (0 : ℝ), j0LapTerm p j t =
      ((BZ.besselCoeff 0 j / 4 ^ j * ((2 * j).factorial / p ^ (2 * j + 1)) : ℝ) : ℂ) := by
    intro j
    rw [show (fun t => j0LapTerm p j t) = fun t : ℝ => ((BZ.besselCoeff 0 j / 4 ^ j : ℝ) : ℂ) *
        ((t : ℂ) ^ (2 * j) * Complex.exp (-((p : ℂ) * t))) from rfl, integral_const_mul,
      integral_Ioi_pow_mul_cexp_neg (by simpa using hp0)]
    push_cast; ring
  have hnorm : ∀ j, ∫ t in Ioi (0 : ℝ), ‖j0LapTerm p j t‖ =
      |BZ.besselCoeff 0 j| / 4 ^ j * ((2 * j).factorial / p ^ (2 * j + 1)) := by
    intro j
    rw [← integral_pow_mul_exp_neg_real hp0, ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    have ht : 0 < t := ht
    simp only [j0LapTerm, norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_pow,
      Complex.norm_exp]
    rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < 4 ^ j), abs_of_pos ht]
    simp
  have hsum : Summable fun j => ∫ t in Ioi (0 : ℝ), ‖j0LapTerm p j t‖ := by
    simp only [hnorm]
    refine Summable.of_nonneg_of_le (fun j => by positivity) (fun j => ?_)
      ((summable_geometric_of_lt_one (by positivity) (show (p ^ 2)⁻¹ < 1 from
        inv_lt_one_of_one_lt₀ (by nlinarith))).mul_left p⁻¹)
    have hc : |BZ.besselCoeff 0 j| = ((j.factorial : ℝ) ^ 2)⁻¹ := by
      simp [BZ.besselCoeff, abs_div, sq]
    have hcb : ((2 * j).factorial : ℝ) ≤ 4 ^ j * (j.factorial : ℝ) ^ 2 := by
      have h1 := Nat.choose_mul_factorial_mul_factorial (show j ≤ 2 * j by omega)
      rw [show 2 * j - j = j by omega] at h1
      have h2 := Nat.centralBinom_le_four_pow j
      rw [Nat.centralBinom_eq_two_mul_choose] at h2
      have : ((2 * j).factorial : ℝ) = ((2 * j).choose j : ℝ) * j.factorial * j.factorial := by
        exact_mod_cast h1.symm
      rw [this, sq, ← mul_assoc]
      gcongr
      exact_mod_cast h2
    rw [hc]
    have hj : (0 : ℝ) < (j.factorial : ℝ) ^ 2 := by positivity
    calc ((j.factorial : ℝ) ^ 2)⁻¹ / 4 ^ j * ((2 * j).factorial / p ^ (2 * j + 1))
        = ((2 * j).factorial / (4 ^ j * (j.factorial : ℝ) ^ 2)) * (p ^ (2 * j + 1))⁻¹ := by
          ring
      _ ≤ 1 * (p ^ (2 * j + 1))⁻¹ :=
          mul_le_mul_of_nonneg_right (div_le_one_of_le₀ hcb (by positivity)) (by positivity)
      _ = p⁻¹ * (p ^ 2)⁻¹ ^ j := by
          rw [inv_pow, ← pow_mul, pow_succ, mul_inv]; ring
  -- the termwise integral
  rw [laplace]
  rw [show (fun t : ℝ => Complex.exp (-((p : ℂ) * t)) * (besselJ0 t : ℂ)) =
      fun t => ∑' j, j0LapTerm p j t from funext hJ,
    ← integral_tsum_of_summable_integral_norm hint hsum]
  simp only [hval]
  rw [← Complex.ofReal_tsum]
  congr 1
  -- the binomial series
  have hx : |(p ^ 2)⁻¹| < 1 := by
    rw [abs_of_pos (by positivity)]; exact inv_lt_one_of_one_lt₀ (by nlinarith)
  have hb := (hasSum_one_add_rpow_neg_half hx).mul_left p⁻¹
  have e1 : ∀ j, p⁻¹ * (Ring.choose (-1 / 2 : ℝ) j * ((p ^ 2)⁻¹) ^ j) =
      BZ.besselCoeff 0 j / 4 ^ j * ((2 * j).factorial / p ^ (2 * j + 1)) := fun j => by
    rw [choose_neg_half, BZ.besselCoeff, inv_pow, ← pow_mul, pow_succ]
    have : (j.factorial : ℝ) ≠ 0 := by positivity
    simp only [zero_add]
    field_simp
    ring
  simp only [e1] at hb
  rw [hb.tsum_eq]
  have hq : (0 : ℝ) < p ^ 2 + 1 := by positivity
  rw [show 1 + (p ^ 2)⁻¹ = (p ^ 2 + 1) * (p⁻¹) ^ 2 by field_simp,
    Real.mul_rpow hq.le (by positivity)]
  have hpp : ((p⁻¹) ^ 2) ^ (-1 / 2 : ℝ) = p := by
    rw [show (-1 / 2 : ℝ) = -(1 / 2) by ring, Real.rpow_neg (by positivity),
      ← Real.sqrt_eq_rpow, Real.sqrt_sq (by positivity), inv_inv]
  rw [hpp]
  field_simp

/-! ### 3.5.40 and the inversion 3.5.39 for `σ > 0` -/

/-- `G(p) = 1/√(p² + 1)` (principal branch). -/
noncomputable def lapG (p : ℂ) : ℂ := (p ^ 2 + 1) ^ (-(1 / 2 : ℂ))

theorem sq_add_one_mem_slitPlane {p : ℂ} (hp : 0 < p.re) : p ^ 2 + 1 ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  by_cases him : p.im = 0
  · left; simp [sq, him]; positivity
  · right
    simp only [Complex.add_im, sq, Complex.mul_im, Complex.one_im, add_zero]
    have := mul_ne_zero hp.ne' him
    intro h; apply this; linarith

theorem continuous_besselJ0 : Continuous besselJ0 :=
  continuous_iff_continuousAt.mpr fun t => (hasDerivAt_besselJ0 t).continuousAt

theorem expGrowth_besselJ0 : ExpGrowth 1 0 (fun t => (besselJ0 t : ℂ)) := fun t ht => by
  simpa using abs_besselJ0_le_one ht

/-- **DLMF 3.5.40**: `ℒ[J₀](p) = 1/√(p² + 1)` for `ℜp > 0`. -/
theorem laplace_besselJ0 {p : ℂ} (hp : 0 < p.re) :
    laplace (fun t => (besselJ0 t : ℂ)) p = lapG p := by
  set U : Set ℂ := {p | 0 < p.re}
  have hm : AEStronglyMeasurable (fun t => (besselJ0 t : ℂ)) (volume.restrict (Ioi 0)) :=
    (Complex.continuous_ofReal.comp continuous_besselJ0).aestronglyMeasurable
  have hf : AnalyticOnNhd ℂ (laplace fun t => (besselJ0 t : ℂ)) U :=
    analyticOnNhd_laplace hm expGrowth_besselJ0
  have hg : AnalyticOnNhd ℂ lapG U := by
    refine DifferentiableOn.analyticOnNhd (fun q hq => ?_) (isOpen_lt continuous_const
      Complex.continuous_re)
    exact (DifferentiableAt.cpow_const (f := fun z : ℂ => z ^ 2 + 1) (by fun_prop)
      (sq_add_one_mem_slitPlane hq)).differentiableWithinAt
  have hU : IsPreconnected U := (convex_halfSpace_re_gt 0).isPreconnected
  have h2 : (2 : ℂ) ∈ U := by simp [U]
  have hfreq : ∃ᶠ z in 𝓝[≠] (2 : ℂ), laplace (fun t => (besselJ0 t : ℂ)) z = lapG z := by
    have ht : Tendsto (fun x : ℝ => (x : ℂ)) (𝓝[>] 2) (𝓝[≠] (2 : ℂ)) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
      · exact (Complex.continuous_ofReal.tendsto' 2 2 (by simp)).mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with x hx
        simp only [mem_compl_iff, mem_singleton_iff]
        exact_mod_cast (ne_of_gt hx : x ≠ 2)
    refine ht.frequently (Eventually.frequently ?_)
    filter_upwards [self_mem_nhdsWithin] with x (hx : 2 < x)
    rw [laplace_besselJ0_real (by linarith), lapG]
    rw [Complex.ofReal_cpow (by positivity)]
    push_cast; ring_nf
  exact hf.eqOn_of_preconnected_of_frequently_eq hg hU h2 hfreq hp

/-- **DLMF 3.5.39** for the pair 3.5.40 ("satisfy these conditions, provided that `σ > 0`"):
`J₀(t) = (2πi)^{−1} ∫_{σ−i∞}^{σ+i∞} e^{tp} G(p) dp`. -/
theorem tendsto_bromwich_lapG {σ t : ℝ} (hσ : 0 < σ) (ht : 0 < t) :
    Tendsto (bromwichPartial lapG σ t) atTop (𝓝 (besselJ0 t : ℂ)) := by
  have hint : IntegrableOn (fun τ : ℝ => Complex.exp (-((σ : ℂ) * τ)) * (besselJ0 τ : ℂ))
      (Ioi 0) :=
    integrableOn_laplace (Complex.continuous_ofReal.comp continuous_besselJ0).aestronglyMeasurable
      expGrowth_besselJ0 (by simpa using hσ)
  have h := dlmf_2_4_3 (q := fun τ => (besselJ0 τ : ℂ)) (q' := fun τ => (BZ.besselJNat' 0 τ : ℂ))
    hint (fun τ _ => (hasDerivAt_besselJ0 τ).ofReal_comp)
    (Complex.continuous_ofReal.comp (continuous_iff_continuousAt.mpr fun x =>
      (BZ.hasDerivAt_besselJNat' 0 x).continuousAt)).continuousOn le_rfl ht
  refine h.congr fun η => ?_
  unfold bromwichPartial
  congr 1
  refine intervalIntegral.integral_congr fun y _ => ?_
  rw [laplace_besselJ0 (by simpa using hσ)]

/-! ### The substitution `ζ = tp`, `c = tσ`, `f(ζ) = t^{−1} ζ^s G(ζ/t)` -/

/-- The integrand `f(ζ) = t^{−1} ζ^s G(ζ/t)` of 3.5.35 obtained from 3.5.39. -/
noncomputable def lapF (G : ℂ → ℂ) (s t : ℝ) (ζ : ℂ) : ℂ := (t : ℂ)⁻¹ * ζ ^ (s : ℂ) * G (ζ / t)

theorem bromwichPartial_lapF (G : ℂ → ℂ) {s σ t : ℝ} (hσ : 0 < σ) (ht : 0 < t) (η : ℝ) :
    bromwichPartial (fun z => z ^ (-(s : ℂ)) * lapF G s t z) (t * σ) 1 η =
      bromwichPartial G σ t (η / t) := by
  unfold bromwichPartial lapF
  congr 1
  have ht0 : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
  have hint : ∀ y : ℝ, Complex.exp ((((t * σ : ℝ) : ℂ) + y * Complex.I) * ((1 : ℝ) : ℂ)) *
      ((((t * σ : ℝ) : ℂ) + y * Complex.I) ^ (-(s : ℂ)) * ((t : ℂ)⁻¹ *
        (((t * σ : ℝ) : ℂ) + y * Complex.I) ^ (s : ℂ) *
          G ((((t * σ : ℝ) : ℂ) + y * Complex.I) / t))) =
      (t : ℂ)⁻¹ * (Complex.exp (((σ : ℂ) + ((y / t : ℝ) : ℂ) * Complex.I) * t) *
        G ((σ : ℂ) + ((y / t : ℝ) : ℂ) * Complex.I)) := fun y => by
    have hz := line_ne_zero (mul_pos ht hσ) y
    have e1 : (((t * σ : ℝ) : ℂ) + y * Complex.I) / t =
        (σ : ℂ) + ((y / t : ℝ) : ℂ) * Complex.I := by
      push_cast; field_simp
    have e2 : (((t * σ : ℝ) : ℂ) + y * Complex.I) * ((1 : ℝ) : ℂ) =
        ((σ : ℂ) + ((y / t : ℝ) : ℂ) * Complex.I) * t := by
      push_cast; field_simp
    have hzs : (((t * σ : ℝ) : ℂ) + y * Complex.I) ^ (s : ℂ) ≠ 0 := by
      rw [Complex.cpow_def_of_ne_zero hz]; exact Complex.exp_ne_zero _
    rw [e1, e2, Complex.cpow_neg]
    generalize ((((t * σ : ℝ) : ℂ) + y * Complex.I) ^ (s : ℂ)) = Z at hzs ⊢
    field_simp
  simp only [hint]
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_div (fun u => Complex.exp (((σ : ℂ) + (u : ℂ) * Complex.I) * t) *
      G ((σ : ℂ) + (u : ℂ) * Complex.I)) ht.ne', neg_div, Complex.real_smul, ← mul_assoc,
    inv_mul_cancel₀ ht0, one_mul]

/-- 3.5.39 has the form 3.5.35 with `ζ = tp`, `c = tσ`, `f(ζ) = t^{−1} ζ^s G(ζ/t)`: if the
Bromwich integral of `G` converges to `L`, so does `I(f)`. -/
theorem tendsto_cgI_lapF (G : ℂ → ℂ) {s σ t : ℝ} (hσ : 0 < σ) (ht : 0 < t) {L : ℂ}
    (h : Tendsto (bromwichPartial G σ t) atTop (𝓝 L)) :
    Tendsto (bromwichPartial (fun z => z ^ (-(s : ℂ)) * lapF G s t z) (t * σ) 1) atTop
      (𝓝 L) :=
  (h.comp (tendsto_id.atTop_div_const ht)).congr fun η => (bromwichPartial_lapF G hσ ht η).symm

/-- For 3.5.40 and `s = 1`: `I(f) = J₀(t)` with `f(ζ) = t^{−1} ζ G(ζ/t)`. -/
theorem cgI_lapF_besselJ0 {σ t : ℝ} (hσ : 0 < σ) (ht : 0 < t) :
    cgI 1 (t * σ) (lapF lapG 1 t) = besselJ0 t :=
  bromwich_eq_of_tendsto (tendsto_cgI_lapF lapG hσ ht (tendsto_bromwich_lapG hσ ht))

theorem ofReal_mul_cpow_of_pos {c : ℝ} (hc : 0 < c) {w : ℂ} (hw : w ≠ 0) (r : ℂ) :
    ((c : ℂ) * w) ^ r = (c : ℂ) ^ r * w ^ r := by
  have hc0 : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  rw [Complex.cpow_def_of_ne_zero (mul_ne_zero hc0 hw), Complex.cpow_def_of_ne_zero hc0,
    Complex.cpow_def_of_ne_zero hw, Complex.log_ofReal_mul hc hw, ← Complex.exp_add,
    Complex.ofReal_log hc.le]
  ring_nf

/-- With `s = 1`: `f(ζ) = t^{−1} ζ G(ζ/t) = ζ/√(ζ² + t²)`. -/
theorem lapF_lapG {t : ℝ} (ht : 0 < t) (ζ : ℂ) :
    lapF lapG 1 t ζ = ζ / (ζ ^ 2 + (t : ℂ) ^ 2) ^ (1 / 2 : ℂ) := by
  have ht0 : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
  unfold lapF lapG
  rw [Complex.ofReal_one, Complex.cpow_one]
  have e : (ζ / t) ^ 2 + 1 = (((t ^ 2)⁻¹ : ℝ) : ℂ) * (ζ ^ 2 + (t : ℂ) ^ 2) := by
    push_cast; field_simp
  rw [e]
  by_cases hw : ζ ^ 2 + (t : ℂ) ^ 2 = 0
  · rw [hw]; simp
  · have hinv : (0 : ℝ) < (t ^ 2)⁻¹ := by positivity
    rw [ofReal_mul_cpow_of_pos hinv hw]
    have hpow : (((t ^ 2)⁻¹ : ℝ) : ℂ) ^ (-(1 / 2 : ℂ)) = t := by
      rw [show (-(1 / 2 : ℂ)) = ((-(1 / 2) : ℝ) : ℂ) by push_cast; ring,
        ← Complex.ofReal_cpow hinv.le, Real.rpow_neg hinv.le, ← Real.sqrt_eq_rpow,
        Real.sqrt_inv, Real.sqrt_sq ht.le, inv_inv]
    rw [hpow, Complex.cpow_neg]
    field_simp

/-- "We choose `s = 1` so that `f(ζ) = O(1)` at infinity": `|f(ζ)| ≤ 2` for `|ζ| ≥ 2t`. -/
theorem norm_lapF_lapG_le {t : ℝ} (ht : 0 < t) {ζ : ℂ} (hζ : 2 * t ≤ ‖ζ‖) :
    ‖lapF lapG 1 t ζ‖ ≤ 2 := by
  rw [lapF_lapG ht]
  have hζ0 : 0 < ‖ζ‖ := by linarith
  have hw : ‖ζ‖ ^ 2 / 4 ≤ ‖ζ ^ 2 + (t : ℂ) ^ 2‖ := by
    have h1 := norm_sub_norm_le (ζ ^ 2) (-(t : ℂ) ^ 2)
    rw [sub_neg_eq_add, norm_pow, norm_neg, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos ht] at h1
    nlinarith
  have hw0 : ζ ^ 2 + (t : ℂ) ^ 2 ≠ 0 := by
    intro h; rw [h, norm_zero] at hw; nlinarith
  rw [norm_div, show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring, Complex.norm_cpow_real]
  have hs : ‖ζ‖ / 2 ≤ ‖ζ ^ 2 + (t : ℂ) ^ 2‖ ^ (1 / 2 : ℝ) := by
    rw [← Real.sqrt_eq_rpow]
    exact Real.le_sqrt_of_sq_le (by nlinarith)
  rw [div_le_iff₀ ((by positivity : (0 : ℝ) < ‖ζ‖ / 2).trans_le hs)]
  linarith

/-! ### 3.5.41 -/

/-- The approximation 3.5.41 with the `n`-point complex Gauss rule for `s = 1`:
`gₙ(t) = ∑ₖ wₖ ζₖ/√(ζₖ² + t²)`. -/
noncomputable def lapApprox (n : ℕ) (t : ℝ) : ℂ :=
  ∑ ζ ∈ cgNodes 1 n, cgWeight 1 n ζ * (ζ / (ζ ^ 2 + (t : ℂ) ^ 2) ^ (1 / 2 : ℂ))

/-- **DLMF 3.5.41**: `J₀(t) = ∑ₖ wₖ ζₖ/√(ζₖ² + t²) + Eₙ(f)`; dropping the error term of 3.5.36
gives 3.5.41 ("approximately"). -/
theorem dlmf_3_5_41 {σ t : ℝ} (hσ : 0 < σ) (ht : 0 < t) (n : ℕ) :
    (besselJ0 t : ℂ) = lapApprox n t + cgE 1 (t * σ) n (lapF lapG 1 t) := by
  rw [cgE, cgI_lapF_besselJ0 hσ ht, lapApprox]
  simp only [lapF_lapG ht]
  ring

/-- The weights sum to `1/Γ(s)` (3.5.36 with `f = 1`). -/
theorem sum_cgWeight {s : ℝ} (hs : 0 < s) {n : ℕ} (hn : 1 ≤ n) :
    ∑ ζ ∈ cgNodes s n, cgWeight s n ζ = (Real.Gamma s : ℂ)⁻¹ := by
  have h := dlmf_3_5_36 hs one_pos hn (q := 1) (by simp)
  rw [cgE, sub_eq_zero, cgI_poly hs one_pos] at h
  simp only [eval_one, mul_one] at h
  rw [← h, show (1 : ℂ[X]) = C 1 * X ^ 0 by simp, cgL_C_mul_X_pow, cgMu]
  simp

/-- At `t = 0` the sum 3.5.41 is `∑ₖ wₖ = 1` when the nodes have positive real part. -/
theorem lapApprox_zero {n : ℕ} (hn : 1 ≤ n) (hre : ∀ ζ ∈ cgNodes 1 n, 0 < ζ.re) :
    lapApprox n 0 = 1 := by
  have hs := sum_cgWeight one_pos hn
  rw [Real.Gamma_one, Complex.ofReal_one, inv_one] at hs
  rw [lapApprox]
  conv_rhs => rw [← hs]
  · refine sum_congr rfl fun ζ hζ => ?_
    have hr := hre ζ hζ
    have hζ0 : ζ ≠ 0 := by rintro rfl; simp at hr
    have harg := Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hr)
    have hsq : (ζ ^ 2) ^ (1 / 2 : ℂ) = ζ := by
      have := Complex.pow_cpow_nat_inv (n := 2) (x := ζ) two_ne_zero (by
        rw [abs_lt] at harg; push_cast; linarith [harg.1]) (by
        rw [abs_lt] at harg; push_cast; linarith [harg.2])
      simpa [one_div] using this
    simp only [Complex.ofReal_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      add_zero, hsq, div_self hζ0, mul_one]

end Azurite.DLMF
