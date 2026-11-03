/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/


import Azurite.DLMF.Chapter2.Section11Stokes
import Azurite.DLMF.Chapter2.Section7Formal

/-!
# DLMF §2.11(v): exponentially-improved expansions (continued)

The re-expansion of the remainders of the formal solutions 2.7.14 of a rank-one equation
(normalized so that `λ₂ − λ₁ = 1`) in terms of terminants, on the Riemann surface of `ln`
(`z = e^w`, `z^μ = e^{μw}`, `ze^{−πi} = e^{w − πi}`):

* **2.11.19** (`odeRem`): `R^{(j)}_n(z) = w_j(z) − e^{λ_jz} z^{μ_j} ∑_{s<n} a_{s,j}/z^s`.
* **2.11.20**, **2.11.21** (`reexpRem₁`, `reexpRem₂`, `dlmf_2_11_20`, `dlmf_2_11_21`): these
  define `R^{(1)}_{m,n}` and `R^{(2)}_{m,n}` (the factor `(−1)^{n−1}` is written `(−1)^{n+1}`).
* **2.11.22**, **2.11.23** in general: DEFERRED. They rest on the solutions `w_j` of 2.7.14–2.7.16
  and the Stokes multipliers of 2.7.17, whose existence is deferred in §2.7(ii)
  (Olde Daalhuis and Olver, 1994).

**The analytic core** is proved in general: the terminant is exponentially improved *uniformly up
to and on the Stokes lines*. `terminant_uniform`: `F_{ρ+α}(ρe^{iθ}) = O(e^{−ρ}|e^{−z}|)`, that is
`O(e^{−|z|−z})`, uniformly for `|θ| ≤ π` and `|α| ≤ A`. `terminant_bounded_beyond`: it is
`O(1)` for `π ≤ |θ| ≤ 3π`. The saddle point `u = 1` of the rotated integral (`Jint`) and the pole
`u = −e^{iθ}` coalesce as `θ → ±π`. `norm_Jint_le` splits at `|u − 1| = ρ^{−1/2}`, with three
ingredients:
* the pole is removed near `u = 1` by subtracting `e^{−ρ}/(e^{iθ} + u)`, whose integral is a
  bounded logarithm (`norm_integral_inv_cexp_add_le`);
* `|e^{iθ} + u| ≥ |u − 1|` (`abs_sub_one_le_norm_cexp_add`) controls the rest;
* a sharp Laplace bound `Γ(ρ + m)ρ^{−ρ−m} = O(e^{−ρ}ρ^{−1/2})` (`gMom_zero_le_sqrt`, Chebyshev's
  inequality with the second moment).

The closed sector follows by continuity, and the region beyond follows by the connection formulas
`terminant_add_two_pi_I`, `terminant_sub_two_pi_I`.

**Example: the incomplete gamma function.** `w″ + (1 + p/z)w′ = 0` (`incGammaFc`) has
* characteristic roots `λ₁ = −1`, `λ₂ = 0` (`incGamma_charRoots`);
* `μ₁ = −p`, `μ₂ = 0` (`incGamma_mu`);
* coefficients `a_{s,1} = (−1)^s(p)_s` and `a_{s,2} = δ_{s0}` (`incGamma_coeff₁`,
  `incGamma_coeff₂`, from the recursion 2.7.11);
* solutions `w₁ = Γ(1 − p, z) = eiP p (ln z)` (`incGamma_isODESolution`, with 2.7.14 in the
  sector 2.7.15, `incGamma_dlmf_2_7_14`) and `w₂ = 1`;
* Stokes multipliers `C₁ = 2πie^{−πip}/Γ(p)` and `C₂ = 0` (2.7.17, `incGamma_dlmf_2_7_17`).

Here `R^{(1)}_n = (−1)^n(2π/Γ(p))F_{n+p}(z)` (`incGamma_odeRem`, from 2.11.10). Hence
`R^{(1)}_{m,n} = 0` for `m ≥ 1` and `R^{(1)}_{0,n} = C₁F_{n+p}(z)` (`incGamma_reexpRem₁`, which
checks the constants of 2.11.20). **2.11.22** then holds as stated (`incGamma_dlmf_2_11_22`), and
**2.11.21 and 2.11.23** hold with `R^{(2)}_{m,n} = 0` (`incGamma_dlmf_2_11_23`).

The remarks on resurgence, hyperasymptotics, Borel transforms and the literature are not
formalized.
-/

open Filter Topology Set MeasureTheory Complex
open scoped Real Interval

namespace Azurite.DLMF

/-! ### A uniform bound for the terminant up to the Stokes line -/

theorem norm_cexp_add_sq (θ u : ℝ) :
    ‖cexp (θ * I) + u‖ ^ 2 = u ^ 2 + 2 * u * Real.cos θ + 1 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp only [Complex.add_re, Complex.add_im, Complex.exp_ofReal_mul_I_re,
    Complex.exp_ofReal_mul_I_im, Complex.ofReal_re, Complex.ofReal_im, add_zero]
  linear_combination Real.sin_sq_add_cos_sq θ

/-- `|e^{iθ} + u| ≥ |u − 1|` for `u ≥ 0`: the pole `u = −e^{iθ}` is never nearer to a point
of the positive axis than `u = 1` is. -/
theorem abs_sub_one_le_norm_cexp_add (θ : ℝ) {u : ℝ} (hu : 0 ≤ u) :
    |u - 1| ≤ ‖cexp (θ * I) + u‖ := by
  refine (sq_le_sq₀ (abs_nonneg _) (norm_nonneg _)).mp ?_
  rw [sq_abs, norm_cexp_add_sq]
  nlinarith [Real.neg_one_le_cos θ]

theorem exists_pos_le_norm_cexp_add {θ : ℝ} (hθ : |θ| < π) :
    ∃ m : ℝ, 0 < m ∧ ∀ u : ℝ, 0 ≤ u → m ≤ ‖cexp (θ * I) + u‖ := by
  by_cases hc : 0 ≤ Real.cos θ
  · refine ⟨1, one_pos, fun u hu => (sq_le_sq₀ zero_le_one (norm_nonneg _)).mp ?_⟩
    rw [norm_cexp_add_sq]; nlinarith
  · have hs : Real.sin θ ≠ 0 := by
      intro h0
      have hθ0 : θ = 0 := (Real.sin_eq_zero_iff_of_lt_of_lt (by rw [abs_lt] at hθ; linarith)
        (by rw [abs_lt] at hθ; linarith)).mp h0
      exact hc (by rw [hθ0, Real.cos_zero]; norm_num)
    refine ⟨|Real.sin θ|, abs_pos.mpr hs, fun u _ => ?_⟩
    calc |Real.sin θ| = |(cexp (θ * I) + u).im| := by simp [Complex.exp_ofReal_mul_I_im]
      _ ≤ _ := Complex.abs_im_le_norm _

theorem rpow_le_two_mul_two_pow {u a : ℝ} (hu1 : 1 / 2 ≤ u) (hu2 : u ≤ 2) {M : ℕ}
    (ha : |a| ≤ M) : u ^ a ≤ 2 * 2 ^ M := by
  have hu : 0 < u := by linarith
  have h := rpow_le_pow_add_pow hu ha
  have h1 : u ^ (M : ℝ) ≤ 2 ^ M := by
    rw [Real.rpow_natCast]; exact pow_le_pow_left₀ hu.le hu2 M
  have h2 : u ^ (-(M : ℝ)) ≤ 2 ^ M := by
    rw [Real.rpow_neg hu.le, Real.rpow_natCast, ← inv_pow]
    refine pow_le_pow_left₀ (by positivity) ?_ M
    rw [inv_le_comm₀ hu two_pos]
    linarith [show (2 : ℝ)⁻¹ = 1 / 2 by norm_num]
  linarith

theorem exp_neg_mul_rpow_le {ρ u : ℝ} (hρ : 0 ≤ ρ) (hu : 0 < u) :
    Real.exp (-(ρ * u)) * u ^ ρ ≤ Real.exp (-ρ) := by
  rw [Real.rpow_def_of_pos hu, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have := Real.log_le_sub_one_of_pos hu
  nlinarith

theorem norm_cexp_mul_cpow {ρ u : ℝ} (hu : 0 < u) (q : ℂ) :
    ‖cexp (-(ρ * u)) * (u : ℂ) ^ q‖ = Real.exp (-(ρ * u)) * u ^ q.re := by
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hu, Complex.norm_exp]
  congr 2
  simp

theorem integrableOn_Jint {ρ θ : ℝ} (hρ : 0 < ρ) (hθ : |θ| < π) {q : ℂ} (hq : 0 < q.re) :
    IntegrableOn (fun u : ℝ => cexp (-(ρ * u)) * (u : ℂ) ^ (q - 1) / (cexp (θ * I) + u))
      (Ioi 0) := by
  obtain ⟨m, hm, hmle⟩ := exists_pos_le_norm_cexp_add hθ
  have hb : IntegrableOn (fun u : ℝ => m⁻¹ * (Real.exp (-(ρ * u)) * u ^ (q.re - 1))) (Ioi 0) :=
    (integrableOn_rpow_exp hρ hq).const_mul _
  refine hb.mono' ?_ ?_
  · exact Measurable.aestronglyMeasurable (by fun_prop)
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun u hu => ?_)
    have hu0 : (0 : ℝ) < u := hu
    have hX : 0 ≤ Real.exp (-(ρ * u)) * u ^ (q.re - 1) := by positivity
    rw [norm_div, norm_cexp_mul_cpow hu0, show (q - 1).re = q.re - 1 by simp]
    calc _ ≤ Real.exp (-(ρ * u)) * u ^ (q.re - 1) / m :=
          div_le_div_of_nonneg_left hX hm (hmle u hu0.le)
      _ = _ := by ring

/-- `Γ(ρ + m)ρ^{−ρ−m} = O(e^{−ρ}ρ^{−1/2})`, uniformly for `|m| ≤ A` (Chebyshev's inequality with
the second moment `μ₂ = O(μ₀/ρ)` of `gMom_bound`). -/
theorem gMom_zero_le_sqrt (A : ℝ) : ∃ K ρ₀ : ℝ, 0 ≤ K ∧ A + 1 ≤ ρ₀ ∧
    ∀ ρ : ℝ, ρ₀ ≤ ρ → ∀ m : ℝ, |m| ≤ A → gMom ρ m 0 ≤ K * Real.exp (-ρ) / Real.sqrt ρ := by
  obtain ⟨C, hC0, hC⟩ := gMom_bound A 2
  set C' := C + 1 with hC'
  have hC'0 : 0 < C' := by rw [hC']; linarith
  set M : ℕ := ⌈A⌉₊ + 1 with hM
  have hMA : A + 1 ≤ (M : ℝ) := by rw [hM]; push_cast; linarith [Nat.le_ceil A]
  refine ⟨16 * 2 ^ M * Real.sqrt C', max (A + 1) (16 * C'), by positivity, le_max_left _ _,
    fun ρ hρ m hm => ?_⟩
  have hρA : A + 1 ≤ ρ := le_trans (le_max_left _ _) hρ
  have hρC : 16 * C' ≤ ρ := le_trans (le_max_right _ _) hρ
  have hρ0 : 0 < ρ := by linarith
  have hρ1 : 1 ≤ ρ := by linarith
  have hρm : 0 < ρ + m := by rw [abs_le] at hm; linarith
  set sρ := Real.sqrt ρ
  have hsρ : 0 < sρ := Real.sqrt_pos.mpr hρ0
  have hsρ2 : sρ ^ 2 = ρ := Real.sq_sqrt hρ0.le
  set sC := Real.sqrt C'
  have hsC : 0 < sC := Real.sqrt_pos.mpr hC'0
  have hsC2 : sC ^ 2 = C' := Real.sq_sqrt hC'0.le
  set t := 2 * sC / sρ
  have ht0 : 0 < t := by positivity
  have ht2 : t ^ 2 * ρ = 4 * C' := by
    rw [div_pow, mul_pow, hsC2, ← hsρ2]; field_simp; ring
  have ht : t ≤ 1 / 2 := by
    have h4 : t ^ 2 ≤ (1 / 2) ^ 2 := by nlinarith
    exact (sq_le_sq₀ ht0.le (by norm_num)).mp h4
  have hts : t * sρ = 2 * sC := by simp only [t]; field_simp
  set F : ℝ → ℝ := fun u => Real.exp (-(ρ * u)) * u ^ (ρ + m - 1) * (u - 1) ^ 0
  set T := Icc (1 - t) (1 + t)
  have hint := integrableOn_gMom hρ0 hρm 0
  have hTsub : T ⊆ Ioi 0 := fun u hu => by
    simp only [T, mem_Icc] at hu; show (0 : ℝ) < u; linarith [hu.1]
  have hsplit := integral_inter_add_sdiff (μ := volume) (s := Ioi (0 : ℝ))
    (measurableSet_Icc : MeasurableSet T) hint
  rw [inter_eq_right.mpr hTsub] at hsplit
  -- near `u = 1`
  have hnear : ∫ u in T, F u ≤ 2 * t * (Real.exp (-ρ) * (2 * 2 ^ M)) := by
    have hconst : IntegrableOn (fun _ : ℝ => Real.exp (-ρ) * (2 * 2 ^ M)) T :=
      continuousOn_const.integrableOn_Icc
    calc ∫ u in T, F u ≤ ∫ u in T, Real.exp (-ρ) * (2 * 2 ^ M) :=
          setIntegral_mono_on (hint.mono_set hTsub) hconst measurableSet_Icc fun u hu => ?_
      _ = _ := by
          rw [setIntegral_const]
          simp only [T, measureReal_def, Real.volume_Icc]
          rw [ENNReal.toReal_ofReal (by linarith), smul_eq_mul]
          ring
    have hu1 : 1 / 2 ≤ u := by linarith [hu.1]
    have hu2 : u ≤ 2 := by linarith [hu.2]
    have hu0 : 0 < u := by linarith
    have hmM : |m - 1| ≤ M := by
      rw [abs_le] at hm ⊢; constructor <;> linarith
    simp only [F, pow_zero, mul_one]
    rw [show ρ + m - 1 = ρ + (m - 1) by ring, Real.rpow_add hu0, ← mul_assoc]
    exact mul_le_mul (exp_neg_mul_rpow_le hρ0.le hu0) (rpow_le_two_mul_two_pow hu1 hu2 hmM)
      (by positivity) (by positivity)
  -- away from `u = 1`
  have hfar : ∫ u in Ioi 0 \ T, F u ≤ gMom ρ m 0 / 4 := by
    have hint2' := integrableOn_gMom hρ0 hρm 2
    have hint2 : IntegrableOn
        (fun u : ℝ => Real.exp (-(ρ * u)) * u ^ (ρ + m - 1) * (u - 1) ^ 2 / t ^ 2) (Ioi 0) :=
      Integrable.div_const hint2' _
    calc ∫ u in Ioi 0 \ T, F u ≤ ∫ u in Ioi 0 \ T,
          Real.exp (-(ρ * u)) * u ^ (ρ + m - 1) * (u - 1) ^ 2 / t ^ 2 :=
          setIntegral_mono_on (hint.mono_set sdiff_subset)
            (hint2.mono_set sdiff_subset)
            (measurableSet_Ioi.diff measurableSet_Icc) fun u hu => ?_
      _ ≤ ∫ u in Ioi 0, Real.exp (-(ρ * u)) * u ^ (ρ + m - 1) * (u - 1) ^ 2 / t ^ 2 :=
          setIntegral_mono_set hint2
            ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun u hu => by
              have : (0 : ℝ) < u := hu
              positivity))
            sdiff_subset.eventuallyLE
      _ = gMom ρ m 2 / t ^ 2 := by rw [integral_div]; rfl
      _ ≤ gMom ρ m 0 / 4 := ?_
    · obtain ⟨hu0, huT⟩ := hu
      have hu0' : (0 : ℝ) < u := hu0
      have hlt : t ^ 2 ≤ (u - 1) ^ 2 := by
        simp only [T, mem_Icc, not_and_or, not_le] at huT
        rcases huT with h | h <;> nlinarith
      simp only [F, pow_zero, mul_one]
      rw [mul_div_assoc]
      have hX : 0 ≤ Real.exp (-(ρ * u)) * u ^ (ρ + m - 1) := by positivity
      have h1 : 1 ≤ (u - 1) ^ 2 / t ^ 2 := by rw [le_div_iff₀ (by positivity)]; linarith
      exact le_mul_of_one_le_right hX h1
    · have h := hC ρ hρ1 m hm hρm
      norm_num at h
      have hμ0 : 0 ≤ gMom ρ m 0 := gMom_nonneg_zero
      have h2 : gMom ρ m 2 * ρ ≤ C' * gMom ρ m 0 := by
        have h' : gMom ρ m 2 ≤ C / ρ * gMom ρ m 0 := (le_abs_self _).trans h
        have h'' : gMom ρ m 2 * ρ ≤ C * gMom ρ m 0 := by
          calc gMom ρ m 2 * ρ ≤ C / ρ * gMom ρ m 0 * ρ := mul_le_mul_of_nonneg_right h' hρ0.le
            _ = C * gMom ρ m 0 := by field_simp
        rw [hC']; nlinarith
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      by_contra hcon
      push Not at hcon
      have e : gMom ρ m 0 * t ^ 2 * ρ = 4 * C' * gMom ρ m 0 := by
        rw [mul_assoc, ht2]; ring
      nlinarith [mul_lt_mul_of_pos_right hcon hρ0]
  have hμ : gMom ρ m 0 = (∫ u in T, F u) + ∫ u in Ioi 0 \ T, F u := hsplit.symm
  have key : gMom ρ m 0 ≤ 2 * t * (Real.exp (-ρ) * (2 * 2 ^ M)) + gMom ρ m 0 / 4 :=
    hμ.le.trans (add_le_add hnear hfar)
  rw [le_div_iff₀ hsρ]
  have h3 : 2 * t * (Real.exp (-ρ) * (2 * 2 ^ M)) * sρ = 8 * 2 ^ M * sC * Real.exp (-ρ) := by
    rw [show 2 * t * (Real.exp (-ρ) * (2 * 2 ^ M)) * sρ =
      4 * (t * sρ) * Real.exp (-ρ) * 2 ^ M by ring, hts]; ring
  have hP : 0 ≤ 2 ^ M * sC * Real.exp (-ρ) := by positivity
  have := mul_le_mul_of_nonneg_right key hsρ.le
  nlinarith

/-- `|∫_{1−δ}^{1+δ} du/(e^{iθ} + u)| ≤ ln 3 + 2π` for `|θ| < π`, `0 < δ ≤ 1/2`, uniformly as the
pole `−e^{iθ}` approaches `u = 1` (by the logarithm). -/
theorem norm_integral_inv_cexp_add_le {θ : ℝ} (hθ : |θ| < π) {δ : ℝ} (hδ0 : 0 < δ)
    (hδ : δ ≤ 1 / 2) :
    ‖∫ u in (1 - δ)..(1 + δ), (cexp (θ * I) + u)⁻¹‖ ≤ Real.log 3 + 2 * π := by
  set c := cexp (θ * I)
  have hslit : ∀ u : ℝ, 0 < u → c + u ∈ slitPlane := by
    intro u hu
    rw [Complex.mem_slitPlane_iff]
    by_cases hs : Real.sin θ = 0
    · left
      have hθ0 : θ = 0 := (Real.sin_eq_zero_iff_of_lt_of_lt (by rw [abs_lt] at hθ; linarith)
        (by rw [abs_lt] at hθ; linarith)).mp hs
      simp [c, hθ0]; linarith
    · right; simpa [c, Complex.exp_ofReal_mul_I_im] using hs
  have hab : 1 - δ ≤ 1 + δ := by linarith
  have hpos : ∀ u ∈ uIcc (1 - δ) (1 + δ), 0 < u := fun u hu => by
    rw [uIcc_of_le hab] at hu; linarith [hu.1]
  have hFTC : ∫ u in (1 - δ)..(1 + δ), (c + u)⁻¹ =
      Complex.log (c + ((1 + δ : ℝ) : ℂ)) - Complex.log (c + ((1 - δ : ℝ) : ℂ)) := by
    refine intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun u : ℝ => Complex.log (c + u))
      (fun u hu => ?_) ?_
    · have h := (((hasDerivAt_id' u).ofReal_comp).const_add c).clog_real (hslit u (hpos u hu))
      convert h using 1
      simp
    · refine ContinuousOn.intervalIntegrable fun u hu => ?_
      exact ((continuous_const.add Complex.continuous_ofReal).continuousAt.inv₀
        (slitPlane_ne_zero (hslit u (hpos u hu)))).continuousWithinAt
  set z₁ := c + ((1 + δ : ℝ) : ℂ)
  set z₂ := c + ((1 - δ : ℝ) : ℂ)
  have hz₂ : 0 < ‖z₂‖ := norm_pos_iff.mpr (slitPlane_ne_zero (hslit _ (by linarith)))
  have hsq₁ := norm_cexp_add_sq θ (1 + δ)
  have hsq₂ := norm_cexp_add_sq θ (1 - δ)
  have hc1 := Real.neg_one_le_cos θ
  have h21 : ‖z₂‖ ≤ ‖z₁‖ := by
    refine (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp ?_
    rw [hsq₁, hsq₂]; nlinarith
  have h13 : ‖z₁‖ ≤ 3 * ‖z₂‖ := by
    refine (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp ?_
    rw [mul_pow, hsq₁, hsq₂]
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 1 + Real.cos θ)
      (by linarith : (0 : ℝ) ≤ 1 / 2 - δ)]
  have hre : |(Complex.log z₁ - Complex.log z₂).re| ≤ Real.log 3 := by
    rw [Complex.sub_re, Complex.log_re, Complex.log_re, abs_le]
    have l1 := Real.log_le_log hz₂ h21
    have l2 := Real.log_le_log (hz₂.trans_le h21) h13
    rw [Real.log_mul (by norm_num) hz₂.ne'] at l2
    have l3 : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
    constructor <;> linarith
  have him : |(Complex.log z₁ - Complex.log z₂).im| ≤ 2 * π := by
    rw [Complex.sub_im, Complex.log_im, Complex.log_im, abs_le]
    have := Complex.neg_pi_lt_arg z₁
    have := Complex.neg_pi_lt_arg z₂
    have := Complex.arg_le_pi z₁
    have := Complex.arg_le_pi z₂
    constructor <;> linarith
  rw [hFTC]
  exact (Complex.norm_le_abs_re_add_abs_im _).trans (add_le_add hre him)

set_option maxHeartbeats 400000 in
/-- **The integral `J` is `O(e^{−ρ})` uniformly up to the Stokes line**: for `|θ| < π`,
`|α| ≤ A`, `|∫_0^∞ e^{−ρu} u^{ρ+α−1}/(e^{iθ} + u) du| ≤ C e^{−ρ}`. The saddle point `u = 1` and
the pole `u = −e^{iθ}` coalesce as `θ → ±π`; the integral is split at `|u − 1| = ρ^{−1/2}`, the
pole is removed near `u = 1` by subtracting `e^{−ρ}/(e^{iθ} + u)` (`norm_integral_inv_cexp_add_le`),
and `|e^{iθ} + u| ≥ |u − 1|` (`abs_sub_one_le_norm_cexp_add`) controls the rest. -/
theorem norm_Jint_le (A : ℝ) : ∃ C ρ₀ : ℝ, A + 1 ≤ ρ₀ ∧ ∀ ρ : ℝ, ρ₀ ≤ ρ →
    ∀ θ : ℝ, |θ| < π → ∀ α : ℂ, ‖α‖ ≤ A → ‖Jint ρ θ α‖ ≤ C * Real.exp (-ρ) := by
  obtain ⟨K, ρ₁, hK, hρ₁, hμ⟩ := gMom_zero_le_sqrt A
  set M : ℕ := ⌈A⌉₊ + 2 with hM
  have hMA : A + 2 ≤ (M : ℝ) := by rw [hM]; push_cast; linarith [Nat.le_ceil A]
  refine ⟨4 * 2 ^ M * (A + 3) + (Real.log 3 + 2 * π) + K, max ρ₁ 4,
    le_trans hρ₁ (le_max_left _ _), fun ρ hρ θ hθ α hα => ?_⟩
  have hρρ₁ : ρ₁ ≤ ρ := le_trans (le_max_left _ _) hρ
  have hρ4 : 4 ≤ ρ := le_trans (le_max_right _ _) hρ
  have hρA : A + 1 ≤ ρ := le_trans hρ₁ hρρ₁
  have hρ0 : 0 < ρ := by linarith
  have hA0 : 0 ≤ A := (norm_nonneg α).trans hα
  have hαre : |α.re| ≤ A := (Complex.abs_re_le_norm α).trans hα
  have hαre' := abs_le.mp hαre
  set q : ℂ := (ρ : ℂ) + α with hqdef
  have hq : 0 < q.re := by simp only [q, Complex.add_re, Complex.ofReal_re]; linarith
  have hqre : (q - 1).re = ρ + α.re - 1 := by simp [q]
  set sρ := Real.sqrt ρ
  have hsρ : 0 < sρ := Real.sqrt_pos.mpr hρ0
  have hsρ2 : sρ ^ 2 = ρ := Real.sq_sqrt hρ0.le
  have hsρ_ge : 2 ≤ sρ := by
    have : Real.sqrt 4 = 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    rw [← this]; exact Real.sqrt_le_sqrt hρ4
  set δ := 1 / sρ
  have hδ0 : 0 < δ := by positivity
  have hδ : δ ≤ 1 / 2 := by
    simp only [δ]; rw [div_le_div_iff₀ hsρ two_pos]; linarith
  have hρδ : ρ * δ ^ 2 = 1 := by rw [← hsρ2]; simp only [δ]; field_simp
  have hsδ : sρ * δ = 1 := by simp only [δ]; field_simp
  set c := cexp (θ * I)
  set φ : ℝ → ℂ := fun u => cexp (-(ρ * u)) * (u : ℂ) ^ (q - 1)
  set f : ℝ → ℂ := fun u => φ u / (c + u)
  have hJ : Jint ρ θ α = ∫ u in Ioi 0, f u := rfl
  have hcu : ∀ u : ℝ, 0 ≤ u → 0 < ‖c + u‖ := by
    obtain ⟨m, hm, hmle⟩ := exists_pos_le_norm_cexp_add hθ
    exact fun u hu => hm.trans_le (hmle u hu)
  have hcu' : ∀ u : ℝ, 0 ≤ u → c + u ≠ 0 := fun u hu => norm_pos_iff.mp (hcu u hu)
  have hfi : IntegrableOn f (Ioi 0) := integrableOn_Jint hρ0 hθ hq
  set T := Icc (1 - δ) (1 + δ)
  have hTsub : T ⊆ Ioi 0 := fun u hu => by
    simp only [T, mem_Icc] at hu; show (0 : ℝ) < u; linarith [hu.1]
  have hab : 1 - δ ≤ 1 + δ := by linarith
  have hsplit := integral_inter_add_sdiff (μ := volume) (s := Ioi (0 : ℝ))
    (measurableSet_Icc : MeasurableSet T) hfi
  rw [inter_eq_right.mpr hTsub] at hsplit
  rw [hJ, ← hsplit, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab]
  -- continuity on `T`
  have hφc : ContinuousOn φ T := fun u hu => by
    have hu0 : (0 : ℝ) < u := hTsub hu
    have h1 : ContinuousAt (fun u : ℝ => cexp (-(ρ * u))) u := by fun_prop
    exact (h1.mul (continuousAt_ofReal_cpow_const u (q - 1) (Or.inr hu0.ne'))).continuousWithinAt
  have hgc : ContinuousOn (fun u : ℝ => (c + u)⁻¹) T := fun u hu =>
    ((continuous_const.add Complex.continuous_ofReal).continuousAt.inv₀
      (hcu' u (hTsub hu).le)).continuousWithinAt
  have hfT : IntervalIntegrable f volume (1 - δ) (1 + δ) := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le hab]
    exact hφc.div (fun u hu => (continuous_const.add Complex.continuous_ofReal).continuousAt
      |>.continuousWithinAt) fun u hu => hcu' u (hTsub hu).le
  have hgT : IntervalIntegrable (fun u : ℝ => (c + u)⁻¹) volume (1 - δ) (1 + δ) := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le hab]; exact hgc
  set E : ℂ := ((Real.exp (-ρ) : ℝ) : ℂ)
  have hφ1 : φ 1 = E := by simp [φ, E]
  have hsplit2 : (∫ u in (1 - δ)..(1 + δ), f u) =
      (∫ u in (1 - δ)..(1 + δ), (f u - E * (c + u)⁻¹)) +
        E * ∫ u in (1 - δ)..(1 + δ), (c + u)⁻¹ := by
    rw [← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_add (hfT.sub (hgT.const_mul E)) (hgT.const_mul E)]
    exact intervalIntegral.integral_congr fun u _ => by ring
  rw [hsplit2]
  -- (a) the regular part near `u = 1`, by the mean value inequality
  set L := Real.exp (-ρ) * (2 * 2 ^ M) * (2 * (ρ * δ + A + 1))
  have hL0 : 0 ≤ L := by positivity
  have hderiv : ∀ x ∈ T, HasDerivWithinAt φ (φ x * (-(ρ : ℂ) + (q - 1) / x)) T x := by
    intro x hx
    have hx0 : (0 : ℝ) < x := hTsub hx
    have hxC : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx0.ne'
    refine HasDerivAt.hasDerivWithinAt ?_
    have h1 : HasDerivAt (fun z : ℂ => cexp (-(ρ * z))) (cexp (-(ρ * x)) * (-(ρ : ℂ))) x := by
      have h := ((hasDerivAt_id (x : ℂ)).const_mul (ρ : ℂ)).neg.cexp
      convert h using 1 <;> simp
    have h2 : HasDerivAt (fun z : ℂ => z ^ (q - 1)) ((q - 1) * (x : ℂ) ^ (q - 1 - 1)) x :=
      (Complex.hasStrictDerivAt_cpow_const (Complex.ofReal_mem_slitPlane.mpr hx0)).hasDerivAt
    have h3 := (h1.mul h2).comp_ofReal
    convert h3 using 1
    rw [Complex.cpow_sub (q - 1) 1 hxC, Complex.cpow_one]
    simp only [φ]
    field_simp
  have hbound : ∀ x ∈ T, ‖φ x * (-(ρ : ℂ) + (q - 1) / x)‖ ≤ L := by
    intro x hx
    have hx0 : (0 : ℝ) < x := hTsub hx
    have hx1 : 1 / 2 ≤ x := by linarith [hx.1]
    have hx2 : x ≤ 2 := by linarith [hx.2]
    have hxd : |x - 1| ≤ δ := abs_le.mpr ⟨by linarith [hx.1], by linarith [hx.2]⟩
    rw [norm_mul]
    have hn1 : ‖φ x‖ ≤ Real.exp (-ρ) * (2 * 2 ^ M) := by
      simp only [φ]
      rw [norm_cexp_mul_cpow hx0, hqre, show ρ + α.re - 1 = ρ + (α.re - 1) by ring,
        Real.rpow_add hx0, ← mul_assoc]
      have hM' : |α.re - 1| ≤ M := abs_le.mpr ⟨by linarith, by linarith⟩
      exact mul_le_mul (exp_neg_mul_rpow_le hρ0.le hx0) (rpow_le_two_mul_two_pow hx1 hx2 hM')
        (by positivity) (by positivity)
    have hn2 : ‖-(ρ : ℂ) + (q - 1) / x‖ ≤ 2 * (ρ * δ + A + 1) := by
      have hxC : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx0.ne'
      rw [show -(ρ : ℂ) + (q - 1) / x = (((ρ * (1 - x) : ℝ) : ℂ) + (α - 1)) / x by
        simp only [q]; field_simp; push_cast; ring, norm_div, Complex.norm_real,
        Real.norm_of_nonneg hx0.le, div_le_iff₀ hx0]
      have e1 : ‖(((ρ * (1 - x) : ℝ) : ℂ))‖ ≤ ρ * δ := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_pos hρ0, abs_sub_comm]
        exact mul_le_mul_of_nonneg_left hxd hρ0.le
      have e2 : ‖α - 1‖ ≤ A + 1 := (norm_sub_le _ _).trans (by rw [norm_one]; linarith)
      have := norm_add_le (((ρ * (1 - x) : ℝ) : ℂ)) (α - 1)
      have hρδ0 : 0 ≤ ρ * δ := by positivity
      nlinarith
    exact mul_le_mul hn1 hn2 (norm_nonneg _) (by positivity)
  have hmvt : ∀ u ∈ T, ‖φ u - φ 1‖ ≤ L * |u - 1| := fun u hu => by
    have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hderiv hbound (convex_Icc _ _)
      (⟨by linarith, by linarith⟩ : (1 : ℝ) ∈ T) hu
    rwa [Real.norm_eq_abs] at h
  have ha : ‖∫ u in (1 - δ)..(1 + δ), (f u - E * (c + u)⁻¹)‖ ≤ L * |(1 + δ) - (1 - δ)| := by
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun u hu => ?_
    rw [uIoc_of_le hab] at hu
    have huT : u ∈ T := ⟨hu.1.le, hu.2⟩
    have hu0 : (0 : ℝ) ≤ u := (hTsub huT).le
    have e : f u - E * (c + u)⁻¹ = (φ u - φ 1) / (c + u) := by
      simp only [f]; rw [hφ1]; field_simp
    rw [e, norm_div, div_le_iff₀ (hcu u hu0)]
    exact (hmvt u huT).trans (mul_le_mul_of_nonneg_left (abs_sub_one_le_norm_cexp_add θ hu0) hL0)
  have ha' : L * |(1 + δ) - (1 - δ)| ≤ 4 * 2 ^ M * (A + 3) * Real.exp (-ρ) := by
    rw [show (1 + δ) - (1 - δ) = 2 * δ by ring, abs_of_pos (by positivity)]
    have hP : 0 ≤ Real.exp (-ρ) * 2 ^ M := by positivity
    have e : L * (2 * δ) = 8 * (Real.exp (-ρ) * 2 ^ M) * (ρ * δ ^ 2 + (A + 1) * δ) := by
      simp only [L]; ring
    rw [e, hρδ]
    have : (A + 1) * δ ≤ (A + 1) / 2 := by nlinarith
    nlinarith
  -- (b) the pole part
  have hb : ‖E * ∫ u in (1 - δ)..(1 + δ), (c + u)⁻¹‖ ≤
      (Real.log 3 + 2 * π) * Real.exp (-ρ) := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le, mul_comm]
    exact mul_le_mul_of_nonneg_right (norm_integral_inv_cexp_add_le hθ hδ0 hδ)
      (Real.exp_pos _).le
  -- (c) away from `u = 1`
  have hc : ‖∫ u in Ioi 0 \ T, f u‖ ≤ K * Real.exp (-ρ) := by
    have hint0 := integrableOn_gMom hρ0 (m := α.re) (by linarith) 0
    have hfin : IntegrableOn (fun u => ‖f u‖) (Ioi 0) := hfi.norm
    have hint1 : IntegrableOn (fun u : ℝ =>
        sρ * (Real.exp (-(ρ * u)) * u ^ (ρ + α.re - 1) * (u - 1) ^ 0)) (Ioi 0) :=
      Integrable.const_mul hint0 _
    calc ‖∫ u in Ioi 0 \ T, f u‖ ≤ ∫ u in Ioi 0 \ T, ‖f u‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ u in Ioi 0 \ T, sρ * (Real.exp (-(ρ * u)) * u ^ (ρ + α.re - 1) * (u - 1) ^ 0) :=
          setIntegral_mono_on (hfin.mono_set sdiff_subset) (hint1.mono_set sdiff_subset)
            (measurableSet_Ioi.diff measurableSet_Icc) fun u hu => ?_
      _ ≤ ∫ u in Ioi 0, sρ * (Real.exp (-(ρ * u)) * u ^ (ρ + α.re - 1) * (u - 1) ^ 0) :=
          setIntegral_mono_set hint1
            ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun u hu => by
              have : (0 : ℝ) < u := hu
              positivity))
            sdiff_subset.eventuallyLE
      _ = sρ * gMom ρ α.re 0 := by rw [integral_const_mul]; rfl
      _ ≤ sρ * (K * Real.exp (-ρ) / sρ) :=
          mul_le_mul_of_nonneg_left (hμ ρ hρρ₁ α.re hαre) hsρ.le
      _ = K * Real.exp (-ρ) := by field_simp
    obtain ⟨hu0, huT⟩ := hu
    have hu0' : (0 : ℝ) < u := hu0
    have hdu : δ < |u - 1| := by
      simp only [T, mem_Icc, not_and_or, not_le] at huT
      rcases huT with h | h
      · rw [abs_of_neg (by linarith)]; linarith
      · rw [abs_of_pos (by linarith)]; linarith
    have hcδ : δ ≤ ‖c + u‖ := hdu.le.trans (abs_sub_one_le_norm_cexp_add θ hu0'.le)
    simp only [f, φ]
    rw [norm_div, norm_cexp_mul_cpow hu0', hqre, pow_zero, mul_one,
      div_le_iff₀ (hcu u hu0'.le)]
    have hX : 0 ≤ Real.exp (-(ρ * u)) * u ^ (ρ + α.re - 1) := by positivity
    have h1 : 1 ≤ sρ * ‖c + u‖ := by
      calc (1 : ℝ) = sρ * δ := hsδ.symm
        _ ≤ sρ * ‖c + u‖ := mul_le_mul_of_nonneg_left hcδ hsρ.le
    nlinarith
  calc _ ≤ ‖∫ u in (1 - δ)..(1 + δ), (f u - E * (c + u)⁻¹)‖ +
        ‖E * ∫ u in (1 - δ)..(1 + δ), (c + u)⁻¹‖ + ‖∫ u in Ioi 0 \ T, f u‖ :=
        (norm_add_le _ _).trans (add_le_add_left (norm_add_le _ _) _)
    _ ≤ _ := by nlinarith [ha.trans ha']

theorem terminant_eq_Jint {ρ θ : ℝ} (hρ : 0 < ρ) (hθ : |θ| < π) {α : ℂ}
    (hq : 0 < ((ρ : ℂ) + α).re) :
    terminant ((ρ : ℂ) + α) (polarW ρ θ) = cexp (-cexp (polarW ρ θ)) *
      cexp ((1 - ((ρ : ℂ) + α)) * (θ * I)) * Jint ρ θ α / (2 * π) := by
  rw [terminant, show Complex.Gamma ((ρ : ℂ) + α) / (2 * π) * eiP ((ρ : ℂ) + α) (polarW ρ θ) =
    Complex.Gamma ((ρ : ℂ) + α) * eiP ((ρ : ℂ) + α) (polarW ρ θ) / (2 * π) by ring,
    gamma_mul_eiP_rotated hq hρ hθ, cexp_polarW hρ]
  rfl

theorem norm_cexp_mul_I_mul_le (r : ℝ) {q : ℂ} {A : ℝ} (hq : |q.im| ≤ A) :
    ‖cexp (r * I * q)‖ ≤ Real.exp (|r| * A) := by
  rw [Complex.norm_exp]
  apply Real.exp_le_exp.mpr
  have e : ((r : ℂ) * I * q).re = -(r * q.im) := by simp [Complex.mul_re]
  rw [e]
  calc -(r * q.im) ≤ |r * q.im| := neg_le_abs _
    _ = |r| * |q.im| := abs_mul _ _
    _ ≤ |r| * A := mul_le_mul_of_nonneg_left hq (abs_nonneg _)

theorem exp_neg_mul_norm_cexp_polarW_le {ρ : ℝ} (hρ : 0 < ρ) (θ : ℝ) :
    Real.exp (-ρ) * ‖cexp (-cexp (polarW ρ θ))‖ ≤ 1 := by
  rw [cexp_polarW hρ, Complex.norm_exp, ← Real.exp_add, Real.exp_le_one_iff]
  have e : (-((ρ : ℂ) * cexp (θ * I))).re = -(ρ * Real.cos θ) := by
    simp [Complex.exp_ofReal_mul_I_re]
  rw [e]
  nlinarith [Real.neg_one_le_cos θ]

/-- **The terminant is `O(e^{−|z|−z})` uniformly in `|ph z| ≤ π`**: for `|α| ≤ A`,
`|F_{ρ+α}(ρe^{iθ})| ≤ C e^{−ρ}|e^{−z}|`, `ρ ≥ ρ₀`, including the Stokes lines `θ = ±π` (where
`|e^{−|z|−z}| = 1`); compare 2.11.15, by which `F ∼ ½ erfc(⋯)` there. -/
theorem terminant_uniform (A : ℝ) : ∃ C ρ₀ : ℝ, 0 ≤ C ∧ A + 1 ≤ ρ₀ ∧ ∀ ρ : ℝ, ρ₀ ≤ ρ →
    ∀ θ : ℝ, |θ| ≤ π → ∀ α : ℂ, ‖α‖ ≤ A →
      ‖terminant ((ρ : ℂ) + α) (polarW ρ θ)‖ ≤
        C * Real.exp (-ρ) * ‖cexp (-cexp (polarW ρ θ))‖ := by
  obtain ⟨C, ρ₀, hρ₀, hJ⟩ := norm_Jint_le A
  refine ⟨max C 0 * Real.exp (π * A) / (2 * π), ρ₀, by positivity, hρ₀,
    fun ρ hρ θ hθ α hα => ?_⟩
  have hA0 : 0 ≤ A := (norm_nonneg α).trans hα
  have hρ0 : 0 < ρ := by linarith
  have hq : 0 < ((ρ : ℂ) + α).re := by
    simp only [Complex.add_re, Complex.ofReal_re]
    linarith [Complex.abs_re_le_norm α, neg_abs_le α.re]
  set K := max C 0 * Real.exp (π * A) / (2 * π)
  have hstrict : ∀ θ : ℝ, |θ| < π → ‖terminant ((ρ : ℂ) + α) (polarW ρ θ)‖ ≤
      K * Real.exp (-ρ) * ‖cexp (-cexp (polarW ρ θ))‖ := by
    intro θ hθ
    have h1 : ‖cexp ((1 - ((ρ : ℂ) + α)) * (θ * I))‖ ≤ Real.exp (π * A) := by
      have h := norm_cexp_mul_I_mul_le θ (q := 1 - ((ρ : ℂ) + α)) (A := A)
        (by simpa using (Complex.abs_im_le_norm α).trans hα)
      rw [show (1 - ((ρ : ℂ) + α)) * (θ * I) = θ * I * (1 - ((ρ : ℂ) + α)) by ring]
      exact h.trans (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hθ.le hA0))
    have h2 : ‖Jint ρ θ α‖ ≤ max C 0 * Real.exp (-ρ) :=
      (hJ ρ hρ θ hθ α hα).trans (mul_le_mul_of_nonneg_right (le_max_left C 0) (Real.exp_pos _).le)
    have h2π : ‖(2 * π : ℂ)‖ = 2 * π := by
      rw [norm_mul, Complex.norm_two, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
    rw [terminant_eq_Jint hρ0 hθ hq, norm_div, norm_mul, norm_mul, h2π]
    calc ‖cexp (-cexp (polarW ρ θ))‖ * ‖cexp ((1 - ((ρ : ℂ) + α)) * (θ * I))‖ * ‖Jint ρ θ α‖ /
          (2 * π) ≤ ‖cexp (-cexp (polarW ρ θ))‖ * Real.exp (π * A) *
            (max C 0 * Real.exp (-ρ)) / (2 * π) :=
          div_le_div_of_nonneg_right (mul_le_mul (mul_le_mul_of_nonneg_left h1 (norm_nonneg _))
            h2 (norm_nonneg _) (by positivity)) (by positivity)
      _ = _ := by simp only [K]; ring
  -- the closed sector, by continuity
  have hpc : Continuous fun θ : ℝ => polarW ρ θ := by unfold polarW; fun_prop
  have hd : Differentiable ℂ (eiP ((ρ : ℂ) + α)) := fun w =>
    (hasDerivAt_eiP _ w).differentiableAt
  have hc1 : Continuous fun θ : ℝ => ‖terminant ((ρ : ℂ) + α) (polarW ρ θ)‖ := by
    unfold terminant
    exact (continuous_const.mul (hd.continuous.comp hpc)).norm
  have hc2 : Continuous fun θ : ℝ => K * Real.exp (-ρ) * ‖cexp (-cexp (polarW ρ θ))‖ :=
    continuous_const.mul (Complex.continuous_exp.comp (Complex.continuous_exp.comp hpc).neg).norm
  have hsub : Ioo (-π) π ⊆ {θ : ℝ | ‖terminant ((ρ : ℂ) + α) (polarW ρ θ)‖ ≤
      K * Real.exp (-ρ) * ‖cexp (-cexp (polarW ρ θ))‖} :=
    fun θ hθ => hstrict θ (abs_lt.mpr ⟨hθ.1, hθ.2⟩)
  have hcl := (isClosed_le hc1 hc2).closure_subset_iff.mpr hsub
  rw [closure_Ioo (by linarith [Real.pi_pos] : -π ≠ π)] at hcl
  exact hcl (abs_le.mp hθ)

/-- The connection formula of the terminant (from 8.19.18 / `eiC_eq_connConst`):
`F_q(ze^{2πi}) = e^{−2πiq}(F_q(z) + ie^{πiq})`. -/
theorem terminant_add_two_pi_I {q : ℂ} (hq : Complex.Gamma q ≠ 0) (w : ℂ) :
    terminant q (w + 2 * π * I) =
      cexp (-(2 * π * I * q)) * (terminant q w + I * cexp (π * I * q)) := by
  have h := eiC_eq q w
  rw [eiC_eq_connConst, connConst] at h
  have hinv := exp_two_pi_I_mul_neg q
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hΓ : Complex.Gamma q * (Complex.Gamma q)⁻¹ = 1 := mul_inv_cancel₀ hq
  have hπ' : (π : ℂ) * (π : ℂ)⁻¹ = 1 := mul_inv_cancel₀ hπ
  unfold terminant
  linear_combination (Complex.Gamma q / (2 * π) * cexp (-(2 * π * I * q))) * h -
    (Complex.Gamma q / (2 * π) * eiP q (w + 2 * π * I)) * hinv +
    (cexp (-(2 * π * I * q)) * I * cexp (π * I * q) * π * (π : ℂ)⁻¹) * hΓ +
    (cexp (-(2 * π * I * q)) * I * cexp (π * I * q)) * hπ'

/-- `F_q(ze^{−2πi}) = e^{2πiq}F_q(z) − ie^{πiq}`. -/
theorem terminant_sub_two_pi_I {q : ℂ} (hq : Complex.Gamma q ≠ 0) (w : ℂ) :
    terminant q (w - 2 * π * I) = cexp (2 * π * I * q) * terminant q w - I * cexp (π * I * q) := by
  have h := eiC_eq q (w - 2 * π * I)
  rw [eiC_eq_connConst, connConst, sub_add_cancel] at h
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hΓ : Complex.Gamma q * (Complex.Gamma q)⁻¹ = 1 := mul_inv_cancel₀ hq
  unfold terminant
  field_simp
  linear_combination (-(Complex.Gamma q)) * h - (2 * π * I * cexp (π * I * q)) * hΓ

/-- **Beyond the Stokes lines the terminant is `O(1)`**: uniformly for `π ≤ |θ| ≤ 3π`,
`|α| ≤ A` (from `terminant_uniform` and the connection formulas). -/
theorem terminant_bounded_beyond (A : ℝ) : ∃ C ρ₀ : ℝ, 0 ≤ C ∧ A + 1 ≤ ρ₀ ∧
    ∀ ρ : ℝ, ρ₀ ≤ ρ → ∀ θ : ℝ, π ≤ |θ| → |θ| ≤ 3 * π → ∀ α : ℂ, ‖α‖ ≤ A →
      ‖terminant ((ρ : ℂ) + α) (polarW ρ θ)‖ ≤ C := by
  obtain ⟨C, ρ₀, hC, hρ₀, hF⟩ := terminant_uniform A
  refine ⟨Real.exp (2 * π * A) * (C + Real.exp (π * A)), ρ₀, by positivity, hρ₀,
    fun ρ hρ θ hθ₁ hθ₂ α hα => ?_⟩
  have hA0 : 0 ≤ A := (norm_nonneg α).trans hα
  have hρ0 : 0 < ρ := by linarith
  set q : ℂ := (ρ : ℂ) + α
  have hqim : |q.im| ≤ A := by simpa [q] using (Complex.abs_im_le_norm α).trans hα
  have hq : Complex.Gamma q ≠ 0 := by
    refine Complex.Gamma_ne_zero_of_re_pos ?_
    simp only [q, Complex.add_re, Complex.ofReal_re]
    linarith [Complex.abs_re_le_norm α, neg_abs_le α.re]
  have hπ := Real.pi_pos
  have hB : ∀ θ' : ℝ, |θ'| ≤ π → ‖terminant q (polarW ρ θ')‖ ≤ C := fun θ' h' => by
    have := hF ρ hρ θ' h' α hα
    have h1 := exp_neg_mul_norm_cexp_polarW_le hρ0 θ'
    calc _ ≤ C * Real.exp (-ρ) * ‖cexp (-cexp (polarW ρ θ'))‖ := this
      _ = C * (Real.exp (-ρ) * ‖cexp (-cexp (polarW ρ θ'))‖) := by ring
      _ ≤ C * 1 := mul_le_mul_of_nonneg_left h1 hC
      _ = C := mul_one C
  have e1 : ‖cexp (π * I * q)‖ ≤ Real.exp (π * A) := by
    have := norm_cexp_mul_I_mul_le π hqim; rwa [abs_of_pos hπ] at this
  have e2 : ‖cexp (-(2 * π * I * q))‖ ≤ Real.exp (2 * π * A) := by
    have := norm_cexp_mul_I_mul_le (-(2 * π)) hqim
    rw [abs_neg, abs_of_pos (by positivity)] at this
    convert this using 3; push_cast; ring
  have e3 : ‖cexp (2 * π * I * q)‖ ≤ Real.exp (2 * π * A) := by
    have := norm_cexp_mul_I_mul_le (2 * π) hqim
    rw [abs_of_pos (by positivity)] at this
    convert this using 3; push_cast; ring
  have hexp : 1 ≤ Real.exp (2 * π * A) := Real.one_le_exp (by positivity)
  rcases le_abs'.mp hθ₁ with hθ | hθ
  · -- `θ ≤ −π`: `z = z' e^{−2πi}`
    have hw : polarW ρ θ = polarW ρ (θ + 2 * π) - 2 * π * I := by
      simp only [polarW]; push_cast; ring
    have h' : |θ + 2 * π| ≤ π := abs_le.mpr ⟨by rw [abs_le] at hθ₂; linarith, by linarith⟩
    rw [hw, terminant_sub_two_pi_I hq]
    calc _ ≤ ‖cexp (2 * π * I * q) * terminant q (polarW ρ (θ + 2 * π))‖ +
          ‖I * cexp (π * I * q)‖ := norm_sub_le _ _
      _ ≤ Real.exp (2 * π * A) * C + Real.exp (π * A) := by
          rw [norm_mul, norm_mul, Complex.norm_I, one_mul]
          exact add_le_add (mul_le_mul e3 (hB _ h') (norm_nonneg _) (by positivity)) e1
      _ ≤ _ := by nlinarith [Real.exp_pos (π * A)]
  · -- `θ ≥ π`: `z = z' e^{2πi}`
    have hw : polarW ρ θ = polarW ρ (θ - 2 * π) + 2 * π * I := by
      simp only [polarW]; push_cast; ring
    have h' : |θ - 2 * π| ≤ π := abs_le.mpr ⟨by linarith, by rw [abs_le] at hθ₂; linarith⟩
    rw [hw, terminant_add_two_pi_I hq, norm_mul]
    refine mul_le_mul e2 ((norm_add_le _ _).trans (add_le_add (hB _ h') ?_)) (norm_nonneg _)
      (by positivity)
    rw [norm_mul, Complex.norm_I, one_mul]; exact e1

/-! ### The re-expansions 2.11.19–2.11.21 -/

/-- **DLMF 2.11.19**: the remainder `R_n(z) = w(z) − e^{λz} z^μ ∑_{s<n} a_s/z^s` of a solution
`w`, on the Riemann surface of `ln` (`z = e^w`, `z^μ = e^{μw}`). -/
noncomputable def odeRem (lam mu : ℂ) (a : ℕ → ℂ) (W : ℂ → ℂ) (n : ℕ) (w : ℂ) : ℂ :=
  W w - cexp (lam * cexp w) * cexp (mu * w) * ∑ s ∈ Finset.range n, a s / cexp w ^ s

/-- The prefactor `(−1)^{n−1} i e^{(μ₂−μ₁)πi} e^{λ₂z} z^{μ₂}` of 2.11.20
(`(−1)^{n−1} = (−1)^{n+1}`). -/
noncomputable def reexpPref₁ (lam₂ mu₁ mu₂ : ℂ) (n : ℕ) (w : ℂ) : ℂ :=
  (-1) ^ (n + 1) * I * cexp ((mu₂ - mu₁) * π * I) * cexp (lam₂ * cexp w) * cexp (mu₂ * w)

/-- The prefactor `(−1)^n i e^{(μ₂−μ₁)πi} e^{λ₁z} z^{μ₁}` of 2.11.21. -/
noncomputable def reexpPref₂ (lam₁ mu₁ mu₂ : ℂ) (n : ℕ) (w : ℂ) : ℂ :=
  (-1) ^ n * I * cexp ((mu₂ - mu₁) * π * I) * cexp (lam₁ * cexp w) * cexp (mu₁ * w)

/-- `R^{(1)}_{m,n}(z)`, defined by 2.11.20 from the remainder `R = R^{(1)}_n`. -/
noncomputable def reexpRem₁ (lam₂ mu₁ mu₂ C₁ : ℂ) (a₂ : ℕ → ℂ) (R : ℂ → ℂ) (m n : ℕ)
    (w : ℂ) : ℂ :=
  R w / reexpPref₁ lam₂ mu₁ mu₂ n w -
    C₁ * ∑ s ∈ Finset.range m, (-1) ^ s * a₂ s * terminant (n + mu₂ - mu₁ - s) w / cexp w ^ s

/-- `R^{(2)}_{m,n}(z)`, defined by 2.11.21 from the remainder `R = R^{(2)}_n`
(`F_p(ze^{−πi})`, `ze^{−πi} = e^{w − πi}`). -/
noncomputable def reexpRem₂ (lam₁ mu₁ mu₂ C₂ : ℂ) (a₁ : ℕ → ℂ) (R : ℂ → ℂ) (m n : ℕ)
    (w : ℂ) : ℂ :=
  R w / reexpPref₂ lam₁ mu₁ mu₂ n w -
    C₂ * ∑ s ∈ Finset.range m, (-1) ^ s * a₁ s * terminant (n + mu₁ - mu₂ - s) (w - π * I) /
      cexp w ^ s

theorem reexpPref₁_ne_zero (lam₂ mu₁ mu₂ : ℂ) (n : ℕ) (w : ℂ) :
    reexpPref₁ lam₂ mu₁ mu₂ n w ≠ 0 := by
  simp [reexpPref₁, Complex.exp_ne_zero]

theorem reexpPref₂_ne_zero (lam₁ mu₁ mu₂ : ℂ) (n : ℕ) (w : ℂ) :
    reexpPref₂ lam₁ mu₁ mu₂ n w ≠ 0 := by
  simp [reexpPref₂, Complex.exp_ne_zero]

/-- **DLMF 2.11.20** (the definition of `R^{(1)}_{m,n}`). -/
theorem dlmf_2_11_20 (lam₂ mu₁ mu₂ C₁ : ℂ) (a₂ : ℕ → ℂ) (R : ℂ → ℂ) (m n : ℕ) (w : ℂ) :
    R w = reexpPref₁ lam₂ mu₁ mu₂ n w * (C₁ * ∑ s ∈ Finset.range m,
      (-1) ^ s * a₂ s * terminant (n + mu₂ - mu₁ - s) w / cexp w ^ s +
        reexpRem₁ lam₂ mu₁ mu₂ C₁ a₂ R m n w) := by
  rw [reexpRem₁, add_sub_cancel, mul_div_cancel₀ _ (reexpPref₁_ne_zero _ _ _ _ _)]

/-- **DLMF 2.11.21** (the definition of `R^{(2)}_{m,n}`). -/
theorem dlmf_2_11_21 (lam₁ mu₁ mu₂ C₂ : ℂ) (a₁ : ℕ → ℂ) (R : ℂ → ℂ) (m n : ℕ) (w : ℂ) :
    R w = reexpPref₂ lam₁ mu₁ mu₂ n w * (C₂ * ∑ s ∈ Finset.range m,
      (-1) ^ s * a₁ s * terminant (n + mu₁ - mu₂ - s) (w - π * I) / cexp w ^ s +
        reexpRem₂ lam₁ mu₁ mu₂ C₂ a₁ R m n w) := by
  rw [reexpRem₂, add_sub_cancel, mul_div_cancel₀ _ (reexpPref₂_ne_zero _ _ _ _ _)]

/-! ### Example: the incomplete gamma function -/

/-- The coefficients of `f(z) = 1 + p/z` at infinity: `f₀ = 1`, `f₁ = p`, `fₛ = 0` (`s ≥ 2`). -/
def incGammaFc (p : ℂ) : ℕ → ℂ := fun s => if s = 0 then 1 else if s = 1 then p else 0

/-- The characteristic roots of `w″ + (1 + p/z)w′ = 0` (2.7.9) are `λ₁ = −1`, `λ₂ = 0`, so that
`λ₂ − λ₁ = 1` as §2.11(v) assumes. -/
theorem incGamma_charRoots (p : ℂ) :
    rankOneChar (incGammaFc p) (fun _ => 0) (-1) = 0 ∧
      rankOneChar (incGammaFc p) (fun _ => 0) 0 = 0 := by
  simp [rankOneChar, incGammaFc]

/-- `μ₁ = −p`, `μ₂ = 0` (2.7.10). -/
theorem incGamma_mu (p : ℂ) :
    rankOneMu (incGammaFc p) (fun _ => 0) (-1) = -p ∧
      rankOneMu (incGammaFc p) (fun _ => 0) 0 = 0 := by
  refine ⟨?_, by simp [rankOneMu, incGammaFc]⟩
  simp [rankOneMu, incGammaFc]
  norm_num
  rw [div_neg, div_one]

theorem incGamma_sum (p lam mu : ℂ) (a : ℕ → ℂ) (s : ℕ) :
    ∑ i ∈ Finset.range (s + 1), (lam * incGammaFc p (s + 2 - i) + (fun _ => (0 : ℂ)) (s + 2 - i) -
      ((i : ℂ) - mu) * incGammaFc p (s + 1 - i)) * a i = -(((s : ℂ) - mu) * p) * a s := by
  rw [Finset.sum_range_succ, Finset.sum_eq_zero, zero_add]
  · simp [incGammaFc]
  · intro i hi
    have hi' := Finset.mem_range.mp hi
    simp [incGammaFc, show s + 2 - i ≠ 0 by omega, show s + 2 - i ≠ 1 by omega,
      show s + 1 - i ≠ 0 by omega, show s + 1 - i ≠ 1 by omega]

/-- The coefficients `a_{s,1} = (−1)^s (p)_s` (2.7.11 with `λ = −1`, `μ = −p`). -/
theorem incGamma_coeff₁ (p : ℂ) (s : ℕ) :
    rankOneCoeff (incGammaFc p) (fun _ => 0) (-1) (-p) s =
      (-1) ^ s * (ascPochhammer ℂ s).eval p := by
  have hne : incGammaFc p 0 + 2 * (-1) ≠ 0 := by simp [incGammaFc]; norm_num
  induction s with
  | zero => simp [rankOneCoeff_zero]
  | succ s ih =>
    have h := rankOneCoeff_succ (incGammaFc p) (fun _ => 0) (-p) hne s
    rw [incGamma_sum, ih] at h
    have hs : ((s + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero s)
    rw [ascPochhammer_succ_eval, pow_succ]
    apply mul_left_cancel₀ (mul_ne_zero hne hs)
    rw [h]
    simp only [incGammaFc, ite_true]
    push_cast
    ring

/-- The coefficients `a_{s,2} = δ_{s0}` (2.7.11 with `λ = μ = 0`): the solution `w₂ = 1`. -/
theorem incGamma_coeff₂ (p : ℂ) (s : ℕ) :
    rankOneCoeff (incGammaFc p) (fun _ => 0) 0 0 s = if s = 0 then 1 else 0 := by
  have hne : incGammaFc p 0 + 2 * 0 ≠ 0 := by simp [incGammaFc]
  induction s with
  | zero => simp [rankOneCoeff_zero]
  | succ s ih =>
    have h := rankOneCoeff_succ (incGammaFc p) (fun _ => 0) (0 : ℂ) hne s
    rw [incGamma_sum, ih] at h
    have hs : ((s + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero s)
    simp only [Nat.succ_ne_zero, ite_false]
    apply mul_left_cancel₀ (mul_ne_zero hne hs)
    rw [h, mul_zero]
    rcases Nat.eq_zero_or_pos s with rfl | hs0
    · simp
    · simp [hs0.ne']

/-- **`w₁(z) = Γ(1 − p, z) = ∫_z^∞ e^{−t}t^{−p} dt` solves `w″ + (1 + p/z)w′ = 0`** on the
principal sheet (`eiP p (ln z)`); its derivative is `−e^{−z}z^{−p}`. -/
theorem incGamma_isODESolution (p : ℂ) :
    IsODESolution slitPlane (fun z => 1 + p / z) (fun _ => 0)
      (fun z => eiP p (Complex.log z)) := by
  set D : ℂ → ℂ := fun y => -cexp (-y) * cexp (-p * Complex.log y)
  have hw' : ∀ y ∈ slitPlane, HasDerivAt (fun z => eiP p (Complex.log z)) (D y) y := by
    intro y hy
    have hy0 : y ≠ 0 := slitPlane_ne_zero hy
    have h1 := (hasDerivAt_eiP p (Complex.log y)).comp y (Complex.hasDerivAt_log hy)
    convert h1 using 1
    · rfl
    simp only [D, eiF, Complex.exp_log hy0]
    rw [show (1 - p) * Complex.log y = -p * Complex.log y + Complex.log y by ring,
      Complex.exp_add, Complex.exp_log hy0]
    field_simp
  refine ⟨fun y hy => (hw' y hy).differentiableAt.differentiableWithinAt, fun z hz => ?_⟩
  have hz0 : z ≠ 0 := slitPlane_ne_zero hz
  have hev : deriv (fun z => eiP p (Complex.log z)) =ᶠ[𝓝 z] D :=
    Filter.eventually_of_mem (Complex.isOpen_slitPlane.mem_nhds hz) fun y hy => (hw' y hy).deriv
  have hD : HasDerivAt D (cexp (-z) * cexp (-p * Complex.log z) * (1 + p / z)) z := by
    have h1 := (hasDerivAt_id z).neg.cexp.neg
    have h2 := ((Complex.hasDerivAt_log hz).const_mul (-p)).cexp
    convert h1.mul h2 using 1
    · rfl
    simp only [Pi.neg_apply, id_eq]
    field_simp
  rw [hev.deriv_eq, hD.deriv, (hw' z hz).deriv]
  simp only [D]
  ring

/-- The Stokes multiplier `C₁ = 2πi e^{−πip}/Γ(p)` of the example. -/
noncomputable def incGammaC₁ (p : ℂ) : ℂ := 2 * π * I * cexp (-(π * I * p)) / Complex.Gamma p

/-- **DLMF 2.7.17 in the example**: `w₁(z) = e^{2πiμ₁}w₁(ze^{−2πi}) + C₁w₂(z)` with `μ₁ = −p`,
`w₂ = 1` (and `w₂(z) = e^{−2πiμ₂}w₂(ze^{2πi}) + C₂w₁(z)` with `C₂ = 0`). -/
theorem incGamma_dlmf_2_7_17 (p w : ℂ) :
    eiP p w = cexp (2 * π * I * (-p)) * eiP p (w - 2 * π * I) + incGammaC₁ p * 1 := by
  have h := eiC_eq p (w - 2 * π * I)
  rw [eiC_eq_connConst, connConst, sub_add_cancel] at h
  have hinv := exp_two_pi_I_mul_neg p
  have heq : cexp (2 * π * I * (-p)) * cexp (π * I * p) = cexp (-(π * I * p)) := by
    rw [← Complex.exp_add]; ring_nf
  have hneg : cexp (2 * π * I * (-p)) = cexp (-(2 * π * I * p)) := by ring_nf
  rw [incGammaC₁, mul_one]
  rw [hneg] at heq ⊢
  linear_combination cexp (-(2 * π * I * p)) * h - eiP p w * hinv +
    (2 * π * I / Complex.Gamma p) * heq

/-- **DLMF 2.7.14 in the example** (sector 2.7.15): `w₁ = Γ(1 − p, z)` has the expansion
`e^{−z}z^{−p} ∑ (−1)^s (p)_s/z^s`, with remainder `O(e^{−z}z^{−p−n})` for `|z| ≥ 1`,
`|ph z| ≤ 3π/2 − δ` (from 2.11.6). -/
theorem incGamma_dlmf_2_7_14 (p : ℂ) (n : ℕ) {δ : ℝ} (hδ : 0 < δ) (hδ' : δ ≤ π) :
    ∃ C : ℝ, ∀ w : ℂ, |w.im| ≤ 3 * π / 2 - δ → 0 ≤ w.re →
      ‖odeRem (-1) (-p) (fun s => (-1) ^ s * (ascPochhammer ℂ s).eval p) (eiP p) n w‖ ≤
        C * (‖cexp (-cexp w)‖ * ‖cexp (-p * w)‖ / ‖cexp w‖ ^ n) := by
  obtain ⟨C, hC⟩ := dlmf_2_11_6 p n hδ hδ'
  refine ⟨C, fun w hw hre => ?_⟩
  have hz : cexp w ≠ 0 := Complex.exp_ne_zero w
  have hP : eiP p w = cexp ((1 - p) * w) * genExpInt p w := by
    rw [genExpInt, ← mul_assoc, ← Complex.exp_add]; ring_nf; simp
  have h1 : cexp ((1 - p) * w) = cexp (-p * w) * cexp w := by
    rw [← Complex.exp_add]; ring_nf
  have hR : odeRem (-1) (-p) (fun s => (-1) ^ s * (ascPochhammer ℂ s).eval p) (eiP p) n w =
      cexp ((1 - p) * w) * (genExpInt p w - cexp (-cexp w) / cexp w * ∑ s ∈ Finset.range n,
        (-1) ^ s * (ascPochhammer ℂ s).eval p / cexp w ^ s) := by
    rw [odeRem, hP, h1]
    simp only [neg_one_mul, mul_div_assoc]
    field_simp
  rw [hR, norm_mul, h1, norm_mul]
  have hb := hC w hw hre
  have hzn : 0 < ‖cexp w‖ := norm_pos_iff.mpr hz
  calc ‖cexp (-p * w)‖ * ‖cexp w‖ * ‖_‖ ≤ ‖cexp (-p * w)‖ * ‖cexp w‖ *
        (C * (‖cexp (-cexp w)‖ / ‖cexp w‖ ^ (n + 1))) :=
        mul_le_mul_of_nonneg_left hb (by positivity)
    _ = _ := by rw [pow_succ]; field_simp

/-- The remainder of `w₁` is a single terminant: `R^{(1)}_n(z) = (−1)^n (2π/Γ(p)) F_{n+p}(z)`
(2.11.10). -/
theorem incGamma_odeRem {p : ℂ} (hp : ∀ m : ℕ, p ≠ -m) (n : ℕ) (w : ℂ) :
    odeRem (-1) (-p) (fun s => (-1) ^ s * (ascPochhammer ℂ s).eval p) (eiP p) n w =
      (-1) ^ n * (2 * π / Complex.Gamma p) * terminant (n + p) w := by
  have hE := dlmf_2_11_10 hp w n
  have hP : eiP p w = cexp ((1 - p) * w) * genExpInt p w := by
    rw [genExpInt, ← mul_assoc, ← Complex.exp_add]; ring_nf; simp
  have h1 : cexp ((1 - p) * w) / cexp w = cexp (-p * w) := by
    rw [← Complex.exp_sub]; ring_nf
  have h2 : cexp ((1 - p) * w) * cexp ((p - 1) * w) = 1 := by
    rw [← Complex.exp_add]; ring_nf; simp
  rw [odeRem, hP, hE]
  simp only [neg_one_mul]
  linear_combination (cexp (-cexp w) * ∑ s ∈ Finset.range n,
    (-1) ^ s * (ascPochhammer ℂ s).eval p / cexp w ^ s) * h1 +
    ((-1) ^ n * (2 * π / Complex.Gamma p) * terminant (n + p) w) * h2

/-- **DLMF 2.11.20 in the example**, exactly: since `a_{s,2} = δ_{s0}`, the re-expansion of
`R^{(1)}_n` terminates, `R^{(1)}_{m,n} = 0` for `m ≥ 1` (and `R^{(1)}_{0,n} = C₁F_{n+p}(z)`). -/
theorem incGamma_reexpRem₁ {p : ℂ} (hp : ∀ m : ℕ, p ≠ -m) (m n : ℕ) (w : ℂ) :
    reexpRem₁ 0 (-p) 0 (incGammaC₁ p) (fun s => if s = 0 then 1 else 0)
        (odeRem (-1) (-p) (fun s => (-1) ^ s * (ascPochhammer ℂ s).eval p) (eiP p) n) m n w =
      if m = 0 then incGammaC₁ p * terminant (n + p) w else 0 := by
  have hG : Complex.Gamma p ≠ 0 := Complex.Gamma_ne_zero hp
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hR : odeRem (-1) (-p) (fun s => (-1) ^ s * (ascPochhammer ℂ s).eval p) (eiP p) n w /
      reexpPref₁ 0 (-p) 0 n w = incGammaC₁ p * terminant (n + p) w := by
    rw [incGamma_odeRem hp, reexpPref₁, incGammaC₁]
    have he : cexp ((0 - -p) * π * I) * cexp (-(π * I * p)) = 1 := by
      rw [← Complex.exp_add]; ring_nf; simp
    rw [eq_inv_of_mul_eq_one_right he]
    simp only [zero_mul, Complex.exp_zero, mul_one]
    have hE : cexp ((0 - -p) * π * I) ≠ 0 := Complex.exp_ne_zero _
    field_simp
    rw [pow_succ]
    linear_combination ((-1) ^ n * terminant (n + p) w) * Complex.I_sq
  rw [reexpRem₁, hR]
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  · rw [Finset.sum_eq_single 0 (fun s _ hs => by simp [hs]) (fun h => absurd
      (Finset.mem_range.mpr hm) h)]
    simp only [hm.ne', ↓reduceIte, pow_zero, one_mul, Nat.cast_zero, sub_zero, div_one]
    ring_nf

/-- **DLMF 2.11.22 in the example**: as `ρ = |z| → ∞` with `|n − ρ| ≤ B` and `m` fixed,
`R^{(1)}_{m,n}(z) = O(e^{−|z|−z}z^{−m})` uniformly for `|ph z| ≤ π` and `O(z^{−m})` for
`π ≤ |ph z| ≤ 3π` (which contains DLMF's `π ≤ |ph z| ≤ 5π/2 − δ`). -/
theorem incGamma_dlmf_2_11_22 {p : ℂ} (hp : ∀ m : ℕ, p ≠ -m) (m : ℕ) (B : ℝ) :
    ∃ C ρ₀ : ℝ, 0 < ρ₀ ∧ ∀ ρ : ℝ, ρ₀ ≤ ρ → ∀ n : ℕ, |(n : ℝ) - ρ| ≤ B →
      (∀ θ : ℝ, |θ| ≤ π →
        ‖reexpRem₁ 0 (-p) 0 (incGammaC₁ p) (fun s => if s = 0 then 1 else 0)
          (odeRem (-1) (-p) (fun s => (-1) ^ s * (ascPochhammer ℂ s).eval p) (eiP p) n) m n
            (polarW ρ θ)‖ ≤
          C * (Real.exp (-ρ) * ‖cexp (-cexp (polarW ρ θ))‖) / ρ ^ m) ∧
      (∀ θ : ℝ, π ≤ |θ| → |θ| ≤ 3 * π →
        ‖reexpRem₁ 0 (-p) 0 (incGammaC₁ p) (fun s => if s = 0 then 1 else 0)
          (odeRem (-1) (-p) (fun s => (-1) ^ s * (ascPochhammer ℂ s).eval p) (eiP p) n) m n
            (polarW ρ θ)‖ ≤ C / ρ ^ m) := by
  set A := |B| + ‖p‖
  obtain ⟨C₁, ρ₁, hC₁, hρ₁, h₁⟩ := terminant_uniform A
  obtain ⟨C₂, ρ₂, hC₂, hρ₂, h₂⟩ := terminant_bounded_beyond A
  have hA : 0 ≤ A := by positivity
  refine ⟨‖incGammaC₁ p‖ * max C₁ C₂, max ρ₁ ρ₂, by
    linarith [le_max_left ρ₁ ρ₂], fun ρ hρ n hn => ?_⟩
  have hρ0 : 0 < ρ := by linarith [le_max_left ρ₁ ρ₂]
  set α : ℂ := (n : ℂ) + p - ρ
  have hα : ‖α‖ ≤ A := by
    have e : α = (((n : ℝ) - ρ : ℝ) : ℂ) + p := by simp only [α]; push_cast; ring
    rw [e]
    have h1 : ‖(((n : ℝ) - ρ : ℝ) : ℂ)‖ ≤ |B| := by
      rw [Complex.norm_real, Real.norm_eq_abs]; exact hn.trans (le_abs_self B)
    exact (norm_add_le _ _).trans (by simp only [A]; linarith)
  have hq : (n : ℂ) + p = (ρ : ℂ) + α := by simp only [α]; ring
  have hK : 0 ≤ ‖incGammaC₁ p‖ * max C₁ C₂ := by positivity
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp only [incGamma_reexpRem₁ hp, ↓reduceIte, pow_zero, div_one, norm_mul, hq]
    refine ⟨fun θ hθ => ?_, fun θ hθ₁ hθ₂ => ?_⟩
    · have := h₁ ρ (le_trans (le_max_left _ _) hρ) θ hθ α hα
      calc _ ≤ ‖incGammaC₁ p‖ * (C₁ * Real.exp (-ρ) * ‖cexp (-cexp (polarW ρ θ))‖) :=
            mul_le_mul_of_nonneg_left this (norm_nonneg _)
        _ ≤ ‖incGammaC₁ p‖ * (max C₁ C₂ * Real.exp (-ρ) * ‖cexp (-cexp (polarW ρ θ))‖) := by
            gcongr; exact le_max_left _ _
        _ = _ := by ring
    · have := h₂ ρ (le_trans (le_max_right _ _) hρ) θ hθ₁ hθ₂ α hα
      exact mul_le_mul_of_nonneg_left (this.trans (le_max_right _ _)) (norm_nonneg _)
  · simp only [incGamma_reexpRem₁ hp, hm.ne', ↓reduceIte, norm_zero]
    exact ⟨fun _ _ => by positivity, fun _ _ _ => by positivity⟩

/-- **DLMF 2.11.21 and 2.11.23 in the example**: `w₂ = 1` has `R^{(2)}_n = 0` (`n ≥ 1`) and
`C₂ = 0`, so `R^{(2)}_{m,n} = 0`. -/
theorem incGamma_dlmf_2_11_23 (p : ℂ) {n : ℕ} (hn : 1 ≤ n) (m : ℕ) (w : ℂ) :
    reexpRem₂ (-1) (-p) 0 0 (fun s => (-1) ^ s * (ascPochhammer ℂ s).eval p)
      (odeRem 0 0 (fun s => if s = 0 then 1 else 0) (fun _ => 1) n) m n w = 0 := by
  have hR : odeRem 0 0 (fun s => if s = 0 then 1 else 0) (fun _ => 1) n w = 0 := by
    rw [odeRem, Finset.sum_eq_single 0 (fun s _ hs => by simp [hs]) (fun h => absurd
      (Finset.mem_range.mpr hn) h)]
    simp
  rw [reexpRem₂, hR]
  simp

end Azurite.DLMF
