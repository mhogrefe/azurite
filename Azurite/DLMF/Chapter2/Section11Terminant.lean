/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/


import Azurite.DLMF.Chapter2.Section11ExpintLaplace

/-!
# DLMF §2.11(iii): re-expansion of the remainder, 2.11.8–2.11.12

With `z = e^w` on the Riemann surface (`Section11Expint.lean`):

* 2.11.9 (`dlmf_2_11_9`): `1/(1 + t) = ∑_{s<n} (−1)^s t^s + (−1)^n tⁿ/(1 + t)`.
* The terminant function `F_q(z) = Γ(q)/(2π) · E_q(z)/z^{q−1}` (2.11.11, second form;
  `terminant q w = Γ(q)/(2π) · eiP q w`).
* 2.11.10 (`dlmf_2_11_10`): `E_p(z) = (e^{−z}/z) ∑_{s<n} (−1)^s (p)_s/z^s
  + (−1)^n (2π/Γ(p)) z^{p−1} F_{n+p}(z)`, exactly, for every `n` (`p` not a nonpositive integer).
* 2.11.11, first form (`dlmf_2_11_11`): `F_q(z) = (e^{−z}/2π) ∫_0^∞ e^{−zt} t^{q−1}/(1 + t) dt`,
  `ℜq > 0`, `|ph z| < π/2`.
* 2.11.8 and 2.11.12 (`dlmf_2_11_12`): with `z = ρe^{iθ}` and `q = n + p = ρ + α`,
  `F_q(z) = (e^{−z}/2π) ∫_0^∞ exp(−ρ(te^{iθ} − ln t)) t^{α−1}/(1 + t) dt`.
* The path rotated through `−θ` (`terminant_rotated`), for `−π < θ < π` ("valid by analytic
  continuation"; proved by Fubini from the ray representation of §2.11(ii)):
  `F_q(z) = (e^{−z}/2π) e^{−iqθ} ∫_0^∞ e^{−ρu} u^{q−1}/(1 + e^{−iθ}u) du`.
-/

open Filter Topology Set MeasureTheory Complex
open scoped Real Interval

namespace Azurite.DLMF

/-- **DLMF 2.11.9**. -/
theorem dlmf_2_11_9 {t : ℂ} (ht : t ≠ -1) (n : ℕ) :
    1 / (1 + t) = ∑ s ∈ Finset.range n, (-1) ^ s * t ^ s + (-1) ^ n * t ^ n / (1 + t) := by
  have h : (1 : ℂ) + t ≠ 0 := fun h => ht (by linear_combination h)
  induction n with
  | zero => simp
  | succ n ih =>
    rw [ih, Finset.sum_range_succ]
    field_simp
    ring

/-- The terminant function `F_q(z) = Γ(q)/(2π) · E_q(z)/z^{q−1}`, `z = e^w` (2.11.11). -/
noncomputable def terminant (q w : ℂ) : ℂ := Complex.Gamma q / (2 * π) * eiP q w

theorem terminant_eq_genExpInt (q w : ℂ) :
    terminant q w = Complex.Gamma q / (2 * π) * (genExpInt q w / cexp ((q - 1) * w)) := by
  rw [terminant, genExpInt, mul_div_cancel_left₀ _ (Complex.exp_ne_zero _)]

theorem ascPochhammer_eval_eq_Gamma {p : ℂ} (hp : ∀ m : ℕ, p ≠ -m) (n : ℕ) :
    (ascPochhammer ℂ n).eval p = Complex.Gamma (p + n) / Complex.Gamma p := by
  have hG : Complex.Gamma p ≠ 0 := Complex.Gamma_ne_zero hp
  induction n with
  | zero => simp [hG]
  | succ n ih =>
    have hpn : p + n ≠ 0 := fun h => hp n (by linear_combination h)
    rw [ascPochhammer_succ_eval, ih, show (p + ((n + 1 : ℕ) : ℂ)) = (p + n) + 1 by push_cast; ring,
      Complex.Gamma_add_one _ hpn]
    field_simp

/-- **DLMF 2.11.10**: `E_p(z) = (e^{−z}/z) ∑_{s<n} (−1)^s (p)_s/z^s
+ (−1)^n (2π/Γ(p)) z^{p−1} F_{n+p}(z)`. -/
theorem dlmf_2_11_10 {p : ℂ} (hp : ∀ m : ℕ, p ≠ -m) (w : ℂ) (n : ℕ) :
    genExpInt p w = cexp (-cexp w) / cexp w * ∑ s ∈ Finset.range n,
        (-1) ^ s * (ascPochhammer ℂ s).eval p / cexp w ^ s +
      (-1) ^ n * (2 * π / Complex.Gamma p) * cexp ((p - 1) * w) * terminant (n + p) w := by
  rw [genExpInt_expansion p w n, ascPochhammer_eval_eq_Gamma hp, terminant,
    show (n : ℂ) + p = p + n by ring]
  have hG : Complex.Gamma p ≠ 0 := Complex.Gamma_ne_zero hp
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  field_simp

/-- **DLMF 2.11.11** (first form): `F_q(z) = (e^{−z}/2π) ∫_0^∞ e^{−zt} t^{q−1}/(1 + t) dt` for
`ℜq > 0`, `|ph z| < π/2`. -/
theorem dlmf_2_11_11 {q : ℂ} (hq : 0 < q.re) {w : ℂ} (hw : |w.im| < π / 2) :
    terminant q w = cexp (-cexp w) / (2 * π) *
      ∫ t in Ioi (0 : ℝ), cexp (-(cexp w * t)) * (t : ℂ) ^ (q - 1) / (1 + t) := by
  have h := dlmf_2_11_5 hq hw
  rw [terminant_eq_genExpInt, h, cexp_cpow_of_abs_lt (by linarith [Real.pi_pos])]
  have hG : Complex.Gamma q ≠ 0 := Complex.Gamma_ne_zero_of_re_pos hq
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hE : cexp ((q - 1) * w) ≠ 0 := Complex.exp_ne_zero _
  field_simp

/-- The point `z = ρe^{iθ}` in logarithmic coordinates. -/
noncomputable def polarW (ρ θ : ℝ) : ℂ := (Real.log ρ : ℂ) + θ * I

theorem cexp_polarW {ρ : ℝ} (hρ : 0 < ρ) (θ : ℝ) : cexp (polarW ρ θ) = ρ * cexp (θ * I) := by
  rw [polarW, Complex.exp_add, ← Complex.ofReal_exp, Real.exp_log hρ]

theorem polarW_im (ρ θ : ℝ) : (polarW ρ θ).im = θ := by simp [polarW]

/-- **DLMF 2.11.12** (with 2.11.8, `q = n + p = ρ + α`): for `|θ| < π/2`,
`F_q(ρe^{iθ}) = (e^{−z}/2π) ∫_0^∞ exp(−ρ(te^{iθ} − ln t)) t^{α−1}/(1 + t) dt`. -/
theorem dlmf_2_11_12 {ρ θ : ℝ} (hρ : 0 < ρ) (hθ : |θ| < π / 2) {α : ℂ}
    (hq : 0 < ((ρ : ℂ) + α).re) :
    terminant (ρ + α) (polarW ρ θ) = cexp (-cexp (polarW ρ θ)) / (2 * π) *
      ∫ t in Ioi (0 : ℝ), cexp (-(ρ * (t * cexp (θ * I) - Real.log t))) *
        (t : ℂ) ^ (α - 1) / (1 + t) := by
  rw [dlmf_2_11_11 hq (by rwa [polarW_im])]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  have ht0 : (0 : ℝ) < t := ht
  have htC : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht0.ne'
  rw [cexp_polarW hρ]
  have e1 : (t : ℂ) ^ ((ρ : ℂ) + α - 1) = (t : ℂ) ^ (ρ : ℂ) * (t : ℂ) ^ (α - 1) := by
    rw [← Complex.cpow_add _ _ htC]; ring_nf
  have e2 : (t : ℂ) ^ (ρ : ℂ) = cexp (ρ * Real.log t) := by
    rw [Complex.cpow_def_of_ne_zero htC, ← Complex.ofReal_log ht0.le]; ring_nf
  rw [e1, e2, show -((ρ : ℂ) * ((t : ℂ) * cexp (θ * I) - (Real.log t : ℂ))) =
    -((ρ : ℂ) * cexp (θ * I) * t) + ρ * Real.log t by ring, Complex.exp_add]
  ring

/-! ### The rotated path -/

/-- **The path rotated through `−θ`**, `−π < θ < π`, `ℜq > 0`:
`Γ(q) ∫_z^∞ e^{−t} t^{−q} dt = e^{−z} e^{i(1−q)θ} ∫_0^∞ e^{−ρu} u^{q−1}/(e^{iθ} + u) du`. -/
theorem gamma_mul_eiP_rotated {q : ℂ} (hq : 0 < q.re) {ρ θ : ℝ} (hρ : 0 < ρ) (hθ : |θ| < π) :
    Complex.Gamma q * eiP q (polarW ρ θ) = cexp (-(ρ * cexp (θ * I))) *
      cexp ((1 - q) * (θ * I)) *
        ∫ u in Ioi (0 : ℝ), cexp (-(ρ * u)) * (u : ℂ) ^ (q - 1) / (cexp (θ * I) + u) := by
  set w := polarW ρ θ
  set z := cexp w
  have hz : z = ρ * cexp (θ * I) := cexp_polarW hρ θ
  have hθ2 : |θ / 2| < π / 2 := by rw [abs_div, abs_two]; linarith
  have hc2 : 0 < Real.cos (θ / 2) :=
    Real.cos_pos_of_mem_Ioo ⟨by rw [abs_lt] at hθ2; linarith, by rw [abs_lt] at hθ2; linarith⟩
  set e := cexp (((-(θ / 2) : ℝ) : ℂ) * I)
  have hre_e : e.re = Real.cos (θ / 2) := by
    rw [Complex.exp_ofReal_mul_I_re, Real.cos_neg]
  have hray : ∀ σ : ℝ, 0 ≤ σ → 1 ≤ (1 + σ * e).re := fun σ hσ => by
    have : (1 + (σ : ℂ) * e).re = 1 + σ * Real.cos (θ / 2) := by
      rw [Complex.add_re, Complex.one_re, Complex.re_ofReal_mul, hre_e]
    rw [this]; nlinarith
  have hze : z * e = ρ * cexp ((θ / 2 : ℝ) * I) := by
    rw [hz, mul_assoc, ← Complex.exp_add]; congr 2; push_cast; ring
  have hre_ze : (z * e).re = ρ * Real.cos (θ / 2) := by
    rw [hze, Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]
  have hze0 : 0 < (z * e).re := by rw [hre_ze]; positivity
  have harg_e : arg e = -(θ / 2) := by
    show arg (cexp (((-(θ / 2) : ℝ) : ℂ) * I)) = _
    rw [Complex.exp_mul_I]
    exact Complex.arg_cos_add_sin_mul_I ⟨by rw [abs_lt] at hθ; linarith, by
      rw [abs_lt] at hθ; linarith⟩
  have he_slit : e ∈ slitPlane := Complex.mem_slitPlane_iff.mpr (Or.inl (by rw [hre_e]; exact hc2))
  have h := eiP_eq_ray (le_of_lt hq) (fun σ hσ => Complex.mem_slitPlane_iff.mpr
    (Or.inl (by linarith [hray σ hσ]))) one_pos (fun σ hσ => (hray σ hσ).trans
      (Complex.re_le_norm _)) he_slit hze0
    (by rw [polarW_im, harg_e, show θ + -(θ / 2) = θ / 2 by ring]; exact hθ2)
  -- Fubini
  set H : ℝ → ℝ → ℂ := fun σ s =>
    cexp (-(z * (1 + σ * e))) * ((s : ℂ) ^ (q - 1) * cexp (-((1 + σ * e) * s)))
  have hin1 : ∀ σ ∈ Ioi (0 : ℝ), ∫ s in Ioi (0 : ℝ), H σ s =
      Complex.Gamma q * (cexp (-(z * (1 + σ * e))) * (1 + σ * e) ^ (-q)) := fun σ hσ => by
    have hre : 0 < (1 + σ * e).re := by linarith [hray σ (le_of_lt hσ)]
    simp only [H]
    rw [MeasureTheory.integral_const_mul, integral_cpow_mul_cexp_neg_complex hq hre,
      one_div_cpow_of_re_pos hre]
    ring
  have hin2 : ∀ s ∈ Ioi (0 : ℝ), ∫ σ in Ioi (0 : ℝ), H σ s =
      (s : ℂ) ^ (q - 1) * cexp (-z) * cexp (-s) / (e * (z + s)) := fun s hs => by
    have hs' : (0 : ℝ) < s := hs
    have hre : (-(e * (z + s))).re < 0 := by
      rw [show e * (z + s) = z * e + (s : ℂ) * e by ring, Complex.neg_re, Complex.add_re,
        Complex.re_ofReal_mul, hre_e]
      have := mul_pos hs' hc2
      linarith
    have hne : e * (z + s) ≠ 0 := fun h0 => by rw [h0] at hre; simp at hre
    have eH : ∀ σ : ℝ, H σ s = (s : ℂ) ^ (q - 1) * cexp (-z) * cexp (-s) *
        cexp (-(e * (z + s)) * σ) := by
      intro σ
      simp only [H]
      rw [show -(z * (1 + σ * e)) = -z + -(σ * (e * z)) by ring,
        show -((1 + σ * e) * s) = -(s : ℂ) + -(σ * (e * s)) by ring,
        show -(e * (z + s)) * σ = -(σ * (e * z)) + -(σ * (e * s)) by ring,
        Complex.exp_add, Complex.exp_add, Complex.exp_add]
      ring
    simp only [eH]
    rw [MeasureTheory.integral_const_mul, integral_exp_mul_complex_Ioi hre 0]
    simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero]
    field_simp
  have hint : Integrable (Function.uncurry H)
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) := by
    have h1 : Integrable (fun σ : ℝ => Real.exp (-z.re) * Real.exp (-(z * e).re * σ))
        (volume.restrict (Ioi (0 : ℝ))) := (exp_neg_integrableOn_Ioi 0 hze0).const_mul _
    have h2 : Integrable (fun s : ℝ => ‖(s : ℂ) ^ (q - 1) * cexp (-(1 * s))‖)
        (volume.restrict (Ioi (0 : ℝ))) := (integrableOn_cpow_mul_cexp_neg hq (by simp)).norm
    refine (h1.mul_prod h2).mono' ?_ ?_
    · refine Measurable.aestronglyMeasurable ?_
      simp only [H, Function.uncurry_def]
      fun_prop
    · rw [Measure.prod_restrict, ae_restrict_iff' (measurableSet_Ioi.prod measurableSet_Ioi)]
      refine Eventually.of_forall fun x hx => ?_
      obtain ⟨hs, ht⟩ := hx
      have hs' : (0 : ℝ) < x.1 := hs
      have ht' : (0 : ℝ) < x.2 := ht
      simp only [H, Function.uncurry_def]
      rw [norm_mul, norm_mul, norm_mul]
      have e1 : ‖cexp (-(z * (1 + x.1 * e)))‖ =
          Real.exp (-z.re) * Real.exp (-(z * e).re * x.1) := by
        rw [Complex.norm_exp, ← Real.exp_add]
        congr 1
        rw [show z * (1 + x.1 * e) = z + x.1 * (z * e) by ring, Complex.neg_re, Complex.add_re,
          Complex.re_ofReal_mul]
        ring
      have e2 : ‖cexp (-((1 + x.1 * e) * x.2))‖ ≤ ‖cexp (-(1 * x.2))‖ := by
        rw [Complex.norm_exp, Complex.norm_exp]
        apply Real.exp_le_exp.mpr
        have a1 : (-((1 + (x.1 : ℂ) * e) * x.2)).re = -x.2 - x.1 * x.2 * Real.cos (θ / 2) := by
          rw [Complex.neg_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
            sub_zero, Complex.add_re, Complex.one_re, Complex.re_ofReal_mul, hre_e]
          ring
        rw [a1]
        simp
        nlinarith [mul_pos (mul_pos hs' ht') hc2]
      rw [e1]
      gcongr
  have hswap := integral_integral_swap hint
  rw [setIntegral_congr_fun measurableSet_Ioi hin1, setIntegral_congr_fun measurableSet_Ioi hin2,
    MeasureTheory.integral_const_mul] at hswap
  -- assemble
  have hkey : Complex.Gamma q * eiP q w = cexp ((1 - q) * w) * cexp (-z) *
      ∫ s in Ioi (0 : ℝ), (s : ℂ) ^ (q - 1) * cexp (-s) / (z + s) := by
    rw [h, show Complex.Gamma q * (cexp ((1 - q) * w) * e *
        ∫ σ in Ioi (0 : ℝ), cexp (-(cexp w * (1 + σ * e))) * (1 + σ * e) ^ (-q)) =
        cexp ((1 - q) * w) * e * (Complex.Gamma q *
          ∫ σ in Ioi (0 : ℝ), cexp (-(z * (1 + σ * e))) * (1 + σ * e) ^ (-q)) by ring, hswap]
    have he0 : e ≠ 0 := Complex.exp_ne_zero _
    rw [show (∫ s in Ioi (0 : ℝ), (s : ℂ) ^ (q - 1) * cexp (-z) * cexp (-s) / (e * (z + s))) =
        ∫ s in Ioi (0 : ℝ), (cexp (-z) / e) * ((s : ℂ) ^ (q - 1) * cexp (-s) / (z + s)) by
      congr 1; funext s; field_simp, MeasureTheory.integral_const_mul]
    field_simp
  -- substitution `s = ρu`
  set g : ℝ → ℂ := fun s => (s : ℂ) ^ (q - 1) * cexp (-s) / (z + s)
  have hs := integral_comp_mul_left_Ioi g 0 hρ
  rw [mul_zero] at hs
  have hρC : (ρ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hρ.ne'
  have hcongr : (∫ u in Ioi (0 : ℝ), g (ρ * u)) = ((ρ : ℂ) ^ (q - 1) / ρ) *
      ∫ u in Ioi (0 : ℝ), cexp (-(ρ * u)) * (u : ℂ) ^ (q - 1) / (cexp (θ * I) + u) := by
    rw [← MeasureTheory.integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun u hu => ?_
    have hu0 : (0 : ℝ) < u := hu
    have hden : cexp (θ * I) + u ≠ 0 := by
      intro h0
      have h1 : Real.sin θ = 0 := by
        have := congrArg Complex.im h0
        simpa [Complex.exp_ofReal_mul_I_im] using this
      have h2 : Real.cos θ + u = 0 := by
        have := congrArg Complex.re h0
        simpa [Complex.exp_ofReal_mul_I_re] using this
      have hθ0 : θ = 0 := (Real.sin_eq_zero_iff_of_lt_of_lt (by rw [abs_lt] at hθ; linarith)
        (by rw [abs_lt] at hθ; linarith)).mp h1
      rw [hθ0, Real.cos_zero] at h2
      linarith
    simp only [g]
    rw [Complex.ofReal_mul, mul_cpow_ofReal_nonneg hρ.le hu0.le, hz,
      show (ρ : ℂ) * cexp (θ * I) + (ρ : ℂ) * u = ρ * (cexp (θ * I) + u) by ring]
    field_simp
  have hsub : (∫ s in Ioi (0 : ℝ), g s) = (ρ : ℂ) ^ (q - 1) *
      ∫ u in Ioi (0 : ℝ), cexp (-(ρ * u)) * (u : ℂ) ^ (q - 1) / (cexp (θ * I) + u) := by
    calc (∫ s in Ioi (0 : ℝ), g s) = (ρ : ℝ) • ∫ u in Ioi (0 : ℝ), g (ρ * u) := by
          rw [hs, smul_smul, mul_inv_cancel₀ hρ.ne', one_smul]
      _ = _ := by rw [hcongr, Complex.real_smul]; field_simp
  have hpow : cexp ((1 - q) * w) * (ρ : ℂ) ^ (q - 1) = cexp ((1 - q) * (θ * I)) := by
    rw [Complex.cpow_def_of_ne_zero hρC, ← Complex.ofReal_log hρ.le, ← Complex.exp_add]
    congr 1
    simp only [w, polarW]
    ring
  rw [hkey, show (∫ s in Ioi (0 : ℝ), (s : ℂ) ^ (q - 1) * cexp (-s) / (z + s)) =
    ∫ s in Ioi (0 : ℝ), g s from rfl, hsub, ← hz]
  rw [← hpow]
  ring

/-- **The rotated path in DLMF's form**: for `ℜq > 0`, `|θ| < π`,
`F_q(ρe^{iθ}) = (e^{−z}/2π) e^{−iqθ} ∫_0^∞ e^{−ρu} u^{q−1}/(1 + e^{−iθ}u) du`. -/
theorem terminant_rotated {q : ℂ} (hq : 0 < q.re) {ρ θ : ℝ} (hρ : 0 < ρ) (hθ : |θ| < π) :
    terminant q (polarW ρ θ) = cexp (-(ρ * cexp (θ * I))) / (2 * π) * cexp (-(q * (θ * I))) *
      ∫ u in Ioi (0 : ℝ), cexp (-(ρ * u)) * (u : ℂ) ^ (q - 1) / (1 + cexp (-(θ * I)) * u) := by
  have h := gamma_mul_eiP_rotated hq hρ hθ
  have hc : cexp (θ * I) ≠ 0 := Complex.exp_ne_zero _
  have hinv : cexp (θ * I) * cexp (-(θ * I)) = 1 := by rw [← Complex.exp_add]; simp
  have hint : (∫ u in Ioi (0 : ℝ), cexp (-(ρ * u)) * (u : ℂ) ^ (q - 1) / (cexp (θ * I) + u)) =
      cexp (-(θ * I)) * ∫ u in Ioi (0 : ℝ), cexp (-(ρ * u)) * (u : ℂ) ^ (q - 1) /
        (1 + cexp (-(θ * I)) * u) := by
    rw [← MeasureTheory.integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
    have e : cexp (θ * I) + u = cexp (θ * I) * (1 + cexp (-(θ * I)) * u) := by
      rw [mul_add, mul_one, ← mul_assoc, hinv, one_mul]
    rw [e]
    simp only [div_eq_mul_inv, mul_inv, ← Complex.exp_neg]
    ring
  have hexp : cexp ((1 - q) * (θ * I)) * cexp (-(θ * I)) = cexp (-(q * (θ * I))) := by
    rw [← Complex.exp_add]; ring_nf
  rw [terminant, show Complex.Gamma q / (2 * π) * eiP q (polarW ρ θ) =
    (Complex.Gamma q * eiP q (polarW ρ θ)) / (2 * π) by ring, h, hint, ← hexp]
  ring

end Azurite.DLMF
