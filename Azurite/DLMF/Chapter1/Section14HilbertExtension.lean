/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/


import Azurite.DLMF.Chapter1.Section14HilbertDensity

/-!
# DLMF 1.14.45: from the dense class to `L^p`

`DenseBound p A` says `‖Q₁ − Q₂‖_p ≤ A ‖P₁ − P₂‖_p` for data of the dense class (`DenseDatum`).
It holds with `A = tan(π/2p)` for `1 < p ≤ 2` (`denseBound_of_le_two`).
`hilbert_Lp_of_denseBound` extends any such bound to `L^p`:
* the conjugate integrals of the approximants are Cauchy in `L^p`, with limit `h`;
* `Q_ε f = P_ε ∗ h`, by the semigroup identities and Hölder (`tendsto_integral_mul_of_eLpNorm`);
* at the common Lebesgue points of `f` and `h`, `ℋf = h` (`hasHilbert_of_lebesgue`, which uses the
  kernel estimate `abs_kappa_le`).
-/

open MeasureTheory Filter Topology Set Complex
open scoped Real ENNReal

namespace Azurite.DLMF

/-! ### Hölder pairing and `L^p` membership from decay -/

theorem holderConjugate_ofReal {p q : ℝ} (hpq : p.HolderConjugate q) :
    ENNReal.HolderConjugate (ENNReal.ofReal p) (ENNReal.ofReal q) := by
  rw [ENNReal.holderConjugate_iff, ← ENNReal.ofReal_inv_of_pos hpq.pos,
    ← ENNReal.ofReal_inv_of_pos hpq.symm.pos, ← ENNReal.ofReal_add (by
      have := hpq.pos; positivity) (by have := hpq.symm.pos; positivity),
    hpq.inv_add_inv_eq_one, ENNReal.ofReal_one]

theorem eLpNorm_toReal_eq {p : ℝ} (hp : 0 < p) {u : ℝ → ℂ} (hu : MemLp u (ENNReal.ofReal p)) :
    (eLpNorm u (ENNReal.ofReal p) volume).toReal = (∫ x, ‖u x‖ ^ p) ^ (1 / p) := by
  rw [hu.eLpNorm_eq_integral_rpow_norm (by simp [hp]) ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal_eq_iff.mpr (by positivity), ENNReal.toReal_ofReal hp.le, one_div]

/-- **Hölder**: `|∫ u v| ≤ ‖u‖_p ‖v‖_q`. -/
theorem norm_integral_mul_le_holder {p q : ℝ} (hpq : p.HolderConjugate q) {u v : ℝ → ℂ}
    (hu : MemLp u (ENNReal.ofReal p)) (hv : MemLp v (ENNReal.ofReal q)) :
    Integrable (fun x => u x * v x) ∧
      ‖∫ x, u x * v x‖ ≤ (eLpNorm u (ENNReal.ofReal p) volume).toReal *
        (eLpNorm v (ENNReal.ofReal q) volume).toReal := by
  have := holderConjugate_ofReal hpq
  have hi : Integrable fun x => u x * v x := hu.integrable_mul hv
  refine ⟨hi, ?_⟩
  have hun : MemLp (fun x => ‖u x‖) (ENNReal.ofReal p) := hu.norm
  have hvn : MemLp (fun x => ‖v x‖) (ENNReal.ofReal q) := hv.norm
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg hpq (ae_of_all _ fun x => norm_nonneg (u x))
    (ae_of_all _ fun x => norm_nonneg (v x)) hun hvn
  rw [eLpNorm_toReal_eq hpq.pos hu, eLpNorm_toReal_eq hpq.symm.pos hv]
  calc ‖∫ x, u x * v x‖ ≤ ∫ x, ‖u x‖ * ‖v x‖ :=
        (norm_integral_le_integral_norm _).trans (le_of_eq (by simp_rw [norm_mul]))
    _ ≤ _ := h

/-- A measurable function with `|u(x)| ≤ K/(1 + |x|)` is in `L^p` for `p > 1`. -/
theorem memLp_of_decay {p : ℝ} (hp1 : 1 < p) {u : ℝ → ℂ} (hum : AEStronglyMeasurable u volume)
    {K : ℝ} (hK : 0 ≤ K) (hub : ∀ x, ‖u x‖ ≤ K / (1 + |x|)) : MemLp u (ENNReal.ofReal p) := by
  have hp0 : 0 < p := by linarith
  refine (integrable_norm_rpow_iff hum (by simp [hp0]) ENNReal.ofReal_ne_top).mp ?_
  rw [ENNReal.toReal_ofReal hp0.le]
  have hI : Integrable fun x : ℝ => (1 + ‖x‖) ^ (-p) := integrable_one_add_norm (by simpa using hp1)
  refine (hI.const_mul (K ^ p)).mono' ((Real.continuous_rpow_const hp0.le
    ).comp_aestronglyMeasurable hum.norm) (ae_of_all _ fun x => ?_)
  rw [Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _), Real.norm_eq_abs]
  have h1 : 0 < 1 + |x| := by positivity
  calc ‖u x‖ ^ p ≤ (K / (1 + |x|)) ^ p := Real.rpow_le_rpow (norm_nonneg _) (hub x) hp0.le
    _ = K ^ p * (1 + |x|) ^ (-p) := by
        rw [Real.div_rpow hK h1.le, Real.rpow_neg h1.le, div_eq_mul_inv]

/-! ### The two-term dense bound -/

/-- Continuous compactly supported real functions: the data of the dense class. -/
structure DenseDatum where
  /-- the function -/
  g : ℝ → ℝ
  /-- the Poisson parameter -/
  b : ℝ
  continuous : Continuous g
  compactSupport : HasCompactSupport g
  pos : 0 < b

namespace DenseDatum

variable (d : DenseDatum)

/-- `g` as a complex function. -/
noncomputable def gC : ℝ → ℂ := fun t => (d.g t : ℂ)

/-- `P_b g`. -/
noncomputable def P : ℝ → ℂ := poissonInt d.b d.gC

/-- `Q_b g`. -/
noncomputable def Q : ℝ → ℂ := conjPoissonInt d.b d.gC

theorem continuous_gC : Continuous d.gC := Complex.continuous_ofReal.comp d.continuous

theorem integrable : Integrable d.gC :=
  d.continuous_gC.integrable_of_hasCompactSupport
    (d.compactSupport.comp_left (g := ((↑) : ℝ → ℂ)) ofReal_zero)

theorem support_bound : ∃ M, 0 ≤ M ∧ ∀ t : ℝ, M < |t| → d.gC t = 0 :=
  exists_support_bound (d.compactSupport.comp_left (g := ((↑) : ℝ → ℂ)) ofReal_zero)

/-- The holomorphic extension `F = P − iQ` on the boundary. -/
noncomputable def F : ℂ → ℂ := cauchyExt d.b d.gC

theorem F_bounds : ∃ K, 0 ≤ K ∧ (∀ z : ℂ, 0 ≤ z.im → ‖d.F z‖ ≤ K / (1 + ‖z‖)) ∧
    (∀ z : ℂ, 0 ≤ z.im → ‖deriv d.F z‖ ≤ K / (1 + ‖z‖) ^ 2) := by
  obtain ⟨M, hM, hMs⟩ := d.support_bound
  obtain ⟨h1, h2⟩ := cauchyExt_bounds d.integrable d.pos hM hMs
  refine ⟨_, ?_, h1, h2⟩
  have : 0 ≤ ∫ t, ‖d.gC t‖ := integral_nonneg fun _ => norm_nonneg _
  have := d.pos
  have := Real.pi_pos
  positivity

theorem differentiableOn_F : DifferentiableOn ℂ d.F {z | -d.b < z.im} :=
  differentiableOn_cauchyExt d.integrable d.b

theorem P_real (x : ℝ) : d.P x = ((d.P x).re : ℂ) := by
  show poissonInt d.b (fun t => (d.g t : ℂ)) x = (poissonInt d.b (fun t => (d.g t : ℂ)) x).re
  rw [poissonInt_ofReal, ofReal_re]

theorem Q_real (x : ℝ) : d.Q x = ((d.Q x).re : ℂ) := by
  show conjPoissonInt d.b (fun t => (d.g t : ℂ)) x =
    (conjPoissonInt d.b (fun t => (d.g t : ℂ)) x).re
  rw [conjPoissonInt_ofReal, ofReal_re]

theorem F_ofReal (x : ℝ) : d.F x = d.P x - I * d.Q x :=
  cauchyExt_ofReal d.integrable d.pos x

theorem F_re (x : ℝ) : (d.F x).re = (d.P x).re := by
  rw [F_ofReal, d.Q_real x]; simp

theorem F_im (x : ℝ) : (d.F x).im = -(d.Q x).re := by
  rw [F_ofReal, d.P_real x, d.Q_real x]; simp

theorem continuous_P : Continuous d.P := by
  have hc := (differentiableOn_F d).continuousOn.comp_continuous continuous_ofReal
    (fun x => by simp [d.pos])
  have : d.P = fun x : ℝ => (((d.F (x : ℂ)).re : ℝ) : ℂ) := funext fun x => by
    rw [d.F_re, ← d.P_real]
  rw [this]; exact Complex.continuous_ofReal.comp (Complex.continuous_re.comp hc)

theorem continuous_Q : Continuous d.Q := continuous_conjPoissonInt d.pos d.integrable

end DenseDatum

/-- For two data, `F₁ − F₂` satisfies the hypotheses of `integral_im_rpow_le`; hence
`∫ |Q₁ − Q₂|^p ≤ tan^p(π/2p) ∫ |P₁ − P₂|^p` for `1 < p ≤ 2`. -/
theorem integral_conjPoisson_sub_rpow_le {p : ℝ} (hp1 : 1 < p) (hp2 : p ≤ 2) (d₁ d₂ : DenseDatum) :
    Integrable (fun x => ‖d₁.P x - d₂.P x‖ ^ p) ∧ Integrable (fun x => ‖d₁.Q x - d₂.Q x‖ ^ p) ∧
      ∫ x, ‖d₁.Q x - d₂.Q x‖ ^ p ≤ pichoridesA p ^ p * ∫ x, ‖d₁.P x - d₂.P x‖ ^ p := by
  obtain ⟨K₁, hK₁, hb₁, hd₁⟩ := d₁.F_bounds
  obtain ⟨K₂, hK₂, hb₂, hd₂⟩ := d₂.F_bounds
  set c := min d₁.b d₂.b with hc
  have hc0 : 0 < c := lt_min d₁.pos d₂.pos
  have hU₁ : {z : ℂ | -c < z.im} ⊆ {z | -d₁.b < z.im} := fun z hz => by
    simp only [Set.mem_ofPred_eq] at hz ⊢; linarith [min_le_left d₁.b d₂.b]
  have hU₂ : {z : ℂ | -c < z.im} ⊆ {z | -d₂.b < z.im} := fun z hz => by
    simp only [Set.mem_ofPred_eq] at hz ⊢; linarith [min_le_right d₁.b d₂.b]
  set F := fun z => d₁.F z - d₂.F z with hF
  have hFd : DifferentiableOn ℂ F {z | -c < z.im} :=
    (d₁.differentiableOn_F.mono hU₁).sub (d₂.differentiableOn_F.mono hU₂)
  have hFb : ∀ z : ℂ, 0 ≤ z.im → ‖F z‖ ≤ (K₁ + K₂) / (1 + ‖z‖) := fun z hz => by
    rw [add_div]; exact (norm_sub_le _ _).trans (add_le_add (hb₁ z hz) (hb₂ z hz))
  have hF'b : ∀ z : ℂ, 0 ≤ z.im → ‖deriv F z‖ ≤ (K₁ + K₂) / (1 + ‖z‖) ^ 2 := fun z hz => by
    have hUo : IsOpen {z : ℂ | -c < z.im} := isOpen_lt continuous_const continuous_im
    have hz' : z ∈ {z : ℂ | -c < z.im} := by simp only [Set.mem_ofPred_eq]; linarith
    have h1 := (d₁.differentiableOn_F.mono hU₁).differentiableAt (hUo.mem_nhds hz')
    have h2 := (d₂.differentiableOn_F.mono hU₂).differentiableAt (hUo.mem_nhds hz')
    have hd : deriv (fun z => d₁.F z - d₂.F z) z = deriv d₁.F z - deriv d₂.F z :=
      (h1.hasDerivAt.sub h2.hasDerivAt).deriv
    rw [hF, hd, add_div]
    exact (norm_sub_le _ _).trans (add_le_add (hd₁ z hz) (hd₂ z hz))
  obtain ⟨h1, h2, h3⟩ := integral_im_rpow_le hp1 hp2 hc0 hFd (by positivity) hFb hF'b
  have hre : ∀ x : ℝ, |(F x).re| ^ p = ‖d₁.P x - d₂.P x‖ ^ p := fun x => by
    rw [hF, sub_re, d₁.F_re, d₂.F_re, d₁.P_real x, d₂.P_real x, ← ofReal_sub, Complex.norm_real,
      Real.norm_eq_abs]
    simp
  have him : ∀ x : ℝ, |(F x).im| ^ p = ‖d₁.Q x - d₂.Q x‖ ^ p := fun x => by
    rw [hF, sub_im, d₁.F_im, d₂.F_im, d₁.Q_real x, d₂.Q_real x, ← ofReal_sub, Complex.norm_real,
      Real.norm_eq_abs]
    simp only [ofReal_re]
    rw [show -(d₁.Q x).re - -(d₂.Q x).re = -((d₁.Q x).re - (d₂.Q x).re) by ring, abs_neg]
  simp_rw [hre, him] at h1 h2 h3
  exact ⟨h1, h2, h3⟩

namespace DenseDatum

variable (d : DenseDatum)

theorem norm_P_le (x : ℝ) : ‖d.P x‖ ≤ ‖d.F x‖ := by
  rw [d.P_real x, Complex.norm_real, Real.norm_eq_abs, ← d.F_re]; exact abs_re_le_norm _

theorem norm_Q_le (x : ℝ) : ‖d.Q x‖ ≤ ‖d.F x‖ := by
  rw [d.Q_real x, Complex.norm_real, Real.norm_eq_abs, ← abs_neg, ← d.F_im]
  exact abs_im_le_norm _

theorem memLp_P {p : ℝ} (hp1 : 1 < p) : MemLp d.P (ENNReal.ofReal p) := by
  obtain ⟨K, hK, hb, -⟩ := d.F_bounds
  refine memLp_of_decay hp1 d.continuous_P.aestronglyMeasurable hK fun x => ?_
  have := hb x (by simp)
  rw [Complex.norm_real, Real.norm_eq_abs] at this
  exact (d.norm_P_le x).trans this

theorem memLp_Q {p : ℝ} (hp1 : 1 < p) : MemLp d.Q (ENNReal.ofReal p) := by
  obtain ⟨K, hK, hb, -⟩ := d.F_bounds
  refine memLp_of_decay hp1 d.continuous_Q.aestronglyMeasurable hK fun x => ?_
  have := hb x (by simp)
  rw [Complex.norm_real, Real.norm_eq_abs] at this
  exact (d.norm_Q_le x).trans this

end DenseDatum

/-- The bound `‖Q₁ − Q₂‖_p ≤ A ‖P₁ − P₂‖_p` on the dense class. -/
def DenseBound (p A : ℝ) : Prop :=
  ∀ d₁ d₂ : DenseDatum, eLpNorm (fun x => d₁.Q x - d₂.Q x) (ENNReal.ofReal p) volume ≤
    ENNReal.ofReal A * eLpNorm (fun x => d₁.P x - d₂.P x) (ENNReal.ofReal p) volume

theorem pichoridesA_pos {p : ℝ} (hp1 : 1 < p) : 0 < pichoridesA p := by
  obtain ⟨h0, h1⟩ := pichorides_theta0_mem hp1
  exact Real.tan_pos_of_pos_of_lt_pi_div_two h0 h1

/-- **The dense bound for `1 < p ≤ 2`** with Pichorides' constant `tan(π/2p)`. -/
theorem denseBound_of_le_two {p : ℝ} (hp1 : 1 < p) (hp2 : p ≤ 2) :
    DenseBound p (pichoridesA p) := by
  intro d₁ d₂
  have hp0 : 0 < p := by linarith
  obtain ⟨-, -, h3⟩ := integral_conjPoisson_sub_rpow_le hp1 hp2 d₁ d₂
  have hQ := (d₁.memLp_Q hp1).sub (d₂.memLp_Q hp1)
  have hP := (d₁.memLp_P hp1).sub (d₂.memLp_P hp1)
  have hA := (pichoridesA_pos hp1).le
  rw [show (fun x => d₁.Q x - d₂.Q x) = d₁.Q - d₂.Q from rfl,
    show (fun x => d₁.P x - d₂.P x) = d₁.P - d₂.P from rfl,
    hQ.eLpNorm_eq_integral_rpow_norm (by simp [hp0]) ENNReal.ofReal_ne_top,
    hP.eLpNorm_eq_integral_rpow_norm (by simp [hp0]) ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal hp0.le, ← ENNReal.ofReal_mul hA]
  refine ENNReal.ofReal_le_ofReal ?_
  have hIP : 0 ≤ ∫ x, ‖(d₁.P - d₂.P) x‖ ^ p :=
    integral_nonneg fun x => Real.rpow_nonneg (norm_nonneg _) _
  calc (∫ x, ‖(d₁.Q - d₂.Q) x‖ ^ p) ^ p⁻¹ ≤
      (pichoridesA p ^ p * ∫ x, ‖(d₁.P - d₂.P) x‖ ^ p) ^ p⁻¹ :=
        Real.rpow_le_rpow (integral_nonneg fun x => Real.rpow_nonneg (norm_nonneg _) _) h3
          (by positivity)
    _ = pichoridesA p * (∫ x, ‖(d₁.P - d₂.P) x‖ ^ p) ^ p⁻¹ := by
        rw [Real.mul_rpow (Real.rpow_nonneg hA _) hIP, ← Real.rpow_mul hA,
          mul_inv_cancel₀ hp0.ne', Real.rpow_one]

/-! ### Kernel estimates and weighted integrability -/

theorem one_add_abs_mul_qK_le {ε : ℝ} (hε : 0 < ε) (s : ℝ) :
    (1 + |s|) * |qK ε s| ≤ (1 / ε + 1) / π := by
  have hπ := Real.pi_pos
  have hD : 0 < s ^ 2 + ε ^ 2 := by positivity
  rw [qK, abs_div, abs_of_pos (by positivity : 0 < π * (s ^ 2 + ε ^ 2)), mul_div_assoc',
    div_le_div_iff₀ (by positivity) hπ]
  have h1 : |s| ≤ (s ^ 2 + ε ^ 2) / (2 * ε) := by
    rw [le_div_iff₀ (by positivity)]; nlinarith [sq_abs s, sq_nonneg (|s| - ε)]
  have h2 : |s| * |s| ≤ s ^ 2 + ε ^ 2 := by nlinarith [sq_abs s]
  have : (1 + |s|) * |s| ≤ (1 / ε + 1) * (s ^ 2 + ε ^ 2) := by
    have e : (1 / ε) * (s ^ 2 + ε ^ 2) = (s ^ 2 + ε ^ 2) / ε := by ring
    nlinarith [div_le_div_of_nonneg_left (by positivity : 0 ≤ s ^ 2 + ε ^ 2)
      (by positivity : 0 < ε) (by linarith : ε ≤ 2 * ε)]
  nlinarith

theorem one_add_abs_mul_pK_le {ε : ℝ} (hε : 0 < ε) (s : ℝ) :
    (1 + |s|) * pK ε s ≤ (1 / ε + 1) / π := by
  have hπ := Real.pi_pos
  rw [pK, mul_div_assoc', div_le_div_iff₀ (by positivity) hπ]
  have h1 : ε * |s| ≤ s ^ 2 + ε ^ 2 := by nlinarith [sq_abs s, sq_nonneg (|s| - ε)]
  have h2 : ε ≤ (1 / ε) * (s ^ 2 + ε ^ 2) := by
    rw [one_div_mul_eq_div, le_div_iff₀ hε]; nlinarith [sq_nonneg s]
  nlinarith

theorem one_add_abs_le_mul (x t : ℝ) : 1 + |t| ≤ (1 + |x|) * (1 + |t - x|) := by
  have := abs_sub_abs_le_abs_sub t x
  nlinarith [abs_nonneg x, abs_nonneg (t - x)]

theorem memLp_qK_sub {q : ℝ} (hq1 : 1 < q) {ε : ℝ} (hε : 0 < ε) (x : ℝ) :
    MemLp (fun t => ((qK ε (t - x) : ℝ) : ℂ)) (ENNReal.ofReal q) := by
  refine memLp_of_decay hq1 ((Complex.continuous_ofReal.comp ((continuous_qK hε).comp
    (continuous_id.sub continuous_const))).aestronglyMeasurable)
    (K := (1 + |x|) * ((1 / ε + 1) / π)) (by have := Real.pi_pos; positivity) fun t => ?_
  rw [Complex.norm_real, Real.norm_eq_abs, le_div_iff₀ (by positivity)]
  have h1 := one_add_abs_mul_qK_le hε (t - x)
  have h2 := one_add_abs_le_mul x t
  nlinarith [abs_nonneg (qK ε (t - x)), abs_nonneg x]

theorem memLp_pK_sub {q : ℝ} (hq1 : 1 < q) {ε : ℝ} (hε : 0 < ε) (x : ℝ) :
    MemLp (fun t => ((pK ε (t - x) : ℝ) : ℂ)) (ENNReal.ofReal q) := by
  refine memLp_of_decay hq1 ((Complex.continuous_ofReal.comp ((continuous_pK hε).comp
    (continuous_id.sub continuous_const))).aestronglyMeasurable)
    (K := (1 + |x|) * ((1 / ε + 1) / π)) (by have := Real.pi_pos; positivity) fun t => ?_
  rw [Complex.norm_real, Real.norm_of_nonneg (pK_nonneg hε _), le_div_iff₀ (by positivity)]
  have h1 := one_add_abs_mul_pK_le hε (t - x)
  have h2 := one_add_abs_le_mul x t
  nlinarith [pK_nonneg hε (t - x), abs_nonneg x]

/-- `L^p` functions (`p > 1`) are integrable against `1/(1 + |t|)`. -/
theorem integrable_div_one_add_abs {p q : ℝ} (hpq : p.HolderConjugate q) {u : ℝ → ℂ}
    (hu : MemLp u (ENNReal.ofReal p)) : Integrable fun t => ‖u t‖ / (1 + |t|) := by
  have hk : MemLp (fun t : ℝ => (((1 + |t|)⁻¹ : ℝ) : ℂ)) (ENNReal.ofReal q) :=
    memLp_of_decay hpq.symm.lt (Complex.continuous_ofReal.comp
      ((by fun_prop : Continuous fun t : ℝ => 1 + |t|).inv₀ fun t => by positivity)
      ).aestronglyMeasurable zero_le_one fun t => by
        rw [Complex.norm_real, Real.norm_of_nonneg (by positivity), one_div]
  have := (norm_integral_mul_le_holder hpq hu hk).1.norm
  refine this.congr (ae_of_all _ fun t => ?_)
  simp only
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity), div_eq_mul_inv]

theorem integrable_div_one_add_sq_of_abs {u : ℝ → ℂ} (hum : AEStronglyMeasurable u volume)
    (hu : Integrable fun t => ‖u t‖ / (1 + |t|)) : Integrable fun t => ‖u t‖ / (1 + t ^ 2) := by
  refine (hu.const_mul 2).mono' (hum.norm.mul (Continuous.inv₀ (by fun_prop : Continuous
    fun t : ℝ => 1 + t ^ 2) fun t => by positivity).aestronglyMeasurable |>.congr
    (ae_of_all _ fun t => (div_eq_mul_inv _ _).symm)) (ae_of_all _ fun t => ?_)
  rw [Real.norm_of_nonneg (by positivity), mul_div_assoc', div_le_div_iff₀ (by positivity)
    (by positivity)]
  have : 1 + |t| ≤ 2 * (1 + t ^ 2) := by nlinarith [sq_abs t, sq_nonneg (|t| - 1)]
  nlinarith [mul_le_mul_of_nonneg_left this (norm_nonneg (u t))]

/-! ### The Hilbert transform at Lebesgue points -/

theorem integrable_translate_weight {u : ℝ → ℂ} (hum : AEStronglyMeasurable u volume)
    (hw : Integrable fun t => ‖u t‖ / (1 + |t|)) (x : ℝ) (σ : ℝ) (hσ : σ = 1 ∨ σ = -1) :
    Integrable fun s => ‖u (x + σ * s)‖ / (1 + |s|) := by
  have hcomp : Integrable fun s => ‖u (x + σ * s)‖ / (1 + |x + σ * s|) := by
    rcases hσ with rfl | rfl
    · simpa using hw.comp_add_left x
    · simpa [← sub_eq_add_neg] using hw.comp_sub_left x
  have hm : AEStronglyMeasurable (fun s => u (x + σ * s)) volume := by
    rcases hσ with rfl | rfl
    · exact (hum.comp_quasiMeasurePreserving (quasiMeasurePreserving_add_left volume x)).congr
        (ae_of_all _ fun s => by simp)
    · exact (hum.comp_quasiMeasurePreserving (quasiMeasurePreserving_sub_left volume x)).congr
        (ae_of_all _ fun s => by simp [sub_eq_add_neg])
  refine (hcomp.const_mul (1 + |x|)).mono' (hm.norm.mul (Continuous.inv₀ (by fun_prop :
    Continuous fun s : ℝ => 1 + |s|) fun s => by positivity).aestronglyMeasurable |>.congr
    (ae_of_all _ fun s => (div_eq_mul_inv _ _).symm)) (ae_of_all _ fun s => ?_)
  have hσ1 : |σ| = 1 := by rcases hσ with rfl | rfl <;> simp
  rw [Real.norm_of_nonneg (by positivity), mul_div_assoc', div_le_div_iff₀ (by positivity)
    (by positivity)]
  have : 1 + |x + σ * s| ≤ (1 + |x|) * (1 + |s|) := by
    have := abs_add_le x (σ * s); rw [abs_mul, hσ1, one_mul] at this
    nlinarith [abs_nonneg x, abs_nonneg s]
  nlinarith [mul_le_mul_of_nonneg_left this (norm_nonneg (u (x + σ * s)))]

theorem integrableOn_hilbert_of_weighted {u : ℝ → ℂ} (hum : AEStronglyMeasurable u volume)
    (hw : Integrable fun t => ‖u t‖ / (1 + |t|)) (x : ℝ) {ε : ℝ} (hε : 0 < ε) :
    IntegrableOn (fun t : ℝ => (u (x + t) - u (x - t)) / t) (Ioi ε) := by
  have h1 := integrable_translate_weight hum hw x 1 (Or.inl rfl)
  have h2 := integrable_translate_weight hum hw x (-1) (Or.inr rfl)
  simp only [one_mul, neg_one_mul, ← sub_eq_add_neg] at h1 h2
  have hm : AEStronglyMeasurable (fun t => u (x + t) - u (x - t)) volume :=
    (hum.comp_quasiMeasurePreserving (quasiMeasurePreserving_add_left volume x)).sub
      (hum.comp_quasiMeasurePreserving (quasiMeasurePreserving_sub_left volume x))
  refine ((h1.add h2).const_mul ((1 + ε) / ε)).integrableOn.mono'
    (hm.restrict.mul (by fun_prop : Measurable fun t : ℝ => (t : ℂ)⁻¹).aestronglyMeasurable)
    ((ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ fun t ht => ?_))
  have ht0 : 0 < t := hε.trans ht
  have hεt : ε < t := ht
  have hts : (1 + |t|) / t ≤ (1 + ε) / ε := by
    rw [abs_of_pos ht0, div_le_div_iff₀ ht0 hε]; nlinarith
  simp only [Pi.add_apply]
  rw [norm_div, Complex.norm_real, Real.norm_of_nonneg ht0.le]
  calc ‖u (x + t) - u (x - t)‖ / t ≤ (‖u (x + t)‖ + ‖u (x - t)‖) / t :=
        div_le_div_of_nonneg_right (norm_sub_le _ _) ht0.le
    _ = (1 + |t|) / t * (‖u (x + t)‖ / (1 + |t|) + ‖u (x - t)‖ / (1 + |t|)) := by
        field_simp
    _ ≤ (1 + ε) / ε * (‖u (x + t)‖ / (1 + |t|) + ‖u (x - t)‖ / (1 + |t|)) :=
        mul_le_mul_of_nonneg_right hts (by positivity)

theorem integrable_kernel_mul_translate {u : ℝ → ℂ} (hum : AEStronglyMeasurable u volume)
    (hw : Integrable fun t => ‖u t‖ / (1 + |t|)) (x : ℝ) {k : ℝ → ℝ} (hk : Continuous k) {C : ℝ}
    (hkC : ∀ s, (1 + |s|) * |k s| ≤ C) : Integrable fun s => (k s : ℂ) * u (x + s) := by
  have h1 := integrable_translate_weight hum hw x 1 (Or.inl rfl)
  simp only [one_mul] at h1
  have hm : AEStronglyMeasurable (fun s => u (x + s)) volume :=
    (hum.comp_quasiMeasurePreserving (quasiMeasurePreserving_add_left volume x)).congr
      (ae_of_all _ fun s => rfl)
  refine (h1.const_mul C).mono' ((Complex.continuous_ofReal.comp hk).aestronglyMeasurable.mul hm)
    (ae_of_all _ fun s => ?_)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_div_assoc', le_div_iff₀ (by positivity)]
  nlinarith [mul_le_mul_of_nonneg_right (hkC s) (norm_nonneg (u (x + s)))]

theorem conjPoissonInt_eq_halves {u : ℝ → ℂ} (hum : AEStronglyMeasurable u volume)
    (hw : Integrable fun t => ‖u t‖ / (1 + |t|)) {ε : ℝ} (hε : 0 < ε) (x : ℝ) :
    conjPoissonInt ε u x = ∫ s in Ioi 0, (qK ε s : ℂ) * (u (x + s) - u (x - s)) := by
  have hi := integrable_kernel_mul_translate hum hw x (continuous_qK hε)
    (one_add_abs_mul_qK_le hε)
  rw [conjPoissonInt_eq_qK, show (fun t => (qK ε (t - x) : ℂ) * u t) =
    fun t => (fun s => (qK ε s : ℂ) * u (x + s)) (t - x) from funext fun t => by
      simp only [add_sub_cancel],
    integral_sub_right_eq_self (fun s => (qK ε s : ℂ) * u (x + s)) x, integral_eq_halves hi]
  refine setIntegral_congr_fun measurableSet_Ioi fun s _ => ?_
  simp only [qK_neg, ← sub_eq_add_neg]
  push_cast; ring

/-- The difference kernel `1_{s>ε}/(πs) − q_ε(s)` is bounded by `(2/π) ε/(ε² + s²)` on `s > 0`. -/
theorem abs_kappa_le {ε s : ℝ} (hε : 0 < ε) (hs : 0 < s) :
    |(Ioi ε).indicator (fun s => (π * s)⁻¹) s - qK ε s| ≤ 2 / π * (ε / (ε ^ 2 + s ^ 2)) := by
  have hπ := Real.pi_pos
  rcases le_or_gt s ε with h | h
  · rw [indicator_of_notMem (by simpa using h), zero_sub, abs_neg, qK,
      abs_of_nonneg (by positivity)]
    rw [div_le_iff₀ (by positivity)]
    field_simp
    nlinarith [mul_pos hπ hε]
  · rw [indicator_of_mem (by simpa using h), qK]
    have : (π * s)⁻¹ - s / (π * (s ^ 2 + ε ^ 2)) = ε ^ 2 / (π * s * (s ^ 2 + ε ^ 2)) := by
      field_simp; ring
    rw [this, abs_of_nonneg (by positivity), div_le_iff₀ (by positivity)]
    field_simp
    nlinarith [mul_pos (mul_pos hπ hε) (mul_pos hs (by positivity : 0 < s ^ 2 + ε ^ 2))]

theorem one_add_abs_mul_kernel_le {ε : ℝ} (hε : 0 < ε) (s : ℝ) :
    (1 + |s|) * |ε / (ε ^ 2 + s ^ 2)| ≤ 1 / ε + 1 := by
  have h := one_add_abs_mul_pK_le hε s
  have hπ := Real.pi_pos
  have he : ε / (ε ^ 2 + s ^ 2) = π * pK ε s := by rw [pK]; field_simp; ring
  rw [he, abs_of_nonneg (mul_nonneg hπ.le (pK_nonneg hε _))]
  rw [le_div_iff₀ hπ] at h
  nlinarith

/-- `|P_ε h(x) − h(x)| ≤ (1/π) ∫ ε/(ε² + s²) |h(x + s) − h(x)| ds` for weighted `h`. -/
theorem norm_poissonInt_sub_le' {h : ℝ → ℂ} (hhm : AEStronglyMeasurable h volume)
    (hw : Integrable fun t => ‖h t‖ / (1 + |t|)) {ε : ℝ} (hε : 0 < ε) (x : ℝ) :
    ‖poissonInt ε h x - h x‖ ≤ π⁻¹ * ∫ s, ε / (ε ^ 2 + s ^ 2) * ‖h (x + s) - h x‖ := by
  have hpi : Integrable fun s => (pK ε s : ℂ) := (integrable_pK hε).ofReal
  have hpg := integrable_kernel_mul_translate hhm hw x (continuous_pK hε) (C := (1 / ε + 1) / π)
    fun s => by rw [abs_of_nonneg (pK_nonneg hε s)]; exact one_add_abs_mul_pK_le hε s
  have h1 : poissonInt ε h x - h x = ∫ s, (pK ε s : ℂ) * (h (x + s) - h x) := by
    rw [poissonInt_eq_pK, show (fun t => (pK ε (t - x) : ℂ) * h t) =
      fun t => (fun s => (pK ε s : ℂ) * h (x + s)) (t - x) from funext fun t => by
        simp only [add_sub_cancel],
      integral_sub_right_eq_self (fun s => (pK ε s : ℂ) * h (x + s)) x]
    simp_rw [mul_sub]
    rw [integral_sub hpg (hpi.mul_const _), integral_mul_const, integral_complex_ofReal,
      integral_pK hε, ofReal_one, one_mul]
  rw [h1, ← integral_const_mul]
  refine (norm_integral_le_integral_norm _).trans (le_of_eq (integral_congr_ae
    (ae_of_all _ fun s => ?_)))
  simp only
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (pK_nonneg hε _), pK]
  field_simp
  ring

theorem norm_tail_sub_conjPoissonInt_le {u : ℝ → ℂ} (hum : AEStronglyMeasurable u volume)
    (hw : Integrable fun t => ‖u t‖ / (1 + |t|)) {ε : ℝ} (hε : 0 < ε) (x : ℝ) :
    ‖(π : ℂ)⁻¹ * (∫ t in Ioi ε, (u (x + t) - u (x - t)) / t) - conjPoissonInt ε u x‖ ≤
      2 / π * ∫ s, ε / (ε ^ 2 + s ^ 2) * ‖u (x + s) - u x‖ := by
  have hπ := Real.pi_pos
  set v : ℝ → ℂ := fun s => u (x + s) - u (x - s) with hv
  set w : ℝ → ℝ := fun s => ‖u (x + s) - u x‖ with hw'
  set κ : ℝ → ℝ := fun s => (Ioi ε).indicator (fun s => (π * s)⁻¹) s with hκ
  set k : ℝ → ℝ := fun s => ε / (ε ^ 2 + s ^ 2) with hk
  have hum1 : AEStronglyMeasurable (fun s => u (x + s)) volume :=
    (hum.comp_quasiMeasurePreserving (quasiMeasurePreserving_add_left volume x)).congr
      (ae_of_all _ fun s => rfl)
  have hum2 : AEStronglyMeasurable (fun s => u (x - s)) volume :=
    (hum.comp_quasiMeasurePreserving (quasiMeasurePreserving_sub_left volume x)).congr
      (ae_of_all _ fun s => rfl)
  -- the tail as an integral over `(0, ∞)`
  have hT : (π : ℂ)⁻¹ * (∫ t in Ioi ε, v t / t) = ∫ s in Ioi 0, (κ s : ℂ) * v s := by
    rw [← integral_const_mul]
    have : (fun s => (κ s : ℂ) * v s) = (Ioi ε).indicator fun s => (π : ℂ)⁻¹ * (v s / s) :=
      funext fun s => by
        by_cases hs : s ∈ Ioi ε
        · simp only [hκ, indicator_of_mem hs]
          push_cast; field_simp
        · simp [hκ, indicator_of_notMem hs]
    rw [this, setIntegral_indicator measurableSet_Ioi,
      inter_eq_right.mpr (Ioi_subset_Ioi hε.le)]
  have hTi : IntegrableOn (fun s => (κ s : ℂ) * v s) (Ioi 0) := by
    have := ((integrableOn_hilbert_of_weighted hum hw x hε).const_mul (π : ℂ)⁻¹)
    have h2 : (fun s => (κ s : ℂ) * v s) = (Ioi ε).indicator fun s => (π : ℂ)⁻¹ * (v s / s) :=
      funext fun s => by
        by_cases hs : s ∈ Ioi ε
        · simp only [hκ, indicator_of_mem hs]
          push_cast; field_simp
        · simp [hκ, indicator_of_notMem hs]
    rw [h2]
    exact (IntegrableOn.integrable_indicator this measurableSet_Ioi).integrableOn
  have hQ := conjPoissonInt_eq_halves hum hw hε x
  have hq1 := integrable_kernel_mul_translate hum hw x (continuous_qK hε)
    (one_add_abs_mul_qK_le hε)
  have hq2 : Integrable fun s => (qK ε s : ℂ) * u (x - s) := by
    have := integrable_translate_weight hum hw x (-1) (Or.inr rfl)
    simp only [neg_one_mul, ← sub_eq_add_neg] at this
    refine (this.const_mul ((1 / ε + 1) / π)).mono' ((Complex.continuous_ofReal.comp
      (continuous_qK hε)).aestronglyMeasurable.mul hum2) (ae_of_all _ fun s => ?_)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_div_assoc', le_div_iff₀ (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_right (one_add_abs_mul_qK_le hε s) (norm_nonneg (u (x - s)))]
  have hQi : IntegrableOn (fun s => (qK ε s : ℂ) * v s) (Ioi 0) :=
    ((hq1.sub hq2).congr (ae_of_all _ fun s => by simp only [hv, Pi.sub_apply]; ring)).integrableOn
  -- the weighted kernel is integrable against `w`
  have hkc : Continuous k := by
    simp only [hk]; exact continuous_const.div (by fun_prop) fun s => by positivity
  have hkw : Integrable fun s => k s * w s := by
    have h1 := integrable_kernel_mul_translate hum hw x (k := k) hkc
      (one_add_abs_mul_kernel_le hε)
    have h2 : Integrable fun s => k s * ‖u x‖ := (integrable_poissonKernel hε).mul_const _
    refine (h1.norm.add h2).mono' (hkc.aestronglyMeasurable.mul
      ((hum1.sub aestronglyMeasurable_const).norm)) (ae_of_all _ fun s => ?_)
    have hk0 : 0 ≤ k s := by simp only [hk]; positivity
    rw [Real.norm_of_nonneg (mul_nonneg hk0 (norm_nonneg _)), Pi.add_apply, norm_mul,
      Complex.norm_real, Real.norm_of_nonneg hk0]
    calc k s * w s ≤ k s * (‖u (x + s)‖ + ‖u x‖) :=
          mul_le_mul_of_nonneg_left (norm_sub_le _ _) hk0
      _ = k s * ‖u (x + s)‖ + k s * ‖u x‖ := by ring
  simp only [hv] at hT hTi hQi
  rw [hT, hQ, ← integral_sub hTi hQi]
  have hbound : ∀ s ∈ Ioi (0 : ℝ),
      ‖(κ s : ℂ) * (u (x + s) - u (x - s)) - (qK ε s : ℂ) * (u (x + s) - u (x - s))‖ ≤
        2 / π * (k s * w s + k (-s) * w (-s)) := fun s hs => by
    have hκb : |κ s - qK ε s| ≤ 2 / π * k s := abs_kappa_le hε hs
    have hv' : ‖u (x + s) - u (x - s)‖ ≤ w s + w (-s) := by
      simp only [hw', ← sub_eq_add_neg]
      calc ‖u (x + s) - u (x - s)‖ = ‖(u (x + s) - u x) - (u (x - s) - u x)‖ := by ring_nf
        _ ≤ _ := norm_sub_le _ _
    have hks : k (-s) = k s := by simp [hk]
    have hk0 : 0 ≤ 2 / π * k s := by
      have : 0 ≤ k s := by simp only [hk]; positivity
      positivity
    rw [← sub_mul, ← ofReal_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs, hks]
    calc |κ s - qK ε s| * ‖u (x + s) - u (x - s)‖ ≤ (2 / π * k s) * (w s + w (-s)) :=
          mul_le_mul hκb hv' (norm_nonneg _) hk0
      _ = 2 / π * (k s * w s + k s * w (-s)) := by ring
  have hbi : IntegrableOn (fun s => 2 / π * (k s * w s + k (-s) * w (-s))) (Ioi 0) :=
    ((hkw.add hkw.comp_neg).const_mul _).integrableOn
  calc ‖∫ s in Ioi 0, (κ s : ℂ) * (u (x + s) - u (x - s)) -
        (qK ε s : ℂ) * (u (x + s) - u (x - s))‖
      ≤ ∫ s in Ioi 0, 2 / π * (k s * w s + k (-s) * w (-s)) :=
        norm_integral_le_of_norm_le hbi ((ae_restrict_iff' measurableSet_Ioi).mpr
          (ae_of_all _ hbound))
    _ = 2 / π * ∫ s, k s * w s := by
        rw [integral_const_mul, integral_eq_halves hkw]

/-- **The Hilbert transform at Lebesgue points.** If `u` and `h` are measurable with
`∫ |·|/(1 + |t|) < ∞`, `x` is a Lebesgue point of both in the Poisson sense, and
`Q_ε u(x) = P_ε h(x)` for all `ε > 0`, then `ℋu(x)` exists and equals `h(x)`. -/
theorem hasHilbert_of_lebesgue {u h : ℝ → ℂ} (hum : AEStronglyMeasurable u volume)
    (hw : Integrable fun t => ‖u t‖ / (1 + |t|)) (hhm : AEStronglyMeasurable h volume)
    (hwh : Integrable fun t => ‖h t‖ / (1 + |t|)) {x : ℝ}
    (hLu : Tendsto (fun ε => ∫ s, ε / (ε ^ 2 + s ^ 2) * ‖u (x + s) - u x‖) (𝓝[>] 0) (𝓝 0))
    (hLh : Tendsto (fun ε => ∫ s, ε / (ε ^ 2 + s ^ 2) * ‖h (x + s) - h x‖) (𝓝[>] 0) (𝓝 0))
    (hQ : ∀ ε, 0 < ε → conjPoissonInt ε u x = poissonInt ε h x) : HasHilbert u x (h x) := by
  set T : ℝ → ℂ := fun ε => (π : ℂ)⁻¹ * ∫ t in Ioi ε, (u (x + t) - u (x - t)) / t with hT
  refine ⟨T, fun ε hε => ?_, ?_⟩
  · exact (intervalIntegral_tendsto_integral_Ioi ε (integrableOn_hilbert_of_weighted hum hw x hε)
      tendsto_id).const_mul _
  have hbound : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ‖T ε - h x‖ ≤
      2 / π * (∫ s, ε / (ε ^ 2 + s ^ 2) * ‖u (x + s) - u x‖) +
        π⁻¹ * ∫ s, ε / (ε ^ 2 + s ^ 2) * ‖h (x + s) - h x‖ := by
    filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
    have h1 := norm_tail_sub_conjPoissonInt_le hum hw hε x
    have h2 := norm_poissonInt_sub_le' hhm hwh hε x
    rw [hQ ε hε] at h1
    calc ‖T ε - h x‖ = ‖(T ε - poissonInt ε h x) + (poissonInt ε h x - h x)‖ := by ring_nf
      _ ≤ _ := (norm_add_le _ _).trans (add_le_add h1 h2)
  have hlim : Tendsto (fun ε => 2 / π * (∫ s, ε / (ε ^ 2 + s ^ 2) * ‖u (x + s) - u x‖) +
      π⁻¹ * ∫ s, ε / (ε ^ 2 + s ^ 2) * ‖h (x + s) - h x‖) (𝓝[>] 0) (𝓝 0) := by
    simpa using (hLu.const_mul (2 / π)).add (hLh.const_mul π⁻¹)
  have := squeeze_zero_norm' hbound hlim
  simpa using this.add_const (h x)

/-! ### Passing to the limit -/

theorem tendsto_integral_mul_of_eLpNorm {p q : ℝ} (hpq : p.HolderConjugate q) {k : ℝ → ℂ}
    (hk : MemLp k (ENNReal.ofReal q)) {u : ℕ → ℝ → ℂ} {u₀ : ℝ → ℂ}
    (hu : ∀ n, MemLp (u n) (ENNReal.ofReal p)) (hu₀ : MemLp u₀ (ENNReal.ofReal p))
    (hlim : Tendsto (fun n => eLpNorm (u n - u₀) (ENNReal.ofReal p) volume) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ t, k t * u n t) atTop (𝓝 (∫ t, k t * u₀ t)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hb : ∀ n, ‖(∫ t, k t * u n t) - ∫ t, k t * u₀ t‖ ≤
      (eLpNorm k (ENNReal.ofReal q) volume).toReal *
        (eLpNorm (u n - u₀) (ENNReal.ofReal p) volume).toReal := fun n => by
    have h1 := norm_integral_mul_le_holder hpq.symm hk (hu n)
    have h2 := norm_integral_mul_le_holder hpq.symm hk hu₀
    have h3 := norm_integral_mul_le_holder hpq.symm hk ((hu n).sub hu₀)
    rw [← integral_sub h1.1 h2.1]
    refine le_of_eq_of_le ?_ h3.2
    congr 1; refine integral_congr_ae (ae_of_all _ fun t => ?_)
    simp only [Pi.sub_apply]; ring
  refine squeeze_zero (fun n => norm_nonneg _) hb ?_
  have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hlim
  simpa using this.const_mul (eLpNorm k (ENNReal.ofReal q) volume).toReal

/-- The datum `g = 0`, with `P = Q = 0`. -/
noncomputable def DenseDatum.zero : DenseDatum where
  g := 0
  b := 1
  continuous := continuous_const
  compactSupport := HasCompactSupport.zero
  pos := one_pos

theorem DenseDatum.zero_P : DenseDatum.zero.P = 0 := funext fun x => by
  simp [DenseDatum.P, DenseDatum.gC, DenseDatum.zero, poissonInt]

theorem DenseDatum.zero_Q : DenseDatum.zero.Q = 0 := funext fun x => by
  simp [DenseDatum.Q, DenseDatum.gC, DenseDatum.zero, conjPoissonInt]

/-- `Q_ε(P_b g) = P_ε(Q_b g)` for a datum. -/
theorem DenseDatum.conjPoissonInt_P (d : DenseDatum) {ε : ℝ} (hε : 0 < ε) (x : ℝ) :
    conjPoissonInt ε d.P x = poissonInt ε d.Q x := by
  rw [DenseDatum.P, DenseDatum.Q, conjPoissonInt_poissonInt hε d.pos d.integrable,
    poissonInt_conjPoissonInt hε d.pos d.integrable]

/-! ### The extension to `L^p` -/

/-- **From the dense class to `L^p`.** If `‖Q₁ − Q₂‖_p ≤ A ‖P₁ − P₂‖_p` on the dense class
(`p > 1`), then for every real `f ∈ L^p` the Hilbert transform `ℋf(x)` exists for almost every
`x`, `ℋf ∈ L^p`, and `‖ℋf‖_p ≤ A ‖f‖_p`. The proof approximates `f` by `P_{bₙ} gₙ`; `Q_{bₙ} gₙ`
is Cauchy in `L^p` with limit `h`; `Q_ε f = P_ε h` by the semigroup identities and Hölder; and at
the common Lebesgue points of `f` and `h`, `ℋf = h` (`hasHilbert_of_lebesgue`). -/
theorem hilbert_Lp_of_denseBound {p A : ℝ} (hp1 : 1 < p) (hA : 0 ≤ A) (hD : DenseBound p A)
    {f : ℝ → ℝ} (hf : MemLp f (ENNReal.ofReal p) volume) :
    (∀ᵐ x, HasHilbert (fun t => (f t : ℂ)) x (hilbert (fun t => (f t : ℂ)) x)) ∧
      MemLp (hilbert fun t => (f t : ℂ)) (ENNReal.ofReal p) volume ∧
      eLpNorm (hilbert fun t => (f t : ℂ)) (ENNReal.ofReal p) volume ≤
        ENNReal.ofReal A * eLpNorm f (ENNReal.ofReal p) volume := by
  set P := ENNReal.ofReal p with hP
  have hpq : p.HolderConjugate p.conjExponent := Real.HolderConjugate.conjExponent hp1
  set q := p.conjExponent
  have hq1 : 1 < q := hpq.symm.lt
  have hP1 : 1 ≤ P := by rw [hP]; exact ENNReal.one_le_ofReal.mpr hp1.le
  set fC : ℝ → ℂ := fun t => (f t : ℂ) with hfC
  have hfCm : MemLp fC P := hf.ofReal
  have hfCn : eLpNorm fC P volume = eLpNorm f P volume :=
    eLpNorm_congr_norm_ae hfCm.aestronglyMeasurable hf.aestronglyMeasurable
      (ae_of_all _ fun x => by simp [hfC])
  -- approximants
  have happrox : ∀ n : ℕ, ∃ d : DenseDatum,
      eLpNorm (fun x => fC x - d.P x) P volume < ENNReal.ofReal ((1 / 2) ^ n) := fun n => by
    obtain ⟨g, hgc, hgs, b, hb, -, hlt⟩ := exists_poissonInt_approx hP1 ENNReal.ofReal_ne_top hf
      (ε := (1 / 2) ^ n) (by positivity)
    exact ⟨⟨g, b, hgc, hgs, hb⟩, hlt⟩
  choose d hd using happrox
  set ψ : ℕ → ℝ → ℂ := fun n => (d n).Q with hψ
  have hψm : ∀ n, MemLp (ψ n) P := fun n => (d n).memLp_Q hp1
  have hdPm : ∀ n, MemLp (d n).P P := fun n => (d n).memLp_P hp1
  have hgeom : Tendsto (fun n : ℕ => ENNReal.ofReal ((1 / 2 : ℝ) ^ n)) atTop (𝓝 0) := by
    have := ENNReal.tendsto_ofReal (tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num))
    rwa [ENNReal.ofReal_zero] at this
  have hdlim : Tendsto (fun n => eLpNorm ((d n).P - fC) P volume) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hgeom (fun n => zero_le)
      fun n => by rw [eLpNorm_sub_comm]; exact (hd n).le
  -- the Cauchy property
  set B : ℕ → ℝ≥0∞ := fun N => ENNReal.ofReal ((A + 1) * 2 * (1 / 2) ^ N) with hB
  have hBsum : ∑' N, B N ≠ ⊤ := by
    rw [hB, ← ENNReal.ofReal_tsum_of_nonneg (fun N => by positivity)
      (summable_geometric_two.mul_left _)]
    exact ENNReal.ofReal_ne_top
  have hcau : ∀ N n m : ℕ, N ≤ n → N ≤ m → eLpNorm (ψ n - ψ m) P volume < B N := by
    intro N n m hn hm
    have hgN : ∀ k, N ≤ k → eLpNorm (fun x => fC x - (d k).P x) P volume <
        ENNReal.ofReal ((1 / 2) ^ N) := fun k hk => (hd k).trans_le (ENNReal.ofReal_le_ofReal
          (pow_le_pow_of_le_one (by norm_num) (by norm_num) hk))
    have hPdiff : eLpNorm (fun x => (d n).P x - (d m).P x) P volume <
        ENNReal.ofReal ((1 / 2) ^ N) + ENNReal.ofReal ((1 / 2) ^ N) := by
      have : (fun x => (d n).P x - (d m).P x) =
          (fun x => fC x - (d m).P x) - (fun x => fC x - (d n).P x) := by
        funext x; simp only [Pi.sub_apply]; ring
      rw [this]
      exact (eLpNorm_sub_le hP1).trans_lt (ENNReal.add_lt_add (hgN m hm) (hgN n hn))
    calc eLpNorm (ψ n - ψ m) P volume
        ≤ ENNReal.ofReal A * eLpNorm (fun x => (d n).P x - (d m).P x) P volume := hD (d n) (d m)
      _ ≤ ENNReal.ofReal A * (ENNReal.ofReal ((1 / 2) ^ N) + ENNReal.ofReal ((1 / 2) ^ N)) := by
          gcongr
      _ = ENNReal.ofReal (A * 2 * (1 / 2) ^ N) := by
          rw [← ENNReal.ofReal_add (by positivity) (by positivity), ← ENNReal.ofReal_mul hA]
          ring_nf
      _ < B N := by
          rw [hB, ENNReal.ofReal_lt_ofReal_iff (by positivity)]
          have : 0 < (1 / 2 : ℝ) ^ N := by positivity
          nlinarith
  obtain ⟨h, hhm, hhlim⟩ := Lp.cauchy_complete_eLpNorm hP1 hψm hBsum hcau
  -- `Q_ε f = P_ε h`
  have hid : ∀ ε, 0 < ε → ∀ x, conjPoissonInt ε fC x = poissonInt ε h x := fun ε hε x => by
    have t1 := tendsto_integral_mul_of_eLpNorm hpq (memLp_qK_sub hq1 hε x) hdPm hfCm hdlim
    have t2 := tendsto_integral_mul_of_eLpNorm hpq (memLp_pK_sub hq1 hε x) hψm hhm hhlim
    rw [conjPoissonInt_eq_qK, poissonInt_eq_pK]
    refine tendsto_nhds_unique t1 (t2.congr fun n => ?_)
    rw [← poissonInt_eq_pK, ← conjPoissonInt_eq_qK]
    exact ((d n).conjPoissonInt_P hε x).symm
  -- a.e. existence
  have hwf := integrable_div_one_add_abs hpq hfCm
  have hwh := integrable_div_one_add_abs hpq hhm
  have hae : ∀ᵐ x, HasHilbert fC x (h x) := by
    filter_upwards [ae_tendsto_poissonKernel hfCm.aestronglyMeasurable
      (integrable_div_one_add_sq_of_abs hfCm.aestronglyMeasurable hwf),
      ae_tendsto_poissonKernel hhm.aestronglyMeasurable
      (integrable_div_one_add_sq_of_abs hhm.aestronglyMeasurable hwh)] with x hx1 hx2
    exact hasHilbert_of_lebesgue hfCm.aestronglyMeasurable hwf hhm.aestronglyMeasurable hwh
      hx1 hx2 fun ε hε => hid ε hε x
  have heq : hilbert fC =ᵐ[volume] h := hae.mono fun x hx => hx.hilbert_eq
  refine ⟨hae.mono fun x hx => by rw [hx.hilbert_eq]; exact hx, hhm.ae_eq heq.symm, ?_⟩
  -- the norm bound
  rw [eLpNorm_congr_ae heq, ← hfCn]
  have hbound : ∀ n, eLpNorm h P volume ≤
      ENNReal.ofReal A * (eLpNorm fC P volume + ENNReal.ofReal ((1 / 2) ^ n)) +
        eLpNorm (h - ψ n) P volume := fun n => by
    have h1 : eLpNorm h P volume ≤ eLpNorm (ψ n) P volume + eLpNorm (h - ψ n) P volume := by
      have : h = ψ n + (h - ψ n) := by abel
      conv_lhs => rw [this]
      exact eLpNorm_add_le hP1
    have h2 : eLpNorm (ψ n) P volume ≤ ENNReal.ofReal A * eLpNorm (d n).P P volume := by
      have := hD (d n) DenseDatum.zero
      simpa [DenseDatum.zero_P, DenseDatum.zero_Q] using this
    have h3 : eLpNorm (d n).P P volume ≤
        eLpNorm fC P volume + ENNReal.ofReal ((1 / 2) ^ n) := by
      have : (d n).P = fC - fun x => fC x - (d n).P x := by funext x; simp
      rw [this]
      exact (eLpNorm_sub_le hP1).trans (add_le_add le_rfl (hd n).le)
    calc eLpNorm h P volume ≤ eLpNorm (ψ n) P volume + eLpNorm (h - ψ n) P volume := h1
      _ ≤ _ := by gcongr; exact h2.trans (by gcongr)
  have hlim : Tendsto (fun n => ENNReal.ofReal A * (eLpNorm fC P volume +
      ENNReal.ofReal ((1 / 2) ^ n)) + eLpNorm (h - ψ n) P volume) atTop
      (𝓝 (ENNReal.ofReal A * (eLpNorm fC P volume + 0) + 0)) := by
    refine (ENNReal.Tendsto.const_mul (tendsto_const_nhds.add hgeom)
      (Or.inr ENNReal.ofReal_ne_top)).add ?_
    have := hhlim
    refine this.congr fun n => ?_
    rw [eLpNorm_sub_comm]
  rw [add_zero, add_zero] at hlim
  exact ge_of_tendsto' hlim hbound

end Azurite.DLMF
