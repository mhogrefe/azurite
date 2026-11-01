/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/


import Azurite.DLMF.Chapter2.Section4Watson
import Azurite.DLMF.Chapter2.Section3LaplaceCoeff
import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# DLMF §2.4(i): Watson's lemma in a larger sector, by rotation of the path

If `q` is analytic in a sector `α₁ < ph t < α₂` containing `ph t = 0`, then 2.4.1 holds in closed
subsectors of `−α₂ − π/2 < ph z < −α₁ + π/2`. The assumptions (`WatsonSector`) hold in closed
subsectors of `α₁ < ph t < α₂`:
* the expansion 2.3.7 as `t → 0` (filter `𝓝[closedSectorC β₁ β₂] 0`);
* `q(t) = O(e^{σ|t|})` as `t → ∞`.

The sector is taken inside the slit plane (`−π < α₁`, `α₂ ≤ π`), so that `t^{(s+λ−μ)/μ}` is the
principal power.

* `laplaceRay q θ z` is `∫` of `e^{−zt} q(t) dt` along the ray `ph t = θ`, i.e.
  `e^{iθ} ∫₀^∞ e^{−z e^{iθ} r} q(re^{iθ}) dr`.
* `WatsonSector.bound`: on every closed subsector, `|q(t)| ≤ C(|t|^{ℜλ/μ−1} + e^{σ'|t|})`.
* `WatsonSector.dlmf_2_4_1_ray`: on each ray, 2.4.1 for `laplaceRay q θ z` as `z → ∞` with
  `|ph(ze^{iθ})| ≤ π/2 − δ`, with the branch `e^{iθαₛ}(ze^{iθ})^{−αₛ}` of `z^{−αₛ}` (DLMF:
  "branches extended by continuity"). `dlmf_2_4_1_ray'` uses principal powers when
  `|ph z + θ| ≤ π/2 − δ`.
* `WatsonSector.laplaceRay_eq`: rotation of the path. Cauchy's theorem on the image under `exp`
  of a rectangle gives `laplaceRay q θ z = laplaceRay q θ' z` whenever `ℜ(ze^{iψ}) ≥ σ' + 1`
  for `ψ` between `θ` and `θ'`. The arcs vanish by the bounds above.
  `laplaceRay_zero`: for `θ = 0` this is the original transform.
* `WatsonSector.dlmf_2_4_1_sector`: 2.4.1 in any closed sector `φ₁ ≤ ph z ≤ φ₂` with
  `−α₂ − π/2 < φ₁`, `φ₂ < −α₁ + π/2` (and `−π < φ₁`, `φ₂ ≤ π`). The left side is the analytic
  continuation `laplaceCont` (the transform along a ray adapted to `ph z`). It agrees with every
  admissible `laplaceRay` and, for `|ph z| < π/2`, with the original integral.
-/

open Set Filter Topology Asymptotics Complex MeasureTheory
open scoped Interval

namespace Azurite.DLMF

/-- The open sector `α₁ < ph t < α₂`. -/
def openSectorC (α₁ α₂ : ℝ) : Set ℂ := {t | t ≠ 0 ∧ α₁ < arg t ∧ arg t < α₂}

/-- The closed sector `β₁ ≤ ph t ≤ β₂` (vertex removed). -/
def closedSectorC (β₁ β₂ : ℝ) : Set ℂ := {t | t ≠ 0 ∧ β₁ ≤ arg t ∧ arg t ≤ β₂}

/-! ### Polar form -/

theorem polar_ne_zero {r : ℝ} (hr : 0 < r) (ψ : ℝ) : (r : ℂ) * cexp (ψ * I) ≠ 0 :=
  mul_ne_zero (ofReal_ne_zero.mpr hr.ne') (Complex.exp_ne_zero _)

theorem norm_polar {r : ℝ} (hr : 0 ≤ r) (ψ : ℝ) : ‖(r : ℂ) * cexp (ψ * I)‖ = r := by
  rw [norm_mul, norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_of_nonneg hr]

theorem arg_polar {r : ℝ} (hr : 0 < r) {ψ : ℝ} (hψ : ψ ∈ Ioc (-Real.pi) Real.pi) :
    arg ((r : ℂ) * cexp (ψ * I)) = ψ := by
  rw [exp_mul_I]
  exact arg_mul_cos_add_sin_mul_I hr hψ

theorem log_polar {r : ℝ} (hr : 0 < r) {ψ : ℝ} (hψ : ψ ∈ Ioc (-Real.pi) Real.pi) :
    Complex.log ((r : ℂ) * cexp (ψ * I)) = Real.log r + ψ * I := by
  apply Complex.ext
  · rw [log_re, norm_polar hr.le]
    simp
  · rw [log_im, arg_polar hr hψ]
    simp

/-- `(re^{iψ})^c = r^c e^{iψc}` (principal powers, `−π < ψ ≤ π`). -/
theorem cpow_polar {r : ℝ} (hr : 0 < r) {ψ : ℝ} (hψ : ψ ∈ Ioc (-Real.pi) Real.pi) (c : ℂ) :
    ((r : ℂ) * cexp (ψ * I)) ^ c = (r : ℂ) ^ c * cexp (ψ * I * c) := by
  rw [cpow_def_of_ne_zero (polar_ne_zero hr ψ), cpow_def_of_ne_zero (ofReal_ne_zero.mpr hr.ne'),
    ← Complex.exp_add, log_polar hr hψ, ← ofReal_log hr.le]
  ring_nf

theorem polar_mem_closedSectorC {r : ℝ} (hr : 0 < r) {ψ β₁ β₂ : ℝ}
    (hψ : ψ ∈ Ioc (-Real.pi) Real.pi) (h : ψ ∈ Icc β₁ β₂) :
    (r : ℂ) * cexp (ψ * I) ∈ closedSectorC β₁ β₂ := by
  refine ⟨polar_ne_zero hr ψ, ?_, ?_⟩ <;> rw [arg_polar hr hψ]
  exacts [h.1, h.2]

theorem polar_mem_openSectorC {r : ℝ} (hr : 0 < r) {ψ α₁ α₂ : ℝ}
    (hψ : ψ ∈ Ioc (-Real.pi) Real.pi) (h : ψ ∈ Ioo α₁ α₂) :
    (r : ℂ) * cexp (ψ * I) ∈ openSectorC α₁ α₂ := by
  refine ⟨polar_ne_zero hr ψ, ?_, ?_⟩ <;> rw [arg_polar hr hψ]
  exacts [h.1, h.2]

theorem isOpen_openSectorC {α₁ α₂ : ℝ} (h₂ : α₂ ≤ Real.pi) : IsOpen (openSectorC α₁ α₂) := by
  have hc : ContinuousOn arg slitPlane := fun x hx => (continuousAt_arg hx).continuousWithinAt
  have he : openSectorC α₁ α₂ = slitPlane ∩ arg ⁻¹' Ioo α₁ α₂ := by
    ext t
    simp only [openSectorC, mem_ofPred_eq, mem_inter_iff, mem_preimage, mem_Ioo,
      mem_slitPlane_iff_arg]
    constructor
    · rintro ⟨h0, h1, h2⟩
      exact ⟨⟨(h2.trans_le h₂).ne, h0⟩, h1, h2⟩
    · rintro ⟨⟨_, h0⟩, h1, h2⟩
      exact ⟨h0, h1, h2⟩
  rw [he]
  exact hc.isOpen_inter_preimage isOpen_slitPlane isOpen_Ioo

/-! ### The hypotheses -/

/-- DLMF's hypotheses for the rotated Watson lemma: `q` analytic in `α₁ < ph t < α₂`
(`−π < α₁ < 0 < α₂ ≤ π`), with the expansion 2.3.7 as `t → 0` and `q = O(e^{σ|t|})` as
`t → ∞`, in every closed subsector. -/
structure WatsonSector (q : ℂ → ℂ) (a : ℕ → ℂ) (lam : ℂ) (μ σ α₁ α₂ : ℝ) : Prop where
  lam_re : 0 < lam.re
  μ_pos : 0 < μ
  α₁_gt : -Real.pi < α₁
  α₁_neg : α₁ < 0
  α₂_pos : 0 < α₂
  α₂_le : α₂ ≤ Real.pi
  differentiableOn : DifferentiableOn ℂ q (openSectorC α₁ α₂)
  expansion : ∀ β₁ β₂, α₁ < β₁ → β₂ < α₂ →
    IsGenAsympExpansionDLMF (𝓝[closedSectorC β₁ β₂] 0)
      (fun s t => t ^ (((s : ℂ) + lam - μ) / μ)) q
      (fun s t => a s * t ^ (((s : ℂ) + lam - μ) / μ))
  growth : ∀ β₁ β₂, α₁ < β₁ → β₂ < α₂ →
    IsBigODLMF (Bornology.cobounded ℂ ⊓ 𝓟 (closedSectorC β₁ β₂)) q
      (fun t => (Real.exp (σ * ‖t‖) : ℂ))

namespace WatsonSector

variable {q : ℂ → ℂ} {a : ℕ → ℂ} {lam : ℂ} {μ σ α₁ α₂ : ℝ}

theorem mem_Ioc_pi (h : WatsonSector q a lam μ σ α₁ α₂) {ψ : ℝ} (hψ : ψ ∈ Ioo α₁ α₂) :
    ψ ∈ Ioc (-Real.pi) Real.pi :=
  ⟨h.α₁_gt.trans hψ.1, (hψ.2.trans_le h.α₂_le).le⟩

theorem continuousAt (h : WatsonSector q a lam μ σ α₁ α₂) {t : ℂ}
    (ht : t ∈ openSectorC α₁ α₂) : ContinuousAt q t :=
  (h.differentiableOn.differentiableAt ((isOpen_openSectorC h.α₂_le).mem_nhds ht)).continuousAt

theorem continuousOn_polar (h : WatsonSector q a lam μ σ α₁ α₂) {ψ : ℝ}
    (hψ : ψ ∈ Ioo α₁ α₂) :
    ContinuousOn (fun r : ℝ => q ((r : ℂ) * cexp (ψ * I))) (Ioi 0) := fun r hr =>
  (ContinuousAt.comp (g := q) (f := fun r : ℝ => (r : ℂ) * cexp (ψ * I))
    (h.continuousAt (polar_mem_openSectorC hr (h.mem_Ioc_pi hψ) hψ))
    (by fun_prop)).continuousWithinAt

/-- The exponent `ℜλ/μ` governing `q` near `0`. -/
noncomputable def beta (lam : ℂ) (μ : ℝ) : ℝ := lam.re / μ

/-- A global bound on a closed subsector: `|q(re^{iψ})| ≤ C(r^{ℜλ/μ−1} + e^{σ'r})`,
`σ' = max σ 0`. -/
theorem bound (h : WatsonSector q a lam μ σ α₁ α₂) {β₁ β₂ : ℝ} (hβ₁ : α₁ < β₁)
    (hβ₂ : β₂ < α₂) :
    ∃ C, 0 ≤ C ∧ ∀ r ψ : ℝ, 0 < r → ψ ∈ Icc β₁ β₂ →
      ‖q ((r : ℂ) * cexp (ψ * I))‖ ≤ C * (r ^ (beta lam μ - 1) + Real.exp (max σ 0 * r)) := by
  set S := closedSectorC β₁ β₂
  set e0 : ℂ := (((0 : ℕ) : ℂ) + lam - μ) / μ with he0
  have hμc : (μ : ℂ) ≠ 0 := ofReal_ne_zero.mpr h.μ_pos.ne'
  have he0re : e0.re = beta lam μ - 1 := by
    rw [he0, beta]
    simp [div_re, normSq_ofReal]
    field_simp
    rw [sub_div, div_self h.μ_pos.ne']
  have hmemIoo : ∀ ψ ∈ Icc β₁ β₂, ψ ∈ Ioo α₁ α₂ := fun ψ hψ =>
    ⟨hβ₁.trans_le hψ.1, hψ.2.trans_lt hβ₂⟩
  -- near `0`
  obtain ⟨K₀, hK₀⟩ := (h.expansion β₁ β₂ hβ₁ hβ₂).2 0
  rw [eventually_map, eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hK₀
  obtain ⟨ρ, hρ, hρK⟩ := hK₀
  -- near `∞`
  obtain ⟨K₁, hK₁⟩ := h.growth β₁ β₂ hβ₁ hβ₂
  rw [eventually_map, eventually_inf_principal,
    Filter.hasBasis_cobounded_norm.eventually_iff] at hK₁
  obtain ⟨R, -, hRK⟩ := hK₁
  -- the middle
  set R' := max R ρ
  have hKc : IsCompact (Icc (ρ / 2) R' ×ˢ Icc β₁ β₂) := isCompact_Icc.prod isCompact_Icc
  have hFc : ContinuousOn (fun p : ℝ × ℝ => q ((p.1 : ℂ) * cexp (p.2 * I)))
      (Icc (ρ / 2) R' ×ˢ Icc β₁ β₂) := by
    intro p hp
    have hr : 0 < p.1 := by linarith [hp.1.1]
    have hψ := hmemIoo p.2 hp.2
    exact (ContinuousAt.comp (g := q) (f := fun p : ℝ × ℝ => (p.1 : ℂ) * cexp (p.2 * I))
      (h.continuousAt (polar_mem_openSectorC hr (h.mem_Ioc_pi hψ) hψ))
      (by fun_prop)).continuousWithinAt
  obtain ⟨M, hM⟩ := hKc.exists_bound_of_continuousOn hFc
  set E := Real.exp (Real.pi * |e0.im|)
  refine ⟨|K₀| * E + |K₁| + |M|, add_nonneg (add_nonneg (mul_nonneg (abs_nonneg _)
    (Real.exp_pos _).le) (abs_nonneg _)) (abs_nonneg _), fun r ψ hr hψ => ?_⟩
  have hψpi := h.mem_Ioc_pi (hmemIoo ψ hψ)
  set t := (r : ℂ) * cexp (ψ * I) with ht
  have htS : t ∈ S := polar_mem_closedSectorC hr hψpi hψ
  have hnt : ‖t‖ = r := norm_polar hr.le ψ
  have hp1 : 0 ≤ r ^ (beta lam μ - 1) := Real.rpow_nonneg hr.le _
  have hp2 : 1 ≤ Real.exp (max σ 0 * r) := Real.one_le_exp (by positivity)
  have hE : 0 ≤ E := (Real.exp_pos _).le
  rcases lt_or_ge r ρ with hrρ | hrρ
  · -- near zero
    have h1 := hρK (by rw [dist_zero_right, hnt]; exact hrρ) htS
    simp only [Finset.range_zero, Finset.sum_empty, sub_zero] at h1
    have ht0 : t ^ e0 ≠ 0 := cpow_ne_zero_of_ne_zero (polar_ne_zero hr ψ) _
    rw [norm_div, div_le_iff₀ (norm_pos_iff.mpr ht0)] at h1
    have hnorm : ‖t ^ e0‖ ≤ E * r ^ (beta lam μ - 1) := by
      rw [norm_cpow_of_ne_zero (polar_ne_zero hr ψ), hnt, he0re, div_le_iff₀ (Real.exp_pos _)]
      have : Real.exp (-(Real.pi * |e0.im|)) ≤ Real.exp (arg t * e0.im) := by
        apply Real.exp_le_exp.mpr
        have h2 : |arg t * e0.im| ≤ Real.pi * |e0.im| := by
          rw [abs_mul]
          gcongr
          exact abs_arg_le_pi t
        linarith [neg_abs_le (arg t * e0.im)]
      calc r ^ (beta lam μ - 1) = E * r ^ (beta lam μ - 1) * Real.exp (-(Real.pi * |e0.im|)) := by
            rw [mul_right_comm, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul]
        _ ≤ E * r ^ (beta lam μ - 1) * Real.exp (arg t * e0.im) := by gcongr
    calc ‖q t‖ ≤ K₀ * ‖t ^ e0‖ := h1
      _ ≤ |K₀| * (E * r ^ (beta lam μ - 1)) :=
          mul_le_mul (le_abs_self _) hnorm (norm_nonneg _) (abs_nonneg _)
      _ ≤ (|K₀| * E + |K₁| + |M|) * (r ^ (beta lam μ - 1) + Real.exp (max σ 0 * r)) := by
          nlinarith [abs_nonneg K₀, abs_nonneg K₁, abs_nonneg M, mul_nonneg (abs_nonneg K₀) hE]
  rcases le_or_gt r R' with hrR | hrR
  · -- the middle
    have h1 := hM (r, ψ) ⟨⟨by linarith, hrR⟩, hψ⟩
    calc ‖q t‖ ≤ M := h1
      _ ≤ |M| := le_abs_self _
      _ ≤ (|K₀| * E + |K₁| + |M|) * (r ^ (beta lam μ - 1) + Real.exp (max σ 0 * r)) := by
          nlinarith [abs_nonneg K₀, abs_nonneg K₁, abs_nonneg M, mul_nonneg (abs_nonneg K₀) hE]
  · -- near infinity
    have hRr : R ≤ ‖t‖ := by rw [hnt]; exact (le_max_left _ _).trans hrR.le
    have h1 := hRK hRr htS
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le,
      div_le_iff₀ (Real.exp_pos _), hnt] at h1
    have h2 : Real.exp (σ * r) ≤ Real.exp (max σ 0 * r) := by
      gcongr
      exact le_max_left _ _
    calc ‖q t‖ ≤ K₁ * Real.exp (σ * r) := h1
      _ ≤ |K₁| * Real.exp (max σ 0 * r) :=
          mul_le_mul (le_abs_self _) h2 (Real.exp_pos _).le (abs_nonneg _)
      _ ≤ (|K₀| * E + |K₁| + |M|) * (r ^ (beta lam μ - 1) + Real.exp (max σ 0 * r)) := by
          nlinarith [abs_nonneg K₀, abs_nonneg K₁, abs_nonneg M, mul_nonneg (abs_nonneg K₀) hE,
            Real.exp_pos (max σ 0 * r)]

/-! ### Watson's lemma along a ray -/

/-- `r ↦ e^{iθ} q(re^{iθ})` for `r > 0` (zero for `r ≤ 0`). -/
noncomputable def rayFun (q : ℂ → ℂ) (θ : ℝ) : ℝ → ℂ :=
  (Ioi (0 : ℝ)).indicator fun r => cexp (θ * I) * q (r * cexp (θ * I))

theorem rayFun_of_pos (q : ℂ → ℂ) (θ : ℝ) {r : ℝ} (hr : 0 < r) :
    rayFun q θ r = cexp (θ * I) * q (r * cexp (θ * I)) :=
  indicator_of_mem (s := Ioi (0 : ℝ)) hr _

theorem continuousOn_rayFun (h : WatsonSector q a lam μ σ α₁ α₂) {θ : ℝ} (hθ : θ ∈ Ioo α₁ α₂) :
    ContinuousOn (rayFun q θ) (Ioi 0) :=
  (continuousOn_const.mul (h.continuousOn_polar hθ)).congr fun _ hr => rayFun_of_pos q θ hr

theorem measurable_rayFun (h : WatsonSector q a lam μ σ α₁ α₂) {θ : ℝ} (hθ : θ ∈ Ioo α₁ α₂) :
    Measurable (rayFun q θ) := by
  rw [rayFun, ← Set.piecewise_eq_indicator]
  exact ContinuousOn.measurable_piecewise (continuousOn_const.mul (h.continuousOn_polar hθ))
    continuousOn_const measurableSet_Ioi

theorem norm_rayFun_le (h : WatsonSector q a lam μ σ α₁ α₂) {θ : ℝ} (hθ : θ ∈ Ioo α₁ α₂) :
    ∃ C, 0 ≤ C ∧ ∀ r : ℝ, 0 < r →
      ‖rayFun q θ r‖ ≤ C * (r ^ (beta lam μ - 1) + Real.exp (max σ 0 * r)) := by
  obtain ⟨C, hC, hb⟩ := h.bound (β₁ := θ) (β₂ := θ) hθ.1 hθ.2
  refine ⟨C, hC, fun r hr => ?_⟩
  rw [rayFun_of_pos q θ hr, norm_mul, norm_exp_ofReal_mul_I, one_mul]
  exact hb r θ hr ⟨le_rfl, le_rfl⟩

theorem beta_pos (h : WatsonSector q a lam μ σ α₁ α₂) : 0 < beta lam μ :=
  div_pos h.lam_re h.μ_pos

/-- For `ℜw ≥ σ' + 1` the ray transform converges absolutely. -/
theorem integrableOn_ray (h : WatsonSector q a lam μ σ α₁ α₂) {θ : ℝ} (hθ : θ ∈ Ioo α₁ α₂)
    {w : ℂ} (hw : max σ 0 + 1 ≤ w.re) :
    IntegrableOn (fun r : ℝ => cexp (-w * r) * rayFun q θ r) (Ioi 0) := by
  obtain ⟨C, hC, hb⟩ := h.norm_rayFun_le hθ
  have h1 := (integrableOn_rpow_mul_exp_neg' (h.beta_pos) (by positivity : 0 < max σ 0 + 1))
  have h2 := integrableOn_exp_mul_Ioi (a := -1) (by norm_num) 0
  refine Integrable.mono' ((h1.add h2).const_mul C)
    ((by fun_prop : Measurable fun r : ℝ => cexp (-w * r)).mul
      (h.measurable_rayFun hθ)).aestronglyMeasurable
    ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun r hr => ?_))
  have hr : (0 : ℝ) < r := hr
  rw [norm_mul, norm_cexp_neg_mul_ofReal]
  have he : Real.exp (-(w.re * r)) ≤ Real.exp (-((max σ 0 + 1) * r)) := by
    gcongr
  have hσ : Real.exp (-((max σ 0 + 1) * r)) * Real.exp (max σ 0 * r) = Real.exp (-1 * r) := by
    rw [← Real.exp_add]
    ring_nf
  calc Real.exp (-(w.re * r)) * ‖rayFun q θ r‖
      ≤ Real.exp (-((max σ 0 + 1) * r)) * (C * (r ^ (beta lam μ - 1) +
          Real.exp (max σ 0 * r))) :=
        mul_le_mul he (hb r hr) (norm_nonneg _) (Real.exp_pos _).le
    _ = C * (r ^ (beta lam μ - 1) * Real.exp (-((max σ 0 + 1) * r)) + Real.exp (-1 * r)) := by
        rw [← hσ]
        ring

theorem hasLimit_ray (h : WatsonSector q a lam μ σ α₁ α₂) {θ : ℝ} (hθ : θ ∈ Ioo α₁ α₂)
    {w : ℂ} (hw : max σ 0 + 1 ≤ w.re) :
    Tendsto (fun R => ∫ r in (0 : ℝ)..R, cexp (-w * r) * rayFun q θ r) atTop
      (𝓝 (∫ r in Ioi (0 : ℝ), cexp (-w * r) * rayFun q θ r)) :=
  intervalIntegral_tendsto_integral_Ioi 0 (h.integrableOn_ray hθ hw) tendsto_id

/-- The transform `∫_0^{∞ e^{iθ}} e^{−zt} q(t) dt` along the ray `ph t = θ`. -/
noncomputable def laplaceRay (q : ℂ → ℂ) (θ : ℝ) (z : ℂ) : ℂ :=
  laplaceIntegralC (rayFun q θ) (z * cexp (θ * I))

theorem laplaceRay_eq_integral (h : WatsonSector q a lam μ σ α₁ α₂) {θ : ℝ}
    (hθ : θ ∈ Ioo α₁ α₂) {z : ℂ} (hz : max σ 0 + 1 ≤ (z * cexp (θ * I)).re) :
    laplaceRay q θ z = ∫ r in Ioi (0 : ℝ), cexp (-(z * cexp (θ * I)) * r) * rayFun q θ r :=
  (h.hasLimit_ray hθ hz).limUnder_eq

theorem hloc_ray (h : WatsonSector q a lam μ σ α₁ α₂) {θ : ℝ} (hθ : θ ∈ Ioo α₁ α₂) :
    ∀ c R : ℝ, 0 < c → c ≤ R → IntervalIntegrable (rayFun q θ) volume c R := fun c R hc hcR =>
  ((h.continuousOn_rayFun hθ).mono (by
    rw [uIcc_of_le hcR]
    exact fun r hr => hc.trans_le hr.1)).intervalIntegrable

/-- The exponents `(s+λ−μ)/μ` of 2.3.7. -/
noncomputable def watsonPow (lam : ℂ) (μ : ℝ) (s : ℕ) : ℂ := ((s : ℂ) + lam - μ) / μ

theorem watsonPow_succ_sub (hμ : 0 < μ) (s : ℕ) :
    watsonPow lam μ (s + 1) - watsonPow lam μ s = ((1 / μ : ℝ) : ℂ) := by
  have hμc : (μ : ℂ) ≠ 0 := ofReal_ne_zero.mpr hμ.ne'
  simp only [watsonPow]
  push_cast
  field_simp
  ring

theorem watsonPow_add_one (hμ : 0 < μ) (s : ℕ) :
    watsonPow lam μ s + 1 = watsonExpC lam μ s := by
  have hμc : (μ : ℂ) ≠ 0 := ofReal_ne_zero.mpr hμ.ne'
  simp only [watsonPow, watsonExpC]
  field_simp
  ring

/-- The coefficients of the rotated expansion: `aₛ e^{iθ(s+λ)/μ}`. -/
noncomputable def rayCoeff (a : ℕ → ℂ) (lam : ℂ) (μ θ : ℝ) (s : ℕ) : ℂ :=
  a s * cexp (θ * I * watsonExpC lam μ s)

/-- 2.3.7 along the ray: `e^{iθ} q(re^{iθ}) ∼ ∑ aₛ e^{iθ(s+λ)/μ} r^{(s+λ−μ)/μ}` as `r → 0+`. -/
theorem expansion_ray (h : WatsonSector q a lam μ σ α₁ α₂) {θ : ℝ} (hθ : θ ∈ Ioo α₁ α₂) :
    IsGenAsympExpansionDLMF (𝓝[>] (0 : ℝ))
      (fun s (r : ℝ) => (r : ℂ) ^ (((s : ℂ) + lam - μ) / μ)) (rayFun q θ)
      (fun s (r : ℝ) => rayCoeff a lam μ θ s * (r : ℂ) ^ (((s : ℂ) + lam - μ) / μ)) := by
  have hθpi := h.mem_Ioc_pi hθ
  refine ⟨fun s => ?_, fun n => ?_⟩
  · have hlim : Tendsto (fun r : ℝ => ((r ^ (1 / μ) : ℝ) : ℂ)) (𝓝[>] 0) (𝓝 0) := by
      have h0 := ((Real.continuous_rpow_const (one_div_pos.mpr h.μ_pos).le).tendsto 0).mono_left
        (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
      rw [Real.zero_rpow (one_div_pos.mpr h.μ_pos).ne'] at h0
      have h1 := (continuous_ofReal.tendsto 0).comp h0
      rwa [ofReal_zero] at h1
    refine hlim.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with r hr
    have hr : (0 : ℝ) < r := hr
    have hsub := watsonPow_succ_sub (lam := lam) h.μ_pos s
    simp only [watsonPow] at hsub
    rw [← cpow_sub _ _ (ofReal_ne_zero.mpr hr.ne'), hsub, ← ofReal_cpow hr.le]
  -- the remainder
  set S := closedSectorC θ θ
  set g : ℝ → ℂ := fun r => (r : ℂ) * cexp (θ * I) with hg
  have hgt : Tendsto g (𝓝[>] 0) (𝓝[S] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have := ((by fun_prop : Continuous g).tendsto 0).mono_left
        (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
      simpa [hg] using this
    · filter_upwards [self_mem_nhdsWithin] with r hr
      exact polar_mem_closedSectorC hr hθpi ⟨le_rfl, le_rfl⟩
  obtain ⟨K, hK⟩ := (h.expansion θ θ hθ.1 hθ.2).2 n
  have hK' := hgt.eventually (eventually_map.mp hK)
  set c := cexp (θ * I * (((n : ℂ) + lam - μ) / μ))
  refine isBigODLMF_of_bound (K := K * ‖c‖) ?_ ?_
  · filter_upwards [hK', self_mem_nhdsWithin] with r hr hr0
    have hr0 : (0 : ℝ) < r := hr0
    have hgr : (g r) ^ (((n : ℂ) + lam - μ) / μ) ≠ 0 :=
      cpow_ne_zero_of_ne_zero (polar_ne_zero hr0 θ) _
    have hr' : ‖q (g r) - ∑ s ∈ Finset.range n, a s * (g r) ^ (((s : ℂ) + lam - μ) / μ)‖ ≤
        K * ‖(g r) ^ (((n : ℂ) + lam - μ) / μ)‖ := by
      have := hr
      rwa [norm_div, div_le_iff₀ (norm_pos_iff.mpr hgr)] at this
    have heq : rayFun q θ r - ∑ s ∈ Finset.range n,
        rayCoeff a lam μ θ s * (r : ℂ) ^ (((s : ℂ) + lam - μ) / μ) =
        cexp (θ * I) * (q (g r) -
          ∑ s ∈ Finset.range n, a s * (g r) ^ (((s : ℂ) + lam - μ) / μ)) := by
      rw [rayFun_of_pos q θ hr0, mul_sub, Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [hg, cpow_polar hr0 hθpi, rayCoeff, ← watsonPow_add_one h.μ_pos s]
      simp only [watsonPow]
      rw [mul_add, mul_one, Complex.exp_add]
      ring
    rw [heq, norm_mul, norm_exp_ofReal_mul_I, one_mul]
    calc _ ≤ K * ‖(g r) ^ (((n : ℂ) + lam - μ) / μ)‖ := hr'
      _ = K * ‖c‖ * ‖(r : ℂ) ^ (((n : ℂ) + lam - μ) / μ)‖ := by
          rw [hg, cpow_polar hr0 hθpi, norm_mul]
          ring
  · filter_upwards [self_mem_nhdsWithin] with r hr
    exact cpow_ne_zero_of_ne_zero (ofReal_ne_zero.mpr (ne_of_gt hr)) _

end WatsonSector

/-- Transport of a generalized expansion along a map. -/
theorem IsGenAsympExpansionDLMF.comp_tendsto' {α β : Type*} {l : Filter α} {l' : Filter β}
    {φ : ℕ → α → ℂ} {f : α → ℂ} {fs : ℕ → α → ℂ} (h : IsGenAsympExpansionDLMF l φ f fs)
    {g : β → α} (hg : Tendsto g l' l) :
    IsGenAsympExpansionDLMF l' (fun s x => φ s (g x)) (fun x => f (g x))
      (fun s x => fs s (g x)) := by
  refine ⟨fun s => (h.1 s).comp hg, fun n => ?_⟩
  obtain ⟨K, hK⟩ := h.2 n
  exact ⟨K, eventually_map.mpr (hg.eventually (eventually_map.mp hK))⟩

theorem IsGenAsympExpansionDLMF.mono_filter {α : Type*} {l l' : Filter α}
    {φ : ℕ → α → ℂ} {f : α → ℂ} {fs : ℕ → α → ℂ} (h : IsGenAsympExpansionDLMF l φ f fs)
    (hl : l' ≤ l) : IsGenAsympExpansionDLMF l' φ f fs :=
  h.comp_tendsto' (g := id) hl

namespace WatsonSector

variable {q : ℂ → ℂ} {a : ℕ → ℂ} {lam : ℂ} {μ σ α₁ α₂ : ℝ}

/-- **DLMF 2.4.1 along a ray** `ph t = θ`, `α₁ < θ < α₂`: as `z → ∞` with
`|ph(ze^{iθ})| ≤ π/2 − δ`,
`∫_0^{∞e^{iθ}} e^{−zt} q(t) dt ∼ ∑ Γ(αₛ) aₛ · e^{iθαₛ}(ze^{iθ})^{−αₛ}`, where
`e^{iθαₛ}(ze^{iθ})^{−αₛ}` is the branch of `z^{−αₛ}` continued from `θ = 0`. -/
theorem dlmf_2_4_1_ray (h : WatsonSector q a lam μ σ α₁ α₂) {θ δ : ℝ} (hθ : θ ∈ Ioo α₁ α₂)
    (hδ : 0 < δ) (hδ' : δ ≤ Real.pi / 2) :
    IsGenAsympExpansionDLMF
      (Bornology.cobounded ℂ ⊓ 𝓟 {z | z * cexp (θ * I) ∈ watsonSector δ})
      (fun s z => (z * cexp (θ * I)) ^ (-watsonExpC lam μ s)) (laplaceRay q θ)
      (fun s z => Complex.Gamma (watsonExpC lam μ s) * rayCoeff a lam μ θ s *
        (z * cexp (θ * I)) ^ (-watsonExpC lam μ s)) := by
  have hA := dlmf_2_4_1 (q := rayFun q θ) (a := rayCoeff a lam μ θ) (x₀ := max σ 0 + 1)
    h.lam_re h.μ_pos hδ hδ' (h.measurable_rayFun hθ) (h.hloc_ray hθ) (h.expansion_ray hθ)
    (fun w hw => ⟨_, h.hasLimit_ray hθ hw⟩)
  refine hA.comp_tendsto' (g := fun z => z * cexp (θ * I)) ?_
  refine Tendsto.inf ?_ (tendsto_principal_principal.mpr fun z hz => hz)
  refine Filter.hasBasis_cobounded_norm.tendsto_right_iff.mpr fun r _ => ?_
  filter_upwards [Filter.hasBasis_cobounded_norm.mem_of_mem (i := r) trivial] with z hz
  simp only [norm_mul, norm_exp_ofReal_mul_I, mul_one] at hz ⊢
  exact hz

/-! ### Principal powers -/

theorem arg_mul_exp_of_abs_le {z : ℂ} (hz : z ≠ 0) {θ : ℝ} (h : |arg z + θ| ≤ Real.pi / 2) :
    arg (z * cexp (θ * I)) = arg z + θ := by
  have hpol : z * cexp (θ * I) = (‖z‖ : ℂ) * cexp ((arg z + θ : ℝ) * I) := by
    conv_lhs => rw [← norm_mul_exp_arg_mul_I z]
    rw [mul_assoc, ← Complex.exp_add]
    push_cast
    ring_nf
  have h' := abs_le.mp h
  rw [hpol, arg_polar (norm_pos_iff.mpr hz) ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩]

/-- On `|ph z + θ| ≤ π/2` the continued branch `e^{iθα}(ze^{iθ})^{−α}` is the principal
`z^{−α}`. -/
theorem branch_eq {z : ℂ} (hz : z ≠ 0) {θ : ℝ} (h : |arg z + θ| ≤ Real.pi / 2) (α : ℂ) :
    cexp (θ * I * α) * (z * cexp (θ * I)) ^ (-α) = z ^ (-α) := by
  have hr := norm_pos_iff.mpr hz
  have h' := abs_le.mp h
  have hpol : z * cexp (θ * I) = (‖z‖ : ℂ) * cexp ((arg z + θ : ℝ) * I) := by
    conv_lhs => rw [← norm_mul_exp_arg_mul_I z]
    rw [mul_assoc, ← Complex.exp_add]
    push_cast
    ring_nf
  have e2 : z ^ (-α) = (‖z‖ : ℂ) ^ (-α) * cexp (arg z * I * (-α)) := by
    conv_lhs => rw [← norm_mul_exp_arg_mul_I z]
    exact cpow_polar hr (arg_mem_Ioc z) _
  rw [hpol, cpow_polar hr ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩, e2,
    mul_left_comm, ← Complex.exp_add]
  congr 2
  push_cast
  ring

/-- Multiplying the scale by nonzero constants preserves a generalized expansion. -/
theorem _root_.Azurite.DLMF.IsGenAsympExpansionDLMF.scale_const_mul {α : Type*} {l : Filter α}
    {φ : ℕ → α → ℂ} {f : α → ℂ} {fs : ℕ → α → ℂ} (h : IsGenAsympExpansionDLMF l φ f fs)
    {c : ℕ → ℂ} (hc : ∀ s, c s ≠ 0) :
    IsGenAsympExpansionDLMF l (fun s x => c s * φ s x) f fs := by
  refine ⟨fun s => ?_, fun n => ?_⟩
  · have := (h.1 s).const_mul (c (s + 1) / c s)
    rw [mul_zero] at this
    refine this.congr fun x => ?_
    by_cases hx : φ s x = 0
    · simp [hx]
    · field_simp [hc s, hc (s + 1)]
  · obtain ⟨K, hK⟩ := h.2 n
    refine ⟨K / ‖c n‖, eventually_map.mpr ((eventually_map.mp hK).mono fun x hx => ?_)⟩
    have hcn := norm_pos_iff.mpr (hc n)
    simp only at hx ⊢
    rw [le_div_iff₀ hcn]
    calc ‖(f x - ∑ s ∈ Finset.range n, fs s x) / (c n * φ n x)‖ * ‖c n‖ =
        ‖(f x - ∑ s ∈ Finset.range n, fs s x) / φ n x‖ := by
          rw [mul_comm (c n), ← div_div, norm_div (_ / φ n x), div_mul_cancel₀ _ hcn.ne']
      _ ≤ K := hx

/-- **DLMF 2.4.1 along a ray, principal powers**: as `z → ∞` with `|ph z + θ| ≤ π/2 − δ`,
`∫_0^{∞e^{iθ}} e^{−zt} q(t) dt ∼ ∑ Γ(αₛ) aₛ z^{−αₛ}`. -/
theorem dlmf_2_4_1_ray' (h : WatsonSector q a lam μ σ α₁ α₂) {θ δ : ℝ} (hθ : θ ∈ Ioo α₁ α₂)
    (hδ : 0 < δ) (hδ' : δ ≤ Real.pi / 2) :
    IsGenAsympExpansionDLMF (Bornology.cobounded ℂ ⊓ 𝓟 {z | |arg z + θ| ≤ Real.pi / 2 - δ})
      (fun s z => z ^ (-watsonExpC lam μ s)) (laplaceRay q θ)
      (fun s z => Complex.Gamma (watsonExpC lam μ s) * a s * z ^ (-watsonExpC lam μ s)) := by
  set P := {z : ℂ | |arg z + θ| ≤ Real.pi / 2 - δ}
  have h1 : {z : ℂ | 1 ≤ ‖z‖} ∈ Bornology.cobounded ℂ :=
    Filter.hasBasis_cobounded_norm.mem_of_mem (i := 1) trivial
  have hle : Bornology.cobounded ℂ ⊓ 𝓟 P ≤
      Bornology.cobounded ℂ ⊓ 𝓟 {z | z * cexp (θ * I) ∈ watsonSector δ} := by
    refine le_inf inf_le_left (le_principal_iff.mpr (mem_inf_of_inter h1 (mem_principal_self P)
      fun z hz => ?_))
    have hz0 : z ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le one_pos hz.1)
    have hP : |arg z + θ| ≤ Real.pi / 2 - δ := hz.2
    show |arg (z * cexp (θ * I))| ≤ Real.pi / 2 - δ
    rw [arg_mul_exp_of_abs_le hz0 (by linarith)]
    exact hP
  have hR := ((h.dlmf_2_4_1_ray hθ hδ hδ').mono_filter hle).scale_const_mul
    (c := fun s => cexp (θ * I * watsonExpC lam μ s)) fun s => Complex.exp_ne_zero _
  have hev : ∀ᶠ z in Bornology.cobounded ℂ ⊓ 𝓟 P, z ≠ 0 ∧ |arg z + θ| ≤ Real.pi / 2 := by
    filter_upwards [mem_inf_of_left h1, mem_inf_of_right (mem_principal_self P)] with z hz hP
    exact ⟨norm_pos_iff.mp (lt_of_lt_of_le one_pos hz), by
      have : |arg z + θ| ≤ Real.pi / 2 - δ := hP
      linarith⟩
  refine hR.congr' (fun s => ?_) (EventuallyEq.refl _ _) (fun s => ?_)
  · filter_upwards [hev] with z hz
    exact branch_eq hz.1 hz.2 _
  · filter_upwards [hev] with z hz
    rw [rayCoeff, ← branch_eq hz.1 hz.2]
    ring

/-! ### Rotation of the path of integration -/

/-- The integrand `e^{−zt} q(t)` along the ray `t = re^{iψ}`, including `dt = e^{iψ} dr`. -/
noncomputable def rayIntegrand (q : ℂ → ℂ) (z : ℂ) (ψ r : ℝ) : ℂ :=
  cexp (-(z * cexp (ψ * I)) * r) * rayFun q ψ r

/-- The integrand after `t = e^w`: `e^{−z e^w} q(e^w) e^w`. -/
noncomputable def rectFun (q : ℂ → ℂ) (z w : ℂ) : ℂ :=
  cexp (-(z * cexp w)) * q (cexp w) * cexp w

theorem exp_add_mul_I (x ψ : ℝ) : cexp ((x : ℂ) + ψ * I) = (Real.exp x : ℂ) * cexp (ψ * I) := by
  rw [Complex.exp_add, Complex.ofReal_exp]

theorem rectFun_eq (q : ℂ → ℂ) (z : ℂ) (x ψ : ℝ) :
    rectFun q z ((x : ℂ) + ψ * I) = Real.exp x • rayIntegrand q z ψ (Real.exp x) := by
  rw [rectFun, exp_add_mul_I, rayIntegrand, rayFun_of_pos q ψ (Real.exp_pos x),
    Complex.real_smul]
  have : -(z * ((Real.exp x : ℂ) * cexp (ψ * I))) = -(z * cexp (ψ * I)) * (Real.exp x : ℂ) := by
    ring
  rw [this]
  ring

theorem continuousOn_rayIntegrand (h : WatsonSector q a lam μ σ α₁ α₂) (z : ℂ) {ψ : ℝ}
    (hψ : ψ ∈ Ioo α₁ α₂) : ContinuousOn (rayIntegrand q z ψ) (Ioi 0) :=
  (by fun_prop : Continuous fun r : ℝ => cexp (-(z * cexp (ψ * I)) * r)).continuousOn.mul
    (h.continuousOn_rayFun hψ)

/-- The change of variables `r = e^x` along a ray. -/
theorem integral_rectFun_eq (h : WatsonSector q a lam μ σ α₁ α₂) (z : ℂ) {ψ : ℝ}
    (hψ : ψ ∈ Ioo α₁ α₂) {ε R : ℝ} (hε : 0 < ε) (hR : 0 < R) :
    ∫ x in Real.log ε..Real.log R, rectFun q z ((x : ℂ) + ψ * I) =
      ∫ r in ε..R, rayIntegrand q z ψ r := by
  have h1 := intervalIntegral.integral_deriv_smul_comp' (a := Real.log ε) (b := Real.log R)
    (f := Real.exp) (f' := Real.exp) (g := rayIntegrand q z ψ)
    (fun x _ => Real.hasDerivAt_exp x) Real.continuous_exp.continuousOn
    ((h.continuousOn_rayIntegrand z hψ).mono fun r ⟨x, _, hx⟩ => hx ▸ Real.exp_pos x)
  rw [Real.exp_log hε, Real.exp_log hR] at h1
  rw [← h1]
  refine intervalIntegral.integral_congr fun x _ => ?_
  rw [rectFun_eq]
  rfl

theorem rectFun_differentiableOn (h : WatsonSector q a lam μ σ α₁ α₂) (z : ℂ) {θ θ' : ℝ}
    (hθ : θ ∈ Ioo α₁ α₂) (hθ' : θ' ∈ Ioo α₁ α₂) (u v : ℝ) :
    DifferentiableOn ℂ (rectFun q z) ([[u, v]] ×ℂ [[θ, θ']]) := by
  intro w hw
  have hwim : w.im ∈ Ioo α₁ α₂ := ordConnected_Ioo.uIcc_subset hθ hθ' hw.2
  have hexp : cexp w = (Real.exp w.re : ℂ) * cexp (w.im * I) := by
    rw [← exp_add_mul_I, re_add_im]
  have hmem : cexp w ∈ openSectorC α₁ α₂ := by
    rw [hexp]
    exact polar_mem_openSectorC (Real.exp_pos _) (h.mem_Ioc_pi hwim) hwim
  have hq : DifferentiableAt ℂ q (cexp w) :=
    h.differentiableOn.differentiableAt ((isOpen_openSectorC h.α₂_le).mem_nhds hmem)
  have h1 : DifferentiableAt ℂ (fun w => cexp (-(z * cexp w))) w := by fun_prop
  have h2 : DifferentiableAt ℂ (fun w => q (cexp w)) w :=
    hq.comp w Complex.differentiable_exp.differentiableAt
  exact ((h1.mul h2).mul Complex.differentiable_exp.differentiableAt).differentiableWithinAt

theorem norm_rayIntegrand (z : ℂ) {ψ r : ℝ} (hr : 0 < r) :
    ‖rayIntegrand q z ψ r‖ = Real.exp (-((z * cexp (ψ * I)).re * r)) *
      ‖q ((r : ℂ) * cexp (ψ * I))‖ := by
  rw [rayIntegrand, norm_mul, norm_cexp_neg_mul_ofReal, rayFun_of_pos q ψ hr, norm_mul,
    norm_exp_ofReal_mul_I, one_mul]

/-- **Rotation of the path** (DLMF: "the region of validity may be increased by rotation of the
integration paths"): if `ℜ(ze^{iψ}) ≥ σ' + 1` for all `ψ` between `θ` and `θ'`, the transforms
along the rays `ph t = θ` and `ph t = θ'` agree. -/
theorem laplaceRay_eq (h : WatsonSector q a lam μ σ α₁ α₂) {θ θ' : ℝ} (hθ : θ ∈ Ioo α₁ α₂)
    (hθ' : θ' ∈ Ioo α₁ α₂) {z : ℂ}
    (hz : ∀ ψ ∈ uIcc θ θ', max σ 0 + 1 ≤ (z * cexp (ψ * I)).re) :
    laplaceRay q θ z = laplaceRay q θ' z := by
  have hzθ := hz θ left_mem_uIcc
  have hzθ' := hz θ' right_mem_uIcc
  rw [h.laplaceRay_eq_integral hθ hzθ, h.laplaceRay_eq_integral hθ' hzθ']
  set σ' := max σ 0
  set β := beta lam μ
  have hβ := h.beta_pos
  -- the bound on the closed sector between the rays
  have hsub : uIcc θ θ' ⊆ Ioo α₁ α₂ := ordConnected_Ioo.uIcc_subset hθ hθ'
  obtain ⟨C, hC, hb⟩ := h.bound (β₁ := min θ θ') (β₂ := max θ θ')
    (lt_min hθ.1 hθ'.1) (max_lt hθ.2 hθ'.2)
  have hbψ : ∀ ψ ∈ uIcc θ θ', ∀ r : ℝ, 0 < r →
      ‖q ((r : ℂ) * cexp (ψ * I))‖ ≤ C * (r ^ (β - 1) + Real.exp (σ' * r)) :=
    fun ψ hψ r hr => hb r ψ hr hψ
  -- the ray integrals as limits
  set ε : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 2) with hεdef
  set R : ℕ → ℝ := fun n => (n : ℝ) + 2 with hRdef
  have hε0 : ∀ n, 0 < ε n := fun n => by simp only [hεdef]; positivity
  have hε1 : ∀ n, ε n ≤ 1 := fun n => by
    simp only [hεdef]
    rw [div_le_one (by positivity)]
    linarith [n.cast_nonneg (α := ℝ)]
  have hR1 : ∀ n, 1 ≤ R n := fun n => by simp only [hRdef]; linarith [n.cast_nonneg (α := ℝ)]
  have hR0 : ∀ n, 0 < R n := fun n => by linarith [hR1 n]
  have hRt : Tendsto R atTop atTop :=
    tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop
  have hεt : Tendsto ε atTop (𝓝 0) := tendsto_const_nhds.div_atTop hRt
  have hlim : ∀ ψ ∈ uIcc θ θ', Tendsto (fun n => ∫ r in ε n..R n, rayIntegrand q z ψ r) atTop
      (𝓝 (∫ r in Ioi (0 : ℝ), cexp (-(z * cexp (ψ * I)) * r) * rayFun q ψ r)) := by
    intro ψ hψ
    have hI := h.integrableOn_ray (hsub hψ) (hz ψ hψ)
    have hII : ∀ b : ℝ, 0 ≤ b → IntervalIntegrable (rayIntegrand q z ψ) volume 0 b := fun b hb' =>
      (intervalIntegrable_iff_integrableOn_Ioc_of_le hb').mpr (hI.mono_set Ioc_subset_Ioi_self)
    have h1 : Tendsto (fun n => ∫ r in (0 : ℝ)..R n, rayIntegrand q z ψ r) atTop
        (𝓝 (∫ r in Ioi (0 : ℝ), cexp (-(z * cexp (ψ * I)) * r) * rayFun q ψ r)) :=
      (intervalIntegral_tendsto_integral_Ioi 0 hI tendsto_id).comp hRt
    have hc := intervalIntegral.continuousOn_primitive_interval
      (f := rayIntegrand q z ψ) (μ := volume) (a := 0) (b := 1)
      (by
        rw [uIcc_of_le zero_le_one]
        exact (intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one).mp (hII 1 zero_le_one))
    have h2 : Tendsto (fun n => ∫ r in (0 : ℝ)..ε n, rayIntegrand q z ψ r) atTop (𝓝 0) := by
      have h3 := (hc 0 left_mem_uIcc).tendsto.comp (tendsto_nhdsWithin_iff.mpr
        ⟨hεt, Eventually.of_forall fun n => (show ε n ∈ uIcc 0 1 by
          rw [uIcc_of_le zero_le_one]; exact ⟨(hε0 n).le, hε1 n⟩)⟩)
      simpa only [Function.comp_def, intervalIntegral.integral_same] using h3
    have h4 := h1.sub h2
    rw [sub_zero] at h4
    refine h4.congr fun n => ?_
    exact intervalIntegral.integral_interval_sub_left (hII _ (hR0 n).le) (hII _ (hε0 n).le)
  -- the arcs
  have hnorm_arc : ∀ ψ ∈ uIcc θ θ', ∀ x : ℝ, ‖rectFun q z ((x : ℂ) + ψ * I)‖ ≤
      Real.exp x * (Real.exp (-((z * cexp (ψ * I)).re * Real.exp x)) *
        (C * (Real.exp x ^ (β - 1) + Real.exp (σ' * Real.exp x)))) := by
    intro ψ hψ x
    rw [rectFun_eq, norm_smul, Real.norm_of_nonneg (Real.exp_pos x).le,
      norm_rayIntegrand z (Real.exp_pos x)]
    gcongr
    exact hbψ ψ hψ _ (Real.exp_pos x)
  have harcR : Tendsto (fun n => ∫ y in θ..θ', rectFun q z ((Real.log (R n) : ℂ) + y * I))
      atTop (𝓝 0) := by
    have hbd : ∀ n, ‖∫ y in θ..θ', rectFun q z ((Real.log (R n) : ℂ) + y * I)‖ ≤
        C * (R n ^ β * Real.exp (-1 * R n) + R n * Real.exp (-1 * R n)) * |θ' - θ| := by
      intro n
      refine intervalIntegral.norm_integral_le_of_norm_le_const fun y hy => ?_
      have hy' : y ∈ uIcc θ θ' := uIoc_subset_uIcc hy
      refine (hnorm_arc y hy' _).trans ?_
      rw [Real.exp_log (hR0 n)]
      have hRn := hR0 n
      have he1 : Real.exp (-((z * cexp (y * I)).re * R n)) ≤ Real.exp (-((σ' + 1) * R n)) := by
        gcongr
        exact hz y hy'
      have he2 : Real.exp (-((σ' + 1) * R n)) ≤ Real.exp (-1 * R n) := by
        gcongr
        nlinarith [le_max_right σ 0]
      have he3 : Real.exp (-((σ' + 1) * R n)) * Real.exp (σ' * R n) = Real.exp (-1 * R n) := by
        rw [← Real.exp_add]
        ring_nf
      have hpow : R n * R n ^ (β - 1) = R n ^ β := by
        rw [Real.rpow_sub_one hRn.ne']
        field_simp
      calc R n * (Real.exp (-((z * cexp (y * I)).re * R n)) *
            (C * (R n ^ (β - 1) + Real.exp (σ' * R n))))
          ≤ R n * (Real.exp (-((σ' + 1) * R n)) * (C * (R n ^ (β - 1) +
              Real.exp (σ' * R n)))) := by
            gcongr
        _ = C * (R n * R n ^ (β - 1) * Real.exp (-((σ' + 1) * R n)) +
              R n * (Real.exp (-((σ' + 1) * R n)) * Real.exp (σ' * R n))) := by ring
        _ ≤ C * (R n ^ β * Real.exp (-1 * R n) + R n * Real.exp (-1 * R n)) := by
            rw [hpow, he3]
            gcongr
    refine squeeze_zero_norm hbd ?_
    have t1 := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero β 1 one_pos).comp hRt
    have t2 := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 1 one_pos).comp hRt
    have t3 := ((t1.add t2).const_mul C).mul_const |θ' - θ|
    simp only [add_zero, mul_zero, zero_mul] at t3
    refine t3.congr fun n => ?_
    simp only [Function.comp_apply, Real.rpow_one, neg_mul, one_mul]
  have harcε : Tendsto (fun n => ∫ y in θ..θ', rectFun q z ((Real.log (ε n) : ℂ) + y * I))
      atTop (𝓝 0) := by
    have hbd : ∀ n, ‖∫ y in θ..θ', rectFun q z ((Real.log (ε n) : ℂ) + y * I)‖ ≤
        Real.exp ‖z‖ * C * (ε n ^ β + ε n * Real.exp σ') * |θ' - θ| := by
      intro n
      refine intervalIntegral.norm_integral_le_of_norm_le_const fun y hy => ?_
      have hy' : y ∈ uIcc θ θ' := uIoc_subset_uIcc hy
      refine (hnorm_arc y hy' _).trans ?_
      rw [Real.exp_log (hε0 n)]
      have hεn := hε0 n
      have hε1n := hε1 n
      have hre : -((z * cexp (y * I)).re * ε n) ≤ ‖z‖ := by
        have h1 : -(z * cexp (y * I)).re ≤ ‖z‖ := by
          have := neg_abs_le (z * cexp (y * I)).re
          have h2 := abs_re_le_norm (z * cexp (y * I))
          rw [norm_mul, norm_exp_ofReal_mul_I, mul_one] at h2
          linarith
        nlinarith [norm_nonneg z]
      have he1 : Real.exp (σ' * ε n) ≤ Real.exp σ' := by
        gcongr
        nlinarith [le_max_right σ 0]
      have hpow : ε n * ε n ^ (β - 1) = ε n ^ β := by
        rw [Real.rpow_sub_one hεn.ne']
        field_simp
      calc ε n * (Real.exp (-((z * cexp (y * I)).re * ε n)) *
            (C * (ε n ^ (β - 1) + Real.exp (σ' * ε n))))
          ≤ ε n * (Real.exp ‖z‖ * (C * (ε n ^ (β - 1) + Real.exp σ'))) := by
            gcongr
        _ = Real.exp ‖z‖ * C * (ε n * ε n ^ (β - 1) + ε n * Real.exp σ') := by ring
        _ = Real.exp ‖z‖ * C * (ε n ^ β + ε n * Real.exp σ') := by rw [hpow]
    refine squeeze_zero_norm hbd ?_
    have t1 : Tendsto (fun n => ε n ^ β) atTop (𝓝 0) := by
      have := ((Real.continuous_rpow_const hβ.le).tendsto 0).comp hεt
      rwa [Real.zero_rpow hβ.ne'] at this
    have t3 := (((t1.add (hεt.mul_const (Real.exp σ'))).const_mul
      (Real.exp ‖z‖ * C)).mul_const |θ' - θ|)
    simp only [zero_mul, add_zero, mul_zero] at t3
    exact t3
  -- Cauchy's theorem on the rectangles
  have hcauchy : ∀ n, (∫ r in ε n..R n, rayIntegrand q z θ r) -
      (∫ r in ε n..R n, rayIntegrand q z θ' r) +
      I • (∫ y in θ..θ', rectFun q z ((Real.log (R n) : ℂ) + y * I)) -
      I • (∫ y in θ..θ', rectFun q z ((Real.log (ε n) : ℂ) + y * I)) = 0 := by
    intro n
    have hc := integral_boundary_rect_eq_zero_of_differentiableOn (rectFun q z)
      ((Real.log (ε n) : ℂ) + θ * I) ((Real.log (R n) : ℂ) + θ' * I) (by
        simpa using h.rectFun_differentiableOn z hθ hθ' (Real.log (ε n)) (Real.log (R n)))
    simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
      add_zero, add_im, mul_im, zero_add] at hc
    rwa [h.integral_rectFun_eq z hθ (hε0 n) (hR0 n),
      h.integral_rectFun_eq z hθ' (hε0 n) (hR0 n)] at hc
  have hA := (hlim θ left_mem_uIcc).sub (hlim θ' right_mem_uIcc)
  have hB : Tendsto (fun n => (∫ r in ε n..R n, rayIntegrand q z θ r) -
      (∫ r in ε n..R n, rayIntegrand q z θ' r)) atTop (𝓝 0) := by
    have := ((harcR.const_smul I).sub (harcε.const_smul I)).neg
    simp only [smul_zero, sub_zero, neg_zero] at this
    refine this.congr fun n => ?_
    linear_combination (hcauchy n).symm
  exact sub_eq_zero.mp (tendsto_nhds_unique hA hB)

/-- For `θ = 0` the ray transform is the original Laplace transform of `q` on `(0, ∞)`. -/
theorem laplaceRay_zero (q : ℂ → ℂ) (z : ℂ) :
    laplaceRay q 0 z = laplaceIntegralC (fun t : ℝ => q t) z := by
  have hz : z * cexp ((0 : ℝ) * I) = z := by simp
  rw [laplaceRay, hz, laplaceIntegralC, laplaceIntegralC]
  unfold limUnder
  congr 1
  refine Filter.map_congr ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with R hR
  refine intervalIntegral.integral_congr_ae (Eventually.of_forall fun t ht => ?_)
  rw [uIoc_of_le hR] at ht
  rw [rayFun_of_pos q 0 ht.1]
  simp

/-! ### The enlarged sector -/

theorem isAsympScale_cpow_neg {l : Filter ℂ} (hl : l ≤ Bornology.cobounded ℂ) (hμ : 0 < μ)
    (lam : ℂ) : IsAsympScaleDLMF l (fun s z => z ^ (-watsonExpC lam μ s)) := fun s => by
  have hcob : Tendsto (fun z : ℂ => ‖z‖) l atTop := tendsto_norm_cobounded_atTop.mono_left hl
  have hlim : Tendsto (fun z : ℂ => ‖z‖ ^ (-(1 / μ))) l (𝓝 0) :=
    (tendsto_rpow_neg_atTop (one_div_pos.mpr hμ)).comp hcob
  rw [IsLittleODLMF, tendsto_zero_iff_norm_tendsto_zero]
  refine hlim.congr' ?_
  filter_upwards [hcob.eventually (eventually_gt_atTop 0)] with z hz
  have hz0 : z ≠ 0 := norm_pos_iff.mp hz
  rw [← cpow_sub _ _ hz0]
  have : -watsonExpC lam μ (s + 1) - -watsonExpC lam μ s = (((-(1 / μ)) : ℝ) : ℂ) := by
    simp only [watsonExpC]
    push_cast
    ring
  rw [this, norm_cpow_real]

theorem re_ge_of_abs_arg_add {z : ℂ} (hz : z ≠ 0) {ψ κ : ℝ} (hκ : 0 ≤ κ)
    (h : |arg z + ψ| ≤ Real.pi / 2 - κ) : Real.sin κ * ‖z‖ ≤ (z * cexp (ψ * I)).re := by
  have hmem : z * cexp (ψ * I) ∈ watsonSector κ := by
    show |arg (z * cexp (ψ * I))| ≤ Real.pi / 2 - κ
    rw [arg_mul_exp_of_abs_le hz (by linarith)]
    exact h
  have := re_ge_of_mem_watsonSector hκ hmem
  rwa [norm_mul, norm_exp_ofReal_mul_I, mul_one] at this

/-- Two rays with `|ph z + θ|, |ph z + θ'| ≤ π/2 − κ` give the same transform once
`|z| sin κ ≥ σ' + 1`. -/
theorem laplaceRay_eq_of_abs (h : WatsonSector q a lam μ σ α₁ α₂) {θ θ' κ : ℝ}
    (hθ : θ ∈ Ioo α₁ α₂) (hθ' : θ' ∈ Ioo α₁ α₂) (hκ : 0 ≤ κ) {z : ℂ} (hz : z ≠ 0)
    (h1 : |arg z + θ| ≤ Real.pi / 2 - κ) (h2 : |arg z + θ'| ≤ Real.pi / 2 - κ)
    (hR : max σ 0 + 1 ≤ Real.sin κ * ‖z‖) :
    laplaceRay q θ z = laplaceRay q θ' z := by
  refine h.laplaceRay_eq hθ hθ' fun ψ hψ => hR.trans (re_ge_of_abs_arg_add hz hκ ?_)
  have hmem : arg z + ψ ∈ uIcc (arg z + θ) (arg z + θ') := by
    rcases le_total θ θ' with hle | hle
    · rw [uIcc_of_le hle] at hψ
      rw [uIcc_of_le (by linarith)]
      exact ⟨by linarith [hψ.1], by linarith [hψ.2]⟩
    · rw [uIcc_of_ge hle] at hψ
      rw [uIcc_of_ge (by linarith)]
      exact ⟨by linarith [hψ.1], by linarith [hψ.2]⟩
  have hs := (ordConnected_Icc (a := -(Real.pi / 2 - κ)) (b := Real.pi / 2 - κ)).uIcc_subset
    (abs_le.mp h1) (abs_le.mp h2) hmem
  exact abs_le.mpr hs

/-- The ray adapted to `ph z`: `−ph z` clamped to `[α₁ + η, α₂ − η]`. -/
noncomputable def adaptedRay (α₁ α₂ η : ℝ) (z : ℂ) : ℝ := max (α₁ + η) (min (α₂ - η) (-arg z))

/-- The analytic continuation of the transform 2.4.1 into `−α₂ − π/2 < ph z < −α₁ + π/2`: the
transform along the ray adapted to `ph z`. -/
noncomputable def laplaceCont (q : ℂ → ℂ) (α₁ α₂ η : ℝ) (z : ℂ) : ℂ :=
  laplaceRay q (adaptedRay α₁ α₂ η z) z

theorem adaptedRay_mem {α₁ α₂ η : ℝ} (hβ : α₁ + η ≤ α₂ - η) (z : ℂ) :
    adaptedRay α₁ α₂ η z ∈ Icc (α₁ + η) (α₂ - η) :=
  ⟨le_max_left _ _, max_le hβ (min_le_left _ _)⟩

theorem abs_arg_add_adaptedRay {α₁ α₂ η φ₁ φ₂ : ℝ}
    (hη4 : 2 * η ≤ Real.pi / 2) (hβ : α₁ + η ≤ α₂ - η)
    (h1 : -α₂ - Real.pi / 2 + 3 * η ≤ φ₁) (h2 : φ₂ ≤ -α₁ + Real.pi / 2 - 3 * η) {z : ℂ}
    (hz : φ₁ ≤ arg z ∧ arg z ≤ φ₂) :
    |arg z + adaptedRay α₁ α₂ η z| ≤ Real.pi / 2 - 2 * η := by
  rw [abs_le]
  simp only [adaptedRay, max_def, min_def]
  split_ifs <;> constructor <;> linarith [hz.1, hz.2]

/-- **DLMF 2.4.1 in the enlarged sector**: if `q` satisfies `WatsonSector`, then for every closed
sector `φ₁ ≤ ph z ≤ φ₂` with `−α₂ − π/2 < φ₁` and `φ₂ < −α₁ + π/2` there is `η > 0` such
that the continuation `laplaceCont` of `∫₀^∞ e^{−zt} q(t) dt` satisfies
`laplaceCont(z) ∼ ∑ Γ((s+λ)/μ) aₛ z^{−(s+λ)/μ}` as `z → ∞` in the sector, and
`laplaceCont(z)` is the transform along every ray `ph t = θ`, `α₁ < θ < α₂`, with
`|ph z + θ| ≤ π/2 − κ`, for `|z|` large. -/
theorem dlmf_2_4_1_sector (h : WatsonSector q a lam μ σ α₁ α₂) {φ₁ φ₂ : ℝ}
    (hφ₁ : -α₂ - Real.pi / 2 < φ₁) (hφ₂ : φ₂ < -α₁ + Real.pi / 2) :
    ∃ η > 0, IsGenAsympExpansionDLMF
        (Bornology.cobounded ℂ ⊓ 𝓟 {z | φ₁ ≤ arg z ∧ arg z ≤ φ₂})
        (fun s z => z ^ (-watsonExpC lam μ s)) (laplaceCont q α₁ α₂ η)
        (fun s z => Complex.Gamma (watsonExpC lam μ s) * a s * z ^ (-watsonExpC lam μ s)) ∧
      ∀ θ ∈ Ioo α₁ α₂, ∀ κ > 0, ∀ᶠ z in Bornology.cobounded ℂ ⊓
        𝓟 {z | (φ₁ ≤ arg z ∧ arg z ≤ φ₂) ∧ |arg z + θ| ≤ Real.pi / 2 - κ},
        laplaceCont q α₁ α₂ η z = laplaceRay q θ z := by
  have hpi := Real.two_le_pi
  set η := min (min ((φ₁ + α₂ + Real.pi / 2) / 3) ((Real.pi / 2 - α₁ - φ₂) / 3))
    (min ((α₂ - α₁) / 4) (1 / 2)) with hηdef
  have hα := h.α₁_neg.trans h.α₂_pos
  have hη : 0 < η := lt_min (lt_min (by linarith) (by linarith)) (lt_min (by linarith) one_half_pos)
  have hηa : η ≤ (φ₁ + α₂ + Real.pi / 2) / 3 := (min_le_left _ _).trans (min_le_left _ _)
  have hηb : η ≤ (Real.pi / 2 - α₁ - φ₂) / 3 := (min_le_left _ _).trans (min_le_right _ _)
  have hηc : η ≤ (α₂ - α₁) / 4 := (min_le_right _ _).trans (min_le_left _ _)
  have hηd : η ≤ 1 / 2 := (min_le_right _ _).trans (min_le_right _ _)
  have hβ : α₁ + η ≤ α₂ - η := by linarith
  have hη4 : 2 * η ≤ Real.pi / 2 := by linarith
  have h1 : -α₂ - Real.pi / 2 + 3 * η ≤ φ₁ := by linarith
  have h2 : φ₂ ≤ -α₁ + Real.pi / 2 - 3 * η := by linarith
  have hηpi : η ≤ Real.pi / 2 := by linarith
  set Z := {z : ℂ | φ₁ ≤ arg z ∧ arg z ≤ φ₂}
  have hIcc : ∀ x ∈ Icc (α₁ + η) (α₂ - η), x ∈ Ioo α₁ α₂ := fun x hx =>
    ⟨by linarith [hx.1], by linarith [hx.2]⟩
  set σ' := max σ 0
  have hcob_big : ∀ c : ℝ, ∀ᶠ z in Bornology.cobounded ℂ, c ≤ ‖z‖ := fun c =>
    Filter.hasBasis_cobounded_norm.mem_of_mem (i := c) trivial
  refine ⟨η, hη, ⟨isAsympScale_cpow_neg inf_le_left h.μ_pos lam, fun n => ?_⟩, ?_⟩
  · -- the grid of rays
    set β₁ := α₁ + η
    set β₂ := α₂ - η
    have hβlt : β₁ < β₂ := by simp only [β₁, β₂]; linarith
    set N : ℕ := ⌈(β₂ - β₁) / η⌉₊ with hNdef
    have hN : 0 < N := Nat.ceil_pos.mpr (div_pos (by linarith) hη)
    have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr hN
    set d := (β₂ - β₁) / N with hddef
    have hd0 : 0 < d := div_pos (by linarith) hNr
    have hd : d ≤ η := by
      rw [hddef, div_le_iff₀ hNr]
      have := Nat.le_ceil ((β₂ - β₁) / η)
      rw [← hNdef, div_le_iff₀ hη] at this
      linarith
    set θg : ℕ → ℝ := fun j => β₁ + (min j N : ℕ) * d with hθg
    have hθg_mem : ∀ j, θg j ∈ Icc β₁ β₂ := fun j => by
      have hm : ((min j N : ℕ) : ℝ) ≤ N := by exact_mod_cast min_le_right j N
      have hNd : (N : ℝ) * d = β₂ - β₁ := by rw [hddef]; field_simp
      have h0 : (0 : ℝ) ≤ ((min j N : ℕ) : ℝ) := Nat.cast_nonneg _
      refine ⟨by simp only [hθg]; nlinarith, ?_⟩
      · simp only [hθg]
        nlinarith
    have hcover : ∀ x ∈ Icc β₁ β₂, ∃ j ∈ Finset.range (N + 1), |x - θg j| ≤ η := by
      intro x hx
      set j := ⌊(x - β₁) / d⌋₊
      have hjN : j ≤ N := by
        refine Nat.floor_le_of_le ?_
        rw [div_le_iff₀ hd0, hddef]
        field_simp
        linarith [hx.2]
      refine ⟨j, Finset.mem_range.mpr (Nat.lt_succ_of_le hjN), ?_⟩
      have hmin : min j N = j := min_eq_left hjN
      simp only [hθg, hmin]
      have hfl := Nat.floor_le (div_nonneg (sub_nonneg.mpr hx.1) hd0.le)
      have hlt := Nat.lt_floor_add_one ((x - β₁) / d)
      rw [le_div_iff₀ hd0] at hfl
      rw [div_lt_iff₀ hd0] at hlt
      rw [abs_le]
      constructor <;> nlinarith
    -- the bound on each ray
    have hK : ∀ j, ∃ K, ∀ᶠ z in Bornology.cobounded ℂ,
        |arg z + θg j| ≤ Real.pi / 2 - η →
        ‖(laplaceRay q (θg j) z - ∑ s ∈ Finset.range n,
          Complex.Gamma (watsonExpC lam μ s) * a s * z ^ (-watsonExpC lam μ s)) /
            z ^ (-watsonExpC lam μ n)‖ ≤ K := by
      intro j
      obtain ⟨K, hK⟩ := (h.dlmf_2_4_1_ray' (hIcc _ (hθg_mem j)) hη hηpi).2 n
      exact ⟨K, eventually_inf_principal.mp (eventually_map.mp hK)⟩
    choose K hK using hK
    set Kmax := ∑ j ∈ Finset.range (N + 1), |K j|
    have hall := (Filter.eventually_all_finset (Finset.range (N + 1))).mpr fun j _ => hK j
    refine isBigODLMF_of_bound (K := Kmax) ?_ ?_
    · have hs := Real.sin_pos_of_pos_of_lt_pi hη (by linarith)
      filter_upwards [hall.filter_mono inf_le_left,
        (hcob_big ((σ' + 1) / Real.sin η)).filter_mono inf_le_left,
        (hcob_big 1).filter_mono inf_le_left, mem_inf_of_right (mem_principal_self Z)]
        with z hzK hzR hz1 hzZ
      have hz0 : z ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le one_pos hz1)
      have hφ0 : z ^ (-watsonExpC lam μ n) ≠ 0 := cpow_ne_zero_of_ne_zero hz0 _
      obtain ⟨j, hj, hjx⟩ := hcover _ (adaptedRay_mem hβ z)
      have ha := abs_arg_add_adaptedRay hη4 hβ h1 h2 hzZ
      have hPj : |arg z + θg j| ≤ Real.pi / 2 - η := by
        calc |arg z + θg j| = |(arg z + adaptedRay α₁ α₂ η z) - (adaptedRay α₁ α₂ η z - θg j)| := by
              ring_nf
          _ ≤ |arg z + adaptedRay α₁ α₂ η z| + |adaptedRay α₁ α₂ η z - θg j| := abs_sub _ _
          _ ≤ Real.pi / 2 - η := by linarith
      have heq : laplaceCont q α₁ α₂ η z = laplaceRay q (θg j) z :=
        h.laplaceRay_eq_of_abs (hIcc _ (adaptedRay_mem hβ z)) (hIcc _ (hθg_mem j)) hη.le hz0
          (by linarith) hPj (by rwa [div_le_iff₀' hs] at hzR)
      have hb := hzK j hj hPj
      rw [norm_div, div_le_iff₀ (norm_pos_iff.mpr hφ0)] at hb
      simp only [heq]
      calc _ ≤ K j * ‖z ^ (-watsonExpC lam μ n)‖ := hb
        _ ≤ Kmax * ‖z ^ (-watsonExpC lam μ n)‖ := by
            gcongr
            exact (le_abs_self _).trans (Finset.single_le_sum (f := fun j => |K j|)
              (fun j _ => abs_nonneg _) hj)
    · filter_upwards [(hcob_big 1).filter_mono inf_le_left] with z hz
      exact cpow_ne_zero_of_ne_zero (norm_pos_iff.mp (lt_of_lt_of_le one_pos hz)) _
  · intro θ hθ κ hκ
    set κ' := min κ η
    have hκ' : 0 < κ' := lt_min hκ hη
    have hs := Real.sin_pos_of_pos_of_lt_pi hκ' (by linarith [min_le_right κ η])
    filter_upwards [(hcob_big ((σ' + 1) / Real.sin κ')).filter_mono inf_le_left,
      (hcob_big 1).filter_mono inf_le_left, mem_inf_of_right (mem_principal_self _)]
      with z hzR hz1 hzZ
    have hz0 : z ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le one_pos hz1)
    have ha := abs_arg_add_adaptedRay hη4 hβ h1 h2 hzZ.1
    exact h.laplaceRay_eq_of_abs (hIcc _ (adaptedRay_mem hβ z)) hθ hκ'.le hz0
      (by linarith [min_le_right κ η]) (by linarith [hzZ.2, min_le_left κ η])
      (by rwa [div_le_iff₀' hs] at hzR)

/-- In `|ph z| ≤ π/2 − κ` the continuation is the original transform `∫₀^∞ e^{−zt} q(t) dt`. -/
theorem laplaceCont_eq_laplaceIntegralC (h : WatsonSector q a lam μ σ α₁ α₂) {φ₁ φ₂ : ℝ}
    (hφ₁ : -α₂ - Real.pi / 2 < φ₁) (hφ₂ : φ₂ < -α₁ + Real.pi / 2) :
    ∃ η > 0, ∀ κ > 0, ∀ᶠ z in Bornology.cobounded ℂ ⊓
        𝓟 {z | (φ₁ ≤ arg z ∧ arg z ≤ φ₂) ∧ |arg z| ≤ Real.pi / 2 - κ},
      laplaceCont q α₁ α₂ η z = laplaceIntegralC (fun t : ℝ => q t) z := by
  obtain ⟨η, hη, -, h2⟩ := h.dlmf_2_4_1_sector hφ₁ hφ₂
  refine ⟨η, hη, fun κ hκ => ?_⟩
  filter_upwards [h2 0 ⟨h.α₁_neg, h.α₂_pos⟩ κ hκ |>.filter_mono (by simp)] with z hz
  rw [hz, laplaceRay_zero]

end WatsonSector

end Azurite.DLMF
