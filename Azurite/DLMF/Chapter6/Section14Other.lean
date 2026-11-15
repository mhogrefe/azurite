/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter6.Section14

/-!
# DLMF §6.14(ii): other integrals

Formalizations of <https://dlmf.nist.gov/6.14.ii>.

## Main results

* `dlmf_6_14_4`: `∫_0^∞ E₁²(t) dt = 2 ln 2`.
* `dlmf_6_14_5`: `∫_0^∞ cos t Ci(t) dt = ∫_0^∞ sin t si(t) dt = −π/4`, as improper integrals
  (the integrands behave like `sin 2t/(2t)` and are not absolutely integrable).
* `dlmf_6_14_6`: `∫_0^∞ Ci²(t) dt = ∫_0^∞ si²(t) dt = π/2`.
* `dlmf_6_14_7`: `∫_0^∞ Ci(t) si(t) dt = ln 2`.

All by real integration by parts with explicit antiderivatives, e.g. `t Ci² − 2 sin t Ci + Si(2t)`
for `Ci²`, `t Ci si − sin t si + cos t Ci − Ci(2t)` for `Ci si`, and
`tE₁² − 2(e^{−t}E₁(t) − E₁(2t))` for `E₁²`.  The values at `0+` come from `Ci(t) − ln t → γ`,
`E₁(t) + ln t → −γ` (so `cos t Ci(t) − Ci(2t) → −ln 2`, `e^{−t}E₁(t) − E₁(2t) → ln 2`), those at
`∞` from `|Ci|, |si|, E₁ ≤ 2/t` (`abs_le_two_div`) and `Si(∞) = π/2`.  Integrability of the
products: `ln²t ≤ 16/√t` on `(0, 1]` (`log_sq_le_rpow`), `≤ 4/t²` on `(1, ∞)`
(`integrableOn_mul_of_log_bounds`).

§6.14(iii) (compendia) contains references only.
-/

open Complex Filter Topology Set MeasureTheory
open scoped Real Nat

namespace Azurite.DLMF

local notation "γ" => Real.eulerMascheroniConstant

/-! ### Real tools -/

/-- FTC on `(0, ∞)` with limits at both ends (real-valued). -/
theorem integral_Ioi_zero_of_hasDerivAt_real {Φ h : ℝ → ℝ}
    (hd : ∀ t : ℝ, 0 < t → HasDerivAt Φ (h t) t)
    (hint : IntegrableOn h (Ioi 0)) {L₀ L₁ : ℝ} (h0 : Tendsto Φ (𝓝[>] 0) (𝓝 L₀))
    (h1 : Tendsto Φ atTop (𝓝 L₁)) : ∫ t in Ioi (0 : ℝ), h t = L₁ - L₀ := by
  have hu : Ioi (0 : ℝ) = Ioc 0 1 ∪ Ioi 1 := (Ioc_union_Ioi_eq_Ioi zero_le_one).symm
  rw [hu, setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
    (hint.mono_set Ioc_subset_Ioi_self) (hint.mono_set (Ioi_subset_Ioi zero_le_one)),
    ← intervalIntegral.integral_of_le zero_le_one]
  have hA := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto zero_lt_one
    (fun x hx => hd x hx.1)
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).2
      (hint.mono_set Ioc_subset_Ioi_self)) h0
    ((hd 1 one_pos).continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
  have hB := integral_Ioi_of_hasDerivAt_of_tendsto
    (hd 1 one_pos).continuousAt.continuousWithinAt
    (fun x (hx : 1 < x) => hd x (by linarith)) (hint.mono_set (Ioi_subset_Ioi zero_le_one)) h1
  rw [hA, hB]; ring

/-- `ln²t ≤ 16/√t` on `(0, 1]`. -/
theorem log_sq_le_rpow {t : ℝ} (ht : t ∈ Ioc (0 : ℝ) 1) :
    Real.log t ^ 2 ≤ 16 * t ^ (-(1 / 2 : ℝ)) := by
  have h := Real.abs_log_mul_self_rpow_lt t (1 / 4) ht.1 ht.2 (by norm_num)
  have hq : (t ^ (1 / 4 : ℝ)) ^ 2 = t ^ (1 / 2 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul ht.1.le]; norm_num
  have hpos : 0 < t ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos ht.1 _
  have h2 : (Real.log t * t ^ (1 / 4 : ℝ)) ^ 2 < 16 := by
    have := sq_abs (Real.log t * t ^ (1 / 4 : ℝ))
    nlinarith [abs_nonneg (Real.log t * t ^ (1 / 4 : ℝ))]
  rw [mul_pow, hq] at h2
  rw [Real.rpow_neg ht.1.le, ← div_eq_mul_inv, le_div_iff₀ hpos]
  linarith

/-- A product `F G` is integrable on `(0, ∞)` if `|F|, |G| ≤ M + |ln t|` on `(0, 1]` and
`|F|, |G| ≤ 2/t` on `(1, ∞)`. -/
theorem integrableOn_mul_of_log_bounds {F G : ℝ → ℝ} (hF : ContinuousOn F (Ioi 0))
    (hG : ContinuousOn G (Ioi 0)) {M : ℝ} (hM : 0 ≤ M)
    (hF0 : ∀ t ∈ Ioc (0 : ℝ) 1, |F t| ≤ M + |Real.log t|)
    (hG0 : ∀ t ∈ Ioc (0 : ℝ) 1, |G t| ≤ M + |Real.log t|)
    (hF1 : ∀ t : ℝ, 1 < t → |F t| ≤ 2 / t) (hG1 : ∀ t : ℝ, 1 < t → |G t| ≤ 2 / t) :
    IntegrableOn (fun t => F t * G t) (Ioi 0) := by
  have hu : Ioi (0 : ℝ) = Ioc 0 1 ∪ Ioi 1 := (Ioc_union_Ioi_eq_Ioi zero_le_one).symm
  have hc : ContinuousOn (fun t => F t * G t) (Ioi 0) := hF.mul hG
  rw [hu]
  refine IntegrableOn.union ?_ ?_
  · have hr : IntegrableOn (fun t : ℝ => 2 * M ^ 2 + 32 * t ^ (-(1 / 2 : ℝ))) (Ioc 0 1) := by
      refine (integrableOn_const (by simp)).add ?_
      exact ((intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).1
        (intervalIntegral.intervalIntegrable_rpow' (by norm_num))).const_mul 32
    refine hr.mono' ((hc.mono Ioc_subset_Ioi_self).aestronglyMeasurable measurableSet_Ioc)
      ((ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun t ht => ?_))
    have h1 := hF0 t ht
    have h2 := hG0 t ht
    have hl := log_sq_le_rpow ht
    rw [Real.norm_eq_abs, abs_mul]
    have hl2 : |Real.log t| ^ 2 = Real.log t ^ 2 := sq_abs _
    have hp : |F t| * |G t| ≤ (M + |Real.log t|) ^ 2 := by
      rw [sq]; exact mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
    have hq : (M + |Real.log t|) ^ 2 ≤ 2 * M ^ 2 + 2 * |Real.log t| ^ 2 := by
      nlinarith [sq_nonneg (M - |Real.log t|)]
    rw [hl2] at hq
    linarith
  · refine ((integrableOn_Ioi_rpow_of_lt (a := -2) (by norm_num) one_pos).const_mul 4).mono'
      ((hc.mono (Ioi_subset_Ioi zero_le_one)).aestronglyMeasurable measurableSet_Ioi)
      ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun t (ht : 1 < t) => ?_))
    rw [Real.norm_eq_abs, abs_mul, show (-2 : ℝ) = ((-2 : ℤ) : ℝ) by norm_num,
      Real.rpow_intCast, zpow_neg, zpow_ofNat]
    have ht0 : 0 < t := by linarith
    calc |F t| * |G t| ≤ (2 / t) * (2 / t) :=
          mul_le_mul (hF1 t ht) (hG1 t ht) (abs_nonneg _) (by positivity)
      _ = 4 * (t ^ 2)⁻¹ := by field_simp; ring

/-- If `F(t) − σ ln t → L` as `t → 0+`, then `tF(t) → 0` and `tF(t)² → 0`. -/
theorem tendsto_mul_sq_of_sub_log {F : ℝ → ℝ} {σ L : ℝ}
    (h : Tendsto (fun t => F t - σ * Real.log t) (𝓝[>] 0) (𝓝 L)) :
    Tendsto (fun t => t * F t) (𝓝[>] 0) (𝓝 0) ∧
      Tendsto (fun t => t * F t ^ 2) (𝓝[>] 0) (𝓝 0) := by
  have ht : Tendsto (fun t : ℝ => t) (𝓝[>] 0) (𝓝 0) := tendsto_nhdsWithin_of_tendsto_nhds
    (continuous_id.tendsto 0)
  have hl : Tendsto (fun t : ℝ => Real.log t * t) (𝓝[>] 0) (𝓝 0) := by
    simpa using tendsto_log_mul_rpow_nhdsGT_zero (r := 1) one_pos
  have hl2 : Tendsto (fun t : ℝ => t * Real.log t ^ 2) (𝓝[>] 0) (𝓝 0) := by
    have := tendsto_log_mul_rpow_nhdsGT_zero (r := 1 / 2) (by norm_num)
    have := this.pow 2
    rw [zero_pow two_ne_zero] at this
    refine this.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
    rw [mul_pow, ← Real.rpow_natCast (t ^ (1 / 2 : ℝ)) 2, ← Real.rpow_mul ht.le]
    norm_num; ring
  constructor
  · have := (ht.mul h).add (hl.const_mul σ)
    rw [zero_mul, mul_zero, add_zero] at this
    exact this.congr fun t => by ring
  · have := ((ht.mul (h.pow 2)).add (h.mul (hl.const_mul (2 * σ)))).add
      (hl2.const_mul (σ ^ 2))
    simp only [zero_mul, mul_zero, add_zero] at this
    exact this.congr fun t => by ring

theorem tendsto_CiR_sub_log : Tendsto (fun t => CiR t - 1 * Real.log t) (𝓝[>] 0) (𝓝 γ) := by
  have h : Tendsto (fun t : ℝ => -CinR t + γ) (𝓝[>] 0) (𝓝 (-CinR 0 + γ)) :=
    ((continuous_CinR.neg.add continuous_const).tendsto 0).mono_left nhdsWithin_le_nhds
  rw [CinR_zero, neg_zero, zero_add] at h
  exact h.congr fun t => by rw [CiR]; ring

theorem tendsto_E1R_sub_log :
    Tendsto (fun t => expIntE₁R t - (-1) * Real.log t) (𝓝[>] 0) (𝓝 (-γ)) := by
  have h : Tendsto (fun t : ℝ => BZ.EinR t - γ) (𝓝[>] 0) (𝓝 (BZ.EinR 0 - γ)) :=
    ((continuous_EinR.sub continuous_const).tendsto 0).mono_left nhdsWithin_le_nhds
  rw [BZ.EinR_zero, zero_sub] at h
  exact h.congr fun t => by rw [expIntE₁R]; ring

/-- `|Ci(t)|, |si(t)|, E₁(t) ≤ 2/t` for `t ≥ 1`. -/
theorem abs_le_two_div {t : ℝ} (ht : 1 ≤ t) :
    |CiR t| ≤ 2 / t ∧ |SiR t - π / 2| ≤ 2 / t ∧ |expIntE₁R t| ≤ 2 / t := by
  have ht0 : 0 < t := by linarith
  obtain ⟨-, -, hF0, -, hG0, -⟩ := fR_gR_spec ht0 0
  obtain ⟨-, -, hF1, -, hG1, -⟩ := fR_gR_spec ht0 1
  simp only [pow_zero, one_mul, pow_one, fS_one, gS_one, show fS 0 t = 0 by simp [fS],
    show gS 0 t = 0 by simp [gS], sub_zero] at hF0 hG0 hF1 hG1
  have hg : gR t < 1 / t := by
    have : 1 / t ^ 2 ≤ 1 / t := by
      rw [div_le_div_iff₀ (by positivity) ht0]; nlinarith
    linarith
  have hs := Real.abs_sin_le_one t
  have hc := Real.abs_cos_le_one t
  have b : ∀ u v : ℝ, |u| ≤ 1 → |v| ≤ 1 → |fR t * u| + |gR t * v| ≤ 2 / t := by
    intro u v hu hv
    rw [abs_mul, abs_mul, abs_of_pos hF0, abs_of_pos hG0]
    have : fR t * |u| ≤ 1 / t := by nlinarith [abs_nonneg u]
    have : gR t * |v| ≤ 1 / t := by nlinarith [abs_nonneg v]
    rw [show 2 / t = 1 / t + 1 / t by ring]; linarith
  refine ⟨?_, ?_, ?_⟩
  · rw [CiR_eq ht0]; exact (abs_sub _ _).trans (b _ _ hs hc)
  · rw [SiR_eq ht0, show π / 2 - fR t * Real.cos t - gR t * Real.sin t - π / 2 =
      -(fR t * Real.cos t) - gR t * Real.sin t by ring]
    exact (abs_sub _ _).trans (by rw [abs_neg]; exact b _ _ hc hs)
  · have h := norm_expIntE₁_le_exp ht
    rw [dlmf_6_3_F1_real ht0, Complex.norm_real, Real.norm_eq_abs] at h
    refine h.trans ?_
    rw [le_div_iff₀ ht0]
    have := Real.add_one_le_exp t
    have : t * Real.exp (-t) ≤ 1 := by
      rw [Real.exp_neg, ← div_eq_mul_inv, div_le_one (Real.exp_pos t)]; linarith
    linarith [Real.exp_pos (-t)]

/-- `|Ci(t)| ≤ M + |ln t|`, `|si(t)| ≤ M`, `|E₁(t)| ≤ M + |ln t|` on `(0, 1]`. -/
theorem exists_log_bounds :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t ∈ Ioc (0 : ℝ) 1, |CiR t| ≤ M + |Real.log t| ∧
      |SiR t - π / 2| ≤ M + |Real.log t| ∧ |expIntE₁R t| ≤ M + |Real.log t| := by
  obtain ⟨B, hB⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    (f := fun t => |CinR t| + |SiR t|)
    (continuous_CinR.abs.add continuous_SiR.abs).continuousOn
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0 ⟨le_rfl, zero_le_one⟩)
  have hγ : 0 < γ := by linarith [Real.one_half_lt_eulerMascheroniConstant]
  have hE1 : 0 ≤ BZ.EinR 1 := by
    have := strictMono_EinR.monotone zero_le_one; rwa [BZ.EinR_zero] at this
  refine ⟨B + γ + π / 2 + BZ.EinR 1, by positivity, fun t ht => ?_⟩
  have hb := hB t ⟨ht.1.le, ht.2⟩
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)] at hb
  have hl := abs_nonneg (Real.log t)
  have hc := abs_nonneg (CinR t)
  have hs := abs_nonneg (SiR t)
  have hπ := Real.pi_pos
  refine ⟨?_, ?_, ?_⟩
  · rw [CiR]
    calc |-CinR t + Real.log t + γ| ≤ |CinR t| + |Real.log t| + γ := by
          rw [abs_le]; constructor <;>
            linarith [le_abs_self (CinR t), neg_abs_le (CinR t), le_abs_self (Real.log t),
              neg_abs_le (Real.log t)]
      _ ≤ _ := by linarith
  · rw [abs_le]; constructor <;> linarith [le_abs_self (SiR t), neg_abs_le (SiR t)]
  · have := norm_expIntE₁_le_log ht
    rw [dlmf_6_3_F1_real ht.1, Complex.norm_real, Real.norm_eq_abs] at this
    linarith

theorem continuousOn_CiR' : ContinuousOn CiR (Ioi 0) := continuousOn_CiR fun _ h => h

theorem continuousOn_E1R : ContinuousOn expIntE₁R (Ioi 0) := continuousOn_expIntE₁R

theorem hasDerivAt_SiR' {t : ℝ} (ht : t ≠ 0) : HasDerivAt SiR (Real.sin t / t) t := by
  have := hasDerivAt_SiR t; rwa [sincR_of_ne ht] at this

theorem hasDerivAt_CiR_two {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s => CiR (2 * s)) (Real.cos (2 * t) / t) t := by
  have h := (hasDerivAt_CiR (by positivity : 0 < 2 * t)).comp t ((hasDerivAt_id t).const_mul 2)
  refine h.congr_deriv ?_
  field_simp

theorem hasDerivAt_SiR_two {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s => SiR (2 * s)) (Real.sin (2 * t) / t) t := by
  have h := (hasDerivAt_SiR' (by positivity : 2 * t ≠ 0)).comp t ((hasDerivAt_id t).const_mul 2)
  refine h.congr_deriv ?_
  field_simp

theorem tendsto_two_mul_nhdsGT : Tendsto (fun t : ℝ => 2 * t) (𝓝[>] 0) (𝓝[>] 0) := by
  refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
  · have hc : Continuous fun t : ℝ => 2 * t := by fun_prop
    have := (hc.tendsto (0 : ℝ)).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
    simpa using this
  · filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
    exact mul_pos two_pos ht

theorem tendsto_two_mul_atTop : Tendsto (fun t : ℝ => 2 * t) atTop atTop :=
  tendsto_id.const_mul_atTop two_pos

theorem tendsto_id_nhdsGT : Tendsto (fun t : ℝ => t) (𝓝[>] 0) (𝓝 0) :=
  tendsto_nhdsWithin_of_tendsto_nhds (continuous_id.tendsto 0)

/-- `sin t · F(t) → 0` as `t → 0+` when `tF(t) → 0`. -/
theorem tendsto_sin_mul_of {F : ℝ → ℝ} (h : Tendsto (fun t => t * F t) (𝓝[>] 0) (𝓝 0)) :
    Tendsto (fun t => Real.sin t * F t) (𝓝[>] 0) (𝓝 0) := by
  have hn : Tendsto (fun t => ‖t * F t‖) (𝓝[>] 0) (𝓝 0) := by simpa using h.norm
  refine squeeze_zero_norm' ?_ hn
  filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
  simp only [norm_mul, Real.norm_eq_abs, abs_of_pos ht]
  gcongr
  exact (Real.abs_sin_le_abs (x := t)).trans (le_of_eq (abs_of_pos ht))

/-- `(cos t − 1) F(t) → 0` and `(e^{−t} − 1) F(t) → 0` as `t → 0+` when `tF(t) → 0`. -/
theorem tendsto_cos_exp_sub_one_mul {F : ℝ → ℝ} (h : Tendsto (fun t => t * F t) (𝓝[>] 0) (𝓝 0)) :
    Tendsto (fun t => (Real.cos t - 1) * F t) (𝓝[>] 0) (𝓝 0) ∧
      Tendsto (fun t => (Real.exp (-t) - 1) * F t) (𝓝[>] 0) (𝓝 0) := by
  have hn : Tendsto (fun t => ‖t * F t‖) (𝓝[>] 0) (𝓝 0) := by simpa using h.norm
  constructor <;> refine squeeze_zero_norm' ?_ hn <;>
    filter_upwards [self_mem_nhdsWithin, Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)]
      with t (ht : 0 < t) ht1 <;>
    simp only [norm_mul, Real.norm_eq_abs, abs_of_pos ht] <;> gcongr
  · have h1 := Real.cos_le_one t
    have h2 := Real.one_sub_sq_div_two_le_cos (x := t)
    rw [abs_le]; constructor <;> nlinarith [ht1.2]
  · have h1 : Real.exp (-t) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
    have h2 := Real.add_one_le_exp (-t)
    rw [abs_le]; constructor <;> linarith

theorem tendsto_div_two_atTop : Tendsto (fun t : ℝ => 2 / t) atTop (𝓝 0) :=
  tendsto_const_nhds.div_atTop tendsto_id

/-- `t F(t) G(t) → 0` and `F(t)G'(t)`-type products vanish at `∞` when `|F|, |G| ≤ 2/t`. -/
theorem tendsto_atTop_of_le_two_div {F : ℝ → ℝ} (hF : ∀ t : ℝ, 1 ≤ t → |F t| ≤ 2 / t)
    {G : ℝ → ℝ} (hG : ∀ t : ℝ, 1 ≤ t → |G t| ≤ 2) :
    Tendsto (fun t => G t * F t) atTop (𝓝 0) := by
  have h := tendsto_div_two_atTop.const_mul 2
  rw [mul_zero] at h
  refine squeeze_zero_norm' ?_ h
  filter_upwards [eventually_ge_atTop 1] with t ht
  rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
  exact mul_le_mul (hG t ht) (hF t ht) (abs_nonneg _) zero_le_two

theorem tendsto_mul_mul_atTop_of_le_two_div {F G : ℝ → ℝ} (hF : ∀ t : ℝ, 1 ≤ t → |F t| ≤ 2 / t)
    (hG : ∀ t : ℝ, 1 ≤ t → |G t| ≤ 2 / t) :
    Tendsto (fun t => t * F t * G t) atTop (𝓝 0) := by
  refine (tendsto_atTop_of_le_two_div hG (G := fun t => t * F t) fun t ht => ?_).congr
    fun t => by ring
  have := hF t ht
  rw [abs_mul, abs_of_pos (by linarith)]
  calc t * |F t| ≤ t * (2 / t) := by gcongr
    _ = 2 := by field_simp

/-! ### The real integrals -/

/-- **6.14.6** (real form): `∫_0^∞ Ci²(t) dt = π/2`. -/
theorem integral_CiR_sq : ∫ t in Ioi (0 : ℝ), CiR t * CiR t = π / 2 := by
  obtain ⟨M, hM, hb⟩ := exists_log_bounds
  have hd : ∀ t : ℝ, 0 < t → HasDerivAt (fun t => t * CiR t * CiR t - 2 * Real.sin t * CiR t +
      SiR (2 * t)) (CiR t * CiR t) t := by
    intro t ht
    have hC := hasDerivAt_CiR ht
    have h := ((((hasDerivAt_id t).mul hC).mul hC).sub (((Real.hasDerivAt_sin t).const_mul 2).mul
      hC)).add (hasDerivAt_SiR_two ht)
    refine h.congr_deriv ?_
    simp only [id, Pi.mul_apply, one_mul]
    rw [Real.sin_two_mul]; field_simp; ring
  have hint := integrableOn_mul_of_log_bounds continuousOn_CiR' continuousOn_CiR' hM
    (fun t ht => (hb t ht).1) (fun t ht => (hb t ht).1)
    (fun t ht => (abs_le_two_div ht.le).1) (fun t ht => (abs_le_two_div ht.le).1)
  obtain ⟨h1, h2⟩ := tendsto_mul_sq_of_sub_log tendsto_CiR_sub_log
  have h0 : Tendsto (fun t => t * CiR t * CiR t - 2 * Real.sin t * CiR t + SiR (2 * t))
      (𝓝[>] 0) (𝓝 (0 - 2 * 0 + SiR (2 * 0))) := by
    refine ((h2.congr fun t => by ring).sub ((tendsto_sin_mul_of h1).const_mul 2 |>.congr
      fun t => by ring)).add ?_
    exact ((continuous_SiR.comp (continuous_const.mul continuous_id)).tendsto 0).mono_left
      nhdsWithin_le_nhds
  have hinf : Tendsto (fun t => t * CiR t * CiR t - 2 * Real.sin t * CiR t + SiR (2 * t))
      atTop (𝓝 (0 - 2 * 0 + π / 2)) := by
    refine ((tendsto_mul_mul_atTop_of_le_two_div (fun t ht => (abs_le_two_div ht).1)
      (fun t ht => (abs_le_two_div ht).1)).sub ((tendsto_atTop_of_le_two_div
        (fun t ht => (abs_le_two_div ht).1) (G := Real.sin) fun t _ => by
          linarith [Real.abs_sin_le_one t]).const_mul 2 |>.congr fun t => by ring)).add ?_
    exact tendsto_SiR.comp tendsto_two_mul_atTop
  rw [integral_Ioi_zero_of_hasDerivAt_real hd hint h0 hinf, mul_zero, SiR_zero]; ring

/-- **6.14.6** (real form): `∫_0^∞ si²(t) dt = π/2`. -/
theorem integral_siR_sq :
    ∫ t in Ioi (0 : ℝ), (SiR t - π / 2) * (SiR t - π / 2) = π / 2 := by
  obtain ⟨M, hM, hb⟩ := exists_log_bounds
  have hcs : ContinuousOn (fun t => SiR t - π / 2) (Ioi 0) :=
    (continuous_SiR.sub continuous_const).continuousOn
  have hd : ∀ t : ℝ, 0 < t → HasDerivAt (fun t => t * (SiR t - π / 2) * (SiR t - π / 2) +
      2 * Real.cos t * (SiR t - π / 2) - SiR (2 * t)) ((SiR t - π / 2) * (SiR t - π / 2)) t := by
    intro t ht
    have hS := (hasDerivAt_SiR' ht.ne').sub_const (π / 2)
    have h := ((((hasDerivAt_id t).mul hS).mul hS).add (((Real.hasDerivAt_cos t).const_mul 2).mul
      hS)).sub (hasDerivAt_SiR_two ht)
    refine h.congr_deriv ?_
    simp only [id, Pi.mul_apply, one_mul]
    rw [Real.sin_two_mul]; field_simp; ring
  have hint := integrableOn_mul_of_log_bounds hcs hcs hM
    (fun t ht => (hb t ht).2.1) (fun t ht => (hb t ht).2.1)
    (fun t ht => (abs_le_two_div ht.le).2.1) (fun t ht => (abs_le_two_div ht.le).2.1)
  have hs0 : Tendsto (fun t => SiR t - π / 2) (𝓝[>] 0) (𝓝 (SiR 0 - π / 2)) :=
    (((continuous_SiR.sub continuous_const).tendsto 0)).mono_left nhdsWithin_le_nhds
  have hc0 : Tendsto Real.cos (𝓝[>] 0) (𝓝 (Real.cos 0)) :=
    (Real.continuous_cos.tendsto 0).mono_left nhdsWithin_le_nhds
  have h0 : Tendsto (fun t => t * (SiR t - π / 2) * (SiR t - π / 2) +
      2 * Real.cos t * (SiR t - π / 2) - SiR (2 * t)) (𝓝[>] 0)
      (𝓝 (0 * (SiR 0 - π / 2) * (SiR 0 - π / 2) + 2 * Real.cos 0 * (SiR 0 - π / 2) -
        SiR (2 * 0))) := by
    refine (((tendsto_id_nhdsGT.mul hs0).mul hs0).add ((hc0.const_mul 2).mul hs0)).sub ?_
    exact ((continuous_SiR.comp (continuous_const.mul continuous_id)).tendsto 0).mono_left
      nhdsWithin_le_nhds
  have hinf : Tendsto (fun t => t * (SiR t - π / 2) * (SiR t - π / 2) +
      2 * Real.cos t * (SiR t - π / 2) - SiR (2 * t)) atTop (𝓝 (0 + 2 * 0 - π / 2)) := by
    refine ((tendsto_mul_mul_atTop_of_le_two_div (fun t ht => (abs_le_two_div ht).2.1)
      (fun t ht => (abs_le_two_div ht).2.1)).add ((tendsto_atTop_of_le_two_div
        (fun t ht => (abs_le_two_div ht).2.1) (G := Real.cos) fun t _ => by
          linarith [Real.abs_cos_le_one t]).const_mul 2 |>.congr fun t => by ring)).sub ?_
    exact tendsto_SiR.comp tendsto_two_mul_atTop
  rw [integral_Ioi_zero_of_hasDerivAt_real hd hint h0 hinf, mul_zero, SiR_zero, Real.cos_zero]
  ring

/-- **6.14.7** (real form): `∫_0^∞ Ci(t) si(t) dt = ln 2`. -/
theorem integral_CiR_siR : ∫ t in Ioi (0 : ℝ), CiR t * (SiR t - π / 2) = Real.log 2 := by
  obtain ⟨M, hM, hb⟩ := exists_log_bounds
  have hcs : ContinuousOn (fun t => SiR t - π / 2) (Ioi 0) :=
    (continuous_SiR.sub continuous_const).continuousOn
  set Φ := fun t => t * CiR t * (SiR t - π / 2) - Real.sin t * (SiR t - π / 2) +
    Real.cos t * CiR t - CiR (2 * t)
  have hd : ∀ t : ℝ, 0 < t → HasDerivAt Φ (CiR t * (SiR t - π / 2)) t := by
    intro t ht
    have hC := hasDerivAt_CiR ht
    have hS := (hasDerivAt_SiR' ht.ne').sub_const (π / 2)
    have h := (((((hasDerivAt_id t).mul hC).mul hS).sub ((Real.hasDerivAt_sin t).mul hS)).add
      ((Real.hasDerivAt_cos t).mul hC)).sub (hasDerivAt_CiR_two ht)
    refine h.congr_deriv ?_
    simp only [id, Pi.mul_apply, one_mul]
    rw [Real.cos_two_mul]
    field_simp
    linear_combination (-2) * Real.sin_sq_add_cos_sq t
  have hint := integrableOn_mul_of_log_bounds continuousOn_CiR' hcs hM
    (fun t ht => (hb t ht).1) (fun t ht => (hb t ht).2.1)
    (fun t ht => (abs_le_two_div ht.le).1) (fun t ht => (abs_le_two_div ht.le).2.1)
  obtain ⟨h1, -⟩ := tendsto_mul_sq_of_sub_log tendsto_CiR_sub_log
  have hs0 : Tendsto (fun t => SiR t - π / 2) (𝓝[>] 0) (𝓝 (SiR 0 - π / 2)) :=
    (((continuous_SiR.sub continuous_const).tendsto 0)).mono_left nhdsWithin_le_nhds
  have hsin0 : Tendsto Real.sin (𝓝[>] 0) (𝓝 (Real.sin 0)) :=
    (Real.continuous_sin.tendsto 0).mono_left nhdsWithin_le_nhds
  -- `cos t Ci(t) − Ci(2t) → −ln 2`
  have hkey : Tendsto (fun t => Real.cos t * CiR t - CiR (2 * t)) (𝓝[>] 0)
      (𝓝 (0 + γ - γ - Real.log 2)) := by
    have hA := (tendsto_cos_exp_sub_one_mul h1).1
    have hB := tendsto_CiR_sub_log
    have hC := tendsto_CiR_sub_log.comp tendsto_two_mul_nhdsGT
    refine (((hA.add hB).sub hC).sub tendsto_const_nhds).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
    simp only [Function.comp]
    rw [Real.log_mul two_ne_zero ht.ne']; ring
  have h0 : Tendsto Φ (𝓝[>] 0)
      (𝓝 (0 * (SiR 0 - π / 2) - Real.sin 0 * (SiR 0 - π / 2) + (0 + γ - γ - Real.log 2))) := by
    refine (((h1.mul hs0).sub (hsin0.mul hs0)).add hkey).congr fun t => ?_
    simp only [Φ]; ring
  have hinf : Tendsto Φ atTop (𝓝 (0 - 0 + 0 - 0)) := by
    refine (((tendsto_mul_mul_atTop_of_le_two_div (fun t ht => (abs_le_two_div ht).1)
      (fun t ht => (abs_le_two_div ht).2.1)).sub (tendsto_atTop_of_le_two_div
        (fun t ht => (abs_le_two_div ht).2.1) (G := Real.sin) fun t _ => by
          linarith [Real.abs_sin_le_one t])).add (tendsto_atTop_of_le_two_div
        (fun t ht => (abs_le_two_div ht).1) (G := Real.cos) fun t _ => by
          linarith [Real.abs_cos_le_one t])).sub ?_
    exact tendsto_CiR.comp tendsto_two_mul_atTop
  rw [integral_Ioi_zero_of_hasDerivAt_real hd hint h0 hinf, Real.sin_zero]; ring

/-- **6.14.4** (real form): `∫_0^∞ E₁²(t) dt = 2 ln 2`. -/
theorem integral_E1R_sq : ∫ t in Ioi (0 : ℝ), expIntE₁R t * expIntE₁R t = 2 * Real.log 2 := by
  obtain ⟨M, hM, hb⟩ := exists_log_bounds
  set Φ := fun t => t * expIntE₁R t * expIntE₁R t -
    2 * (Real.exp (-t) * expIntE₁R t - expIntE₁R (2 * t))
  have hd : ∀ t : ℝ, 0 < t → HasDerivAt Φ (expIntE₁R t * expIntE₁R t) t := by
    intro t ht
    have hE := hasDerivAt_expIntE₁R ht
    have hE2 := (hasDerivAt_expIntE₁R (by positivity : 0 < 2 * t)).comp t
      ((hasDerivAt_id t).const_mul 2)
    have hexp := (hasDerivAt_neg t).exp
    have h := (((hasDerivAt_id t).mul hE).mul hE).sub
      (((hexp.mul hE).sub hE2).const_mul 2)
    refine h.congr_deriv ?_
    simp only [id, Pi.mul_apply, mul_one, one_mul]
    rw [show -(2 * t) = -t + -t by ring, Real.exp_add]
    field_simp; ring
  have hint := integrableOn_mul_of_log_bounds continuousOn_E1R continuousOn_E1R hM
    (fun t ht => (hb t ht).2.2) (fun t ht => (hb t ht).2.2)
    (fun t ht => (abs_le_two_div ht.le).2.2) (fun t ht => (abs_le_two_div ht.le).2.2)
  obtain ⟨h1, h2⟩ := tendsto_mul_sq_of_sub_log tendsto_E1R_sub_log
  have hkey : Tendsto (fun t => Real.exp (-t) * expIntE₁R t - expIntE₁R (2 * t)) (𝓝[>] 0)
      (𝓝 (0 + -γ - -γ + Real.log 2)) := by
    have hA := (tendsto_cos_exp_sub_one_mul h1).2
    have hB := tendsto_E1R_sub_log
    have hC := tendsto_E1R_sub_log.comp tendsto_two_mul_nhdsGT
    refine (((hA.add hB).sub hC).add tendsto_const_nhds).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
    simp only [Function.comp]
    rw [Real.log_mul two_ne_zero ht.ne']; ring
  have h2' : Tendsto (fun t => t * expIntE₁R t * expIntE₁R t) (𝓝[>] 0) (𝓝 0) :=
    h2.congr fun t => by ring
  have h0 : Tendsto Φ (𝓝[>] 0) (𝓝 (0 - 2 * (0 + -γ - -γ + Real.log 2))) :=
    h2'.sub (hkey.const_mul 2)
  have hinf : Tendsto Φ atTop (𝓝 (0 - 2 * (0 - 0))) := by
    refine (tendsto_mul_mul_atTop_of_le_two_div (fun t ht => (abs_le_two_div ht).2.2)
      (fun t ht => (abs_le_two_div ht).2.2)).sub ((tendsto_atTop_of_le_two_div
        (fun t ht => (abs_le_two_div ht).2.2) (G := fun t => Real.exp (-t)) fun t ht => by
          rw [abs_of_pos (Real.exp_pos _)]
          linarith [Real.exp_le_one_iff.2 (by linarith : -t ≤ 0)]).sub ?_ |>.const_mul 2)
    have := (tendsto_atTop_of_le_two_div (fun t ht => (abs_le_two_div ht).2.2)
      (G := fun _ => (1 : ℝ)) fun _ _ => by norm_num).comp tendsto_two_mul_atTop
    simpa [Function.comp_def] using this
  rw [integral_Ioi_zero_of_hasDerivAt_real hd hint h0 hinf]; ring

/-! ### 6.14.5 (improper) -/

theorem intervalIntegrable_of_log_bound {h : ℝ → ℝ} (hc : ContinuousOn h (Ioi 0)) {M : ℝ}
    (h01 : ∀ t ∈ Ioc (0 : ℝ) 1, |h t| ≤ M + |Real.log t|) {R : ℝ} (hR : 0 < R) :
    IntervalIntegrable h volume 0 R := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hR.le]
  have hu : Ioc (0 : ℝ) (max R 1) = Ioc 0 1 ∪ Ioc 1 (max R 1) :=
    (Ioc_union_Ioc_eq_Ioc zero_le_one (le_max_right R 1)).symm
  refine IntegrableOn.mono_set ?_ (Ioc_subset_Ioc_right (le_max_left R 1))
  rw [hu]
  refine IntegrableOn.union ?_ ?_
  · have hlog : IntegrableOn (fun t => M + |Real.log t|) (Ioc 0 1) := by
      refine (integrableOn_const (by simp)).add ?_
      exact ((intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).1
        (intervalIntegral.intervalIntegrable_log' (a := 0) (b := 1))).norm
    refine hlog.mono' ((hc.mono Ioc_subset_Ioi_self).aestronglyMeasurable measurableSet_Ioc)
      ((ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun t ht => ?_))
    rw [Real.norm_eq_abs]; exact h01 t ht
  · exact ((hc.mono fun t ht => lt_of_lt_of_le one_pos ht.1).integrableOn_Icc).mono_set
      Ioc_subset_Icc_self

/-- **6.14.5** (real form, improper): `∫_0^∞ cos t Ci(t) dt = −π/4`. -/
theorem tendsto_integral_cos_CiR :
    Tendsto (fun R => ∫ t in (0 : ℝ)..R, Real.cos t * CiR t) atTop (𝓝 (-(π / 4))) := by
  obtain ⟨M, hM, hb⟩ := exists_log_bounds
  set Ψ := fun t => Real.sin t * CiR t - SiR (2 * t) / 2
  have hd : ∀ t : ℝ, 0 < t → HasDerivAt Ψ (Real.cos t * CiR t) t := by
    intro t ht
    have h := ((Real.hasDerivAt_sin t).mul (hasDerivAt_CiR ht)).sub
      ((hasDerivAt_SiR_two ht).div_const 2)
    refine h.congr_deriv ?_
    rw [Real.sin_two_mul]; field_simp; ring
  obtain ⟨h1, -⟩ := tendsto_mul_sq_of_sub_log tendsto_CiR_sub_log
  have h0 : Tendsto Ψ (𝓝[>] 0) (𝓝 (0 - SiR (2 * 0) / 2)) :=
    (tendsto_sin_mul_of h1).sub ((((continuous_SiR.comp (continuous_const.mul
      continuous_id)).tendsto 0).mono_left nhdsWithin_le_nhds).div_const 2)
  rw [mul_zero, SiR_zero, zero_div, sub_zero] at h0
  have hint : ∀ R : ℝ, 0 < R → ∫ t in (0 : ℝ)..R, Real.cos t * CiR t = Ψ R := fun R hR => by
    have := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto hR
      (fun x hx => hd x hx.1)
      (intervalIntegrable_of_log_bound
        ((Real.continuous_cos.continuousOn).mul continuousOn_CiR') (M := M) (fun t ht => by
          show |Real.cos t * CiR t| ≤ _
          rw [abs_mul]
          exact (mul_le_of_le_one_left (abs_nonneg _) (Real.abs_cos_le_one t)).trans (hb t ht).1)
        hR) h0 ((hd R hR).continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
    rw [this, sub_zero]
  have hinf : Tendsto Ψ atTop (𝓝 (0 - π / 2 / 2)) :=
    (tendsto_atTop_of_le_two_div (fun t ht => (abs_le_two_div ht).1) (G := Real.sin)
      fun t _ => by linarith [Real.abs_sin_le_one t]).sub
      ((tendsto_SiR.comp tendsto_two_mul_atTop).div_const 2)
  refine (hinf.congr' ?_).trans (by rw [show (0 : ℝ) - π / 2 / 2 = -(π / 4) by ring])
  filter_upwards [eventually_gt_atTop 0] with R hR
  exact (hint R hR).symm

/-- **6.14.5** (real form, improper): `∫_0^∞ sin t si(t) dt = −π/4`. -/
theorem tendsto_integral_sin_siR :
    Tendsto (fun R => ∫ t in (0 : ℝ)..R, Real.sin t * (SiR t - π / 2)) atTop
      (𝓝 (-(π / 4))) := by
  obtain ⟨M, hM, hb⟩ := exists_log_bounds
  set Ψ := fun t => -(Real.cos t * (SiR t - π / 2)) + SiR (2 * t) / 2
  have hd : ∀ t : ℝ, 0 < t → HasDerivAt Ψ (Real.sin t * (SiR t - π / 2)) t := by
    intro t ht
    have h := (((Real.hasDerivAt_cos t).mul ((hasDerivAt_SiR' ht.ne').sub_const (π / 2))).neg).add
      ((hasDerivAt_SiR_two ht).div_const 2)
    refine h.congr_deriv ?_
    rw [Real.sin_two_mul]; field_simp; ring
  have h0 : Tendsto Ψ (𝓝[>] 0) (𝓝 (-(Real.cos 0 * (SiR 0 - π / 2)) + SiR (2 * 0) / 2)) := by
    have : Continuous Ψ := by
      simp only [Ψ]
      exact ((Real.continuous_cos.mul (continuous_SiR.sub continuous_const)).neg).add
        ((continuous_SiR.comp (continuous_const.mul continuous_id)).div_const 2)
    exact (this.tendsto 0).mono_left nhdsWithin_le_nhds
  rw [mul_zero, SiR_zero, Real.cos_zero, zero_div, add_zero] at h0
  have hint : ∀ R : ℝ, 0 < R → ∫ t in (0 : ℝ)..R, Real.sin t * (SiR t - π / 2) =
      Ψ R - π / 2 := fun R hR => by
    have := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto hR
      (fun x hx => hd x hx.1)
      (intervalIntegrable_of_log_bound ((Real.continuous_sin.continuousOn).mul
        (continuous_SiR.sub continuous_const).continuousOn) (M := M) (fun t ht => by
          show |Real.sin t * (SiR t - π / 2)| ≤ _
          rw [abs_mul]
          exact (mul_le_of_le_one_left (abs_nonneg _) (Real.abs_sin_le_one t)).trans
            (hb t ht).2.1) hR) h0 ((hd R hR).continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
    rw [this]; ring
  have hinf : Tendsto (fun R => Ψ R - π / 2) atTop (𝓝 (-0 + π / 2 / 2 - π / 2)) :=
    (((tendsto_atTop_of_le_two_div (fun t ht => (abs_le_two_div ht).2.1) (G := Real.cos)
      fun t _ => by linarith [Real.abs_cos_le_one t]).neg).add
      ((tendsto_SiR.comp tendsto_two_mul_atTop).div_const 2)).sub_const _
  refine (hinf.congr' ?_).trans (by rw [show -(0 : ℝ) + π / 2 / 2 - π / 2 = -(π / 4) by ring])
  filter_upwards [eventually_gt_atTop 0] with R hR
  exact (hint R hR).symm

/-! ### The DLMF statements -/

theorem integral_Ioi_ofReal_congr {F : ℝ → ℂ} {f : ℝ → ℝ} (h : ∀ t : ℝ, 0 < t → F t = f t) :
    ∫ t in Ioi (0 : ℝ), F t = ((∫ t in Ioi (0 : ℝ), f t : ℝ) : ℂ) := by
  rw [← integral_complex_ofReal]
  exact setIntegral_congr_fun measurableSet_Ioi fun t ht => h t ht

theorem intervalIntegral_ofReal_congr {F : ℝ → ℂ} {f : ℝ → ℝ} (h : ∀ t : ℝ, 0 < t → F t = f t)
    {R : ℝ} (hR : 0 ≤ R) : ∫ t in (0 : ℝ)..R, F t = ((∫ t in (0 : ℝ)..R, f t : ℝ) : ℂ) := by
  rw [intervalIntegral.integral_of_le hR, intervalIntegral.integral_of_le hR,
    ← integral_complex_ofReal]
  exact setIntegral_congr_fun measurableSet_Ioc fun t ht => h t ht.1

/-- **DLMF 6.14.4**: `∫_0^∞ E₁²(t) dt = 2 ln 2`. -/
theorem dlmf_6_14_4 : ∫ t in Ioi (0 : ℝ), expIntE₁ t ^ 2 = 2 * Real.log 2 := by
  rw [integral_Ioi_ofReal_congr (f := fun t => expIntE₁R t * expIntE₁R t) fun t ht => by
    rw [dlmf_6_3_F1_real ht]; push_cast; ring, integral_E1R_sq]
  push_cast; ring

/-- **DLMF 6.14.5**: `∫_0^∞ cos t Ci(t) dt = ∫_0^∞ sin t si(t) dt = −π/4` (improper integrals; the
integrands are not absolutely integrable). -/
theorem dlmf_6_14_5 :
    Tendsto (fun R => ∫ t in (0 : ℝ)..R, Complex.cos t * Ci t) atTop (𝓝 (-(π / 4))) ∧
      Tendsto (fun R => ∫ t in (0 : ℝ)..R, Complex.sin t * si t) atTop (𝓝 (-(π / 4))) := by
  have hc : Continuous fun x : ℝ => (x : ℂ) := continuous_ofReal
  constructor
  · have := (hc.tendsto _).comp tendsto_integral_cos_CiR
    refine (this.congr' ?_).trans (by push_cast; rfl)
    filter_upwards [eventually_ge_atTop 0] with R hR
    simp only [Function.comp]
    rw [intervalIntegral_ofReal_congr (f := fun t => Real.cos t * CiR t) (fun t ht => by
      rw [Ci_ofReal ht]; push_cast; ring) hR]
  · have := (hc.tendsto _).comp tendsto_integral_sin_siR
    refine (this.congr' ?_).trans (by push_cast; rfl)
    filter_upwards [eventually_ge_atTop 0] with R hR
    simp only [Function.comp]
    rw [intervalIntegral_ofReal_congr (f := fun t => Real.sin t * (SiR t - π / 2))
      (fun t _ => by rw [si_ofReal]; push_cast; ring) hR]

/-- **DLMF 6.14.6**: `∫_0^∞ Ci²(t) dt = ∫_0^∞ si²(t) dt = π/2`. -/
theorem dlmf_6_14_6 :
    ∫ t in Ioi (0 : ℝ), Ci t ^ 2 = π / 2 ∧ ∫ t in Ioi (0 : ℝ), si t ^ 2 = π / 2 := by
  constructor
  · rw [integral_Ioi_ofReal_congr (f := fun t => CiR t * CiR t) fun t ht => by
      rw [Ci_ofReal ht]; push_cast; ring, integral_CiR_sq]
    push_cast; ring
  · rw [integral_Ioi_ofReal_congr (f := fun t => (SiR t - π / 2) * (SiR t - π / 2)) fun t _ => by
      rw [si_ofReal]; push_cast; ring, integral_siR_sq]
    push_cast; ring

/-- **DLMF 6.14.7**: `∫_0^∞ Ci(t) si(t) dt = ln 2`. -/
theorem dlmf_6_14_7 : ∫ t in Ioi (0 : ℝ), Ci t * si t = Real.log 2 := by
  rw [integral_Ioi_ofReal_congr (f := fun t => CiR t * (SiR t - π / 2)) fun t ht => by
    rw [Ci_ofReal ht, si_ofReal]; push_cast; ring, integral_CiR_siR]

end Azurite.DLMF
