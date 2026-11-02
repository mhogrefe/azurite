/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/


import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.NonIntegrable
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Azurite.DLMF.Chapter2.Section1Generalized

/-!
# DLMF §2.6(i) Distributional Methods: Divergent Integrals (2.6.1–2.6.7)

The motivating example: `S(x) = ∫₀^∞ dt / ((1 + t)^{1/3} (x + t))`, `x > 0` (2.6.1, `dlmfS`,
convergent: `integrableOn_dlmfS`). For `t > 1`, `(1 + t)^{−1/3} = ∑ binom(−1/3, s) t^{−s−1/3}`
(2.6.2, `dlmf_2_6_2`, from Mathlib's binomial series). Substituting and integrating term by term
produces the integrals `∫₀^∞ t^{−s−1/3}/(x + t) dt` (2.6.3), which diverge for `s ≥ 1`
(`dlmf_2_6_3`). They can be given a generalized meaning: for `ℜα, ℜβ > 0`,

`∫₀^∞ t^{α−1}/(x + t)^{α+β} dt = Γ(α)Γ(β)/Γ(α + β) · x^{−β}` (2.6.4, `dlmf_2_6_4`, the beta
integral after `t = xu`, `u = v/(1 − v)`),

and the right side makes sense for all `α, β` off the non-positive integers. Taking it as the
definition of the left side (`genBetaIntegral`), `∫₀^∞ t^{−s−1/3}/(x + t) dt = (2π/√3) (−1)^s
x^{−s−1/3}` (2.6.5, `dlmf_2_6_5`; for `s = 0` this is the honest value, `dlmf_2_6_5_zero`). The
formal term-by-term result is 2.6.6 (`dlmf_2_6_6_formal`), which is *incorrect*: the correct
expansion 2.6.7 has an additional series `−∑_{s≥1} 3^s (s−1)!/(2·5⋯(3s−1)) x^{−s}`, and is
derived in §2.6(ii). Both 2.6.7 and the failure of 2.6.6 are recorded there.
-/

open MeasureTheory Filter Topology Set Complex Asymptotics
open scoped Real Nat Interval

namespace Azurite.DLMF

/-! ### 2.6.1 -/

/-- **DLMF 2.6.1**: `S(x) = ∫₀^∞ dt / ((1 + t)^{1/3} (x + t))`. -/
noncomputable def dlmfS (x : ℝ) : ℝ := ∫ t in Ioi (0 : ℝ), 1 / ((1 + t) ^ (1 / 3 : ℝ) * (x + t))

/-- `x + t ≥ min(x, 1) (1 + t)` for `x, t > 0`. -/
theorem min_mul_one_add_le {x t : ℝ} (ht : 0 ≤ t) : min x 1 * (1 + t) ≤ x + t := by
  rcases le_total x 1 with h | h
  · rw [min_eq_left h]
    nlinarith
  · rw [min_eq_right h]
    linarith

/-- The integral 2.6.1 converges for `x > 0`. -/
theorem integrableOn_dlmfS {x : ℝ} (hx : 0 < x) :
    IntegrableOn (fun t : ℝ => 1 / ((1 + t) ^ (1 / 3 : ℝ) * (x + t))) (Ioi 0) := by
  have hcont : ContinuousOn (fun t : ℝ => 1 / ((1 + t) ^ (1 / 3 : ℝ) * (x + t))) (Ici 0) := by
    have h1 : ContinuousOn (fun t : ℝ => 1 + t) (Ici 0) := continuousOn_const.add continuousOn_id
    have h2 : ContinuousOn (fun t : ℝ => x + t) (Ici 0) := continuousOn_const.add continuousOn_id
    have h3 : ContinuousOn (fun t : ℝ => (1 + t) ^ (1 / 3 : ℝ)) (Ici 0) :=
      h1.rpow_const fun t ht => Or.inl (by linarith [mem_Ici.mp ht])
    have h4 : ContinuousOn (fun t : ℝ => (1 + t) ^ (1 / 3 : ℝ) * (x + t)) (Ici 0) := h3.mul h2
    exact continuousOn_const.div h4 fun t ht => mul_ne_zero
      (Real.rpow_pos_of_pos (by linarith [mem_Ici.mp ht]) _).ne' (by linarith [mem_Ici.mp ht])
  -- on `(0, 1]`: continuous; on `(1, ∞)`: dominated by `t^{−4/3}/min(x,1)`
  have h1 : IntegrableOn (fun t : ℝ => 1 / ((1 + t) ^ (1 / 3 : ℝ) * (x + t))) (Ioc 0 1) :=
    ((hcont.mono Icc_subset_Ici_self).integrableOn_compact isCompact_Icc).mono_set
      Ioc_subset_Icc_self
  have h2 : IntegrableOn (fun t : ℝ => 1 / ((1 + t) ^ (1 / 3 : ℝ) * (x + t))) (Ioi 1) := by
    have hm : 0 < min x 1 := lt_min hx one_pos
    have hint : IntegrableOn (fun t : ℝ => (min x 1)⁻¹ * t ^ (-(4 / 3 : ℝ))) (Ioi 1) :=
      ((integrableOn_Ioi_rpow_iff zero_lt_one).mpr (by norm_num)).const_mul _
    refine Integrable.mono' hint ((hcont.mono fun t ht =>
      (zero_lt_one.trans (mem_Ioi.mp ht)).le).aestronglyMeasurable measurableSet_Ioi) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht : (1 : ℝ) < t := ht
    have hpos : 0 < (1 + t) ^ (1 / 3 : ℝ) * (x + t) :=
      mul_pos (Real.rpow_pos_of_pos (by linarith) _) (by linarith)
    have ht0 : (0 : ℝ) < t := by linarith
    have e : (min x 1)⁻¹ * t ^ (-(4 / 3 : ℝ)) = 1 / (min x 1 * (t ^ (1 / 3 : ℝ) * t)) := by
      rw [Real.rpow_neg ht0.le, show (4 / 3 : ℝ) = 1 / 3 + 1 by norm_num, Real.rpow_add ht0,
        Real.rpow_one]
      field_simp
    rw [Real.norm_of_nonneg (by positivity), e]
    refine one_div_le_one_div_of_le (by positivity) ?_
    calc min x 1 * (t ^ (1 / 3 : ℝ) * t) = t ^ (1 / 3 : ℝ) * (min x 1 * t) := by ring
      _ ≤ (1 + t) ^ (1 / 3 : ℝ) * (x + t) := by
          refine mul_le_mul (Real.rpow_le_rpow (by linarith) (by linarith) (by norm_num)) ?_
            (by positivity) (by positivity)
          nlinarith [min_le_left x 1, min_le_right x 1,
            min_mul_one_add_le (x := x) (by linarith : (0:ℝ) ≤ t)]
  have : Ioi (0 : ℝ) = Ioc 0 1 ∪ Ioi 1 := by
    ext t
    simp only [mem_Ioi, mem_union, mem_Ioc]
    constructor
    · intro h
      rcases le_or_gt t 1 with h1 | h1
      · exact Or.inl ⟨h, h1⟩
      · exact Or.inr h1
    · rintro (⟨h, -⟩ | h)
      · exact h
      · linarith
  rw [this]
  exact h1.union h2

/-! ### 2.6.2 -/

/-- The binomial series `(1 + y)^a = ∑ binom(a, s) y^s` for `|y| < 1`. -/
theorem hasSum_one_add_rpow {a y : ℝ} (hy : |y| < 1) :
    HasSum (fun s : ℕ => Ring.choose a s * y ^ s) ((1 + y) ^ a) := by
  have h := Real.one_add_rpow_hasFPowerSeriesOnBall_zero (a := a)
  have hy' : y ∈ Metric.eball (0 : ℝ) 1 := by
    rw [Metric.mem_eball, edist_zero_right, ← ofReal_norm]
    exact ENNReal.ofReal_lt_one.mpr (by simpa using hy)
  have := h.hasSum hy'
  simp only [zero_add] at this
  refine this.congr_fun fun s => ?_
  simp only [binomialSeries_apply, List.prod_ofFn, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul]

/-- **DLMF 2.6.2**: for `t > 1`, `(1 + t)^{−1/3} = ∑_{s≥0} binom(−1/3, s) t^{−s−1/3}`. -/
theorem dlmf_2_6_2 {t : ℝ} (ht : 1 < t) :
    HasSum (fun s : ℕ => Ring.choose (-1 / 3 : ℝ) s * t ^ (-(s : ℝ) - 1 / 3))
      ((1 + t) ^ (-1 / 3 : ℝ)) := by
  have ht0 : 0 < t := by linarith
  have hy : |t⁻¹| < 1 := by
    rw [abs_of_pos (inv_pos.mpr ht0)]
    exact inv_lt_one_of_one_lt₀ ht
  have h := (hasSum_one_add_rpow (a := -1 / 3) hy).mul_right (t ^ (-1 / 3 : ℝ))
  have e : (1 + t) ^ (-1 / 3 : ℝ) = (1 + t⁻¹) ^ (-1 / 3 : ℝ) * t ^ (-1 / 3 : ℝ) := by
    rw [← Real.mul_rpow (by positivity) ht0.le]
    congr 1
    field_simp
    ring
  rw [e]
  refine h.congr_fun fun s => ?_
  rw [mul_assoc, inv_pow, ← Real.rpow_natCast, ← Real.rpow_neg ht0.le, ← Real.rpow_add ht0]
  congr 2
  ring

/-! ### 2.6.3 -/

/-- **DLMF 2.6.3**: for `s ≥ 1` the integrals `∫₀^∞ t^{−s−1/3}/(x + t) dt` diverge (already on
`(0, 1]`, where the integrand grows like `t^{−4/3}` or faster). -/
theorem dlmf_2_6_3 {x : ℝ} (hx : 0 < x) {s : ℕ} (hs : 1 ≤ s) :
    ¬ IntegrableOn (fun t : ℝ => t ^ (-(s : ℝ) - 1 / 3) / (x + t)) (Ioi 0) := by
  intro hint
  have hint' : IntervalIntegrable (fun t : ℝ => t ^ (-(s : ℝ) - 1 / 3) / (x + t)) volume 0 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
    exact hint.mono_set Ioc_subset_Ioi_self
  -- the test function `f(t) = t^{−1/3}` blows up at `0` and `f' = O(g)` on `(0, 1]`
  have hsub : [[(0 : ℝ), 1]] \ {0} ⊆ Ioc 0 1 := fun t ht => by
    rw [uIcc_of_le zero_le_one] at ht
    exact ⟨lt_of_le_of_ne ht.1.1 (Ne.symm ht.2), ht.1.2⟩
  have hmem : [[(0 : ℝ), 1]] \ {0} ∈ 𝓝[[[(0 : ℝ), 1]] \ {0}] 0 := self_mem_nhdsWithin
  refine not_intervalIntegrable_of_tendsto_norm_atTop_of_deriv_isBigO_within_sdiff_singleton
    (f := fun t : ℝ => t ^ (-(1 / 3 : ℝ))) (c := 0) zero_ne_one (by simp) ?_ ?_ ?_ hint'
  · filter_upwards [hmem] with t ht
    exact (Real.hasDerivAt_rpow_const (Or.inl (hsub ht).1.ne')).differentiableAt
  · have h1 : Tendsto (fun t : ℝ => t ^ (-(1 / 3 : ℝ))) (𝓝[>] 0) atTop := by
      have := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 3)).comp tendsto_inv_nhdsGT_zero
      refine this.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with t ht
      simp only [Function.comp]
      rw [Real.inv_rpow (le_of_lt ht), ← Real.rpow_neg (le_of_lt ht)]
    refine (h1.mono_left (nhdsWithin_mono _ fun t ht => (hsub ht).1)).congr' ?_
    filter_upwards [hmem] with t ht
    rw [Real.norm_of_nonneg (Real.rpow_nonneg (hsub ht).1.le _)]
  · refine IsBigO.of_bound ((x + 1) / 3) ?_
    filter_upwards [hmem] with t ht
    obtain ⟨ht0, ht1⟩ := hsub ht
    rw [(Real.hasDerivAt_rpow_const (Or.inl ht0.ne')).deriv]
    have hs' : (1 : ℝ) ≤ s := by exact_mod_cast hs
    have hpow : t ^ (-(1 / 3 : ℝ) - 1) ≤ t ^ (-(s : ℝ) - 1 / 3) :=
      Real.rpow_le_rpow_of_exponent_ge ht0 ht1 (by linarith)
    have hg : 0 ≤ t ^ (-(s : ℝ) - 1 / 3) / (x + t) := by positivity
    rw [Real.norm_of_nonneg hg, norm_mul, Real.norm_of_nonneg (Real.rpow_nonneg ht0.le _),
      norm_neg, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 3)]
    calc 1 / 3 * t ^ (-(1 / 3 : ℝ) - 1) ≤ 1 / 3 * t ^ (-(s : ℝ) - 1 / 3) :=
          mul_le_mul_of_nonneg_left hpow (by norm_num)
      _ = (x + 1) / 3 * (t ^ (-(s : ℝ) - 1 / 3) / (x + 1)) := by
          field_simp
      _ ≤ (x + 1) / 3 * (t ^ (-(s : ℝ) - 1 / 3) / (x + t)) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact div_le_div_of_nonneg_left (Real.rpow_nonneg ht0.le _) (by positivity) (by linarith)

/-! ### 2.6.4 -/

/-- The substitution `u = v/(1 − v)` maps `(0, 1)` onto `(0, ∞)`. -/
theorem image_div_one_sub_Ioo : (fun v : ℝ => v / (1 - v)) '' Ioo 0 1 = Ioi 0 := by
  ext u
  constructor
  · rintro ⟨v, ⟨hv0, hv1⟩, rfl⟩
    exact div_pos hv0 (by linarith)
  · intro hu
    have hu : (0 : ℝ) < u := hu
    refine ⟨u / (1 + u), ⟨by positivity, (div_lt_one (by linarith)).mpr (by linarith)⟩, ?_⟩
    have h1 : (1 : ℝ) + u ≠ 0 := by linarith
    field_simp
    ring

theorem injOn_div_one_sub : InjOn (fun v : ℝ => v / (1 - v)) (Ioo 0 1) := by
  intro v hv w hw h
  have hv1 : (1 : ℝ) - v ≠ 0 := by linarith [hv.2]
  have hw1 : (1 : ℝ) - w ≠ 0 := by linarith [hw.2]
  rw [div_eq_div_iff hv1 hw1] at h
  linarith

theorem hasDerivAt_div_one_sub {v : ℝ} (hv : v ≠ 1) :
    HasDerivAt (fun v : ℝ => v / (1 - v)) (1 / (1 - v) ^ 2) v := by
  have hd : HasDerivAt (fun v : ℝ => 1 - v) (0 - 1) v :=
    (hasDerivAt_const v (1 : ℝ)).sub (hasDerivAt_id' v)
  have h := HasDerivAt.div (c := fun v : ℝ => v) (d := fun v : ℝ => 1 - v) (hasDerivAt_id' v) hd
    (sub_ne_zero.mpr hv.symm)
  refine h.congr_deriv ?_
  ring

/-- `∫₀^∞ u^{α−1} (1 + u)^{−(α+β)} du = Γ(α)Γ(β)/Γ(α+β)`, `ℜα, ℜβ > 0`: the beta integral after
`u = v/(1 − v)`. -/
theorem integral_cpow_mul_one_add_cpow {α β : ℂ} (hα : 0 < α.re) (hβ : 0 < β.re) :
    (∫ u in Ioi (0 : ℝ), (u : ℂ) ^ (α - 1) * ((1 + u : ℝ) : ℂ) ^ (-(α + β))) =
      Gamma α * Gamma β / Gamma (α + β) := by
  rw [← betaIntegral_eq_Gamma_mul_div α β hα hβ, betaIntegral,
    intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo,
    ← image_div_one_sub_Ioo, integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo
      (f' := fun v => 1 / (1 - v) ^ 2)
      (fun v hv => (hasDerivAt_div_one_sub (by linarith [hv.2] : v ≠ 1)).hasDerivWithinAt)
      injOn_div_one_sub]
  refine setIntegral_congr_fun measurableSet_Ioo fun v hv => ?_
  obtain ⟨hv0, hv1⟩ := hv
  have hw0 : (0 : ℝ) < 1 - v := by linarith
  have hwc : ((1 - v : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr hw0.ne'
  have hvc : (v : ℂ) ≠ 0 := ofReal_ne_zero.mpr hv0.ne'
  have harg : arg ((1 - v : ℝ) : ℂ) ≠ π := by
    rw [arg_ofReal_of_nonneg hw0.le]
    exact Real.pi_pos.ne
  -- `u = v (1 − v)⁻¹`, `1 + u = (1 − v)⁻¹`
  have hu : (v / (1 - v) : ℝ) = v * (1 - v)⁻¹ := div_eq_mul_inv _ _
  have h1u : (1 + v * (1 - v)⁻¹ : ℝ) = (1 - v)⁻¹ := by
    field_simp
    ring
  rw [show (1 : ℂ) - (v : ℂ) = ((1 - v : ℝ) : ℂ) by push_cast; ring]
  simp only [hu, h1u, abs_of_pos (by positivity : (0 : ℝ) < 1 / (1 - v) ^ 2), real_smul]
  rw [ofReal_mul, mul_cpow_ofReal_nonneg hv0.le (inv_pos.mpr hw0).le, ofReal_inv,
    inv_cpow _ _ harg, inv_cpow _ _ harg, cpow_neg, inv_inv, cpow_sub _ _ hwc, cpow_sub _ _ hwc,
    cpow_add _ _ hwc, cpow_one, ofReal_div, ofReal_one, ofReal_pow]
  have hα0 : ((1 - v : ℝ) : ℂ) ^ α ≠ 0 := fun h => hwc ((cpow_eq_zero_iff _ _).mp h).1
  have hβ0 : ((1 - v : ℝ) : ℂ) ^ β ≠ 0 := fun h => hwc ((cpow_eq_zero_iff _ _).mp h).1
  field_simp

/-- **DLMF 2.6.4**: for `ℜα > 0`, `ℜβ > 0` and `x > 0`,
`∫₀^∞ t^{α−1}/(x + t)^{α+β} dt = Γ(α)Γ(β)/Γ(α+β) · x^{−β}`. -/
theorem dlmf_2_6_4 {α β : ℂ} (hα : 0 < α.re) (hβ : 0 < β.re) {x : ℝ} (hx : 0 < x) :
    (∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (α - 1) / ((x + t : ℝ) : ℂ) ^ (α + β)) =
      Gamma α * Gamma β / Gamma (α + β) * (x : ℂ) ^ (-β) := by
  -- `t = x u`
  have hsub := integral_comp_mul_left_Ioi
    (fun t : ℝ => (t : ℂ) ^ (α - 1) / ((x + t : ℝ) : ℂ) ^ (α + β)) 0 hx
  rw [mul_zero, real_smul, ofReal_inv] at hsub
  have hx0 : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hx.ne'
  have e : (∫ u in Ioi (0 : ℝ), (fun t : ℝ => (t : ℂ) ^ (α - 1) / ((x + t : ℝ) : ℂ) ^ (α + β))
      (x * u)) = (x : ℂ) ^ (-β - 1) *
        ∫ u in Ioi (0 : ℝ), (u : ℂ) ^ (α - 1) * ((1 + u : ℝ) : ℂ) ^ (-(α + β)) := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun u hu => ?_
    have hu : (0 : ℝ) < u := hu
    have hxu : (x + x * u : ℝ) = x * (1 + u) := by ring
    simp only [hxu]
    rw [ofReal_mul, ofReal_mul, mul_cpow_ofReal_nonneg hx.le hu.le,
      mul_cpow_ofReal_nonneg hx.le (by linarith), cpow_sub _ _ hx0, cpow_sub _ _ hx0, cpow_one,
      cpow_neg, cpow_neg, cpow_add _ _ hx0]
    have h1 : (x : ℂ) ^ α ≠ 0 := fun h => hx0 ((cpow_eq_zero_iff _ _).mp h).1
    have h2 : (x : ℂ) ^ β ≠ 0 := fun h => hx0 ((cpow_eq_zero_iff _ _).mp h).1
    have h3 : ((1 + u : ℝ) : ℂ) ^ (α + β) ≠ 0 := fun h =>
      (ofReal_ne_zero.mpr (by linarith : (1 + u : ℝ) ≠ 0)) ((cpow_eq_zero_iff _ _).mp h).1
    field_simp
  have hI : (∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (α - 1) / ((x + t : ℝ) : ℂ) ^ (α + β)) =
      (x : ℂ) * ∫ u in Ioi (0 : ℝ), (fun t : ℝ => (t : ℂ) ^ (α - 1) / ((x + t : ℝ) : ℂ) ^ (α + β))
        (x * u) := by
    rw [hsub, ← mul_assoc, mul_inv_cancel₀ hx0, one_mul]
  rw [hI, e, integral_cpow_mul_one_add_cpow hα hβ, cpow_sub _ _ hx0, cpow_one]
  field_simp

/-! ### 2.6.5 -/

/-- The generalized value of `∫₀^∞ t^{α−1}/(x + t)^{α+β} dt`: the right side of 2.6.4, defined
for all `α, β` (DLMF: other than non-positive integers, where the right side is `0` in Lean). -/
noncomputable def genBetaIntegral (α β : ℂ) (x : ℝ) : ℂ :=
  Gamma α * Gamma β / Gamma (α + β) * (x : ℂ) ^ (-β)

/-- The generalized value agrees with the integral when it converges (2.6.4). -/
theorem genBetaIntegral_eq {α β : ℂ} (hα : 0 < α.re) (hβ : 0 < β.re) {x : ℝ} (hx : 0 < x) :
    genBetaIntegral α β x = ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (α - 1) / ((x + t : ℝ) : ℂ) ^ (α + β) :=
  (dlmf_2_6_4 hα hβ hx).symm

/-- `Γ(2/3 − s) Γ(1/3 + s) = (−1)^s · 2π/√3`. -/
theorem Gamma_two_thirds_sub_mul (s : ℕ) :
    Gamma (2 / 3 - s) * Gamma (1 / 3 + s) = (-1) ^ s * (2 * π / Real.sqrt 3) := by
  have := Gamma_mul_Gamma_one_sub ((1 / 3 : ℂ) + s)
  rw [show (1 : ℂ) - (1 / 3 + s) = 2 / 3 - s by ring, mul_comm] at this
  rw [this, show (π : ℂ) * (1 / 3 + s) = ((π / 3 + s * π : ℝ) : ℂ) by push_cast; ring,
    ← ofReal_sin, Real.sin_add_nat_mul_pi, Real.sin_pi_div_three]
  have h3 : ((Real.sqrt 3 : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr (by positivity)
  have hc : ((-1 : ℂ) ^ s) ≠ 0 := pow_ne_zero _ (by norm_num)
  push_cast
  rw [show (π : ℂ) / ((-1) ^ s * (Real.sqrt 3 / 2)) = ((-1 : ℂ) ^ s)⁻¹ * (2 * π / Real.sqrt 3) by
    field_simp, ← inv_pow, inv_neg, inv_one]

/-- **DLMF 2.6.5**: with the generalized interpretation (`α = 2/3 − s`, `β = s + 1/3`),
`∫₀^∞ t^{−s−1/3}/(x + t) dt = (2π/√3) (−1)^s x^{−s−1/3}`, `s = 0, 1, 2, …`. -/
theorem dlmf_2_6_5 (s : ℕ) (x : ℝ) :
    genBetaIntegral (2 / 3 - s) (s + 1 / 3) x =
      2 * π / Real.sqrt 3 * ((-1) ^ s * (x : ℂ) ^ (-((s : ℂ) + 1 / 3))) := by
  rw [genBetaIntegral, show (2 / 3 - (s : ℂ)) + (s + 1 / 3) = 1 by ring, Gamma_one, div_one,
    show (s : ℂ) + 1 / 3 = 1 / 3 + s by ring, Gamma_two_thirds_sub_mul]
  ring

/-- **DLMF 2.6.5** for `s = 0`, where the integral converges:
`∫₀^∞ t^{−1/3}/(x + t) dt = (2π/√3) x^{−1/3}`. -/
theorem dlmf_2_6_5_zero {x : ℝ} (hx : 0 < x) :
    (∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (-(1 / 3 : ℂ)) / ((x + t : ℝ) : ℂ)) =
      2 * π / Real.sqrt 3 * (x : ℂ) ^ (-(1 / 3 : ℂ)) := by
  have h := dlmf_2_6_4 (α := 2 / 3) (β := 1 / 3) (by norm_num) (by norm_num) hx
  rw [show (2 / 3 : ℂ) + 1 / 3 = 1 by norm_num, Gamma_one, div_one] at h
  have h' := Gamma_two_thirds_sub_mul 0
  simp only [Nat.cast_zero, sub_zero, add_zero, pow_zero, one_mul] at h'
  rw [← h', ← h]
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  rw [show (2 / 3 : ℂ) - 1 = -(1 / 3) by norm_num, cpow_one]

/-! ### 2.6.6 -/

/-- **DLMF 2.6.6**, the formal term-by-term result: inserting 2.6.2 into 2.6.1 and replacing each
divergent integral 2.6.3 by its generalized value 2.6.5 gives the series
`(2π/√3) ∑ (−1)^s binom(−1/3, s) x^{−s−1/3}`. This is a definitional identity on the partial
sums; the resulting expansion is **incorrect** (see 2.6.7 in §2.6(ii)). -/
theorem dlmf_2_6_6_formal (x : ℝ) (N : ℕ) :
    ∑ s ∈ Finset.range N, ((Ring.choose (-1 / 3 : ℝ) s : ℝ) : ℂ) *
        genBetaIntegral (2 / 3 - s) (s + 1 / 3) x =
      2 * π / Real.sqrt 3 * ∑ s ∈ Finset.range N,
        (-1) ^ s * ((Ring.choose (-1 / 3 : ℝ) s : ℝ) : ℂ) * (x : ℂ) ^ (-((s : ℂ) + 1 / 3)) := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [dlmf_2_6_5]
  ring

end Azurite.DLMF
