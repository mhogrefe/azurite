/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/


import Azurite.DLMF.Chapter2.Section1
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# DLMF §2.1(ii): Ritt's theorem

* `sectorDLMF θ ω` (`|ph(z e^{−iθ})| < ω`), `closedSectorDLMF`; `closedBall_subset_sectorDLMF`:
  a closed sector properly interior to `sectorDLMF θ ω` (`|θ′ − θ| + ω′ < ω`) has discs of
  radius `κ|z|` inside it.
* `ritt_bound`: the Cauchy estimate `|f′| ≤ (C 2^{|ν|}/κ)|z|^{ν−1}` from `|f| ≤ C|z|^ν`.
* `dlmf_2_1_ii_ritt` (`O`) and `dlmf_2_1_ii_ritt_littleO` (`o`): Ritt's theorem.
-/

open Set Filter Topology Asymptotics Metric Complex

namespace Azurite.DLMF

/-! ### Sectors -/

/-- The open sector `|ph(z e^{−iθ})| < ω` with vertex `0`, bisector `θ` and half-opening `ω`. -/
def sectorDLMF (θ ω : ℝ) : Set ℂ := {z | z ≠ 0 ∧ |arg (z * exp (-(θ * I)))| < ω}

/-- The closed sector `|ph(z e^{−iθ})| ≤ ω`, `z ≠ 0`. -/
def closedSectorDLMF (θ ω : ℝ) : Set ℂ := {z | z ≠ 0 ∧ |arg (z * exp (-(θ * I)))| ≤ ω}

/-- Points close to `1` have small argument: `|sin(ph u)| ≤ |u − 1|`. -/
theorem abs_sin_arg_le_norm_sub_one (u : ℂ) : |Real.sin (arg u)| ≤ ‖u - 1‖ := by
  have hre := norm_mul_cos_arg u
  have him := norm_mul_sin_arg u
  have hsq : ‖u - 1‖ ^ 2 = (‖u‖ - Real.cos (arg u)) ^ 2 + Real.sin (arg u) ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    simp only [sub_re, one_re, sub_im, one_im, sub_zero]
    rw [← hre, ← him]
    linear_combination (‖u‖ ^ 2 - 1) * Real.sin_sq_add_cos_sq (arg u)
  rw [← Real.sqrt_sq (abs_nonneg _), ← Real.sqrt_sq (norm_nonneg (u - 1)), sq_abs]
  exact Real.sqrt_le_sqrt (by rw [hsq]; nlinarith [sq_nonneg (‖u‖ - Real.cos (arg u))])

theorem abs_arg_lt_of_norm_sub_one_lt {u : ℂ} {γ : ℝ} (hγ : 0 < γ) (hγ' : γ ≤ Real.pi / 2)
    (hu : ‖u - 1‖ < Real.sin γ) : |arg u| < γ := by
  have hs1 : Real.sin γ ≤ 1 := Real.sin_le_one γ
  have hre : 0 < u.re := by
    have := Complex.abs_re_le_norm (u - 1)
    simp only [sub_re, one_re] at this
    have := abs_le.mp (this.trans hu.le)
    by_contra h; push Not at h
    have h3 : ‖u - 1‖ ≥ 1 := by
      have := Complex.abs_re_le_norm (u - 1)
      simp only [sub_re, one_re] at this
      rw [abs_of_nonpos (by linarith)] at this; linarith
    linarith
  have hpi : |arg u| ≤ Real.pi / 2 := abs_arg_le_pi_div_two_iff.mpr hre.le
  by_contra h; push Not at h
  have h1 : Real.sin γ ≤ Real.sin |arg u| :=
    Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith) hpi h
  have h2 : Real.sin |arg u| = |Real.sin (arg u)| := by
    rcases le_or_gt 0 (arg u) with h0 | h0
    · rw [abs_of_nonneg h0, abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi h0
        (Complex.arg_le_pi u))]
    · have := Real.sin_nonneg_of_nonneg_of_le_pi (x := -arg u) (by linarith)
        (by linarith [Complex.neg_pi_lt_arg u])
      rw [Real.sin_neg] at this
      rw [abs_of_neg h0, Real.sin_neg, abs_of_nonpos (by linarith)]
  linarith [abs_sin_arg_le_norm_sub_one u]

theorem arg_exp_mul_I_of_mem {t : ℝ} (ht : t ∈ Ioc (-Real.pi) Real.pi) :
    arg (exp (t * I)) = t := by
  rw [arg_exp_mul_I, toIocMod_eq_self]
  convert ht using 2; ring

/-- The opening constant of a closed sector properly interior to `sectorDLMF θ ω`. -/
noncomputable def ritt_κ (θ ω θ' ω' : ℝ) : ℝ :=
  Real.sin (min (ω - (|θ' - θ| + ω')) (Real.pi / 2)) / 2

theorem ritt_κ_pos {θ ω θ' ω' : ℝ} (hsub : |θ' - θ| + ω' < ω) : 0 < ritt_κ θ ω θ' ω' := by
  unfold ritt_κ
  have h1 : 0 < min (ω - (|θ' - θ| + ω')) (Real.pi / 2) :=
    lt_min (by linarith) (by linarith [Real.pi_pos])
  have h2 : min (ω - (|θ' - θ| + ω')) (Real.pi / 2) < Real.pi :=
    (min_le_right _ _).trans_lt (by linarith [Real.pi_pos])
  exact half_pos (Real.sin_pos_of_pos_of_lt_pi h1 h2)

theorem ritt_κ_le {θ ω θ' ω' : ℝ} : ritt_κ θ ω θ' ω' ≤ 1 / 2 := by
  unfold ritt_κ; linarith [Real.sin_le_one (min (ω - (|θ' - θ| + ω')) (Real.pi / 2))]

/-- A closed sector properly interior to `sectorDLMF θ ω`: for `z` in it, the closed disc of
radius `κ|z|` about `z` lies in `sectorDLMF θ ω`. -/
theorem closedBall_subset_sectorDLMF {θ ω θ' ω' : ℝ} (hω : ω ≤ Real.pi)
    (hsub : |θ' - θ| + ω' < ω) {z : ℂ} (hz : z ∈ closedSectorDLMF θ' ω') :
    closedBall z (ritt_κ θ ω θ' ω' * ‖z‖) ⊆ sectorDLMF θ ω := by
  obtain ⟨hz0, hza⟩ := hz
  set γ := min (ω - (|θ' - θ| + ω')) (Real.pi / 2)
  have hγ : 0 < γ := lt_min (by linarith) (by linarith [Real.pi_pos])
  have hγ' : γ ≤ Real.pi / 2 := min_le_right _ _
  have hγω : γ ≤ ω - (|θ' - θ| + ω') := min_le_left _ _
  have hsγ : 0 < Real.sin γ :=
    Real.sin_pos_of_pos_of_lt_pi hγ (by linarith [Real.pi_pos])
  have hnz : 0 < ‖z‖ := norm_pos_iff.mpr hz0
  intro w hw
  rw [mem_closedBall, dist_eq_norm] at hw
  set u := w / z
  have hu : ‖u - 1‖ < Real.sin γ := by
    have : u - 1 = (w - z) / z := by simp only [u]; field_simp
    rw [this, norm_div, div_lt_iff₀ hnz]
    have : ritt_κ θ ω θ' ω' * ‖z‖ < Real.sin γ * ‖z‖ := by
      unfold ritt_κ; nlinarith
    linarith
  have hu0 : u ≠ 0 := by
    intro h; rw [h, zero_sub, norm_neg, norm_one] at hu
    linarith [Real.sin_le_one γ]
  have hw0 : w ≠ 0 := by
    intro h; apply hu0; simp [u, h]
  have harg := abs_arg_lt_of_norm_sub_one_lt hγ hγ' hu
  set A := z * exp (-(θ' * I))
  set B := exp (((θ' - θ : ℝ) : ℂ) * I)
  have hA0 : A ≠ 0 := mul_ne_zero hz0 (exp_ne_zero _)
  have hB0 : B ≠ 0 := exp_ne_zero _
  have hθ : |θ' - θ| < Real.pi := by linarith [abs_nonneg (θ' - θ), abs_nonneg (arg A)]
  have hargB : arg B = θ' - θ :=
    arg_exp_mul_I_of_mem ⟨by linarith [neg_abs_le (θ' - θ)], by linarith [le_abs_self (θ' - θ)]⟩
  have hAB : arg (A * B) = arg A + (θ' - θ) := by
    rw [arg_mul hA0 hB0 ⟨?_, ?_⟩, hargB] <;> rw [hargB] <;>
      linarith [abs_le.mp hza, abs_le.mp (le_refl |θ' - θ|), neg_abs_le (θ' - θ),
        le_abs_self (θ' - θ)]
  have hABu : arg (A * B * u) = arg A + (θ' - θ) + arg u := by
    rw [arg_mul (mul_ne_zero hA0 hB0) hu0 ⟨?_, ?_⟩, hAB] <;> rw [hAB] <;>
      linarith [abs_le.mp hza, neg_abs_le (θ' - θ), le_abs_self (θ' - θ), abs_lt.mp harg]
  have heq : w * exp (-(θ * I)) = A * B * u := by
    simp only [A, B, u]
    rw [mul_assoc z, mul_assoc z, ← exp_add]
    field_simp
    congr 1
    push_cast; ring
  refine ⟨hw0, ?_⟩
  rw [heq, hABu, abs_lt]
  constructor <;> linarith [abs_le.mp hza, neg_abs_le (θ' - θ), le_abs_self (θ' - θ),
    abs_lt.mp harg]

/-! ### The Cauchy estimate -/

theorem rpow_le_two_rpow_abs_mul {a b ν : ℝ} (ha : 0 < a) (hb : 0 < b) (h1 : b ≤ 2 * a)
    (h2 : a ≤ 2 * b) : b ^ ν ≤ 2 ^ |ν| * a ^ ν := by
  have hb' : b = b / a * a := by field_simp
  rw [hb', Real.mul_rpow (div_pos hb ha).le ha.le]
  gcongr
  rcases le_or_gt 0 ν with hν | hν
  · rw [abs_of_nonneg hν]
    exact Real.rpow_le_rpow (div_pos hb ha).le (by rw [div_le_iff₀ ha]; linarith) hν
  · have e : (b / a) ^ ν = (a / b) ^ (-ν) := by
      rw [Real.rpow_neg (div_pos ha hb).le, ← Real.inv_rpow (div_pos ha hb).le, inv_div]
    rw [abs_of_neg hν, e]
    exact Real.rpow_le_rpow (div_pos ha hb).le (by rw [div_le_iff₀ hb]; linarith) (by linarith)

theorem eventually_cobounded_inf_principal {S : Set ℂ} {P : ℂ → Prop} :
    (∀ᶠ z in Bornology.cobounded ℂ ⊓ 𝓟 S, P z) ↔ ∃ R, ∀ z ∈ S, R < ‖z‖ → P z := by
  rw [eventually_inf_principal, (hasBasis_cobounded_compl_closedBall (0 : ℂ)).eventually_iff]
  simp only [true_and, mem_compl_iff, mem_closedBall, dist_zero_right, not_le]
  exact ⟨fun ⟨R, h⟩ => ⟨R, fun z hz hR => h hR hz⟩, fun ⟨R, h⟩ => ⟨R, fun z hR hz => h z hz hR⟩⟩

/-- The estimate behind Ritt's theorem: `|f| ≤ C|z|^ν` on the sector gives
`|f′| ≤ (C 2^{|ν|}/κ) |z|^{ν−1}` on a properly interior closed sector. -/
theorem ritt_bound {θ ω θ' ω' : ℝ} (hω : ω ≤ Real.pi) (hsub : |θ' - θ| + ω' < ω)
    {f : ℂ → ℂ} {R : ℝ} (hf : DifferentiableOn ℂ f (sectorDLMF θ ω ∩ {z | R < ‖z‖}))
    {ν C R₁ : ℝ} (hb : ∀ z ∈ sectorDLMF θ ω, R₁ < ‖z‖ → ‖f z‖ ≤ C * ‖z‖ ^ ν) :
    ∀ z ∈ closedSectorDLMF θ' ω', 2 * max (max R R₁) 0 < ‖z‖ →
      ‖deriv f z‖ ≤ C * 2 ^ |ν| / ritt_κ θ ω θ' ω' * ‖z‖ ^ (ν - 1) := by
  intro z hz hzR
  set κ := ritt_κ θ ω θ' ω'
  have hκ := ritt_κ_pos hsub
  have hκ2 : κ ≤ 1 / 2 := ritt_κ_le
  have hm0 : 0 ≤ max (max R R₁) 0 := le_max_right _ _
  have hnz : 0 < ‖z‖ := by linarith
  have hball := closedBall_subset_sectorDLMF hω hsub hz
  have hρ : 0 < κ * ‖z‖ := mul_pos hκ hnz
  have hnorm : ∀ w ∈ closedBall z (κ * ‖z‖), ‖z‖ / 2 ≤ ‖w‖ ∧ ‖w‖ ≤ 2 * ‖z‖ := fun w hw => by
    rw [mem_closedBall, dist_eq_norm] at hw
    have h1 := norm_sub_norm_le z w
    have h2 := norm_sub_norm_le w z
    rw [norm_sub_rev] at h1
    constructor <;> nlinarith
  have hbig : ∀ w ∈ closedBall z (κ * ‖z‖), max (max R R₁) 0 < ‖w‖ := fun w hw => by
    linarith [(hnorm w hw).1]
  have hU : closedBall z (κ * ‖z‖) ⊆ sectorDLMF θ ω ∩ {w | R < ‖w‖} := fun w hw =>
    ⟨hball hw, lt_of_le_of_lt ((le_max_left _ _).trans (le_max_left _ _)) (hbig w hw)⟩
  have hC0 : 0 ≤ C := by
    have h := hb z (hball (mem_closedBall_self hρ.le))
      (lt_of_le_of_lt ((le_max_right _ _).trans (le_max_left _ _)) (by linarith))
    have := Real.rpow_pos_of_pos hnz ν
    nlinarith [norm_nonneg (f z)]
  have hsph : ∀ w ∈ sphere z (κ * ‖z‖), ‖f w‖ ≤ C * 2 ^ |ν| * ‖z‖ ^ ν := fun w hw => by
    have hw' := sphere_subset_closedBall hw
    have h := hb w (hball hw')
      (lt_of_le_of_lt ((le_max_right _ _).trans (le_max_left _ _)) (hbig w hw'))
    obtain ⟨h1, h2⟩ := hnorm w hw'
    have hw0 : 0 < ‖w‖ := by linarith
    have := rpow_le_two_rpow_abs_mul (ν := ν) hnz hw0 h2 (by linarith)
    calc ‖f w‖ ≤ C * ‖w‖ ^ ν := h
      _ ≤ C * (2 ^ |ν| * ‖z‖ ^ ν) := by gcongr
      _ = C * 2 ^ |ν| * ‖z‖ ^ ν := by ring
  have hcauchy := norm_deriv_le_of_forall_mem_sphere_norm_le hρ (hf.diffContOnCl_ball hU) hsph
  refine hcauchy.trans (le_of_eq ?_)
  rw [Real.rpow_sub_one hnz.ne']
  field_simp

/-! ### Ritt's theorem -/

theorem norm_cpow_real_sub_one (z : ℂ) (ν : ℝ) : ‖z ^ ((ν : ℂ) - 1)‖ = ‖z‖ ^ (ν - 1) := by
  rw [show (ν : ℂ) - 1 = ((ν - 1 : ℝ) : ℂ) by push_cast; ring, norm_cpow_real]

/-- **DLMF §2.1(ii), Ritt's theorem**: if `f` is analytic for all sufficiently large `|z|` in a
sector `𝐒` and `f(z) = O(z^ν)` as `z → ∞` in `𝐒` (`ν` real), then `f′(z) = O(z^{ν−1})` as
`z → ∞` in any closed sector properly interior to `𝐒` with the same vertex. -/
theorem dlmf_2_1_ii_ritt {θ ω θ' ω' : ℝ} (hω : ω ≤ Real.pi) (hsub : |θ' - θ| + ω' < ω)
    {f : ℂ → ℂ} (hf : ∃ R, DifferentiableOn ℂ f (sectorDLMF θ ω ∩ {z | R < ‖z‖})) {ν : ℝ}
    (hO : IsBigODLMF (Bornology.cobounded ℂ ⊓ 𝓟 (sectorDLMF θ ω)) f fun z => z ^ (ν : ℂ)) :
    IsBigODLMF (Bornology.cobounded ℂ ⊓ 𝓟 (closedSectorDLMF θ' ω')) (deriv f)
      fun z => z ^ ((ν : ℂ) - 1) := by
  obtain ⟨R, hR⟩ := hf
  obtain ⟨C, hC⟩ := hO
  obtain ⟨R₁, hR₁⟩ := eventually_cobounded_inf_principal.mp (eventually_map.mp hC)
  have hb : ∀ z ∈ sectorDLMF θ ω, R₁ < ‖z‖ → ‖f z‖ ≤ C * ‖z‖ ^ ν := fun z hz hzR => by
    have h := hR₁ z hz hzR
    have hp : 0 < ‖z‖ ^ ν := Real.rpow_pos_of_pos (norm_pos_iff.mpr hz.1) ν
    rwa [norm_div, norm_cpow_real, div_le_iff₀ hp] at h
  refine ⟨C * 2 ^ |ν| / ritt_κ θ ω θ' ω', eventually_map.mpr
    (eventually_cobounded_inf_principal.mpr ⟨2 * max (max R R₁) 0, fun z hz hzR => ?_⟩)⟩
  have h := ritt_bound hω hsub hR hb z hz hzR
  have hp : 0 < ‖z‖ ^ (ν - 1) := Real.rpow_pos_of_pos (norm_pos_iff.mpr hz.1) _
  show ‖deriv f z / z ^ ((ν : ℂ) - 1)‖ ≤ _
  rwa [norm_div, norm_cpow_real_sub_one, div_le_iff₀ hp]

/-- **DLMF §2.1(ii)**: Ritt's theorem also holds with both `O`'s replaced by `o`'s. -/
theorem dlmf_2_1_ii_ritt_littleO {θ ω θ' ω' : ℝ} (hω : ω ≤ Real.pi)
    (hsub : |θ' - θ| + ω' < ω) {f : ℂ → ℂ}
    (hf : ∃ R, DifferentiableOn ℂ f (sectorDLMF θ ω ∩ {z | R < ‖z‖})) {ν : ℝ}
    (ho : IsLittleODLMF (Bornology.cobounded ℂ ⊓ 𝓟 (sectorDLMF θ ω)) f fun z => z ^ (ν : ℂ)) :
    IsLittleODLMF (Bornology.cobounded ℂ ⊓ 𝓟 (closedSectorDLMF θ' ω')) (deriv f)
      fun z => z ^ ((ν : ℂ) - 1) := by
  obtain ⟨R, hR⟩ := hf
  have hκ := ritt_κ_pos hsub
  set K := 2 ^ |ν| / ritt_κ θ ω θ' ω'
  have hK : 0 < K := div_pos (Real.rpow_pos_of_pos two_pos _) hκ
  rw [IsLittleODLMF, tendsto_zero_iff_norm_tendsto_zero, Metric.tendsto_nhds]
  intro ε hε
  have ho' := (Metric.tendsto_nhds.mp
    (tendsto_zero_iff_norm_tendsto_zero.mp ho)) (ε / (2 * K)) (by positivity)
  simp only [Real.dist_eq, sub_zero, abs_norm] at ho' ⊢
  obtain ⟨R₁, hR₁⟩ := eventually_cobounded_inf_principal.mp ho'
  have hb : ∀ z ∈ sectorDLMF θ ω, R₁ < ‖z‖ → ‖f z‖ ≤ ε / (2 * K) * ‖z‖ ^ ν := fun z hz hzR => by
    have h := hR₁ z hz hzR
    have hp : 0 < ‖z‖ ^ ν := Real.rpow_pos_of_pos (norm_pos_iff.mpr hz.1) ν
    rw [norm_div, norm_cpow_real, div_lt_iff₀ hp] at h
    exact h.le
  refine eventually_cobounded_inf_principal.mpr ⟨2 * max (max R R₁) 0, fun z hz hzR => ?_⟩
  have h := ritt_bound hω hsub hR hb z hz hzR
  have hp : 0 < ‖z‖ ^ (ν - 1) := Real.rpow_pos_of_pos (norm_pos_iff.mpr hz.1) _
  rw [norm_div, norm_cpow_real_sub_one, div_lt_iff₀ hp]
  calc ‖deriv f z‖ ≤ ε / (2 * K) * 2 ^ |ν| / ritt_κ θ ω θ' ω' * ‖z‖ ^ (ν - 1) := h
    _ = ε / 2 * ‖z‖ ^ (ν - 1) := by simp only [K]; field_simp
    _ < ε * ‖z‖ ^ (ν - 1) := by nlinarith

end Azurite.DLMF
