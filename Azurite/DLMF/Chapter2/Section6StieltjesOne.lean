/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/


import Azurite.DLMF.Chapter2.Section6StieltjesExpansion

/-!
# DLMF §2.6(ii): the case `α = 1`, 2.6.28–2.6.29

* `integral_Ioc_inv_ofReal_add`: `∫₀¹ dτ/(τ + z) = ln(1 + z) − ln z`;
  `integral_Ioi_one_inv_mul_add`: `∫₁^∞ dτ/(τ(τ + z)) = ln(1 + z)/z`. Their combination
  `∫₁^∞ dτ/(τ(τ + z)) − (1/z) ∫₀¹ dτ/(τ + z) = (ln z)/z` is the source of the `ln z` in 2.6.28.
* 2.6.29 (`stieltjesDTilde`): the constants `d̃ₙ`. Since `fₙ = aₙ τ^{−n−1} + f_{n+1}` cannot be
  integrated term by term against `τⁿ` (both `∫₀¹ τ^{−1}` and `∫₁^∞ τⁿ fₙ` diverge), the natural
  finite expression is `d̃ₙ = ∫₀¹ τⁿ fₙ(τ) dτ + ∫₁^∞ τⁿ f_{n+1}(τ) dτ`, and that is the definition.
  `dlmf_2_6_29` identifies it with DLMF's limit `lim_{z→n+1} (𝓜f(z) + aₙ/(z − n − 1))`, under the
  additional hypothesis `f = O(t^c)`, `c > −1`, as `t → 0+`, which makes `𝓜f₁` analytic near
  `z = n + 1` (without it, the limit need not exist for `n = 0`: `𝓜f₁(z)` can diverge for every
  `ℜz < 1` when `f` is merely integrable near `0`; `docs/dlmf_errata.md`).
* 2.6.28 (`dlmf_2_6_28`): for `α = 1` and `|ph z| < π`,
  `𝓢f(z) = ln z ∑_{s<n} (−1)^s aₛ z^{−s−1} + ∑_{s<n} (−1)^s d̃ₛ z^{−s−1} + Rₙ(z)`, with `Rₙ` from
  2.6.30. As for 2.6.27 the proof is an induction on `n` (`stieltjesR_succ_one`), now splitting
  the integral at `τ = 1`.
-/

open MeasureTheory Filter Topology Set Complex Asymptotics
open scoped Real

namespace Azurite.DLMF

/-! ### Two logarithmic integrals -/

theorem ofReal_add_mem_slitPlane {z : ℂ} (hz : z ∈ slitPlane) {t : ℝ} (ht : 0 ≤ t) :
    (t : ℂ) + z ∈ slitPlane := by
  rw [mem_slitPlane_iff] at hz ⊢
  simp only [add_re, ofReal_re, add_im, ofReal_im, zero_add]
  rcases hz with h | h
  · exact Or.inl (by linarith)
  · exact Or.inr h

theorem one_add_mul_inv_mem_slitPlane {z : ℂ} (hz : z ∈ slitPlane) {t : ℝ} (ht : 0 < t) :
    1 + z * (t : ℂ)⁻¹ ∈ slitPlane := by
  rw [mem_slitPlane_iff] at hz ⊢
  rw [← ofReal_inv]
  simp only [add_re, one_re, mul_re, ofReal_re, ofReal_im, mul_zero, sub_zero, add_im, one_im,
    mul_im, zero_add]
  rcases hz with h | h
  · exact Or.inl (by positivity)
  · exact Or.inr (mul_ne_zero h (inv_ne_zero ht.ne'))

/-- `∫₀¹ dτ/(τ + z) = ln(1 + z) − ln z` for `|ph z| < π`. -/
theorem integral_Ioc_inv_ofReal_add {z : ℂ} (hz : z ∈ slitPlane) :
    (∫ τ in Ioc (0 : ℝ) 1, ((τ : ℂ) + z)⁻¹) = log (1 + z) - log z := by
  have hd : ∀ τ ∈ uIcc (0 : ℝ) 1,
      HasDerivAt (fun τ : ℝ => log ((τ : ℂ) + z)) ((τ : ℂ) + z)⁻¹ τ := by
    intro τ hτ
    rw [uIcc_of_le zero_le_one] at hτ
    have h1 : HasDerivAt (fun τ : ℝ => (τ : ℂ) + z) 1 τ := by
      have := ((hasDerivAt_id τ).ofReal_comp).add_const z
      simpa using this
    have := h1.clog_real (ofReal_add_mem_slitPlane hz hτ.1)
    rwa [one_div] at this
  have hint : IntervalIntegrable (fun τ : ℝ => ((τ : ℂ) + z)⁻¹) volume 0 1 := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le zero_le_one]
    exact (continuousOn_inv_ofReal_add hz).mono Icc_subset_Ici_self
  have := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hint
  rw [intervalIntegral.integral_of_le zero_le_one] at this
  rw [this]
  simp

/-- The integrand of `integral_Ioi_one_inv_mul_add` is integrable. -/
theorem integrableOn_Ioi_one_inv_mul_add {z : ℂ} (hz : z ∈ slitPlane) :
    IntegrableOn (fun τ : ℝ => ((τ : ℂ) * (τ + z))⁻¹) (Ioi 1) := by
  obtain ⟨c, hc, hb⟩ := exists_mul_one_add_le_norm_add hz
  have hloc : LocallyIntegrableOn (fun τ : ℝ => ((τ : ℂ) * (τ + z))⁻¹) (Ioi 0) :=
    (ContinuousOn.inv₀ (continuous_ofReal.continuousOn.mul
      (continuous_ofReal.continuousOn.add continuousOn_const)) fun t ht =>
        mul_ne_zero (ofReal_ne_zero.mpr (ne_of_gt ht))
          (ofReal_add_ne_zero hz (le_of_lt ht))).locallyIntegrableOn measurableSet_Ioi
  refine StieltjesSetup.integrableOn_Ioi_one_of_isBigO hloc (b := 2) ?_ one_lt_two
  refine IsBigO.of_bound (1 / c) ?_
  filter_upwards [eventually_ge_atTop 1] with t ht
  have ht0 : 0 < t := by linarith
  have hpos : 0 < ‖(t : ℂ) + z‖ := lt_of_lt_of_le (by positivity) (hb t ht0.le)
  rw [norm_inv, norm_mul, norm_real, Real.norm_of_nonneg ht0.le,
    Real.norm_of_nonneg (Real.rpow_nonneg ht0.le _), Real.rpow_neg ht0.le,
    show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rw [inv_le_iff_one_le_mul₀ (by positivity)]
  calc (1 : ℝ) = 1 / c * (t * (c * t)) / t ^ 2 := by field_simp
    _ ≤ 1 / c * (t * ‖(t : ℂ) + z‖) / t ^ 2 := by
      gcongr
      linarith [hb t ht0.le]
    _ = 1 / c * (t ^ 2)⁻¹ * (t * ‖(t : ℂ) + z‖) := by ring

/-- `∫₁^∞ dτ/(τ(τ + z)) = ln(1 + z)/z` for `|ph z| < π`. -/
theorem integral_Ioi_one_inv_mul_add {z : ℂ} (hz : z ∈ slitPlane) :
    (∫ τ in Ioi (1 : ℝ), ((τ : ℂ) * (τ + z))⁻¹) = log (1 + z) / z := by
  have hz0 : z ≠ 0 := slitPlane_ne_zero hz
  set F : ℝ → ℂ := fun τ => -log (1 + z * (τ : ℂ)⁻¹) with hF
  have hderiv : ∀ τ : ℝ, 0 < τ → HasDerivAt F (z * ((τ : ℂ) * (τ + z))⁻¹) τ := by
    intro τ hτ
    have hτ0 : (τ : ℂ) ≠ 0 := ofReal_ne_zero.mpr hτ.ne'
    have hτz : (τ : ℂ) + z ≠ 0 := ofReal_add_ne_zero hz hτ.le
    have h1 : HasDerivAt (fun τ : ℝ => (τ : ℂ)) 1 τ := by
      simpa using (hasDerivAt_id τ).ofReal_comp
    have h2 := (((h1.inv hτ0).const_mul z).const_add 1).clog_real
      (one_add_mul_inv_mem_slitPlane hz hτ)
    refine (h2.neg).congr_deriv ?_
    have hne : (1 : ℂ) + z * (τ : ℂ)⁻¹ ≠ 0 :=
      slitPlane_ne_zero (one_add_mul_inv_mem_slitPlane hz hτ)
    simp only [Pi.inv_apply]
    field_simp
  have hcont : ContinuousWithinAt F (Ici 1) 1 :=
    (hderiv 1 one_pos).continuousAt.continuousWithinAt
  have hint : IntegrableOn (fun τ : ℝ => z * ((τ : ℂ) * (τ + z))⁻¹) (Ioi 1) :=
    (integrableOn_Ioi_one_inv_mul_add hz).const_mul z
  have hlim : Tendsto F atTop (𝓝 0) := by
    have h1 : Tendsto (fun τ : ℝ => (τ : ℂ)⁻¹) atTop (𝓝 0) := by
      have := (continuous_ofReal.tendsto 0).comp tendsto_inv_atTop_zero
      simpa [Function.comp_def] using this
    have h2 : Tendsto (fun τ : ℝ => 1 + z * (τ : ℂ)⁻¹) atTop (𝓝 (1 + z * 0)) :=
      tendsto_const_nhds.add (tendsto_const_nhds.mul h1)
    rw [mul_zero, add_zero] at h2
    have := ((continuousAt_clog one_mem_slitPlane).tendsto.comp h2).neg
    simpa [Function.comp_def, hF] using this
  have h := integral_Ioi_of_hasDerivAt_of_tendsto hcont (fun τ hτ => hderiv τ (lt_trans one_pos hτ))
    hint hlim
  rw [integral_const_mul] at h
  rw [eq_div_iff hz0, mul_comm, h, hF]
  simp

/-! ### 2.6.29: the constants `d̃ₙ` -/

/-- **DLMF 2.6.29**, the finite part: `d̃ₙ = ∫₀¹ τⁿ fₙ(τ) dτ + ∫₁^∞ τⁿ f_{n+1}(τ) dτ`
(`= lim_{z→n+1} (𝓜f(z) + aₙ/(z − n − 1))`, `dlmf_2_6_29`). -/
noncomputable def stieltjesDTilde (f : ℝ → ℂ) (a : ℕ → ℂ) (α : ℝ) (n : ℕ) : ℂ :=
  (∫ τ in Ioc (0 : ℝ) 1, (τ : ℂ) ^ n * stieltjesRem f a α n τ) +
    ∫ τ in Ioi (1 : ℝ), (τ : ℂ) ^ n * stieltjesRem f a α (n + 1) τ

namespace StieltjesSetup

variable {f : ℝ → ℂ} {a : ℕ → ℂ} {α : ℝ} (hS : StieltjesSetup f a α)
include hS

/-- `τⁿ fₘ(τ) = O(τ^{n−m−α})` as `τ → ∞`. -/
theorem isBigO_pow_mul_rem (n m : ℕ) :
    (fun τ : ℝ => (τ : ℂ) ^ n * stieltjesRem f a α m τ) =O[atTop]
      fun τ => τ ^ ((n : ℝ) - (m + α)) := by
  have h1 : (fun τ : ℝ => (τ : ℂ) ^ n) =O[atTop] fun τ => τ ^ (n : ℝ) := by
    refine IsBigO.of_bound 1 ?_
    filter_upwards [eventually_gt_atTop 0] with τ hτ
    rw [norm_pow, norm_real, Real.norm_of_nonneg hτ.le,
      Real.norm_of_nonneg (Real.rpow_nonneg hτ.le _), Real.rpow_natCast, one_mul]
  refine (h1.mul (hS.rem_isBigO m)).congr' EventuallyEq.rfl ?_
  filter_upwards [eventually_gt_atTop 0] with τ hτ
  rw [← Real.rpow_add hτ, sub_eq_add_neg]

theorem locallyIntegrableOn_pow_mul_rem (n m : ℕ) :
    LocallyIntegrableOn (fun τ : ℝ => (τ : ℂ) ^ n * stieltjesRem f a α m τ) (Ioi 0) :=
  (hS.locallyIntegrableOn_rem m).continuousOn_mul (continuous_ofReal.continuousOn.pow n)
    isOpen_Ioi.isLocallyClosed

/-- `τⁿ f_{n+1}(τ)` is integrable on `(1, ∞)`. -/
theorem integrableOn_Ioi_one_pow_mul_rem_succ (n : ℕ) :
    IntegrableOn (fun τ : ℝ => (τ : ℂ) ^ n * stieltjesRem f a α (n + 1) τ) (Ioi 1) := by
  refine integrableOn_Ioi_one_of_isBigO (hS.locallyIntegrableOn_pow_mul_rem n (n + 1))
    (b := 1 + α) ?_ (by linarith [hS.α_pos])
  refine (hS.isBigO_pow_mul_rem n (n + 1)).congr' EventuallyEq.rfl
    (Eventually.of_forall fun τ => ?_)
  rw [show (n : ℝ) - (((n + 1 : ℕ) : ℝ) + α) = -(1 + α) by push_cast; ring]

/-- **One step of 2.6.28**, `α = 1`:
`Rₙ(z) = (−1)ⁿ aₙ (ln z)/z^{n+1} + (−1)ⁿ d̃ₙ/z^{n+1} + R_{n+1}(z)`. -/
theorem stieltjesR_succ_one (hα : α = 1) {z : ℂ} (hz : z ∈ slitPlane) (n : ℕ) :
    stieltjesR f a α n z =
      (-1) ^ n * a n * log z / z ^ (n + 1) + (-1) ^ n * stieltjesDTilde f a α n / z ^ (n + 1) +
        stieltjesR f a α (n + 1) z := by
  subst hα
  have hz0 : z ≠ 0 := slitPlane_ne_zero hz
  -- integrability of all the pieces
  have hIn := hS.integrableOn_pow_mul_rem_div hz n
  have hIn1 := hS.integrableOn_pow_mul_rem_div hz (n + 1)
  have hP₁ := hIn.mono_set (Ioc_subset_Ioi_self : Ioc (0 : ℝ) 1 ⊆ Ioi 0)
  have hP₂ := hIn.mono_set (Ioi_subset_Ioi zero_le_one)
  have hC₁ := hIn1.mono_set (Ioc_subset_Ioi_self : Ioc (0 : ℝ) 1 ⊆ Ioi 0)
  have hB₂ := hIn1.mono_set (Ioi_subset_Ioi zero_le_one)
  have hL₂ := integrableOn_Ioi_one_inv_mul_add hz
  have hL₁ : IntegrableOn (fun τ : ℝ => ((τ : ℂ) + z)⁻¹) (Ioc 0 1) :=
    (((continuousOn_inv_ofReal_add hz).mono Icc_subset_Ici_self).integrableOn_compact
      isCompact_Icc).mono_set Ioc_subset_Icc_self
  have hA₁ := hS.integrableOn_Ioc_pow_mul_rem n n (by linarith)
  have hA₂ := hS.integrableOn_Ioi_one_pow_mul_rem_succ n
  have hB₁' := hS.integrableOn_Ioc_pow_mul_rem (n + 1) n (by push_cast; linarith)
  have hB₁ : IntegrableOn (fun τ : ℝ => (τ : ℂ) ^ (n + 1) * stieltjesRem f a 1 n τ / (τ + z))
      (Ioc 0 1) := by
    refine IntegrableOn.congr_fun (integrableOn_Ioc_mul_of_continuousOn
      ((continuousOn_inv_ofReal_add hz).mono Icc_subset_Ici_self) hB₁') (fun τ _ => ?_)
      measurableSet_Ioc
    ring
  -- pointwise identities
  have hrem : ∀ τ : ℝ, 0 < τ → stieltjesRem f a 1 n τ =
      a n * ((τ : ℂ) ^ (n + 1))⁻¹ + stieltjesRem f a 1 (n + 1) τ := by
    intro τ hτ
    rw [rem_eq_add_succ, ofReal_one, ← cpow_natCast, ← cpow_neg]
    push_cast
    ring_nf
  have hQ₂ : IntegrableOn (fun τ : ℝ => (τ : ℂ) ^ n * stieltjesRem f a 1 (n + 1) τ / (τ + z))
      (Ioi 1) := by
    refine IntegrableOn.congr_fun (hP₂.sub (hL₂.const_mul (a n))) (fun τ hτ => ?_) measurableSet_Ioi
    have hτ0 : (τ : ℂ) ≠ 0 := ofReal_ne_zero.mpr (lt_trans one_pos hτ).ne'
    have hτz : (τ : ℂ) + z ≠ 0 := ofReal_add_ne_zero hz (lt_trans one_pos hτ).le
    simp only [Pi.sub_apply]
    rw [hrem τ (lt_trans one_pos hτ)]
    field_simp
    ring
  -- the splittings
  have e0 : (∫ τ in Ioi (0 : ℝ), (τ : ℂ) ^ n * stieltjesRem f a 1 n τ / (τ + z)) =
      (∫ τ in Ioc (0 : ℝ) 1, (τ : ℂ) ^ n * stieltjesRem f a 1 n τ / (τ + z)) +
        ∫ τ in Ioi (1 : ℝ), (τ : ℂ) ^ n * stieltjesRem f a 1 n τ / (τ + z) := by
    rw [← Ioc_union_Ioi_eq_Ioi zero_le_one]
    exact setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi hP₁ hP₂
  have e0' : (∫ τ in Ioi (0 : ℝ), (τ : ℂ) ^ (n + 1) * stieltjesRem f a 1 (n + 1) τ / (τ + z)) =
      (∫ τ in Ioc (0 : ℝ) 1, (τ : ℂ) ^ (n + 1) * stieltjesRem f a 1 (n + 1) τ / (τ + z)) +
        ∫ τ in Ioi (1 : ℝ), (τ : ℂ) ^ (n + 1) * stieltjesRem f a 1 (n + 1) τ / (τ + z) := by
    rw [← Ioc_union_Ioi_eq_Ioi zero_le_one]
    exact setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi hC₁ hB₂
  -- `P₂ = aₙ L₂ + Q₂`
  have e1 : (∫ τ in Ioi (1 : ℝ), (τ : ℂ) ^ n * stieltjesRem f a 1 n τ / (τ + z)) =
      a n * (∫ τ in Ioi (1 : ℝ), ((τ : ℂ) * (τ + z))⁻¹) +
        ∫ τ in Ioi (1 : ℝ), (τ : ℂ) ^ n * stieltjesRem f a 1 (n + 1) τ / (τ + z) := by
    rw [← integral_const_mul, ← integral_add (hL₂.const_mul _) hQ₂]
    refine setIntegral_congr_fun measurableSet_Ioi fun τ hτ => ?_
    have hτ0 : (τ : ℂ) ≠ 0 := ofReal_ne_zero.mpr (lt_trans one_pos hτ).ne'
    have hτz : (τ : ℂ) + z ≠ 0 := ofReal_add_ne_zero hz (lt_trans one_pos hτ).le
    rw [hrem τ (lt_trans one_pos hτ)]
    field_simp
    ring
  -- `P₁ = z⁻¹ A₁ − z⁻¹ B₁`
  have e2 : (∫ τ in Ioc (0 : ℝ) 1, (τ : ℂ) ^ n * stieltjesRem f a 1 n τ / (τ + z)) =
      z⁻¹ * (∫ τ in Ioc (0 : ℝ) 1, (τ : ℂ) ^ n * stieltjesRem f a 1 n τ) -
        z⁻¹ * ∫ τ in Ioc (0 : ℝ) 1, (τ : ℂ) ^ (n + 1) * stieltjesRem f a 1 n τ / (τ + z) := by
    rw [← integral_const_mul, ← integral_const_mul, ← integral_sub (hA₁.const_mul _)
      (hB₁.const_mul _)]
    refine setIntegral_congr_fun measurableSet_Ioc fun τ hτ => ?_
    have hτz : (τ : ℂ) + z ≠ 0 := ofReal_add_ne_zero hz hτ.1.le
    field_simp
    ring
  -- `Q₂ = z⁻¹ A₂ − z⁻¹ B₂`
  have e3 : (∫ τ in Ioi (1 : ℝ), (τ : ℂ) ^ n * stieltjesRem f a 1 (n + 1) τ / (τ + z)) =
      z⁻¹ * (∫ τ in Ioi (1 : ℝ), (τ : ℂ) ^ n * stieltjesRem f a 1 (n + 1) τ) -
        z⁻¹ * ∫ τ in Ioi (1 : ℝ), (τ : ℂ) ^ (n + 1) * stieltjesRem f a 1 (n + 1) τ / (τ + z) := by
    rw [← integral_const_mul, ← integral_const_mul, ← integral_sub (hA₂.const_mul _)
      (hB₂.const_mul _)]
    refine setIntegral_congr_fun measurableSet_Ioi fun τ hτ => ?_
    have hτz : (τ : ℂ) + z ≠ 0 := ofReal_add_ne_zero hz (lt_trans one_pos hτ).le
    field_simp
    ring
  -- `B₁ = aₙ L₁ + C₁`
  have e4 : (∫ τ in Ioc (0 : ℝ) 1, (τ : ℂ) ^ (n + 1) * stieltjesRem f a 1 n τ / (τ + z)) =
      a n * (∫ τ in Ioc (0 : ℝ) 1, ((τ : ℂ) + z)⁻¹) +
        ∫ τ in Ioc (0 : ℝ) 1, (τ : ℂ) ^ (n + 1) * stieltjesRem f a 1 (n + 1) τ / (τ + z) := by
    rw [← integral_const_mul, ← integral_add (hL₁.const_mul _) hC₁]
    refine setIntegral_congr_fun measurableSet_Ioc fun τ hτ => ?_
    have hτ0 : (τ : ℂ) ≠ 0 := ofReal_ne_zero.mpr hτ.1.ne'
    have hτz : (τ : ℂ) + z ≠ 0 := ofReal_add_ne_zero hz hτ.1.le
    rw [hrem τ hτ.1]
    field_simp
  simp only [stieltjesR, stieltjesDTilde]
  rw [e0, e0', e1, e2, e3, e4, integral_Ioc_inv_ofReal_add hz, integral_Ioi_one_inv_mul_add hz]
  have hzn1 : z ^ (n + 1) ≠ 0 := pow_ne_zero _ hz0
  have hzn : z ^ n ≠ 0 := pow_ne_zero _ hz0
  field_simp
  ring

/-- **DLMF 2.6.28** (with 2.6.30), `α = 1`, `|ph z| < π`: for every `n`,
`𝓢f(z) = ln z ∑_{s<n} (−1)^s aₛ z^{−s−1} + ∑_{s<n} (−1)^s d̃ₛ z^{−s−1} + Rₙ(z)`. -/
theorem dlmf_2_6_28 (hα : α = 1) {z : ℂ} (hz : z ∈ slitPlane) (n : ℕ) :
    stieltjesT f z =
      log z * ∑ s ∈ Finset.range n, (-1) ^ s * a s / z ^ (s + 1) +
        ∑ s ∈ Finset.range n, (-1) ^ s * stieltjesDTilde f a α s / z ^ (s + 1) +
        stieltjesR f a α n z := by
  induction n with
  | zero => simp [stieltjesR, stieltjesT, rem_zero]
  | succ n ih =>
    rw [ih, hS.stieltjesR_succ_one hα hz n, Finset.sum_range_succ, Finset.sum_range_succ]
    ring

/-! ### 2.6.29 as a limit -/

/-- **DLMF 2.6.29**: `d̃ₙ = lim_{z→n+1} (𝓜f(z) + aₙ/(z − n − 1))`, `α = 1`, for `f = O(t^c)` at `0+`
with `c > −1` (so that `𝓜f₁` is analytic at `n + 1`). -/
theorem dlmf_2_6_29 (hα : α = 1) {c : ℝ} (hc : -1 < c) (hf0 : f =O[𝓝[>] 0] (· ^ c)) (n : ℕ) :
    Tendsto (fun z : ℂ => mellinCont f a α z + a n / (z - ((n : ℂ) + 1))) (𝓝[≠] ((n : ℂ) + 1))
      (𝓝 (stieltjesDTilde f a α n)) := by
  subst hα
  -- the regular part
  set G : ℂ → ℂ := fun z => mellin (trunc₁ f) z -
    ∑ s ∈ Finset.range n, a s / (z - ((s : ℂ) + 1)) +
    mellin (trunc₂ (stieltjesRem f a 1 (n + 1))) z with hG
  have hGcont : ContinuousAt G ((n : ℂ) + 1) := by
    have h1 : DifferentiableAt ℂ (mellin (trunc₁ f)) ((n : ℂ) + 1) :=
      differentiableAt_mellin_trunc₁ hS.hloc hf0 (by simp; linarith)
    have h2 : DifferentiableAt ℂ (mellin (trunc₂ (stieltjesRem f a 1 (n + 1)))) ((n : ℂ) + 1) :=
      differentiableAt_mellin_trunc₂ (hS.locallyIntegrableOn_rem (n + 1)) (hS.rem_isBigO (n + 1))
        (by push_cast; simp)
    have h3 : DifferentiableAt ℂ (fun z : ℂ => ∑ s ∈ Finset.range n, a s / (z - ((s : ℂ) + 1)))
        ((n : ℂ) + 1) := by
      refine DifferentiableAt.fun_sum fun s hs => (differentiableAt_const _).div
        (differentiableAt_id.sub_const _) ?_
      intro h
      have := congrArg Complex.re h
      simp only [sub_re, add_re, natCast_re, one_re, zero_re] at this
      have : (s : ℝ) < n := Nat.cast_lt.mpr (Finset.mem_range.mp hs)
      linarith
    exact ((h1.sub h3).add h2).continuousAt
  have hGval : G ((n : ℂ) + 1) = stieltjesDTilde f a 1 n := by
    have hw : ∀ s < n, 0 < ((n : ℂ) + 1).re + (-((s : ℂ) + 1)).re := fun s hs => by
      have : (s : ℝ) < n := Nat.cast_lt.mpr hs
      simp only [add_re, natCast_re, one_re, neg_re]
      linarith
    obtain ⟨-, e₁⟩ := mellin_trunc₁_sub_sum (mellinConvergent_trunc₁_of_integrableOn hS.f_int₁
      (z := (n : ℂ) + 1) (by simp)) hw (c := a)
    have hrem : (fun t : ℝ => f t - ∑ s ∈ Finset.range n, a s * (t : ℂ) ^ (-((s : ℂ) + 1))) =
        stieltjesRem f a 1 n := by
      ext t
      simp [stieltjesRem]
    rw [hrem] at e₁
    have hsum : ∑ s ∈ Finset.range n, a s / ((n : ℂ) + 1 + -((s : ℂ) + 1)) =
        ∑ s ∈ Finset.range n, a s / ((n : ℂ) + 1 - ((s : ℂ) + 1)) :=
      Finset.sum_congr rfl fun s _ => by rw [← sub_eq_add_neg]
    rw [hG]
    simp only
    rw [← hsum, ← e₁, stieltjesDTilde, mellin, mellin]
    congr 1
    · have : ∀ t ∈ Ioi (0 : ℝ), (t : ℂ) ^ ((n : ℂ) + 1 - 1) • trunc₁ (stieltjesRem f a 1 n) t =
          (Ioc 0 1).indicator (fun τ : ℝ => (τ : ℂ) ^ n * stieltjesRem f a 1 n τ) t := by
        intro t _
        simp only [trunc₁, indicator, add_sub_cancel_right, cpow_natCast, smul_eq_mul]
        split_ifs <;> simp
      rw [setIntegral_congr_fun measurableSet_Ioi this, setIntegral_indicator measurableSet_Ioc,
        inter_eq_right.mpr Ioc_subset_Ioi_self]
    · have : ∀ t ∈ Ioi (0 : ℝ), (t : ℂ) ^ ((n : ℂ) + 1 - 1) •
          trunc₂ (stieltjesRem f a 1 (n + 1)) t =
          (Ioi 1).indicator (fun τ : ℝ => (τ : ℂ) ^ n * stieltjesRem f a 1 (n + 1) τ) t := by
        intro t ht
        rw [trunc₂_eq_indicator ht]
        simp only [indicator, add_sub_cancel_right, cpow_natCast, smul_eq_mul]
        split_ifs <;> simp
      rw [setIntegral_congr_fun measurableSet_Ioi this, setIntegral_indicator measurableSet_Ioi,
        inter_eq_right.mpr (Ioi_subset_Ioi zero_le_one)]
  -- the function agrees with `G` on a punctured neighbourhood
  have hev : ∀ᶠ z in 𝓝[≠] ((n : ℂ) + 1),
      mellinCont f a 1 z + a n / (z - ((n : ℂ) + 1)) = G z := by
    have hopen : IsOpen {z : ℂ | (n : ℝ) < z.re ∧ z.re < n + 2} :=
      (isOpen_lt continuous_const continuous_re).inter (isOpen_lt continuous_re continuous_const)
    have hmem : ((n : ℂ) + 1) ∈ {z : ℂ | (n : ℝ) < z.re ∧ z.re < n + 2} := by
      simp only [mem_ofPred_eq, add_re, natCast_re, one_re]
      constructor <;> linarith
    filter_upwards [nhdsWithin_le_nhds (hopen.mem_nhds hmem), self_mem_nhdsWithin] with z hz hz'
    obtain ⟨hz1, hz2⟩ := hz
    have hz'' : ∀ s ≤ n, z ≠ s + ((1 : ℝ) : ℂ) := by
      intro s hs h
      rcases Nat.lt_or_ge s n with hlt | hge
      · have := congrArg Complex.re h
        simp only [add_re, natCast_re, ofReal_one, one_re] at this
        have : (s : ℝ) + 1 ≤ n := by exact_mod_cast hlt
        linarith
      · have : s = n := le_antisymm hs hge
        subst this
        exact hz' (by rw [h]; simp)
    rw [mellinCont, hS.mellinTrunc₂ContZero_eq_sum_add (by linarith) hz'', hG]
    simp only [ofReal_one, Finset.sum_range_succ]
    field_simp
    ring
  rw [← hGval]
  exact Tendsto.congr' (hev.mono fun z hz => hz.symm)
    (hGcont.tendsto.mono_left nhdsWithin_le_nhds)

end StieltjesSetup

end Azurite.DLMF
