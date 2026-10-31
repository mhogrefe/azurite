/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter1.Section16Derivatives
import Mathlib.Analysis.Distribution.TemperedDistribution

/-!
# DLMF §1.16(v): Tempered distributions

https://dlmf.nist.gov/1.16.v

* `𝒯(ℝ)` (`IsTempTest`, `tempSpace`): smooth functions whose derivatives are `O(|x|^{−N})` for
  all `N`. This is equivalent to the bounds `|x^N φ⁽ᵏ⁾| ≤ c_{k,N}` of 1.16.24
  (`isTempTest_iff_bound`), and `𝒯(ℝ)` is Mathlib's Schwartz space `𝓢(ℝ, ℂ)`
  (`isTempTest_iff_schwartz`, `tempEquiv`).
* Convergence in `𝒯` (`TempConverges`, 1.16.24): locally uniform convergence of all derivatives
  with `n`-independent bounds. It is equivalent to the usual weighted uniform convergence
  (`tempConverges_iff`) and to convergence in the topology of `𝓢(ℝ, ℂ)`
  (`tempConverges_iff_tendsto`).
* Tempered distributions (`IsTempDist`, `temperedSpace` = `𝒯*`) are exactly the continuous linear
  functionals on `𝓢(ℝ, ℂ)` (`isTempDist_iff_continuous`, `isTempDist_iff_exists_clm`), that is,
  the elements of Mathlib's `𝓢'(ℝ, ℂ)`. 1.16.25 defines convergence in `𝒯*`
  (`TempDistConverges`).
* Derivatives `tempDeriv` (`⟨Λ', φ⟩ = −⟨Λ, φ'⟩` and iterates, as in §1.16(ii)).
* Examples:
  * `𝒟(ℝ) ⊆ 𝒯(ℝ)`, with convergence (`TestConverges.tempConverges`), so `𝒯* ⊆ 𝒟*(ℝ)`
    (`IsTempDist.isDistribution`).
  * `δ_{x₀}` (`tempDirac`).
  * The regular tempered distributions of polynomially bounded measurable functions
    (`tempRegular`). On `𝒟(ℝ)` these agree with `Λ_f` (`tempRegular_comp_testToTemp`).
-/

open Set Filter Topology MeasureTheory Asymptotics
open scoped ContDiff SchwartzMap

namespace Azurite.DLMF

/-! ### The space `𝒯(ℝ)` -/

/-- DLMF §1.16(v): a test function for tempered distributions: infinitely differentiable, with
the function and all its derivatives `O(|x|^{−N})` as `|x| → ∞` for all `N`. -/
def IsTempTest (φ : ℝ → ℂ) : Prop :=
  ContDiff ℝ ∞ φ ∧ ∀ k N : ℕ, iteratedDeriv k φ =O[cocompact ℝ] fun x => (|x| ^ N)⁻¹

theorem norm_pow_mul (x : ℝ) (N : ℕ) (z : ℂ) : ‖(x : ℂ) ^ N * z‖ = |x| ^ N * ‖z‖ := by
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]

/-- The decay condition is equivalent to the bounds `|x^N φ⁽ᵏ⁾(x)| ≤ c_{k,N}` of 1.16.24. -/
theorem isTempTest_iff_bound {φ : ℝ → ℂ} :
    IsTempTest φ ↔ ContDiff ℝ ∞ φ ∧
      ∀ k N : ℕ, ∃ c, ∀ x : ℝ, ‖(x : ℂ) ^ N * iteratedDeriv k φ x‖ ≤ c := by
  refine and_congr_right fun hφ => forall_congr' fun k => forall_congr' fun N => ?_
  have hcont : Continuous (iteratedDeriv k φ) := hφ.continuous_iteratedDeriv k
    (by exact_mod_cast le_top)
  simp_rw [norm_pow_mul]
  constructor
  · intro h
    obtain ⟨c, hc⟩ := h.bound
    rw [cocompact_eq_atBot_atTop, eventually_sup, eventually_atBot, eventually_atTop] at hc
    obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := hc
    set R := max (max (-a) b) 1
    obtain ⟨M, hM⟩ := (isCompact_Icc (a := -R) (b := R)).exists_bound_of_continuousOn
      hcont.continuousOn
    refine ⟨max c 0 + R ^ N * max M 0, fun x => ?_⟩
    by_cases hx : |x| ≤ R
    · have h1 := hM x (abs_le.mp hx)
      have h2 : |x| ^ N ≤ R ^ N := pow_le_pow_left₀ (abs_nonneg x) hx N
      have h3 : |x| ^ N * ‖iteratedDeriv k φ x‖ ≤ R ^ N * max M 0 :=
        mul_le_mul h2 (h1.trans (le_max_left _ _)) (norm_nonneg _)
          (pow_nonneg (by linarith [le_max_right (max (-a) b) 1]) N)
      linarith [le_max_right c 0]
    · have hR1 : 1 ≤ R := le_max_right _ _
      have hxpos : 0 < |x| := by linarith
      have hbound : ‖iteratedDeriv k φ x‖ ≤ c * ‖(|x| ^ N)⁻¹‖ := by
        rcases le_or_gt x 0 with hx0 | hx0
        · refine ha x ?_
          rw [abs_of_nonpos hx0] at hx
          linarith [le_max_left (-a) b, le_max_left (max (-a) b) 1]
        · refine hb x ?_
          rw [abs_of_pos hx0] at hx
          linarith [le_max_right (-a) b, le_max_left (max (-a) b) 1]
      rw [norm_inv, norm_pow, Real.norm_eq_abs, abs_abs] at hbound
      have hpos : 0 < |x| ^ N := pow_pos hxpos N
      have : |x| ^ N * ‖iteratedDeriv k φ x‖ ≤ c := by
        calc |x| ^ N * ‖iteratedDeriv k φ x‖ ≤ |x| ^ N * (c * (|x| ^ N)⁻¹) :=
              mul_le_mul_of_nonneg_left hbound hpos.le
          _ = c := by field_simp
      nlinarith [le_max_left c 0, pow_nonneg (show (0 : ℝ) ≤ R by linarith) N,
        le_max_right M 0]
  · rintro ⟨c, hc⟩
    refine IsBigO.of_bound c ?_
    rw [cocompact_eq_atBot_atTop, eventually_sup, eventually_atBot, eventually_atTop]
    have key : ∀ x : ℝ, x ≠ 0 → ‖iteratedDeriv k φ x‖ ≤ c * ‖(|x| ^ N)⁻¹‖ := fun x hx => by
      have hpos : 0 < |x| ^ N := pow_pos (abs_pos.mpr hx) N
      rw [norm_inv, norm_pow, Real.norm_eq_abs, abs_abs, ← div_eq_mul_inv, le_div_iff₀ hpos,
        mul_comm]
      exact hc x
    exact ⟨⟨-1, fun x hx => key x (by linarith)⟩, ⟨1, fun x hx => key x (by linarith)⟩⟩

/-- `𝒯(ℝ)` is Mathlib's Schwartz space `𝓢(ℝ, ℂ)`. -/
theorem isTempTest_iff_schwartz {φ : ℝ → ℂ} : IsTempTest φ ↔ ∃ ψ : 𝓢(ℝ, ℂ), ⇑ψ = φ := by
  rw [isTempTest_iff_bound]
  simp_rw [norm_pow_mul]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨⟨φ, h1, fun k n => ?_⟩, rfl⟩
    obtain ⟨c, hc⟩ := h2 n k
    exact ⟨c, fun x => by
      rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs]; exact hc x⟩
  · rintro ⟨ψ, rfl⟩
    refine ⟨ψ.smooth ⊤, fun k N => ?_⟩
    obtain ⟨c, hc⟩ := ψ.decay N k
    exact ⟨c, fun x => by
      have := hc.2 x
      rwa [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs] at this⟩

/-- The space `𝒯(ℝ)`. -/
def tempSpace : Submodule ℂ (ℝ → ℂ) where
  carrier := {φ | IsTempTest φ}
  add_mem' := fun {φ ψ} hφ hψ => by
    obtain ⟨f, rfl⟩ := isTempTest_iff_schwartz.mp hφ
    obtain ⟨g, rfl⟩ := isTempTest_iff_schwartz.mp hψ
    exact isTempTest_iff_schwartz.mpr ⟨f + g, rfl⟩
  zero_mem' := isTempTest_iff_schwartz.mpr ⟨0, rfl⟩
  smul_mem' := fun c φ hφ => by
    obtain ⟨f, rfl⟩ := isTempTest_iff_schwartz.mp hφ
    exact isTempTest_iff_schwartz.mpr ⟨c • f, rfl⟩

theorem mem_tempSpace {φ : ℝ → ℂ} : φ ∈ tempSpace ↔ IsTempTest φ := Iff.rfl

/-- The identification `𝒯(ℝ) ≃ 𝓢(ℝ, ℂ)`. -/
noncomputable def tempEquiv : tempSpace ≃ₗ[ℂ] 𝓢(ℝ, ℂ) where
  toFun φ := (isTempTest_iff_schwartz.mp φ.2).choose
  invFun ψ := ⟨ψ, isTempTest_iff_schwartz.mpr ⟨ψ, rfl⟩⟩
  map_add' φ ψ := by
    ext x
    simp only [add_apply, (isTempTest_iff_schwartz.mp (φ + ψ).2).choose_spec,
      (isTempTest_iff_schwartz.mp φ.2).choose_spec, (isTempTest_iff_schwartz.mp ψ.2).choose_spec]
    rfl
  map_smul' c φ := by
    ext x
    simp only [smul_apply, (isTempTest_iff_schwartz.mp (c • φ).2).choose_spec,
      (isTempTest_iff_schwartz.mp φ.2).choose_spec, RingHom.id_apply]
    rfl
  left_inv φ := by
    ext x
    simp [(isTempTest_iff_schwartz.mp φ.2).choose_spec]
  right_inv ψ := by
    ext x
    exact congrFun (isTempTest_iff_schwartz.mp (isTempTest_iff_schwartz.mpr ⟨ψ, rfl⟩)).choose_spec x

theorem coe_tempEquiv (φ : tempSpace) : ⇑(tempEquiv φ) = (φ : ℝ → ℂ) :=
  (isTempTest_iff_schwartz.mp φ.2).choose_spec

theorem coe_tempEquiv_symm (ψ : 𝓢(ℝ, ℂ)) : ((tempEquiv.symm ψ : tempSpace) : ℝ → ℂ) = ψ := rfl

/-! ### Convergence in `𝒯` (1.16.24) -/

/-- DLMF §1.16(v), 1.16.24: `φₙ → φ` in `𝒯` when `φₙ⁽ᵏ⁾ → φ⁽ᵏ⁾` uniformly on every finite
interval and `|x^N φₙ⁽ᵏ⁾(x)| ≤ c_{k,N}` with `c_{k,N}` independent of `n`. -/
def TempConverges (φs : ℕ → ℝ → ℂ) (φ : ℝ → ℂ) : Prop :=
  (∀ (k : ℕ) (a b : ℝ),
    TendstoUniformlyOn (fun n => iteratedDeriv k (φs n)) (iteratedDeriv k φ) atTop (Icc a b)) ∧
  ∀ k N : ℕ, ∃ c, ∀ n (x : ℝ), ‖(x : ℂ) ^ N * iteratedDeriv k (φs n) x‖ ≤ c

/-- Weighted uniform convergence: `sup_x |x|^N |φₙ⁽ᵏ⁾(x) − φ⁽ᵏ⁾(x)| → 0` for all `k`, `N`. -/
def WeightedConverges (φs : ℕ → ℝ → ℂ) (φ : ℝ → ℂ) : Prop :=
  ∀ k N : ℕ, ∀ ε > 0, ∀ᶠ n in atTop,
    ∀ x : ℝ, |x| ^ N * ‖iteratedDeriv k (φs n) x - iteratedDeriv k φ x‖ ≤ ε

/-- DLMF's convergence in `𝒯` is the usual convergence of Schwartz functions. -/
theorem tempConverges_iff {φs : ℕ → ℝ → ℂ} {φ : ℝ → ℂ} (hφs : ∀ n, IsTempTest (φs n))
    (hφ : IsTempTest φ) : TempConverges φs φ ↔ WeightedConverges φs φ := by
  constructor
  · rintro ⟨hloc, hb⟩ k N ε hε
    obtain ⟨c, hc⟩ := hb k (N + 1)
    obtain ⟨d, hd⟩ := (isTempTest_iff_bound.mp hφ).2 k (N + 1)
    simp_rw [norm_pow_mul] at hc hd
    set R := max 1 (2 * (|c| + |d|) / ε) with hRdef
    have hR1 : 1 ≤ R := le_max_left _ _
    have hR0 : 0 < R := by linarith
    have hδ : 0 < ε / (R ^ N + 1) := by positivity
    filter_upwards [Metric.tendstoUniformlyOn_iff.mp (hloc k (-R) R) _ hδ] with n hn x
    by_cases hx : |x| ≤ R
    · have h1 := hn x (abs_le.mp hx)
      rw [dist_comm, dist_eq_norm] at h1
      calc |x| ^ N * ‖iteratedDeriv k (φs n) x - iteratedDeriv k φ x‖
          ≤ R ^ N * (ε / (R ^ N + 1)) :=
            mul_le_mul (pow_le_pow_left₀ (abs_nonneg x) hx N) h1.le (norm_nonneg _)
              (by positivity)
        _ ≤ ε := by
            rw [mul_div_assoc', div_le_iff₀ (by positivity)]
            nlinarith [pow_nonneg hR0.le N]
    · have hxpos : 0 < |x| := by linarith
      have h1 : |x| ^ (N + 1) * ‖iteratedDeriv k (φs n) x - iteratedDeriv k φ x‖ ≤ |c| + |d| := by
        calc |x| ^ (N + 1) * ‖iteratedDeriv k (φs n) x - iteratedDeriv k φ x‖
            ≤ |x| ^ (N + 1) * ‖iteratedDeriv k (φs n) x‖ +
                |x| ^ (N + 1) * ‖iteratedDeriv k φ x‖ := by
              rw [← mul_add]
              exact mul_le_mul_of_nonneg_left (norm_sub_le _ _) (by positivity)
          _ ≤ |c| + |d| := add_le_add ((hc n x).trans (le_abs_self c))
              ((hd x).trans (le_abs_self d))
      have h2 : |c| + |d| ≤ ε / 2 * |x| := by
        have : 2 * (|c| + |d|) / ε ≤ R := le_max_right _ _
        rw [div_le_iff₀ hε] at this
        nlinarith
      have h3 : |x| ^ N * ‖iteratedDeriv k (φs n) x - iteratedDeriv k φ x‖ * |x| ≤
          ε / 2 * |x| := by
        calc _ = |x| ^ (N + 1) * ‖iteratedDeriv k (φs n) x - iteratedDeriv k φ x‖ := by ring
          _ ≤ _ := h1.trans h2
      have := le_of_mul_le_mul_right h3 hxpos
      linarith
  · intro hw
    refine ⟨fun k a b => ?_, fun k N => ?_⟩
    · rw [Metric.tendstoUniformlyOn_iff]
      intro ε hε
      filter_upwards [hw k 0 (ε / 2) (by positivity)] with n hn x _
      have := hn x
      rw [pow_zero, one_mul] at this
      rw [dist_comm, dist_eq_norm]
      linarith
    · obtain ⟨d, hd⟩ := (isTempTest_iff_bound.mp hφ).2 k N
      simp_rw [norm_pow_mul] at hd ⊢
      obtain ⟨n₀, hn₀⟩ := eventually_atTop.mp (hw k N 1 one_pos)
      have hcs : ∀ n, ∃ c, ∀ x : ℝ, |x| ^ N * ‖iteratedDeriv k (φs n) x‖ ≤ c := fun n => by
        obtain ⟨c, hc⟩ := (isTempTest_iff_bound.mp (hφs n)).2 k N
        simp_rw [norm_pow_mul] at hc
        exact ⟨c, hc⟩
      choose c hc using hcs
      have hd0 : 0 ≤ d := (mul_nonneg (pow_nonneg (abs_nonneg 0) N) (norm_nonneg _)).trans (hd 0)
      refine ⟨d + 1 + ∑ n ∈ Finset.range n₀, |c n|, fun n x => ?_⟩
      have hsum : 0 ≤ ∑ n ∈ Finset.range n₀, |c n| :=
        Finset.sum_nonneg fun _ _ => abs_nonneg _
      by_cases hn : n₀ ≤ n
      · have h1 := hn₀ n hn x
        have h2 : |x| ^ N * ‖iteratedDeriv k (φs n) x‖ ≤
            |x| ^ N * ‖iteratedDeriv k (φs n) x - iteratedDeriv k φ x‖ +
              |x| ^ N * ‖iteratedDeriv k φ x‖ := by
          rw [← mul_add]
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          calc ‖iteratedDeriv k (φs n) x‖ =
              ‖(iteratedDeriv k (φs n) x - iteratedDeriv k φ x) + iteratedDeriv k φ x‖ := by
                rw [sub_add_cancel]
            _ ≤ _ := norm_add_le _ _
        linarith [hd x]
      · have hmem : n ∈ Finset.range n₀ := Finset.mem_range.mpr (not_le.mp hn)
        have := Finset.single_le_sum (f := fun n => |c n|) (fun _ _ => abs_nonneg _) hmem
        linarith [hc n x, le_abs_self (c n)]

theorem norm_iteratedFDeriv_tempEquiv_sub (a b : tempSpace) (k : ℕ) (x : ℝ) :
    ‖iteratedFDeriv ℝ k ⇑(tempEquiv a - tempEquiv b) x‖ =
      ‖iteratedDeriv k (a : ℝ → ℂ) x - iteratedDeriv k (b : ℝ → ℂ) x‖ := by
  have e : ⇑(tempEquiv a - tempEquiv b) = (a : ℝ → ℂ) - (b : ℝ → ℂ) := by
    ext y; simp [coe_tempEquiv]
  rw [e, norm_iteratedFDeriv_eq_norm_iteratedDeriv,
    iteratedDeriv_sub (a.2.1.contDiffAt.of_le (by exact_mod_cast le_top))
      (b.2.1.contDiffAt.of_le (by exact_mod_cast le_top))]

/-- Convergence in `𝒯` is convergence in the topology of Mathlib's `𝓢(ℝ, ℂ)`. -/
theorem tempConverges_iff_tendsto (φs : ℕ → tempSpace) (φ : tempSpace) :
    TempConverges (fun n => φs n) φ ↔
      Tendsto (fun n => tempEquiv (φs n)) atTop (𝓝 (tempEquiv φ)) := by
  rw [tempConverges_iff (fun n => (φs n).2) φ.2, (schwartz_withSeminorms ℂ ℝ ℂ).tendsto_nhds]
  constructor
  · rintro hw ⟨N, k⟩ ε hε
    filter_upwards [hw k N (ε / 2) (by positivity)] with n hn
    rw [SchwartzMap.schwartzSeminormFamily_apply]
    refine lt_of_le_of_lt (SchwartzMap.seminorm_le_bound ℂ N k _ (M := ε / 2) (by positivity)
      fun x => ?_) (by linarith)
    rw [norm_iteratedFDeriv_tempEquiv_sub, Real.norm_eq_abs]
    exact hn x
  · intro h k N ε hε
    filter_upwards [h (N, k) ε hε] with n hn x
    have := SchwartzMap.le_seminorm ℂ N k (tempEquiv (φs n) - tempEquiv φ) x
    rw [norm_iteratedFDeriv_tempEquiv_sub, Real.norm_eq_abs] at this
    rw [SchwartzMap.schwartzSeminormFamily_apply] at hn
    exact this.trans hn.le

/-! ### Tempered distributions -/

/-- DLMF §1.16(v): a tempered distribution is a continuous linear functional on `𝒯`, continuity
being sequential as in §1.16(i). -/
def IsTempDist (Λ : tempSpace →ₗ[ℂ] ℂ) : Prop :=
  ∀ (φs : ℕ → tempSpace) (φ : tempSpace), TempConverges (fun n => φs n) φ →
    Tendsto (fun n => Λ (φs n)) atTop (𝓝 (Λ φ))

/-- The space `𝒯*` of tempered distributions. -/
def temperedSpace : Submodule ℂ (tempSpace →ₗ[ℂ] ℂ) where
  carrier := {Λ | IsTempDist Λ}
  add_mem' := fun hΛ hM φs φ h => by
    simpa only [LinearMap.add_apply] using (hΛ φs φ h).add (hM φs φ h)
  zero_mem' := fun φs φ _ => by simp
  smul_mem' := fun c Λ hΛ φs φ h => by
    simpa only [LinearMap.smul_apply, smul_eq_mul] using (hΛ φs φ h).const_mul c

/-- DLMF tempered distributions are exactly the continuous linear functionals on Mathlib's
Schwartz space `𝓢(ℝ, ℂ)` (the elements of `𝓢'(ℝ, ℂ)`). -/
theorem isTempDist_iff_continuous (Λ : tempSpace →ₗ[ℂ] ℂ) :
    IsTempDist Λ ↔ Continuous (Λ ∘ₗ tempEquiv.symm.toLinearMap) := by
  rw [continuous_iff_seqContinuous]
  constructor
  · intro h ψs ψ hψ
    have := h (fun n => tempEquiv.symm (ψs n)) (tempEquiv.symm ψ)
      ((tempConverges_iff_tendsto _ _).mpr (by simpa using hψ))
    simpa [Function.comp_def] using this
  · intro h φs φ hc
    have := h ((tempConverges_iff_tendsto φs φ).mp hc)
    simpa [Function.comp_def] using this

theorem isTempDist_iff_exists_clm (Λ : tempSpace →ₗ[ℂ] ℂ) :
    IsTempDist Λ ↔ ∃ T : 𝓢(ℝ, ℂ) →L[ℂ] ℂ, ∀ φ, T (tempEquiv φ) = Λ φ := by
  rw [isTempDist_iff_continuous]
  constructor
  · intro h
    exact ⟨⟨Λ ∘ₗ tempEquiv.symm.toLinearMap, h⟩, fun φ => by simp⟩
  · rintro ⟨T, hT⟩
    have : Λ ∘ₗ tempEquiv.symm.toLinearMap = T.toLinearMap := by
      ext ψ
      simpa using (hT (tempEquiv.symm ψ)).symm
    rw [this]
    exact T.continuous

/-- DLMF 1.16.25: `Λₙ → Λ` in `𝒯*` when `⟨Λₙ, φ⟩ → ⟨Λ, φ⟩` for all `φ ∈ 𝒯`. -/
def TempDistConverges (Λs : ℕ → tempSpace →ₗ[ℂ] ℂ) (Λ : tempSpace →ₗ[ℂ] ℂ) : Prop :=
  ∀ φ : tempSpace, Tendsto (fun n => Λs n φ) atTop (𝓝 (Λ φ))

theorem dlmf_1_16_25 (Λs : ℕ → tempSpace →ₗ[ℂ] ℂ) (Λ : tempSpace →ₗ[ℂ] ℂ) :
    TempDistConverges Λs Λ ↔ ∀ φ : tempSpace, Tendsto (fun n => Λs n φ) atTop (𝓝 (Λ φ)) :=
  Iff.rfl

/-! ### Derivatives of tempered distributions -/

theorem isTempTest_deriv {φ : ℝ → ℂ} (hφ : IsTempTest φ) : IsTempTest (deriv φ) := by
  rw [isTempTest_iff_bound] at hφ ⊢
  refine ⟨(contDiff_infty_iff_deriv.mp hφ.1).2, fun k N => ?_⟩
  obtain ⟨c, hc⟩ := hφ.2 (k + 1) N
  exact ⟨c, fun x => by rw [← iteratedDeriv_succ']; exact hc x⟩

/-- Differentiation `φ ↦ φ'` on `𝒯`. -/
noncomputable def derivTempTest : tempSpace →ₗ[ℂ] tempSpace where
  toFun φ := ⟨deriv (φ : ℝ → ℂ), isTempTest_deriv φ.2⟩
  map_add' φ ψ := by
    ext x
    simp only [Submodule.coe_add, Pi.add_apply]
    exact deriv_add ((φ.2.1.differentiable (by simp)) x) ((ψ.2.1.differentiable (by simp)) x)
  map_smul' c φ := by
    ext x
    simp only [Submodule.coe_smul, RingHom.id_apply, Pi.smul_apply]
    exact deriv_const_smul c ((φ.2.1.differentiable (by simp)) x)

theorem coe_derivTempTest (φ : tempSpace) :
    (derivTempTest φ : ℝ → ℂ) = deriv (φ : ℝ → ℂ) := rfl

theorem TempConverges.deriv {φs : ℕ → ℝ → ℂ} {φ : ℝ → ℂ} (h : TempConverges φs φ) :
    TempConverges (fun n => _root_.deriv (φs n)) (_root_.deriv φ) := by
  refine ⟨fun k a b => ?_, fun k N => ?_⟩
  · simp only [← iteratedDeriv_succ']; exact h.1 (k + 1) a b
  · simp only [← iteratedDeriv_succ']; exact h.2 (k + 1) N

/-- DLMF §1.16(v): the derivative of a tempered distribution, `⟨Λ', φ⟩ = −⟨Λ, φ'⟩`. -/
noncomputable def tempDeriv (Λ : tempSpace →ₗ[ℂ] ℂ) : tempSpace →ₗ[ℂ] ℂ :=
  -(Λ ∘ₗ derivTempTest)

theorem tempDeriv_apply (Λ : tempSpace →ₗ[ℂ] ℂ) (φ : tempSpace) :
    tempDeriv Λ φ = -Λ (derivTempTest φ) := rfl

theorem isTempDist_tempDeriv {Λ : tempSpace →ₗ[ℂ] ℂ} (hΛ : IsTempDist Λ) :
    IsTempDist (tempDeriv Λ) :=
  fun φs φ h => (hΛ (fun n => derivTempTest (φs n)) (derivTempTest φ) h.deriv).neg

theorem coe_derivTempTest_iterate (k : ℕ) (φ : tempSpace) :
    (derivTempTest^[k] φ : ℝ → ℂ) = iteratedDeriv k (φ : ℝ → ℂ) := by
  induction k with
  | zero => simp
  | succ k ih => rw [Function.iterate_succ_apply', coe_derivTempTest, ih, iteratedDeriv_succ]

/-- `⟨Λ⁽ᵏ⁾, φ⟩ = (−1)ᵏ ⟨Λ, φ⁽ᵏ⁾⟩`, as in 1.16.9. -/
theorem tempDeriv_iterate_apply (Λ : tempSpace →ₗ[ℂ] ℂ) (k : ℕ) (φ : tempSpace) :
    (tempDeriv^[k] Λ) φ = (-1) ^ k * Λ (derivTempTest^[k] φ) := by
  induction k generalizing φ with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', tempDeriv_apply, ih, Function.iterate_succ_apply]
    ring

/-! ### Examples -/

/-- The Dirac delta `δ_{x₀}` is a tempered distribution. -/
noncomputable def tempDirac (x₀ : ℝ) : tempSpace →ₗ[ℂ] ℂ where
  toFun φ := (φ : ℝ → ℂ) x₀
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem isTempDist_tempDirac (x₀ : ℝ) : IsTempDist (tempDirac x₀) := by
  intro φs φ h
  have := (h.1 0 x₀ x₀).tendsto_at (left_mem_Icc.mpr le_rfl)
  simp only [iteratedDeriv_zero] at this
  exact this

theorem tsupport_iteratedDeriv_subset (φ : ℝ → ℂ) (k : ℕ) :
    tsupport (iteratedDeriv k φ) ⊆ tsupport φ := by
  induction k with
  | zero => simp
  | succ k ih => rw [iteratedDeriv_succ]; exact tsupport_deriv_subset.trans ih

/-- Test functions are tempered test functions: `𝒟(ℝ) ⊆ 𝒯(ℝ)`. -/
theorem isTempTest_of_isTestFunction {φ : ℝ → ℂ} (hφ : IsTestFunction univ φ) :
    IsTempTest φ := by
  rw [isTempTest_iff_bound]
  refine ⟨hφ.1, fun k N => ?_⟩
  have hc : Continuous fun x : ℝ => (x : ℂ) ^ N * iteratedDeriv k φ x :=
    (Complex.continuous_ofReal.pow N).mul (hφ.1.continuous_iteratedDeriv k
      (by exact_mod_cast le_top))
  have hs : HasCompactSupport fun x : ℝ => (x : ℂ) ^ N * iteratedDeriv k φ x :=
    (hφ.2.1.mono' (subset_tsupport _ |>.trans (tsupport_iteratedDeriv_subset φ k))).mul_left
  exact hc.bounded_above_of_compact_support hs

/-- Convergence in `𝒟(ℝ)` implies convergence in `𝒯(ℝ)`. -/
theorem TestConverges.tempConverges {φs : ℕ → ℝ → ℂ} {φ : ℝ → ℂ}
    (hφs : ∀ n, IsTestFunction univ (φs n)) (hφ : IsTestFunction univ φ)
    (h : TestConverges univ φs φ) : TempConverges φs φ := by
  rw [tempConverges_iff (fun n => isTempTest_of_isTestFunction (hφs n))
    (isTempTest_of_isTestFunction hφ)]
  obtain ⟨K, hK, -, hs, hφK, hu⟩ := h
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall 0
  intro k N ε hε
  have hδ : 0 < ε / (|R| ^ N + 1) := by positivity
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp (hu k) _ hδ] with n hn x
  by_cases hx : x ∈ K
  · have h1 := hn x hx
    rw [dist_comm, dist_eq_norm] at h1
    have hxR : |x| ≤ |R| := by
      have := hR hx
      rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] at this
      exact this.trans (le_abs_self R)
    calc |x| ^ N * ‖iteratedDeriv k (φs n) x - iteratedDeriv k φ x‖
        ≤ |R| ^ N * (ε / (|R| ^ N + 1)) :=
          mul_le_mul (pow_le_pow_left₀ (abs_nonneg x) hxR N) h1.le (norm_nonneg _)
            (by positivity)
      _ ≤ ε := by
          rw [mul_div_assoc', div_le_iff₀ (by positivity)]
          nlinarith [pow_nonneg (abs_nonneg R) N]
  · rw [iteratedDeriv_eq_zero_of_notMem_tsupport (fun h => hx (hs n h)),
      iteratedDeriv_eq_zero_of_notMem_tsupport (fun h => hx (hφK h)), sub_zero, norm_zero,
      mul_zero]
    exact hε.le

/-- The inclusion `𝒟(ℝ) → 𝒯(ℝ)`. -/
noncomputable def testToTemp : testSpace univ →ₗ[ℂ] tempSpace where
  toFun φ := ⟨φ, isTempTest_of_isTestFunction φ.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- A tempered distribution restricts to a distribution on `ℝ`: `𝒯* ⊆ 𝒟*(ℝ)`. -/
theorem IsTempDist.isDistribution {Λ : tempSpace →ₗ[ℂ] ℂ} (hΛ : IsTempDist Λ) :
    IsDistribution univ (Λ ∘ₗ testToTemp) := fun φs φ h =>
  hΛ (fun n => testToTemp (φs n)) (testToTemp φ)
    (h.tempConverges (fun n => (φs n).2) φ.2)

/-! ### Regular tempered distributions -/

theorem one_add_abs_pow_le (x : ℝ) (m : ℕ) : (1 + |x|) ^ m ≤ 2 ^ m * (1 + |x| ^ m) := by
  rcases le_or_gt |x| 1 with hx | hx
  · calc (1 + |x|) ^ m ≤ 2 ^ m := pow_le_pow_left₀ (by positivity) (by linarith) m
      _ ≤ 2 ^ m * (1 + |x| ^ m) := le_mul_of_one_le_right (by positivity)
          (by linarith [pow_nonneg (abs_nonneg x) m])
  · calc (1 + |x|) ^ m ≤ (2 * |x|) ^ m := pow_le_pow_left₀ (by positivity) (by linarith) m
      _ = 2 ^ m * |x| ^ m := mul_pow _ _ _
      _ ≤ 2 ^ m * (1 + |x| ^ m) := by gcongr; linarith

/-- The key estimate: if `|f(x)| ≤ C(1 + |x|)^M` and `|g| ≤ ε`, `|x|^{M+2}|g| ≤ ε`, then
`|f g| ≤ 2^{M+3} C ε/(1 + x²)`. -/
theorem norm_mul_le_of_polyBound {f g : ℝ → ℂ} {C ε : ℝ} {M : ℕ} (hC : 0 ≤ C)
    (hb : ∀ x, ‖f x‖ ≤ C * (1 + |x|) ^ M) (h0 : ∀ x, ‖g x‖ ≤ ε)
    (hM : ∀ x, |x| ^ (M + 2) * ‖g x‖ ≤ ε) (x : ℝ) :
    ‖f x * g x‖ ≤ C * 2 ^ (M + 2) * (2 * ε) * (1 + x ^ 2)⁻¹ := by
  have hpos : 0 < 1 + |x| := by positivity
  have h1 : (1 + |x|) ^ (M + 2) * ‖g x‖ ≤ 2 ^ (M + 2) * (2 * ε) := by
    calc (1 + |x|) ^ (M + 2) * ‖g x‖ ≤ 2 ^ (M + 2) * (1 + |x| ^ (M + 2)) * ‖g x‖ :=
          mul_le_mul_of_nonneg_right (one_add_abs_pow_le x _) (norm_nonneg _)
      _ = 2 ^ (M + 2) * (‖g x‖ + |x| ^ (M + 2) * ‖g x‖) := by ring
      _ ≤ 2 ^ (M + 2) * (2 * ε) := by gcongr; linarith [h0 x, hM x]
  have h2 : 1 + x ^ 2 ≤ (1 + |x|) ^ 2 := by nlinarith [sq_abs x, abs_nonneg x]
  have h3 : (1 + |x|) ^ M * ‖g x‖ ≤ 2 ^ (M + 2) * (2 * ε) * (1 + x ^ 2)⁻¹ := by
    rw [← div_eq_mul_inv, le_div_iff₀ (by positivity)]
    calc (1 + |x|) ^ M * ‖g x‖ * (1 + x ^ 2) ≤ (1 + |x|) ^ M * ‖g x‖ * (1 + |x|) ^ 2 :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = (1 + |x|) ^ (M + 2) * ‖g x‖ := by ring
      _ ≤ _ := h1
  rw [norm_mul]
  calc ‖f x‖ * ‖g x‖ ≤ C * (1 + |x|) ^ M * ‖g x‖ :=
        mul_le_mul_of_nonneg_right (hb x) (norm_nonneg _)
    _ = C * ((1 + |x|) ^ M * ‖g x‖) := by ring
    _ ≤ C * (2 ^ (M + 2) * (2 * ε) * (1 + x ^ 2)⁻¹) := mul_le_mul_of_nonneg_left h3 hC
    _ = _ := by ring

theorem exists_sup_bounds {φ : ℝ → ℂ} (hφ : IsTempTest φ) (M : ℕ) :
    ∃ ε, 0 ≤ ε ∧ (∀ x, ‖φ x‖ ≤ ε) ∧ ∀ x, |x| ^ (M + 2) * ‖φ x‖ ≤ ε := by
  obtain ⟨a, ha⟩ := (isTempTest_iff_bound.mp hφ).2 0 0
  obtain ⟨b, hb⟩ := (isTempTest_iff_bound.mp hφ).2 0 (M + 2)
  simp only [norm_pow_mul, iteratedDeriv_zero, pow_zero, one_mul] at ha hb
  refine ⟨max a b, (norm_nonneg _).trans ((ha 0).trans (le_max_left _ _)),
    fun x => (ha x).trans (le_max_left _ _), fun x => (hb x).trans (le_max_right _ _)⟩

theorem integrable_mul_of_polyBound {f : ℝ → ℂ} (hf : AEStronglyMeasurable f volume) {C : ℝ}
    {M : ℕ} (hC : 0 ≤ C) (hb : ∀ x, ‖f x‖ ≤ C * (1 + |x|) ^ M) {φ : ℝ → ℂ}
    (hφ : IsTempTest φ) : Integrable fun x => f x * φ x := by
  obtain ⟨ε, -, h0, hM⟩ := exists_sup_bounds hφ M
  exact (integrable_inv_one_add_sq.const_mul (C * 2 ^ (M + 2) * (2 * ε))).mono'
    (hf.mul hφ.1.continuous.aestronglyMeasurable)
    (ae_of_all _ fun x => norm_mul_le_of_polyBound hC hb h0 hM x)

/-- The regular tempered distribution `φ ↦ ∫ f φ` of a polynomially bounded measurable `f`. -/
noncomputable def tempRegular {f : ℝ → ℂ} (hf : AEStronglyMeasurable f volume) {C : ℝ} {M : ℕ}
    (hC : 0 ≤ C) (hb : ∀ x, ‖f x‖ ≤ C * (1 + |x|) ^ M) : tempSpace →ₗ[ℂ] ℂ where
  toFun φ := ∫ x, f x * (φ : ℝ → ℂ) x
  map_add' φ ψ := by
    simp only [Submodule.coe_add, Pi.add_apply, mul_add]
    exact integral_add (integrable_mul_of_polyBound hf hC hb φ.2)
      (integrable_mul_of_polyBound hf hC hb ψ.2)
  map_smul' c φ := by
    simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [← integral_const_mul]
    congr 1; funext x; ring

theorem isTempDist_tempRegular {f : ℝ → ℂ} (hf : AEStronglyMeasurable f volume) {C : ℝ}
    {M : ℕ} (hC : 0 ≤ C) (hb : ∀ x, ‖f x‖ ≤ C * (1 + |x|) ^ M) :
    IsTempDist (tempRegular hf hC hb) := by
  intro φs φ h
  have hw := (tempConverges_iff (fun n => (φs n).2) φ.2).mp h
  set A := ∫ x : ℝ, (1 + x ^ 2)⁻¹
  have hA : 0 ≤ A := integral_nonneg fun x => by positivity
  set K := C * 2 ^ (M + 2) * 2 * A
  have hK : 0 ≤ K := by positivity
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hδ : 0 < ε / (2 * (K + 1)) := by positivity
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.mp ((hw 0 0 _ hδ).and (hw 0 (M + 2) _ hδ))
  refine ⟨n₀, fun n hn => ?_⟩
  obtain ⟨h1, h2⟩ := hn₀ n hn
  simp only [iteratedDeriv_zero, pow_zero, one_mul] at h1 h2
  rw [dist_eq_norm]
  change ‖(∫ x, f x * (φs n : ℝ → ℂ) x) - ∫ x, f x * (φ : ℝ → ℂ) x‖ < ε
  rw [← integral_sub (integrable_mul_of_polyBound hf hC hb (φs n).2)
    (integrable_mul_of_polyBound hf hC hb φ.2)]
  simp_rw [← mul_sub]
  have hb' := norm_integral_le_of_norm_le
    (integrable_inv_one_add_sq.const_mul (C * 2 ^ (M + 2) * (2 * (ε / (2 * (K + 1))))))
    (ae_of_all _ fun x => norm_mul_le_of_polyBound (g := fun x =>
      (φs n : ℝ → ℂ) x - (φ : ℝ → ℂ) x) hC hb h1 h2 x)
  rw [integral_const_mul] at hb'
  refine hb'.trans_lt ?_
  calc C * 2 ^ (M + 2) * (2 * (ε / (2 * (K + 1)))) * A = K * (ε / (2 * (K + 1))) := by ring
    _ < ε := by
        rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
        nlinarith

theorem locallyIntegrable_of_polyBound {f : ℝ → ℂ} (hf : AEStronglyMeasurable f volume) {C : ℝ}
    {M : ℕ} (hb : ∀ x, ‖f x‖ ≤ C * (1 + |x|) ^ M) : LocallyIntegrable f volume := by
  rw [locallyIntegrable_iff]
  intro K hK
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall 0
  have : IsFiniteMeasure (volume.restrict K) := ⟨by
    rw [Measure.restrict_apply_univ]; exact hK.measure_lt_top⟩
  refine (integrable_const (C * (1 + |R|) ^ M)).mono' hf.restrict ?_
  filter_upwards [ae_restrict_mem hK.measurableSet] with x hx
  refine (hb x).trans ?_
  have hxR : |x| ≤ |R| := by
    have := hR hx
    rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] at this
    exact this.trans (le_abs_self R)
  have hC : 0 ≤ C := by
    have := (norm_nonneg _).trans (hb 0)
    simp only [abs_zero, add_zero, one_pow, mul_one] at this
    exact this
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) (by linarith) M) hC

/-- On `𝒟(ℝ)` the regular tempered distribution is the regular distribution `Λ_f` of 1.16.3. -/
theorem tempRegular_comp_testToTemp {f : ℝ → ℂ} (hf : AEStronglyMeasurable f volume) {C : ℝ}
    {M : ℕ} (hC : 0 ≤ C) (hb : ∀ x, ‖f x‖ ≤ C * (1 + |x|) ^ M) :
    tempRegular hf hC hb ∘ₗ testToTemp =
      regularDist isOpen_univ ((locallyIntegrable_of_polyBound hf hb).locallyIntegrableOn univ) := by
  ext φ
  simp only [LinearMap.comp_apply, dlmf_1_16_3, Measure.restrict_univ]
  rfl

end Azurite.DLMF
