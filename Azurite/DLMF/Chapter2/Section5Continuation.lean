/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/


import Azurite.DLMF.Chapter2.Section5Truncation

/-!
# DLMF §2.5(ii): the continuations 2.5.25–2.5.28

* 2.5.25 (`dlmf_2_5_25`): `𝓜f₁(z)` continues to a meromorphic function on `ℂ` with simple poles at
  `z = −αₛ` of principal parts `aₛ/(z + αₛ)`. The continuation is explicit: for `ℜz > −ℜα_N`,
  `𝓜f₁(z) = ∑_{s<N} aₛ/(z + αₛ) + ∫₀¹ t^{z−1} (f(t) − ∑_{s<N} aₛ t^{αₛ}) dt`
  (`mellinTrunc₁Ext`, `mellin_trunc₁_eq_ext`), the remainder integral being analytic there; the
  pieces are glued (`glue`) into `mellinTrunc₁Cont`.
* 2.5.26 (`dlmf_2_5_26`): `𝓜f(z) := 𝓜f₁(z) + 𝓜f₂(z)` for `ℜz < b` extends `𝓜f` with the same
  poles.
* 2.5.27 with `κ = 0` (`dlmf_2_5_27_zero`): `𝓜h₂(z)` continues meromorphically with simple poles
  at `βₛ` of principal parts `−bₛ/(z − βₛ)`, by `t ↦ 1/t` from 2.5.25. (`κ ≠ 0`, where `𝓜h₂`
  continues to an entire function, is in `Section5Oscillatory`.)
* 2.5.28 (`dlmf_2_5_28`): `𝓜h(z) := 𝓜h₁(z) + 𝓜h₂(z)`, for any continuation of `𝓜h₂`.
-/

open MeasureTheory Filter Topology Set Complex Asymptotics
open scoped Real

namespace Azurite.DLMF

/-! ### Gluing analytic functions along an exhaustion -/

open Classical in
/-- The function equal to `g N` on `U N`, for an increasing family `U` and compatible `g`. -/
noncomputable def glue (U : ℕ → Set ℂ) (g : ℕ → ℂ → ℂ) (z : ℂ) : ℂ :=
  if h : ∃ N, z ∈ U N then g (Nat.find h) z else 0

section Glue

variable {U : ℕ → Set ℂ} {g : ℕ → ℂ → ℂ} (hU : Monotone U)
  (hg : ∀ N, ∀ z ∈ U N, g (N + 1) z = g N z)
include hU hg

theorem glue_compat {M N : ℕ} (hMN : M ≤ N) {z : ℂ} (hz : z ∈ U M) : g N z = g M z := by
  induction N, hMN using Nat.le_induction with
  | base => rfl
  | succ N hMN ih => rw [hg N z (hU hMN hz), ih]

theorem glue_eq {N : ℕ} {z : ℂ} (hz : z ∈ U N) : glue U g z = g N z := by
  classical
  have h : ∃ N, z ∈ U N := ⟨N, hz⟩
  simp only [glue, h, ↓reduceDIte]
  exact (glue_compat hU hg (Nat.find_min' h hz) (Nat.find_spec h)).symm

theorem differentiableAt_glue (hUo : ∀ N, IsOpen (U N))
    (hd : ∀ N, DifferentiableOn ℂ (g N) (U N)) {N : ℕ} {z : ℂ} (hz : z ∈ U N) :
    DifferentiableAt ℂ (glue U g) z := by
  refine ((hd N).differentiableAt ((hUo N).mem_nhds hz)).congr_of_eventuallyEq ?_
  filter_upwards [(hUo N).mem_nhds hz] with w hw
  exact glue_eq hU hg hw

end Glue

/-! ### 2.5.25 -/

/-- The partial sums `∑_{s<N} aₛ t^{αₛ}` of 2.5.17. -/
noncomputable def expPartial (a α : ℕ → ℂ) (N : ℕ) (t : ℝ) : ℂ :=
  ∑ s ∈ Finset.range N, a s * (t : ℂ) ^ α s

/-- The truncated remainder `(f − ∑_{s<N} aₛ t^{αₛ})₁`. -/
noncomputable def truncRem (f : ℝ → ℂ) (a α : ℕ → ℂ) (N : ℕ) : ℝ → ℂ :=
  trunc₁ fun t => f t - expPartial a α N t

/-- **DLMF 2.5.25**, the explicit continuation of `𝓜f₁` to `ℜz > −ℜα_N`:
`∑_{s<N} aₛ/(z + αₛ) + ∫₀¹ t^{z−1} (f(t) − ∑_{s<N} aₛ t^{αₛ}) dt`. -/
noncomputable def mellinTrunc₁Ext (f : ℝ → ℂ) (a α : ℕ → ℂ) (N : ℕ) (z : ℂ) : ℂ :=
  ∑ s ∈ Finset.range N, a s / (z + α s) + mellin (truncRem f a α N) z

/-- The domain of `mellinTrunc₁Ext f a α N`: `ℜz > −ℜα_N` minus the poles `−αₛ`, `s < N`. -/
def contDomain (α : ℕ → ℂ) (N : ℕ) : Set ℂ :=
  {z | -(α N).re < z.re ∧ ∀ s < N, z ≠ -α s}

/-- **DLMF 2.5.25**, the meromorphic continuation of `𝓜f₁` to `ℂ`. -/
noncomputable def mellinTrunc₁Cont (f : ℝ → ℂ) (a α : ℕ → ℂ) : ℂ → ℂ :=
  glue (contDomain α) (mellinTrunc₁Ext f a α)

section Ext

variable {f : ℝ → ℂ} {a α : ℕ → ℂ}

theorem expPartial_zero (a α : ℕ → ℂ) (t : ℝ) : expPartial a α 0 t = 0 := by
  simp [expPartial]

theorem truncRem_zero (f : ℝ → ℂ) (a α : ℕ → ℂ) : truncRem f a α 0 = trunc₁ f := by
  ext t
  simp [truncRem, expPartial_zero]

theorem mellinTrunc₁Ext_zero (f : ℝ → ℂ) (a α : ℕ → ℂ) (z : ℂ) :
    mellinTrunc₁Ext f a α 0 z = mellin (trunc₁ f) z := by
  simp [mellinTrunc₁Ext, truncRem_zero]

theorem continuousOn_expPartial (a α : ℕ → ℂ) (N : ℕ) :
    ContinuousOn (expPartial a α N) (Ioi 0) :=
  continuousOn_finsetSum _ fun _ _ => continuousOn_const.mul (continuousOn_ofReal_cpow_Ioi _)

theorem locallyIntegrableOn_sub_expPartial (hloc : LocallyIntegrableOn f (Ioi 0)) (N : ℕ) :
    LocallyIntegrableOn (fun t => f t - expPartial a α N t) (Ioi 0) :=
  hloc.sub ((continuousOn_expPartial a α N).locallyIntegrableOn measurableSet_Ioi)

variable (hα : StrictMono fun s => (α s).re)
  (hf : IsGenAsympExpansionDLMF (𝓝[>] (0 : ℝ)) (fun s t => (t : ℂ) ^ α s) f
    fun s t => a s * (t : ℂ) ^ α s)
include hf

/-- The remainder after `N` terms is `O(t^{ℜα_N})` as `t → 0+`. -/
theorem sub_expPartial_isBigO (N : ℕ) :
    (fun t => f t - expPartial a α N t) =O[𝓝[>] 0] (· ^ (α N).re) :=
  isBigO_rpow_re_of_isBigODLMF_cpow_zero (hf.2 N)

theorem mellinConvergent_truncRem (hloc : LocallyIntegrableOn f (Ioi 0)) {N : ℕ} {z : ℂ}
    (hz : -(α N).re < z.re) : MellinConvergent (truncRem f a α N) z :=
  mellinConvergent_trunc₁ (locallyIntegrableOn_sub_expPartial hloc N)
    (sub_expPartial_isBigO hf N) hz

theorem differentiableAt_mellin_truncRem (hloc : LocallyIntegrableOn f (Ioi 0)) {N : ℕ} {z : ℂ}
    (hz : -(α N).re < z.re) : DifferentiableAt ℂ (mellin (truncRem f a α N)) z :=
  differentiableAt_mellin_trunc₁ (locallyIntegrableOn_sub_expPartial hloc N)
    (sub_expPartial_isBigO hf N) hz

include hα in
/-- One step of the continuation: for `ℜz > −ℜα_N`,
`∫₀¹ t^{z−1} r_N(t) dt = a_N/(z + α_N) + ∫₀¹ t^{z−1} r_{N+1}(t) dt`. -/
theorem mellin_truncRem_succ (hloc : LocallyIntegrableOn f (Ioi 0)) {N : ℕ} {z : ℂ}
    (hz : -(α N).re < z.re) :
    mellin (truncRem f a α N) z = a N / (z + α N) + mellin (truncRem f a α (N + 1)) z := by
  have hzN : 0 < z.re + (α N).re := by linarith
  have hpow := hasMellin_cpow_Ioc (α N) hzN
  have hterm : HasMellin ((Ioc 0 1).indicator fun t : ℝ => a N * (t : ℂ) ^ α N) z
      (a N * (1 / (z + α N))) := by
    have h1 : ((Ioc 0 1).indicator fun t : ℝ => a N * (t : ℂ) ^ α N) =
        fun t => a N • (Ioc 0 1).indicator (fun t : ℝ => (t : ℂ) ^ α N) t := by
      ext t
      simp [indicator]
    rw [h1, ← hpow.2]
    exact ⟨hpow.1.const_smul (a N), mellin_const_smul _ _ _⟩
  have hsucc : MellinConvergent (truncRem f a α (N + 1)) z :=
    mellinConvergent_truncRem hf hloc (lt_of_le_of_lt (neg_le_neg (hα (Nat.lt_succ_self N)).le) hz)
  have hsplit : truncRem f a α N = fun t =>
      (Ioc 0 1).indicator (fun t : ℝ => a N * (t : ℂ) ^ α N) t + truncRem f a α (N + 1) t := by
    ext t
    by_cases ht : t ∈ Ioc 0 1
    · simp only [truncRem, trunc₁, expPartial, Finset.sum_range_succ, indicator_of_mem ht]
      ring
    · simp only [truncRem, trunc₁, expPartial, indicator_of_notMem ht, add_zero]
  have := hasMellin_add hterm.1 hsucc
  rw [← hsplit, hterm.2] at this
  rw [this.2, one_div, ← div_eq_mul_inv]

include hα in
theorem mellinTrunc₁Ext_succ (hloc : LocallyIntegrableOn f (Ioi 0)) {N : ℕ} {z : ℂ}
    (hz : -(α N).re < z.re) :
    mellinTrunc₁Ext f a α (N + 1) z = mellinTrunc₁Ext f a α N z := by
  simp only [mellinTrunc₁Ext, Finset.sum_range_succ]
  rw [mellin_truncRem_succ hα hf hloc hz]
  ring

omit hf in
include hα in
theorem contDomain_mono : Monotone (contDomain α) := by
  refine monotone_nat_of_le_succ fun N z hz => ⟨?_, fun s hs => ?_⟩
  · exact lt_of_le_of_lt (neg_le_neg (hα (Nat.lt_succ_self N)).le) hz.1
  · rcases Nat.lt_succ_iff_lt_or_eq.mp hs with h | h
    · exact hz.2 s h
    · subst h
      intro h
      have := congrArg Complex.re h
      simp only [neg_re] at this
      linarith [hz.1]

omit hf in
theorem isOpen_contDomain (α : ℕ → ℂ) (N : ℕ) : IsOpen (contDomain α N) := by
  have h1 : IsOpen {z : ℂ | -(α N).re < z.re} := isOpen_lt continuous_const continuous_re
  have h2 : IsOpen {z : ℂ | ∀ s < N, z ≠ -α s} := by
    have : {z : ℂ | ∀ s < N, z ≠ -α s} = ⋂ s ∈ Finset.range N, {-α s}ᶜ := by
      ext z
      simp
    rw [this]
    exact isOpen_biInter_finset fun _ _ => isOpen_compl_singleton
  exact h1.inter h2

theorem differentiableOn_mellinTrunc₁Ext (hloc : LocallyIntegrableOn f (Ioi 0)) (N : ℕ) :
    DifferentiableOn ℂ (mellinTrunc₁Ext f a α N) (contDomain α N) := by
  intro z hz
  refine DifferentiableAt.differentiableWithinAt (DifferentiableAt.add ?_
    (differentiableAt_mellin_truncRem hf hloc hz.1))
  refine DifferentiableAt.fun_sum fun s hs => (differentiableAt_const _).div
    (differentiableAt_id.add_const _) ?_
  intro h
  exact hz.2 s (Finset.mem_range.mp hs) (eq_neg_of_add_eq_zero_left h)

include hα in
theorem mellinTrunc₁Cont_eq (hloc : LocallyIntegrableOn f (Ioi 0)) {N : ℕ} {z : ℂ}
    (hz : z ∈ contDomain α N) : mellinTrunc₁Cont f a α z = mellinTrunc₁Ext f a α N z :=
  glue_eq (contDomain_mono hα) (fun _ _ hz => mellinTrunc₁Ext_succ hα hf hloc hz.1) hz

include hα in
/-- **DLMF 2.5.25**: `𝓜f₁(z)` can be continued analytically to a meromorphic function on the
whole `z`-plane, with simple poles at `z = −αₛ`, `s = 0, 1, 2, …`, of principal parts
`aₛ/(z + αₛ)`. The continuation is `mellinTrunc₁Cont f a α`: it equals `𝓜f₁` on `ℜz > −ℜα₀`
(Table 2.5.1), is analytic off the poles, and near `−αₛ` differs from `aₛ/(z + αₛ)` by an
analytic function. -/
theorem dlmf_2_5_25 (hloc : LocallyIntegrableOn f (Ioi 0))
    (hα' : Tendsto (fun s => (α s).re) atTop atTop) :
    (∀ z : ℂ, -(α 0).re < z.re → mellinTrunc₁Cont f a α z = mellin (trunc₁ f) z) ∧
      (∀ z : ℂ, (∀ s, z ≠ -α s) → DifferentiableAt ℂ (mellinTrunc₁Cont f a α) z) ∧
      ∀ s, ∃ g : ℂ → ℂ, AnalyticAt ℂ g (-α s) ∧
        ∀ᶠ z in 𝓝[≠] (-α s), mellinTrunc₁Cont f a α z = a s / (z + α s) + g z := by
  refine ⟨fun z hz => ?_, fun z hz => ?_, fun s => ?_⟩
  · rw [mellinTrunc₁Cont_eq hα hf hloc (N := 0) ⟨hz, fun s hs => absurd hs (Nat.not_lt_zero s)⟩,
      mellinTrunc₁Ext_zero]
  · obtain ⟨N, hN⟩ := (hα'.eventually_gt_atTop (-z.re)).exists
    exact differentiableAt_glue (contDomain_mono hα)
      (fun _ _ hz => mellinTrunc₁Ext_succ hα hf hloc hz.1) (isOpen_contDomain α)
      (differentiableOn_mellinTrunc₁Ext hf hloc) (N := N) ⟨by linarith, fun s _ => hz s⟩
  · -- the analytic part near `−αₛ`
    set V : Set ℂ := {w | -(α (s + 1)).re < w.re ∧ ∀ s' < s + 1, s' ≠ s → w ≠ -α s'}
    have hVo : IsOpen V := by
      have h1 : IsOpen {w : ℂ | -(α (s + 1)).re < w.re} := isOpen_lt continuous_const continuous_re
      have h2 : IsOpen {w : ℂ | ∀ s' < s + 1, s' ≠ s → w ≠ -α s'} := by
        have : {w : ℂ | ∀ s' < s + 1, s' ≠ s → w ≠ -α s'} =
            ⋂ s' ∈ (Finset.range (s + 1)).erase s, {-α s'}ᶜ := by
          ext w
          simp only [mem_ofPred_eq, mem_iInter, Finset.mem_erase, Finset.mem_range, mem_compl_iff,
            mem_singleton_iff, and_imp]
          exact ⟨fun h s' h1 h2 => h s' h2 h1, fun h s' h1 h2 => h s' h2 h1⟩
        rw [this]
        exact isOpen_biInter_finset fun _ _ => isOpen_compl_singleton
      exact h1.inter h2
    have hmem : -α s ∈ V := by
      refine ⟨?_, fun s' _ hs' h => hs' ?_⟩
      · simp only [neg_re]
        linarith [hα (Nat.lt_succ_self s)]
      · exact hα.injective (congrArg Complex.re (neg_injective h)).symm
    refine ⟨fun w => ∑ s' ∈ (Finset.range (s + 1)).erase s, a s' / (w + α s') +
      mellin (truncRem f a α (s + 1)) w, ?_, ?_⟩
    · refine DifferentiableOn.analyticAt (fun w hw => DifferentiableAt.differentiableWithinAt
        (DifferentiableAt.add ?_ (differentiableAt_mellin_truncRem hf hloc hw.1)))
        (hVo.mem_nhds hmem)
      refine DifferentiableAt.fun_sum fun s' hs' => (differentiableAt_const _).div
        (differentiableAt_id.add_const _) fun h => ?_
      obtain ⟨hne, hlt⟩ := Finset.mem_erase.mp hs'
      exact hw.2 s' (Finset.mem_range.mp hlt) hne (eq_neg_of_add_eq_zero_left h)
    · have hVn : V ∈ 𝓝[≠] (-α s) := mem_nhdsWithin_of_mem_nhds (hVo.mem_nhds hmem)
      filter_upwards [hVn, self_mem_nhdsWithin] with w hw hw'
      have hwD : w ∈ contDomain α (s + 1) := ⟨hw.1, fun s' hs' => by
        by_cases h : s' = s
        · subst h
          exact hw'
        · exact hw.2 s' hs' h⟩
      rw [mellinTrunc₁Cont_eq hα hf hloc hwD, mellinTrunc₁Ext,
        ← Finset.add_sum_erase _ _ (Finset.mem_range.mpr (Nat.lt_succ_self s)), add_assoc]

end Ext

/-! ### 2.5.26 -/

/-- **DLMF 2.5.26**: the extended `𝓜f(z) := 𝓜f₁(z) + 𝓜f₂(z)`, `ℜz < b`, with `𝓜f₁` continued. -/
noncomputable def mellinExt (f : ℝ → ℂ) (a α : ℕ → ℂ) (z : ℂ) : ℂ :=
  mellinTrunc₁Cont f a α z + mellin (trunc₂ f) z

/-- `𝓜f = 𝓜f₁ + 𝓜f₂` wherever both converge. -/
theorem mellin_eq_trunc_add {f : ℝ → ℂ} {z : ℂ} (h₁ : MellinConvergent (trunc₁ f) z)
    (h₂ : MellinConvergent (trunc₂ f) z) :
    mellin f z = mellin (trunc₁ f) z + mellin (trunc₂ f) z := by
  have := hasMellin_add h₁ h₂
  rw [show (fun t => trunc₁ f t + trunc₂ f t) = f from funext (trunc₁_add_trunc₂ f)] at this
  exact this.2

/-- **DLMF 2.5.26**: for `ℜz < b`, `𝓜f(z) = 𝓜f₁(z) + 𝓜f₂(z)` extends `𝓜f` from its strip of
convergence `−ℜα₀ < ℜz < b` to the half-plane `ℜz < b`, where it is meromorphic with the poles
and principal parts of `𝓜f₁` (2.5.25). -/
theorem dlmf_2_5_26 {f : ℝ → ℂ} {a α : ℕ → ℂ} {b : ℝ} (hloc : LocallyIntegrableOn f (Ioi 0))
    (hα : StrictMono fun s => (α s).re) (hα' : Tendsto (fun s => (α s).re) atTop atTop)
    (hf : IsGenAsympExpansionDLMF (𝓝[>] (0 : ℝ)) (fun s t => (t : ℂ) ^ α s) f
      fun s t => a s * (t : ℂ) ^ α s)
    (hb : f =O[atTop] (· ^ (-b))) :
    (∀ z : ℂ, -(α 0).re < z.re → z.re < b → mellinExt f a α z = mellin f z) ∧
      (∀ z : ℂ, z.re < b → (∀ s, z ≠ -α s) → DifferentiableAt ℂ (mellinExt f a α) z) ∧
      ∀ s, -(α s).re < b → ∃ g : ℂ → ℂ, AnalyticAt ℂ g (-α s) ∧
        ∀ᶠ z in 𝓝[≠] (-α s), mellinExt f a α z = a s / (z + α s) + g z := by
  obtain ⟨h1, h2, h3⟩ := dlmf_2_5_25 hα hf hloc hα'
  refine ⟨fun z hz hzb => ?_, fun z hzb hz => ?_, fun s hs => ?_⟩
  · have h0 := hf.2 0
    simp only [Finset.range_zero, Finset.sum_empty, sub_zero] at h0
    rw [mellinExt, h1 z hz, mellin_eq_trunc_add (mellinConvergent_trunc₁ hloc
      (isBigO_rpow_re_of_isBigODLMF_cpow_zero h0) hz) (mellinConvergent_trunc₂ hloc hb hzb)]
  · exact (h2 z hz).add (differentiableAt_mellin_trunc₂ hloc hb hzb)
  · obtain ⟨g, hg, hgeq⟩ := h3 s
    refine ⟨fun z => g z + mellin (trunc₂ f) z, hg.add ?_, ?_⟩
    · have hdiff : DifferentiableOn ℂ (mellin (trunc₂ f)) {z | z.re < b} := fun z hz =>
        (differentiableAt_mellin_trunc₂ hloc hb hz).differentiableWithinAt
      exact hdiff.analyticAt ((isOpen_lt continuous_re continuous_const).mem_nhds
        (by simpa using hs))
    · filter_upwards [hgeq] with z hz
      rw [mellinExt, hz]
      ring

/-! ### 2.5.27 for `κ = 0`, by inversion -/

section Inversion

/-- `f` and `g` agreeing a.e. on `(0, ∞)` have the same Mellin transform. -/
theorem mellin_congr_ae {f g : ℝ → ℂ} (h : f =ᵐ[volume.restrict (Ioi 0)] g) (s : ℂ) :
    mellin f s = mellin g s :=
  integral_congr_ae (h.mono fun t ht => by simp only [ht])

theorem mellinConvergent_congr_ae {f g : ℝ → ℂ} (h : f =ᵐ[volume.restrict (Ioi 0)] g) (s : ℂ) :
    MellinConvergent f s ↔ MellinConvergent g s :=
  integrable_congr (h.mono fun t ht => by simp only [ht])

/-- Off `t = 1`, `h₂(t) = h₁'(1/t)` where `h₁'` is the truncation of `h(1/t)`. -/
theorem trunc₂_eq_trunc₁_inv (h : ℝ → ℂ) {t : ℝ} (ht : 0 < t) (ht1 : t ≠ 1) :
    trunc₂ h t = trunc₁ (fun u => h u⁻¹) t⁻¹ := by
  rcases lt_or_gt_of_ne ht1 with h1 | h1
  · rw [trunc₂_apply_of_mem ht h1.le, trunc₁_apply_of_one_lt (one_lt_inv_iff₀.mpr ⟨ht, h1⟩)]
  · rw [trunc₂_apply_of_one_lt h1, trunc₁_apply_of_mem (inv_pos.mpr ht)
      (inv_le_one_of_one_le₀ h1.le), inv_inv]

theorem trunc₂_ae_eq_trunc₁_inv (h : ℝ → ℂ) :
    trunc₂ h =ᵐ[volume.restrict (Ioi 0)] fun t => trunc₁ (fun u => h u⁻¹) t⁻¹ := by
  have h1 : ∀ᵐ t : ℝ ∂volume, t ≠ 1 := by
    rw [ae_iff]
    simp
  filter_upwards [ae_restrict_of_ae h1, ae_restrict_mem measurableSet_Ioi] with t ht ht'
  exact trunc₂_eq_trunc₁_inv h ht' ht

/-- Local integrability on `(0, ∞)` is preserved by `t ↦ 1/t`. -/
theorem locallyIntegrableOn_comp_inv {h : ℝ → ℂ} (hloc : LocallyIntegrableOn h (Ioi 0)) :
    LocallyIntegrableOn (fun t => h t⁻¹) (Ioi 0) := by
  intro x hx
  have hx : (0 : ℝ) < x := hx
  refine ⟨Icc (x / 2) (2 * x),
    mem_nhdsWithin_of_mem_nhds (Icc_mem_nhds (by linarith) (by linarith)), ?_⟩
  have hKpos : ∀ u ∈ Icc (2 * x)⁻¹ (x / 2)⁻¹, 0 < u := fun u hu =>
    lt_of_lt_of_le (by positivity) hu.1
  have hint : IntegrableOn h (Icc (2 * x)⁻¹ (x / 2)⁻¹) :=
    hloc.integrableOn_compact_subset (fun u hu => hKpos u hu) isCompact_Icc
  have himg : Inv.inv '' Icc (2 * x)⁻¹ (x / 2)⁻¹ = Icc (x / 2) (2 * x) := by
    ext t
    constructor
    · rintro ⟨u, ⟨hu1, hu2⟩, rfl⟩
      have hu : 0 < u := hKpos u ⟨hu1, hu2⟩
      exact ⟨by simpa using inv_anti₀ hu hu2, by simpa using inv_anti₀ (by positivity) hu1⟩
    · intro ht
      have ht0 : 0 < t := lt_of_lt_of_le (by positivity) ht.1
      exact ⟨t⁻¹, ⟨inv_anti₀ ht0 ht.2, inv_anti₀ (by positivity) ht.1⟩, inv_inv t⟩
  rw [← himg, integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Icc
    (f' := fun u => -(u ^ 2)⁻¹) (fun u hu => (hasDerivAt_inv (hKpos u hu).ne').hasDerivWithinAt)
    inv_injective.injOn]
  have hcont : ContinuousOn (fun u : ℝ => |(-(u ^ 2)⁻¹)|) (Icc (2 * x)⁻¹ (x / 2)⁻¹) :=
    ((continuousOn_pow 2).inv₀ fun u hu => pow_ne_zero 2 (hKpos u hu).ne').neg.abs
  refine (hint.continuousOn_smul hcont isCompact_Icc).congr_fun (fun u _ => ?_)
    measurableSet_Icc
  simp

/-- `𝓜h₂(z) = 𝓜(h(1/·))₁(−z)`. -/
theorem mellin_trunc₂_eq_inv (h : ℝ → ℂ) (z : ℂ) :
    mellin (trunc₂ h) z = mellin (trunc₁ fun u => h u⁻¹) (-z) := by
  rw [mellin_congr_ae (trunc₂_ae_eq_trunc₁_inv h), mellin_comp_inv]

/-- `(1/t)^{−β} = t^β` for `t > 0`. -/
theorem ofReal_inv_cpow_neg {t : ℝ} (ht : 0 < t) (β : ℂ) :
    ((t⁻¹ : ℝ) : ℂ) ^ (-β) = (t : ℂ) ^ β := by
  rw [ofReal_inv, cpow_neg, inv_cpow _ _ (by rw [arg_ofReal_of_nonneg ht.le]; exact
    Real.pi_pos.ne), inv_inv]

/-- The expansion 2.5.18 with `κ = 0`, transported by `t ↦ 1/t` to an expansion at `0+`. -/
theorem isGenAsympExpansion_inv {h : ℝ → ℂ} {bs β : ℕ → ℂ}
    (hh : IsGenAsympExpansionDLMF atTop (fun (s : ℕ) (t : ℝ) => (t : ℂ) ^ (-β s)) h
      fun s t => bs s * (t : ℂ) ^ (-β s)) :
    IsGenAsympExpansionDLMF (𝓝[>] (0 : ℝ)) (fun s t => (t : ℂ) ^ β s) (fun t => h t⁻¹)
      fun s t => bs s * (t : ℂ) ^ β s := by
  have hinv : Tendsto (fun t : ℝ => t⁻¹) (𝓝[>] 0) atTop := tendsto_inv_nhdsGT_zero
  have hpow : ∀ s, ∀ᶠ t : ℝ in 𝓝[>] 0, ((t⁻¹ : ℝ) : ℂ) ^ (-β s) = (t : ℂ) ^ β s := fun s => by
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact ofReal_inv_cpow_neg ht _
  refine ⟨fun s => ?_, fun n => ?_⟩
  · -- the scale
    have := (hh.1 s).comp hinv
    refine this.congr' ?_
    filter_upwards [hpow s, hpow (s + 1)] with t h1 h2
    simp only [Function.comp, h1, h2]
  · obtain ⟨C, hC⟩ := hh.2 n
    refine ⟨C, eventually_map.mpr ?_⟩
    have := hinv.eventually (eventually_map.mp hC)
    filter_upwards [this, hpow n, self_mem_nhdsWithin] with t ht h1 ht'
    have hsum : ∑ s ∈ Finset.range n, bs s * ((t⁻¹ : ℝ) : ℂ) ^ (-β s) =
        ∑ s ∈ Finset.range n, bs s * (t : ℂ) ^ β s :=
      Finset.sum_congr rfl fun s _ => by rw [ofReal_inv_cpow_neg ht' _]
    simpa only [hsum, h1] using ht

/-- **DLMF 2.5.27** for `κ = 0`: `𝓜h₂(z)` can be continued analytically to a meromorphic
function on the whole `z`-plane with simple poles at `z = βₛ` of principal parts
`−bₛ/(z − βₛ)`. The continuation is `z ↦ mellinTrunc₁Cont (h(1/·)) b β (−z)`. -/
theorem dlmf_2_5_27_zero {h : ℝ → ℂ} {bs β : ℕ → ℂ} (hloc : LocallyIntegrableOn h (Ioi 0))
    (hβ : StrictMono fun s => (β s).re) (hβ' : Tendsto (fun s => (β s).re) atTop atTop)
    (hh : IsGenAsympExpansionDLMF atTop (fun (s : ℕ) (t : ℝ) => (t : ℂ) ^ (-β s)) h
      fun s t => bs s * (t : ℂ) ^ (-β s)) :
    ∃ G : ℂ → ℂ, (∀ z : ℂ, z.re < (β 0).re → G z = mellin (trunc₂ h) z) ∧
      (∀ z : ℂ, (∀ s, z ≠ β s) → DifferentiableAt ℂ G z) ∧
      ∀ s, ∃ g : ℂ → ℂ, AnalyticAt ℂ g (β s) ∧
        ∀ᶠ z in 𝓝[≠] (β s), G z = -bs s / (z - β s) + g z := by
  have hloc' := locallyIntegrableOn_comp_inv hloc
  obtain ⟨h1, h2, h3⟩ := dlmf_2_5_25 hβ (isGenAsympExpansion_inv hh) hloc' hβ'
  refine ⟨fun z => mellinTrunc₁Cont (fun t => h t⁻¹) bs β (-z), fun z hz => ?_, fun z hz => ?_,
    fun s => ?_⟩
  · dsimp only
    rw [h1 (-z) (by simpa using hz), mellin_trunc₂_eq_inv]
  · exact (h2 (-z) fun s hs => hz s (neg_injective hs)).comp z differentiableAt_id.neg
  · obtain ⟨g, hg, hgeq⟩ := h3 s
    refine ⟨fun z => g (-z), AnalyticAt.comp_of_eq hg analyticAt_id.neg (by simp), ?_⟩
    have hneg : Tendsto (fun z : ℂ => -z) (𝓝[≠] (β s)) (𝓝[≠] (-β s)) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
        ((continuous_neg.tendsto _).mono_left nhdsWithin_le_nhds) ?_
      filter_upwards [self_mem_nhdsWithin] with z hz
      exact fun h => hz (neg_injective h)
    filter_upwards [hneg.eventually hgeq] with z hz
    rw [hz, neg_div, ← div_neg, neg_sub, neg_add_eq_sub]

end Inversion

/-! ### 2.5.28 -/

/-- **DLMF 2.5.28**: `𝓜h(z) := 𝓜h₁(z) + 𝓜h₂(z)`, with `𝓜h₂` continued by any `G`
(2.5.27): it agrees with `𝓜h` on the strip `−c < ℜz < ℜβ₀` and is analytic at every
`z` with `ℜz > −c` where `G` is. -/
theorem dlmf_2_5_28 {h : ℝ → ℂ} {β₀ c : ℝ} (hloc : LocallyIntegrableOn h (Ioi 0))
    (hzero : h =O[𝓝[>] 0] (· ^ c)) (htop : h =O[atTop] (· ^ (-β₀))) {G : ℂ → ℂ}
    (hG : ∀ z : ℂ, z.re < β₀ → G z = mellin (trunc₂ h) z) :
    (∀ z : ℂ, -c < z.re → z.re < β₀ → mellin (trunc₁ h) z + G z = mellin h z) ∧
      ∀ z : ℂ, -c < z.re → DifferentiableAt ℂ G z →
        DifferentiableAt ℂ (fun z => mellin (trunc₁ h) z + G z) z :=
  ⟨fun z h₁ h₂ => by
    rw [hG z h₂, mellin_eq_trunc_add (mellinConvergent_trunc₁ hloc hzero h₁)
      (mellinConvergent_trunc₂ hloc htop h₂)],
    fun z h₁ hGd => (differentiableAt_mellin_trunc₁ hloc hzero h₁).add hGd⟩

end Azurite.DLMF
