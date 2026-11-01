/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/


import Azurite.DLMF.Chapter2.Section4CoalescingIFT

/-!
# The theorem of Chester, Friedman and Ursell

`p(α, t)` analytic in `t` on a disc around `t̂` and continuous in `(α, t)` (the hypotheses of
DLMF §2.4(v)), with `∂ₜp = ∂ₜ²p = 0 ≠ ∂ₜ³p` at `(α̂, t̂)`: two saddle points coalesce at `t̂` for
`α = α̂`. Then on a fixed disc `|t − t̂| < ρ` and for all `α` near `α̂` there is a change of
variable `w = w(α, t)` of the form 2.4.18 (with `a = 0`),
`p(α, t) = ⅓w³ + b(α) w + c(α)`, analytic in `t`, one-to-one with `∂ₜw ≠ 0`, continuous in
`(α, t)`, with `b`, `c` continuous and `b(α̂) = 0`, `w(α̂, t̂) = 0` (`chester_friedman_ursell`).

**Proof.** With the prepared form `p(α̂, s) = p(α̂, t̂) + (s − t̂)³V(α̂, s)`, the analytic
coordinate `u(s) = (s − t̂)(3V(α̂, s))^{1/3}` has `p(α̂, ·) − p(α̂, t̂) = ⅓u³`. In the variable
`W = u(s)` the family `g_α(W) = p(α, u⁻¹(W)) − p(α, t̂)` lies in the disc algebra, depends
continuously on `α`, and `g_α̂ = ⅓W³`. The inverse function theorem for
`Φ(b, c, h) = ⅓(W + h)³ + b(W + h) + c` (`cfuPH`) gives `(b, c, h)(α)` continuous with
`Φ(b, c, h) = g_α`; then `w(α, s) = u(s) + h_α(u(s))`.
-/

open Set Filter Topology Complex Metric

namespace Azurite.DLMF

variable {ι : Type*} [TopologicalSpace ι]

section Setup

variable {p : ι → ℂ → ℂ} {t₀ : ℂ} {R : ℝ} {α₀ : ι}

omit [TopologicalSpace ι] in
/-- At `α₀`: `p(α₀, s) = p(α₀, t₀) + (s − t₀)³ V(α₀, s)`. -/
theorem cfu_prep_at (hR : 0 < R) (hp : ∀ α, DifferentiableOn ℂ (p α) (ball t₀ R))
    (h1 : deriv (p α₀) t₀ = 0) (h2 : iteratedDeriv 2 (p α₀) t₀ = 0) (s : ℂ) :
    p α₀ s = p α₀ t₀ + (s - t₀) ^ 3 * cfuV p t₀ α₀ s := by
  have := cfu_prep p t₀ α₀ s
  rw [show cfuEps₁ p t₀ α₀ = 0 from h1,
    cfuEps₂_eq ((hp α₀).analyticAt (isOpen_ball.mem_nhds (mem_ball_self hR))), h2] at this
  simpa using this

omit [TopologicalSpace ι] in
/-- The coordinate at the confluence: `UnifSetup` for `3V(α₀, ·)`, `μ = 3`. -/
theorem cfu_unifSetup (hR : 0 < R) (hp : ∀ α, DifferentiableOn ℂ (p α) (ball t₀ R))
    (h3 : iteratedDeriv 3 (p α₀) t₀ ≠ 0) :
    UnifSetup t₀ (arg (3 * cfuV p t₀ α₀ t₀)) 3 R (fun s => 3 * cfuV p t₀ α₀ s) where
  μ_pos := by norm_num
  ρ_pos := hR
  differentiableOn := (differentiableOn_cfuV hR hp α₀).const_mul 3
  P_a := (Complex.norm_mul_exp_arg_mul_I _).symm
  P_ne := by
    rw [cfuV_self ((hp α₀).analyticAt (isOpen_ball.mem_nhds (mem_ball_self hR)))]
    exact mul_ne_zero three_ne_zero (div_ne_zero h3 (by norm_num))

end Setup

/-- A radius on which the inverse `S = unifInv` is analytic, maps into a given ball around `a`,
and is a right inverse of `unif`. -/
theorem UnifSetup.exists_inv_radius {a : ℂ} {φ₀ μ ρ : ℝ} {P : ℂ → ℂ} (h : UnifSetup a φ₀ μ ρ P)
    {r₁ : ℝ} (hr₁ : 0 < r₁) :
    ∃ r > 0, (∀ W ∈ closedBall (0 : ℂ) r,
        unifInv h W ∈ ball a r₁ ∧ unif a φ₀ μ P (unifInv h W) = W) ∧
      DifferentiableOn ℂ (unifInv h) (ball 0 (2 * r)) := by
  have h1 : ∀ᶠ W in 𝓝 (0 : ℂ), unifInv h W ∈ ball a r₁ :=
    h.tendsto_unifInv.eventually (ball_mem_nhds a hr₁)
  have h2 := h.eventually_unif_unifInv
  have h3 := h.analyticAt_unifInv.eventually_analyticAt
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp ((h1.and h2).and h3)
  refine ⟨δ / 3, by positivity, fun W hW => ?_, fun W hW => ?_⟩
  · have : dist W 0 < δ := by
      have := mem_closedBall.mp hW
      linarith
    exact (hball this).1
  · have : dist W 0 < δ := by
      have := mem_ball.mp hW
      linarith
    exact (hball this).2.differentiableAt.differentiableWithinAt

/-- **The theorem of Chester, Friedman and Ursell** (DLMF §2.4(v), the existence of the change
of variable 2.4.18 uniformly near the confluence). Let `p(α, t)` be analytic in `t` on
`|t − t₀| < R` for each `α` and continuous in `(α, t)`, with `∂ₜp = ∂ₜ²p = 0 ≠ ∂ₜ³p` at
`(α₀, t₀)`. Then there are a neighbourhood `N` of `α₀`, a radius `ρ > 0`, continuous `b`, `c` on
`N` and `w(α, t)`, continuous in `(α, t)`, such that for every `α ∈ N`, `w(α, ·)` is an analytic
change of variable on `|t − t₀| < ρ` with `p(α, t) = ⅓w³ + b(α)w + c(α)`; moreover `b(α₀) = 0`
and `w(α₀, t₀) = 0` (the two saddle points `±√(−b(α))` coalesce at `α₀`). -/
theorem chester_friedman_ursell {p : ι → ℂ → ℂ} {t₀ : ℂ} {R : ℝ} (hR : 0 < R)
    (hp : ∀ α, DifferentiableOn ℂ (p α) (ball t₀ R))
    (hcont : ContinuousOn (fun q : ι × ℂ => p q.1 q.2) (univ ×ˢ ball t₀ R)) {α₀ : ι}
    (h1 : deriv (p α₀) t₀ = 0) (h2 : iteratedDeriv 2 (p α₀) t₀ = 0)
    (h3 : iteratedDeriv 3 (p α₀) t₀ ≠ 0) :
    ∃ N ∈ 𝓝 α₀, ∃ ρ > 0, ∃ (b c : ι → ℂ) (w : ι → ℂ → ℂ),
      ContinuousOn b N ∧ ContinuousOn c N ∧
      ContinuousOn (fun q : ι × ℂ => w q.1 q.2) (N ×ˢ ball t₀ ρ) ∧
      (∀ α ∈ N, CFUTransform (p α) (ball t₀ ρ) (w α) 0 (b α) (c α)) ∧
      b α₀ = 0 ∧ w α₀ t₀ = 0 := by
  -- Step A: the coordinate `u` at the confluence
  have hU := cfu_unifSetup hR hp h3
  set φ₀ := arg (3 * cfuV p t₀ α₀ t₀) with hφ₀
  set u := unif t₀ φ₀ 3 (fun s => 3 * cfuV p t₀ α₀ s) with hu
  set S := unifInv hU with hS
  obtain ⟨N₀, hN₀, r₀, hr₀, hr₀R, hVne⟩ := exists_cfuV_ne_zero hR hp hcont h3
  have hcube : ∀ s ∈ ball t₀ r₀, p α₀ s - p α₀ t₀ = u s ^ 3 / 3 := fun s hs => by
    have hP : (fun s => 3 * cfuV p t₀ α₀ s) s ≠ 0 :=
      mul_ne_zero (three_ne_zero : (3 : ℂ) ≠ 0) (hVne α₀ (mem_of_mem_nhds hN₀) s hs)
    rw [hu, unif_three_cube t₀ φ₀ (P := fun s => 3 * cfuV p t₀ α₀ s) hP, cfu_prep_at hR hp h1 h2 s]
    ring
  -- Step B: the radius `r` for the inverse `S` and the family `g`
  obtain ⟨r, hr, hSprop, hSd⟩ := hU.exists_inv_radius hr₀
  rw [← hS] at hSd
  simp only [← hS, ← hu] at hSprop
  have hSd' : DifferentiableOn ℂ S (ball 0 r) := hSd.mono (ball_subset_ball (by linarith))
  have hScont : ContinuousOn S (closedBall 0 r) :=
    (hSd.mono (closedBall_subset_ball (by linarith))).continuousOn
  have hSmem : ∀ W ∈ closedBall (0 : ℂ) r, S W ∈ ball t₀ R := fun W hW =>
    ball_subset_ball hr₀R (hSprop W hW).1
  set G : ι → ℂ → ℂ := fun α W => p α (S W) - p α t₀ with hG
  have hGd : ∀ α, DifferentiableOn ℂ (G α) (ball 0 r) := fun α =>
    ((hp α).comp hSd' fun W hW => hSmem W (ball_subset_closedBall hW)).sub_const _
  have hGc : ∀ α, ContinuousOn (G α) (closedBall 0 r) := fun α =>
    ((hp α).continuousOn.comp hScont hSmem).sub continuousOn_const
  set g : ι → discAlg r := fun α => discMk (G α) (hGc α) (hGd α) with hg
  have hg0 : g α₀ = cfuΦ r 0 := discAlg_ext fun W hW => by
    rw [discExt_discMk _ _ hW, discExt_cfuΦ _ hW]
    simp only [hG, Prod.snd_zero, Prod.fst_zero, discExt_zero r hW, add_zero, zero_mul]
    rw [hcube (S W) (hSprop W hW).1, (hSprop W hW).2]
    ring
  have hgc : Continuous g := by
    have hGjoint : Continuous fun q : ι × closedBall (0 : ℂ) r => G q.1 q.2 := by
      have e1 : Continuous fun q : ι × closedBall (0 : ℂ) r => p q.1 (S q.2) :=
        hcont.comp_continuous (f := fun q : ι × closedBall (0 : ℂ) r => (q.1, S q.2))
          (continuous_fst.prodMk
            (hScont.comp_continuous (continuous_subtype_val.comp continuous_snd) fun q => q.2.2))
          fun q => ⟨trivial, hSmem _ q.2.2⟩
      have e2 : Continuous fun q : ι × closedBall (0 : ℂ) r => p q.1 t₀ :=
        hcont.comp_continuous (f := fun q : ι × closedBall (0 : ℂ) r => (q.1, t₀))
          (continuous_fst.prodMk continuous_const) fun q => ⟨trivial, mem_ball_self hR⟩
      exact e1.sub e2
    have : Continuous fun α => (g α : C(closedBall (0 : ℂ) r, ℂ)) :=
      ContinuousMap.continuous_of_continuous_uncurry _ hGjoint
    exact continuous_induced_rng.2 this
  -- Step C: the inverse `(b, c, h)(α)`
  have hT : IsOpen (cfuPH hr).target := isOpen_cfuPH_target hr
  have hg0T : g α₀ ∈ (cfuPH hr).target := by
    rw [hg0]
    exact cfuΦ_zero_mem_cfuPH_target hr
  set N₁ := g ⁻¹' (cfuPH hr).target with hN₁def
  have hN₁ : N₁ ∈ 𝓝 α₀ := hgc.continuousAt.preimage_mem_nhds (hT.mem_nhds hg0T)
  set bch : ι → ℂ × ℂ × discAlg r := fun α => (cfuPH hr).symm (g α) with hbchdef
  have hbch : ContinuousOn bch N₁ :=
    (continuousOn_cfuPH_symm hr).comp hgc.continuousOn fun α hα => hα
  have hΦ : ∀ α ∈ N₁, cfuΦ r (bch α) = g α := fun α hα => cfuΦ_cfuPH_symm hr hα
  have hbch0 : bch α₀ = 0 := by
    simp only [hbchdef, hg0]
    exact cfuPH_symm_zero hr
  -- Step D: the neighbourhood on which `h` is small
  set r₂ := r / 2 with hr₂def
  have hr₂ : r₂ < r := by
    rw [hr₂def]
    linarith
  have hsmall_ev : ∀ᶠ α in 𝓝 α₀, ‖(bch α).2.2‖ < (r - r₂) / 2 := by
    have hc : ContinuousAt (fun α => (bch α).2.2) α₀ := (hbch.continuousAt hN₁).snd.snd
    have h0 : ‖(bch α₀).2.2‖ < (r - r₂) / 2 := by
      rw [hbch0]
      simp only [Prod.snd_zero, norm_zero]
      linarith
    exact hc.eventually ((isOpen_lt continuous_norm continuous_const).mem_nhds h0)
  set N := N₁ ∩ {α | ‖(bch α).2.2‖ < (r - r₂) / 2} with hNdef
  have hN : N ∈ 𝓝 α₀ := inter_mem hN₁ hsmall_ev
  -- Step E: the radius `ρ` in the `t`-plane
  have hu_an : AnalyticAt ℂ u t₀ := hU.analyticAt_unif_a
  have hu_d : deriv u t₀ ≠ 0 := hU.deriv_unif_a_ne
  obtain ⟨ρ₁, hρ₁, huinj, hud⟩ := exists_ball_injOn_of_analyticAt hu_an hu_d
  have hu0 : u t₀ = 0 := UnifSetup.unif_a _ _ _ _
  have hev : ∀ᶠ s in 𝓝 t₀, u s ∈ ball 0 r₂ ∧ S (u s) = s := by
    have e1 : ∀ᶠ s in 𝓝 t₀, u s ∈ ball 0 r₂ := by
      have := hu_an.continuousAt.tendsto
      rw [hu0] at this
      exact this.eventually (ball_mem_nhds 0 (by positivity))
    exact e1.and hU.eventually_unifInv_unif
  obtain ⟨ρ₂, hρ₂, hρball⟩ := Metric.eventually_nhds_iff.mp hev
  have hρ : 0 < min ρ₁ ρ₂ := lt_min hρ₁ hρ₂
  have hρ₁' : ball t₀ (min ρ₁ ρ₂) ⊆ ball t₀ ρ₁ := ball_subset_ball (min_le_left _ _)
  have hρ₂' : ∀ s ∈ ball t₀ (min ρ₁ ρ₂), u s ∈ ball 0 r₂ ∧ S (u s) = s := fun s hs =>
    hρball (lt_of_lt_of_le (mem_ball.mp hs) (min_le_right _ _))
  have hucl : ∀ s ∈ ball t₀ (min ρ₁ ρ₂), u s ∈ closedBall (0 : ℂ) r := fun s hs =>
    ball_subset_closedBall (ball_subset_ball hr₂.le (hρ₂' s hs).1)
  -- the change of variable
  set w : ι → ℂ → ℂ := fun α s =>
    u s + discExt r ((bch α).2.2 : C(closedBall (0 : ℂ) r, ℂ)) (u s) with hwdef
  have hpt : ContinuousOn (fun α => p α t₀) N :=
    hcont.comp (continuousOn_id.prodMk continuousOn_const) fun α _ => ⟨trivial, mem_ball_self hR⟩
  refine ⟨N, hN, min ρ₁ ρ₂, hρ, fun α => (bch α).1, fun α => (bch α).2.1 + p α t₀, w,
    (hbch.mono inter_subset_left).fst, ((hbch.mono inter_subset_left).snd.fst).add hpt, ?_,
    fun α hα => ?_, ?_, ?_⟩
  · rw [continuousOn_iff_continuous_domRestrict]
    have hu_c : ContinuousOn u (ball t₀ (min ρ₁ ρ₂)) := fun s hs =>
      (hud s (hρ₁' hs)).2.continuousAt.continuousWithinAt
    have c1 : Continuous fun q : N ×ˢ ball t₀ (min ρ₁ ρ₂) => u (q : ι × ℂ).2 :=
      hu_c.comp_continuous (continuous_snd.comp continuous_subtype_val) fun q => q.2.2
    have c2 : Continuous fun q : N ×ˢ ball t₀ (min ρ₁ ρ₂) =>
        ((bch (q : ι × ℂ).1).2.2 : C(closedBall (0 : ℂ) r, ℂ)) := by
      have : ContinuousOn (fun α => ((bch α).2.2 : C(closedBall (0 : ℂ) r, ℂ))) N :=
        continuous_subtype_val.comp_continuousOn (hbch.mono inter_subset_left).snd.snd
      exact this.comp_continuous (continuous_fst.comp continuous_subtype_val) fun q => q.2.1
    have c3 : Continuous fun q : N ×ˢ ball t₀ (min ρ₁ ρ₂) =>
        (⟨u (q : ι × ℂ).2, hucl _ q.2.2⟩ : closedBall (0 : ℂ) r) :=
      c1.subtype_mk _
    have c4 : Continuous fun q : N ×ˢ ball t₀ (min ρ₁ ρ₂) =>
        ((bch (q : ι × ℂ).1).2.2 : C(closedBall (0 : ℂ) r, ℂ)) ⟨u (q : ι × ℂ).2, hucl _ q.2.2⟩ :=
      ContinuousEval.continuous_eval.comp (c2.prodMk c3)
    refine (c1.add c4).congr fun q => ?_
    simp only [hwdef, Set.domRestrict_apply]
    rw [discExt_apply r _ (hucl _ q.2.2)]
    rfl
  · obtain ⟨hα₁, hαs⟩ := hα
    set H := discExt r ((bch α).2.2 : C(closedBall (0 : ℂ) r, ℂ)) with hH
    obtain ⟨hinj, hder⟩ := injOn_add_discExt (bch α).2.2 hr₂ hαs
    have hHd : ∀ s ∈ ball t₀ (min ρ₁ ρ₂), DifferentiableAt ℂ H (u s) := fun s hs =>
      (differentiableOn_discExt r _).differentiableAt
        (isOpen_ball.mem_nhds (ball_subset_ball hr₂.le (hρ₂' s hs).1))
    have hwd : ∀ s ∈ ball t₀ (min ρ₁ ρ₂),
        HasDerivAt (w α) (deriv (fun W => W + H W) (u s) * deriv u s) s := fun s hs =>
      ((differentiableAt_id.add (hHd s hs)).hasDerivAt).comp s
        (hud s (hρ₁' hs)).2.differentiableAt.hasDerivAt
    exact
      { U_open := isOpen_ball
        w_diff := fun s hs => (hwd s hs).differentiableAt.differentiableWithinAt
        w_inj := fun s₁ hs₁ s₂ hs₂ heq =>
          (huinj.mono hρ₁') hs₁ hs₂ (hinj (hρ₂' s₁ hs₁).1 (hρ₂' s₂ hs₂).1 heq)
        deriv_ne := fun s hs => by
          rw [(hwd s hs).deriv]
          exact mul_ne_zero (hder (u s) (hρ₂' s hs).1) (hud s (hρ₁' hs)).1
        p_eq := fun s hs => by
          have e := congrArg (fun F : discAlg r =>
            discExt r (F : C(closedBall (0 : ℂ) r, ℂ)) (u s)) (hΦ α hα₁)
          rw [discExt_cfuΦ _ (hucl s hs), discExt_discMk _ _ (hucl s hs)] at e
          have e' : (1 / 3 : ℂ) * (u s + H (u s)) ^ 3 + (bch α).1 * (u s + H (u s)) +
              (bch α).2.1 = p α s - p α t₀ := by
            rw [e]
            show p α (S (u s)) - p α t₀ = p α s - p α t₀
            rw [(hρ₂' s hs).2]
          simp only [hwdef, cfuCubic]
          linear_combination -e' }
  · show (bch α₀).1 = 0
    rw [hbch0]
    rfl
  · show u t₀ + discExt r ((bch α₀).2.2 : C(closedBall (0 : ℂ) r, ℂ)) (u t₀) = 0
    rw [hbch0, hu0]
    simp only [Prod.snd_zero]
    rw [discExt_zero r (mem_closedBall_self hr.le), add_zero]

end Azurite.DLMF
