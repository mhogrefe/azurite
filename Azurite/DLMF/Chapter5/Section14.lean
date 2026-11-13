/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter5.Section12

/-!
# DLMF §5.14: Multidimensional integrals — Dirichlet's integrals

Formalization of <https://dlmf.nist.gov/5.14>, equations 5.14.1–5.14.3.

`Vₙ = {t : tₖ ≥ 0, t₁ + ⋯ + tₙ ≤ 1}` (`simplexDLMF`). Dirichlet's integral
`∫_{Vₙ} (1 − ∑tₖ)^{w−1} ∏ tₖ^{zₖ−1} dt = Γ(z₁)⋯Γ(zₙ)Γ(w)/Γ(z₁ + ⋯ + zₙ + w)`
(`dirichlet_integral`) is proved by induction on `n`: peel off `t₀ = x`
(`volume_preserving_piFinSuccAbove`), rescale the remaining coordinates by `1 − x`
(`integral_comp_smul`), which gives `x^{z₀−1}(1 − x)^{z₁+⋯+zₙ+w−1}` times the `(n − 1)`-dimensional
integral, and finish with Euler's beta integral (5.12.1). 5.14.2 is this with `w = zₙ₊₁`, and
5.14.1 is the case `w = 1`.
-/

open Complex Filter Topology Set MeasureTheory
open scoped Real

namespace Azurite.DLMF

/-- The simplex `Vₙ = {t : tₖ ≥ 0, ∑ tₖ ≤ 1}`. -/
def simplexDLMF (n : ℕ) : Set (Fin n → ℝ) := {t | (∀ k, 0 ≤ t k) ∧ ∑ k, t k ≤ 1}

theorem measurableSet_simplexDLMF (n : ℕ) : MeasurableSet (simplexDLMF n) := by
  have he : simplexDLMF n = (⋂ k, {t : Fin n → ℝ | 0 ≤ t k}) ∩ {t | ∑ k, t k ≤ 1} := by
    ext t; simp [simplexDLMF]
  have h : IsClosed (simplexDLMF n) := by
    rw [he]
    exact (isClosed_iInter fun k => isClosed_le continuous_const (continuous_apply k)).inter
      (isClosed_le (continuous_finsetSum _ fun k _ => continuous_apply k) continuous_const)
  exact h.measurableSet

/-- Dirichlet's integrand `∏ tₖ^{zₖ−1} (1 − ∑ tₖ)^{w−1}`. -/
noncomputable def dirichletF (n : ℕ) (z : Fin n → ℂ) (w : ℂ) (t : Fin n → ℝ) : ℂ :=
  (∏ k, (t k : ℂ) ^ (z k - 1)) * ((1 - ∑ k, t k : ℝ) : ℂ) ^ (w - 1)

/-- The integrand extended by zero off the simplex. -/
noncomputable def dirichletG (n : ℕ) (z : Fin n → ℂ) (w : ℂ) : (Fin n → ℝ) → ℂ :=
  (simplexDLMF n).indicator (dirichletF n z w)

theorem measurable_dirichletG (n : ℕ) (z : Fin n → ℂ) (w : ℂ) :
    Measurable (dirichletG n z w) := by
  refine Measurable.indicator ?_ (measurableSet_simplexDLMF n)
  unfold dirichletF
  fun_prop

/-- `∏ R^{aₖ} = R^{∑ aₖ}` for `R > 0`. -/
theorem prod_ofReal_cpow {R : ℝ} (hR : 0 < R) {n : ℕ} (a : Fin n → ℂ) :
    ∏ k, (R : ℂ) ^ a k = (R : ℂ) ^ ∑ k, a k := by
  have hR0 : (R : ℂ) ≠ 0 := ofReal_ne_zero.mpr hR.ne'
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Fin.prod_univ_succ, Fin.sum_univ_succ, cpow_add _ _ hR0, ih]

/-- **The scaling step**: for `0 < x < 1`, `R = 1 − x`,
`G_{n+1}(x, R s) = x^{z₀−1} R^{∑z' + w − 1 − n} Gₙ(s)`. -/
theorem dirichletG_cons_smul {n : ℕ} (z : Fin (n + 1) → ℂ) (w : ℂ) {x : ℝ} (hx0 : 0 < x)
    (hx1 : x < 1) (s : Fin n → ℝ) :
    dirichletG (n + 1) z w (Fin.cons x ((1 - x) • s)) =
      (x : ℂ) ^ (z 0 - 1) * ((1 - x : ℝ) : ℂ) ^ (∑ k : Fin n, z k.succ + w - 1 - n) *
        dirichletG n (fun k => z k.succ) w s := by
  set R := 1 - x
  have hR : 0 < R := by simp only [R]; linarith
  have hmem : Fin.cons x (R • s) ∈ simplexDLMF (n + 1) ↔ s ∈ simplexDLMF n := by
    simp only [simplexDLMF, Set.mem_ofPred_eq, Fin.forall_fin_succ, Fin.cons_zero, Fin.cons_succ,
      Fin.sum_univ_succ, Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum]
    constructor
    · rintro ⟨⟨-, h1⟩, h2⟩
      refine ⟨fun k => nonneg_of_mul_nonneg_right (h1 k) hR, ?_⟩
      simp only [R] at h2 ⊢; nlinarith
    · rintro ⟨h1, h2⟩
      refine ⟨⟨hx0.le, fun k => mul_nonneg hR.le (h1 k)⟩, ?_⟩
      simp only [R]; nlinarith
  by_cases hs : s ∈ simplexDLMF n
  · rw [dirichletG, dirichletG, indicator_of_mem (hmem.mpr hs), indicator_of_mem hs, dirichletF,
      dirichletF, Fin.prod_univ_succ, Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ, Pi.smul_apply, smul_eq_mul]
    have hsum : 1 - (x + ∑ k, R * s k) = R * (1 - ∑ k, s k) := by
      rw [← Finset.mul_sum]; simp only [R]; ring
    have hS : 0 ≤ 1 - ∑ k, s k := by linarith [hs.2]
    rw [hsum]
    simp only [ofReal_mul]
    rw [mul_cpow_ofReal_nonneg hR.le hS]
    have hprod : ∏ k : Fin n, ((R : ℂ) * (s k : ℂ)) ^ (z k.succ - 1) =
        (R : ℂ) ^ (∑ k : Fin n, z k.succ - n) * ∏ k : Fin n, (s k : ℂ) ^ (z k.succ - 1) := by
      rw [show ∑ k : Fin n, z k.succ - n = ∑ k : Fin n, (z k.succ - 1) by
          simp [Finset.sum_sub_distrib],
        ← prod_ofReal_cpow hR, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun k _ => ?_
      exact_mod_cast mul_cpow_ofReal_nonneg hR.le (hs.1 k) _
    rw [show ((R : ℝ) : ℂ) = (R : ℂ) from rfl] at *
    have hR0 : (R : ℂ) ≠ 0 := ofReal_ne_zero.mpr hR.ne'
    rw [show ∏ k : Fin n, ((R : ℂ) * (s k : ℂ)) ^ (z k.succ - 1) = _ from hprod,
      show ∑ k : Fin n, z k.succ + w - 1 - n = (∑ k : Fin n, z k.succ - n) + (w - 1) by ring,
      cpow_add _ _ hR0]
    ring
  · rw [dirichletG, dirichletG, indicator_of_notMem (fun h => hs (hmem.mp h)),
      indicator_of_notMem hs, mul_zero]

/-- `∫ f = Rⁿ ∫ f(R s) ds` on `ℝⁿ`, `R > 0`. -/
theorem integral_eq_pow_mul_integral_smul {n : ℕ} {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (f : (Fin n → ℝ) → E) {R : ℝ} (hR : 0 < R) :
    ∫ t, f t = R ^ n • ∫ s, f (R • s) := by
  rw [Measure.integral_comp_smul, Module.finrank_fin_fun, smul_smul,
    abs_of_pos (inv_pos.mpr (pow_pos hR n)), mul_inv_cancel₀ (pow_ne_zero n hR.ne'), one_smul]

/-- The inner integral of the induction step, for `0 < x < 1`. -/
theorem integral_dirichletG_cons {n : ℕ} (z : Fin (n + 1) → ℂ) (w : ℂ) {x : ℝ} (hx : x ∈ Ioo 0 1) :
    ∫ t, dirichletG (n + 1) z w (Fin.cons x t) =
      (x : ℂ) ^ (z 0 - 1) * ((1 - x : ℝ) : ℂ) ^ (∑ k : Fin n, z k.succ + w - 1) *
        ∫ s, dirichletG n (fun k => z k.succ) w s := by
  have hR : 0 < 1 - x := by linarith [hx.2]
  have hR0 : ((1 - x : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr hR.ne'
  rw [integral_eq_pow_mul_integral_smul _ hR]
  simp_rw [dirichletG_cons_smul z w hx.1 hx.2]
  rw [integral_const_mul, Complex.real_smul]
  have e : (((1 - x) ^ n : ℝ) : ℂ) * ((1 - x : ℝ) : ℂ) ^ (∑ k : Fin n, z k.succ + w - 1 - n) =
      ((1 - x : ℝ) : ℂ) ^ (∑ k : Fin n, z k.succ + w - 1) := by
    have h1 : (1 : ℂ) - x ≠ 0 := by exact_mod_cast hR.ne'
    rw [cpow_sub _ _ hR0, cpow_natCast]; push_cast; field_simp
  rw [← e]
  ring

theorem integral_norm_dirichletG_cons {n : ℕ} (z : Fin (n + 1) → ℂ) (w : ℂ) {x : ℝ}
    (hx : x ∈ Ioo 0 1) :
    ∫ t, ‖dirichletG (n + 1) z w (Fin.cons x t)‖ =
      ‖(x : ℂ) ^ (z 0 - 1) * ((1 - x : ℝ) : ℂ) ^ (∑ k : Fin n, z k.succ + w - 1)‖ *
        ∫ s, ‖dirichletG n (fun k => z k.succ) w s‖ := by
  have hR : 0 < 1 - x := by linarith [hx.2]
  have hR0 : ((1 - x : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr hR.ne'
  rw [integral_eq_pow_mul_integral_smul _ hR]
  simp_rw [dirichletG_cons_smul z w hx.1 hx.2, norm_mul]
  rw [integral_const_mul, smul_eq_mul]
  have e : (1 - x) ^ n * ‖((1 - x : ℝ) : ℂ) ^ (∑ k : Fin n, z k.succ + w - 1 - n)‖ =
      ‖((1 - x : ℝ) : ℂ) ^ (∑ k : Fin n, z k.succ + w - 1)‖ := by
    rw [cpow_sub _ _ hR0, cpow_natCast, norm_div, norm_pow, norm_real,
      Real.norm_of_nonneg hR.le]
    field_simp
  rw [← e]
  ring

/-- Outside `[0, 1]` the slice `t ↦ G_{n+1}(x, t)` vanishes. -/
theorem dirichletG_cons_eq_zero {n : ℕ} (z : Fin (n + 1) → ℂ) (w : ℂ) {x : ℝ}
    (hx : x < 0 ∨ 1 < x) (t : Fin n → ℝ) : dirichletG (n + 1) z w (Fin.cons x t) = 0 := by
  refine indicator_of_notMem (fun h => ?_) _
  obtain ⟨h1, h2⟩ := h
  have h0 := h1 0
  simp only [Fin.cons_zero] at h0
  rcases hx with hx | hx
  · linarith
  · rw [Fin.sum_univ_succ] at h2
    simp only [Fin.cons_zero, Fin.cons_succ] at h2
    have : 0 ≤ ∑ k : Fin n, t k := Finset.sum_nonneg fun k _ => by
      simpa using h1 k.succ
    linarith

/-- **Dirichlet's integral**: `∫_{Vₙ} ∏ tₖ^{zₖ−1}(1 − ∑ tₖ)^{w−1} dt =
∏ Γ(zₖ) Γ(w)/Γ(∑ zₖ + w)` for `ℜzₖ > 0`, `ℜw > 0`, together with integrability. -/
theorem dirichlet_integral (n : ℕ) (z : Fin n → ℂ) (hz : ∀ k, 0 < (z k).re) {w : ℂ}
    (hw : 0 < w.re) : Integrable (dirichletG n z w) ∧
      ∫ t, dirichletG n z w t = (∏ k, Gamma (z k)) * Gamma w / Gamma (∑ k, z k + w) := by
  induction n with
  | zero =>
    have hG : ∀ t : Fin 0 → ℝ, dirichletG 0 z w t = 1 := fun t => by
      rw [dirichletG, indicator_of_mem (show t ∈ simplexDLMF 0 from ⟨fun k => k.elim0, by simp⟩),
        dirichletF]; simp
    have hGw := Complex.Gamma_ne_zero_of_re_pos hw
    refine ⟨?_, ?_⟩
    · rw [show dirichletG 0 z w = fun _ => 1 from funext hG]; exact integrable_const _
    · simp_rw [hG]
      rw [integral_const, measureReal_def, volume_pi, Measure.pi_univ]
      simp [hGw]
  | succ n ih =>
    set z' : Fin n → ℂ := fun k => z k.succ
    obtain ⟨hI, hV⟩ := ih z' (fun k => hz k.succ)
    set c := ∑ k : Fin n, z k.succ + w - 1
    have hc : 0 < (c + 1).re := by
      simp only [c, sub_add_cancel, add_re, re_sum]
      exact add_pos_of_nonneg_of_pos (Finset.sum_nonneg fun k _ => (hz k.succ).le) hw
    set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0
    have hmp : MeasurePreserving e.symm (volume.prod volume) volume :=
      (volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0).symm _
    have he : ∀ p : ℝ × (Fin n → ℝ), e.symm p = Fin.cons p.1 p.2 := fun p => by
      simp [e, MeasurableEquiv.piFinSuccAbove]; rfl
    set F : ℝ × (Fin n → ℝ) → ℂ := fun p => dirichletG (n + 1) z w (Fin.cons p.1 p.2)
    have hFG : (dirichletG (n + 1) z w) ∘ e.symm = F := funext fun p => by
      simp only [Function.comp, he, F]
    -- the one-dimensional factor
    set φ : ℝ → ℂ := fun x => (x : ℂ) ^ (z 0 - 1) * ((1 - x : ℝ) : ℂ) ^ c
    have hφ : IntegrableOn φ (Ioo 0 1) := by
      have h := Complex.betaIntegral_convergent (hz 0) hc
      rw [intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one] at h
      refine h.congr_fun (fun x _ => ?_) measurableSet_Ioo
      simp only [φ, add_sub_cancel_right]; push_cast; ring_nf
    have hnull : ∀ᵐ x : ℝ, x ≠ 0 ∧ x ≠ 1 := by
      have h0 : ∀ᵐ x : ℝ, x ≠ 0 := Measure.ae_ne volume 0
      have h1 : ∀ᵐ x : ℝ, x ≠ 1 := Measure.ae_ne volume 1
      filter_upwards [h0, h1] with x hx0 hx1 using ⟨hx0, hx1⟩
    have hcases : ∀ x : ℝ, x ≠ 0 → x ≠ 1 → x ∈ Ioo 0 1 ∨ (x < 0 ∨ 1 < x) := fun x h0 h1 => by
      rcases lt_trichotomy x 0 with h | h | h
      · exact Or.inr (Or.inl h)
      · exact absurd h h0
      · rcases lt_trichotomy x 1 with h' | h' | h'
        · exact Or.inl ⟨h, h'⟩
        · exact absurd h' h1
        · exact Or.inr (Or.inr h')
    -- integrability of `F`
    have hFm : AEStronglyMeasurable F (volume.prod volume) :=
      ((measurable_dirichletG (n + 1) z w).comp (by fun_prop :
        Measurable fun p : ℝ × (Fin n → ℝ) =>
          (Fin.cons p.1 p.2 : Fin (n + 1) → ℝ))).aestronglyMeasurable
    have hFi : Integrable F (volume.prod volume) := by
      rw [integrable_prod_iff hFm]
      constructor
      · filter_upwards [hnull] with x hx
        rcases hcases x hx.1 hx.2 with hx' | hx'
        · have hR : 0 < 1 - x := by linarith [hx'.2]
          have h := (hI.comp_smul (inv_ne_zero hR.ne')).const_mul
            ((x : ℂ) ^ (z 0 - 1) * ((1 - x : ℝ) : ℂ) ^ (c - n))
          refine h.congr (ae_of_all _ fun t => ?_)
          have h2 := dirichletG_cons_smul z w hx'.1 hx'.2 ((1 - x)⁻¹ • t)
          rw [smul_smul, mul_inv_cancel₀ hR.ne', one_smul] at h2
          simp only [F, h2, c]
          rfl
        · simp only [F, dirichletG_cons_eq_zero z w hx']; exact integrable_zero _ _ _
      · have h : IntegrableOn (fun x => ‖φ x‖ * ∫ s, ‖dirichletG n z' w s‖) (Ioo 0 1) :=
          hφ.norm.mul_const _
        rw [← integrable_indicator_iff measurableSet_Ioo] at h
        refine h.congr ?_
        filter_upwards [hnull] with x hx
        rcases hcases x hx.1 hx.2 with hx' | hx'
        · rw [indicator_of_mem hx']
          simp only [F, φ]
          rw [integral_norm_dirichletG_cons z w hx']
        · rw [indicator_of_notMem (fun h => by rcases hx' with h' | h' <;> linarith [h.1, h.2])]
          simp only [F, dirichletG_cons_eq_zero z w hx', norm_zero, integral_zero]
    refine ⟨?_, ?_⟩
    · rw [← hmp.integrable_comp_emb e.symm.measurableEmbedding, hFG]; exact hFi
    · rw [← hmp.integral_comp', show (fun p => dirichletG (n + 1) z w (e.symm p)) = F from hFG,
        integral_prod F hFi]
      have hinner : ∀ᵐ x : ℝ, ∫ t, F (x, t) =
          (Ioo (0 : ℝ) 1).indicator (fun x => φ x * ∫ s, dirichletG n z' w s) x := by
        filter_upwards [hnull] with x hx
        rcases hcases x hx.1 hx.2 with hx' | hx'
        · rw [indicator_of_mem hx']
          exact integral_dirichletG_cons z w hx'
        · rw [indicator_of_notMem (fun h => by rcases hx' with h' | h' <;> linarith [h.1, h.2])]
          simp only [F, dirichletG_cons_eq_zero z w hx', integral_zero]
      rw [integral_congr_ae hinner, integral_indicator measurableSet_Ioo, integral_mul_const, hV]
      have hB := Complex.betaIntegral_eq_Gamma_mul_div (z 0) (c + 1) (hz 0) hc
      rw [Complex.betaIntegral, intervalIntegral.integral_of_le zero_le_one,
        integral_Ioc_eq_integral_Ioo] at hB
      have hφB : ∫ x in Ioo (0 : ℝ) 1, φ x =
          Gamma (z 0) * Gamma (c + 1) / Gamma (z 0 + (c + 1)) := by
        rw [← hB]
        refine setIntegral_congr_fun measurableSet_Ioo fun x _ => ?_
        simp only [φ, add_sub_cancel_right]; push_cast; ring_nf
      rw [hφB, Fin.prod_univ_succ, Fin.sum_univ_succ]
      have hc1 : c + 1 = ∑ k : Fin n, z' k + w := by simp only [c, z']; ring
      rw [hc1, show z 0 + (∑ k : Fin n, z' k + w) = z 0 + ∑ k : Fin n, z k.succ + w by
        simp only [z']; ring]
      have hG := Complex.Gamma_ne_zero_of_re_pos (show 0 < (∑ k : Fin n, z' k + w).re by
        rw [← hc1]; exact hc)
      simp only [z'] at hG ⊢
      field_simp

/-- **DLMF 5.14.2**: `∫_{Vₙ} (1 − ∑ tₖ)^{z_{n+1}−1} ∏ tₖ^{zₖ−1} dtₖ =
Γ(z₁)⋯Γ(z_{n+1})/Γ(z₁ + ⋯ + z_{n+1})`, `ℜzₖ > 0` (`z (Fin.last n)` is `z_{n+1}`). -/
theorem dlmf_5_14_2 {n : ℕ} (z : Fin (n + 1) → ℂ) (hz : ∀ k, 0 < (z k).re) :
    ∫ t in simplexDLMF n, ((1 - ∑ k, t k : ℝ) : ℂ) ^ (z (Fin.last n) - 1) *
      ∏ k : Fin n, (t k : ℂ) ^ (z k.castSucc - 1) = (∏ k, Gamma (z k)) / Gamma (∑ k, z k) := by
  have h := (dirichlet_integral n (fun k => z k.castSucc) (fun k => hz _) (hz (Fin.last n))).2
  rw [dirichletG, integral_indicator (measurableSet_simplexDLMF n)] at h
  rw [Fin.prod_univ_castSucc, Fin.sum_univ_castSucc, ← h]
  refine setIntegral_congr_fun (measurableSet_simplexDLMF n) fun t _ => ?_
  rw [dirichletF, mul_comm]

/-- **DLMF 5.14.1**: `∫_{Vₙ} t₁^{z₁−1}⋯tₙ^{zₙ−1} dt = Γ(z₁)⋯Γ(zₙ)/Γ(1 + z₁ + ⋯ + zₙ)`,
`ℜzₖ > 0`. -/
theorem dlmf_5_14_1 {n : ℕ} (z : Fin n → ℂ) (hz : ∀ k, 0 < (z k).re) :
    ∫ t in simplexDLMF n, ∏ k, (t k : ℂ) ^ (z k - 1) =
      (∏ k, Gamma (z k)) / Gamma (1 + ∑ k, z k) := by
  have h := (dirichlet_integral n z hz (w := 1) (by simp)).2
  rw [dirichletG, integral_indicator (measurableSet_simplexDLMF n), Complex.Gamma_one,
    mul_one, add_comm] at h
  rw [← h]
  refine setIntegral_congr_fun (measurableSet_simplexDLMF n) fun t _ => ?_
  rw [dirichletF, sub_self, cpow_zero, mul_one]

/-- **DLMF 5.14.3**: `Δ(t₁, …, tₙ) = ∏_{1≤j<k≤n} (tⱼ − tₖ)`. -/
def vandermondeDelta {n : ℕ} (t : Fin n → ℝ) : ℝ := ∏ j, ∏ k ∈ Finset.Ioi j, (t j - t k)

end Azurite.DLMF
