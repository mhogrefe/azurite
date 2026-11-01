/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter1.Section18WeylLP

/-!
# DLMF §1.18(ix): boundary values (1.18.71)

Following Dunford–Schwartz XIII.2 (Def. 17, Thm. 19), a *boundary value* for `ℒ` on `X` is a
linear functional on `𝒟(ℒ*)` that is bounded in the graph norm and vanishes on `𝒟(ℒ)`; it is a
boundary value *at `a`* if it vanishes on functions vanishing near `a`.

* `maxRep`, `maxRepD`: the `C¹` representative of `f ∈ 𝒟(ℒ*)` and its derivative, with
  `f′(x) = f′(c) + ∫_c^x (q f − ℒ*f)`; `evalRep_bound` bounds `|f(x)| + |f′(x)|` by the graph norm.
* `IsBoundaryValue`, `VanishesNear`, `leftEnd`, `rightEnd`.
* `graphBounded_of_tendsto`: a pointwise limit of graph-bounded functionals is graph bounded
  (Banach–Steinhaus on the closed graph).
* `dlmf_1_18_71_left`, `dlmf_1_18_71_right`: functionals
  `B(f) = lim_{x → a} (α(x) f(x) + β(x) f′(x))` are boundary values at `a` (resp. `b`).
* `IsBoundaryValue.eq_zero_of_mem`: boundary values vanish on `𝒟(ℒ**)`.
-/

open Set Filter Topology MeasureTheory LinearPMap
open scoped InnerProductSpace ComplexConjugate ContDiff

namespace Azurite.DLMF

variable {Y : Set ℝ} {q : ℝ → ℝ}

/-! ### The `C¹` representative of an element of `𝒟(ℒ*)` -/

section Rep

variable (hY : IsOpen Y) (hYc : Y.OrdConnected) (hYne : Y.Nonempty) (hq : ContinuousOn q Y)

include hY hYc hYne hq in
theorem exists_maxRep (w : (minOp Y q)†.domain) :
    ∃ FF : (ℝ → ℂ) × (ℝ → ℂ), ((w : L2X Y) : ℝ → ℂ) =ᵐ[volume.restrict Y] FF.1 ∧
      (∀ x ∈ Y, HasDerivAt FF.1 (FF.2 x) x) ∧
      ∀ c ∈ Y, ∀ x ∈ Y, FF.2 x = FF.2 c +
        ∫ t in c..x, ((q t : ℂ) * FF.1 t - (((minOp Y q)† w : L2X Y) : ℝ → ℂ) t) := by
  have hw := (weak_schrodinger_iff hY hq (w : L2X Y) ((minOp Y q)† w)).mpr
    ((adjoint_isFormalAdjoint (dense_minOp_domain hY hq)) w)
  obtain ⟨F, F', h1, h2, h3⟩ := weak_regularity hY hYc hYne hq (L2X.locallyIntegrableOn hY _)
    (L2X.locallyIntegrableOn hY _) hw
  exact ⟨(F, F'), h1, h2, h3⟩

/-- The continuous representative `F` of `w ∈ 𝒟(ℒ*)`. -/
noncomputable def maxRep (w : (minOp Y q)†.domain) : ℝ → ℂ :=
  (exists_maxRep hY hYc hYne hq w).choose.1

/-- Its derivative `F′`. -/
noncomputable def maxRepD (w : (minOp Y q)†.domain) : ℝ → ℂ :=
  (exists_maxRep hY hYc hYne hq w).choose.2

theorem maxRep_spec (w : (minOp Y q)†.domain) :
    ((w : L2X Y) : ℝ → ℂ) =ᵐ[volume.restrict Y] maxRep hY hYc hYne hq w ∧
      (∀ x ∈ Y, HasDerivAt (maxRep hY hYc hYne hq w) (maxRepD hY hYc hYne hq w x) x) ∧
      ∀ c ∈ Y, ∀ x ∈ Y, maxRepD hY hYc hYne hq w x = maxRepD hY hYc hYne hq w c +
        ∫ t in c..x, ((q t : ℂ) * maxRep hY hYc hYne hq w t -
          (((minOp Y q)† w : L2X Y) : ℝ → ℂ) t) :=
  (exists_maxRep hY hYc hYne hq w).choose_spec

theorem continuousOn_maxRep (w : (minOp Y q)†.domain) :
    ContinuousOn (maxRep hY hYc hYne hq w) Y := fun x hx =>
  ((maxRep_spec hY hYc hYne hq w).2.1 x hx).continuousAt.continuousWithinAt

/-- A continuous function a.e. equal to `w` on `Y` is the representative on `Y`. -/
theorem eqOn_maxRep (w : (minOp Y q)†.domain) {G : ℝ → ℂ} (hG : ContinuousOn G Y)
    (hwG : ((w : L2X Y) : ℝ → ℂ) =ᵐ[volume.restrict Y] G) :
    EqOn (maxRep hY hYc hYne hq w) G Y :=
  eqOn_of_ae_eq_of_continuousOn hY (continuousOn_maxRep hY hYc hYne hq w) hG
    ((maxRep_spec hY hYc hYne hq w).1.symm.trans hwG)

/-- If the representatives agree on `Y`, so do their derivatives. -/
theorem maxRepD_eq_of_eqOn (w : (minOp Y q)†.domain) {G G' : ℝ → ℂ}
    (hG : ∀ x ∈ Y, HasDerivAt G (G' x) x) (heq : EqOn (maxRep hY hYc hYne hq w) G Y) {x : ℝ}
    (hx : x ∈ Y) : maxRepD hY hYc hYne hq w x = G' x :=
  ((maxRep_spec hY hYc hYne hq w).2.1 x hx).unique
    ((hG x hx).congr_of_eventuallyEq (Filter.eventuallyEq_of_mem (hY.mem_nhds hx) heq))

/-- Evaluation of the representative and its derivative at `x ∈ Y` as linear maps. -/
noncomputable def evalRep {x : ℝ} (hx : x ∈ Y) : (minOp Y q)†.domain →ₗ[ℂ] ℂ × ℂ where
  toFun w := (maxRep hY hYc hYne hq w x, maxRepD hY hYc hYne hq w x)
  map_add' v w := by
    obtain ⟨hv1, hv2, -⟩ := maxRep_spec hY hYc hYne hq v
    obtain ⟨hw1, hw2, -⟩ := maxRep_spec hY hYc hYne hq w
    have heq := eqOn_maxRep hY hYc hYne hq (v + w)
      ((continuousOn_maxRep hY hYc hYne hq v).add (continuousOn_maxRep hY hYc hYne hq w))
      (by rw [Submodule.coe_add]; exact (Lp.coeFn_add _ _).trans (hv1.add hw1))
    simp only [Prod.mk_add_mk, Prod.mk.injEq]
    exact ⟨heq hx, maxRepD_eq_of_eqOn hY hYc hYne hq (v + w)
      (fun y hy => (hv2 y hy).add (hw2 y hy)) heq hx⟩
  map_smul' a v := by
    obtain ⟨hv1, hv2, -⟩ := maxRep_spec hY hYc hYne hq v
    have heq := eqOn_maxRep hY hYc hYne hq (a • v)
      (continuousOn_const.smul (continuousOn_maxRep hY hYc hYne hq v))
      (by rw [Submodule.coe_smul]; exact (Lp.coeFn_smul _ _).trans (hv1.const_smul a))
    simp only [RingHom.id_apply, Prod.smul_mk, Prod.mk.injEq]
    exact ⟨heq hx, maxRepD_eq_of_eqOn hY hYc hYne hq (a • v)
      (fun y hy => (hv2 y hy).const_smul a) heq hx⟩

end Rep

/-! ### The local estimate (Dunford–Schwartz XIII.2.16) -/

/-- `∫_J ‖v‖ ≤ √|J| ‖v‖` for `v ∈ L²(Y)` and `J ⊆ Y` of finite positive measure. -/
theorem setIntegral_norm_le_L2 (v : L2X Y) {J : Set ℝ} (hJY : J ⊆ Y)
    (hm : 0 < volume.real J) (hmt : volume J < ⊤) :
    ∫ t in J, ‖(v : ℝ → ℂ) t‖ ≤ Real.sqrt (volume.real J) * ‖v‖ := by
  have : IsFiniteMeasure (volume.restrict J) := ⟨by simpa using hmt⟩
  have hres : (volume.restrict Y).restrict J = volume.restrict J :=
    Measure.restrict_restrict_of_subset hJY
  have hL2J : MemLp (v : ℝ → ℂ) 2 (volume.restrict J) := by
    have := (Lp.memLp v).restrict J
    rwa [hres] at this
  have hint1 : IntegrableOn (fun t => ‖(v : ℝ → ℂ) t‖) J :=
    (MemLp.integrable (by norm_num) hL2J).norm
  have hint2 : IntegrableOn (fun t => ‖(v : ℝ → ℂ) t‖ ^ 2) J :=
    (memLp_two_iff_integrable_sq_norm hL2J.aestronglyMeasurable).mp hL2J
  have hsq : ∫ t in J, ‖(v : ℝ → ℂ) t‖ ^ 2 ≤ ‖v‖ ^ 2 := by
    rw [← integral_norm_sq_Lp v, ← hres]
    exact setIntegral_le_integral ((memLp_two_iff_integrable_sq_norm
      (Lp.memLp v).aestronglyMeasurable).mp (Lp.memLp v)) (ae_of_all _ fun t => by positivity)
  set m := volume.real J
  rcases eq_or_lt_of_le (norm_nonneg v) with h0 | hpos
  · have hv0 : (v : ℝ → ℂ) =ᵐ[volume.restrict Y] 0 := by
      rw [← Lp.eq_zero_iff_ae_eq_zero, ← norm_eq_zero]; exact h0.symm
    have : ∀ᵐ t ∂(volume.restrict J), ‖(v : ℝ → ℂ) t‖ = 0 := by
      have := ae_restrict_of_ae_restrict_of_subset hJY hv0
      filter_upwards [this] with t ht; simp [ht]
    rw [integral_congr_ae this, ← h0]; simp
  · set lam := ‖v‖ / Real.sqrt m
    have hsm : 0 < Real.sqrt m := Real.sqrt_pos.mpr hm
    have hlam : 0 < lam := div_pos hpos hsm
    have hpt : ∀ t, ‖(v : ℝ → ℂ) t‖ ≤ (‖(v : ℝ → ℂ) t‖ ^ 2 / lam + lam) / 2 := fun t => by
      rw [div_add' _ _ _ hlam.ne', div_div, le_div_iff₀ (by positivity)]
      nlinarith [sq_nonneg (‖(v : ℝ → ℂ) t‖ - lam)]
    have hint3 : IntegrableOn (fun t => (‖(v : ℝ → ℂ) t‖ ^ 2 / lam + lam) / 2) J := by
      refine Integrable.div_const ?_ 2
      exact (hint2.div_const lam).add (integrable_const lam)
    have e : ∫ t in J, (‖(v : ℝ → ℂ) t‖ ^ 2 / lam + lam) / 2 =
        ((∫ t in J, ‖(v : ℝ → ℂ) t‖ ^ 2) / lam + lam * m) / 2 := by
      rw [integral_div, integral_add (hint2.div_const lam) (integrable_const lam), integral_div,
        setIntegral_const]
      simp only [m, smul_eq_mul]
      ring
    calc ∫ t in J, ‖(v : ℝ → ℂ) t‖ ≤ ∫ t in J, (‖(v : ℝ → ℂ) t‖ ^ 2 / lam + lam) / 2 :=
          setIntegral_mono hint1 hint3 hpt
      _ = ((∫ t in J, ‖(v : ℝ → ℂ) t‖ ^ 2) / lam + lam * m) / 2 := e
      _ ≤ (‖v‖ ^ 2 / lam + lam * m) / 2 := by gcongr
      _ = Real.sqrt m * ‖v‖ := by
          simp only [lam]
          have : Real.sqrt m ^ 2 = m := Real.sq_sqrt hm.le
          field_simp
          nlinarith

section Estimate

variable (hY : IsOpen Y) (hYc : Y.OrdConnected) (hYne : Y.Nonempty) (hq : ContinuousOn q Y)

include hY hYc hYne hq in
/-- **Local estimate** (Dunford–Schwartz XIII.2.16): `|F(x)| + |F′(x)| ≤ C (‖f‖ + ‖ℒ*f‖)`. -/
theorem evalRep_bound {x : ℝ} (hx : x ∈ Y) : ∃ C, ∀ w : (minOp Y q)†.domain,
    ‖maxRep hY hYc hYne hq w x‖ + ‖maxRepD hY hYc hYne hq w x‖ ≤
      C * (‖(w : L2X Y)‖ + ‖(minOp Y q)† w‖) := by
  obtain ⟨ε, hε, hJ⟩ := exists_Icc_ball hY hx
  set J := Icc (x - ε) (x + ε)
  have hmJ : volume.real J = 2 * ε := by
    simp only [J, Real.volume_real_Icc]; rw [max_eq_left (by linarith)]; ring
  have hmt : volume J < ⊤ := by simp [J]
  obtain ⟨Q, hQ⟩ := isCompact_Icc.exists_bound_of_continuousOn (hq.mono hJ)
  have hQ0 : 0 ≤ Q := (norm_nonneg _).trans (hQ x ⟨by linarith, by linarith⟩)
  set K := Real.sqrt (2 * ε)
  have hK0 : 0 ≤ K := Real.sqrt_nonneg _
  refine ⟨(1 / ε + 2 / ε ^ 2) * K * (1 + ε ^ 2 * (Q + 1)), fun w => ?_⟩
  obtain ⟨hwF, hF, hD⟩ := maxRep_spec hY hYc hYne hq w
  set F := maxRep hY hYc hYne hq w
  set D := maxRepD hY hYc hYne hq w
  set g : ℝ → ℂ := (((minOp Y q)† w : L2X Y) : ℝ → ℂ)
  set h : ℝ → ℂ := fun t => (q t : ℂ) * F t - g t
  set A := F x
  set B := D x
  -- `L¹` bounds on `J`
  have hFJ : ∫ t in J, ‖F t‖ ≤ K * ‖(w : L2X Y)‖ := by
    have h1 := setIntegral_norm_le_L2 (w : L2X Y) hJ (by rw [hmJ]; positivity) hmt
    rw [hmJ] at h1
    refine le_of_eq_of_le (integral_congr_ae ?_) h1
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hJ hwF] with t ht
    rw [ht]
  have hgJ : ∫ t in J, ‖g t‖ ≤ K * ‖(minOp Y q)† w‖ := by
    have h1 := setIntegral_norm_le_L2 ((minOp Y q)† w) hJ (by rw [hmJ]; positivity) hmt
    rwa [hmJ] at h1
  have hFc : ContinuousOn F J := (continuousOn_maxRep hY hYc hYne hq w).mono hJ
  have hres : (volume.restrict Y).restrict J = volume.restrict J :=
    Measure.restrict_restrict_of_subset hJ
  have hfin : IsFiniteMeasure (volume.restrict J) := ⟨by simpa using hmt⟩
  have hgint : IntegrableOn g J := by
    have := (Lp.memLp ((minOp Y q)† w)).restrict J
    rw [hres] at this
    exact MemLp.integrable (by norm_num) this
  have hFint : IntegrableOn F J := hFc.integrableOn_compact isCompact_Icc
  have hqF : IntegrableOn (fun t => (q t : ℂ) * F t) J :=
    ((Complex.continuous_ofReal.comp_continuousOn (hq.mono hJ)).mul hFc).integrableOn_compact
      isCompact_Icc
  have hhint : IntegrableOn h J := hqF.sub hgint
  set H := ∫ t in J, ‖h t‖
  have hH : H ≤ Q * (K * ‖(w : L2X Y)‖) + K * ‖(minOp Y q)† w‖ := by
    have h1 : H ≤ ∫ t in J, (Q * ‖F t‖ + ‖g t‖) := by
      refine setIntegral_mono_on hhint.norm ((hFint.norm.const_mul Q).add hgint.norm)
        measurableSet_Icc fun t ht => ?_
      simp only [h]
      refine (norm_sub_le _ _).trans (add_le_add ?_ le_rfl)
      rw [norm_mul, Complex.norm_real]
      exact mul_le_mul_of_nonneg_right (hQ t ht) (norm_nonneg _)
    rw [integral_add (hFint.norm.const_mul Q) hgint.norm, integral_const_mul] at h1
    nlinarith [hFJ, hgJ]
  have hH0 : 0 ≤ H := setIntegral_nonneg measurableSet_Icc fun t _ => norm_nonneg _
  -- `|D(s) − D(x)| ≤ H` on `J`
  have hsub : ∀ s ∈ J, uIcc x s ⊆ J := fun s hs =>
    uIcc_subset_Icc ⟨by linarith, by linarith⟩ hs
  have hDs : ∀ s ∈ J, ‖D s - B‖ ≤ H := fun s hs => by
    rw [hD x hx s (hJ hs), add_sub_cancel_left]
    refine (intervalIntegral.norm_integral_le_integral_norm_uIoc).trans ?_
    exact setIntegral_mono_set hhint.norm (ae_of_all _ fun t => norm_nonneg _)
      (Eventually.of_forall (uIoc_subset_uIcc.trans (hsub s hs)))
  have hDc : ContinuousOn D J := by
    intro s hs
    have hprim := intervalIntegral.continuousOn_primitive_interval' (μ := volume) (a := x)
      (b₁ := x - ε) (b₂ := x + ε)
      ((hhint.mono_set (by rw [uIcc_of_le (by linarith)])).intervalIntegrable)
      (by rw [uIcc_of_le (by linarith)]; exact ⟨by linarith, by linarith⟩)
    have : EqOn D (fun s => B + ∫ t in x..s, h t) J := fun s hs => hD x hx s (hJ hs)
    rw [uIcc_of_le (by linarith)] at hprim
    exact ((continuousOn_const.add hprim).congr this) s hs
  -- the Taylor remainder
  have hR : ∀ t ∈ J, ‖F t - A - B * ((t : ℂ) - x)‖ ≤ ε * H := fun t ht => by
    have hDi := (hDc.mono (hsub t ht)).intervalIntegrable (μ := volume)
    have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := x) (b := t)
      (fun s hs => hF s (hJ (hsub t ht hs))) hDi
    have e : F t - A - B * ((t : ℂ) - x) = ∫ s in x..t, (D s - B) := by
      rw [intervalIntegral.integral_sub hDi intervalIntegrable_const, hFTC,
        intervalIntegral.integral_const, Complex.real_smul]
      push_cast; ring
    rw [e]
    have htx : |t - x| ≤ ε := abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩
    refine (intervalIntegral.norm_integral_le_of_norm_le_const fun s hs =>
      hDs s (hsub t ht (uIoc_subset_uIcc hs))).trans ?_
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_right htx hH0
  -- integrals over the two halves
  set Φ : ℝ → ℂ := fun t => A * t + B * ((t : ℂ) - x) ^ 2 / 2
  have hΦ : ∀ t : ℝ, HasDerivAt Φ (A + B * ((t : ℂ) - x)) t := fun t => by
    have h1 : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 t := by
      simpa using (hasDerivAt_id t).ofReal_comp
    have := ((h1.const_mul A).add (((h1.sub_const (x : ℂ)).pow 2).const_mul B |>.div_const 2))
    refine this.congr_deriv ?_
    push_cast; ring
  have hAff : Continuous fun t : ℝ => A + B * ((t : ℂ) - x) := by fun_prop
  have half : ∀ a b, x - ε ≤ a → a ≤ b → b ≤ x + ε →
      ‖∫ t in a..b, F t‖ ≤ ∫ t in J, ‖F t‖ ∧
      ∫ t in a..b, F t = (∫ t in a..b, (F t - A - B * ((t : ℂ) - x))) + (Φ b - Φ a) ∧
      ‖∫ t in a..b, (F t - A - B * ((t : ℂ) - x))‖ ≤ ε * H * (b - a) := by
    intro a b ha hab hb
    have hsubab : Icc a b ⊆ J := Icc_subset_Icc ha hb
    have hFi : IntervalIntegrable F volume a b :=
      (hFc.mono (by rw [uIcc_of_le hab]; exact hsubab)).intervalIntegrable
    refine ⟨?_, ?_, ?_⟩
    · refine (intervalIntegral.norm_integral_le_integral_norm_uIoc).trans ?_
      exact setIntegral_mono_set hFint.norm (ae_of_all _ fun t => norm_nonneg _)
        (Eventually.of_forall (by rw [uIoc_of_le hab]; exact Ioc_subset_Icc_self.trans hsubab))
    · have hRi : IntervalIntegrable (fun t => F t - A - B * ((t : ℂ) - x)) volume a b := by
        refine ContinuousOn.intervalIntegrable ?_
        rw [uIcc_of_le hab]
        exact ((hFc.mono hsubab).sub continuousOn_const).sub
          (continuous_const.mul (Complex.continuous_ofReal.sub continuous_const)).continuousOn
      rw [← intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hΦ t)
        (hAff.intervalIntegrable _ _), ← intervalIntegral.integral_add hRi
        (hAff.intervalIntegrable _ _)]
      refine intervalIntegral.integral_congr fun t _ => ?_
      ring
    · refine (intervalIntegral.norm_integral_le_of_norm_le_const fun t ht => hR t ?_).trans ?_
      · rw [uIoc_of_le hab] at ht; exact hsubab (Ioc_subset_Icc_self ht)
      · rw [abs_of_nonneg (by linarith)]
  obtain ⟨hp1, hp2, hp3⟩ := half x (x + ε) (by linarith) (by linarith) le_rfl
  obtain ⟨hm1, hm2, hm3⟩ := half (x - ε) x le_rfl (by linarith) (by linarith)
  set Ij := ∫ t in J, ‖F t‖
  set Rp := ∫ t in x..x + ε, (F t - A - B * ((t : ℂ) - x))
  set Rm := ∫ t in x - ε..x, (F t - A - B * ((t : ℂ) - x))
  have hΦp : Φ (x + ε) - Φ x = A * ε + B * ε ^ 2 / 2 := by simp only [Φ]; push_cast; ring
  have hΦm : Φ x - Φ (x - ε) = A * ε - B * ε ^ 2 / 2 := by simp only [Φ]; push_cast; ring
  rw [hΦp] at hp2
  rw [hΦm] at hm2
  have hA : (2 * ε : ℂ) * A = (∫ t in x..x + ε, F t) + (∫ t in x - ε..x, F t) - Rp - Rm := by
    rw [hp2, hm2]; ring
  have hB : (ε ^ 2 : ℂ) * B = (∫ t in x..x + ε, F t) - (∫ t in x - ε..x, F t) - Rp + Rm := by
    rw [hp2, hm2]; ring
  have hRp : ‖Rp‖ ≤ ε * H * ε := by simpa using hp3
  have hRm : ‖Rm‖ ≤ ε * H * ε := by simpa using hm3
  have nA : 2 * ε * ‖A‖ ≤ 2 * Ij + 2 * (ε * H * ε) := by
    have := congrArg norm hA
    rw [norm_mul, show ‖(2 * ε : ℂ)‖ = 2 * ε by
      rw [show (2 * ε : ℂ) = ((2 * ε : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
        Real.norm_of_nonneg (by positivity)]] at this
    rw [this]
    refine (norm_sub_le _ _).trans ?_
    have := (norm_sub_le ((∫ t in x..x + ε, F t) + ∫ t in x - ε..x, F t) Rp)
    have := norm_add_le (∫ t in x..x + ε, F t) (∫ t in x - ε..x, F t)
    linarith
  have nB : ε ^ 2 * ‖B‖ ≤ 2 * Ij + 2 * (ε * H * ε) := by
    have := congrArg norm hB
    rw [norm_mul, show ‖(ε ^ 2 : ℂ)‖ = ε ^ 2 by
      rw [show (ε ^ 2 : ℂ) = ((ε ^ 2 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
        Real.norm_of_nonneg (by positivity)]] at this
    rw [this]
    refine (norm_add_le _ _).trans ?_
    have := norm_sub_le ((∫ t in x..x + ε, F t) - ∫ t in x - ε..x, F t) Rp
    have := norm_sub_le (∫ t in x..x + ε, F t) (∫ t in x - ε..x, F t)
    linarith
  have hAb : ‖A‖ ≤ (Ij + ε ^ 2 * H) / ε := by
    rw [le_div_iff₀ hε]; nlinarith
  have hBb : ‖B‖ ≤ 2 * (Ij + ε ^ 2 * H) / ε ^ 2 := by
    rw [le_div_iff₀ (by positivity)]; nlinarith
  have hsum : ‖A‖ + ‖B‖ ≤ (1 / ε + 2 / ε ^ 2) * (Ij + ε ^ 2 * H) := by
    have e1 : (Ij + ε ^ 2 * H) / ε = 1 / ε * (Ij + ε ^ 2 * H) := by ring
    have e2 : 2 * (Ij + ε ^ 2 * H) / ε ^ 2 = 2 / ε ^ 2 * (Ij + ε ^ 2 * H) := by ring
    rw [add_mul]; linarith
  refine hsum.trans ?_
  have hc : 0 ≤ 1 / ε + 2 / ε ^ 2 := by positivity
  have hw0 := norm_nonneg (w : L2X Y)
  have hT0 := norm_nonneg ((minOp Y q)† w)
  calc (1 / ε + 2 / ε ^ 2) * (Ij + ε ^ 2 * H)
      ≤ (1 / ε + 2 / ε ^ 2) * (K * ‖(w : L2X Y)‖ +
          ε ^ 2 * (Q * (K * ‖(w : L2X Y)‖) + K * ‖(minOp Y q)† w‖)) :=
        mul_le_mul_of_nonneg_left (add_le_add hFJ (mul_le_mul_of_nonneg_left hH (sq_nonneg ε)))
          hc
    _ ≤ (1 / ε + 2 / ε ^ 2) * K * (1 + ε ^ 2 * (Q + 1)) *
          (‖(w : L2X Y)‖ + ‖(minOp Y q)† w‖) := by
        rw [show (1 / ε + 2 / ε ^ 2) * K * (1 + ε ^ 2 * (Q + 1)) *
            (‖(w : L2X Y)‖ + ‖(minOp Y q)† w‖) = (1 / ε + 2 / ε ^ 2) *
            (K * (1 + ε ^ 2 * (Q + 1)) * (‖(w : L2X Y)‖ + ‖(minOp Y q)† w‖)) by ring]
        refine mul_le_mul_of_nonneg_left ?_ hc
        have e1 := mul_nonneg hK0 hT0
        have e2 := mul_nonneg (sq_nonneg ε) (mul_nonneg (mul_nonneg hQ0 hK0) hT0)
        have e3 := mul_nonneg (sq_nonneg ε) (mul_nonneg hK0 hw0)
        nlinarith

end Estimate

/-! ### Boundary values -/

section BoundaryValues

variable (Y q)

/-- Dunford–Schwartz XIII.2.17: a boundary value is a linear functional on `𝒟(ℒ*)`, bounded in
the graph norm, vanishing on `𝒟(ℒ) = C²_c`. -/
def IsBoundaryValue (B : (minOp Y q)†.domain →ₗ[ℂ] ℂ) : Prop :=
  (∃ C, ∀ f, ‖B f‖ ≤ C * (‖(f : L2X Y)‖ + ‖(minOp Y q)† f‖)) ∧
    ∀ f : (minOp Y q)†.domain, (f : L2X Y) ∈ (minOp Y q).domain → B f = 0

/-- `f` vanishes near the endpoint described by the sets `S d`. -/
def VanishesNear (S : ℝ → Set ℝ) (f : (minOp Y q)†.domain) : Prop :=
  ∃ d ∈ Y, ((f : L2X Y) : ℝ → ℂ) =ᵐ[volume.restrict (S d)] 0

/-- The left end `a` of `Y`: the filter of the sets `Y ∩ (−∞, d)`, `d ∈ Y`. -/
def leftEnd : Filter ℝ := ⨅ d ∈ Y, 𝓟 (Y ∩ Iio d)

/-- The right end `b` of `Y`. -/
def rightEnd : Filter ℝ := ⨅ d ∈ Y, 𝓟 (Y ∩ Ioi d)

variable {Y q}

section Generic

variable (hY : IsOpen Y) (hYc : Y.OrdConnected) (hYne : Y.Nonempty) (hq : ContinuousOn q Y)

include hY hYc hYne hq in
/-- **Banach–Steinhaus**: a limit `B f = lim (α(x) F(x) + β(x) F′(x))` along a sequence in `Y`
is bounded in the graph norm (Dunford–Schwartz XIII.2.27). -/
theorem graphBounded_of_tendsto {xs : ℕ → ℝ} (hxs : ∀ n, xs n ∈ Y) (α β : ℝ → ℂ)
    (B : (minOp Y q)†.domain →ₗ[ℂ] ℂ)
    (hB : ∀ f, Tendsto (fun n => α (xs n) * maxRep hY hYc hYne hq f (xs n) +
      β (xs n) * maxRepD hY hYc hYne hq f (xs n)) atTop (𝓝 (B f))) :
    ∃ C, ∀ f, ‖B f‖ ≤ C * (‖(f : L2X Y)‖ + ‖(minOp Y q)† f‖) := by
  set G := (minOp Y q)†.graph
  have hGc : IsClosed (G : Set (L2X Y × L2X Y)) := adjoint_isClosed (dense_minOp_domain hY hq)
  have : CompleteSpace G := hGc.completeSpace_coe
  have hπmem : ∀ p : G, (p : L2X Y × L2X Y).1 ∈ (minOp Y q)†.domain := fun p =>
    mem_domain_of_mem_graph (show ((p : L2X Y × L2X Y).1, (p : L2X Y × L2X Y).2) ∈
      (minOp Y q)†.graph
      from p.2)
  set π : G →ₗ[ℂ] (minOp Y q)†.domain :=
    { toFun := fun p => ⟨(p : L2X Y × L2X Y).1, hπmem p⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hπT : ∀ p : G, (minOp Y q)† (π p) = (p : L2X Y × L2X Y).2 := fun p => by
    obtain ⟨y, hy1, hy2⟩ := (mem_graph_iff (minOp Y q)†).mp p.2
    have : π p = y := Subtype.ext hy1.symm
    rw [this, hy2]
  choose C hC using fun n => evalRep_bound hY hYc hYne hq (hxs n)
  set ℓ : ℕ → (minOp Y q)†.domain →ₗ[ℂ] ℂ := fun n =>
    α (xs n) • (LinearMap.fst ℂ ℂ ℂ ∘ₗ evalRep hY hYc hYne hq (hxs n)) +
      β (xs n) • (LinearMap.snd ℂ ℂ ℂ ∘ₗ evalRep hY hYc hYne hq (hxs n))
  have hℓ : ∀ n f, ℓ n f = α (xs n) * maxRep hY hYc hYne hq f (xs n) +
      β (xs n) * maxRepD hY hYc hYne hq f (xs n) := fun n f => rfl
  have hnorm : ∀ p : G, ‖((p : L2X Y × L2X Y).1 : L2X Y)‖ + ‖(p : L2X Y × L2X Y).2‖ ≤ 2 * ‖p‖ :=
    fun p => by
      have h1 := norm_fst_le (p : L2X Y × L2X Y)
      have h2 := norm_snd_le (p : L2X Y × L2X Y)
      have e : ‖(p : L2X Y × L2X Y)‖ = ‖p‖ := rfl
      linarith
  set Λ : ℕ → G →L[ℂ] ℂ := fun n => ((ℓ n).comp π).mkContinuous
    ((‖α (xs n)‖ + ‖β (xs n)‖) * |C n| * 2) fun p => by
      rw [LinearMap.comp_apply, hℓ]
      have hb := hC n (π p)
      rw [hπT] at hb
      have hb' : ‖maxRep hY hYc hYne hq (π p) (xs n)‖ + ‖maxRepD hY hYc hYne hq (π p) (xs n)‖ ≤
          |C n| * (2 * ‖p‖) :=
        hb.trans (mul_le_mul (le_abs_self _) (hnorm p) (by positivity) (abs_nonneg _))
      calc ‖α (xs n) * maxRep hY hYc hYne hq (π p) (xs n) +
            β (xs n) * maxRepD hY hYc hYne hq (π p) (xs n)‖
          ≤ ‖α (xs n)‖ * ‖maxRep hY hYc hYne hq (π p) (xs n)‖ +
            ‖β (xs n)‖ * ‖maxRepD hY hYc hYne hq (π p) (xs n)‖ := by
            refine (norm_add_le _ _).trans ?_; rw [norm_mul, norm_mul]
        _ ≤ (‖α (xs n)‖ + ‖β (xs n)‖) * (‖maxRep hY hYc hYne hq (π p) (xs n)‖ +
            ‖maxRepD hY hYc hYne hq (π p) (xs n)‖) := by
            nlinarith [norm_nonneg (α (xs n)), norm_nonneg (β (xs n)),
              norm_nonneg (maxRep hY hYc hYne hq (π p) (xs n)),
              norm_nonneg (maxRepD hY hYc hYne hq (π p) (xs n))]
        _ ≤ (‖α (xs n)‖ + ‖β (xs n)‖) * (|C n| * (2 * ‖p‖)) := by gcongr
        _ = _ := by ring
  have hpt : ∀ p : G, ∃ M, ∀ n, ‖Λ n p‖ ≤ M := fun p => by
    obtain ⟨M, hM⟩ := isBounded_iff_forall_norm_le.mp
      (Metric.isBounded_range_of_tendsto _ (hB (π p)))
    exact ⟨M, fun n => hM _ ⟨n, rfl⟩⟩
  obtain ⟨C', hC'⟩ := banach_steinhaus hpt
  refine ⟨C', fun f => ?_⟩
  have hfG : ((f : L2X Y), (minOp Y q)† f) ∈ G := (mem_graph_iff (minOp Y q)†).mpr ⟨f, rfl, rfl⟩
  set p : G := ⟨_, hfG⟩
  have hπp : π p = f := rfl
  have hlim : Tendsto (fun n => ‖Λ n p‖) atTop (𝓝 ‖B f‖) := by
    rw [← hπp]; exact (hB (π p)).norm
  have hle : ‖B f‖ ≤ C' * ‖p‖ :=
    le_of_tendsto hlim (Eventually.of_forall fun n => ((Λ n).le_opNorm p).trans
      (mul_le_mul_of_nonneg_right (hC' n) (norm_nonneg _)))
  have hC'0 : 0 ≤ C' := (norm_nonneg _).trans (hC' 0)
  have hp : ‖p‖ ≤ ‖(f : L2X Y)‖ + ‖(minOp Y q)† f‖ := by
    show ‖(p : L2X Y × L2X Y)‖ ≤ _
    rw [Prod.norm_def]
    exact max_le (le_add_of_nonneg_right (norm_nonneg _)) (le_add_of_nonneg_left (norm_nonneg _))
  exact hle.trans (mul_le_mul_of_nonneg_left hp hC'0)

end Generic

end BoundaryValues

/-! ### Sequences tending to the endpoints -/

theorem exists_seq_leftEnd (hY : IsOpen Y) (hYc : Y.OrdConnected) (hYne : Y.Nonempty) :
    ∃ xs : ℕ → ℝ, (∀ n, xs n ∈ Y) ∧ Tendsto xs atTop (leftEnd Y) := by
  obtain ⟨c, hc⟩ := hYne
  obtain ⟨r, hr, hIcc⟩ := exists_Icc_ball hY hc
  have hinto : ∀ {xs : ℕ → ℝ}, (∀ n, xs n ∈ Y) → (∀ d ∈ Y, ∀ᶠ n in atTop, xs n < d) →
      Tendsto xs atTop (leftEnd Y) := fun hmem hev => by
    simp only [leftEnd, tendsto_iInf, tendsto_principal]
    intro d hd
    filter_upwards [hev d hd] with n hn
    exact ⟨hmem n, hn⟩
  by_cases hb : BddBelow Y
  · set a := sInf Y
    have hac : a < c := lt_of_le_of_lt (csInf_le hb (hIcc ⟨le_rfl, by linarith⟩)) (by linarith)
    set xs : ℕ → ℝ := fun n => a + (c - a) / 2 * (1 / ((n : ℝ) + 1))
    have hpos : ∀ n : ℕ, 0 < 1 / ((n : ℝ) + 1) := fun n => by positivity
    have hle1 : ∀ n : ℕ, 1 / ((n : ℝ) + 1) ≤ 1 := fun n => by
      rw [div_le_one (by positivity)]; linarith [n.cast_nonneg (α := ℝ)]
    have hmem : ∀ n, xs n ∈ Y := fun n => by
      have h1 : a < xs n := by
        simp only [xs]; have := hpos n; have : 0 < (c - a) / 2 := by linarith
        nlinarith
      obtain ⟨y, hy, hyx⟩ := exists_lt_of_csInf_lt ⟨c, hc⟩ h1
      refine hYc.out hy hc ⟨hyx.le, ?_⟩
      simp only [xs]; have := hle1 n; have : 0 < (c - a) / 2 := by linarith
      nlinarith
    refine ⟨xs, hmem, hinto hmem fun d hd => ?_⟩
    have had : a < d := by
      obtain ⟨r', hr', hI'⟩ := exists_Icc_ball hY hd
      exact lt_of_le_of_lt (csInf_le hb (hI' ⟨le_rfl, by linarith⟩)) (by linarith)
    have hlim : Tendsto xs atTop (𝓝 a) := by
      have := (tendsto_one_div_add_atTop_nhds_zero_nat.const_mul ((c - a) / 2)).const_add a
      rw [mul_zero, add_zero] at this
      exact this
    exact hlim.eventually (gt_mem_nhds had)
  · set xs : ℕ → ℝ := fun n => c - ((n : ℝ) + 1)
    have hmem : ∀ n, xs n ∈ Y := fun n => by
      obtain ⟨y, hy, hyx⟩ := not_bddBelow_iff.mp hb (xs n)
      exact hYc.out hy hc ⟨hyx.le, by simp only [xs]; linarith [n.cast_nonneg (α := ℝ)]⟩
    refine ⟨xs, hmem, hinto hmem fun d _ => ?_⟩
    refine Filter.eventually_atTop.mpr ⟨⌈c - d⌉₊, fun n hn => ?_⟩
    have h1 : c - d ≤ (n : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hn)
    simp only [xs]; linarith

theorem exists_seq_rightEnd (hY : IsOpen Y) (hYc : Y.OrdConnected) (hYne : Y.Nonempty) :
    ∃ xs : ℕ → ℝ, (∀ n, xs n ∈ Y) ∧ Tendsto xs atTop (rightEnd Y) := by
  obtain ⟨c, hc⟩ := hYne
  obtain ⟨r, hr, hIcc⟩ := exists_Icc_ball hY hc
  have hinto : ∀ {xs : ℕ → ℝ}, (∀ n, xs n ∈ Y) → (∀ d ∈ Y, ∀ᶠ n in atTop, d < xs n) →
      Tendsto xs atTop (rightEnd Y) := fun hmem hev => by
    simp only [rightEnd, tendsto_iInf, tendsto_principal]
    intro d hd
    filter_upwards [hev d hd] with n hn
    exact ⟨hmem n, hn⟩
  by_cases hb : BddAbove Y
  · set a := sSup Y
    have hac : c < a := lt_of_lt_of_le (by linarith) (le_csSup hb (hIcc ⟨by linarith, le_rfl⟩))
    set xs : ℕ → ℝ := fun n => a - (a - c) / 2 * (1 / ((n : ℝ) + 1))
    have hpos : ∀ n : ℕ, 0 < 1 / ((n : ℝ) + 1) := fun n => by positivity
    have hle1 : ∀ n : ℕ, 1 / ((n : ℝ) + 1) ≤ 1 := fun n => by
      rw [div_le_one (by positivity)]; linarith [n.cast_nonneg (α := ℝ)]
    have hmem : ∀ n, xs n ∈ Y := fun n => by
      have h1 : xs n < a := by
        simp only [xs]; have := hpos n; have : 0 < (a - c) / 2 := by linarith
        nlinarith
      obtain ⟨y, hy, hyx⟩ := exists_lt_of_lt_csSup ⟨c, hc⟩ h1
      refine hYc.out hc hy ⟨?_, hyx.le⟩
      simp only [xs]; have := hle1 n; have : 0 < (a - c) / 2 := by linarith
      nlinarith
    refine ⟨xs, hmem, hinto hmem fun d hd => ?_⟩
    have had : d < a := by
      obtain ⟨r', hr', hI'⟩ := exists_Icc_ball hY hd
      exact lt_of_lt_of_le (by linarith) (le_csSup hb (hI' ⟨by linarith, le_rfl⟩))
    have hlim : Tendsto xs atTop (𝓝 a) := by
      have := (tendsto_one_div_add_atTop_nhds_zero_nat.const_mul ((a - c) / 2)).const_sub a
      rw [mul_zero, sub_zero] at this
      exact this
    exact hlim.eventually (lt_mem_nhds had)
  · set xs : ℕ → ℝ := fun n => c + ((n : ℝ) + 1)
    have hmem : ∀ n, xs n ∈ Y := fun n => by
      obtain ⟨y, hy, hyx⟩ := not_bddAbove_iff.mp hb (xs n)
      exact hYc.out hc hy ⟨by simp only [xs]; linarith [n.cast_nonneg (α := ℝ)], hyx.le⟩
    refine ⟨xs, hmem, hinto hmem fun d _ => ?_⟩
    refine Filter.eventually_atTop.mpr ⟨⌈d - c⌉₊, fun n hn => ?_⟩
    have h1 : d - c ≤ (n : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hn)
    simp only [xs]; linarith

/-! ### DLMF (1.18.71) -/

section DLMF

variable (hY : IsOpen Y) (hYc : Y.OrdConnected) (hYne : Y.Nonempty) (hq : ContinuousOn q Y)

include hY hYc hYne hq in
/-- If `f` vanishes a.e. on an open `S ⊆ Y`, so do its representative and its derivative. -/
theorem maxRep_eq_zero_of_ae {S : Set ℝ} (hS : IsOpen S) (hSY : S ⊆ Y)
    (f : (minOp Y q)†.domain) (hf : ((f : L2X Y) : ℝ → ℂ) =ᵐ[volume.restrict S] 0) :
    ∀ x ∈ S, maxRep hY hYc hYne hq f x = 0 ∧ maxRepD hY hYc hYne hq f x = 0 := by
  have heq : EqOn (maxRep hY hYc hYne hq f) 0 S :=
    eqOn_of_ae_eq_of_continuousOn hS ((continuousOn_maxRep hY hYc hYne hq f).mono hSY)
      continuousOn_const
      (Filter.EventuallyEq.trans (show ((f : L2X Y) : ℝ → ℂ) =ᵐ[volume.restrict S]
        maxRep hY hYc hYne hq f from ae_restrict_of_ae_restrict_of_subset hSY
          (maxRep_spec hY hYc hYne hq f).1).symm hf)
  intro x hx
  refine ⟨heq hx, ?_⟩
  have hev : maxRep hY hYc hYne hq f =ᶠ[𝓝 x] 0 := Filter.eventuallyEq_of_mem (hS.mem_nhds hx) heq
  exact ((maxRep_spec hY hYc hYne hq f).2.1 x (hSY hx)).unique
    ((hasDerivAt_const x (0 : ℂ)).congr_of_eventuallyEq hev)

include hY hYne hq in
/-- Elements of `𝒟(ℒ) = C²_c(Y)` vanish near both ends. -/
theorem vanishesNear_of_mem_minOp (f : (minOp Y q)†.domain)
    (hf : (f : L2X Y) ∈ (minOp Y q).domain) :
    VanishesNear Y q (fun d => Y ∩ Iio d) f ∧ VanishesNear Y q (fun d => Y ∩ Ioi d) f := by
  rw [minOp_domain hY hq] at hf
  obtain ⟨φ, hφ, hfφ⟩ := hf
  obtain ⟨c, hc⟩ := hYne
  obtain ⟨α, β, hα, hβ, -, hK, -⟩ := exists_Ioo_of_isCompact hY hφ.2.1.isCompact hφ.2.2 hc
  have hz : ∀ x ∉ Ioo α β, φ x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport fun h => hx (hK h)
  refine ⟨⟨α, hα, ?_⟩, ⟨β, hβ, ?_⟩⟩
  · refine Filter.EventuallyEq.trans (show ((f : L2X Y) : ℝ → ℂ) =ᵐ[volume.restrict
        (Y ∩ Iio α)] φ from ae_restrict_of_ae_restrict_of_subset inter_subset_left hfφ) ?_
    exact (ae_restrict_iff' (hY.inter isOpen_Iio).measurableSet).mpr
      (ae_of_all _ fun x hx => hz x fun h => lt_irrefl _ (h.1.trans hx.2))
  · refine Filter.EventuallyEq.trans (show ((f : L2X Y) : ℝ → ℂ) =ᵐ[volume.restrict
        (Y ∩ Ioi β)] φ from ae_restrict_of_ae_restrict_of_subset inter_subset_left hfφ) ?_
    exact (ae_restrict_iff' (hY.inter isOpen_Ioi).measurableSet).mpr
      (ae_of_all _ fun x hx => hz x fun h => lt_irrefl _ (hx.2.trans h.2))

/-- DLMF (1.18.71): `B(f) = lim_{x→a+} (α(x) f(x) + β(x) f′(x))` for all `f ∈ 𝒟(ℒ*)`. -/
def IsLimBoundaryValueLeft (B : (minOp Y q)†.domain →ₗ[ℂ] ℂ) : Prop :=
  ∃ α β : ℝ → ℂ, ∀ f, Tendsto (fun x => α x * maxRep hY hYc hYne hq f x +
    β x * maxRepD hY hYc hYne hq f x) (leftEnd Y) (𝓝 (B f))

/-- The same at the right end `b`. -/
def IsLimBoundaryValueRight (B : (minOp Y q)†.domain →ₗ[ℂ] ℂ) : Prop :=
  ∃ α β : ℝ → ℂ, ∀ f, Tendsto (fun x => α x * maxRep hY hYc hYne hq f x +
    β x * maxRepD hY hYc hYne hq f x) (rightEnd Y) (𝓝 (B f))

include hY hYc hYne hq in
theorem boundaryValue_of_tendsto {ℓ : Filter ℝ} (S : ℝ → Set ℝ) (hSo : ∀ d, IsOpen (S d))
    (hSY : ∀ d, S d ⊆ Y) (hSℓ : ∀ d ∈ Y, S d ∈ ℓ)
    (hseq : ∃ xs : ℕ → ℝ, (∀ n, xs n ∈ Y) ∧ Tendsto xs atTop ℓ)
    (hmin : ∀ f : (minOp Y q)†.domain, (f : L2X Y) ∈ (minOp Y q).domain → VanishesNear Y q S f)
    {B : (minOp Y q)†.domain →ₗ[ℂ] ℂ} {α β : ℝ → ℂ}
    (hB : ∀ f, Tendsto (fun x => α x * maxRep hY hYc hYne hq f x +
      β x * maxRepD hY hYc hYne hq f x) ℓ (𝓝 (B f))) :
    IsBoundaryValue Y q B ∧ ∀ f, VanishesNear Y q S f → B f = 0 := by
  obtain ⟨xs, hxs, hxsℓ⟩ := hseq
  have : ℓ.NeBot := hxsℓ.neBot
  have hvan : ∀ f, VanishesNear Y q S f → B f = 0 := by
    rintro f ⟨d, hd, hf⟩
    have h0 := maxRep_eq_zero_of_ae hY hYc hYne hq (hSo d) (hSY d) f hf
    refine tendsto_nhds_unique (hB f) (tendsto_const_nhds.congr' ?_)
    filter_upwards [hSℓ d hd] with x hx
    simp [(h0 x hx).1, (h0 x hx).2]
  exact ⟨⟨graphBounded_of_tendsto hY hYc hYne hq hxs α β B fun f => (hB f).comp hxsℓ,
    fun f hf => hvan f (hmin f hf)⟩, hvan⟩

include hY hYc hYne hq in
/-- **DLMF (1.18.71)** in Dunford–Schwartz's sense (XIII.2.27): a boundary value at `a` of the
form `lim_{x→a+} (α f + β f′)` is a boundary value (graph-norm bounded, zero on `C²_c`), and it
vanishes on every `f` vanishing near `a`. -/
theorem dlmf_1_18_71_left {B : (minOp Y q)†.domain →ₗ[ℂ] ℂ}
    (hB : IsLimBoundaryValueLeft hY hYc hYne hq B) :
    IsBoundaryValue Y q B ∧ ∀ f, VanishesNear Y q (fun d => Y ∩ Iio d) f → B f = 0 := by
  obtain ⟨α, β, hB⟩ := hB
  exact boundaryValue_of_tendsto hY hYc hYne hq (fun d => Y ∩ Iio d)
    (fun d => hY.inter isOpen_Iio) (fun d => inter_subset_left)
    (fun d hd => mem_iInf_of_mem d (mem_iInf_of_mem hd (mem_principal_self _)))
    (exists_seq_leftEnd hY hYc hYne)
    (fun f hf => (vanishesNear_of_mem_minOp hY hYne hq f hf).1) hB

include hY hYc hYne hq in
theorem dlmf_1_18_71_right {B : (minOp Y q)†.domain →ₗ[ℂ] ℂ}
    (hB : IsLimBoundaryValueRight hY hYc hYne hq B) :
    IsBoundaryValue Y q B ∧ ∀ f, VanishesNear Y q (fun d => Y ∩ Ioi d) f → B f = 0 := by
  obtain ⟨α, β, hB⟩ := hB
  exact boundaryValue_of_tendsto hY hYc hYne hq (fun d => Y ∩ Ioi d)
    (fun d => hY.inter isOpen_Ioi) (fun d => inter_subset_left)
    (fun d hd => mem_iInf_of_mem d (mem_iInf_of_mem hd (mem_principal_self _)))
    (exists_seq_rightEnd hY hYc hYne)
    (fun f hf => (vanishesNear_of_mem_minOp hY hYne hq f hf).2) hB

end DLMF

/-! ### `T**` is the graph closure of `T` -/

section Closure

open WithLp

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
  {T : V →ₗ.[ℂ] V}

/-- Every `(h, T**h)` is a limit of `(φ, Tφ)`, `φ ∈ 𝒟(T)`. -/
theorem IsSymmetricDLMF.approx_adjoint_adjoint (hT : IsSymmetricDLMF T) (h : T††.domain)
    {ε : ℝ} (hε : 0 < ε) : ∃ φ : T.domain, ‖(h : V) - φ‖ < ε ∧ ‖T†† h - T φ‖ < ε := by
  set e := (WithLp.linearEquiv 2 ℂ (V × V)).symm
  set K : Submodule ℂ (WithLp 2 (V × V)) := T.graph.map (e : (V × V) →ₗ[ℂ] WithLp 2 (V × V))
  set z : WithLp 2 (V × V) := toLp 2 ((h : V), T†† h)
  have hd := hT.dense_adjoint
  have hz : z ∈ Kᗮᗮ := by
    rw [Submodule.mem_orthogonal]
    intro w hw
    rw [Submodule.mem_orthogonal] at hw
    have hw' : ∀ x : T.domain, ⟪(x : V), (ofLp w).1⟫_ℂ + ⟪T x, (ofLp w).2⟫_ℂ = 0 := fun x => by
      have := hw (toLp 2 ((x : V), T x)) ⟨((x : V), T x), (mem_graph_iff T).mpr ⟨x, rfl, rfl⟩, rfl⟩
      simpa [prod_inner_apply] using this
    have key : ∀ x : T.domain, ⟪-(ofLp w).1, (x : V)⟫_ℂ = ⟪(ofLp w).2, T x⟫_ℂ := fun x => by
      have h2 := congrArg conj (hw' x)
      simp only [_root_.map_add, inner_conj_symm, _root_.map_zero] at h2
      rw [inner_neg_left]
      linear_combination -h2
    have hmem : (ofLp w).2 ∈ T†.domain := mem_adjoint_domain_of_exists _ ⟨_, key⟩
    have hTw : T† ⟨(ofLp w).2, hmem⟩ = -(ofLp w).1 := adjoint_apply_eq hT.1 _ key
    have hfa := (adjoint_isFormalAdjoint (T := T†) hd) h ⟨(ofLp w).2, hmem⟩
    rw [hTw] at hfa
    have h3 : ⟪(ofLp w).2, T†† h⟫_ℂ = -⟪(ofLp w).1, (h : V)⟫_ℂ := by
      rw [← inner_conj_symm, hfa, inner_neg_right, _root_.map_neg, inner_conj_symm]
    simp only [z, prod_inner_apply]
    rw [h3]
    ring
  rw [Submodule.orthogonal_orthogonal_eq_closure] at hz
  obtain ⟨b, hb, hzb⟩ := Metric.mem_closure_iff.mp hz ε hε
  obtain ⟨p, hp, rfl⟩ := Submodule.mem_map.mp hb
  obtain ⟨x, hx1, hx2⟩ := (mem_graph_iff T).mp hp
  refine ⟨x, ?_, ?_⟩
  · refine lt_of_le_of_lt ?_ hzb
    rw [dist_eq_norm]
    have := prod_norm_sq_eq_of_L2 (z - (e : (V × V) →ₗ[ℂ] WithLp 2 (V × V)) p)
    have h1 : (z - (e : (V × V) →ₗ[ℂ] WithLp 2 (V × V)) p).fst = (h : V) - x := by
      simp [z, e, hx1]
    rw [h1] at this
    exact le_of_pow_le_pow_left₀ two_ne_zero (norm_nonneg _)
      (by rw [this]; nlinarith [sq_nonneg ‖(z - (e : (V × V) →ₗ[ℂ] WithLp 2 (V × V)) p).snd‖])
  · refine lt_of_le_of_lt ?_ hzb
    rw [dist_eq_norm]
    have := prod_norm_sq_eq_of_L2 (z - (e : (V × V) →ₗ[ℂ] WithLp 2 (V × V)) p)
    have h2 : (z - (e : (V × V) →ₗ[ℂ] WithLp 2 (V × V)) p).snd = T†† h - T x := by
      simp [z, e, hx2]
    rw [h2] at this
    exact le_of_pow_le_pow_left₀ two_ne_zero (norm_nonneg _)
      (by rw [this]; nlinarith [sq_nonneg ‖(z - (e : (V × V) →ₗ[ℂ] WithLp 2 (V × V)) p).fst‖])

end Closure

/-- Boundary values vanish on `𝒟(ℒ**)`. -/
theorem IsBoundaryValue.eq_zero_of_mem (hY : IsOpen Y) (hq : ContinuousOn q Y)
    {B : (minOp Y q)†.domain →ₗ[ℂ] ℂ} (hB : IsBoundaryValue Y q B) (f : (minOp Y q)†.domain)
    (hf : (f : L2X Y) ∈ (minOp Y q)††.domain) : B f = 0 := by
  have hT := isSymmetricDLMF_minOp hY hq
  have hle := hT.le_adjoint_adjoint
  obtain ⟨C, hC⟩ := hB.1
  by_contra hne
  have hpos : 0 < ‖B f‖ := norm_pos_iff.mpr hne
  set ε := ‖B f‖ / (2 * (|C| + 1))
  have hε : 0 < ε := by positivity
  obtain ⟨φ, h1, h2⟩ := hT.approx_adjoint_adjoint ⟨f, hf⟩ hε
  set φ' : (minOp Y q)†.domain := ⟨φ, hT.le_adjoint.1 φ.2⟩
  have hBφ : B φ' = 0 := hB.2 φ' φ.2
  have hTφ : (minOp Y q)† φ' = minOp Y q φ := (hT.le_adjoint.2 rfl).symm
  have hTf : (minOp Y q)† f = (minOp Y q)†† ⟨f, hf⟩ := (hle.2.2 (x := ⟨f, hf⟩) rfl).symm
  have hb := hC (f - φ')
  rw [_root_.map_sub, hBφ, sub_zero, LinearPMap.map_sub, hTφ, hTf] at hb
  have : ‖B f‖ ≤ |C| * (ε + ε) := by
    refine hb.trans ?_
    refine (mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)).trans ?_
    exact mul_le_mul_of_nonneg_left (add_le_add h1.le h2.le) (abs_nonneg _)
  have : |C| * (ε + ε) < ‖B f‖ := by
    simp only [ε]
    rw [show |C| * (‖B f‖ / (2 * (|C| + 1)) + ‖B f‖ / (2 * (|C| + 1))) =
      ‖B f‖ * (|C| / (|C| + 1)) by field_simp; ring]
    exact mul_lt_of_lt_one_right hpos ((div_lt_one (by positivity)).mpr (by linarith))
  linarith

end Azurite.DLMF
