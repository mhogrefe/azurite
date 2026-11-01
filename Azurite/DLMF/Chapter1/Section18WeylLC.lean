/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter1.Section18WeylBV2

/-!
# DLMF §1.18(ix): boundary values at a limit-circle endpoint

* `wronskian_sub_eq_integral`, `lagrange_solution`, `lagrange_domain`: Lagrange's identity for
  functions whose derivative is a primitive of a locally integrable function.
* `wronskianBV`: the Wronskian boundary value `W_v(f) = lim_{x → a} [f v′ − f′ v](x)` against a
  solution `v ∈ L²` near `a` (`tendsto_wronskianBV`, `wronskianBV_isBoundaryValue`).
* `inner_adjoint_eq_of_wronskian`: Plücker's identity
  `[f̄, g][P, Q] = [f̄, P][g, Q] − [f̄, Q][g, P]` makes the boundary form vanish when the
  Wronskians against `P, Q` vanish at `a`.
* `boundaryValuesLeft`, `boundaryValuesRight`: the boundary values at `a`, `b`.
* `dlmf_1_18_ix_boundaryValuesLeft_LP` (`n₁ = 1`: none) and
  `dlmf_1_18_ix_boundaryValuesLeft_LC` (`n₁ = 2`: a two-dimensional class, spanned by the
  Wronskians against two independent solutions).
-/

open Set Filter Topology MeasureTheory LinearPMap
open scoped InnerProductSpace ComplexConjugate ContDiff

namespace Azurite.DLMF

/-! ### Lagrange's identity -/

/-- `∫_α^β (∫_α^t k) ψ′(t) dt = ∫_α^β k(s)(ψ(β) − ψ(s)) ds`, with hypotheses on `[α, β]` only. -/
theorem integral_primitive_mul_deriv_on {k ψ ψ' : ℝ → ℂ} {α β : ℝ} (hαβ : α ≤ β)
    (hk : IntervalIntegrable k volume α β) (hψ : ∀ t ∈ Icc α β, HasDerivAt ψ (ψ' t) t)
    (hψ' : ContinuousOn ψ' (Icc α β)) :
    ∫ t in α..β, (∫ s in α..t, k s) * ψ' t = ∫ s in α..β, k s * (ψ β - ψ s) := by
  set S := Ioc α β
  have hkS : IntegrableOn k S := (intervalIntegrable_iff_integrableOn_Ioc_of_le hαβ).mp hk
  have h1 : ∀ t ∈ S, ∫ s in α..t, k s = ∫ s in S, (Iic t).indicator k s := fun t ht => by
    have hset : Ioc α t = S ∩ Iic t := by
      ext s
      simp only [S, mem_Ioc, mem_inter_iff, mem_Iic]
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨⟨h1, h2.trans ht.2⟩, h2⟩
      · rintro ⟨⟨h1, -⟩, h2⟩; exact ⟨h1, h2⟩
    rw [intervalIntegral.integral_of_le ht.1.le, setIntegral_indicator measurableSet_Iic, hset]
  have hL : ∫ t in α..β, (∫ s in α..t, k s) * ψ' t =
      ∫ t in S, ∫ s in S, {p : ℝ × ℝ | p.2 ≤ p.1}.indicator
        (fun p => k p.2 * ψ' p.1) (t, s) := by
    rw [intervalIntegral.integral_of_le hαβ]
    refine setIntegral_congr_fun measurableSet_Ioc fun t ht => ?_
    rw [h1 t ht, ← integral_mul_const]
    congr 1
    funext s
    by_cases hst : s ≤ t <;> simp [indicator, hst]
  have hψS : IntegrableOn ψ' S := (hψ'.integrableOn_Icc).mono_set Ioc_subset_Icc_self
  have hint : Integrable (Function.uncurry fun t s => {p : ℝ × ℝ | p.2 ≤ p.1}.indicator
      (fun p => k p.2 * ψ' p.1) (t, s)) ((volume.restrict S).prod (volume.restrict S)) := by
    refine (hψS.norm.mul_prod hkS.norm).mono' ?_ (ae_of_all _ fun p => ?_)
    · refine AEStronglyMeasurable.indicator ?_ (measurableSet_le measurable_snd measurable_fst)
      have hk2 : AEStronglyMeasurable (fun p : ℝ × ℝ => k p.2)
          ((volume.restrict S).prod (volume.restrict S)) := hkS.aestronglyMeasurable.comp_snd
      exact hk2.mul hψS.aestronglyMeasurable.comp_fst
    · simp only [Function.uncurry]
      by_cases h : p.2 ≤ p.1
      · simp only [indicator, mem_ofPred_eq, h, ↓reduceIte, norm_mul]
        exact (mul_comm _ _).le
      · simp only [indicator, mem_ofPred_eq, h, ↓reduceIte, norm_zero]
        positivity
  rw [hL, integral_integral_swap hint, intervalIntegral.integral_of_le hαβ]
  refine setIntegral_congr_fun measurableSet_Ioc fun s hs => ?_
  have h2 : ∫ t in S, {p : ℝ × ℝ | p.2 ≤ p.1}.indicator (fun p => k p.2 * ψ' p.1) (t, s) =
      k s * ∫ t in S, (Ici s).indicator ψ' t := by
    rw [← integral_const_mul]
    congr 1
    funext t
    by_cases hst : s ≤ t <;> simp [indicator, hst]
  rw [h2, setIntegral_indicator measurableSet_Ici]
  congr 1
  have h3 : S ∩ Ici s = Icc s β := by
    ext t
    simp only [S, mem_inter_iff, mem_Ioc, mem_Ici, mem_Icc]
    constructor
    · rintro ⟨⟨-, h2⟩, h3⟩; exact ⟨h3, h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨⟨hs.1.trans_le h1, h2⟩, h1⟩
  have hsub : Icc s β ⊆ Icc α β := Icc_subset_Icc_left hs.1.le
  rw [h3, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hs.2,
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t ht => hψ t (hsub (by rwa [uIcc_of_le hs.2] at ht)))
      ((hψ'.mono hsub).intervalIntegrable_of_Icc hs.2)]

/-- **Lagrange's identity**: if `A′ = A′(x₁) + ∫ k_A` and `B′ = B′(x₁) + ∫ k_B` on `[x₁, x₂]`, then
`[AB′ − A′B]_{x₁}^{x₂} = ∫_{x₁}^{x₂} (A k_B − k_A B)`. -/
theorem wronskian_sub_eq_integral {A A' B B' kA kB : ℝ → ℂ} {x₁ x₂ : ℝ} (h : x₁ ≤ x₂)
    (hA : ∀ t ∈ Icc x₁ x₂, HasDerivAt A (A' t) t) (hB : ∀ t ∈ Icc x₁ x₂, HasDerivAt B (B' t) t)
    (hA'c : ContinuousOn A' (Icc x₁ x₂)) (hB'c : ContinuousOn B' (Icc x₁ x₂))
    (hkA : IntervalIntegrable kA volume x₁ x₂) (hkB : IntervalIntegrable kB volume x₁ x₂)
    (hA' : ∀ t ∈ Icc x₁ x₂, A' t = A' x₁ + ∫ s in x₁..t, kA s)
    (hB' : ∀ t ∈ Icc x₁ x₂, B' t = B' x₁ + ∫ s in x₁..t, kB s) :
    (A x₂ * B' x₂ - A' x₂ * B x₂) - (A x₁ * B' x₁ - A' x₁ * B x₁) =
      ∫ s in x₁..x₂, (A s * kB s - kA s * B s) := by
  have hAc : ContinuousOn A (Icc x₁ x₂) := fun t ht => (hA t ht).continuousAt.continuousWithinAt
  have hBc : ContinuousOn B (Icc x₁ x₂) := fun t ht => (hB t ht).continuousAt.continuousWithinAt
  have ii : ∀ u : ℝ → ℂ, ContinuousOn u (Icc x₁ x₂) → IntervalIntegrable u volume x₁ x₂ :=
    fun u hu => hu.intervalIntegrable_of_Icc h
  have imul : ∀ {k u : ℝ → ℂ}, IntervalIntegrable k volume x₁ x₂ → ContinuousOn u (Icc x₁ x₂) →
      IntervalIntegrable (fun s => k s * u s) volume x₁ x₂ := fun hk hu =>
    hk.mul_continuousOn (by rwa [uIcc_of_le h])
  have hAx : ∫ s in x₁..x₂, kA s = A' x₂ - A' x₁ := by
    rw [hA' x₂ ⟨h, le_rfl⟩]; ring
  have hBx : ∫ s in x₁..x₂, kB s = B' x₂ - B' x₁ := by
    rw [hB' x₂ ⟨h, le_rfl⟩]; ring
  -- `∫ A′B′` computed in two ways
  have key : ∀ {C' k : ℝ → ℂ} {D D' : ℝ → ℂ}, ContinuousOn C' (Icc x₁ x₂) →
      (∀ t ∈ Icc x₁ x₂, HasDerivAt D (D' t) t) → ContinuousOn D' (Icc x₁ x₂) →
      ContinuousOn D (Icc x₁ x₂) → IntervalIntegrable k volume x₁ x₂ →
      (∀ t ∈ Icc x₁ x₂, C' t = C' x₁ + ∫ s in x₁..t, k s) →
      ∫ t in x₁..x₂, C' t * D' t = C' x₁ * (D x₂ - D x₁) +
        (D x₂ * (∫ s in x₁..x₂, k s) - ∫ s in x₁..x₂, k s * D s) := by
    intro C' k D D' hC'c hD hD'c hDc hk hC'
    have hpr : ContinuousOn (fun t => ∫ s in x₁..t, k s) (Icc x₁ x₂) := by
      have := intervalIntegral.continuousOn_primitive_interval' (μ := volume) (a := x₁) hk
        (by rw [uIcc_of_le h]; exact ⟨le_rfl, h⟩)
      rwa [uIcc_of_le h] at this
    rw [intervalIntegral.integral_congr (g := fun t => C' x₁ * D' t +
      (∫ s in x₁..t, k s) * D' t) fun t ht => by
        rw [hC' t (by rwa [uIcc_of_le h] at ht)]; ring,
      intervalIntegral.integral_add (f := fun t => C' x₁ * D' t)
        (g := fun t => (∫ s in x₁..t, k s) * D' t) ((ii _ hD'c).const_mul _)
        (ii _ (hpr.mul hD'c)),
      integral_primitive_mul_deriv_on h hk hD hD'c, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun t ht => hD t (by rwa [uIcc_of_le h] at ht)) (ii _ hD'c),
      intervalIntegral.integral_congr (g := fun s => D x₂ * k s - k s * D s)
        fun t _ => by ring,
      intervalIntegral.integral_sub (hk.const_mul _) (imul hk hDc),
      intervalIntegral.integral_const_mul]
  have e1 := key hA'c hB hB'c hBc hkA hA'
  have e2 := key hB'c hA hA'c hAc hkB hB'
  rw [intervalIntegral.integral_congr (g := fun t => A' t * B' t) fun t _ => mul_comm _ _] at e2
  rw [intervalIntegral.integral_congr (g := fun s => kB s * A s - kA s * B s)
      fun t _ => by ring, intervalIntegral.integral_sub (imul hkB hAc) (imul hkA hBc)]
  rw [hAx] at e1
  rw [hBx] at e2
  linear_combination e1 - e2

/-! ### Lagrange's identity for `𝒟(ℒ*)` -/

variable {X : Set ℝ} {q : ℝ → ℝ}

section Lagrange

variable (hX : IsOpen X) (hXc : X.OrdConnected) (hne : X.Nonempty) (hq : ContinuousOn q X)
include hX hXc hne hq

theorem intervalIntegrable_maxRep_kernel (f : (minOp X q)†.domain) {x₁ x₂ : ℝ} (hx₁ : x₁ ∈ X)
    (hx₂ : x₂ ∈ X) :
    IntervalIntegrable (fun t => (q t : ℂ) * maxRep hX hXc hne hq f t -
      (((minOp X q)† f : L2X X) : ℝ → ℂ) t) volume x₁ x₂ := by
  have hloc : LocallyIntegrableOn (fun t => (q t : ℂ) * maxRep hX hXc hne hq f t -
      (((minOp X q)† f : L2X X) : ℝ → ℂ) t) X :=
    (((Complex.continuous_ofReal.comp_continuousOn hq).mul
      (continuousOn_maxRep hX hXc hne hq f)).locallyIntegrableOn hX.measurableSet).sub
      (L2X.locallyIntegrableOn hX _)
  exact (hloc.integrableOn_compact_subset (hXc.uIcc_subset hx₁ hx₂) isCompact_uIcc)
    |>.intervalIntegrable

/-- **Lagrange's identity** for `f ∈ 𝒟(ℒ*)` and a solution of `ℒv = zv`:
`[f v′ − f′ v]_{x₁}^{x₂} = ∫_{x₁}^{x₂} (ℒ*f − z f) v`. -/
theorem lagrange_solution (f : (minOp X q)†.domain) {z : ℂ} {v v' : ℝ → ℂ}
    (hv : ∀ x ∈ X, HasDerivAt v (v' x) x ∧ HasDerivAt v' (((q x : ℂ) - z) * v x) x)
    {x₁ x₂ : ℝ} (hx₁ : x₁ ∈ X) (hx₂ : x₂ ∈ X) (h : x₁ ≤ x₂) :
    (maxRep hX hXc hne hq f x₂ * v' x₂ - maxRepD hX hXc hne hq f x₂ * v x₂) -
        (maxRep hX hXc hne hq f x₁ * v' x₁ - maxRepD hX hXc hne hq f x₁ * v x₁) =
      ∫ s in x₁..x₂, ((((minOp X q)† f : L2X X) : ℝ → ℂ) s -
        z * maxRep hX hXc hne hq f s) * v s := by
  obtain ⟨-, hF, hD⟩ := maxRep_spec hX hXc hne hq f
  have hI : Icc x₁ x₂ ⊆ X := hXc.out hx₁ hx₂
  have hvc : ContinuousOn v X := fun x hx => (hv x hx).1.continuousAt.continuousWithinAt
  have hv'c : ContinuousOn v' X := fun x hx => (hv x hx).2.continuousAt.continuousWithinAt
  have hkv : ContinuousOn (fun x => ((q x : ℂ) - z) * v x) X :=
    ((Complex.continuous_ofReal.comp_continuousOn hq).sub continuousOn_const).mul hvc
  have hW := wronskian_sub_eq_integral h (fun t ht => hF t (hI ht)) (fun t ht => (hv t (hI ht)).1)
    ((continuousOn_maxRepD hX hXc hne hq f).mono hI) (hv'c.mono hI)
    (intervalIntegrable_maxRep_kernel hX hXc hne hq f hx₁ hx₂)
    ((hkv.mono hI).intervalIntegrable_of_Icc h)
    (fun t ht => hD x₁ hx₁ t (hI ht))
    (fun t ht => by
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun y hy => (hv y (hI (Icc_subset_Icc_right ht.2 (by rwa [uIcc_of_le ht.1] at hy)))).2)
        ((hkv.mono ((Icc_subset_Icc_right ht.2).trans hI)).intervalIntegrable_of_Icc ht.1)]
      ring)
  rw [hW]
  exact intervalIntegral.integral_congr fun t _ => by ring

/-- **Lagrange's identity** for `f₁, f₂ ∈ 𝒟(ℒ*)`:
`[f̄₁ f₂′ − f̄₁′ f₂]_{x₁}^{x₂} = ∫_{x₁}^{x₂} (conj(ℒ*f₁) f₂ − f̄₁ ℒ*f₂)`. -/
theorem lagrange_domain (f₁ f₂ : (minOp X q)†.domain) {x₁ x₂ : ℝ} (hx₁ : x₁ ∈ X) (hx₂ : x₂ ∈ X)
    (h : x₁ ≤ x₂) :
    (conj (maxRep hX hXc hne hq f₁ x₂) * maxRepD hX hXc hne hq f₂ x₂ -
        conj (maxRepD hX hXc hne hq f₁ x₂) * maxRep hX hXc hne hq f₂ x₂) -
      (conj (maxRep hX hXc hne hq f₁ x₁) * maxRepD hX hXc hne hq f₂ x₁ -
        conj (maxRepD hX hXc hne hq f₁ x₁) * maxRep hX hXc hne hq f₂ x₁) =
      ∫ s in x₁..x₂, (conj ((((minOp X q)† f₁ : L2X X) : ℝ → ℂ) s) *
          maxRep hX hXc hne hq f₂ s -
        conj (maxRep hX hXc hne hq f₁ s) * (((minOp X q)† f₂ : L2X X) : ℝ → ℂ) s) := by
  obtain ⟨-, hF₁, hD₁⟩ := maxRep_spec hX hXc hne hq f₁
  obtain ⟨-, hF₂, hD₂⟩ := maxRep_spec hX hXc hne hq f₂
  have hI : Icc x₁ x₂ ⊆ X := hXc.out hx₁ hx₂
  have hk₁ := intervalIntegrable_maxRep_kernel hX hXc hne hq f₁ hx₁ hx₂
  have hW := wronskian_sub_eq_integral h
    (A := fun x => conj (maxRep hX hXc hne hq f₁ x))
    (A' := fun x => conj (maxRepD hX hXc hne hq f₁ x))
    (fun t ht => by simpa [Complex.star_def] using (hF₁ t (hI ht)).star)
    (fun t ht => hF₂ t (hI ht))
    ((Complex.continuous_conj.comp_continuousOn
      (continuousOn_maxRepD hX hXc hne hq f₁)).mono hI)
    ((continuousOn_maxRepD hX hXc hne hq f₂).mono hI)
    (kA := fun t => conj ((q t : ℂ) * maxRep hX hXc hne hq f₁ t -
      (((minOp X q)† f₁ : L2X X) : ℝ → ℂ) t))
    (by
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le h] at hk₁ ⊢
      exact (Complex.conjCLE : ℂ →L[ℝ] ℂ).integrable_comp hk₁)
    (intervalIntegrable_maxRep_kernel hX hXc hne hq f₂ hx₁ hx₂)
    (fun t ht => by
      rw [hD₁ x₁ hx₁ t (hI ht), _root_.map_add, intervalIntegral.integral_of_le ht.1,
        intervalIntegral.integral_of_le ht.1, integral_conj])
    (fun t ht => hD₂ x₁ hx₁ t (hI ht))
  rw [hW]
  refine intervalIntegral.integral_congr fun t _ => ?_
  simp only [_root_.map_sub, map_mul, Complex.conj_ofReal]
  ring

end Lagrange

/-! ### Integrals near the left end -/

theorem mem_leftEnd {d : ℝ} (hd : d ∈ X) : X ∩ Iio d ∈ leftEnd X :=
  mem_iInf_of_mem d (mem_iInf_of_mem hd (mem_principal_self _))

/-- `∫_{X ∩ (−∞, x)} H → 0` as `x → a`. -/
theorem tendsto_setIntegral_leftEnd (hX : IsOpen X) (hXc : X.OrdConnected) {H : ℝ → ℂ} {c : ℝ}
    (hc : c ∈ X) (hH : IntegrableOn H (X ∩ Iio c)) :
    Tendsto (fun x => ∫ t in X ∩ Iio x, H t) (leftEnd X) (𝓝 0) := by
  obtain ⟨xs, hxs, hlim⟩ := exists_seq_leftEnd hX hXc ⟨c, hc⟩
  set μ := volume.restrict (X ∩ Iio c)
  have hG : Tendsto (fun n => ∫ t, (Iio (xs n)).indicator (fun t => ‖H t‖) t ∂μ) atTop
      (𝓝 (∫ _t, (0 : ℝ) ∂μ)) := by
    refine tendsto_integral_of_dominated_convergence (fun t => ‖H t‖)
      (fun n => hH.norm.aestronglyMeasurable.indicator measurableSet_Iio) hH.norm
      (fun n => ae_of_all _ fun t => ?_) ?_
    · rw [Real.norm_eq_abs, abs_of_nonneg (indicator_nonneg (fun _ _ => norm_nonneg _) _)]
      exact indicator_le_self' (fun _ _ => norm_nonneg _) t
    · filter_upwards [ae_restrict_mem ((hX.inter isOpen_Iio).measurableSet)] with t ht
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [hlim (mem_leftEnd ht.1)] with n hn
      exact (indicator_of_notMem (s := Iio (xs n)) (fun h : t < xs n => lt_asymm h hn.2) _).symm
  rw [integral_zero] at hG
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp hG) ε hε
  have hNN := hN N le_rfl
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (integral_nonneg fun _ =>
    indicator_nonneg (fun _ _ => norm_nonneg _) _)] at hNN
  filter_upwards [mem_leftEnd hc, mem_leftEnd (hxs N)] with x hx hxN
  rw [dist_zero_right]
  refine (norm_integral_le_integral_norm _).trans_lt (lt_of_le_of_lt ?_ hNN)
  have hsub : X ∩ Iio x = X ∩ Iio c ∩ Iio x := by
    ext t; simp only [mem_inter_iff, mem_Iio]
    exact ⟨fun h => ⟨⟨h.1, h.2.trans hx.2⟩, h.2⟩, fun h => ⟨h.1.1, h.2⟩⟩
  rw [hsub, ← setIntegral_indicator measurableSet_Iio]
  refine integral_mono (hH.norm.indicator measurableSet_Iio)
    (hH.norm.indicator measurableSet_Iio) fun t => ?_
  exact indicator_le_indicator_of_subset (Iio_subset_Iio hxN.2.le)
    (fun _ => norm_nonneg _) t

/-- Splitting `∫_{X ∩ (−∞, c)} = ∫_{X ∩ (−∞, x)} + ∫_x^c`. -/
theorem setIntegral_split_left (hXc : X.OrdConnected) {H : ℝ → ℂ} {c x : ℝ} (hc : c ∈ X)
    (hx : x ∈ X) (hxc : x ≤ c) (hH : IntegrableOn H (X ∩ Iio c)) :
    ∫ t in X ∩ Iio c, H t = (∫ t in X ∩ Iio x, H t) + ∫ t in x..c, H t := by
  have hI : Icc x c ⊆ X := hXc.out hx hc
  have hset : X ∩ Iio c = (X ∩ Iio x) ∪ Ico x c := by
    ext t
    simp only [mem_inter_iff, mem_Iio, mem_union, mem_Ico]
    constructor
    · rintro ⟨h1, h2⟩
      rcases lt_or_ge t x with h | h
      · exact Or.inl ⟨h1, h⟩
      · exact Or.inr ⟨h, h2⟩
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · exact ⟨h1, h2.trans_le hxc⟩
      · exact ⟨hI ⟨h1, h2.le⟩, h2⟩
  have hd : Disjoint (X ∩ Iio x) (Ico x c) :=
    Set.disjoint_left.mpr fun t h1 h2 => absurd h1.2 (not_lt.mpr h2.1)
  rw [hset, setIntegral_union hd measurableSet_Ico (hH.mono_set (hset ▸ subset_union_left))
    (hH.mono_set (hset ▸ subset_union_right)), integral_Ico_eq_integral_Ioo,
    intervalIntegral.integral_of_le hxc, integral_Ioc_eq_integral_Ioo]

/-! ### Wronskian boundary values at the left end -/

section Wronskian

variable (hX : IsOpen X) (hXc : X.OrdConnected) (hne : X.Nonempty) (hq : ContinuousOn q X)
  {c : ℝ} (hc : c ∈ X) (z : ℂ) {v : ℝ → ℂ} (v' : ℝ → ℂ)
  (hv : ∀ x ∈ X, HasDerivAt v (v' x) x ∧ HasDerivAt v' (((q x : ℂ) - z) * v x) x)
  (hv2 : MemLp v 2 (volume.restrict (X ∩ Iio c)))

include hX hv2 in
theorem memLp_wronskianKernel :
    MemLp ((X ∩ Iio c).indicator fun x => conj (v x)) 2 (volume.restrict X) := by
  rw [memLp_indicator_iff_restrict ((hX.inter isOpen_Iio).measurableSet),
    Measure.restrict_restrict_of_subset inter_subset_left]
  exact hv2.star

/-- The kernel `1_{X ∩ (−∞, c)} v̄` of the integral part of the Wronskian boundary value. -/
noncomputable def wronskianKernel : L2X X := (memLp_wronskianKernel hX hv2).toLp

/-- The **Wronskian boundary value** at `a`:
`W_v(f) = [f v′ − f′ v](c) − ∫_{a}^{c} (ℒ*f − z f) v = lim_{x → a} [f v′ − f′ v](x)`. -/
noncomputable def wronskianBV : (minOp X q)†.domain →ₗ[ℂ] ℂ :=
  (v' c • LinearMap.fst ℂ ℂ ℂ - v c • LinearMap.snd ℂ ℂ ℂ) ∘ₗ evalRep hX hXc hne hq hc -
    (innerₛₗ ℂ (wronskianKernel hX hv2)) ∘ₗ
      ((minOp X q)†.toFun - z • (minOp X q)†.domain.subtype)

theorem wronskianBV_apply (f : (minOp X q)†.domain) :
    wronskianBV hX hXc hne hq hc z v' hv2 f =
      (maxRep hX hXc hne hq f c * v' c - maxRepD hX hXc hne hq f c * v c) -
        ∫ x in X ∩ Iio c, ((((minOp X q)† f : L2X X) : ℝ → ℂ) x -
          z * maxRep hX hXc hne hq f x) * v x := by
  obtain ⟨hwF, -, -⟩ := maxRep_spec hX hXc hne hq f
  simp only [wronskianBV, LinearMap.sub_apply, LinearMap.comp_apply, evalRep,
    LinearMap.coe_mk, AddHom.coe_mk, LinearMap.smul_apply, LinearMap.coe_fst,
    LinearMap.coe_snd, smul_eq_mul, innerₛₗ_apply_apply, Submodule.subtype_apply]
  congr 1
  · ring
  rw [inner_L2X, ← inter_eq_right.mpr (inter_subset_left : X ∩ Iio c ⊆ X),
    ← setIntegral_indicator ((hX.inter isOpen_Iio).measurableSet)]
  refine integral_congr_ae ?_
  filter_upwards [(memLp_wronskianKernel hX hv2).coeFn_toLp,
    Lp.coeFn_sub ((minOp X q)† f) (z • (f : L2X X)), Lp.coeFn_smul z (f : L2X X), hwF]
    with x h1 h2 h3 h4
  change conj (((memLp_wronskianKernel hX hv2).toLp : ℝ → ℂ) x) *
    ((((minOp X q)† f : L2X X) - z • (f : L2X X) : L2X X) : ℝ → ℂ) x = _
  rw [h1, h2, Pi.sub_apply, h3, Pi.smul_apply, h4, smul_eq_mul]
  by_cases hx : x ∈ X ∩ Iio c
  · simp only [indicator_of_mem hx, Complex.conj_conj]; ring
  · simp [indicator_of_notMem hx]

include hv2 in
theorem integrableOn_wronskian_integrand (f : (minOp X q)†.domain) :
    IntegrableOn (fun x => ((((minOp X q)† f : L2X X) : ℝ → ℂ) x -
      z * maxRep hX hXc hne hq f x) * v x) (X ∩ Iio c) := by
  obtain ⟨hwF, -, -⟩ := maxRep_spec hX hXc hne hq f
  have hm := memLp_restrict_sub (inter_subset_left : X ∩ Iio c ⊆ X)
    (((minOp X q)† f : L2X X) - z • (f : L2X X))
  have hm' : MemLp (fun x => (((minOp X q)† f : L2X X) : ℝ → ℂ) x -
      z * maxRep hX hXc hne hq f x) 2 (volume.restrict (X ∩ Iio c)) := by
    refine hm.ae_eq ?_
    have hs : X ∩ Iio c ⊆ X := inter_subset_left
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hs
        (Lp.coeFn_sub ((minOp X q)† f) (z • (f : L2X X))),
      ae_restrict_of_ae_restrict_of_subset hs (Lp.coeFn_smul z (f : L2X X)),
      ae_restrict_of_ae_restrict_of_subset hs hwF] with x h2 h3 h4
    rw [h2, Pi.sub_apply, h3, Pi.smul_apply, h4, smul_eq_mul]
  exact hm'.integrable_mul hv2

include hv in
/-- `W_v(f) = [f v′ − f′ v](x) − ∫_a^x (ℒ*f − z f) v` for every `x ∈ X`, `x ≤ c`. -/
theorem wronskianBV_eq_at (f : (minOp X q)†.domain) {x : ℝ} (hx : x ∈ X) (hxc : x ≤ c) :
    wronskianBV hX hXc hne hq hc z v' hv2 f =
      (maxRep hX hXc hne hq f x * v' x - maxRepD hX hXc hne hq f x * v x) -
        ∫ y in X ∩ Iio x, ((((minOp X q)† f : L2X X) : ℝ → ℂ) y -
          z * maxRep hX hXc hne hq f y) * v y := by
  have hH := integrableOn_wronskian_integrand hX hXc hne hq z hv2 f
  have hL := lagrange_solution hX hXc hne hq f hv hx hc hxc
  rw [wronskianBV_apply hX hXc hne hq hc z v' hv2, setIntegral_split_left hXc hc hx hxc hH, ← hL]
  ring

include hv in
/-- `W_v(f) = lim_{x → a} [f v′ − f′ v](x)`. -/
theorem tendsto_wronskianBV (f : (minOp X q)†.domain) :
    Tendsto (fun x => v' x * maxRep hX hXc hne hq f x + (-v x) * maxRepD hX hXc hne hq f x)
      (leftEnd X) (𝓝 (wronskianBV hX hXc hne hq hc z v' hv2 f)) := by
  have hH := integrableOn_wronskian_integrand hX hXc hne hq z hv2 f
  have ht := (tendsto_setIntegral_leftEnd hX hXc hc hH).const_add
    (wronskianBV hX hXc hne hq hc z v' hv2 f)
  rw [add_zero] at ht
  refine ht.congr' ?_
  filter_upwards [mem_leftEnd hc] with x hx
  rw [wronskianBV_eq_at hX hXc hne hq hc z v' hv hv2 f hx.1 hx.2.le]
  ring

include hv in
/-- The Wronskian boundary values are boundary values at `a`. -/
theorem wronskianBV_isBoundaryValue :
    IsBoundaryValue X q (wronskianBV hX hXc hne hq hc z v' hv2) ∧
      ∀ f, VanishesNear X q (fun d => X ∩ Iio d) f → wronskianBV hX hXc hne hq hc z v' hv2 f = 0 :=
  dlmf_1_18_71_left hX hXc hne hq
    ⟨fun x => v' x, fun x => -v x, tendsto_wronskianBV hX hXc hne hq hc z v' hv hv2⟩

end Wronskian

/-! ### Cut-off solutions -/

theorem solution_deriv_eq (hXc : X.OrdConnected) (hq : ContinuousOn q X) {z : ℂ} {u u' : ℝ → ℂ}
    (hu : ∀ x ∈ X, HasDerivAt u (u' x) x ∧ HasDerivAt u' (((q x : ℂ) - z) * u x) x)
    {x₁ t : ℝ} (hx₁ : x₁ ∈ X) (ht : t ∈ X) (h : x₁ ≤ t) :
    u' t = u' x₁ + ∫ s in x₁..t, ((q s : ℂ) - z) * u s := by
  have hI : Icc x₁ t ⊆ X := hXc.out hx₁ ht
  have huc : ContinuousOn u X := fun x hx => (hu x hx).1.continuousAt.continuousWithinAt
  have hk : ContinuousOn (fun x => ((q x : ℂ) - z) * u x) X :=
    ((Complex.continuous_ofReal.comp_continuousOn hq).sub continuousOn_const).mul huc
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun y hy => (hu y (hI (by rwa [uIcc_of_le h] at hy))).2)
    ((hk.mono hI).intervalIntegrable_of_Icc h)]
  ring

/-- The Wronskian of two solutions of `ℒu = zu` is constant. -/
theorem wronskian_const (hXc : X.OrdConnected) (hq : ContinuousOn q X) {z : ℂ}
    {u u' v v' : ℝ → ℂ}
    (hu : ∀ x ∈ X, HasDerivAt u (u' x) x ∧ HasDerivAt u' (((q x : ℂ) - z) * u x) x)
    (hv : ∀ x ∈ X, HasDerivAt v (v' x) x ∧ HasDerivAt v' (((q x : ℂ) - z) * v x) x)
    {x₁ x₂ : ℝ} (hx₁ : x₁ ∈ X) (hx₂ : x₂ ∈ X) :
    u x₁ * v' x₁ - u' x₁ * v x₁ = u x₂ * v' x₂ - u' x₂ * v x₂ := by
  wlog h : x₁ ≤ x₂ generalizing x₁ x₂
  · exact (this hx₂ hx₁ (le_of_not_ge h)).symm
  have hI : Icc x₁ x₂ ⊆ X := hXc.out hx₁ hx₂
  have huc : ContinuousOn u X := fun x hx => (hu x hx).1.continuousAt.continuousWithinAt
  have hvc : ContinuousOn v X := fun x hx => (hv x hx).1.continuousAt.continuousWithinAt
  have hqc : ContinuousOn (fun x => (q x : ℂ) - z) X :=
    (Complex.continuous_ofReal.comp_continuousOn hq).sub continuousOn_const
  have hW := wronskian_sub_eq_integral h (fun t ht => (hu t (hI ht)).1)
    (fun t ht => (hv t (hI ht)).1)
    (fun t ht => (hu t (hI ht)).2.continuousAt.continuousWithinAt)
    (fun t ht => (hv t (hI ht)).2.continuousAt.continuousWithinAt)
    (((hqc.mul huc).mono hI).intervalIntegrable_of_Icc h)
    (((hqc.mul hvc).mono hI).intervalIntegrable_of_Icc h)
    (fun t ht => solution_deriv_eq hXc hq hu hx₁ (hI ht) ht.1)
    (fun t ht => solution_deriv_eq hXc hq hv hx₁ (hI ht) ht.1)
  rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℂ)) fun t _ => by
      simp only [Pi.mul_apply]; ring,
    intervalIntegral.integral_zero, sub_eq_zero] at hW
  exact hW.symm

/-- A function supported in `x < c`, bounded by an `L²(X ∩ (−∞, c))` function, is in `L²(X)`. -/
theorem memLp_cutoff_left {χ : ℝ → ℝ} (hχ : Continuous χ) (hχb : ∀ x, |χ x| ≤ 1) {c : ℝ}
    (hχ0 : ∀ x, c ≤ x → χ x = 0) (hX : MeasurableSet X) {w : ℝ → ℂ}
    (hw : MemLp w 2 (volume.restrict (X ∩ Iio c))) :
    MemLp (fun x => (χ x : ℂ) * w x) 2 (volume.restrict X) := by
  have hm : MeasurableSet (X ∩ Iio c) := hX.inter measurableSet_Iio
  have heq : (fun x => (χ x : ℂ) * w x) =ᵐ[volume.restrict X]
      (X ∩ Iio c).indicator (fun x => (χ x : ℂ) * w x) := by
    filter_upwards [ae_restrict_mem hX] with x hx
    by_cases h : x < c
    · rw [indicator_of_mem (show x ∈ X ∩ Iio c from ⟨hx, h⟩)]
    · rw [indicator_of_notMem fun h' => h h'.2, hχ0 x (le_of_not_gt h)]; simp
  refine MemLp.ae_eq heq.symm ?_
  rw [memLp_indicator_iff_restrict hm, Measure.restrict_restrict_of_subset inter_subset_left]
  refine hw.of_le ((Complex.continuous_ofReal.comp hχ).aestronglyMeasurable.mul
    hw.aestronglyMeasurable)
    (ae_of_all _ fun x => ?_)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_of_le_one_left (norm_nonneg _) (hχb x)

/-- A solution `u ∈ L²(X ∩ (−∞, c))` cut off near `c` is an element `g ∈ 𝒟(ℒ*)` agreeing with `u`
near `a`. -/
theorem exists_cutoff_solution (hX : IsOpen X) (hXc : X.OrdConnected) (hq : ContinuousOn q X)
    {c : ℝ} (hc : c ∈ X) {z : ℂ} {u u' : ℝ → ℂ}
    (hu : ∀ x ∈ X, HasDerivAt u (u' x) x ∧ HasDerivAt u' (((q x : ℂ) - z) * u x) x)
    (hu2 : MemLp u 2 (volume.restrict (X ∩ Iio c))) :
    ∃ g : (minOp X q)†.domain, ∃ x ∈ X, x < c ∧
      EqOn (maxRep hX hXc ⟨c, hc⟩ hq g) u (X ∩ Iic x) ∧
      maxRepD hX hXc ⟨c, hc⟩ hq g x = u' x ∧
      (((minOp X q)† g : L2X X) : ℝ → ℂ) =ᵐ[volume.restrict (X ∩ Iio x)] fun y => z * u y := by
  have hne : X.Nonempty := ⟨c, hc⟩
  obtain ⟨R, hR, hIccR⟩ := exists_Icc_ball hX hc
  obtain ⟨χ, hχ, hχb, hχ1, hχ0, hχc⟩ :=
    exists_cutoff (show c - 3 * R / 4 < c - R / 2 by linarith)
  have hαβ : Icc (c - R) (c - R / 4) ⊆ X := fun x hx => hIccR ⟨hx.1, by linarith [hx.2]⟩
  have hχb' : ∀ x, |χ x| ≤ 1 := fun x => abs_le.mpr ⟨by linarith [(hχb x).1], (hχb x).2⟩
  have hχ0' : ∀ x, c ≤ x → χ x = 0 := fun x hx => hχ0 x (by linarith)
  have huc : ContinuousOn u X := fun x hx => (hu x hx).1.continuousAt.continuousWithinAt
  have hu'c : ContinuousOn u' X := fun x hx => (hu x hx).2.continuousAt.continuousWithinAt
  have h1 := memLp_cutoff_left hχ.continuous hχb' hχ0' hX.measurableSet hu2
  have hg2 := memLp_cutoff_left hχ.continuous hχb' hχ0' hX.measurableSet (hu2.const_mul z)
  obtain ⟨h2, hm, hT⟩ := mem_adjoint_cutoff_of_weak hX hXc hne hq (fun x hx => (hu x hx).1)
    hu'c ((continuousOn_const.mul huc).locallyIntegrableOn hX.measurableSet)
    (fun ψ hψ => weak_of_isSolution hX hXc hne hq ⟨u', hu⟩ hψ) hχ hαβ
    (hχc _ _ (by linarith) (by linarith)) h1 hg2
  set g : (minOp X q)†.domain := ⟨_, hm⟩
  -- `χ` is locally constant `1` to the left of `c − 3R/4`
  have hflat : ∀ y, y < c - 3 * R / 4 → χ y = 1 ∧ deriv χ y = 0 ∧ deriv (deriv χ) y = 0 :=
    fun y hy => by
      have hev : χ =ᶠ[𝓝 y] fun _ => 1 := by
        filter_upwards [Iio_mem_nhds hy] with t ht using hχ1 t ht.le
      have hev' : deriv χ =ᶠ[𝓝 y] fun _ => 0 := by
        filter_upwards [hev.eventuallyEq_nhds] with t ht
        rw [ht.deriv_eq]; simp
      refine ⟨hev.eq_of_nhds, hev'.eq_of_nhds, ?_⟩
      rw [hev'.deriv_eq]; simp
  have hGc : ContinuousOn (fun x => (χ x : ℂ) * u x) X :=
    ((Complex.continuous_ofReal.comp hχ.continuous).continuousOn).mul huc
  have heq := eqOn_maxRep hX hXc hne hq g hGc h1.coeFn_toLp
  have hGd : ∀ x ∈ X, HasDerivAt (fun x => (χ x : ℂ) * u x)
      (((deriv χ x : ℝ) : ℂ) * u x + (χ x : ℂ) * u' x) x := fun x hx =>
    ((cutoff_derivs hχ x).1.mul (hu x hx).1)
  have hx0 : c - 7 * R / 8 ∈ X := hIccR ⟨by linarith, by linarith⟩
  refine ⟨g, c - 7 * R / 8, hx0, by linarith, fun y hy => ?_, ?_, ?_⟩
  · rw [heq hy.1]
    show (χ y : ℂ) * u y = u y
    rw [(hflat y (by linarith [hy.2.out])).1]; simp
  · rw [maxRepD_eq_of_eqOn hX hXc hne hq g hGd heq hx0, (hflat _ (by linarith)).1,
      (hflat _ (by linarith)).2.1]; simp
  · change (((minOp X q)† ⟨_, hm⟩ : L2X X) : ℝ → ℂ) =ᵐ[_] _
    rw [hT]
    filter_upwards [ae_restrict_of_ae_restrict_of_subset inter_subset_left h2.coeFn_toLp,
      ae_restrict_mem (hX.measurableSet.inter measurableSet_Iio)] with y h hy
    obtain ⟨e1, e2, e3⟩ := hflat y (by linarith [hy.2.out])
    rw [h]; simp [e1, e2, e3]

/-! ### Vanishing of the boundary form -/

theorem leftEnd_inter_le (hX : IsOpen X) {c : ℝ} (hc : c ∈ X) :
    leftEnd (X ∩ Iio c) ≤ leftEnd X := by
  obtain ⟨R, hR, hIcc⟩ := exists_Icc_ball hX hc
  have hy : c - R ∈ X ∩ Iio c := ⟨hIcc ⟨le_rfl, by linarith⟩, by simp [hR]⟩
  simp only [leftEnd, le_iInf_iff, le_principal_iff]
  intro d hd
  rcases lt_or_ge d c with h | h
  · refine mem_of_superset (mem_leftEnd (X := X ∩ Iio c) ⟨hd, h⟩) fun t ht => ⟨ht.1.1, ht.2⟩
  · refine mem_of_superset (mem_leftEnd (X := X ∩ Iio c) hy) fun t ht =>
      ⟨ht.1.1, show t < d by linarith [ht.2.out]⟩

theorem leftEnd_neBot (hX : IsOpen X) (hXc : X.OrdConnected) (hne : X.Nonempty) :
    (leftEnd X).NeBot := by
  obtain ⟨xs, -, hlim⟩ := exists_seq_leftEnd hX hXc hne
  exact hlim.neBot

section BoundaryForm

variable (hX : IsOpen X) (hXc : X.OrdConnected) (hne : X.Nonempty) (hq : ContinuousOn q X)
include hX hXc hne hq

/-- If `R ∈ 𝒟(ℒ*)` vanishes near the right end and its Wronskians against two solutions `P, Q`
with `W(P, Q) = 1` tend to `0` at `a`, the boundary form of `R` against every `G ∈ 𝒟(ℒ*)`
vanishes. -/
theorem inner_adjoint_eq_of_wronskian {z : ℂ} {P P' Q Q' : ℝ → ℂ}
    (hP : ∀ x ∈ X, HasDerivAt P (P' x) x ∧ HasDerivAt P' (((q x : ℂ) - z) * P x) x)
    (hQ : ∀ x ∈ X, HasDerivAt Q (Q' x) x ∧ HasDerivAt Q' (((q x : ℂ) - z) * Q x) x)
    {c : ℝ} (hc : c ∈ X) (hP2 : MemLp P 2 (volume.restrict (X ∩ Iio c)))
    (hQ2 : MemLp Q 2 (volume.restrict (X ∩ Iio c)))
    (hPQ : ∀ x ∈ X, P x * Q' x - P' x * Q x = 1) (R : (minOp X q)†.domain) {y₀ y : ℝ}
    (hy : y ∈ X) (hy₀y : y₀ < y)
    (hR0 : ((R : L2X X) : ℝ → ℂ) =ᵐ[volume.restrict (X ∩ Ioi y₀)] 0)
    (hTR0 : (((minOp X q)† R : L2X X) : ℝ → ℂ) =ᵐ[volume.restrict (X ∩ Ioi y₀)] 0)
    (hRP : Tendsto (fun x => conj (maxRep hX hXc hne hq R x) * P' x -
      conj (maxRepD hX hXc hne hq R x) * P x) (leftEnd X) (𝓝 0))
    (hRQ : Tendsto (fun x => conj (maxRep hX hXc hne hq R x) * Q' x -
      conj (maxRepD hX hXc hne hq R x) * Q x) (leftEnd X) (𝓝 0))
    (G : (minOp X q)†.domain) :
    ⟪(minOp X q)† R, (G : L2X X)⟫_ℂ = ⟪(R : L2X X), (minOp X q)† G⟫_ℂ := by
  have := leftEnd_neBot hX hXc hne
  obtain ⟨hwR, hFR, -⟩ := maxRep_spec hX hXc hne hq R
  obtain ⟨hwG, -, -⟩ := maxRep_spec hX hXc hne hq G
  set FR := maxRep hX hXc hne hq R
  set FR' := maxRepD hX hXc hne hq R
  set FG := maxRep hX hXc hne hq G
  set FG' := maxRepD hX hXc hne hq G
  set TR : ℝ → ℂ := (((minOp X q)† R : L2X X) : ℝ → ℂ)
  set TG : ℝ → ℂ := (((minOp X q)† G : L2X X) : ℝ → ℂ)
  set Wr : ℝ → ℂ := fun x => conj (FR x) * FG' x - conj (FR' x) * FG x
  -- the Wronskian `[R̄, G]` tends to `0` at `a`
  have hWr : Tendsto Wr (leftEnd X) (𝓝 0) := by
    have h := (hRP.mul (tendsto_wronskianBV hX hXc hne hq hc z Q' hQ hQ2 G)).sub
      (hRQ.mul (tendsto_wronskianBV hX hXc hne hq hc z P' hP hP2 G))
    rw [zero_mul, zero_mul, sub_zero] at h
    refine h.congr' ?_
    filter_upwards [mem_leftEnd hc] with x hx
    simp only [Wr, FR, FR', FG, FG']
    linear_combination (conj (FR x) * FG' x - conj (FR' x) * FG x) * hPQ x hx.1
  -- `R` vanishes near `y`
  have hOpen : IsOpen (X ∩ Ioi y₀) := hX.inter isOpen_Ioi
  have hFR0 : EqOn FR 0 (X ∩ Ioi y₀) := by
    refine eqOn_of_ae_eq_of_continuousOn hOpen ((continuousOn_maxRep hX hXc hne hq R).mono
      inter_subset_left) continuousOn_const ?_
    filter_upwards [(ae_restrict_of_ae_restrict_of_subset inter_subset_left hwR), hR0]
      with x h1 h2
    rw [← h1, h2]
  have hyy : y ∈ X ∩ Ioi y₀ := ⟨hy, hy₀y⟩
  have hev : FR =ᶠ[𝓝 y] fun _ => 0 :=
    Filter.eventuallyEq_of_mem (hOpen.mem_nhds hyy) fun t ht => hFR0 ht
  have hFR'0 : FR' y = 0 :=
    (hFR y hy).unique ((hasDerivAt_const y (0 : ℂ)).congr_of_eventuallyEq hev)
  have hWry : Wr y = 0 := by simp [Wr, hFR0 hyy, hFR'0]
  -- integrability
  have hmG : MemLp FG 2 (volume.restrict X) := (Lp.memLp (G : L2X X)).ae_eq hwG
  have hmR : MemLp FR 2 (volume.restrict X) := (Lp.memLp (R : L2X X)).ae_eq hwR
  have hK1 : Integrable (fun x => conj (TR x) * FG x) (volume.restrict X) :=
    (Lp.memLp ((minOp X q)† R)).star.integrable_mul hmG
  have hK2 : Integrable (fun x => conj (FR x) * TG x) (volume.restrict X) :=
    hmR.star.integrable_mul (Lp.memLp ((minOp X q)† G))
  set K : ℝ → ℂ := fun x => conj (TR x) * FG x - conj (FR x) * TG x
  have hK : IntegrableOn K X := hK1.sub hK2
  have hinner : ⟪(minOp X q)† R, (G : L2X X)⟫_ℂ - ⟪(R : L2X X), (minOp X q)† G⟫_ℂ =
      ∫ x in X, K x := by
    rw [inner_L2X, inner_L2X, ← integral_sub
      (f := fun x => conj (TR x) * ((G : L2X X) : ℝ → ℂ) x)
      (g := fun x => conj (((R : L2X X) : ℝ → ℂ) x) * TG x)
      (hK1.congr (by filter_upwards [hwG] with x hx; rw [hx]))
      (hK2.congr (by filter_upwards [hwR] with x hx; rw [hx]))]
    exact integral_congr_ae (by filter_upwards [hwG, hwR] with x h1 h2; simp only [K, h1, h2])
  -- `∫_X K = ∫_{X ∩ (−∞, x)} K − Wr x`
  have hcut : ∫ x in X, K x = ∫ x in X ∩ Iio y, K x := by
    refine setIntegral_eq_of_subset_of_ae_sdiff_eq_zero hX.measurableSet.nullMeasurableSet
      inter_subset_left ?_
    have h := (ae_restrict_iff' hOpen.measurableSet).mp hTR0
    filter_upwards [h] with x hx hxs
    have hxy : x ∈ X ∩ Ioi y₀ := ⟨hxs.1, lt_of_lt_of_le hy₀y (le_of_not_gt fun h' =>
      hxs.2 ⟨hxs.1, h'⟩)⟩
    simp [K, hx hxy, hFR0 hxy]
  have hform : ∀ᶠ x in leftEnd X, ∫ t in X, K t = (∫ t in X ∩ Iio x, K t) - Wr x := by
    filter_upwards [mem_leftEnd hy] with x hx
    rw [hcut, setIntegral_split_left hXc hy hx.1 hx.2.le (hK.mono_set inter_subset_left),
      ← lagrange_domain hX hXc hne hq R G hx.1 hy hx.2.le]
    simp only [Wr] at hWry ⊢
    rw [hWry]; ring
  have hlim := ((tendsto_setIntegral_leftEnd hX hXc hy (hK.mono_set inter_subset_left)).sub hWr)
  rw [sub_zero] at hlim
  have h0 : ∫ x in X, K x = 0 :=
    tendsto_nhds_unique (tendsto_const_nhds.congr' hform) hlim
  rw [← sub_eq_zero, hinner, h0]

end BoundaryForm

/-! ### The space of boundary values at an endpoint -/

section Space

variable (X q)

/-- The boundary values at `a`. -/
def boundaryValuesLeft : Submodule ℂ ((minOp X q)†.domain →ₗ[ℂ] ℂ) where
  carrier := {B | IsBoundaryValue X q B ∧
    ∀ f, VanishesNear X q (fun d => X ∩ Iio d) f → B f = 0}
  zero_mem' := ⟨⟨⟨0, fun f => by simp⟩, fun f _ => rfl⟩, fun f _ => rfl⟩
  add_mem' := by
    rintro B₁ B₂ ⟨⟨⟨C₁, h₁⟩, m₁⟩, a₁⟩ ⟨⟨⟨C₂, h₂⟩, m₂⟩, a₂⟩
    refine ⟨⟨⟨C₁ + C₂, fun f => ?_⟩, fun f hf => by simp [m₁ f hf, m₂ f hf]⟩,
      fun f hf => by simp [a₁ f hf, a₂ f hf]⟩
    rw [LinearMap.add_apply, add_mul]
    exact (norm_add_le _ _).trans (add_le_add (h₁ f) (h₂ f))
  smul_mem' := by
    rintro a B ⟨⟨⟨C, h⟩, m⟩, b⟩
    refine ⟨⟨⟨‖a‖ * C, fun f => ?_⟩, fun f hf => by simp [m f hf]⟩,
      fun f hf => by simp [b f hf]⟩
    rw [LinearMap.smul_apply, norm_smul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (h f) (norm_nonneg _)

/-- The boundary values at `b`. -/
def boundaryValuesRight : Submodule ℂ ((minOp X q)†.domain →ₗ[ℂ] ℂ) where
  carrier := {B | IsBoundaryValue X q B ∧
    ∀ f, VanishesNear X q (fun d => X ∩ Ioi d) f → B f = 0}
  zero_mem' := ⟨⟨⟨0, fun f => by simp⟩, fun f _ => rfl⟩, fun f _ => rfl⟩
  add_mem' := by
    rintro B₁ B₂ ⟨⟨⟨C₁, h₁⟩, m₁⟩, a₁⟩ ⟨⟨⟨C₂, h₂⟩, m₂⟩, a₂⟩
    refine ⟨⟨⟨C₁ + C₂, fun f => ?_⟩, fun f hf => by simp [m₁ f hf, m₂ f hf]⟩,
      fun f hf => by simp [a₁ f hf, a₂ f hf]⟩
    rw [LinearMap.add_apply, add_mul]
    exact (norm_add_le _ _).trans (add_le_add (h₁ f) (h₂ f))
  smul_mem' := by
    rintro a B ⟨⟨⟨C, h⟩, m⟩, b⟩
    refine ⟨⟨⟨‖a‖ * C, fun f => ?_⟩, fun f hf => by simp [m f hf]⟩,
      fun f hf => by simp [b f hf]⟩
    rw [LinearMap.smul_apply, norm_smul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (h f) (norm_nonneg _)

end Space

/-- **DLMF §1.18(ix)**: if `n₁ = 1` there are no nonzero boundary values at `a`. -/
theorem dlmf_1_18_ix_boundaryValuesLeft_LP (hX : IsOpen X) (hXc : X.OrdConnected)
    (hq : ContinuousOn q X) {c : ℝ} (hc : c ∈ X) {z : ℂ} (hz : z.im ≠ 0)
    (h1 : Module.finrank ℂ (deficiencySpace (minOp (X ∩ Iio c) q) z) = 1) :
    boundaryValuesLeft X q = ⊥ :=
  (Submodule.eq_bot_iff _).mpr fun _ hB =>
    dlmf_1_18_ix_boundary_values_LP_left hX hXc hq hc hz h1 hB.1 hB.2

/-- **DLMF §1.18(ix)**: if `n₂ = 1` there are no nonzero boundary values at `b`. -/
theorem dlmf_1_18_ix_boundaryValuesRight_LP (hX : IsOpen X) (hXc : X.OrdConnected)
    (hq : ContinuousOn q X) {c : ℝ} (hc : c ∈ X) {z : ℂ} (hz : z.im ≠ 0)
    (h1 : Module.finrank ℂ (deficiencySpace (minOp (X ∩ Ioi c) q) z) = 1) :
    boundaryValuesRight X q = ⊥ :=
  (Submodule.eq_bot_iff _).mpr fun _ hB =>
    dlmf_1_18_ix_boundary_values_LP_right hX hXc hq hc hz h1 hB.1 hB.2

/-- The representatives of the restriction of `g ∈ 𝒟(ℒ_X*)` to `Y` are those of `g`. -/
theorem maxRep_restrict (hX : IsOpen X) (hXc : X.OrdConnected) (hne : X.Nonempty)
    (hq : ContinuousOn q X) {Y : Set ℝ} (hY : IsOpen Y) (hYc : Y.OrdConnected)
    (hYne : Y.Nonempty) (hYX : Y ⊆ X) (g : (minOp X q)†.domain)
    (hr : (memLp_restrict_sub hYX (g : L2X X)).toLp ∈ (minOp Y q)†.domain) {x : ℝ}
    (hx : x ∈ Y) :
    maxRep hY hYc hYne (hq.mono hYX) ⟨_, hr⟩ x = maxRep hX hXc hne hq g x ∧
      maxRepD hY hYc hYne (hq.mono hYX) ⟨_, hr⟩ x = maxRepD hX hXc hne hq g x := by
  obtain ⟨hwg, hFg, -⟩ := maxRep_spec hX hXc hne hq g
  have heq : EqOn (maxRep hY hYc hYne (hq.mono hYX) ⟨_, hr⟩) (maxRep hX hXc hne hq g) Y :=
    eqOn_maxRep hY hYc hYne (hq.mono hYX) ⟨_, hr⟩
      ((continuousOn_maxRep hX hXc hne hq g).mono hYX) (by
        filter_upwards [(memLp_restrict_sub hYX (g : L2X X)).coeFn_toLp,
          ae_restrict_of_ae_restrict_of_subset hYX hwg] with y h1 h2
        exact h1.trans h2)
  exact ⟨heq hx, maxRepD_eq_of_eqOn hY hYc hYne (hq.mono hYX) ⟨_, hr⟩
    (fun y hy => hFg y (hYX hy)) heq hx⟩

/-- `W_v(g) = [u v′ − u′ v](x)` when `g` agrees with a solution `u` to the left of `x`. -/
theorem wronskianBV_of_eq (hX : IsOpen X) (hXc : X.OrdConnected) (hne : X.Nonempty)
    (hq : ContinuousOn q X) {c : ℝ} (hc : c ∈ X) (z : ℂ) {v v' : ℝ → ℂ}
    (hv : ∀ x ∈ X, HasDerivAt v (v' x) x ∧ HasDerivAt v' (((q x : ℂ) - z) * v x) x)
    (hv2 : MemLp v 2 (volume.restrict (X ∩ Iio c))) (g : (minOp X q)†.domain) {x : ℝ}
    (hx : x ∈ X) (hxc : x ≤ c) {u u' : ℝ → ℂ} (he : EqOn (maxRep hX hXc hne hq g) u (X ∩ Iic x))
    (hd : maxRepD hX hXc hne hq g x = u' x)
    (hT : (((minOp X q)† g : L2X X) : ℝ → ℂ) =ᵐ[volume.restrict (X ∩ Iio x)]
      fun y => z * u y) :
    wronskianBV hX hXc hne hq hc z v' hv2 g = u x * v' x - u' x * v x := by
  rw [wronskianBV_eq_at hX hXc hne hq hc z v' hv hv2 g hx hxc, he ⟨hx, (le_refl x : x ∈ Iic x)⟩, hd,
    integral_eq_zero_of_ae, sub_zero]
  filter_upwards [hT, ae_restrict_mem (hX.measurableSet.inter measurableSet_Iio)] with y h hy
  rw [h, he ⟨hy.1, hy.2.out.le⟩]
  simp

/-- On a limit-circle side, a boundary value at `a` vanishes on the common kernel of the two
Wronskian boundary values. -/
theorem boundaryValue_eq_zero_of_wronskians (hX : IsOpen X) (hXc : X.OrdConnected)
    (hq : ContinuousOn q X) {c : ℝ} (hc : c ∈ X) (z : ℂ) {v₁ v₁' v₂ v₂' : ℝ → ℂ}
    (hv₁ : ∀ x ∈ X, HasDerivAt v₁ (v₁' x) x ∧ HasDerivAt v₁' (((q x : ℂ) - z) * v₁ x) x)
    (hv₂ : ∀ x ∈ X, HasDerivAt v₂ (v₂' x) x ∧ HasDerivAt v₂' (((q x : ℂ) - z) * v₂ x) x)
    (hv₁2 : MemLp v₁ 2 (volume.restrict (X ∩ Iio c)))
    (hv₂2 : MemLp v₂ 2 (volume.restrict (X ∩ Iio c)))
    (h12 : v₁ c * v₂' c - v₁' c * v₂ c = 1) {B : (minOp X q)†.domain →ₗ[ℂ] ℂ}
    (hB : B ∈ boundaryValuesLeft X q) (f : (minOp X q)†.domain)
    (hf₁ : wronskianBV hX hXc ⟨c, hc⟩ hq hc z v₁' hv₁2 f = 0)
    (hf₂ : wronskianBV hX hXc ⟨c, hc⟩ hq hc z v₂' hv₂2 f = 0) : B f = 0 := by
  have hne : X.Nonempty := ⟨c, hc⟩
  obtain ⟨hY, hYc, hYne, hYX⟩ := halfInterval_props hX hXc hc (Or.inl rfl)
  have hqY : ContinuousOn q (X ∩ Iio c) := hq.mono hYX
  obtain ⟨R, hR, hIccR⟩ := exists_Icc_ball hX hc
  obtain ⟨χ, hχ, hχb, hχ1, hχ0, hχc⟩ :=
    exists_cutoff (show c - 3 * R / 4 < c - R / 2 by linarith)
  have hαβ : Icc (c - R) (c - R / 4) ⊆ X := fun x hx => hIccR ⟨hx.1, by linarith [hx.2]⟩
  have hχb' : ∀ x, |χ x| ≤ 1 := fun x => abs_le.mpr ⟨by linarith [(hχb x).1], (hχb x).2⟩
  obtain ⟨hwF, -, -⟩ := maxRep_spec hX hXc hne hq f
  obtain ⟨m1, m2, hm, hTg⟩ := mem_adjoint_cutoff hX hXc hne hq f hχ hχb' hαβ
    (hχc _ _ (by linarith) (by linarith))
  set g : (minOp X q)†.domain := ⟨_, hm⟩
  have hflat : ∀ x, c - R / 2 < x → χ x = 0 ∧ deriv χ x = 0 ∧ deriv (deriv χ) x = 0 :=
    fun x hx => by
      have hev : χ =ᶠ[𝓝 x] fun _ => 0 := by
        filter_upwards [Ioi_mem_nhds hx] with y hy using hχ0 y hy.le
      have hev' : deriv χ =ᶠ[𝓝 x] fun _ => 0 := by
        filter_upwards [hev.eventuallyEq_nhds] with y hy
        rw [hy.deriv_eq]; simp
      refine ⟨hev.eq_of_nhds, hev'.eq_of_nhds, ?_⟩
      rw [hev'.deriv_eq]; simp
  have hm0 : MeasurableSet (X ∩ Ioi (c - R / 2)) := hX.measurableSet.inter measurableSet_Ioi
  have hg0 : ((g : L2X X) : ℝ → ℂ) =ᵐ[volume.restrict (X ∩ Ioi (c - R / 2))] 0 := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset inter_subset_left m1.coeFn_toLp,
      ae_restrict_mem hm0] with x h hx
    change (m1.toLp : ℝ → ℂ) x = 0
    rw [h, (hflat x hx.2).1]; simp
  have hTg0 : (((minOp X q)† g : L2X X) : ℝ → ℂ) =ᵐ[volume.restrict (X ∩ Ioi (c - R / 2))] 0 := by
    change (((minOp X q)† ⟨_, hm⟩ : L2X X) : ℝ → ℂ) =ᵐ[_] 0
    rw [hTg]
    filter_upwards [ae_restrict_of_ae_restrict_of_subset inter_subset_left m2.coeFn_toLp,
      ae_restrict_mem hm0] with x h hx
    obtain ⟨e1, e2, e3⟩ := hflat x hx.2
    rw [h]; simp [e1, e2, e3]
  -- `f − g` vanishes near `a`
  have hd : c - 3 * R / 4 ∈ X := hIccR ⟨by linarith, by linarith⟩
  have hfg : VanishesNear X q (fun d => X ∩ Iio d) (f - g) := ⟨_, hd, by
    show (((f : L2X X) - (g : L2X X) : L2X X) : ℝ → ℂ) =ᵐ[volume.restrict (X ∩ Iio _)] 0
    filter_upwards [ae_restrict_of_ae_restrict_of_subset inter_subset_left
        (Lp.coeFn_sub (f : L2X X) (g : L2X X)),
      ae_restrict_of_ae_restrict_of_subset inter_subset_left hwF,
      ae_restrict_of_ae_restrict_of_subset inter_subset_left m1.coeFn_toLp,
      ae_restrict_mem (hX.inter isOpen_Iio).measurableSet] with x h1 h2 h3 h4
    change _ = (0 : ℂ)
    rw [h1, Pi.sub_apply, h2]
    change maxRep hX hXc hne hq f x - (m1.toLp : ℝ → ℂ) x = 0
    rw [h3, hχ1 x h4.2.le]; simp⟩
  have hW₁ : wronskianBV hX hXc hne hq hc z v₁' hv₁2 g = 0 := by
    have h := (wronskianBV_isBoundaryValue hX hXc hne hq hc z v₁' hv₁ hv₁2).2 _ hfg
    rwa [_root_.map_sub, hf₁, zero_sub, neg_eq_zero] at h
  have hW₂ : wronskianBV hX hXc hne hq hc z v₂' hv₂2 g = 0 := by
    have h := (wronskianBV_isBoundaryValue hX hXc hne hq hc z v₂' hv₂ hv₂2).2 _ hfg
    rwa [_root_.map_sub, hf₂, zero_sub, neg_eq_zero] at h
  suffices hBg : B g = 0 by
    have h := hB.2 _ hfg
    rwa [_root_.map_sub, hBg, sub_zero] at h
  -- the restriction of `g` to `X ∩ (−∞, c)` lies in `𝒟(ℒ**)`
  obtain ⟨hr, hTr⟩ := restrict_mem_adjoint hX hq hY hYX g
  set Rg : (minOp (X ∩ Iio c) q)†.domain := ⟨_, hr⟩
  have conjSol : ∀ {v v' : ℝ → ℂ},
      (∀ x ∈ X, HasDerivAt v (v' x) x ∧ HasDerivAt v' (((q x : ℂ) - z) * v x) x) →
      ∀ x ∈ X ∩ Iio c, HasDerivAt (fun x => conj (v x)) (conj (v' x)) x ∧
        HasDerivAt (fun x => conj (v' x)) (((q x : ℂ) - conj z) * conj (v x)) x :=
    fun hv x hx => ⟨by simpa [Complex.star_def] using (hv x (hYX hx)).1.star,
      by simpa [Complex.star_def] using (hv x (hYX hx)).2.star⟩
  have hc₀ : c - R ∈ X ∩ Iio c := ⟨hIccR ⟨le_rfl, by linarith⟩, by simp [hR]⟩
  have hsub : X ∩ Iio c ∩ Iio (c - R) ⊆ X ∩ Iio c := inter_subset_left
  have hP2 : MemLp (fun x => conj (v₁ x)) 2 (volume.restrict (X ∩ Iio c ∩ Iio (c - R))) :=
    hv₁2.star.mono_measure (Measure.restrict_mono hsub le_rfl)
  have hQ2 : MemLp (fun x => conj (v₂ x)) 2 (volume.restrict (X ∩ Iio c ∩ Iio (c - R))) :=
    hv₂2.star.mono_measure (Measure.restrict_mono hsub le_rfl)
  have hPQ : ∀ x ∈ X ∩ Iio c,
      conj (v₁ x) * conj (v₂' x) - conj (v₁' x) * conj (v₂ x) = 1 := fun x hx => by
    have h := wronskian_const hXc hq hv₁ hv₂ hx.1 hc
    rw [h12] at h
    rw [← map_mul, ← map_mul, ← _root_.map_sub, h, map_one]
  have hRW : ∀ {v v' : ℝ → ℂ}
      (hv : ∀ x ∈ X, HasDerivAt v (v' x) x ∧ HasDerivAt v' (((q x : ℂ) - z) * v x) x)
      (hv2 : MemLp v 2 (volume.restrict (X ∩ Iio c))),
      wronskianBV hX hXc hne hq hc z v' hv2 g = 0 →
      Tendsto (fun x => conj (maxRep hY hYc hYne hqY Rg x) * conj (v' x) -
        conj (maxRepD hY hYc hYne hqY Rg x) * conj (v x)) (leftEnd (X ∩ Iio c)) (𝓝 0) := by
    intro v v' hv hv2 hW
    have h := tendsto_wronskianBV hX hXc hne hq hc z v' hv hv2 g
    rw [hW] at h
    have h' := ((Complex.continuous_conj.tendsto 0).comp
      (h.mono_left (leftEnd_inter_le hX hc)))
    rw [_root_.map_zero] at h'
    refine h'.congr' ?_
    filter_upwards [mem_leftEnd (X := X ∩ Iio c) hc₀] with x hx
    obtain ⟨e1, e2⟩ := maxRep_restrict hX hXc hne hq hY hYc hYne hYX g hr hx.1
    simp only [Function.comp_apply, Rg, e1, e2, _root_.map_add, map_mul, _root_.map_neg]
    ring
  have hy : c - R / 4 ∈ X ∩ Iio c := ⟨hIccR ⟨by linarith, by linarith⟩, by simp; linarith⟩
  have hsub2 : X ∩ Iio c ∩ Ioi (c - R / 2) ⊆ X ∩ Ioi (c - R / 2) :=
    fun x hx => ⟨hx.1.1, hx.2⟩
  have hR0 : ((Rg : L2X (X ∩ Iio c)) : ℝ → ℂ) =ᵐ[volume.restrict
      (X ∩ Iio c ∩ Ioi (c - R / 2))] 0 := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset inter_subset_left
        (memLp_restrict_sub hYX (g : L2X X)).coeFn_toLp,
      ae_restrict_of_ae_restrict_of_subset hsub2 hg0] with x h1 h2
    exact h1.trans h2
  have hTR0 : (((minOp (X ∩ Iio c) q)† Rg : L2X (X ∩ Iio c)) : ℝ → ℂ) =ᵐ[volume.restrict
      (X ∩ Iio c ∩ Ioi (c - R / 2))] 0 := by
    rw [hTr]
    filter_upwards [ae_restrict_of_ae_restrict_of_subset inter_subset_left
        (memLp_restrict_sub hYX ((minOp X q)† g)).coeFn_toLp,
      ae_restrict_of_ae_restrict_of_subset hsub2 hTg0] with x h1 h2
    exact h1.trans h2
  have hYm : ((Rg : L2X (X ∩ Iio c))) ∈ (minOp (X ∩ Iio c) q)††.domain :=
    mem_adjoint_domain_of_exists _ ⟨(minOp (X ∩ Iio c) q)† Rg, fun G =>
      inner_adjoint_eq_of_wronskian hY hYc hYne hqY (conjSol hv₁) (conjSol hv₂) hc₀ hP2 hQ2
        hPQ Rg hy (show c - R / 2 < c - R / 4 by linarith) hR0 hTR0 (hRW hv₁ hv₁2 hW₁)
        (hRW hv₂ hv₂2 hW₂) G⟩
  have hsd : X \ (X ∩ Iio c) ⊆ X ∩ Ioi (c - R / 2) := fun x hx =>
    ⟨hx.1, by
      have : c ≤ x := le_of_not_gt fun h => hx.2 ⟨hx.1, h⟩
      show c - R / 2 < x
      linarith⟩
  exact IsBoundaryValue.eq_zero_of_restrict hX hq hB.1 hY hYX g
    (ae_restrict_of_ae_restrict_of_subset hsd hg0) (ae_restrict_of_ae_restrict_of_subset hsd hTg0)
    hYm

/-- **DLMF §1.18(ix)**: if `n₁ = 2` (limit circle at `a`), the boundary values at `a` form a
two-dimensional class, spanned by the Wronskians against two solutions. -/
theorem dlmf_1_18_ix_boundaryValuesLeft_LC (hX : IsOpen X) (hXc : X.OrdConnected)
    (hq : ContinuousOn q X) {c : ℝ} (hc : c ∈ X) {z : ℂ}
    (h2 : Module.finrank ℂ (deficiencySpace (minOp (X ∩ Iio c) q) z) = 2) :
    Module.finrank ℂ (boundaryValuesLeft X q) = 2 := by
  have hne : X.Nonempty := ⟨c, hc⟩
  obtain ⟨hY, hYc, hYne, hYX⟩ := halfInterval_props hX hXc hc (Or.inl rfl)
  have hall := (finrank_eq_two_iff hY hYc hYne (hq.mono hYX) z).mp h2
  have hW : ContinuousOn (fun x => (q x : ℂ) - z) X :=
    (Complex.continuous_ofReal.comp_continuousOn hq).sub continuousOn_const
  obtain ⟨v₁, v₁', hv₁, hv₁c, hv₁'c⟩ := exists_solution_on hX hXc hW hc 1 0
  obtain ⟨v₂, v₂', hv₂, hv₂c, hv₂'c⟩ := exists_solution_on hX hXc hW hc 0 1
  have hv₁2 := hall v₁ ⟨v₁', fun x hx => hv₁ x (hYX hx)⟩
  have hv₂2 := hall v₂ ⟨v₂', fun x hx => hv₂ x (hYX hx)⟩
  set W₁ := wronskianBV hX hXc hne hq hc z v₁' hv₁2
  set W₂ := wronskianBV hX hXc hne hq hc z v₂' hv₂2
  have h12 : v₁ c * v₂' c - v₁' c * v₂ c = 1 := by
    rw [hv₁c, hv₂c, hv₁'c, hv₂'c]; ring
  -- values on cut-off solutions
  have hval : ∀ {u u' : ℝ → ℂ}
      (_ : ∀ x ∈ X, HasDerivAt u (u' x) x ∧ HasDerivAt u' (((q x : ℂ) - z) * u x) x)
      (_ : MemLp u 2 (volume.restrict (X ∩ Iio c))),
      ∃ g : (minOp X q)†.domain, ∀ (v v' : ℝ → ℂ)
        (hv : ∀ x ∈ X, HasDerivAt v (v' x) x ∧ HasDerivAt v' (((q x : ℂ) - z) * v x) x)
        (hv2 : MemLp v 2 (volume.restrict (X ∩ Iio c))),
        wronskianBV hX hXc hne hq hc z v' hv2 g = u c * v' c - u' c * v c := by
    intro u u' hu hu2
    obtain ⟨g, x, hx, hxc, he, hd, hT⟩ := exists_cutoff_solution hX hXc hq hc hu hu2
    refine ⟨g, fun v v' hv hv2 => ?_⟩
    rw [wronskianBV_of_eq hX hXc hne hq hc z hv hv2 g hx hxc.le he hd hT]
    exact wronskian_const hXc hq hu hv hx hc
  obtain ⟨g₁, hg₁⟩ := hval hv₁ hv₁2
  obtain ⟨g₂, hg₂⟩ := hval hv₂ hv₂2
  have a11 : W₁ g₁ = 0 := by rw [hg₁ v₁ v₁' hv₁ hv₁2]; ring
  have a12 : W₂ g₁ = 1 := by rw [hg₁ v₂ v₂' hv₂ hv₂2, h12]
  have a21 : W₁ g₂ = -1 := by rw [hg₂ v₁ v₁' hv₁ hv₁2, ← h12]; ring
  have a22 : W₂ g₂ = 0 := by rw [hg₂ v₂ v₂' hv₂ hv₂2]; ring
  have hli : LinearIndependent ℂ ![W₁, W₂] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have e1 := LinearMap.congr_fun hst g₁
    have e2 := LinearMap.congr_fun hst g₂
    simp only [LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, a11, a12, a21, a22,
      LinearMap.zero_apply] at e1 e2
    constructor
    · linear_combination -e2
    · linear_combination e1
  have hspan : boundaryValuesLeft X q = Submodule.span ℂ (range ![W₁, W₂]) := by
    refine le_antisymm (fun B hB => mem_span_of_iInf_ker_le_ker fun f hf => ?_)
      (Submodule.span_le.mpr (range_subset_iff.mpr fun i => ?_))
    · rw [Submodule.mem_iInf] at hf
      exact LinearMap.mem_ker.mpr (boundaryValue_eq_zero_of_wronskians hX hXc hq hc z hv₁ hv₂
        hv₁2 hv₂2 h12 hB f (LinearMap.mem_ker.mp (hf 0)) (LinearMap.mem_ker.mp (hf 1)))
    · fin_cases i
      · exact wronskianBV_isBoundaryValue hX hXc hne hq hc z v₁' hv₁ hv₁2
      · exact wronskianBV_isBoundaryValue hX hXc hne hq hc z v₂' hv₂ hv₂2
  rw [hspan, finrank_span_eq_card hli, Fintype.card_fin]

end Azurite.DLMF
