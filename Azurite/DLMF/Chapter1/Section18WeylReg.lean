/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter1.Section18WeylMin
import Mathlib.Analysis.Calculus.BumpFunction.Normed

/-!
# DLMF §1.18(ix): regularity of the maximal domain

* `integral_primitive_mul_deriv`: integration by parts against the primitive of an `L¹`
  function, by Fubini.
* `exists_double_primitive` and `ae_eq_affine_of_integral_deriv_deriv`: the second-order
  du Bois-Reymond lemma. If `∫_X D φ″ = 0` for all `φ ∈ C²_c(X)` on an open interval `X`, then
  `D` is affine a.e. The proof subtracts moments using a normalized bump.
* `weak_regularity`: if `ℒw = g` distributionally, with `w, g` locally integrable on `X`, then
  `w` is a.e. a `C¹` function `F` with `F′(x) = F′(c) + ∫_c^x (qF − g)`.
-/

open Set Filter Topology MeasureTheory
open scoped InnerProductSpace ComplexConjugate ContDiff

namespace Azurite.DLMF

/-- Integration by parts against a primitive of an integrable function (by Fubini):
`∫_α^β (∫_α^t k) ψ′(t) dt = ∫_α^β k(s)(ψ(β) − ψ(s)) ds`. -/
theorem integral_primitive_mul_deriv {k ψ ψ' : ℝ → ℂ} {α β : ℝ} (hαβ : α ≤ β)
    (hk : IntervalIntegrable k volume α β) (hψ : ∀ t, HasDerivAt ψ (ψ' t) t)
    (hψ' : Continuous ψ') :
    ∫ t in α..β, (∫ s in α..t, k s) * ψ' t = ∫ s in α..β, k s * (ψ β - ψ s) := by
  set S := Ioc α β
  have hkS : IntegrableOn k S := (intervalIntegrable_iff_integrableOn_Ioc_of_le hαβ).mp hk
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn (s := Icc α β) hψ'.continuousOn
  -- rewrite the inner integral with an indicator
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
  have hψS : IntegrableOn ψ' S := hψ'.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hint : Integrable (Function.uncurry fun t s => {p : ℝ × ℝ | p.2 ≤ p.1}.indicator
      (fun p => k p.2 * ψ' p.1) (t, s)) ((volume.restrict S).prod (volume.restrict S)) := by
    refine (hψS.norm.mul_prod hkS.norm).mono' ?_ (ae_of_all _ fun p => ?_)
    · refine AEStronglyMeasurable.indicator ?_ (measurableSet_le measurable_snd measurable_fst)
      have hk2 : AEStronglyMeasurable (fun p : ℝ × ℝ => k p.2)
          ((volume.restrict S).prod (volume.restrict S)) := hkS.aestronglyMeasurable.comp_snd
      exact hk2.mul (hψ'.comp continuous_fst).aestronglyMeasurable
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
  rw [h3, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hs.2,
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hψ t)
      (hψ'.intervalIntegrable _ _)]

/-! ### Test functions on an interval -/

variable {X : Set ℝ}

/-- A compact subset of an open interval `X` lies in some `(α, β)` with `[α, β] ⊆ X`. -/
theorem exists_Ioo_of_isCompact (hX : IsOpen X) {K : Set ℝ}
    (hK : IsCompact K) (hKX : K ⊆ X) {x0 : ℝ} (hx0 : x0 ∈ X) :
    ∃ α β, α ∈ X ∧ β ∈ X ∧ α < β ∧ K ⊆ Ioo α β ∧ x0 ∈ Ioo α β := by
  set K' := insert x0 K
  have hK' : IsCompact K' := hK.insert x0
  have hne : K'.Nonempty := ⟨x0, mem_insert _ _⟩
  have hK'X : K' ⊆ X := insert_subset hx0 hKX
  have hm := hK'.sInf_mem hne
  have hM := hK'.sSup_mem hne
  obtain ⟨ε, hε, hεX⟩ := Metric.isOpen_iff.mp hX _ (hK'X hm)
  obtain ⟨δ, hδ, hδX⟩ := Metric.isOpen_iff.mp hX _ (hK'X hM)
  refine ⟨sInf K' - ε / 2, sSup K' + δ / 2, hεX ?_, hδX ?_, ?_, fun y hy => ⟨?_, ?_⟩, ?_, ?_⟩
  · rw [Metric.mem_ball, Real.dist_eq, abs_lt]; constructor <;> linarith
  · rw [Metric.mem_ball, Real.dist_eq, abs_lt]; constructor <;> linarith
  · linarith [csInf_le hK'.bddBelow hm, le_csSup hK'.bddAbove (mem_insert x0 K),
      csInf_le hK'.bddBelow (mem_insert x0 K)]
  · linarith [csInf_le hK'.bddBelow (mem_insert_of_mem x0 hy)]
  · linarith [le_csSup hK'.bddAbove (mem_insert_of_mem x0 hy)]
  · linarith [csInf_le hK'.bddBelow (mem_insert x0 K)]
  · linarith [le_csSup hK'.bddAbove (mem_insert x0 K)]

theorem setIntegral_eq_intervalIntegral_of_vanish {f : ℝ → ℂ} {α β : ℝ} (hαβ : α ≤ β)
    (hIcc : Icc α β ⊆ X) (hf : ∀ x ∉ Ioo α β, f x = 0) :
    ∫ x in X, f x = ∫ x in α..β, f x := by
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx =>
      hf x fun h => hx (hIcc (Ioo_subset_Icc_self h)),
    intervalIntegral.integral_of_le hαβ,
    setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx =>
      hf x fun h => hx (Ioo_subset_Ioc_self h)]

theorem integral_eq_intervalIntegral_of_vanish {f : ℝ → ℂ} {α β : ℝ} (hαβ : α ≤ β)
    (hf : ∀ x ∉ Ioo α β, f x = 0) : ∫ x, f x = ∫ x in α..β, f x := by
  rw [intervalIntegral.integral_of_le hαβ,
    setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx =>
      hf x fun h => hx (Ioo_subset_Ioc_self h)]

theorem eventuallyEq_zero_of_notMem {g : ℝ → ℝ} {α β x : ℝ} (hs : tsupport g ⊆ Ioo α β)
    (hx : x ∉ Ioo α β) : g =ᶠ[𝓝 x] 0 :=
  (notMem_tsupport_iff_eventuallyEq).mp fun h => hx (hs h)

theorem deriv_eq_zero_of_notMem {g : ℝ → ℝ} {α β x : ℝ} (hs : tsupport g ⊆ Ioo α β)
    (hx : x ∉ Ioo α β) : deriv g x = 0 := by
  rw [(eventuallyEq_zero_of_notMem hs hx).deriv_eq]; simp

/-- The double primitive `Ψ(x) = ∫_α^x ∫_α^t χ` of a continuous `χ` vanishing outside `(α, β)`
with `∫ χ = ∫ s χ(s) ds = 0` is a `C²` function supported in `[α, β]` with `Ψ″ = χ`. -/
theorem exists_double_primitive {χ : ℝ → ℂ} (hχ : Continuous χ) {α β : ℝ} (hαβ : α ≤ β)
    (hz : ∀ x ∉ Ioo α β, χ x = 0) (h0 : ∫ x in α..β, χ x = 0)
    (h1 : ∫ x in α..β, (x : ℂ) * χ x = 0) :
    ∃ Ψ : ℝ → ℂ, ContDiff ℝ 2 Ψ ∧ HasCompactSupport Ψ ∧ tsupport Ψ ⊆ Icc α β ∧
      deriv (deriv Ψ) = χ := by
  set Φ : ℝ → ℂ := fun t => ∫ s in α..t, χ s
  set Ψ : ℝ → ℂ := fun x => ∫ t in α..x, Φ t
  have hΦ : ∀ t, HasDerivAt Φ (χ t) t := fun t => (hχ.integral_hasStrictDerivAt α t).hasDerivAt
  have hΦc : Continuous Φ := continuous_iff_continuousAt.mpr fun t => (hΦ t).continuousAt
  have hΨ : ∀ x, HasDerivAt Ψ (Φ x) x := fun x => (hΦc.integral_hasStrictDerivAt α x).hasDerivAt
  have hdΨ : deriv Ψ = Φ := funext fun x => (hΨ x).deriv
  have hdΦ : deriv Φ = χ := funext fun x => (hΦ x).deriv
  -- vanishing outside `(α, β)`
  have hΦl : ∀ t ≤ α, Φ t = 0 := fun t ht => by
    simp only [Φ]
    rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℂ)) fun s hs => hz s fun h => by
      rw [uIcc_of_ge ht] at hs; linarith [h.1, hs.2]]
    simp
  have hΦr : ∀ t, β ≤ t → Φ t = 0 := fun t ht => by
    simp only [Φ]
    rw [← intervalIntegral.integral_add_adjacent_intervals (b := β)
      (hχ.intervalIntegrable _ _) (hχ.intervalIntegrable _ _), h0, zero_add,
      intervalIntegral.integral_congr (g := fun _ => (0 : ℂ)) fun s hs => hz s fun h => by
        rw [uIcc_of_le ht] at hs; linarith [h.2, hs.1]]
    simp
  have hΨβ : Ψ β = 0 := by
    simp only [Ψ]
    have := integral_primitive_mul_deriv (k := χ) (ψ := fun t => (t : ℂ)) (ψ' := fun _ => 1)
      hαβ (hχ.intervalIntegrable _ _)
      (fun t => by simpa using (hasDerivAt_id t).ofReal_comp) continuous_const
    simp only [mul_one] at this
    rw [this]
    have e : ∀ s : ℝ, χ s * ((β : ℂ) - s) = (β : ℂ) * χ s - (s : ℂ) * χ s := fun s => by ring
    simp_rw [e]
    rw [intervalIntegral.integral_sub (f := fun s => (β : ℂ) * χ s)
      (g := fun s => (s : ℂ) * χ s) ((hχ.intervalIntegrable _ _).const_mul _)
      ((Complex.continuous_ofReal.mul hχ).intervalIntegrable _ _),
      intervalIntegral.integral_const_mul, h0, h1]
    ring
  have hvan : ∀ x ∉ Ioo α β, Ψ x = 0 := by
    intro x hx
    rcases le_or_gt x α with hxa | hxa
    · simp only [Ψ]
      rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℂ)) fun t ht => hΦl t (by
        rw [uIcc_of_ge hxa] at ht; exact ht.2)]
      simp
    · have hxb : β ≤ x := by
        by_contra h; push Not at h; exact hx ⟨hxa, h⟩
      simp only [Ψ]
      rw [← intervalIntegral.integral_add_adjacent_intervals (b := β)
        (hΦc.intervalIntegrable _ _) (hΦc.intervalIntegrable _ _)]
      have : Ψ β = ∫ t in α..β, Φ t := rfl
      rw [← this, hΨβ, zero_add,
        intervalIntegral.integral_congr (g := fun _ => (0 : ℂ)) fun t ht => hΦr t (by
          rw [uIcc_of_le hxb] at ht; exact ht.1)]
      simp
  have hsupp : Function.support Ψ ⊆ Icc α β := fun x hx => by
    by_contra h
    exact hx (hvan x fun h' => h (Ioo_subset_Icc_self h'))
  refine ⟨Ψ, ?_, HasCompactSupport.intro isCompact_Icc fun x hx => by
      by_contra h'; exact hx (hsupp h'), closure_minimal hsupp isClosed_Icc, by rw [hdΨ, hdΦ]⟩
  rw [show (2 : WithTop ℕ∞) = 1 + 1 from rfl, contDiff_succ_iff_deriv]
  refine ⟨fun x => (hΨ x).differentiableAt, by simp, ?_⟩
  rw [hdΨ, contDiff_one_iff_deriv, hdΦ]
  exact ⟨fun x => (hΦ x).differentiableAt, hχ⟩

/-- `∫ (f − c g − d h) = ∫ f − c ∫ g − d ∫ h`. -/
theorem intervalIntegral_sub_smul₃ {f g h : ℝ → ℂ} {α β : ℝ} (hf : IntervalIntegrable f volume α β)
    (hg : IntervalIntegrable g volume α β) (hh : IntervalIntegrable h volume α β) (c d : ℂ) :
    ∫ x in α..β, (f x - c * g x - d * h x) =
      (∫ x in α..β, f x) - c * (∫ x in α..β, g x) - d * ∫ x in α..β, h x := by
  rw [intervalIntegral.integral_sub (f := fun x => f x - c * g x) (g := fun x => d * h x)
      (hf.sub (hg.const_mul c)) (hh.const_mul d),
    intervalIntegral.integral_sub (f := f) (g := fun x => c * g x) hf (hg.const_mul c),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]

theorem intervalIntegrable_mul_of_locallyIntegrableOn {D : ℝ → ℂ} (hD : LocallyIntegrableOn D X)
    {f : ℝ → ℂ} (hf : Continuous f) {α β : ℝ} (hαβ : α ≤ β) (hIcc : Icc α β ⊆ X) :
    IntervalIntegrable (fun x => D x * f x) volume α β := by
  have hi : IntegrableOn D (Icc α β) := hD.integrableOn_compact_subset hIcc isCompact_Icc
  exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hαβ).mpr
    ((hi.mul_continuousOn hf.continuousOn isCompact_Icc).mono_set Ioc_subset_Icc_self)

/-- **Second-order du Bois-Reymond lemma**: if `∫_X D φ″ = 0` for all `φ ∈ C²_c(X)` on an open
interval `X`, then `D` is affine a.e. on `X`. -/
theorem ae_eq_affine_of_integral_deriv_deriv (hX : IsOpen X) (hXc : X.OrdConnected)
    (hne : X.Nonempty) {D : ℝ → ℂ} (hD : LocallyIntegrableOn D X)
    (h : ∀ φ : ℝ → ℂ, IsC2c X φ → ∫ x in X, D x * deriv (deriv φ) x = 0) :
    ∃ a b : ℂ, ∀ᵐ x ∂(volume.restrict X), D x = a + b * x := by
  obtain ⟨x0, hx0⟩ := hne
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hX x0 hx0
  let bump : ContDiffBump x0 := ⟨r / 4, r / 2, by positivity, by linarith⟩
  set ρ : ℝ → ℝ := bump.normed volume
  have hρs : tsupport ρ ⊆ X := by
    rw [bump.tsupport_normed_eq]
    exact (Metric.closedBall_subset_ball (by simp [bump]; linarith)).trans hball
  have hρd : ContDiff ℝ 2 ρ := bump.contDiff_normed (n := 2)
  have hρcs : HasCompactSupport ρ := bump.hasCompactSupport_normed
  have hρ1 : ∫ x, ρ x = 1 := bump.integral_normed
  have hρ' : ∀ x, HasDerivAt ρ (deriv ρ x) x := fun x =>
    (hρd.differentiable (by norm_num) x).hasDerivAt
  have hρ'c : Continuous (deriv ρ) := hρd.continuous_deriv (by norm_num)
  set ρc : ℝ → ℂ := fun x => (ρ x : ℂ)
  set μc : ℝ → ℂ := fun x => -((deriv ρ x : ℝ) : ℂ)
  have hρcc : Continuous ρc := Complex.continuous_ofReal.comp hρd.continuous
  have hμcc : Continuous μc := (Complex.continuous_ofReal.comp hρ'c).neg
  set m1 : ℂ := ∫ x : ℝ, (x : ℂ) * ρc x
  set a0 := ∫ x in X, D x * ρc x
  set b0 := ∫ x in X, D x * μc x
  refine ⟨a0 - b0 * m1, b0, ?_⟩
  have hlin : Continuous fun x : ℝ => a0 - b0 * m1 + b0 * x := by fun_prop
  have hloc : LocallyIntegrableOn (fun x => D x - (a0 - b0 * m1 + b0 * x)) X :=
    hD.sub (hlin.locallyIntegrable.locallyIntegrableOn X)
  have key := hX.ae_eq_zero_of_integral_contDiff_smul_eq_zero hloc fun χ hχ hχc hχs => by
    obtain ⟨α, β, hα, hβ, hαβ, hK, -⟩ := exists_Ioo_of_isCompact hX
      (hχc.isCompact.union hρcs.isCompact) (union_subset hχs hρs) hx0
    have hIcc : Icc α β ⊆ X := hXc.out hα hβ
    have hχK : tsupport χ ⊆ Ioo α β := subset_union_left.trans hK
    have hρK : tsupport ρ ⊆ Ioo α β := subset_union_right.trans hK
    have hχz : ∀ x ∉ Ioo α β, χ x = 0 := fun x hx => (eventuallyEq_zero_of_notMem hχK hx).eq_of_nhds
    have hρz : ∀ x ∉ Ioo α β, ρ x = 0 := fun x hx => (eventuallyEq_zero_of_notMem hρK hx).eq_of_nhds
    have hρ'z : ∀ x ∉ Ioo α β, deriv ρ x = 0 := fun x hx => deriv_eq_zero_of_notMem hρK hx
    set χc : ℝ → ℂ := fun x => (χ x : ℂ)
    have hχcc : Continuous χc := Complex.continuous_ofReal.comp hχ.continuous
    set A : ℂ := ∫ x in α..β, χc x
    set B : ℂ := (∫ x in α..β, (x : ℂ) * χc x) - A * m1
    set χt : ℝ → ℂ := fun x => χc x - A * ρc x - B * μc x
    have hχtc : Continuous χt := (hχcc.sub (continuous_const.mul hρcc)).sub
      (continuous_const.mul hμcc)
    have hχtz : ∀ x ∉ Ioo α β, χt x = 0 := fun x hx => by
      simp [χt, χc, ρc, μc, hχz x hx, hρz x hx, hρ'z x hx]
    -- moments of `ρ` and `μ` on `[α, β]`
    have hρ1' : ∫ x in α..β, ρc x = 1 := by
      rw [← integral_eq_intervalIntegral_of_vanish hαβ.le fun x hx => by simp [ρc, hρz x hx]]
      show ∫ x, ((ρ x : ℝ) : ℂ) = 1
      rw [integral_complex_ofReal, hρ1, Complex.ofReal_one]
    have hm1' : ∫ x in α..β, (x : ℂ) * ρc x = m1 :=
      (integral_eq_intervalIntegral_of_vanish hαβ.le fun x hx => by simp [ρc, hρz x hx]).symm
    have hρcD : ∀ x, HasDerivAt ρc ((deriv ρ x : ℝ) : ℂ) x := fun x => (hρ' x).ofReal_comp
    have hμ0 : ∫ x in α..β, μc x = 0 := by
      simp only [μc, intervalIntegral.integral_neg]
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hρcD x)
        ((Complex.continuous_ofReal.comp hρ'c).intervalIntegrable _ _)]
      simp [ρc, hρz α fun h => lt_irrefl _ h.1, hρz β fun h => lt_irrefl _ h.2]
    have hμ1 : ∫ x in α..β, (x : ℂ) * μc x = 1 := by
      have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := α) (b := β)
        (u := fun x : ℝ => (x : ℂ)) (u' := fun _ => 1) (v := ρc)
        (v' := fun x => ((deriv ρ x : ℝ) : ℂ))
        (fun x _ => by simpa using (hasDerivAt_id x).ofReal_comp) (fun x _ => hρcD x)
        intervalIntegrable_const ((Complex.continuous_ofReal.comp hρ'c).intervalIntegrable _ _)
      simp only [one_mul] at hibp
      simp only [μc, mul_neg, intervalIntegral.integral_neg]
      rw [hibp, hρ1']
      simp [ρc, hρz α fun h => lt_irrefl _ h.1, hρz β fun h => lt_irrefl _ h.2]
    have hχt0 : ∫ x in α..β, χt x = 0 := by
      simp only [χt]
      rw [intervalIntegral_sub_smul₃ (hχcc.intervalIntegrable _ _) (hρcc.intervalIntegrable _ _)
        (hμcc.intervalIntegrable _ _), hρ1', hμ0]
      ring
    have hχt1 : ∫ x in α..β, (x : ℂ) * χt x = 0 := by
      have e : ∀ x : ℝ, (x : ℂ) * χt x =
          (x : ℂ) * χc x - A * ((x : ℂ) * ρc x) - B * ((x : ℂ) * μc x) := fun x => by
        simp only [χt]; ring
      simp_rw [e]
      have c1 : Continuous fun x : ℝ => (x : ℂ) * χc x := Complex.continuous_ofReal.mul hχcc
      have c2 : Continuous fun x : ℝ => (x : ℂ) * ρc x := Complex.continuous_ofReal.mul hρcc
      have c3 : Continuous fun x : ℝ => (x : ℂ) * μc x := Complex.continuous_ofReal.mul hμcc
      rw [intervalIntegral_sub_smul₃ (c1.intervalIntegrable _ _) (c2.intervalIntegrable _ _)
        (c3.intervalIntegrable _ _), hm1', hμ1]
      simp only [B]
      ring
    obtain ⟨Ψ, hΨ2, hΨc, hΨs, hΨ''⟩ := exists_double_primitive hχtc hαβ.le hχtz hχt0 hχt1
    have hD0 := h Ψ ⟨hΨ2, hΨc, hΨs.trans hIcc⟩
    rw [hΨ''] at hD0
    -- expand `∫_X D χt = 0`
    have iD : ∀ f : ℝ → ℂ, Continuous f → IntervalIntegrable (fun x => D x * f x) volume α β :=
      fun f hf => intervalIntegrable_mul_of_locallyIntegrableOn hD hf hαβ.le hIcc
    have hDt : ∫ x in α..β, D x * χc x = A * a0 + B * b0 := by
      rw [setIntegral_eq_intervalIntegral_of_vanish hαβ.le hIcc fun x hx => by
        simp [hχtz x hx]] at hD0
      have e : ∀ x, D x * χt x = D x * χc x - A * (D x * ρc x) - B * (D x * μc x) := fun x => by
        simp only [χt]; ring
      simp_rw [e] at hD0
      rw [intervalIntegral_sub_smul₃ (iD _ hχcc) (iD _ hρcc) (iD _ hμcc)] at hD0
      have ha0 : a0 = ∫ x in α..β, D x * ρc x :=
        setIntegral_eq_intervalIntegral_of_vanish hαβ.le hIcc fun x hx => by simp [ρc, hρz x hx]
      have hb0 : b0 = ∫ x in α..β, D x * μc x :=
        setIntegral_eq_intervalIntegral_of_vanish hαβ.le hIcc fun x hx => by simp [μc, hρ'z x hx]
      rw [ha0, hb0]
      linear_combination hD0
    -- the target integral
    have e2 : ∀ x : ℝ, χ x • (D x - (a0 - b0 * m1 + b0 * x)) =
        D x * χc x - (a0 - b0 * m1) * χc x - b0 * ((x : ℂ) * χc x) := fun x => by
      simp only [χc, Complex.real_smul]; ring
    simp_rw [e2]
    rw [integral_eq_intervalIntegral_of_vanish hαβ.le fun x hx => by simp [χc, hχz x hx],
      intervalIntegral_sub_smul₃ (h := fun x : ℝ => (x : ℂ) * χc x) (iD _ hχcc)
        (hχcc.intervalIntegrable _ _)
        ((Complex.continuous_ofReal.mul hχcc).intervalIntegrable _ _), hDt]
    simp only [B]
    ring
  rw [ae_restrict_iff' hX.measurableSet]
  filter_upwards [key] with x hx hxX
  exact sub_eq_zero.mp (hx hxX)

/-! ### Regularity -/

theorem deriv_deriv_eq_zero_of_notMem {φ : ℝ → ℂ} {α β x : ℝ} (hs : tsupport φ ⊆ Ioo α β)
    (hx : x ∉ Ioo α β) : deriv (deriv φ) x = 0 := by
  have hz : φ =ᶠ[𝓝 x] 0 := (notMem_tsupport_iff_eventuallyEq).mp fun h => hx (hs h)
  have hd : deriv φ =ᶠ[𝓝 x] 0 := by
    filter_upwards [hz.eventuallyEq_nhds] with y hy
    rw [hy.deriv_eq]; simp
  rw [hd.deriv_eq]; simp

theorem deriv_eq_zero_of_notMem' {φ : ℝ → ℂ} {α β x : ℝ} (hs : tsupport φ ⊆ Ioo α β)
    (hx : x ∉ Ioo α β) : deriv φ x = 0 := by
  have hz : φ =ᶠ[𝓝 x] 0 := (notMem_tsupport_iff_eventuallyEq).mp fun h => hx (hs h)
  rw [hz.deriv_eq]; simp

variable {q : ℝ → ℝ}

/-- **Regularity of the maximal domain**: on an open interval `X`, if `ℒw = g` in the sense of
distributions with `w, g` locally integrable, then `w` agrees a.e. with a `C¹` function `F`
whose derivative is absolutely continuous: `F′(x) = F′(c) + ∫_c^x (qF − g)`. -/
theorem weak_regularity (hX : IsOpen X) (hXc : X.OrdConnected) (hne : X.Nonempty)
    (hq : ContinuousOn q X) {w g : ℝ → ℂ} (hw : LocallyIntegrableOn w X)
    (hg : LocallyIntegrableOn g X)
    (h : ∀ φ : ℝ → ℂ, IsC2c X φ →
      ∫ x in X, w x * schrodingerOp q φ x = ∫ x in X, g x * φ x) :
    ∃ F F' : ℝ → ℂ, w =ᵐ[volume.restrict X] F ∧ (∀ x ∈ X, HasDerivAt F (F' x) x) ∧
      ∀ c ∈ X, ∀ x ∈ X, F' x = F' c + ∫ t in c..x, ((q t : ℂ) * F t - g t) := by
  obtain ⟨c, hc⟩ := hne
  have hqc : ContinuousOn (fun x => (q x : ℂ)) X := Complex.continuous_ofReal.comp_continuousOn hq
  set h1 : ℝ → ℂ := fun t => (q t : ℂ) * w t - g t
  have hh1 : LocallyIntegrableOn h1 X := (hw.continuousOn_mul hqc hX.isLocallyClosed).sub hg
  have hii : ∀ {a b}, a ∈ X → b ∈ X → IntervalIntegrable h1 volume a b := fun ha hb =>
    (hh1.integrableOn_compact_subset (hXc.uIcc_subset ha hb) isCompact_uIcc).intervalIntegrable
  set K : ℝ → ℂ := fun t => ∫ s in c..t, h1 s
  have hKc : ContinuousOn K X := by
    intro x hx
    obtain ⟨α, β, hα, hβ, -, hxK, hcK⟩ := exists_Ioo_of_isCompact hX (isCompact_singleton (x := x))
      (singleton_subset_iff.mpr hx) hc
    have hcont := intervalIntegral.continuousOn_primitive_interval' (hii hα hβ)
      (a := c) (by rw [uIcc_of_le (hcK.1.trans hcK.2).le]; exact Ioo_subset_Icc_self hcK)
    have hxI : x ∈ Ioo α β := hxK rfl
    exact (hcont.continuousAt (Icc_mem_nhds hxI.1 hxI.2 |> fun h => by
      rw [uIcc_of_le (hxI.1.trans hxI.2).le]; exact h)).continuousWithinAt
  set H : ℝ → ℂ := fun x => ∫ t in c..x, K t
  have hKi : ∀ {a b}, a ∈ X → b ∈ X → IntervalIntegrable K volume a b := fun ha hb =>
    (hKc.mono (hXc.uIcc_subset ha hb)).intervalIntegrable
  have hH : ∀ x ∈ X, HasDerivAt H (K x) x := fun x hx =>
    intervalIntegral.integral_hasDerivAt_right (hKi hc hx)
      (hKc.stronglyMeasurableAtFilter hX x hx) (hKc.continuousAt (hX.mem_nhds hx))
  have hHc : ContinuousOn H X := fun x hx => (hH x hx).continuousAt.continuousWithinAt
  -- `∫ H φ″ = ∫ h1 φ` and `∫ w φ″ = ∫ h1 φ`
  have hD : ∀ φ : ℝ → ℂ, IsC2c X φ → ∫ x in X, (w x - H x) * deriv (deriv φ) x = 0 := by
    intro φ hφ
    obtain ⟨α, β, hα, hβ, hαβ, hK, hcK⟩ := exists_Ioo_of_isCompact hX hφ.2.1.isCompact hφ.2.2 hc
    have hIcc : Icc α β ⊆ X := hXc.out hα hβ
    have hφz : ∀ x ∉ Ioo α β, φ x = 0 := fun x hx =>
      ((notMem_tsupport_iff_eventuallyEq).mp fun h => hx (hK h)).eq_of_nhds
    have hφ'z : ∀ x ∉ Ioo α β, deriv φ x = 0 := fun x hx => deriv_eq_zero_of_notMem' hK hx
    have hφ''z : ∀ x ∉ Ioo α β, deriv (deriv φ) x = 0 := fun x hx =>
      deriv_deriv_eq_zero_of_notMem hK hx
    have hφd := fun x => (hasDerivAt_deriv_of_contDiff_two hφ.1 x).1
    have hφdd := fun x => (hasDerivAt_deriv_of_contDiff_two hφ.1 x).2
    have hφ'' : Continuous (deriv (deriv φ)) := continuous_deriv_deriv hφ.1
    have hφ' : Continuous (deriv φ) := continuous_deriv' hφ.1
    have hαX := hα
    -- `∫_α^β H φ″ = −∫_α^β K φ′`
    have e1 : ∫ x in α..β, H x * deriv (deriv φ) x = -∫ x in α..β, K x * deriv φ x := by
      have := intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := α) (b := β)
        (u := H) (u' := K) (v := deriv φ) (v' := deriv (deriv φ))
        (fun x hx => hH x (hIcc (by rwa [uIcc_of_le hαβ.le] at hx)))
        (fun x _ => hφdd x) (hKi hα hβ) (hφ''.intervalIntegrable _ _)
      rw [this, hφ'z α (fun h => lt_irrefl _ h.1), hφ'z β (fun h => lt_irrefl _ h.2)]
      simp
    -- `∫_α^β K φ′ = −∫_α^β h1 φ`
    have e2 : ∫ x in α..β, K x * deriv φ x = -∫ x in α..β, h1 x * φ x := by
      have hKsplit : ∀ t ∈ uIcc α β, K t = K α + ∫ s in α..t, h1 s := fun t ht => by
        simp only [K]
        rw [intervalIntegral.integral_add_adjacent_intervals (hii hc hα)
          (hii hα (hIcc (by rwa [uIcc_of_le hαβ.le] at ht)))]
      rw [intervalIntegral.integral_congr (g := fun t => K α * deriv φ t +
        (∫ s in α..t, h1 s) * deriv φ t) fun t ht => by simp only; rw [hKsplit t ht]; ring]
      have hprim : ContinuousOn (fun t => ∫ s in α..t, h1 s) (uIcc α β) :=
        intervalIntegral.continuousOn_primitive_interval
          (hh1.integrableOn_compact_subset (hXc.uIcc_subset hα hβ) isCompact_uIcc)
      rw [intervalIntegral.integral_add (f := fun t => K α * deriv φ t)
          (g := fun t => (∫ s in α..t, h1 s) * deriv φ t) ((hφ'.intervalIntegrable _ _).const_mul _)
          ((hprim.mul hφ'.continuousOn).intervalIntegrable),
        intervalIntegral.integral_const_mul,
        intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hφd x)
          (hφ'.intervalIntegrable _ _),
        integral_primitive_mul_deriv hαβ.le (hii hα hβ) hφd hφ',
        hφz α (fun h => lt_irrefl _ h.1), hφz β (fun h => lt_irrefl _ h.2)]
      simp
    -- the hypothesis on `[α, β]`
    have hqφ : Continuous fun x => (q x : ℂ) * φ x :=
      continuous_mul_of_tsupport hX hq hφ.1.continuous hφ.2.2
    have iw := fun f (hf : Continuous f) =>
      intervalIntegrable_mul_of_locallyIntegrableOn hw hf hαβ.le hIcc
    have ig := fun f (hf : Continuous f) =>
      intervalIntegrable_mul_of_locallyIntegrableOn hg hf hαβ.le hIcc
    have hyp := h φ hφ
    rw [setIntegral_eq_intervalIntegral_of_vanish hαβ.le hIcc fun x hx => by
        simp [schrodingerOp, hφz x hx, hφ''z x hx],
      setIntegral_eq_intervalIntegral_of_vanish hαβ.le hIcc fun x hx => by simp [hφz x hx]]
      at hyp
    have e3 : ∫ x in α..β, w x * schrodingerOp q φ x =
        -(∫ x in α..β, w x * deriv (deriv φ) x) + ∫ x in α..β, w x * ((q x : ℂ) * φ x) := by
      rw [← intervalIntegral.integral_neg, ← intervalIntegral.integral_add
        (f := fun x => -(w x * deriv (deriv φ) x)) (g := fun x => w x * ((q x : ℂ) * φ x))
        (iw _ hφ'').neg (iw _ hqφ)]
      refine intervalIntegral.integral_congr fun x _ => ?_
      simp only [schrodingerOp]; ring
    have e4 : ∫ x in α..β, h1 x * φ x =
        (∫ x in α..β, w x * ((q x : ℂ) * φ x)) - ∫ x in α..β, g x * φ x := by
      rw [← intervalIntegral.integral_sub (f := fun x => w x * ((q x : ℂ) * φ x))
        (g := fun x => g x * φ x) (iw _ hqφ) (ig _ hφ.1.continuous)]
      refine intervalIntegral.integral_congr fun x _ => ?_
      simp only [h1]; ring
    have e5 : ∫ x in α..β, (w x - H x) * deriv (deriv φ) x =
        (∫ x in α..β, w x * deriv (deriv φ) x) - ∫ x in α..β, H x * deriv (deriv φ) x := by
      rw [← intervalIntegral.integral_sub (f := fun x => w x * deriv (deriv φ) x)
        (g := fun x => H x * deriv (deriv φ) x) (iw _ hφ'')
        ((hHc.mono hIcc).mul hφ''.continuousOn |>.intervalIntegrable_of_Icc hαβ.le)]
      refine intervalIntegral.integral_congr fun x _ => ?_
      ring
    rw [setIntegral_eq_intervalIntegral_of_vanish hαβ.le hIcc fun x hx => by simp [hφ''z x hx],
      e5, e1, e2, e4]
    rw [e3] at hyp
    linear_combination (-1 : ℂ) * hyp
  have hDloc : LocallyIntegrableOn (fun x => w x - H x) X :=
    hw.sub (hHc.locallyIntegrableOn hX.measurableSet)
  obtain ⟨a, b, hab⟩ := ae_eq_affine_of_integral_deriv_deriv hX hXc ⟨c, hc⟩ hDloc hD
  have hwF : w =ᵐ[volume.restrict X] fun x => H x + a + b * x := by
    filter_upwards [hab] with x hx
    linear_combination hx
  refine ⟨fun x => H x + a + b * x, fun x => K x + b, hwF, fun x hx => ?_, ?_⟩
  · have hb : HasDerivAt (fun x : ℝ => b * (x : ℂ)) b x := by
      simpa using ((hasDerivAt_id x).ofReal_comp).const_mul b
    exact ((hH x hx).add_const a).add hb
  · intro c' hc' x hx
    have hsub := intervalIntegral.integral_interval_sub_left (hii hc hx) (hii hc hc')
    have hae : ∀ᵐ t ∂volume, t ∈ X → w t = H t + a + b * t :=
      (ae_restrict_iff' hX.measurableSet).mp hwF
    have hcongr : ∫ t in c'..x, h1 t = ∫ t in c'..x, ((q t : ℂ) * (H t + a + b * t) - g t) := by
      refine intervalIntegral.integral_congr_ae ?_
      filter_upwards [hae] with t ht htI
      have htX : t ∈ X := hXc.uIcc_subset hc' hx (uIoc_subset_uIcc htI)
      simp only [h1, ht htX]
    simp only
    rw [← hcongr, ← hsub]
    simp only [K]
    ring

end Azurite.DLMF
