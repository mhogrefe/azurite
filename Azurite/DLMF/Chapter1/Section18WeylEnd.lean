/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter1.Section18WeylODE

/-!
# DLMF §1.18(ix): the Weyl alternative

* `boundary_eq_zero_of_mem`, `boundary_eq_zero_of_bot`: the boundary form vanishes against
  `D(T**)`, and on all of `D(T*)` when `N_{±i} = 0`.
* `mem_adjoint_of_isC2c`: `C²_c(X)` functions lie in `𝒟(ℒ_Y*)` for subintervals `Y ⊆ X`.
* `exists_boundary_pair`, `boundaryForm_testFunctions`: test functions `e₁, e₂` near `c` with
  data `(0, 1)`, `(1, 0)`, whose boundary form on `X ∩ (−∞, c)`, resp. `X ∩ (c, ∞)`, is
  `±conj W(f, g)(c)`.
* `dlmf_1_18_ix_weyl_alternative`: `n₁, n₂ ∈ {1, 2}` for non-real `z`. If `n₁ = 0` the
  boundary form would vanish on `D(T₁*)`, but `B(e₁, e₂) ≠ 0`.
-/

open Set Filter Topology MeasureTheory LinearPMap
open scoped InnerProductSpace ComplexConjugate ContDiff

namespace Azurite.DLMF

/-! ### Abstract facts about the boundary form -/

section Abstract

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
  {T : V →ₗ.[ℂ] V}

/-- The boundary form `⟪T*x, y⟫ − ⟪x, T*y⟫` vanishes when `x ∈ D(T**)`. -/
theorem IsSymmetricDLMF.boundary_eq_zero_of_mem (hT : IsSymmetricDLMF T) (x y : T†.domain)
    (hx : (x : V) ∈ T††.domain) : ⟪T† x, (y : V)⟫_ℂ - ⟪(x : V), T† y⟫_ℂ = 0 := by
  have hle := hT.le_adjoint_adjoint.2
  have h1 := hT.inner_adjoint_adjoint ⟨x, hx⟩ y
  rw [hle.2 (x := ⟨x, hx⟩) (y := x) rfl] at h1
  rw [h1, sub_self]

/-- If `N_i = N_{−i} = 0` the boundary form vanishes on `D(T*)`. -/
theorem IsSymmetricDLMF.boundary_eq_zero_of_bot (hT : IsSymmetricDLMF T)
    (hpos : deficiencySpace T Complex.I = ⊥) (hneg : deficiencySpace T (-Complex.I) = ⊥)
    (x y : T†.domain) : ⟪T† x, (y : V)⟫_ℂ - ⟪(x : V), T† y⟫_ℂ = 0 := by
  obtain ⟨g, a, ha, b, hb, hx⟩ := hT.vonNeumann_decomp x
  obtain ⟨g', a', ha', b', hb', hy⟩ := hT.vonNeumann_decomp y
  rw [hT.boundaryForm x y g g' ha ha' hb hb' hx hy]
  rw [hpos, Submodule.mem_bot] at ha ha'
  rw [hneg, Submodule.mem_bot] at hb hb'
  simp [ha, ha', hb, hb']

end Abstract

/-! ### `C²_c(X)` functions in the adjoint domain of a subinterval -/

variable {X : Set ℝ} {q : ℝ → ℝ}

theorem IsC2c.memLp_on {f : ℝ → ℂ} (hf : IsC2c X f) (Y : Set ℝ) :
    MemLp f 2 (volume.restrict Y) :=
  (hf.1.continuous.memLp_of_hasCompactSupport hf.2.1).restrict Y

theorem IsC2c.memLp_schrodingerOp_on (hX : IsOpen X) (hq : ContinuousOn q X) {f : ℝ → ℂ}
    (hf : IsC2c X f) (Y : Set ℝ) : MemLp (schrodingerOp q f) 2 (volume.restrict Y) :=
  ((continuous_schrodingerOp hX hq hf).memLp_of_hasCompactSupport
    (hf.2.1.mono' (support_schrodingerOp_subset q f))).restrict Y

/-- A `C²_c(X)` function lies in `𝒟(ℒ_Y*)` for any open `Y ⊆ X`, with `ℒ_Y* f = ℒf`. -/
theorem mem_adjoint_of_isC2c (hX : IsOpen X) (hq : ContinuousOn q X) {Y : Set ℝ} (hY : IsOpen Y)
    (hYX : Y ⊆ X) {f : ℝ → ℂ} (hf : IsC2c X f) :
    ∃ h : (hf.memLp_on Y).toLp ∈ (minOp Y q)†.domain,
      (minOp Y q)† ⟨_, h⟩ = (hf.memLp_schrodingerOp_on hX hq Y).toLp := by
  have hqY : ContinuousOn q Y := hq.mono hYX
  have hweak : ∀ φ : ℝ → ℂ, IsC2c Y φ →
      ∫ x in Y, ((hf.memLp_on Y).toLp : ℝ → ℂ) x * schrodingerOp q φ x =
        ∫ x in Y, ((hf.memLp_schrodingerOp_on hX hq Y).toLp : ℝ → ℂ) x * φ x := by
    intro φ hφ
    have hφX : IsC2c X φ := ⟨hφ.1, hφ.2.1, hφ.2.2.trans hYX⟩
    have e1 : ∫ x in Y, ((hf.memLp_on Y).toLp : ℝ → ℂ) x * schrodingerOp q φ x =
        ∫ x in Y, f x * schrodingerOp q φ x :=
      integral_congr_ae (by filter_upwards [(hf.memLp_on Y).coeFn_toLp] with x hx; rw [hx])
    have e2 : ∫ x in Y, ((hf.memLp_schrodingerOp_on hX hq Y).toLp : ℝ → ℂ) x * φ x =
        ∫ x in Y, schrodingerOp q f x * φ x :=
      integral_congr_ae (by
        filter_upwards [(hf.memLp_schrodingerOp_on hX hq Y).coeFn_toLp] with x hx; rw [hx])
    have hφz : ∀ x ∉ Y, φ x = 0 := fun x hx => image_eq_zero_of_notMem_tsupport
      fun h => hx (hφ.2.2 h)
    have hLφz : ∀ x ∉ Y, schrodingerOp q φ x = 0 := fun x hx => by
      by_contra h
      exact hx (hφ.2.2 (support_schrodingerOp_subset q φ h))
    have hsym := dlmf_1_18_iv_symmetric hX hq hf hφX.conj
    rw [schrodingerOp_conj q hφ.1] at hsym
    simp only [Complex.conj_conj] at hsym
    rw [e1, e2, setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by simp [hLφz x hx],
      setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by simp [hφz x hx]]
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
        simp [image_eq_zero_of_notMem_tsupport fun h => hx (hφX.2.2 h)],
      setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
        simp [show schrodingerOp q φ x = 0 by
          by_contra h; exact hx (hφX.2.2 (support_schrodingerOp_subset q φ h))]] at hsym
    exact hsym.symm
  have hmem := (dlmf_1_18_ix_maxDomain hY hqY _).mpr ⟨_, hweak⟩
  exact ⟨hmem, minOp_adjoint_apply hY hqY ⟨_, hmem⟩ _ hweak⟩

/-! ### Test functions at an interior point -/

/-- Functions `e₁ = χ·(x − c)` and `e₂ = χ`, `χ = 1` near `c`, supported in `(c − r, c + r)`. -/
theorem exists_boundary_pair {c r : ℝ} (hr : 0 < r) (hIcc : Icc (c - r) (c + r) ⊆ X) :
    ∃ e₁ e₂ : ℝ → ℂ, IsC2c X e₁ ∧ IsC2c X e₂ ∧ tsupport e₁ ⊆ Ioo (c - r) (c + r) ∧
      tsupport e₂ ⊆ Ioo (c - r) (c + r) ∧ e₁ c = 0 ∧ deriv e₁ c = 1 ∧ e₂ c = 1 ∧
        deriv e₂ c = 0 := by
  let χ : ContDiffBump c := ⟨r / 4, r / 2, by positivity, by linarith⟩
  have hts : tsupport χ ⊆ Ioo (c - r) (c + r) := by
    rw [χ.tsupport_eq]
    intro x hx
    rw [Metric.mem_closedBall, Real.dist_eq] at hx
    have h1 : χ.rOut = r / 2 := rfl
    rw [h1] at hx
    constructor <;> linarith [abs_le.mp hx]
  set e₂ : ℝ → ℂ := fun x => ((χ x : ℝ) : ℂ)
  set e₁ : ℝ → ℂ := fun x => ((χ x : ℝ) : ℂ) * ((x : ℂ) - c)
  have hχd : ContDiff ℝ 2 fun x => ((χ x : ℝ) : ℂ) :=
    Complex.ofRealCLM.contDiff.comp χ.contDiff
  have hts₂ : tsupport e₂ ⊆ Ioo (c - r) (c + r) :=
    (tsupport_comp_subset Complex.ofReal_zero _).trans hts
  have hts₁ : tsupport e₁ ⊆ Ioo (c - r) (c + r) := tsupport_mul_subset_left.trans hts₂
  have hX₂ : IsC2c X e₂ := ⟨hχd, HasCompactSupport.intro isCompact_Icc fun x hx => by
      by_contra h; exact hx (Ioo_subset_Icc_self (hts₂ (subset_tsupport _ h))),
    hts₂.trans (Ioo_subset_Icc_self.trans hIcc)⟩
  have hX₁ : IsC2c X e₁ := ⟨hχd.mul (Complex.ofRealCLM.contDiff.sub contDiff_const),
    HasCompactSupport.intro isCompact_Icc
      fun x hx => by
        by_contra h; exact hx (Ioo_subset_Icc_self (hts₁ (subset_tsupport _ h))),
    hts₁.trans (Ioo_subset_Icc_self.trans hIcc)⟩
  have hone : ∀ᶠ x in 𝓝 c, χ x = 1 := χ.eventuallyEq_one
  have he₂ : e₂ =ᶠ[𝓝 c] fun _ => 1 := by
    filter_upwards [hone] with x hx; simp [e₂, hx]
  have he₁ : e₁ =ᶠ[𝓝 c] fun x => (x : ℂ) - c := by
    filter_upwards [hone] with x hx; simp [e₁, hx]
  refine ⟨e₁, e₂, hX₁, hX₂, hts₁, hts₂, ?_, ?_, ?_, ?_⟩
  · simp [e₁]
  · rw [he₁.deriv_eq]
    have := ((hasDerivAt_id c).ofReal_comp.sub_const (c : ℂ)).deriv
    simpa using this
  · simp [e₂, χ.one_of_mem_closedBall (Metric.mem_closedBall_self χ.rIn_pos.le)]
  · rw [he₂.deriv_eq]; simp

/-- The boundary form of two test functions supported near `c`, on `Y = X ∩ (−∞, c)` and on
`Y = X ∩ (c, ∞)`: `±conj W(f, g)(c)`. -/
theorem boundaryForm_testFunctions (hX : IsOpen X) (hq : ContinuousOn q X) {c r : ℝ}
    (hr : 0 < r) (hIcc : Icc (c - r) (c + r) ⊆ X) {f g : ℝ → ℂ} (hf : IsC2c X f)
    (hg : IsC2c X g) (hfs : tsupport f ⊆ Ioo (c - r) (c + r))
    (hgs : tsupport g ⊆ Ioo (c - r) (c + r)) {Y : Set ℝ} (hY : IsOpen Y) (hYX : Y ⊆ X)
    (s : ℂ) (hside : (Y = X ∩ Iio c ∧ s = 1) ∨ (Y = X ∩ Ioi c ∧ s = -1)) :
    ∃ hF : (hf.memLp_on Y).toLp ∈ (minOp Y q)†.domain,
    ∃ hG : (hg.memLp_on Y).toLp ∈ (minOp Y q)†.domain,
      ⟪(minOp Y q)† ⟨_, hF⟩, (hg.memLp_on Y).toLp⟫_ℂ -
          ⟪(hf.memLp_on Y).toLp, (minOp Y q)† ⟨_, hG⟩⟫_ℂ = s * conj (wronskianConj f g c) := by
  obtain ⟨hF, hTF⟩ := mem_adjoint_of_isC2c hX hq hY hYX hf
  obtain ⟨hG, hTG⟩ := mem_adjoint_of_isC2c hX hq hY hYX hg
  refine ⟨hF, hG, ?_⟩
  rw [hTF, hTG, inner_L2X, inner_L2X]
  have hLf := continuous_schrodingerOp hX hq hf
  have hLg := continuous_schrodingerOp hX hq hg
  set H : ℝ → ℂ := fun x => schrodingerOp q f x * conj (g x) - f x * conj (schrodingerOp q g x)
  have hHc : Continuous H := (hLf.mul (Complex.continuous_conj.comp hg.1.continuous)).sub
    (hf.1.continuous.mul (Complex.continuous_conj.comp hLg))
  have hzero : ∀ x ∉ Ioo (c - r) (c + r), f x = 0 ∧ g x = 0 ∧ deriv f x = 0 ∧
      deriv g x = 0 ∧ schrodingerOp q f x = 0 ∧ schrodingerOp q g x = 0 := fun x hx => by
    have hfx : f =ᶠ[𝓝 x] 0 := (notMem_tsupport_iff_eventuallyEq).mp fun h => hx (hfs h)
    have hgx : g =ᶠ[𝓝 x] 0 := (notMem_tsupport_iff_eventuallyEq).mp fun h => hx (hgs h)
    refine ⟨hfx.eq_of_nhds, hgx.eq_of_nhds, by rw [hfx.deriv_eq]; simp,
      by rw [hgx.deriv_eq]; simp, ?_, ?_⟩
    · by_contra h; exact hx (hfs (support_schrodingerOp_subset q f h))
    · by_contra h; exact hx (hgs (support_schrodingerOp_subset q g h))
  have hHz : ∀ x ∉ Ioo (c - r) (c + r), H x = 0 := fun x hx => by
    obtain ⟨h1, h2, -, -, h5, h6⟩ := hzero x hx
    simp [H, h1, h2, h5, h6]
  have hcs : ∀ {F : ℝ → ℂ}, Continuous F → (∀ x ∉ Ioo (c - r) (c + r), F x = 0) →
      Integrable F := fun hF hz => hF.integrable_of_hasCompactSupport
    (HasCompactSupport.intro isCompact_Icc fun x hx => hz x fun h => hx (Ioo_subset_Icc_self h))
  have I1 : ∫ x in Y, conj (((hf.memLp_schrodingerOp_on hX hq Y).toLp : ℝ → ℂ) x) *
      ((hg.memLp_on Y).toLp : ℝ → ℂ) x = ∫ x in Y, conj (schrodingerOp q f x) * g x :=
    integral_congr_ae (by
      filter_upwards [(hf.memLp_schrodingerOp_on hX hq Y).coeFn_toLp,
        (hg.memLp_on Y).coeFn_toLp] with x h1 h2
      rw [h1, h2])
  have I2 : ∫ x in Y, conj (((hf.memLp_on Y).toLp : ℝ → ℂ) x) *
      ((hg.memLp_schrodingerOp_on hX hq Y).toLp : ℝ → ℂ) x =
        ∫ x in Y, conj (f x) * schrodingerOp q g x :=
    integral_congr_ae (by
      filter_upwards [(hf.memLp_on Y).coeFn_toLp,
        (hg.memLp_schrodingerOp_on hX hq Y).coeFn_toLp] with x h1 h2
      rw [h1, h2])
  have c1 : Continuous fun x => conj (schrodingerOp q f x) * g x :=
    (Complex.continuous_conj.comp hLf).mul hg.1.continuous
  have c2 : Continuous fun x => conj (f x) * schrodingerOp q g x :=
    (Complex.continuous_conj.comp hf.1.continuous).mul hLg
  rw [I1, I2, ← integral_sub (hcs c1 fun x hx => by simp [(hzero x hx).2.1]).integrableOn
    (hcs c2 fun x hx => by simp [(hzero x hx).1]).integrableOn]
  have e3 : ∫ x in Y, (conj (schrodingerOp q f x) * g x - conj (f x) * schrodingerOp q g x) =
      conj (∫ x in Y, H x) := by
    rw [← integral_conj]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    simp [H, _root_.map_sub, map_mul]
  rw [e3]
  -- reduce to an interval integral and apply Green's formula
  have hgreen := dlmf_1_18_iv_green q hf.1 hg.1
  have hWz : ∀ x ∉ Ioo (c - r) (c + r), wronskianConj f g x = 0 := fun x hx => by
    obtain ⟨h1, -, h3, -, -, -⟩ := hzero x hx
    simp [wronskianConj, h1, h3]
  have hl : c - r ∉ Ioo (c - r) (c + r) := fun h => lt_irrefl _ h.1
  have hu : c + r ∉ Ioo (c - r) (c + r) := fun h => lt_irrefl _ h.2
  rcases hside with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · have hsub : Ioo (c - r) c ⊆ X ∩ Iio c := fun x hx =>
      ⟨hIcc ⟨hx.1.le, by linarith [hx.2]⟩, hx.2⟩
    rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero (hY.measurableSet) hsub
      fun x hx => hHz x fun h => hx.2 ⟨h.1, hx.1.2⟩, ← integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le (by linarith), hgreen, hWz _ hl, sub_zero, one_mul]
  · have hsub : Ioo c (c + r) ⊆ X ∩ Ioi c := fun x hx =>
      ⟨hIcc ⟨by linarith [hx.1], hx.2.le⟩, hx.1⟩
    rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero (hY.measurableSet) hsub
      fun x hx => hHz x fun h => hx.2 ⟨hx.1.2, h.2⟩, ← integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le (by linarith), hgreen, hWz _ hu, zero_sub, _root_.map_neg]
    ring

/-! ### The Weyl alternative -/

theorem exists_Icc_ball (hX : IsOpen X) {c : ℝ} (hc : c ∈ X) :
    ∃ r > 0, Icc (c - r) (c + r) ⊆ X := by
  obtain ⟨R, hR, hball⟩ := Metric.isOpen_iff.mp hX c hc
  refine ⟨R / 2, by positivity, fun x hx => hball ?_⟩
  rw [Metric.mem_ball, Real.dist_eq, abs_lt]
  constructor <;> linarith [hx.1, hx.2]

/-- The two half-intervals `X ∩ (−∞, c)` and `X ∩ (c, ∞)` are open intervals containing points
near `c`. -/
theorem halfInterval_props (hX : IsOpen X) (hXc : X.OrdConnected) {c : ℝ} (hc : c ∈ X)
    {Y : Set ℝ} (hside : Y = X ∩ Iio c ∨ Y = X ∩ Ioi c) :
    IsOpen Y ∧ Y.OrdConnected ∧ Y.Nonempty ∧ Y ⊆ X := by
  obtain ⟨r, hr, hIcc⟩ := exists_Icc_ball hX hc
  rcases hside with rfl | rfl
  · exact ⟨hX.inter isOpen_Iio, hXc.inter ordConnected_Iio,
      ⟨c - r, hIcc ⟨le_rfl, by linarith⟩, by simp [hr]⟩, inter_subset_left⟩
  · exact ⟨hX.inter isOpen_Ioi, hXc.inter ordConnected_Ioi,
      ⟨c + r, hIcc ⟨by linarith, le_rfl⟩, by simp [hr]⟩, inter_subset_left⟩

/-- For a symmetric operator with finite deficiency spaces, `dim N_z = 0` for one non-real `z`
forces `N_i = N_{−i} = 0`, when `dim N_z = dim N_{z̄}`. -/
theorem deficiency_bot_of_finrank_zero {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [CompleteSpace V] {T : V →ₗ.[ℂ] V} (hT : IsSymmetricDLMF T)
    (hconj : ∀ w : ℂ, Module.finrank ℂ (deficiencySpace T w) =
      Module.finrank ℂ (deficiencySpace T (conj w)))
    [∀ w : ℂ, FiniteDimensional ℂ (deficiencySpace T w)] {z : ℂ} (hz : z.im ≠ 0)
    (h0 : Module.finrank ℂ (deficiencySpace T z) = 0) :
    deficiencySpace T Complex.I = ⊥ ∧ deficiencySpace T (-Complex.I) = ⊥ := by
  have hfr : ∀ w w' : ℂ, Module.rank ℂ (deficiencySpace T w) =
      Module.rank ℂ (deficiencySpace T w') →
      Module.finrank ℂ (deficiencySpace T w) = Module.finrank ℂ (deficiencySpace T w') :=
    fun w w' h => by unfold Module.finrank; rw [h]
  have hI : Module.finrank ℂ (deficiencySpace T Complex.I) = 0 := by
    rcases lt_or_gt_of_ne hz with hlt | hgt
    · have h1 := hfr _ _ (dlmf_1_18_ix_deficiency_const hT (z := z) (w := -Complex.I)
        (Or.inr ⟨hlt, by simp⟩))
      rw [hconj Complex.I, Complex.conj_I, ← h1, h0]
    · have h1 := hfr _ _ (dlmf_1_18_ix_deficiency_const hT (z := z) (w := Complex.I)
        (Or.inl ⟨hgt, by simp⟩))
      rw [← h1, h0]
  have hmI : Module.finrank ℂ (deficiencySpace T (-Complex.I)) = 0 := by
    rw [← Complex.conj_I, ← hconj, hI]
  exact ⟨Submodule.finrank_eq_zero.mp hI, Submodule.finrank_eq_zero.mp hmI⟩

/-- **DLMF §1.18(ix), Weyl's alternative**: for `c ∈ X` and non-real `z`, the deficiency index
`n₁ = dim N_z` of `ℒ` restricted to `X ∩ (−∞, c)` is `1` (limit point) or `2` (limit circle);
likewise `n₂` for `X ∩ (c, ∞)`. -/
theorem dlmf_1_18_ix_weyl_alternative (hX : IsOpen X) (hXc : X.OrdConnected)
    (hq : ContinuousOn q X) {c : ℝ} (hc : c ∈ X) {z : ℂ} (hz : z.im ≠ 0) {Y : Set ℝ}
    (hside : Y = X ∩ Iio c ∨ Y = X ∩ Ioi c) :
    1 ≤ Module.finrank ℂ (deficiencySpace (minOp Y q) z) ∧
      Module.finrank ℂ (deficiencySpace (minOp Y q) z) ≤ 2 := by
  obtain ⟨hYo, hYc, hYne, hYX⟩ := halfInterval_props hX hXc hc hside
  have hqY : ContinuousOn q Y := hq.mono hYX
  refine ⟨?_, (dlmf_1_18_ix_finrank_le hYo hYc hYne hqY z).2⟩
  by_contra h
  push Not at h
  have h0 : Module.finrank ℂ (deficiencySpace (minOp Y q) z) = 0 := by omega
  have : ∀ w : ℂ, FiniteDimensional ℂ (deficiencySpace (minOp Y q) w) := fun w =>
    (dlmf_1_18_ix_finrank_le hYo hYc hYne hqY w).1
  have hT := isSymmetricDLMF_minOp hYo hqY
  obtain ⟨hpos, hneg⟩ := deficiency_bot_of_finrank_zero hT
    (dlmf_1_18_ix_deficiency_eq hYo hYc hYne hqY) hz h0
  obtain ⟨r, hr, hIcc⟩ := exists_Icc_ball hX hc
  obtain ⟨e₁, e₂, h₁, h₂, hs₁, hs₂, he₁c, he₁d, he₂c, he₂d⟩ := exists_boundary_pair hr hIcc
  obtain ⟨s, hs, hs0⟩ : ∃ s : ℂ, ((Y = X ∩ Iio c ∧ s = 1) ∨ (Y = X ∩ Ioi c ∧ s = -1)) ∧
      s ≠ 0 := by
    rcases hside with h | h
    · exact ⟨1, Or.inl ⟨h, rfl⟩, one_ne_zero⟩
    · exact ⟨-1, Or.inr ⟨h, rfl⟩, by norm_num⟩
  obtain ⟨hF, hG, hB⟩ := boundaryForm_testFunctions hX hq hr hIcc h₁ h₂ hs₁ hs₂ hYo hYX s hs
  have hzero := hT.boundary_eq_zero_of_bot hpos hneg ⟨_, hF⟩ ⟨_, hG⟩
  rw [hB] at hzero
  have hW : wronskianConj e₁ e₂ c = -1 := by simp [wronskianConj, he₁c, he₁d, he₂c, he₂d]
  rw [hW] at hzero
  simp [hs0] at hzero

end Azurite.DLMF
