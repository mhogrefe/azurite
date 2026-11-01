/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter1.Section18WeylLC

/-!
# DLMF §1.18(ix): self-adjoint extensions by boundary conditions

* `IsSymmetricDLMF.unique_selfAdjoint_of_bot`: with zero deficiency indices `T*` is the unique
  self-adjoint extension.
* `IsSymmetricDLMF.exists_form_of_finrank_one`: with deficiency indices `(1, 1)` every
  self-adjoint extension is `T*` restricted to the kernel of one nonzero boundary form.
* `formBV`, `formBV_isBoundaryValue`; `boundaryValue_eq_zero_of_vanishesNear_left` (`_right`):
  if `b` (resp. `a`) is limit point, every boundary value is a boundary value at `a` (resp. `b`).
* `dlmf_1_18_ix_ext_LP_LP`, `dlmf_1_18_ix_ext_LC_LP`, `dlmf_1_18_ix_ext_LP_LC`: DLMF's
  description of the self-adjoint extensions when at most one end is limit circle.
-/

open Set Filter Topology MeasureTheory LinearPMap Complex
open scoped InnerProductSpace ComplexConjugate ContDiff

namespace Azurite.DLMF

/-! ### Abstract part -/

section Abstract

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
  {T : V →ₗ.[ℂ] V}

/-- Zero deficiency indices: `T* = T**`. -/
theorem IsSymmetricDLMF.adjoint_eq_of_bot (hT : IsSymmetricDLMF T)
    (hI : deficiencySpace T I = ⊥) (hmI : deficiencySpace T (-I) = ⊥) : T† = T†† := by
  have hle := hT.le_adjoint_adjoint.2
  have h1 : T† ≤ T†† := ⟨fun x hx => ?_, fun x y hxy => (hle.2 hxy.symm).symm⟩
  · exact le_antisymm h1 hle
  obtain ⟨g, a, ha, b, hb, h⟩ := hT.vonNeumann_decomp ⟨x, hx⟩
  rw [hI, Submodule.mem_bot] at ha
  rw [hmI, Submodule.mem_bot] at hb
  have : x = g := by simpa [ha, hb] using h
  rw [this]; exact g.2

/-- Zero deficiency indices: `T*` is self-adjoint and is the unique self-adjoint extension. -/
theorem IsSymmetricDLMF.unique_selfAdjoint_of_bot (hT : IsSymmetricDLMF T)
    (hI : deficiencySpace T I = ⊥) (hmI : deficiencySpace T (-I) = ⊥) :
    IsSelfAdjoint T† ∧ ∀ A : V →ₗ.[ℂ] V, IsSelfAdjoint A → T ≤ A → A = T† := by
  have h := hT.adjoint_eq_of_bot hI hmI
  refine ⟨isSelfAdjoint_def.mpr h.symm, fun A hA hTA => le_antisymm
    (le_adjoint_of_selfAdjoint_ext hT hA hTA) ?_⟩
  rw [h]
  exact adjoint_adjoint_le_of_selfAdjoint_ext hT hA hTA

/-- Deficiency indices `(1, 1)`: every self-adjoint extension `A` is the restriction of `T*` to
the kernel of one nonzero boundary form `f ↦ ⟨T*w, f⟩ − ⟨w, T*f⟩`. -/
theorem IsSymmetricDLMF.exists_form_of_finrank_one (hT : IsSymmetricDLMF T)
    (hI1 : Module.finrank ℂ (deficiencySpace T I) = 1) {A : V →ₗ.[ℂ] V} (hA : IsSelfAdjoint A)
    (hTA : T ≤ A) :
    ∃ w : T†.domain, (∀ f : T†.domain,
      (f : V) ∈ A.domain ↔ ⟪T† w, (f : V)⟫_ℂ - ⟪(w : V), T† f⟫_ℂ = 0) ∧
      ∃ f : T†.domain, ⟪T† w, (f : V)⟫_ℂ - ⟪(w : V), T† f⟫_ℂ ≠ 0 := by
  obtain ⟨U, hAU⟩ := eq_vonNeumannExt_of_selfAdjoint hT hA hTA
  obtain ⟨e, he0, hspan⟩ := finrank_eq_one_iff'.mp hI1
  have hAT := le_adjoint_of_selfAdjoint_ext hT hA hTA
  have hwD : (e : V) + (U e : V) ∈ vonNeumannDomain T U.toLinearIsometry :=
    mem_vonNeumannDomain.mpr ⟨0, e, by simp⟩
  have hwT : (e : V) + (U e : V) ∈ T†.domain := hT.vonNeumannDomain_le _ hwD
  have hwA : (e : V) + (U e : V) ∈ A.domain := by
    rw [hAU]; exact ⟨hwD, hwT⟩
  set w : T†.domain := ⟨_, hwT⟩
  have hne : (e : V) ≠ 0 := fun h => he0 (Subtype.ext h)
  have hnorm : ‖(U e : V)‖ = ‖(e : V)‖ := by
    rw [Submodule.norm_coe, Submodule.norm_coe, U.norm_map]
  have hee : ⟪(e : V), (e : V)⟫_ℂ = ((‖(e : V)‖ ^ 2 : ℝ) : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K]; push_cast; rfl
  have hUU : ⟪(U e : V), (U e : V)⟫_ℂ = ((‖(e : V)‖ ^ 2 : ℝ) : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K, hnorm]; push_cast; rfl
  have hpos : ((‖(e : V)‖ ^ 2 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast pow_ne_zero 2 (norm_ne_zero_iff.mpr hne)
  -- the form in coordinates
  have hform : ∀ f : T†.domain, ∃ g : (T††).domain, ∃ α β : ℂ,
      (f : V) = g + α • (e : V) + β • (U e : V) ∧
      ⟪T† w, (f : V)⟫_ℂ - ⟪(w : V), T† f⟫_ℂ =
        2 * I * ((β - α) * ((‖(e : V)‖ ^ 2 : ℝ) : ℂ)) := fun f => by
    obtain ⟨g, a, ha, b, hb, hf⟩ := hT.vonNeumann_decomp f
    obtain ⟨α, hα⟩ := hspan ⟨a, ha⟩
    obtain ⟨b', hb'⟩ := U.surjective ⟨b, hb⟩
    obtain ⟨β, hβ⟩ := hspan b'
    have ha' : a = α • (e : V) := by
      have := congrArg Subtype.val hα; simpa using this.symm
    have hb'' : b = β • (U e : V) := by
      have := congrArg Subtype.val hb'
      rw [← hβ, LinearIsometryEquiv.map_smul] at this
      simpa using this.symm
    refine ⟨g, α, β, by rw [hf, ha', hb''], ?_⟩
    rw [hT.boundaryForm w f 0 g e.2 ha (U e).2 hb (by simp [w]) hf, ha', hb'', inner_smul_right,
      inner_smul_right, hee, hUU]
    ring
  refine ⟨w, fun f => ⟨fun hfA => ?_, fun h0 => ?_⟩, ?_⟩
  · -- `A` is symmetric
    have hs := (IsSelfAdjoint.isSymmetricDLMF hA).isFormalAdjoint ⟨_, hwA⟩ ⟨_, hfA⟩
    rw [hAT.2 (x := ⟨_, hwA⟩) (y := w) rfl, hAT.2 (x := ⟨_, hfA⟩) (y := f) rfl] at hs
    rw [hs, sub_self]
  · obtain ⟨g, α, β, hf, hfo⟩ := hform f
    rw [hfo] at h0
    have hαβ : β = α := by
      have := mul_eq_zero.mp h0
      rcases this with h | h
      · exact absurd h (mul_ne_zero two_ne_zero I_ne_zero)
      · exact sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_right hpos)
    rw [hAU]
    refine ⟨mem_vonNeumannDomain.mpr ⟨g, α • e, ?_⟩, f.2⟩
    rw [hf, hαβ, LinearIsometryEquiv.coe_toLinearIsometry, LinearIsometryEquiv.map_smul]
    simp [add_assoc]
  · have heT : (e : V) ∈ T†.domain := (mem_eigenspaceDLMF.mp e.2).1
    refine ⟨⟨_, heT⟩, ?_⟩
    rw [hT.boundaryForm w ⟨_, heT⟩ 0 0 e.2 e.2 (U e).2 (Submodule.zero_mem _) (by simp [w])
      (by simp), inner_zero_right, hee]
    simpa using hpos

end Abstract

/-! ### Boundary forms as boundary values -/

variable {X : Set ℝ} {q : ℝ → ℝ}

/-- The boundary form `f ↦ ⟨ℒ*w, f⟩ − ⟨w, ℒ*f⟩` of `w ∈ 𝒟(ℒ*)`. -/
noncomputable def formBV (w : (minOp X q)†.domain) : (minOp X q)†.domain →ₗ[ℂ] ℂ :=
  (innerₛₗ ℂ ((minOp X q)† w)) ∘ₗ (minOp X q)†.domain.subtype -
    (innerₛₗ ℂ (w : L2X X)) ∘ₗ (minOp X q)†.toFun

theorem formBV_apply (w f : (minOp X q)†.domain) :
    formBV w f = ⟪(minOp X q)† w, (f : L2X X)⟫_ℂ - ⟪(w : L2X X), (minOp X q)† f⟫_ℂ := rfl

theorem formBV_isBoundaryValue (hX : IsOpen X) (hq : ContinuousOn q X)
    (w : (minOp X q)†.domain) : IsBoundaryValue X q (formBV w) := by
  have hT := isSymmetricDLMF_minOp hX hq
  refine ⟨⟨‖(minOp X q)† w‖ + ‖(w : L2X X)‖, fun f => ?_⟩, fun f hf => ?_⟩
  · rw [formBV_apply]
    refine (norm_sub_le _ _).trans ?_
    have h1 := norm_inner_le_norm (𝕜 := ℂ) ((minOp X q)† w) (f : L2X X)
    have h2 := norm_inner_le_norm (𝕜 := ℂ) (w : L2X X) ((minOp X q)† f)
    have := norm_nonneg ((minOp X q)† w)
    have := norm_nonneg (w : L2X X)
    have := norm_nonneg (f : L2X X)
    have := norm_nonneg ((minOp X q)† f)
    nlinarith
  · rw [formBV_apply, adjoint_isFormalAdjoint (dense_minOp_domain hX hq) w ⟨_, hf⟩,
      hT.le_adjoint.2 (x := ⟨_, hf⟩) (y := f) rfl, sub_self]

/-- If `b` is limit point, every boundary value vanishes on functions vanishing near `a`. -/
theorem boundaryValue_eq_zero_of_vanishesNear_left (hX : IsOpen X) (hXc : X.OrdConnected)
    (hq : ContinuousOn q X) {c : ℝ} (hc : c ∈ X) {z : ℂ} (hz : z.im ≠ 0)
    (h1 : Module.finrank ℂ (deficiencySpace (minOp (X ∩ Ioi c) q) z) = 1)
    {B : (minOp X q)†.domain →ₗ[ℂ] ℂ} (hB : IsBoundaryValue X q B) (f : (minOp X q)†.domain)
    (hf : VanishesNear X q (fun d => X ∩ Iio d) f) : B f = 0 := by
  obtain ⟨d, hd, hfd⟩ := hf
  obtain ⟨r, hr, hIr⟩ := exists_Icc_ball hX hd
  have hc' : d - r ∈ X := hIr ⟨le_rfl, by linarith⟩
  have h1' : Module.finrank ℂ (deficiencySpace (minOp (X ∩ Ioi (d - r)) q) z) = 1 := by
    rw [← (dlmf_1_18_ix_index_indep hX hXc hq hc hc' hz).2, h1]
  obtain ⟨R', hR', hIR'⟩ := exists_Icc_ball hX hc'
  set R := min R' r
  have hR : 0 < R := lt_min hR' hr
  have hRr : R ≤ r := min_le_right _ _
  have hIccR : Icc (d - r - R) (d - r + R) ⊆ X := fun x hx =>
    hIR' ⟨by linarith [hx.1, min_le_left R' r], by linarith [hx.2, min_le_left R' r]⟩
  set c' := d - r
  obtain ⟨χ, hχ, hχb, hχ1, hχ0, hχc⟩ :=
    exists_cutoff (show c' + R / 2 < c' + 3 * R / 4 by linarith)
  set η : ℝ → ℝ := fun x => 1 - χ x
  have hIcc : Icc (c' - R / 4) (c' + R / 4) ⊆ X := fun x hx =>
    hIccR ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hαβ : Icc (c' + R / 4) (c' + R) ⊆ X := fun x hx => hIccR ⟨by linarith [hx.1], hx.2⟩
  have hηc : ∀ x ∉ Ioo (c' + R / 4) (c' + R), deriv η =ᶠ[𝓝 x] 0 := fun x hx => by
    filter_upwards [hχc _ _ (by linarith) (by linarith) x hx] with y hy
    simp only [η, deriv_const_sub, hy, Pi.zero_apply, neg_zero]
  obtain ⟨hwF, -, -⟩ := maxRep_spec hX hXc ⟨c, hc⟩ hq f
  obtain ⟨g, hg, hBg⟩ := hB.exists_cutoff_eq_zero hX hXc hq hc' hz (-1) (Or.inr ⟨rfl, rfl⟩) h1'
    (by positivity : (0 : ℝ) < R / 4) hIcc f (contDiff_const.sub hχ)
    (fun x => abs_le.mpr ⟨by linarith [(hχb x).2], by linarith [(hχb x).1]⟩) hαβ hηc
    fun x hx hx' => by
      have : x < c' + R / 2 := by
        rcases hx' with h | h
        · have : x ≤ c' := by by_contra h'; exact h ⟨hx, lt_of_not_ge h'⟩
          linarith
        · linarith [h.2]
      filter_upwards [Iio_mem_nhds this] with y hy
      simp [hχ1 y hy.le]
  have hfg : f = g := by
    refine Subtype.ext (Lp.ext ?_)
    have h0 := (ae_restrict_iff' (hX.measurableSet.inter measurableSet_Iio)).mp hfd
    filter_upwards [hwF, hg, ae_restrict_of_ae h0, ae_restrict_mem hX.measurableSet]
      with x h2 h3 h4 hx
    rw [h3]
    by_cases hxd : x < d
    · have := h4 ⟨hx, hxd⟩
      rw [← h2, this]; simp
    · rw [← h2, show χ x = 0 from hχ0 x (by linarith)]; simp
  rw [hfg, hBg]

/-- If `a` is limit point, every boundary value vanishes on functions vanishing near `b`. -/
theorem boundaryValue_eq_zero_of_vanishesNear_right (hX : IsOpen X) (hXc : X.OrdConnected)
    (hq : ContinuousOn q X) {c : ℝ} (hc : c ∈ X) {z : ℂ} (hz : z.im ≠ 0)
    (h1 : Module.finrank ℂ (deficiencySpace (minOp (X ∩ Iio c) q) z) = 1)
    {B : (minOp X q)†.domain →ₗ[ℂ] ℂ} (hB : IsBoundaryValue X q B) (f : (minOp X q)†.domain)
    (hf : VanishesNear X q (fun d => X ∩ Ioi d) f) : B f = 0 := by
  obtain ⟨d, hd, hfd⟩ := hf
  obtain ⟨r, hr, hIr⟩ := exists_Icc_ball hX hd
  have hc' : d + r ∈ X := hIr ⟨by linarith, le_rfl⟩
  have h1' : Module.finrank ℂ (deficiencySpace (minOp (X ∩ Iio (d + r)) q) z) = 1 := by
    rw [← (dlmf_1_18_ix_index_indep hX hXc hq hc hc' hz).1, h1]
  obtain ⟨R', hR', hIR'⟩ := exists_Icc_ball hX hc'
  set R := min R' r
  have hR : 0 < R := lt_min hR' hr
  have hRr : R ≤ r := min_le_right _ _
  have hIccR : Icc (d + r - R) (d + r + R) ⊆ X := fun x hx =>
    hIR' ⟨by linarith [hx.1, min_le_left R' r], by linarith [hx.2, min_le_left R' r]⟩
  set c' := d + r
  obtain ⟨χ, hχ, hχb, hχ1, hχ0, hχc⟩ :=
    exists_cutoff (show c' - 3 * R / 4 < c' - R / 2 by linarith)
  have hIcc : Icc (c' - R / 4) (c' + R / 4) ⊆ X := fun x hx =>
    hIccR ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hαβ : Icc (c' - R) (c' - R / 4) ⊆ X := fun x hx => hIccR ⟨hx.1, by linarith [hx.2]⟩
  obtain ⟨hwF, -, -⟩ := maxRep_spec hX hXc ⟨c, hc⟩ hq f
  obtain ⟨g, hg, hBg⟩ := hB.exists_cutoff_eq_zero hX hXc hq hc' hz 1 (Or.inl ⟨rfl, rfl⟩) h1'
    (by positivity : (0 : ℝ) < R / 4) hIcc f hχ
    (fun x => abs_le.mpr ⟨by linarith [(hχb x).1], (hχb x).2⟩) hαβ
    (hχc _ _ (by linarith) (by linarith)) fun x hx hx' => by
      have : c' - R / 2 < x := by
        rcases hx' with h | h
        · have : c' ≤ x := by by_contra h'; exact h ⟨hx, lt_of_not_ge h'⟩
          linarith
        · linarith [h.1]
      filter_upwards [Ioi_mem_nhds this] with y hy using hχ0 y hy.le
  have hfg : f = g := by
    refine Subtype.ext (Lp.ext ?_)
    have h0 := (ae_restrict_iff' (hX.measurableSet.inter measurableSet_Ioi)).mp hfd
    filter_upwards [hwF, hg, ae_restrict_of_ae h0, ae_restrict_mem hX.measurableSet]
      with x h2 h3 h4 hx
    rw [h3]
    by_cases hxd : d < x
    · have := h4 ⟨hx, hxd⟩
      rw [← h2, this]; simp
    · rw [← h2, show χ x = 1 from hχ1 x (by linarith)]; simp
  rw [hfg, hBg]

/-! ### Self-adjoint extensions by boundary conditions -/

/-- **DLMF §1.18(ix)**: if `n₁ = n₂ = 1` (limit point at both ends), `ℒ*` is self-adjoint and is
the only self-adjoint extension of `ℒ`; no boundary conditions are imposed. -/
theorem dlmf_1_18_ix_ext_LP_LP (hX : IsOpen X) (hXc : X.OrdConnected) (hq : ContinuousOn q X)
    {c : ℝ} (hc : c ∈ X) {z : ℂ} (hz : z.im ≠ 0)
    (h1 : Module.finrank ℂ (deficiencySpace (minOp (X ∩ Iio c) q) z) = 1)
    (h2 : Module.finrank ℂ (deficiencySpace (minOp (X ∩ Ioi c) q) z) = 1) :
    IsSelfAdjoint (minOp X q)† ∧
      ∀ A : L2X X →ₗ.[ℂ] L2X X, IsSelfAdjoint A → minOp X q ≤ A → A = (minOp X q)† := by
  have hne : X.Nonempty := ⟨c, hc⟩
  have hT := isSymmetricDLMF_minOp hX hq
  have : ∀ w : ℂ, FiniteDimensional ℂ (deficiencySpace (minOp X q) w) := fun w =>
    (dlmf_1_18_ix_finrank_le hX hXc hne hq w).1
  have h0 := deficiency_eq_bot_of_LP_LP hX hXc hq hc hz h1 h2
  obtain ⟨hI, hmI⟩ := deficiency_bot_of_finrank_zero hT
    (dlmf_1_18_ix_deficiency_eq hX hXc hne hq) hz (by rw [h0, finrank_bot])
  exact hT.unique_selfAdjoint_of_bot hI hmI

/-- Deficiency indices `(1, 1)` from one limit-circle and one limit-point end. -/
theorem finrank_I_eq_one_of_LC_LP (hX : IsOpen X) (hXc : X.OrdConnected)
    (hq : ContinuousOn q X) {c : ℝ} (hc : c ∈ X) {z : ℂ} (hz : z.im ≠ 0) {Ya Yb : Set ℝ}
    (hab : (Ya = X ∩ Iio c ∧ Yb = X ∩ Ioi c) ∨ (Ya = X ∩ Ioi c ∧ Yb = X ∩ Iio c))
    (h2 : Module.finrank ℂ (deficiencySpace (minOp Ya q) z) = 2)
    (h1 : Module.finrank ℂ (deficiencySpace (minOp Yb q) z) = 1) :
    Module.finrank ℂ (deficiencySpace (minOp X q) I) = 1 := by
  have hsa : Ya = X ∩ Iio c ∨ Ya = X ∩ Ioi c := by
    rcases hab with h | h
    · exact Or.inl h.1
    · exact Or.inr h.1
  obtain ⟨hYa, hYac, hYane, hYaX⟩ := halfInterval_props hX hXc hc hsa
  have hall := (finrank_eq_two_iff hYa hYac hYane (hq.mono hYaX) z).mp h2
  rw [← finrank_deficiency_eq_I hX hXc ⟨c, hc⟩ hq hz]
  exact finrank_eq_one_of_LC_LP hX hXc hq hc hab hall h1

/-- **DLMF §1.18(ix)**: if `n₁ = 2` and `n₂ = 1`, every self-adjoint extension of `ℒ` is obtained
by restricting `ℒ*` to `B₁(f) = 0` for a nonzero boundary value `B₁` at `a`. -/
theorem dlmf_1_18_ix_ext_LC_LP (hX : IsOpen X) (hXc : X.OrdConnected) (hq : ContinuousOn q X)
    {c : ℝ} (hc : c ∈ X) {z : ℂ} (hz : z.im ≠ 0)
    (h2 : Module.finrank ℂ (deficiencySpace (minOp (X ∩ Iio c) q) z) = 2)
    (h1 : Module.finrank ℂ (deficiencySpace (minOp (X ∩ Ioi c) q) z) = 1)
    {A : L2X X →ₗ.[ℂ] L2X X} (hA : IsSelfAdjoint A) (hTA : minOp X q ≤ A) :
    A ≤ (minOp X q)† ∧ ∃ B ∈ boundaryValuesLeft X q, B ≠ 0 ∧
      ∀ f : (minOp X q)†.domain, (f : L2X X) ∈ A.domain ↔ B f = 0 := by
  have hT := isSymmetricDLMF_minOp hX hq
  obtain ⟨w, hw, f₀, hf₀⟩ := hT.exists_form_of_finrank_one
    (finrank_I_eq_one_of_LC_LP hX hXc hq hc hz (Or.inl ⟨rfl, rfl⟩) h2 h1) hA hTA
  have hB := formBV_isBoundaryValue hX hq w
  refine ⟨le_adjoint_of_selfAdjoint_ext hT hA hTA, formBV w,
    ⟨hB, fun f hf => boundaryValue_eq_zero_of_vanishesNear_left hX hXc hq hc hz h1 hB f hf⟩,
    fun h => hf₀ (by rw [← formBV_apply, h, LinearMap.zero_apply]), fun f => ?_⟩
  rw [formBV_apply]; exact hw f

/-- **DLMF §1.18(ix)**: if `n₁ = 1` and `n₂ = 2`, every self-adjoint extension of `ℒ` is obtained
by restricting `ℒ*` to `B₂(f) = 0` for a nonzero boundary value `B₂` at `b`. -/
theorem dlmf_1_18_ix_ext_LP_LC (hX : IsOpen X) (hXc : X.OrdConnected) (hq : ContinuousOn q X)
    {c : ℝ} (hc : c ∈ X) {z : ℂ} (hz : z.im ≠ 0)
    (h1 : Module.finrank ℂ (deficiencySpace (minOp (X ∩ Iio c) q) z) = 1)
    (h2 : Module.finrank ℂ (deficiencySpace (minOp (X ∩ Ioi c) q) z) = 2)
    {A : L2X X →ₗ.[ℂ] L2X X} (hA : IsSelfAdjoint A) (hTA : minOp X q ≤ A) :
    A ≤ (minOp X q)† ∧ ∃ B ∈ boundaryValuesRight X q, B ≠ 0 ∧
      ∀ f : (minOp X q)†.domain, (f : L2X X) ∈ A.domain ↔ B f = 0 := by
  have hT := isSymmetricDLMF_minOp hX hq
  obtain ⟨w, hw, f₀, hf₀⟩ := hT.exists_form_of_finrank_one
    (finrank_I_eq_one_of_LC_LP hX hXc hq hc hz (Or.inr ⟨rfl, rfl⟩) h2 h1) hA hTA
  have hB := formBV_isBoundaryValue hX hq w
  refine ⟨le_adjoint_of_selfAdjoint_ext hT hA hTA, formBV w,
    ⟨hB, fun f hf => boundaryValue_eq_zero_of_vanishesNear_right hX hXc hq hc hz h1 hB f hf⟩,
    fun h => hf₀ (by rw [← formBV_apply, h, LinearMap.zero_apply]), fun f => ?_⟩
  rw [formBV_apply]; exact hw f

end Azurite.DLMF
