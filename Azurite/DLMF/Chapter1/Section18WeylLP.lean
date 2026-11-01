/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter1.Section18WeylEnd

/-!
# DLMF §1.18(ix): limit point, limit circle, and `n = n₁ + n₂ − 2`

* `finrank_eq_two_iff`: limit circle (`n₁ = 2`) iff every solution is `L²` near the endpoint.
* `dlmf_1_18_ix_index_indep`: `n₁, n₂` are independent of the cut point `c`. They are also
  independent of the non-real `z` (`finrank_deficiency_eq_I`).
* `exists_decomp_of_finrank_one`: if `n₊ = n₋ = 1`, then `D(T*) = D(T**) ⊕ span(E₁, E₂)` for
  test functions independent modulo `D(T**)`.
* `side_identity`: on a limit-point side, an `L²` solution satisfies
  `(z̄ − z)‖u‖² = ±conj W(u, u)(c)`.
* `dlmf_1_18_ix_index_formula`: the (equal) deficiency indices of `ℒ` are `n₁ + n₂ − 2`. The
  limit-circle cases use extension of solutions; the limit-point/limit-point case uses
  `side_identity` on both sides.
-/

open Set Filter Topology MeasureTheory LinearPMap
open scoped InnerProductSpace ComplexConjugate ContDiff

namespace Azurite.DLMF

variable {X : Set ℝ} {q : ℝ → ℝ}

/-! ### Independence of `z` -/

/-- For non-real `z`, `dim N_z = dim N_i` (constancy in each half-plane and `f ↦ f̄`). -/
theorem finrank_deficiency_eq_I (hX : IsOpen X) (hXc : X.OrdConnected) (hne : X.Nonempty)
    (hq : ContinuousOn q X) {z : ℂ} (hz : z.im ≠ 0) :
    Module.finrank ℂ (deficiencySpace (minOp X q) z) =
      Module.finrank ℂ (deficiencySpace (minOp X q) Complex.I) := by
  have hT := isSymmetricDLMF_minOp hX hq
  have hfr : ∀ w w' : ℂ, Module.rank ℂ (deficiencySpace (minOp X q) w) =
      Module.rank ℂ (deficiencySpace (minOp X q) w') →
      Module.finrank ℂ (deficiencySpace (minOp X q) w) =
        Module.finrank ℂ (deficiencySpace (minOp X q) w') :=
    fun w w' h => by unfold Module.finrank; rw [h]
  rcases lt_or_gt_of_ne hz with hlt | hgt
  · rw [hfr _ _ (dlmf_1_18_ix_deficiency_const hT (z := z) (w := -Complex.I)
      (Or.inr ⟨hlt, by simp⟩)), dlmf_1_18_ix_deficiency_eq hX hXc hne hq (-Complex.I),
      _root_.map_neg, Complex.conj_I, neg_neg]
  · exact hfr _ _ (dlmf_1_18_ix_deficiency_const hT (Or.inl ⟨hgt, by simp⟩))

/-! ### Solutions on subintervals -/

theorem IsSolution.mono {Y : Set ℝ} {z : ℂ} {u : ℝ → ℂ} (hu : IsSolution X q z u) (hYX : Y ⊆ X) :
    IsSolution Y q z u := by
  obtain ⟨u', hu'⟩ := hu; exact ⟨u', fun x hx => hu' x (hYX hx)⟩

/-- A solution on an open subinterval `Y ⊆ X` extends to a solution on `X`. -/
theorem IsSolution.extend (hX : IsOpen X) (hXc : X.OrdConnected) (hq : ContinuousOn q X)
    {Y : Set ℝ} (hYc : Y.OrdConnected) (hYne : Y.Nonempty) (hYX : Y ⊆ X) {z : ℂ}
    {u : ℝ → ℂ} (hu : IsSolution Y q z u) :
    ∃ v, IsSolution X q z v ∧ EqOn v u Y := by
  obtain ⟨y0, hy0⟩ := hYne
  obtain ⟨u', hu'⟩ := hu
  have hW : ContinuousOn (fun x => (q x : ℂ) - z) X :=
    (Complex.continuous_ofReal.comp_continuousOn hq).sub continuousOn_const
  obtain ⟨v, v', hv, h0, h1⟩ := exists_solution_on hX hXc hW (hYX hy0) (u y0) (u' y0)
  refine ⟨v, ⟨v', hv⟩, fun x hx => ?_⟩
  have hz := ode2c_eq_zero_on hYc (hW.mono hYX) (w := fun x => v x - u x)
    (w' := fun x => v' x - u' x) (fun x hx => (hv x (hYX hx)).1.sub (hu' x hx).1)
    (fun x hx => ((hv x (hYX hx)).2.sub (hu' x hx).2).congr_deriv (by ring)) hy0
    (by simp [h0]) (by simp [h1]) x hx
  exact sub_eq_zero.mp hz

/-- A continuous function on an open interval `X` is square integrable on any compact
interval inside `X`. -/
theorem memLp_Icc_of_continuousOn {u : ℝ → ℂ} (hu : ContinuousOn u X) {α β : ℝ}
    (hIcc : Icc α β ⊆ X) : MemLp u 2 (volume.restrict (Icc α β)) := by
  have : IsFiniteMeasure (volume.restrict (Icc α β)) := ⟨by simp⟩
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn (hu.mono hIcc)
  refine MemLp.of_bound ((hu.mono hIcc).aestronglyMeasurable measurableSet_Icc) C ?_
  exact (ae_restrict_iff' measurableSet_Icc).mpr (ae_of_all _ hC)

theorem memLp_union {u : ℝ → ℂ} {A B : Set ℝ} (hA : MemLp u 2 (volume.restrict A))
    (hB : MemLp u 2 (volume.restrict B)) : MemLp u 2 (volume.restrict (A ∪ B)) := by
  have hm := aestronglyMeasurable_union_iff.mpr ⟨hA.aestronglyMeasurable, hB.aestronglyMeasurable⟩
  rw [memLp_two_iff_integrable_sq_norm hm]
  exact IntegrableOn.union ((memLp_two_iff_integrable_sq_norm hA.aestronglyMeasurable).mp hA)
    ((memLp_two_iff_integrable_sq_norm hB.aestronglyMeasurable).mp hB)

/-! ### Limit circle: all solutions are square integrable -/

section LC

variable {Y : Set ℝ} (hY : IsOpen Y) (hYc : Y.OrdConnected) (hYne : Y.Nonempty)
  (hqY : ContinuousOn q Y) (z : ℂ)

include hY hYc hYne hqY in
/-- The class of a square-integrable classical solution lies in `N_z`, with representative
equal to the solution on `Y`. -/
theorem solData_toLp {u : ℝ → ℂ} (hu : IsSolution Y q z u) (hu2 : MemLp u 2 (volume.restrict Y))
    {y0 : ℝ} (hy0 : y0 ∈ Y) :
    ∃ h : hu2.toLp ∈ deficiencySpace (minOp Y q) z,
      solData hY hYc hYne hqY z hy0 ⟨_, h⟩ = (u y0, deriv u y0) := by
  have hmem : hu2.toLp ∈ deficiencySpace (minOp Y q) z :=
    (dlmf_1_18_ix_deficiency_iff hY hYc hYne hqY z _).mpr ⟨u, hu, hu2.coeFn_toLp⟩
  refine ⟨hmem, ?_⟩
  obtain ⟨hr, hra⟩ := solRep_spec hY hYc hYne hqY z ⟨_, hmem⟩
  have heq : EqOn (solRep hY hYc hYne hqY z ⟨_, hmem⟩) u Y :=
    eqOn_of_ae_eq_of_continuousOn hY hr.continuousOn hu.continuousOn
      (hra.symm.trans hu2.coeFn_toLp)
  have hev := Filter.eventuallyEq_of_mem (hY.mem_nhds hy0) heq
  simp only [solData, LinearMap.coe_mk, AddHom.coe_mk, Prod.mk.injEq]
  exact ⟨heq hy0, hev.deriv_eq⟩

include hY hYc hYne hqY in
/-- **Limit circle**: `dim N_z = 2` iff every solution of `ℒu = zu` on `Y` is in `L²(Y)`. -/
theorem finrank_eq_two_iff :
    Module.finrank ℂ (deficiencySpace (minOp Y q) z) = 2 ↔
      ∀ u, IsSolution Y q z u → MemLp u 2 (volume.restrict Y) := by
  obtain ⟨y0, hy0⟩ := hYne
  set Λ := solData hY hYc ⟨y0, hy0⟩ hqY z hy0
  have hinj := solData_injective hY hYc ⟨y0, hy0⟩ hqY z hy0
  have hfd : FiniteDimensional ℂ (deficiencySpace (minOp Y q) z) :=
    (dlmf_1_18_ix_finrank_le hY hYc ⟨y0, hy0⟩ hqY z).1
  have hW : ContinuousOn (fun x => (q x : ℂ) - z) Y :=
    (Complex.continuous_ofReal.comp_continuousOn hqY).sub continuousOn_const
  constructor
  · intro h2 u hu
    have hsurj : Function.Surjective Λ :=
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by simp [h2])).mp hinj
    obtain ⟨v, hv⟩ := hsurj (u y0, deriv u y0)
    obtain ⟨hr, hra⟩ := solRep_spec hY hYc ⟨y0, hy0⟩ hqY z v
    obtain ⟨r', hr'⟩ := hr
    obtain ⟨u', hu'⟩ := hu
    simp only [Λ, solData, LinearMap.coe_mk, AddHom.coe_mk, Prod.mk.injEq] at hv
    have hd1 : r' y0 = deriv (solRep hY hYc ⟨y0, hy0⟩ hqY z v) y0 := ((hr' y0 hy0).1.deriv).symm
    have hd2 : u' y0 = deriv u y0 := ((hu' y0 hy0).1.deriv).symm
    have hz := ode2c_eq_zero_on hYc hW (w := fun x => solRep hY hYc ⟨y0, hy0⟩ hqY z v x - u x)
      (w' := fun x => r' x - u' x) (fun x hx => (hr' x hx).1.sub (hu' x hx).1)
      (fun x hx => ((hr' x hx).2.sub (hu' x hx).2).congr_deriv (by ring)) hy0
      (by simp [hv.1]) (by simp [hd1, hd2, hv.2])
    refine (Lp.memLp (v : L2X Y)).ae_eq (hra.trans ?_)
    exact (ae_restrict_iff' hY.measurableSet).mpr (ae_of_all _ fun x hx => sub_eq_zero.mp (hz x hx))
  · intro hall
    obtain ⟨u₁, u₁', hu₁, h10, h11⟩ := exists_solution_on hY hYc hW hy0 1 0
    obtain ⟨u₂, u₂', hu₂, h20, h21⟩ := exists_solution_on hY hYc hW hy0 0 1
    have hs₁ : IsSolution Y q z u₁ := ⟨u₁', hu₁⟩
    have hs₂ : IsSolution Y q z u₂ := ⟨u₂', hu₂⟩
    obtain ⟨hm₁, hΛ₁⟩ := solData_toLp hY hYc ⟨y0, hy0⟩ hqY z hs₁ (hall u₁ hs₁) hy0
    obtain ⟨hm₂, hΛ₂⟩ := solData_toLp hY hYc ⟨y0, hy0⟩ hqY z hs₂ (hall u₂ hs₂) hy0
    rw [(hu₁ y0 hy0).1.deriv, h10, h11] at hΛ₁
    rw [(hu₂ y0 hy0).1.deriv, h20, h21] at hΛ₂
    have hsurj : Function.Surjective Λ := fun p => by
      refine ⟨p.1 • ⟨_, hm₁⟩ + p.2 • ⟨_, hm₂⟩, ?_⟩
      rw [_root_.map_add, _root_.map_smul, _root_.map_smul]
      rw [hΛ₁, hΛ₂]
      ext <;> simp
    have := (LinearEquiv.ofBijective Λ ⟨hinj, hsurj⟩).finrank_eq
    simpa using this

end LC

/-! ### Independence of the cut point `c` -/

theorem allL2_mono_left (hX : IsOpen X) (hXc : X.OrdConnected) (hq : ContinuousOn q X)
    {c c' : ℝ} (hcc : c ≤ c') {z : ℂ}
    (h : ∀ u, IsSolution (X ∩ Iio c') q z u → MemLp u 2 (volume.restrict (X ∩ Iio c')))
    (hne : (X ∩ Iio c).Nonempty) :
    ∀ u, IsSolution (X ∩ Iio c) q z u → MemLp u 2 (volume.restrict (X ∩ Iio c)) := by
  intro u hu
  obtain ⟨v, hv, hvu⟩ := hu.extend hX hXc hq (hXc.inter ordConnected_Iio) hne inter_subset_left
  have hsub : X ∩ Iio c ⊆ X ∩ Iio c' := fun x hx => ⟨hx.1, lt_of_lt_of_le hx.2 hcc⟩
  have := (h v (hv.mono inter_subset_left)).mono_measure (Measure.restrict_mono hsub le_rfl)
  exact this.ae_eq ((ae_restrict_iff' ((hX.inter isOpen_Iio).measurableSet)).mpr
    (ae_of_all _ fun x hx => hvu hx))

theorem allL2_anti_left (hX : IsOpen X) (hXc : X.OrdConnected) (hq : ContinuousOn q X)
    {c c' : ℝ} (hc : c ∈ X) (hc' : c' ∈ X) {z : ℂ}
    (h : ∀ u, IsSolution (X ∩ Iio c) q z u → MemLp u 2 (volume.restrict (X ∩ Iio c)))
    (hne : (X ∩ Iio c').Nonempty) :
    ∀ u, IsSolution (X ∩ Iio c') q z u → MemLp u 2 (volume.restrict (X ∩ Iio c')) := by
  intro u hu
  obtain ⟨v, hv, hvu⟩ := hu.extend hX hXc hq (hXc.inter ordConnected_Iio) hne inter_subset_left
  have h1 := h v (hv.mono inter_subset_left)
  have h2 := memLp_Icc_of_continuousOn hv.continuousOn (hXc.out hc hc')
  have h3 := (memLp_union h1 h2).mono_measure (Measure.restrict_mono (fun x hx => by
    rcases lt_or_ge x c with hxc | hxc
    · exact Or.inl ⟨hx.1, hxc⟩
    · exact Or.inr ⟨hxc, hx.2.le⟩) le_rfl : volume.restrict (X ∩ Iio c') ≤ _)
  exact h3.ae_eq ((ae_restrict_iff' ((hX.inter isOpen_Iio).measurableSet)).mpr
    (ae_of_all _ fun x hx => hvu hx))

theorem allL2_mono_right (hX : IsOpen X) (hXc : X.OrdConnected) (hq : ContinuousOn q X)
    {c c' : ℝ} (hcc : c ≤ c') {z : ℂ}
    (h : ∀ u, IsSolution (X ∩ Ioi c) q z u → MemLp u 2 (volume.restrict (X ∩ Ioi c)))
    (hne : (X ∩ Ioi c').Nonempty) :
    ∀ u, IsSolution (X ∩ Ioi c') q z u → MemLp u 2 (volume.restrict (X ∩ Ioi c')) := by
  intro u hu
  obtain ⟨v, hv, hvu⟩ := hu.extend hX hXc hq (hXc.inter ordConnected_Ioi) hne inter_subset_left
  have hsub : X ∩ Ioi c' ⊆ X ∩ Ioi c := fun x hx => ⟨hx.1, lt_of_le_of_lt hcc hx.2⟩
  have := (h v (hv.mono inter_subset_left)).mono_measure (Measure.restrict_mono hsub le_rfl)
  exact this.ae_eq ((ae_restrict_iff' ((hX.inter isOpen_Ioi).measurableSet)).mpr
    (ae_of_all _ fun x hx => hvu hx))

theorem allL2_anti_right (hX : IsOpen X) (hXc : X.OrdConnected) (hq : ContinuousOn q X)
    {c c' : ℝ} (hc : c ∈ X) (hc' : c' ∈ X) {z : ℂ}
    (h : ∀ u, IsSolution (X ∩ Ioi c') q z u → MemLp u 2 (volume.restrict (X ∩ Ioi c')))
    (hne : (X ∩ Ioi c).Nonempty) :
    ∀ u, IsSolution (X ∩ Ioi c) q z u → MemLp u 2 (volume.restrict (X ∩ Ioi c)) := by
  intro u hu
  obtain ⟨v, hv, hvu⟩ := hu.extend hX hXc hq (hXc.inter ordConnected_Ioi) hne inter_subset_left
  have h1 := h v (hv.mono inter_subset_left)
  have h2 := memLp_Icc_of_continuousOn hv.continuousOn (hXc.out hc hc')
  have h3 := (memLp_union h1 h2).mono_measure (Measure.restrict_mono (fun x hx => by
    rcases lt_or_ge c' x with hxc | hxc
    · exact Or.inl ⟨hx.1, hxc⟩
    · exact Or.inr ⟨hx.2.le, hxc⟩) le_rfl : volume.restrict (X ∩ Ioi c) ≤ _)
  exact h3.ae_eq ((ae_restrict_iff' ((hX.inter isOpen_Ioi).measurableSet)).mpr
    (ae_of_all _ fun x hx => hvu hx))

/-- **DLMF §1.18(ix)**: the endpoint deficiency indices `n₁`, `n₂` do not depend on the cut point
`c ∈ X` (nor on the non-real `z`). -/
theorem dlmf_1_18_ix_index_indep (hX : IsOpen X) (hXc : X.OrdConnected) (hq : ContinuousOn q X)
    {c c' : ℝ} (hc : c ∈ X) (hc' : c' ∈ X) {z : ℂ} (hz : z.im ≠ 0) :
    Module.finrank ℂ (deficiencySpace (minOp (X ∩ Iio c) q) z) =
        Module.finrank ℂ (deficiencySpace (minOp (X ∩ Iio c') q) z) ∧
      Module.finrank ℂ (deficiencySpace (minOp (X ∩ Ioi c) q) z) =
        Module.finrank ℂ (deficiencySpace (minOp (X ∩ Ioi c') q) z) := by
  obtain ⟨hL, hLc, hLne, hLX⟩ := halfInterval_props hX hXc hc (Or.inl rfl)
  obtain ⟨hL', hLc', hLne', hLX'⟩ := halfInterval_props hX hXc hc' (Or.inl rfl)
  obtain ⟨hR, hRc, hRne, hRX⟩ := halfInterval_props hX hXc hc (Or.inr rfl)
  obtain ⟨hR', hRc', hRne', hRX'⟩ := halfInterval_props hX hXc hc' (Or.inr rfl)
  have wL := dlmf_1_18_ix_weyl_alternative hX hXc hq hc hz (Y := X ∩ Iio c) (Or.inl rfl)
  have wL' := dlmf_1_18_ix_weyl_alternative hX hXc hq hc' hz (Y := X ∩ Iio c') (Or.inl rfl)
  have wR := dlmf_1_18_ix_weyl_alternative hX hXc hq hc hz (Y := X ∩ Ioi c) (Or.inr rfl)
  have wR' := dlmf_1_18_ix_weyl_alternative hX hXc hq hc' hz (Y := X ∩ Ioi c') (Or.inr rfl)
  have eL := finrank_eq_two_iff hL hLc hLne (hq.mono hLX) z
  have eL' := finrank_eq_two_iff hL' hLc' hLne' (hq.mono hLX') z
  have eR := finrank_eq_two_iff hR hRc hRne (hq.mono hRX) z
  have eR' := finrank_eq_two_iff hR' hRc' hRne' (hq.mono hRX') z
  have key : ∀ {a b : ℕ}, 1 ≤ a → a ≤ 2 → 1 ≤ b → b ≤ 2 → (a = 2 ↔ b = 2) → a = b :=
    fun h1 h2 h3 h4 h5 => by omega
  rcases le_total c c' with hcc | hcc
  · refine ⟨key wL.1 wL.2 wL'.1 wL'.2 ?_, key wR.1 wR.2 wR'.1 wR'.2 ?_⟩
    · rw [eL, eL']
      exact ⟨fun h => allL2_anti_left hX hXc hq hc hc' h hLne',
        fun h => allL2_mono_left hX hXc hq hcc h hLne⟩
    · rw [eR, eR']
      exact ⟨fun h => allL2_mono_right hX hXc hq hcc h hRne',
        fun h => allL2_anti_right hX hXc hq hc hc' h hRne⟩
  · refine ⟨key wL.1 wL.2 wL'.1 wL'.2 ?_, key wR.1 wR.2 wR'.1 wR'.2 ?_⟩
    · rw [eL, eL']
      exact ⟨fun h => allL2_mono_left hX hXc hq hcc h hLne',
        fun h => allL2_anti_left hX hXc hq hc' hc h hLne⟩
    · rw [eR, eR']
      exact ⟨fun h => allL2_anti_right hX hXc hq hc' hc h hRne',
        fun h => allL2_mono_right hX hXc hq hcc h hRne⟩

/-! ### Deficiency indices `(1, 1)`: `D(T*) = D(T**) ⊕ span(E₁, E₂)` -/

section Quotient

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
  {T : V →ₗ.[ℂ] V}

/-- If `dim N_i = dim N_{−i} = 1` and `E₁, E₂ ∈ D(T*)` are independent modulo `D(T**)`, then
every `F ∈ D(T*)` is `F = h + αE₁ + βE₂` with `h ∈ D(T**)`. -/
theorem IsSymmetricDLMF.exists_decomp_of_finrank_one (hT : IsSymmetricDLMF T)
    [FiniteDimensional ℂ (deficiencySpace T Complex.I)]
    [FiniteDimensional ℂ (deficiencySpace T (-Complex.I))]
    (h1 : Module.finrank ℂ (deficiencySpace T Complex.I) = 1)
    (h2 : Module.finrank ℂ (deficiencySpace T (-Complex.I)) = 1) (E₁ E₂ : T†.domain)
    (hind : ∀ α β : ℂ, ((α • E₁ + β • E₂ : T†.domain) : V) ∈ T††.domain → α = 0 ∧ β = 0)
    (F : T†.domain) : ∃ α β : ℂ, ((F - α • E₁ - β • E₂ : T†.domain) : V) ∈ T††.domain := by
  set S : Submodule ℂ T†.domain := (T††.domain).comap T†.domain.subtype
  have hle := hT.le_adjoint_adjoint.2
  have hmemN : ∀ w : ℂ, ∀ a ∈ deficiencySpace T w, a ∈ T†.domain := fun w a ha =>
    (mem_eigenspaceDLMF.mp ha).1
  set Φ : (deficiencySpace T Complex.I × deficiencySpace T (-Complex.I)) →ₗ[ℂ]
      (T†.domain ⧸ S) :=
    S.mkQ ∘ₗ (LinearMap.codRestrict T†.domain
      ((deficiencySpace T Complex.I).subtype ∘ₗ LinearMap.fst _ _ _ +
        (deficiencySpace T (-Complex.I)).subtype ∘ₗ LinearMap.snd _ _ _)
      fun p => by simpa using add_mem (hmemN _ _ p.1.2) (hmemN _ _ p.2.2))
  have hΦinj : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro p hp
    simp only [Φ, LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero,
      S, Submodule.mem_comap, Submodule.subtype_apply, LinearMap.codRestrict_apply,
      LinearMap.add_apply, LinearMap.fst_apply, LinearMap.snd_apply] at hp
    have hu := hT.vonNeumann_unique ⟨_, neg_mem hp⟩ p.1.2 p.2.2 (by simp)
    exact Prod.ext (Subtype.ext hu.2.1) (Subtype.ext hu.2.2)
  have hΦsurj : Function.Surjective Φ := by
    intro Q
    obtain ⟨F, rfl⟩ := Submodule.mkQ_surjective S Q
    obtain ⟨g, a, ha, b, hb, hF⟩ := hT.vonNeumann_decomp F
    refine ⟨(⟨a, ha⟩, ⟨b, hb⟩), ?_⟩
    simp only [Φ, LinearMap.comp_apply, Submodule.mkQ_apply]
    rw [Submodule.Quotient.eq]
    simp only [S, Submodule.mem_comap, Submodule.subtype_apply, Submodule.coe_sub,
      LinearMap.codRestrict_apply, LinearMap.add_apply, LinearMap.coe_comp, Function.comp_apply,
      LinearMap.fst_apply, LinearMap.snd_apply, Submodule.subtype_apply]
    rw [show (a + b - (F : V)) = -(g : V) by rw [hF]; abel]
    exact neg_mem g.2
  set eΦ := LinearEquiv.ofBijective Φ ⟨hΦinj, hΦsurj⟩
  have : FiniteDimensional ℂ (T†.domain ⧸ S) := eΦ.finiteDimensional
  have hQ : Module.finrank ℂ (T†.domain ⧸ S) = 2 := by
    rw [← eΦ.finrank_eq, Module.finrank_prod, h1, h2]
  set Ψ : (ℂ × ℂ) →ₗ[ℂ] (T†.domain ⧸ S) :=
    S.mkQ ∘ₗ (LinearMap.fst ℂ ℂ ℂ).smulRight E₁ + S.mkQ ∘ₗ (LinearMap.snd ℂ ℂ ℂ).smulRight E₂
  have hΨinj : Function.Injective Ψ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro p hp
    simp only [Ψ, LinearMap.add_apply, LinearMap.comp_apply, Submodule.mkQ_apply,
      LinearMap.smulRight_apply, LinearMap.fst_apply, LinearMap.snd_apply,
      ← Submodule.Quotient.mk_add, Submodule.Quotient.mk_eq_zero, S, Submodule.mem_comap,
      Submodule.subtype_apply] at hp
    obtain ⟨h1', h2'⟩ := hind p.1 p.2 hp
    exact Prod.ext h1' h2'
  have hΨsurj : Function.Surjective Ψ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by simp [hQ])).mp hΨinj
  obtain ⟨⟨α, β⟩, hαβ⟩ := hΨsurj (S.mkQ F)
  refine ⟨α, β, ?_⟩
  simp only [Ψ, LinearMap.add_apply, LinearMap.comp_apply, Submodule.mkQ_apply,
    LinearMap.smulRight_apply, LinearMap.fst_apply, LinearMap.snd_apply,
    ← Submodule.Quotient.mk_add, Submodule.Quotient.eq] at hαβ
  have := neg_mem hαβ
  simp only [S, Submodule.mem_comap, Submodule.subtype_apply] at this ⊢
  convert this using 1
  simp only [Submodule.coe_sub, Submodule.coe_add, Submodule.coe_smul, neg_sub]
  abel

end Quotient

/-! ### Green's formula for a solution against a test function -/

/-- `∫_{X∩(−∞,c)} (conj(zu) e − conj(u) ℒe) = conj W(u, e)(c)` and `−conj W(u, e)(c)` on
`X ∩ (c, ∞)`, for a solution `u` on `X` and `e ∈ C²_c` supported near `c`. -/
theorem integral_solution_test (hX : IsOpen X) (hq : ContinuousOn q X) {z : ℂ} {u u' : ℝ → ℂ}
    (hu : ∀ x ∈ X, HasDerivAt u (u' x) x ∧ HasDerivAt u' (((q x : ℂ) - z) * u x) x)
    {c r : ℝ} (hr : 0 < r) (hIcc : Icc (c - r) (c + r) ⊆ X) {e : ℝ → ℂ} (he : IsC2c X e)
    (hes : tsupport e ⊆ Ioo (c - r) (c + r)) {Y : Set ℝ} (hY : IsOpen Y) (s : ℂ)
    (hside : (Y = X ∩ Iio c ∧ s = 1) ∨ (Y = X ∩ Ioi c ∧ s = -1)) :
    ∫ x in Y, (conj (z * u x) * e x - conj (u x) * schrodingerOp q e x) =
      s * conj (wronskianConj u e c) := by
  have hcX : c ∈ X := hIcc ⟨by linarith, by linarith⟩
  have hLe := continuous_schrodingerOp hX hq he
  have hed := fun x => (hasDerivAt_deriv_of_contDiff_two he.1 x).1
  have hedd := fun x => (hasDerivAt_deriv_of_contDiff_two he.1 x).2
  have hzero : ∀ x ∉ Ioo (c - r) (c + r), e x = 0 ∧ deriv e x = 0 ∧
      schrodingerOp q e x = 0 := fun x hx => by
    have hex : e =ᶠ[𝓝 x] 0 := (notMem_tsupport_iff_eventuallyEq).mp fun h => hx (hes h)
    refine ⟨hex.eq_of_nhds, by rw [hex.deriv_eq]; simp, ?_⟩
    by_contra h; exact hx (hes (support_schrodingerOp_subset q e h))
  set H : ℝ → ℂ := fun x => conj (z * u x) * e x - conj (u x) * schrodingerOp q e x
  have hHz : ∀ x ∉ Ioo (c - r) (c + r), H x = 0 := fun x hx => by
    simp [H, (hzero x hx).1, (hzero x hx).2.2]
  -- Green on `[α, β] ⊆ X`
  set W : ℝ → ℂ := fun x => u x * conj (deriv e x) - u' x * conj (e x)
  have hW : ∀ x ∈ X, HasDerivAt W (conj (H x)) x := fun x hx => by
    have h := ((hu x hx).1.mul (hedd x).star).sub ((hu x hx).2.mul (hed x).star)
    refine h.congr_deriv ?_
    simp only [H, schrodingerOp, Complex.star_def, _root_.map_sub, map_mul, _root_.map_add,
      _root_.map_neg, Complex.conj_conj, Complex.conj_ofReal]
    ring
  have hHcX : ContinuousOn H X := by
    have hcu : ContinuousOn u X := fun x hx => (hu x hx).1.continuousAt.continuousWithinAt
    exact ((Complex.continuous_conj.comp_continuousOn (continuousOn_const.mul hcu)).mul
      he.1.continuous.continuousOn).sub
      ((Complex.continuous_conj.comp_continuousOn hcu).mul hLe.continuousOn)
  have hgreen : ∀ α β, Icc α β ⊆ X → α ≤ β → ∫ x in α..β, H x = conj (W β) - conj (W α) :=
    fun α β hab hle => by
      have := intervalIntegral.integral_eq_sub_of_hasDerivAt (f := W) (f' := fun x => conj (H x))
        (fun x hx => hW x (hab (by rwa [uIcc_of_le hle] at hx)))
        ((Complex.continuous_conj.comp_continuousOn (hHcX.mono hab)).intervalIntegrable_of_Icc hle)
      have e1 : ∫ x in α..β, H x = conj (∫ x in α..β, conj (H x)) := by
        rw [intervalIntegral.integral_of_le hle, intervalIntegral.integral_of_le hle, integral_conj,
          Complex.conj_conj]
      rw [e1, this, _root_.map_sub]
  have hWc : W c = wronskianConj u e c := by
    simp [W, wronskianConj, (hu c hcX).1.deriv]
  have hWl : W (c - r) = 0 := by
    have h := hzero (c - r) fun h => lt_irrefl _ h.1
    simp [W, h.1, h.2.1]
  have hWu : W (c + r) = 0 := by
    have h := hzero (c + r) fun h => lt_irrefl _ h.2
    simp [W, h.1, h.2.1]
  rcases hside with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · have hsub : Ioo (c - r) c ⊆ X ∩ Iio c := fun x hx =>
      ⟨hIcc ⟨hx.1.le, by linarith [hx.2]⟩, hx.2⟩
    rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hY.measurableSet hsub
      fun x hx => hHz x fun h => hx.2 ⟨h.1, hx.1.2⟩, ← integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le (by linarith),
      hgreen _ _ (fun x hx => hIcc ⟨hx.1, by linarith [hx.2]⟩) (by linarith), hWc, hWl]
    simp
  · have hsub : Ioo c (c + r) ⊆ X ∩ Ioi c := fun x hx =>
      ⟨hIcc ⟨by linarith [hx.1], hx.2.le⟩, hx.1⟩
    rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hY.measurableSet hsub
      fun x hx => hHz x fun h => hx.2 ⟨hx.1.2, h.2⟩, ← integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le (by linarith),
      hgreen _ _ (fun x hx => hIcc ⟨by linarith [hx.1], hx.2⟩) (by linarith), hWc, hWu]
    simp

/-! ### The case `n₁ = n₂ = 1` -/

set_option maxHeartbeats 400000 in
/-- On a limit-point side `Y` (`dim N_z(Y) = 1`), a square-integrable solution satisfies
`(z̄ − z)‖u‖²_Y = s · conj W(u, u)(c)`. -/
theorem side_identity (hX : IsOpen X) (hXc : X.OrdConnected) (hq : ContinuousOn q X) {c : ℝ}
    (hc : c ∈ X) {z : ℂ} (hz : z.im ≠ 0) {Y : Set ℝ} (s : ℂ)
    (hside : (Y = X ∩ Iio c ∧ s = 1) ∨ (Y = X ∩ Ioi c ∧ s = -1))
    (h1 : Module.finrank ℂ (deficiencySpace (minOp Y q) z) = 1) {u u' : ℝ → ℂ}
    (hu : ∀ x ∈ X, HasDerivAt u (u' x) x ∧ HasDerivAt u' (((q x : ℂ) - z) * u x) x)
    (hu2 : MemLp u 2 (volume.restrict Y)) :
    (conj z - z) * ((‖hu2.toLp‖ ^ 2 : ℝ) : ℂ) = s * conj (wronskianConj u u c) := by
  have hside' : Y = X ∩ Iio c ∨ Y = X ∩ Ioi c := by
    rcases hside with h | h
    · exact Or.inl h.1
    · exact Or.inr h.1
  have hs0 : s ≠ 0 := by rcases hside with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> norm_num
  obtain ⟨hY, hYc, hYne, hYX⟩ := halfInterval_props hX hXc hc hside'
  have hqY : ContinuousOn q Y := hq.mono hYX
  have hT := isSymmetricDLMF_minOp hY hqY
  have : ∀ w : ℂ, FiniteDimensional ℂ (deficiencySpace (minOp Y q) w) := fun w =>
    (dlmf_1_18_ix_finrank_le hY hYc hYne hqY w).1
  have hI : Module.finrank ℂ (deficiencySpace (minOp Y q) Complex.I) = 1 := by
    rw [← finrank_deficiency_eq_I hY hYc hYne hqY hz, h1]
  have hmI : Module.finrank ℂ (deficiencySpace (minOp Y q) (-Complex.I)) = 1 := by
    rw [← Complex.conj_I, ← dlmf_1_18_ix_deficiency_eq hY hYc hYne hqY, hI]
  -- the solution and the test functions in `D(T*)`
  have hsolY : IsSolution Y q z u := ⟨u', fun x hx => hu x (hYX hx)⟩
  have hmem := (dlmf_1_18_ix_deficiency_iff hY hYc hYne hqY z hu2.toLp).mpr
    ⟨u, hsolY, hu2.coeFn_toLp⟩
  obtain ⟨hFd, hTF⟩ := mem_eigenspaceDLMF.mp hmem
  set F : (minOp Y q)†.domain := ⟨hu2.toLp, hFd⟩
  obtain ⟨r, hr, hIcc⟩ := exists_Icc_ball hX hc
  obtain ⟨e₁, e₂, he₁, he₂, hs₁, hs₂, he₁c, he₁d, he₂c, he₂d⟩ := exists_boundary_pair hr hIcc
  obtain ⟨hE₁, hTE₁⟩ := mem_adjoint_of_isC2c hX hq hY hYX he₁
  obtain ⟨hE₂, hTE₂⟩ := mem_adjoint_of_isC2c hX hq hY hYX he₂
  set E₁ : (minOp Y q)†.domain := ⟨_, hE₁⟩
  set E₂ : (minOp Y q)†.domain := ⟨_, hE₂⟩
  set B : (minOp Y q)†.domain → (minOp Y q)†.domain → ℂ := fun x y =>
    ⟪(minOp Y q)† x, (y : L2X Y)⟫_ℂ - ⟪(x : L2X Y), (minOp Y q)† y⟫_ℂ
  have Badd : ∀ x y w, B (x + y) w = B x w + B y w := fun x y w => by
    simp only [B, LinearPMap.map_add, Submodule.coe_add, inner_add_left]; ring
  have Bconj : ∀ x y, B x y = -conj (B y x) := fun x y => by
    simp only [B, _root_.map_sub, inner_conj_symm]; ring
  have Bzero : ∀ x y : (minOp Y q)†.domain, ((x : L2X Y) ∈ (minOp Y q)††.domain) →
      B x y = 0 := fun x y hx =>
    hT.boundary_eq_zero_of_mem x y hx
  -- linear combinations of test functions
  set ê : ℂ → ℂ → ℝ → ℂ := fun α β => α • e₁ + β • e₂
  have hê : ∀ α β, IsC2c X (ê α β) := fun α β => (he₁.smul α).add (he₂.smul β)
  have hsm : ∀ (a : ℂ) (e : ℝ → ℂ), tsupport (a • e) ⊆ tsupport e := fun a e => by
    have := tsupport_smul_subset_right (fun _ : ℝ => a) e
    exact this
  have hês : ∀ α β, tsupport (ê α β) ⊆ Ioo (c - r) (c + r) := fun α β =>
    (tsupport_add _ _).trans (union_subset ((hsm α e₁).trans hs₁) ((hsm β e₂).trans hs₂))
  have hêc : ∀ α β, ê α β c = β := fun α β => by simp [ê, he₁c, he₂c]
  have hêd : ∀ α β, deriv (ê α β) c = α := fun α β => by
    have d1 : DifferentiableAt ℝ e₁ c := he₁.1.differentiable (by norm_num) c
    have d2 : DifferentiableAt ℝ e₂ c := he₂.1.differentiable (by norm_num) c
    simp only [ê]
    rw [deriv_add (d1.const_smul α) (d2.const_smul β), deriv_const_smul _ d1,
      deriv_const_smul _ d2, he₁d, he₂d]
    simp
  have hêL : ∀ α β, ((α • E₁ + β • E₂ : (minOp Y q)†.domain) : L2X Y) =
      ((hê α β).memLp_on Y).toLp := fun α β => by
    refine Lp.ext ?_
    simp only [Submodule.coe_add, Submodule.coe_smul, E₁, E₂]
    filter_upwards [Lp.coeFn_add (α • (he₁.memLp_on Y).toLp) (β • (he₂.memLp_on Y).toLp),
      Lp.coeFn_smul α (he₁.memLp_on Y).toLp, Lp.coeFn_smul β (he₂.memLp_on Y).toLp,
      (he₁.memLp_on Y).coeFn_toLp, (he₂.memLp_on Y).coeFn_toLp,
      ((hê α β).memLp_on Y).coeFn_toLp] with x h1 h2 h3 h4 h5 h6
    rw [h1, Pi.add_apply, h2, h3, Pi.smul_apply, Pi.smul_apply, h4, h5, h6]
    simp [ê]
  -- the boundary form of a combination against the test functions
  have hBcomb : ∀ α β, ∀ (g : ℝ → ℂ) (hg : IsC2c X g), tsupport g ⊆ Ioo (c - r) (c + r) →
      ∀ hG : (hg.memLp_on Y).toLp ∈ (minOp Y q)†.domain,
      B (α • E₁ + β • E₂) ⟨_, hG⟩ = s * conj (wronskianConj (ê α β) g c) := by
    intro α β g hg hgs hG
    obtain ⟨hF', hG', hB'⟩ := boundaryForm_testFunctions hX hq hr hIcc (hê α β) hg (hês α β) hgs
      hY hYX s hside
    have he : (α • E₁ + β • E₂ : (minOp Y q)†.domain) = ⟨_, hF'⟩ := Subtype.ext (hêL α β)
    rw [he]
    exact hB'
  have hind : ∀ α β : ℂ, ((α • E₁ + β • E₂ : (minOp Y q)†.domain) : L2X Y) ∈
      (minOp Y q)††.domain → α = 0 ∧ β = 0 := by
    intro α β hm
    have h₁ := hBcomb α β e₁ he₁ hs₁ hE₁
    have h₂ := hBcomb α β e₂ he₂ hs₂ hE₂
    rw [Bzero _ _ hm] at h₁ h₂
    have w₁ : wronskianConj (ê α β) e₁ c = β := by
      simp [wronskianConj, hêc, hêd, he₁c, he₁d]
    have w₂ : wronskianConj (ê α β) e₂ c = -α := by
      simp [wronskianConj, hêc, hêd, he₂c, he₂d]
    rw [w₁] at h₁
    rw [w₂] at h₂
    have hb : conj β = 0 := (mul_eq_zero.mp h₁.symm).resolve_left hs0
    have ha : conj (-α) = 0 := (mul_eq_zero.mp h₂.symm).resolve_left hs0
    simp only [map_eq_zero, neg_eq_zero] at hb ha
    exact ⟨ha, hb⟩
  obtain ⟨α, β, hdec⟩ := hT.exists_decomp_of_finrank_one hI hmI E₁ E₂ hind F
  set Ê : (minOp Y q)†.domain := α • E₁ + β • E₂
  set h : (minOp Y q)†.domain := F - α • E₁ - β • E₂
  have hFeq : F = h + Ê := by simp only [h, Ê]; abel
  -- `B(F, E_j)` computed directly
  have hBF : ∀ (g : ℝ → ℂ) (hg : IsC2c X g), tsupport g ⊆ Ioo (c - r) (c + r) →
      ∀ hG : (hg.memLp_on Y).toLp ∈ (minOp Y q)†.domain,
      (minOp Y q)† ⟨_, hG⟩ = (hg.memLp_schrodingerOp_on hX hq Y).toLp →
      B F ⟨_, hG⟩ = s * conj (wronskianConj u g c) := by
    intro g hg hgs hG hTG
    simp only [B, F, hTF, hTG]
    rw [inner_L2X, inner_L2X, ← integral_solution_test hX hq hu hr hIcc hg hgs hY s hside,
      ← integral_sub]
    · refine integral_congr_ae ?_
      filter_upwards [Lp.coeFn_smul z hu2.toLp, hu2.coeFn_toLp, (hg.memLp_on Y).coeFn_toLp,
        (hg.memLp_schrodingerOp_on hX hq Y).coeFn_toLp] with x h1 h2 h3 h4
      rw [h1, Pi.smul_apply, h2, h3, h4, smul_eq_mul]
    · exact (L2.integrable_inner (𝕜 := ℂ) (z • hu2.toLp) (hg.memLp_on Y).toLp).congr
        (ae_of_all _ fun x => by simp only [RCLike.inner_apply]; ring)
    · exact (L2.integrable_inner (𝕜 := ℂ) hu2.toLp (hg.memLp_schrodingerOp_on hX hq Y).toLp).congr
        (ae_of_all _ fun x => by simp only [RCLike.inner_apply]; ring)
  have hsplit : ∀ w, B F w = B Ê w := fun w => by rw [hFeq, Badd, Bzero h w hdec, zero_add]
  have Bright : ∀ x y w, B x (y + w) = B x y + B x w := fun x y w => by
    rw [Bconj x (y + w), Badd, Bconj x y, Bconj x w, _root_.map_add]
    ring
  have hcancel : ∀ a b : ℂ, s * conj a = s * conj b → a = b := fun a b hab =>
    (starRingEnd ℂ).injective (mul_left_cancel₀ hs0 hab)
  have hu1 : u c = β := by
    have := hcancel _ _ ((hBF e₁ he₁ hs₁ hE₁ hTE₁).symm.trans
      ((hsplit E₁).trans (hBcomb α β e₁ he₁ hs₁ hE₁)))
    simpa [wronskianConj, hêc, hêd, he₁c, he₁d] using this
  have hu1' : deriv u c = α := by
    have := hcancel _ _ ((hBF e₂ he₂ hs₂ hE₂ hTE₂).symm.trans
      ((hsplit E₂).trans (hBcomb α β e₂ he₂ hs₂ hE₂)))
    simpa [wronskianConj, hêc, hêd, he₂c, he₂d] using this
  -- `B(F, F)` in two ways
  have hFF : B F F = (conj z - z) * ((‖hu2.toLp‖ ^ 2 : ℝ) : ℂ) := by
    simp only [B, F, hTF, inner_smul_left, inner_smul_right]
    rw [show ⟪(hu2.toLp : L2X Y), hu2.toLp⟫_ℂ = ((‖hu2.toLp‖ ^ 2 : ℝ) : ℂ) from
      dlmfInner_self _]
    ring
  obtain ⟨hÊm, -⟩ := mem_adjoint_of_isC2c hX hq hY hYX (hê α β)
  have hÊeq : (⟨_, hÊm⟩ : (minOp Y q)†.domain) = Ê := Subtype.ext (hêL α β).symm
  have hÊÊ : B Ê Ê = s * conj (wronskianConj (ê α β) (ê α β) c) := by
    have := hBcomb α β (ê α β) (hê α β) (hês α β) hÊm
    rw [hÊeq] at this
    exact this
  have hW : wronskianConj (ê α β) (ê α β) c = wronskianConj u u c := by
    simp only [wronskianConj, hêc, hêd, hu1, hu1']
  calc (conj z - z) * ((‖hu2.toLp‖ ^ 2 : ℝ) : ℂ) = B F F := hFF.symm
    _ = B Ê F := hsplit F
    _ = B Ê h + B Ê Ê := by rw [show B Ê F = B Ê (h + Ê) by rw [← hFeq], Bright]
    _ = B Ê Ê := by rw [Bconj Ê h, Bzero h Ê hdec, _root_.map_zero, neg_zero, zero_add]
    _ = s * conj (wronskianConj u u c) := by rw [hÊÊ, hW]

/-! ### The index formula -/

theorem memLp_of_sides {c r : ℝ} (hIcc : Icc (c - r) (c + r) ⊆ X)
    {u : ℝ → ℂ} (hu : ContinuousOn u X) (h1 : MemLp u 2 (volume.restrict (X ∩ Iio c)))
    (h2 : MemLp u 2 (volume.restrict (X ∩ Ioi c))) (hr : 0 ≤ r) :
    MemLp u 2 (volume.restrict X) := by
  have h3 := memLp_union h1 (memLp_union (memLp_Icc_of_continuousOn hu hIcc) h2)
  refine h3.mono_measure (Measure.restrict_mono (fun x hx => ?_) le_rfl)
  rcases lt_trichotomy x c with h | rfl | h
  · exact Or.inl ⟨hx, h⟩
  · exact Or.inr (Or.inl ⟨by linarith, by linarith⟩)
  · exact Or.inr (Or.inr ⟨hx, h⟩)

/-- If one side is limit circle and the other limit point, `dim N_z = 1`. -/
theorem finrank_eq_one_of_LC_LP (hX : IsOpen X) (hXc : X.OrdConnected) (hq : ContinuousOn q X)
    {c : ℝ} (hc : c ∈ X) {z : ℂ} {Ya Yb : Set ℝ}
    (hab : (Ya = X ∩ Iio c ∧ Yb = X ∩ Ioi c) ∨ (Ya = X ∩ Ioi c ∧ Yb = X ∩ Iio c))
    (hA : ∀ u, IsSolution Ya q z u → MemLp u 2 (volume.restrict Ya))
    (hB : Module.finrank ℂ (deficiencySpace (minOp Yb q) z) = 1) :
    Module.finrank ℂ (deficiencySpace (minOp X q) z) = 1 := by
  have hsa : Ya = X ∩ Iio c ∨ Ya = X ∩ Ioi c := by
    rcases hab with h | h
    · exact Or.inl h.1
    · exact Or.inr h.1
  have hsb : Yb = X ∩ Iio c ∨ Yb = X ∩ Ioi c := by
    rcases hab with h | h
    · exact Or.inr h.2
    · exact Or.inl h.2
  obtain ⟨hYa, hYac, hYane, hYaX⟩ := halfInterval_props hX hXc hc hsa
  obtain ⟨hYb, hYbc, hYbne, hYbX⟩ := halfInterval_props hX hXc hc hsb
  have hXne : X.Nonempty := ⟨c, hc⟩
  obtain ⟨r, hr, hIcc⟩ := exists_Icc_ball hX hc
  have hglue : ∀ v, IsSolution X q z v → MemLp v 2 (volume.restrict Yb) →
      MemLp v 2 (volume.restrict X) := fun v hv hvb => by
    have hva := hA v (hv.mono hYaX)
    rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact memLp_of_sides hIcc hv.continuousOn hva hvb hr.le
    · exact memLp_of_sides hIcc hv.continuousOn hvb hva hr.le
  have hle := (dlmf_1_18_ix_finrank_le hX hXc hXne hq z).2
  have hfd := (dlmf_1_18_ix_finrank_le hYb hYbc hYbne (hq.mono hYbX) z).1
  -- `≤ 1`
  have h1 : Module.finrank ℂ (deficiencySpace (minOp X q) z) ≠ 2 := by
    intro h2
    have hall := (finrank_eq_two_iff hX hXc hXne hq z).mp h2
    have : Module.finrank ℂ (deficiencySpace (minOp Yb q) z) = 2 := by
      refine (finrank_eq_two_iff hYb hYbc hYbne (hq.mono hYbX) z).mpr fun u hu => ?_
      obtain ⟨v, hv, hvu⟩ := hu.extend hX hXc hq hYbc hYbne hYbX
      exact ((hall v hv).mono_measure (Measure.restrict_mono hYbX le_rfl)).ae_eq
        ((ae_restrict_iff' hYb.measurableSet).mpr (ae_of_all _ fun x hx => hvu hx))
    omega
  -- `≥ 1`
  have h0 : Module.finrank ℂ (deficiencySpace (minOp X q) z) ≠ 0 := by
    intro h0
    obtain ⟨w, hw⟩ := (Module.finrank_pos_iff_exists_ne_zero).mp (by omega : 0 <
      Module.finrank ℂ (deficiencySpace (minOp Yb q) z))
    obtain ⟨hs, hwa⟩ := solRep_spec hYb hYbc hYbne (hq.mono hYbX) z w
    obtain ⟨v, hv, hvu⟩ := hs.extend hX hXc hq hYbc hYbne hYbX
    have hvb : MemLp v 2 (volume.restrict Yb) := (Lp.memLp (w : L2X Yb)).ae_eq
      (hwa.trans ((ae_restrict_iff' hYb.measurableSet).mpr
        (ae_of_all _ fun x hx => (hvu hx).symm)))
    have hvX := hglue v hv hvb
    have hmem := (dlmf_1_18_ix_deficiency_iff hX hXc hXne hq z hvX.toLp).mpr
      ⟨v, hv, hvX.coeFn_toLp⟩
    have : FiniteDimensional ℂ (deficiencySpace (minOp X q) z) :=
      (dlmf_1_18_ix_finrank_le hX hXc hXne hq z).1
    have hbot : deficiencySpace (minOp X q) z = ⊥ := Submodule.finrank_eq_zero.mp h0
    rw [hbot, Submodule.mem_bot] at hmem
    have hv0 : v =ᵐ[volume.restrict X] 0 :=
      hvX.coeFn_toLp.symm.trans (by rw [hmem]; exact Lp.coeFn_zero _ _ _)
    apply hw
    refine Subtype.ext (Lp.eq_zero_iff_ae_eq_zero.mpr (hwa.trans ?_))
    have := (ae_restrict_iff' hX.measurableSet).mp hv0
    refine (ae_restrict_iff' hYb.measurableSet).mpr ?_
    filter_upwards [this] with x hx hxb
    rw [← hvu hxb]; exact hx (hYbX hxb)
  omega

/-- If both sides are limit point, `N_z = 0`. -/
theorem deficiency_eq_bot_of_LP_LP (hX : IsOpen X) (hXc : X.OrdConnected)
    (hq : ContinuousOn q X) {c : ℝ} (hc : c ∈ X) {z : ℂ} (hz : z.im ≠ 0)
    (h1 : Module.finrank ℂ (deficiencySpace (minOp (X ∩ Iio c) q) z) = 1)
    (h2 : Module.finrank ℂ (deficiencySpace (minOp (X ∩ Ioi c) q) z) = 1) :
    deficiencySpace (minOp X q) z = ⊥ := by
  have hXne : X.Nonempty := ⟨c, hc⟩
  rw [Submodule.eq_bot_iff]
  intro v hv
  obtain ⟨u, ⟨u', hu⟩, hvu⟩ := (dlmf_1_18_ix_deficiency_iff hX hXc hXne hq z v).mp hv
  have hu2 : MemLp u 2 (volume.restrict X) := (Lp.memLp v).ae_eq hvu
  have hu2₁ : MemLp u 2 (volume.restrict (X ∩ Iio c)) :=
    hu2.mono_measure (Measure.restrict_mono inter_subset_left le_rfl)
  have hu2₂ : MemLp u 2 (volume.restrict (X ∩ Ioi c)) :=
    hu2.mono_measure (Measure.restrict_mono inter_subset_left le_rfl)
  have e1 := side_identity hX hXc hq hc hz 1 (Or.inl ⟨rfl, rfl⟩) h1 hu hu2₁
  have e2 := side_identity hX hXc hq hc hz (-1) (Or.inr ⟨rfl, rfl⟩) h2 hu hu2₂
  have hzz : conj z - z ≠ 0 := by
    intro h
    apply hz
    have := congrArg Complex.im h
    simp at this
    linarith
  have hsum : (conj z - z) * (((‖hu2₁.toLp‖ ^ 2 : ℝ) : ℂ) + ((‖hu2₂.toLp‖ ^ 2 : ℝ) : ℂ)) = 0 := by
    rw [mul_add, e1, e2]; ring
  have hn : ‖hu2₁.toLp‖ ^ 2 + ‖hu2₂.toLp‖ ^ 2 = 0 := by
    have := (mul_eq_zero.mp hsum).resolve_left hzz
    exact_mod_cast this
  have hF : hu2₁.toLp = 0 := by
    have : ‖hu2₁.toLp‖ ^ 2 = 0 := by nlinarith [sq_nonneg ‖hu2₁.toLp‖, sq_nonneg ‖hu2₂.toLp‖]
    exact norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp this)
  -- `u = 0` on `X ∩ (−∞, c)`, hence on `X`
  obtain ⟨hY, hYc, hYne, hYX⟩ := halfInterval_props hX hXc hc (Or.inl rfl)
  have hu0 : u =ᵐ[volume.restrict (X ∩ Iio c)] 0 :=
    hu2₁.coeFn_toLp.symm.trans (by rw [hF]; exact Lp.coeFn_zero _ _ _)
  have hcu : ContinuousOn u (X ∩ Iio c) := fun x hx =>
    (hu x (hYX hx)).1.continuousAt.continuousWithinAt
  have heq := eqOn_of_ae_eq_of_continuousOn hY hcu continuousOn_const hu0
  obtain ⟨y0, hy0⟩ := hYne
  have hev : u =ᶠ[𝓝 y0] 0 := Filter.eventuallyEq_of_mem (hY.mem_nhds hy0) heq
  have hd : u' y0 = 0 := by
    rw [← (hu y0 (hYX hy0)).1.deriv, hev.deriv_eq]; simp
  have hW : ContinuousOn (fun x => (q x : ℂ) - z) X :=
    (Complex.continuous_ofReal.comp_continuousOn hq).sub continuousOn_const
  have hz0 := ode2c_eq_zero_on hXc hW (fun x hx => (hu x hx).1) (fun x hx => (hu x hx).2)
    (hYX hy0) (heq hy0) hd
  refine Lp.eq_zero_iff_ae_eq_zero.mpr (hvu.trans ?_)
  exact (ae_restrict_iff' hX.measurableSet).mpr (ae_of_all _ fun x hx => hz0 x hx)

/-- **DLMF §1.18(ix)**: the (equal) deficiency indices of `ℒ` are `n₁ + n₂ − 2`. -/
theorem dlmf_1_18_ix_index_formula (hX : IsOpen X) (hXc : X.OrdConnected)
    (hq : ContinuousOn q X) {c : ℝ} (hc : c ∈ X) {z : ℂ} (hz : z.im ≠ 0) :
    Module.finrank ℂ (deficiencySpace (minOp X q) z) + 2 =
      Module.finrank ℂ (deficiencySpace (minOp (X ∩ Iio c) q) z) +
        Module.finrank ℂ (deficiencySpace (minOp (X ∩ Ioi c) q) z) := by
  have hXne : X.Nonempty := ⟨c, hc⟩
  obtain ⟨hL, hLc, hLne, hLX⟩ := halfInterval_props hX hXc hc (Or.inl rfl)
  obtain ⟨hR, hRc, hRne, hRX⟩ := halfInterval_props hX hXc hc (Or.inr rfl)
  have wL := dlmf_1_18_ix_weyl_alternative hX hXc hq hc hz (Y := X ∩ Iio c) (Or.inl rfl)
  have wR := dlmf_1_18_ix_weyl_alternative hX hXc hq hc hz (Y := X ∩ Ioi c) (Or.inr rfl)
  have eL := finrank_eq_two_iff hL hLc hLne (hq.mono hLX) z
  have eR := finrank_eq_two_iff hR hRc hRne (hq.mono hRX) z
  obtain ⟨r, hr, hIcc⟩ := exists_Icc_ball hX hc
  rcases (show Module.finrank ℂ (deficiencySpace (minOp (X ∩ Iio c) q) z) = 1 ∨
      Module.finrank ℂ (deficiencySpace (minOp (X ∩ Iio c) q) z) = 2 by omega) with h1 | h1 <;>
    rcases (show Module.finrank ℂ (deficiencySpace (minOp (X ∩ Ioi c) q) z) = 1 ∨
      Module.finrank ℂ (deficiencySpace (minOp (X ∩ Ioi c) q) z) = 2 by omega) with h2 | h2
  · rw [deficiency_eq_bot_of_LP_LP hX hXc hq hc hz h1 h2, finrank_bot, h1, h2]
  · rw [finrank_eq_one_of_LC_LP hX hXc hq hc (Or.inr ⟨rfl, rfl⟩) (eR.mp h2) h1, h1, h2]
  · rw [finrank_eq_one_of_LC_LP hX hXc hq hc (Or.inl ⟨rfl, rfl⟩) (eL.mp h1) h2, h1, h2]
  · have : Module.finrank ℂ (deficiencySpace (minOp X q) z) = 2 :=
      (finrank_eq_two_iff hX hXc hXne hq z).mpr fun u hu =>
        memLp_of_sides hIcc hu.continuousOn (eL.mp h1 u (hu.mono hLX))
          (eR.mp h2 u (hu.mono hRX)) hr.le
    rw [this, h1, h2]

end Azurite.DLMF
