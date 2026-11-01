/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter1.Section18WeylExt

/-!
# DLMF §1.18(ix): limit circle at both ends

DLMF states that any self-adjoint extension of `ℒ` is obtained by restricting `ℒ*` to
`B₁(f) = 0` (if `n₁ = 2`), `B₂(f) = 0` (if `n₂ = 2`), with `B₁` a boundary value at `a` and `B₂`
one at `b`. When both ends are limit circle this needs D–S's qualifier (Cor. XIII.2.31) "if the
boundary conditions are separated": `dlmf_1_18_ix_ext_LC_LC_counterexample` exhibits, for
`q = 0` on `(0, 1)`, a self-adjoint extension containing `e^{2πix}` but not its cut-off near `0`;
separated conditions would contain both.
-/

open Set Filter Topology MeasureTheory LinearPMap Complex Real
open scoped InnerProductSpace ComplexConjugate ContDiff

namespace Azurite.DLMF

/-! ### Unitaries between finite-dimensional spaces -/

theorem orthonormal_singleton_unit {ι F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    (i₀ : ι) {u : F} (hu : u ≠ 0) :
    Orthonormal ℂ (({i₀} : Set ι).domRestrict fun _ => ((‖u‖⁻¹ : ℝ) : ℂ) • u) := by
  rw [orthonormal_iff_ite]
  intro i j
  have hij : i = j := Subtype.ext (i.2.trans j.2.symm)
  subst hij
  simp only [Set.domRestrict_apply, ↓reduceIte]
  rw [inner_self_eq_norm_sq_to_K, norm_smul]
  simp [norm_ne_zero_iff.mpr hu]

theorem exists_isometry_map {E E' : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup E'] [InnerProductSpace ℂ E'] [FiniteDimensional ℂ E]
    [FiniteDimensional ℂ E'] (hfr : Module.finrank ℂ E = Module.finrank ℂ E') {a : E} {b : E'}
    (ha : a ≠ 0) (hab : ‖a‖ = ‖b‖) : ∃ U : E ≃ₗᵢ[ℂ] E', U a = b := by
  have hb : b ≠ 0 := by
    intro h; rw [h, norm_zero, norm_eq_zero] at hab; exact ha hab
  have hn : 0 < Module.finrank ℂ E := Module.finrank_pos_iff_exists_ne_zero.mpr ⟨a, ha⟩
  set i₀ : Fin (Module.finrank ℂ E) := ⟨0, hn⟩
  obtain ⟨b₁, hb₁⟩ := Orthonormal.exists_orthonormalBasis_extension_of_card_eq (𝕜 := ℂ)
    (E := E) (ι := Fin (Module.finrank ℂ E)) (by simp) (orthonormal_singleton_unit i₀ ha)
  obtain ⟨b₂, hb₂⟩ := Orthonormal.exists_orthonormalBasis_extension_of_card_eq (𝕜 := ℂ)
    (E := E') (ι := Fin (Module.finrank ℂ E)) (by simp [hfr]) (orthonormal_singleton_unit i₀ hb)
  refine ⟨b₁.equiv b₂ (Equiv.refl _), ?_⟩
  have e1 := hb₁ i₀ rfl
  have e2 := hb₂ i₀ rfl
  have hna : (‖a‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr ha
  have ha' : a = (‖a‖ : ℂ) • b₁ i₀ := by
    rw [e1, smul_smul]; push_cast; rw [mul_inv_cancel₀ hna, one_smul]
  rw [ha', LinearIsometryEquiv.map_smul, OrthonormalBasis.equiv_apply_basis, Equiv.refl_apply, e2,
    smul_smul, hab]
  have hnb : (‖b‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr hb
  push_cast; rw [mul_inv_cancel₀ hnb, one_smul]

/-! ### Solutions on bounded subintervals -/

/-- A solution on `Y ⊆ [α, β] ⊆ X'` is square integrable on `Y`. -/
theorem memLp_of_isSolution_of_subset_Icc {X' Y : Set ℝ} {q : ℝ → ℝ} (hX' : IsOpen X')
    (hX'c : X'.OrdConnected) (hq : ContinuousOn q X') (hYc : Y.OrdConnected) (hYne : Y.Nonempty)
    {α β : ℝ} (hYI : Y ⊆ Icc α β) (hIX : Icc α β ⊆ X') {z : ℂ} {u : ℝ → ℂ}
    (hu : IsSolution Y q z u) : MemLp u 2 (volume.restrict Y) := by
  obtain ⟨v, hv, hvu⟩ := hu.extend hX' hX'c hq hYc hYne (hYI.trans hIX)
  have hvc := hv.continuousOn.mono hIX
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hvc
  have hm : MemLp v 2 (volume.restrict (Icc α β)) :=
    MemLp.of_bound (hvc.aestronglyMeasurable measurableSet_Icc) C
      (by filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx using hC x hx)
  refine (hm.mono_measure (Measure.restrict_mono hYI le_rfl)).ae_eq ?_
  have hYm : MeasurableSet Y := hYc.measurableSet
  filter_upwards [ae_restrict_mem hYm] with x hx using hvu hx

/-! ### The function `e^{2πix}` -/

/-- `e^{2πix}`, a solution of `−u″ = 4π²u`. -/
noncomputable def expSol (x : ℝ) : ℂ := cexp (2 * π * I * x)

theorem expSol_hasDerivAt (x : ℝ) :
    HasDerivAt expSol (2 * π * I * expSol x) x ∧
      HasDerivAt (fun x => 2 * π * I * expSol x)
        ((((0 : ℝ) : ℂ) - ((4 * π ^ 2 : ℝ) : ℂ)) * expSol x) x := by
  have h1 : HasDerivAt expSol (2 * π * I * expSol x) x := by
    have := (((hasDerivAt_id x).ofReal_comp).const_mul (2 * π * I)).cexp
    have e : expSol = fun y : ℝ => cexp (2 * π * I * (y : ℂ)) := rfl
    rw [e]
    convert this using 1
    · rfl
    · beta_reduce
      rw [id_eq, Complex.ofReal_one, mul_one, mul_comm]
  refine ⟨h1, (h1.const_mul (2 * π * I)).congr_deriv ?_⟩
  push_cast
  ring_nf
  rw [I_sq]
  ring

theorem conj_expSol_mul (x : ℝ) : conj (expSol x) * expSol x = 1 := by
  rw [expSol, ← Complex.exp_conj, ← Complex.exp_add]
  have : conj (2 * π * I * (x : ℂ)) + 2 * π * I * x = 0 := by
    simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, map_ofNat]
    ring
  rw [this, Complex.exp_zero]

theorem norm_expSol (x : ℝ) : ‖expSol x‖ = 1 := by
  rw [expSol, Complex.norm_exp]
  simp

theorem continuous_expSol : Continuous expSol := by
  unfold expSol; fun_prop

/-! ### The counterexample -/

/-- The limit-circle/limit-circle case of DLMF §1.18(ix) on `(0, 1)` with `q = 0`: both ends are
limit circle, yet some self-adjoint extension of `ℒ` is not given by separated conditions
`B₁(f) = 0`, `B₂(f) = 0` with `B₁` a boundary value at `a` and `B₂` at `b` (an example is the
periodic extension; DLMF omits D–S's qualifier "if the boundary conditions are separated"). -/
theorem dlmf_1_18_ix_ext_LC_LC_counterexample :
    Module.finrank ℂ (deficiencySpace (minOp (Ioo (0 : ℝ) 1 ∩ Iio (1 / 2)) fun _ => 0) I) = 2 ∧
      Module.finrank ℂ (deficiencySpace (minOp (Ioo (0 : ℝ) 1 ∩ Ioi (1 / 2)) fun _ => 0) I) =
        2 ∧
      ∃ A : L2X (Ioo (0 : ℝ) 1) →ₗ.[ℂ] L2X (Ioo (0 : ℝ) 1), IsSelfAdjoint A ∧
        minOp (Ioo (0 : ℝ) 1) (fun _ => 0) ≤ A ∧
        ∀ B₁ ∈ boundaryValuesLeft (Ioo (0 : ℝ) 1) (fun _ => 0),
        ∀ B₂ ∈ boundaryValuesRight (Ioo (0 : ℝ) 1) (fun _ => 0),
          ¬ ∀ f : (minOp (Ioo (0 : ℝ) 1) fun _ => 0)†.domain,
            ((f : L2X (Ioo (0 : ℝ) 1)) ∈ A.domain ↔ B₁ f = 0 ∧ B₂ f = 0) := by
  set X : Set ℝ := Ioo (0 : ℝ) 1
  set q : ℝ → ℝ := fun _ => 0
  have hX : IsOpen X := isOpen_Ioo
  have hXc : X.OrdConnected := ordConnected_Ioo
  have hq : ContinuousOn q X := continuousOn_const
  have hne : X.Nonempty := ⟨1 / 2, by norm_num [X], by norm_num [X]⟩
  have hT := isSymmetricDLMF_minOp hX hq
  -- both ends are limit circle
  have hLC : ∀ {Y : Set ℝ}, Y = X ∩ Iio (1 / 2) ∨ Y = X ∩ Ioi (1 / 2) →
      Module.finrank ℂ (deficiencySpace (minOp Y q) I) = 2 := fun {Y} hY => by
    obtain ⟨hYo, hYc, hYne, hYX⟩ := halfInterval_props hX hXc
      (show (1 / 2 : ℝ) ∈ X by norm_num [X]) hY
    refine (finrank_eq_two_iff hYo hYc hYne (hq.mono hYX) I).mpr fun u hu => ?_
    exact memLp_of_isSolution_of_subset_Icc (X' := Ioo (-1) 2) isOpen_Ioo ordConnected_Ioo
      continuousOn_const hYc hYne (fun x hx => ⟨(hYX hx).1.le, (hYX hx).2.le⟩)
      (fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩) hu
  refine ⟨hLC (Or.inl rfl), hLC (Or.inr rfl), ?_⟩
  -- `h = e^{2πix}` and `ℒ*h = 4π² h`
  set lam : ℂ := ((4 * π ^ 2 : ℝ) : ℂ)
  set κ : ℂ := 2 * π * I
  have hsol : ∀ x ∈ X, HasDerivAt expSol (κ * expSol x) x ∧
      HasDerivAt (fun x => κ * expSol x) (((q x : ℂ) - lam) * expSol x) x :=
    fun x _ => expSol_hasDerivAt x
  have hL2 : MemLp expSol 2 (volume.restrict X) :=
    MemLp.of_bound continuous_expSol.aestronglyMeasurable 1
      (ae_of_all _ fun x => (norm_expSol x).le)
  have hmem := (dlmf_1_18_ix_deficiency_iff hX hXc hne hq lam hL2.toLp).mpr
    ⟨expSol, ⟨_, hsol⟩, hL2.coeFn_toLp⟩
  obtain ⟨hD, hTh⟩ := mem_eigenspaceDLMF.mp hmem
  set H : (minOp X q)†.domain := ⟨_, hD⟩
  -- the cut-off `χh`
  obtain ⟨χ, hχ, hχb, hχ1, hχ0, hχc⟩ := exists_cutoff (show (1 / 3 : ℝ) < 2 / 3 by norm_num)
  have hχcc : Continuous fun x => (χ x : ℂ) := Complex.continuous_ofReal.comp hχ.continuous
  have hIcc : Icc (1 / 4 : ℝ) (3 / 4) ⊆ X := fun x hx =>
    ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hχn : ∀ x, ‖(χ x : ℂ)‖ ≤ 1 := fun x => by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hχb x).1]; exact (hχb x).2
  have h1 : MemLp (fun x => (χ x : ℂ) * expSol x) 2 (volume.restrict X) :=
    MemLp.of_bound (hχcc.mul continuous_expSol).aestronglyMeasurable 1
      (ae_of_all _ fun x => by rw [norm_mul, norm_expSol, mul_one]; exact hχn x)
  have hg2 : MemLp (fun x => (χ x : ℂ) * (lam * expSol x)) 2 (volume.restrict X) :=
    MemLp.of_bound (hχcc.mul (continuous_const.mul continuous_expSol)).aestronglyMeasurable
      ‖lam‖ (ae_of_all _ fun x => by
        rw [norm_mul, norm_mul, norm_expSol, mul_one]
        exact mul_le_of_le_one_left (norm_nonneg _) (hχn x))
  obtain ⟨h2, hm, hTK⟩ := mem_adjoint_cutoff_of_weak hX hXc hne hq (F := expSol)
    (F' := fun x => κ * expSol x) (g := fun x => lam * expSol x) (fun x hx => (hsol x hx).1)
    (continuous_const.mul continuous_expSol).continuousOn
    ((continuous_const.mul continuous_expSol).continuousOn.locallyIntegrableOn
      hX.measurableSet)
    (fun ψ hψ => weak_of_isSolution hX hXc hne hq ⟨_, hsol⟩ hψ) hχ hIcc
    (hχc _ _ (by norm_num) (by norm_num)) h1 hg2
  set K : (minOp X q)†.domain := ⟨_, hm⟩
  have hTH : (minOp X q)† H = lam • hL2.toLp := hTh
  have hTK' : (minOp X q)† K = h2.toLp := hTK
  obtain ⟨hχ1c, hχ2c⟩ := cutoff_continuous hχ
  have ii : ∀ {u : ℝ → ℂ}, Continuous u → IntegrableOn u X := fun hu =>
    hu.integrableOn_Icc.mono_set Ioo_subset_Icc_self
  -- the boundary form of `h` against `χh`
  have hflat : ∀ x ∉ Ioo (1 / 4 : ℝ) (3 / 4), deriv χ x = 0 := fun x hx =>
    (hχc _ _ (by norm_num) (by norm_num) x hx).eq_of_nhds
  have hform : formBV H K = -2 * κ := by
    rw [formBV_apply, hTH, hTK', inner_smul_left, Complex.conj_ofReal, inner_L2X, inner_L2X]
    have e1 : ∫ x in X, conj ((hL2.toLp : ℝ → ℂ) x) * ((K : L2X X) : ℝ → ℂ) x =
        ∫ x in X, (χ x : ℂ) := integral_congr_ae (by
      filter_upwards [hL2.coeFn_toLp, h1.coeFn_toLp] with x ha hb
      change conj ((hL2.toLp : ℝ → ℂ) x) * (h1.toLp : ℝ → ℂ) x = _
      rw [ha, hb]
      linear_combination (χ x : ℂ) * conj_expSol_mul x)
    have e2 : ∫ x in X, conj (((H : L2X X) : ℝ → ℂ) x) * (h2.toLp : ℝ → ℂ) x =
        ∫ x in X, ((χ x : ℂ) * lam - 2 * κ * ((deriv χ x : ℝ) : ℂ) -
          ((deriv (deriv χ) x : ℝ) : ℂ)) := integral_congr_ae (by
      filter_upwards [hL2.coeFn_toLp, h2.coeFn_toLp] with x ha hb
      change conj ((hL2.toLp : ℝ → ℂ) x) * _ = _
      rw [ha, hb]
      linear_combination ((χ x : ℂ) * lam - 2 * κ * ((deriv χ x : ℝ) : ℂ) -
          ((deriv (deriv χ) x : ℝ) : ℂ)) * conj_expSol_mul x)
    rw [e1, e2, ← integral_const_mul, ← integral_sub
      (f := fun x => ((4 * π ^ 2 : ℝ) : ℂ) * (χ x : ℂ))
      (g := fun x => (χ x : ℂ) * lam - 2 * κ * ((deriv χ x : ℝ) : ℂ) -
        ((deriv (deriv χ) x : ℝ) : ℂ)) (ii (continuous_const.mul hχcc))
      (ii (((hχcc.mul continuous_const).sub (continuous_const.mul hχ1c)).sub hχ2c))]
    rw [integral_congr_ae (g := fun x => 2 * κ * ((deriv χ x : ℝ) : ℂ) +
      ((deriv (deriv χ) x : ℝ) : ℂ)) (ae_of_all _ fun x => by ring),
      ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one,
      intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun x => 2 * κ * (χ x : ℂ) +
        ((deriv χ x : ℝ) : ℂ))
      (fun x _ => ((cutoff_derivs hχ x).1.const_mul _).add (cutoff_derivs hχ x).2)
      (((continuous_const.mul hχ1c).add hχ2c).intervalIntegrable 0 1)]
    rw [hχ0 1 (by norm_num), hχ1 0 (by norm_num), hflat 0 (fun h => by norm_num at h),
      hflat 1 (fun h => by norm_num at h)]
    push_cast; ring
  have hκ0 : -2 * κ ≠ 0 := by
    simp [κ, Real.pi_ne_zero, I_ne_zero]
  -- von Neumann decomposition of `h`
  obtain ⟨g₀, a, ha, b, hb, hdec⟩ := hT.vonNeumann_decomp H
  have hHH : formBV H H = 0 := by
    rw [formBV_apply, hTH, inner_smul_left, inner_smul_right, Complex.conj_ofReal]
    ring
  have hab : ‖a‖ = ‖b‖ := by
    have h := hT.boundaryForm H H g₀ g₀ ha ha hb hb hdec hdec
    rw [← formBV_apply, hHH, inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h
    have h' : ((‖b‖ ^ 2 : ℝ) : ℂ) = ((‖a‖ ^ 2 : ℝ) : ℂ) := by
      have h2I : (2 * I : ℂ) ≠ 0 := mul_ne_zero two_ne_zero I_ne_zero
      push_cast
      have := (mul_eq_zero.mp h.symm).resolve_left h2I
      exact sub_eq_zero.mp this
    exact ((sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (by exact_mod_cast h')).symm
  have ha0 : a ≠ 0 := by
    intro ha0
    have hb0 : b = 0 := by rw [ha0, norm_zero] at hab; exact norm_eq_zero.mp hab.symm
    have hHg : (H : L2X X) = g₀ := by rw [hdec, ha0, hb0]; simp
    have h := hT.inner_adjoint_adjoint g₀ K
    rw [hT.le_adjoint_adjoint.2.2 (x := g₀) (y := H) hHg.symm, ← hHg, ← sub_eq_zero,
      ← formBV_apply, hform] at h
    exact hκ0 h
  -- a unitary `U : N_i → N_{−i}` with `U a = b`
  have : ∀ w : ℂ, FiniteDimensional ℂ (deficiencySpace (minOp X q) w) := fun w =>
    (dlmf_1_18_ix_finrank_le hX hXc hne hq w).1
  obtain ⟨U, hU⟩ := exists_isometry_map (E := deficiencySpace (minOp X q) I)
    (E' := deficiencySpace (minOp X q) (-I))
    (dlmf_1_18_ix_exists_selfAdjoint hX hXc hne hq).2.1 (a := ⟨a, ha⟩) (b := ⟨b, hb⟩)
    (fun h => ha0 (congrArg Subtype.val h)) hab
  set A := vonNeumannExt (minOp X q) U.toLinearIsometry
  have hA : IsSelfAdjoint A := hT.vonNeumannExt_isSelfAdjoint U
  refine ⟨A, hA, hT.le_vonNeumannExt _, fun B₁ hB₁ B₂ hB₂ hiff => ?_⟩
  have hHA : (H : L2X X) ∈ A.domain := ⟨mem_vonNeumannDomain.mpr ⟨g₀, ⟨a, ha⟩, by
    rw [hdec, LinearIsometryEquiv.coe_toLinearIsometry, hU]⟩, hD⟩
  obtain ⟨hB1H, -⟩ := (hiff H).mp hHA
  have hm3 : MeasurableSet (X ∩ Iio (1 / 3)) := hX.measurableSet.inter measurableSet_Iio
  have hm4 : MeasurableSet (X ∩ Ioi (2 / 3)) := hX.measurableSet.inter measurableSet_Ioi
  have hvanL : VanishesNear X q (fun d => X ∩ Iio d) (H - K) := ⟨1 / 3, by norm_num [X], by
    show (((H : L2X X) - (K : L2X X) : L2X X) : ℝ → ℂ) =ᵐ[volume.restrict (X ∩ Iio _)] 0
    filter_upwards [ae_restrict_of_ae_restrict_of_subset inter_subset_left
        (Lp.coeFn_sub (H : L2X X) (K : L2X X)),
      ae_restrict_of_ae_restrict_of_subset inter_subset_left hL2.coeFn_toLp,
      ae_restrict_of_ae_restrict_of_subset inter_subset_left h1.coeFn_toLp,
      ae_restrict_mem hm3] with x e1 e2 e3 hx
    change _ = (0 : ℂ)
    rw [e1, Pi.sub_apply]
    change (hL2.toLp : ℝ → ℂ) x - (h1.toLp : ℝ → ℂ) x = 0
    rw [e2, e3, hχ1 x hx.2.out.le]; simp⟩
  have hvanR : VanishesNear X q (fun d => X ∩ Ioi d) K := ⟨2 / 3, by norm_num [X], by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset inter_subset_left h1.coeFn_toLp,
      ae_restrict_mem hm4] with x e1 hx
    change (h1.toLp : ℝ → ℂ) x = 0
    rw [e1, hχ0 x hx.2.out.le]; simp⟩
  have hB1K : B₁ K = 0 := by
    have h := hB₁.2 _ hvanL
    rwa [_root_.map_sub, hB1H, zero_sub, neg_eq_zero] at h
  have hKA := (hiff K).mpr ⟨hB1K, hB₂.2 _ hvanR⟩
  have hs := (IsSelfAdjoint.isSymmetricDLMF hA).isFormalAdjoint ⟨_, hHA⟩ ⟨_, hKA⟩
  have hAT := vonNeumannExt_le (T := minOp X q) U.toLinearIsometry
  rw [hAT.2 (x := ⟨_, hHA⟩) (y := H) rfl, hAT.2 (x := ⟨_, hKA⟩) (y := K) rfl] at hs
  have h0 : formBV H K = 0 := by rw [formBV_apply]; exact sub_eq_zero.mpr hs
  exact hκ0 (hform ▸ h0)

end Azurite.DLMF
