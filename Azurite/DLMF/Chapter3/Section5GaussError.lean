/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter3.Section3
import Azurite.DLMF.Chapter3.Section5Gauss

/-!
# DLMF §3.5(v): the remainder 3.5.19 of Gauss quadrature

* Hermite interpolation: `hermite` (`H = ∑ₖ (f(xₖ) + (x − xₖ)(f′(xₖ) − 2ℓₖ′(xₖ)f(xₖ))) ℓₖ²`),
  `hermite_eval`, `hermite_derivative_eval`, `natDegree_hermite_le` (degree `≤ 2n − 1`),
  `hermite_error` (`f(t) − H(t) = f^{(2n)}(ξ)/(2n)! ∏ (t − xₖ)²` with `ξ` in any interval containing
  `t` and the nodes: Rolle between the `n + 1` zeros `t, x₁, …, xₙ` of the auxiliary function gives
  `n` zeros of its derivative, which also vanishes at the nodes, then the generalized Rolle theorem
  `exists_iteratedDeriv_eq_zero` of §3.3(i)).
* 3.5.19: `dlmf_3_5_19` on a finite interval `(a, b)` for `f ∈ C^{2n}` on an open set containing
  `[a, b]`, `n ≥ 1`: `E_n(f) = ∫ (f − H) w` by exactness 3.5.20_1, bounded between
  `min f^{(2n)} γ_n/(2n)!` and `max f^{(2n)} γ_n/(2n)!`; an interior `ξ` by the intermediate value
  theorem, or, in the extreme cases, by `exists_mem_Ioo_notMem_eq_zero` and `hermite_error` on
  `(a, b)`.
-/

open Polynomial Finset Set MeasureTheory

namespace Azurite.DLMF

/-! ### Hermite interpolation -/

/-- The Hermite interpolation polynomial of degree `≤ 2n − 1` matching values `f` and slopes `g`
at the nodes `s`:
`H = ∑ₖ (f(xₖ) + (x − xₖ)(g(xₖ) − 2ℓₖ′(xₖ) f(xₖ))) ℓₖ(x)²`. -/
noncomputable def hermite (s : Finset ℝ) (f g : ℝ → ℝ) : ℝ[X] :=
  ∑ k ∈ s, (C (f k) + (X - C k) * C (g k - 2 * (derivative (Lagrange.basis s id k)).eval k * f k))
    * (Lagrange.basis s id k * Lagrange.basis s id k)

theorem hermite_eval {s : Finset ℝ} (f g : ℝ → ℝ) {j : ℝ} (hj : j ∈ s) :
    (hermite s f g).eval j = f j := by
  have hinj : Set.InjOn (id : ℝ → ℝ) (s : Set ℝ) := Function.injective_id.injOn
  rw [hermite, eval_finsetSum, sum_eq_single_of_mem j hj fun k hk hkj => by
    rw [eval_mul, eval_mul, show (Lagrange.basis s id k).eval j = 0 from
      Lagrange.eval_basis_of_ne (v := id) hkj hj]
    simp]
  rw [eval_mul, eval_mul, show (Lagrange.basis s id j).eval j = 1 from
    Lagrange.eval_basis_self (v := id) hinj hj]
  simp

theorem hermite_derivative_eval {s : Finset ℝ} (f g : ℝ → ℝ) {j : ℝ} (hj : j ∈ s) :
    (derivative (hermite s f g)).eval j = g j := by
  have hinj : Set.InjOn (id : ℝ → ℝ) (s : Set ℝ) := Function.injective_id.injOn
  rw [hermite, derivative_sum, eval_finsetSum, sum_eq_single_of_mem j hj fun k hk hkj => by
    simp only [derivative_mul, derivative_add, derivative_C, derivative_sub, derivative_X,
      eval_add, eval_mul, eval_sub, eval_C, eval_X, eval_zero,
      show (Lagrange.basis s id k).eval j = 0 from Lagrange.eval_basis_of_ne (v := id) hkj hj]
    ring]
  simp only [derivative_mul, derivative_add, derivative_C, derivative_sub, derivative_X,
    eval_add, eval_mul, eval_sub, eval_C, eval_X, eval_zero, eval_one,
    show (Lagrange.basis s id j).eval j = 1 from Lagrange.eval_basis_self (v := id) hinj hj]
  ring

theorem natDegree_hermite_le {s : Finset ℝ} (hs : s.Nonempty) (f g : ℝ → ℝ) :
    (hermite s f g).natDegree ≤ 2 * #s - 1 := by
  have hinj : Set.InjOn (id : ℝ → ℝ) (s : Set ℝ) := Function.injective_id.injOn
  have hpos : 0 < #s := card_pos.mpr hs
  refine natDegree_sum_le_of_forall_le _ _ fun k hk => ?_
  refine (natDegree_mul_le).trans ?_
  have h1 : (C (f k) + (X - C k) *
      C (g k - 2 * (derivative (Lagrange.basis s id k)).eval k * f k)).natDegree ≤ 1 := by
    refine (natDegree_add_le _ _).trans (max_le (by simp) ?_)
    refine (natDegree_mul_le).trans ?_
    simp only [natDegree_C, add_zero]
    exact (natDegree_X_sub_C k).le
  have h2 : (Lagrange.basis s id k * Lagrange.basis s id k).natDegree ≤ 2 * (#s - 1) := by
    refine (natDegree_mul_le).trans ?_
    rw [Lagrange.natDegree_basis hinj hk]
    omega
  omega

theorem differentiableOn_iteratedDeriv_of_contDiffOn {f : ℝ → ℝ} {U : Set ℝ} (hU : IsOpen U)
    {N : ℕ} (hf : ContDiffOn ℝ N f U) : ∀ k < N, DifferentiableOn ℝ (iteratedDeriv k f) U :=
  fun k hk => by
    rw [iteratedDeriv_eq_iterate]
    exact (contDiffOn_iterate_deriv hU hf k hk.le).differentiableOn (by norm_cast; omega)

theorem continuousOn_iteratedDeriv_top_of_contDiffOn {f : ℝ → ℝ} {U : Set ℝ} (hU : IsOpen U)
    {N : ℕ} (hf : ContDiffOn ℝ N f U) : ContinuousOn (iteratedDeriv N f) U := by
  rw [iteratedDeriv_eq_iterate]
  exact (contDiffOn_iterate_deriv hU hf N le_rfl).continuousOn

/-- **The Hermite interpolation error**: for `f ∈ C^{2n}` and `t` in an interval `J` containing
the `n` nodes, `f(t) − H(t) = f^{(2n)}(ξ)/(2n)! · ∏ₖ (t − xₖ)²` for some `ξ ∈ J`. -/
theorem hermite_error {s : Finset ℝ} (hs : s.Nonempty) {f : ℝ → ℝ} {U : Set ℝ} (hU : IsOpen U)
    (hf : ContDiffOn ℝ (2 * #s : ℕ) f U) {J : Set ℝ} (hJ : J.OrdConnected) (hJU : J ⊆ U)
    (hsJ : ∀ x ∈ s, x ∈ J) {t : ℝ} (ht : t ∈ J) :
    ∃ ξ ∈ J, f t - (hermite s f (deriv f)).eval t =
      iteratedDeriv (2 * #s) f ξ / (2 * #s).factorial * (Lagrange.nodal s id).eval t ^ 2 := by
  classical
  set n := #s with hn
  have hpos : 0 < n := card_pos.mpr hs
  set H := hermite s f (deriv f)
  set ω := Lagrange.nodal s id
  by_cases hts : t ∈ s
  · refine ⟨t, ht, ?_⟩
    rw [hermite_eval _ _ hts, sub_self,
      show ω.eval t = 0 from Lagrange.eval_nodal_at_node (v := id) hts]
    simp
  have hω : ω.eval t ≠ 0 := by
    rw [Lagrange.eval_nodal]
    exact prod_ne_zero_iff.mpr fun k hk => sub_ne_zero.mpr fun h => hts (h ▸ hk)
  set K := (f t - H.eval t) / ω.eval t ^ 2
  set Q : ℝ[X] := H + C K * (ω * ω)
  set g : ℝ → ℝ := fun u => f u - Q.eval u
  have hd := differentiableOn_iteratedDeriv_of_contDiffOn hU hf
  have hfd : DifferentiableOn ℝ f U := by simpa using hd 0 (by omega)
  have hgd : DifferentiableOn ℝ g U := hfd.sub Q.differentiable.differentiableOn
  have hgt : g t = 0 := by
    simp only [g, Q, K, eval_add, eval_mul, eval_C]
    field_simp
    ring
  have hgs : ∀ x ∈ s, g x = 0 := fun x hx => by
    simp only [g, Q, eval_add, eval_mul, eval_C, H, hermite_eval _ _ hx,
      show ω.eval x = 0 from Lagrange.eval_nodal_at_node (v := id) hx]
    ring
  have hg's : ∀ x ∈ s, deriv g x = 0 := fun x hx => by
    have hfx : DifferentiableAt ℝ f x := hfd.differentiableAt (hU.mem_nhds (hJU (hsJ x hx)))
    rw [show deriv g x = deriv f x - (derivative Q).eval x from
      (hfx.hasDerivAt.sub (Q.hasDerivAt x)).deriv]
    simp only [Q, derivative_add, derivative_mul, derivative_C, eval_add, eval_mul, eval_C,
      eval_zero, H, hermite_derivative_eval _ _ hx,
      show ω.eval x = 0 from Lagrange.eval_nodal_at_node (v := id) hx]
    ring
  -- the `n + 1` zeros `t, x₁, …, xₙ` of `g`, sorted
  set T := insert t s
  have hT : #T = n + 1 := card_insert_of_notMem hts
  set e := T.orderEmbOfFin hT
  have heJ : ∀ i, e i ∈ J := fun i => by
    rcases mem_insert.mp (T.orderEmbOfFin_mem hT i) with h | h
    · rw [h]; exact ht
    · exact hsJ _ h
  have hge : ∀ i, g (e i) = 0 := fun i => by
    rcases mem_insert.mp (T.orderEmbOfFin_mem hT i) with h | h
    · rw [h]; exact hgt
    · exact hgs _ h
  -- Rolle between consecutive zeros
  have hR : ∀ i : Fin n, ∃ σ ∈ Ioo (e i.castSucc) (e i.succ), deriv g σ = 0 := by
    intro i
    have hlt : e i.castSucc < e i.succ := e.strictMono (Fin.castSucc_lt_succ (i := i))
    have hsub : Icc (e i.castSucc) (e i.succ) ⊆ U := (hJ.out (heJ _) (heJ _)).trans hJU
    exact exists_deriv_eq_zero hlt (hgd.continuousOn.mono hsub) (by rw [hge, hge])
  choose σ hσ hσ0 using hR
  have hσmono : StrictMono σ := fun i j hij => by
    have : e i.succ ≤ e j.castSucc := e.monotone (Fin.le_def.mpr (by simp; omega))
    exact (hσ i).2.trans_le (this.trans (hσ j).1.le)
  have hσJ : ∀ i, σ i ∈ J := fun i => hJ.out (heJ _) (heJ _) ⟨(hσ i).1.le, (hσ i).2.le⟩
  have hσs : ∀ i, σ i ∉ s := fun i hi => by
    have hT' : σ i ∈ Set.range e := by
      rw [T.range_orderEmbOfFin hT]; exact Finset.mem_coe.mpr (mem_insert_of_mem hi)
    obtain ⟨j, hj⟩ := hT'
    have h1 : i.castSucc < j := e.lt_iff_lt.mp (hj ▸ (hσ i).1)
    have h2 : j < i.succ := e.lt_iff_lt.mp (hj ▸ (hσ i).2)
    rw [Fin.lt_def] at h1 h2
    simp at h1 h2
    omega
  -- the `2n` zeros of `g′`
  set Z := s ∪ univ.image σ
  have hZ : #Z = (2 * n - 1) + 1 := by
    rw [card_union_of_disjoint (disjoint_left.mpr fun x hx hx' => by
      obtain ⟨i, -, rfl⟩ := mem_image.mp hx'; exact hσs i hx),
      Finset.card_image_of_injective _ hσmono.injective, card_univ, Fintype.card_fin]
    omega
  set e' := Z.orderEmbOfFin hZ
  have he'Z : ∀ i, e' i ∈ Z := Z.orderEmbOfFin_mem hZ
  have he'J : ∀ i, e' i ∈ J := fun i => by
    rcases mem_union.mp (he'Z i) with h | h
    · exact hsJ _ h
    · obtain ⟨j, -, hj⟩ := mem_image.mp h; rw [← hj]; exact hσJ j
  have hz' : ∀ i, deriv g (e' i) = 0 := fun i => by
    rcases mem_union.mp (he'Z i) with h | h
    · exact hg's _ h
    · obtain ⟨j, -, hj⟩ := mem_image.mp h; rw [← hj]; exact hσ0 j
  have hEq := iteratedDeriv_sub_poly_eqOn hU Q (2 * n) hd
  have hdiff : ∀ k < 2 * n - 1, DifferentiableOn ℝ (iteratedDeriv k (deriv g)) U := by
    intro k hk
    rw [← iteratedDeriv_succ']
    exact ((hd (k + 1) (by omega)).sub (derivative^[k + 1] Q).differentiable.differentiableOn).congr
      (hEq (k + 1) (by omega))
  have hsub : Icc (e' 0) (e' (Fin.last _)) ⊆ U := (hJ.out (he'J _) (he'J _)).trans hJU
  obtain ⟨ξ, hξ, hξ0⟩ :=
    exists_iteratedDeriv_eq_zero (2 * n - 1) (deriv g) U hdiff e' e'.strictMono hsub hz'
  have hξJ : ξ ∈ J := hJ.out (he'J _) (he'J _) hξ
  rw [← iteratedDeriv_succ', show 2 * n - 1 + 1 = 2 * n by omega,
    hEq (2 * n) le_rfl (hJU hξJ)] at hξ0
  have hQ : derivative^[2 * n] Q = C (K * (2 * n).factorial) := by
    have hωω : (ω * ω).Monic := (Lagrange.nodal_monic).mul Lagrange.nodal_monic
    have hωdeg : (ω * ω).natDegree = 2 * n := by
      rw [natDegree_mul Lagrange.nodal_monic.ne_zero Lagrange.nodal_monic.ne_zero,
        Lagrange.natDegree_nodal]
      ring
    rw [iterate_map_add, iterate_derivative_eq_zero
      ((natDegree_hermite_le hs f (deriv f)).trans_lt (by omega)), zero_add,
      iterate_derivative_C_mul, ← hωdeg, iterate_derivative_monic_natDegree hωω, hωdeg, ← C_mul]
  simp only [hQ, eval_C] at hξ0
  rw [sub_eq_zero] at hξ0
  refine ⟨ξ, hξJ, ?_⟩
  rw [hξ0]
  have hfac : ((2 * n).factorial : ℝ) ≠ 0 := by positivity
  simp only [K]
  field_simp

/-- A nonnegative integrable function with zero integral over `(a, b)` vanishes at some point of
`(a, b)` outside any given finite set. -/
theorem exists_mem_Ioo_notMem_eq_zero {a b : ℝ} (hab : a < b) {g : ℝ → ℝ}
    (hg : IntegrableOn g (Ioo a b)) (hnn : ∀ x ∈ Ioo a b, 0 ≤ g x)
    (h0 : ∫ x in Ioo a b, g x = 0) (s : Finset ℝ) : ∃ t ∈ Ioo a b, t ∉ s ∧ g t = 0 := by
  by_contra h
  push Not at h
  have hf : 0 ≤ᵐ[volume.restrict (Ioo a b)] g :=
    (ae_restrict_iff' measurableSet_Ioo).mpr (Filter.Eventually.of_forall hnn)
  have hpos : 0 < ∫ x in Ioo a b, g x := by
    rw [setIntegral_pos_iff_support_of_nonneg_ae hf hg]
    have hZ : volume (s : Set ℝ) = 0 := (Finset.finite_toSet _).measure_zero _
    calc 0 < volume (Ioo a b) := by simp [hab]
      _ = volume (Ioo a b \ (s : Set ℝ)) := (measure_sdiff_null hZ).symm
      _ ≤ volume (Function.support g ∩ Ioo a b) :=
          measure_mono fun x hx => ⟨h x hx.1 hx.2, hx.1⟩
  linarith

/-- **DLMF 3.5.19–3.5.20**: on a finite interval `(a, b)`, for `f ∈ C^{2n}` on an open set
containing `[a, b]`, `E_n(f) = γ_n f^{(2n)}(ξ)/(2n)!` with `γ_n = ∫ₐᵇ p_n² w` and `ξ ∈ (a, b)`. -/
theorem dlmf_3_5_19 {a b : ℝ} (hab : a < b) {w : ℝ → ℝ} (hw : IsGaussWeight (Ioo a b) w)
    {n : ℕ} (hn : 0 < n) {p : ℝ[X]} (hp : IsOrthMonic (Ioo a b) w n p) {f : ℝ → ℝ}
    {U : Set ℝ} (hU : IsOpen U) (hIU : Icc a b ⊆ U) (hf : ContDiffOn ℝ (2 * n : ℕ) f U) :
    ∃ ξ ∈ Ioo a b, (∫ x in Ioo a b, f x * w x) -
      ∑ k ∈ p.roots.toFinset, christoffel (Ioo a b) w p k * f k =
        gaussGamma (Ioo a b) w p * iteratedDeriv (2 * n) f ξ / (2 * n).factorial := by
  classical
  set s := p.roots.toFinset
  obtain ⟨hnodup, hcard, hroots⟩ := hp.roots_spec hw
  have hs : #s = n := by rw [Multiset.toFinset_card_of_nodup hnodup, hcard]
  have hsne : s.Nonempty := card_pos.mp (hs ▸ hn)
  have hsI : ∀ x ∈ s, x ∈ Ioo a b := fun x hx => hroots x (Multiset.mem_toFinset.mp hx)
  have hpω : p = Lagrange.nodal s id := hp.eq_nodal hw
  rw [← hs] at hf ⊢
  set H := hermite s f (deriv f)
  set A : ℝ := ((2 * #s).factorial : ℝ)
  have hA : 0 < A := by positivity
  have hHdeg : H.degree < (2 * n : ℕ) := by
    refine degree_le_natDegree.trans_lt ?_
    have h1 := natDegree_hermite_le hsne f (deriv f)
    have h2 : 2 * #s - 1 < 2 * n := by rw [hs]; omega
    exact_mod_cast h1.trans_lt h2
  have hsum : ∑ k ∈ s, christoffel (Ioo a b) w p k * f k = wInt (Ioo a b) w H := by
    rw [dlmf_3_5_20_1 hw hp hHdeg]
    exact sum_congr rfl fun k hk => by rw [hermite_eval _ _ hk]
  have hwI : IntegrableOn w (Ioo a b) := by simpa using hw.integrableOn 0
  have hint : ∀ φ : ℝ → ℝ, ContinuousOn φ (Icc a b) →
      IntegrableOn (fun x => φ x * w x) (Ioo a b) := fun φ hφ =>
    hwI.continuousOn_mul_of_subset hφ isCompact_Icc measurableSet_Ioo Ioo_subset_Icc_self
  have hfc : ContinuousOn f (Icc a b) :=
    ((differentiableOn_iteratedDeriv_of_contDiffOn hU hf 0 (by omega)).continuousOn.mono
      hIU).congr fun x _ => by simp
  have hHc : ContinuousOn (fun x => f x - H.eval x) (Icc a b) :=
    hfc.sub H.continuous.continuousOn
  set E := ∫ x in Ioo a b, (f x - H.eval x) * w x
  have hE : (∫ x in Ioo a b, f x * w x) - ∑ k ∈ s, christoffel (Ioo a b) w p k * f k = E := by
    rw [hsum, wInt, ← integral_sub (hint f hfc) (hint _ H.continuous.continuousOn)]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => by simp only; ring)
  rw [hE]
  set γ := gaussGamma (Ioo a b) w p
  have hγ : 0 < γ := wInt_mul_self_pos hw hp.1.ne_zero
  have hγint : ∀ c : ℝ, ∫ x in Ioo a b, (c * p.eval x ^ 2) * w x = c * γ := fun c => by
    rw [show γ = ∫ x in Ioo a b, (p * p).eval x * w x from rfl, ← integral_const_mul]
    congr 1; ext x; rw [eval_mul]; ring
  set F := iteratedDeriv (2 * #s) f
  have hFc : ContinuousOn F (Icc a b) :=
    (continuousOn_iteratedDeriv_top_of_contDiffOn hU hf).mono hIU
  obtain ⟨u, hu, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr hab.le) hFc
  obtain ⟨v, hv, hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr hab.le) hFc
  -- pointwise error with `ξ ∈ [a, b]`
  have hpt : ∀ t ∈ Icc a b, F u / A * p.eval t ^ 2 ≤ f t - H.eval t ∧
      f t - H.eval t ≤ F v / A * p.eval t ^ 2 := fun t ht => by
    obtain ⟨ξ, hξ, he⟩ := hermite_error hsne hU hf ordConnected_Icc hIU
      (fun x hx => Ioo_subset_Icc_self (hsI x hx)) ht
    rw [he, ← hpω]
    have h1 : F u ≤ F ξ := hmin hξ
    have h2 : F ξ ≤ F v := hmax hξ
    have hsq : 0 ≤ p.eval t ^ 2 := sq_nonneg _
    constructor
    · exact mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right h1 hA.le) hsq
    · exact mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right h2 hA.le) hsq
  have hpc : ∀ c : ℝ, ContinuousOn (fun x => c * p.eval x ^ 2) (Icc a b) := fun c =>
    (continuous_const.mul ((p.continuous).pow 2)).continuousOn
  have hlow : F u / A * γ ≤ E := by
    rw [← hγint]
    refine setIntegral_mono_on (hint _ (hpc _)) (hint _ hHc) measurableSet_Ioo fun t ht => ?_
    exact mul_le_mul_of_nonneg_right (hpt t (Ioo_subset_Icc_self ht)).1 (hw.pos t ht).le
  have hupp : E ≤ F v / A * γ := by
    rw [← hγint]
    refine setIntegral_mono_on (hint _ hHc) (hint _ (hpc _)) measurableSet_Ioo fun t ht => ?_
    exact mul_le_mul_of_nonneg_right (hpt t (Ioo_subset_Icc_self ht)).2 (hw.pos t ht).le
  set c := E * A / γ
  have hc : E = γ * c / A := by simp only [c]; field_simp
  have hcu : F u ≤ c := by
    simp only [c]; rw [le_div_iff₀ hγ]
    have := mul_le_mul_of_nonneg_right hlow hA.le
    calc F u * γ = F u / A * γ * A := by field_simp
      _ ≤ E * A := this
  have hcv : c ≤ F v := by
    simp only [c]; rw [div_le_iff₀ hγ]
    have := mul_le_mul_of_nonneg_right hupp hA.le
    calc E * A ≤ F v / A * γ * A := this
      _ = F v * γ := by field_simp
  -- the equality cases: the pointwise identity holds at some non-node `t ∈ (a, b)`
  have hext : ∀ d : ℝ, (∀ t ∈ Ioo a b, t ∉ s → f t - H.eval t = d / A * p.eval t ^ 2 →
      ∃ ξ ∈ Ioo a b, F ξ = d) := fun d t ht hts hteq => by
    obtain ⟨ξ, hξ, he⟩ := hermite_error hsne hU hf ordConnected_Ioo (Ioo_subset_Icc_self.trans hIU)
      hsI ht
    rw [← hpω, hteq] at he
    have hpt0 : p.eval t ≠ 0 := by
      rw [hpω, Lagrange.eval_nodal]
      exact prod_ne_zero_iff.mpr fun k hk => sub_ne_zero.mpr fun h => hts (h ▸ hk)
    refine ⟨ξ, hξ, ?_⟩
    have := mul_right_cancel₀ (pow_ne_zero 2 hpt0) he
    field_simp at this
    rw [show ((2 * #s).factorial : ℝ) = A from rfl] at this
    apply mul_left_cancel₀ hA.ne'
    linarith [this]
  obtain ⟨ξ, hξ, hFξ⟩ : ∃ ξ ∈ Ioo a b, F ξ = c := by
    rcases hcu.lt_or_eq with hcu' | hcu'
    · rcases hcv.lt_or_eq with hcv' | hcv'
      · rcases le_total u v with huv | hvu
        · obtain ⟨ξ, hξ, hFξ⟩ := intermediate_value_Ioo huv (hFc.mono (Icc_subset_Icc hu.1 hv.2))
            ⟨hcu', hcv'⟩
          exact ⟨ξ, ⟨hu.1.trans_lt hξ.1, hξ.2.trans_le hv.2⟩, hFξ⟩
        · obtain ⟨ξ, hξ, hFξ⟩ := intermediate_value_Ioo' hvu (hFc.mono (Icc_subset_Icc hv.1 hu.2))
            ⟨hcu', hcv'⟩
          exact ⟨ξ, ⟨hv.1.trans_lt hξ.1, hξ.2.trans_le hu.2⟩, hFξ⟩
      · -- `c = F v`
        obtain ⟨t, ht, hts, h0⟩ := exists_mem_Ioo_notMem_eq_zero hab
          (hint _ ((hpc (F v / A)).sub hHc))
          (fun t ht => mul_nonneg (sub_nonneg.mpr (hpt t (Ioo_subset_Icc_self ht)).2)
            (hw.pos t ht).le)
          (by
            rw [integral_congr_ae (g := fun x => F v / A * p.eval x ^ 2 * w x -
              (f x - H.eval x) * w x) (Filter.Eventually.of_forall fun x => by
                simp only [Pi.sub_apply]; ring),
              integral_sub (hint _ (hpc _)) (hint _ hHc), hγint, ← hcv']
            change c / A * γ - E = 0
            rw [hc]
            field_simp
            ring)
          s
        have := (mul_eq_zero.mp h0).resolve_right (hw.pos t ht).ne'
        simp only [Pi.sub_apply] at this
        exact hext c t ht hts (by rw [hcv']; linarith)
    · -- `c = F u`
      obtain ⟨t, ht, hts, h0⟩ := exists_mem_Ioo_notMem_eq_zero hab
        (hint _ (hHc.sub (hpc (F u / A))))
        (fun t ht => mul_nonneg (sub_nonneg.mpr (hpt t (Ioo_subset_Icc_self ht)).1)
          (hw.pos t ht).le)
        (by
          rw [integral_congr_ae (g := fun x => (f x - H.eval x) * w x -
            F u / A * p.eval x ^ 2 * w x) (Filter.Eventually.of_forall fun x => by
              simp only [Pi.sub_apply]; ring),
            integral_sub (hint _ hHc) (hint _ (hpc _)), hγint, hcu']
          change E - c / A * γ = 0
          rw [hc]
          field_simp
          ring)
        s
      have := (mul_eq_zero.mp h0).resolve_right (hw.pos t ht).ne'
      simp only [Pi.sub_apply] at this
      exact hext c t ht hts (by rw [← hcu']; linarith)
  refine ⟨ξ, hξ, ?_⟩
  rw [hc, hFξ]

end Azurite.DLMF
