/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter3.Section3Divided
import Azurite.DLMF.Chapter3.Section3Equal

/-!
# DLMF §3.4(i): numerical differentiation with equally-spaced nodes

Nodes `x_k = x₀ + kh` as in §3.3(ii) (`eqNode`), `R_n` the remainder of §3.3(i)
(`lagrangeRem`), `R′_{n,t} = R_n′(x₀ + th)`.

* 3.4.2: `lagCoeffD` (`B_k^n = dA_k^n/dt`, of the polynomial form `lagCoeff'` of 3.3.10),
  `dlmf_3_4_2` (the same as the derivative of DLMF's `A_k^n` off the node `t = k`).
* 3.4.1: `dlmf_3_4_1`, by differentiating `P_n(x₀ + th) = ∑ A_k^n f_k` (3.3.7) in `t`.
* 3.4.3 (corrected; see `docs/dlmf_errata.md`): `dlmf_3_4_3`, from the general
  `hasDerivAt_lagrangeRem_mean`: for nodes in `[lo, hi]` and `x ∈ (lo, hi)`,
  `R_n′(x) = ω′(x) f^{(n+1)}(ξ₀)/(n+1)! + ω(x) f^{(n+2)}(ξ₁)/(n+2)!`. Proof: `R_n = ω G` with
  `G(y) = [z₀, …, z_n, y] f` (`remG`, `lagrangeRem_eq_nodal_mul_remG`); off the nodes `G` is
  differentiable, `G(x) = f^{(n+1)}(ξ₀)/(n+1)!` and every difference quotient of `G` is a divided
  difference of order `n + 2` (`remG_slope`), i.e. a value of `f^{(n+2)}/(n+2)!` on `[lo, hi]`, so
  the limit `G′(x)` lies in that compact image; at a node `x`, `G(y) = (R(y)/(y − x))/(ω(y)/(y − x))
  → R′(x)/ω′(x)` lies in the compact image of `f^{(n+1)}/(n+1)!`. `dlmf_3_4_3_erratum`: DLMF's
  formula fails for `f(x) = x³`, `n = 1`, `h = 1`, `t = ½`.
* 3.4.4 (corrected): `dlmf_3_4_4`, from `|(d/dt) ∏_{k=n₀}^{n₁} (t − k)| ≤ n!` on `[n₀, n₁]`
  (`abs_deriv_prod_Icc_eqN_le`; equality at the end points). Proof by induction on `n` for
  `p_n(t) = ∏_{k=0}^{n} (t − k)` (`fallProd`), with `p_{n+1}(t) = p_n(t)(t − n − 1)` for `t ≤ n`
  and `p_{n+1}(t) = t p_n(t − 1)` for `t ≥ 1`, and the bound `|∏_{k=0}^{m−1} (t − k)| ≤ m!` on
  `[−1, m]` (`abs_fallProd_le`).
-/

open Polynomial Finset Lagrange Filter Topology

namespace Azurite.DLMF

/-! ### The derivative of the interpolation remainder (general nodes) -/

/-- A polynomial of degree `≤ m + 1` vanishing at `m + 1` distinct points is a multiple of their
nodal polynomial. -/
theorem eq_C_mul_nodal {m : ℕ} (v : Fin (m + 1) → ℝ) (hv : Function.Injective v) (S : ℝ[X])
    (hS : S.natDegree ≤ m + 1) (h0 : ∀ i, S.eval (v i) = 0) :
    S = C (S.coeff (m + 1)) * nodal univ v := by
  have hωdeg : (nodal univ v).natDegree = m + 1 := by
    rw [natDegree_nodal, card_univ, Fintype.card_fin]
  have hlead := (nodal_monic (s := univ) (v := v)).coeff_natDegree
  rw [hωdeg] at hlead
  rw [← sub_eq_zero]
  refine eq_zero_of_natDegree_lt_card_of_eval_eq_zero _ hv (fun i => ?_) ?_
  · rw [eval_sub, eval_mul, eval_C, h0, eval_nodal_at_node (mem_univ i), mul_zero, sub_zero]
  · rw [Fintype.card_fin]
    have : (S - C (S.coeff (m + 1)) * nodal univ v).natDegree ≤ m :=
      natDegree_le_iff_coeff_eq_zero.mpr fun N hN => by
        rcases (show N = m + 1 ∨ m + 1 < N by omega) with rfl | h
        · rw [coeff_sub, coeff_C_mul, hlead, mul_one, sub_self]
        · rw [coeff_sub, coeff_C_mul, coeff_eq_zero_of_natDegree_lt (by omega),
            coeff_eq_zero_of_natDegree_lt (by omega : (nodal univ v).natDegree < N)]
          ring
    omega

theorem snoc_injective {n : ℕ} {z : Fin (n + 1) → ℝ} (hz : Function.Injective z) {y : ℝ}
    (hy : ∀ i, z i ≠ y) : Function.Injective (Fin.snoc z y : Fin (n + 2) → ℝ) := by
  intro i j h
  induction i using Fin.lastCases with
  | last =>
    induction j using Fin.lastCases with
    | last => rfl
    | cast j => simp only [Fin.snoc_last, Fin.snoc_castSucc] at h; exact absurd h.symm (hy j)
  | cast i =>
    induction j using Fin.lastCases with
    | last => simp only [Fin.snoc_last, Fin.snoc_castSucc] at h; exact absurd h (hy i)
    | cast j => simp only [Fin.snoc_castSucc] at h; rw [hz h]

theorem nodal_snoc {n : ℕ} (z : Fin (n + 1) → ℝ) (y : ℝ) :
    nodal univ (Fin.snoc z y : Fin (n + 2) → ℝ) = nodal univ z * (X - C y) := by
  simp only [nodal, Fin.prod_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last]

/-- `G(y) = [z₀, …, z_n, y] f`, the leading coefficient of the interpolant at the nodes and `y`. -/
noncomputable def remG {n : ℕ} (z : Fin (n + 1) → ℝ) (f : ℝ → ℝ) (y : ℝ) : ℝ :=
  (interpolate univ (Fin.snoc z y : Fin (n + 2) → ℝ)
    fun k => f ((Fin.snoc z y : Fin (n + 2) → ℝ) k)).coeff (n + 1)

/-- `R_n(y) = ω_{n+1}(y) [z₀, …, z_n, y] f`. -/
theorem lagrangeRem_eq_nodal_mul_remG {n : ℕ} (z : Fin (n + 1) → ℝ) (hz : Function.Injective z)
    (f : ℝ → ℝ) (y : ℝ) : lagrangeRem z f y = (nodal univ z).eval y * remG z f y := by
  obtain ⟨hPdeg, hPev, -⟩ := lagrange_unique z hz fun k => f (z k)
  by_cases hy : ∃ j, z j = y
  · obtain ⟨j, rfl⟩ := hy
    rw [lagrangeRem, hPev j, sub_self, eval_nodal_at_node (mem_univ j), zero_mul]
  push Not at hy
  have hw := snoc_injective hz hy
  obtain ⟨hQdeg, hQev, -⟩ :=
    lagrange_unique _ hw fun k => f ((Fin.snoc z y : Fin (n + 2) → ℝ) k)
  set Q := interpolate univ (Fin.snoc z y : Fin (n + 2) → ℝ)
    fun k => f ((Fin.snoc z y : Fin (n + 2) → ℝ) k)
  set P := interpolate univ z fun k => f (z k)
  have hS := eq_C_mul_nodal z hz (Q - P) ((natDegree_sub_le _ _).trans (max_le hQdeg (by omega)))
    fun i => by
      have h1 := hQev i.castSucc
      simp only [Fin.snoc_castSucc] at h1
      rw [eval_sub, h1, hPev i, sub_self]
  have hc : (Q - P).coeff (n + 1) = remG z f y := by
    rw [coeff_sub, coeff_eq_zero_of_natDegree_lt (by omega : P.natDegree < n + 1), sub_zero]; rfl
  have := congrArg (eval y) hS
  have hQy := hQev (Fin.last (n + 1))
  simp only [Fin.snoc_last] at hQy
  rw [eval_sub, hQy, eval_mul, eval_C, hc] at this
  rw [lagrangeRem, this, mul_comm]

/-- The difference quotient of `G` is a divided difference of order `n + 2`:
`(G(y) − G(x))/(y − x) = [z₀, …, z_n, x, y] f`. -/
theorem remG_slope {n : ℕ} (z : Fin (n + 1) → ℝ) (hz : Function.Injective z) (f : ℝ → ℝ)
    {x y : ℝ} (hx : ∀ i, z i ≠ x) (hy : ∀ i, z i ≠ y) (hxy : x ≠ y) :
    (remG z f y - remG z f x) / (y - x) =
      divDiff (n + 2) (Fin.snoc (Fin.snoc z x : Fin (n + 2) → ℝ) y : Fin (n + 3) → ℝ) f := by
  have hzx := snoc_injective hz hx
  have hzy := snoc_injective hz hy
  have hw := snoc_injective hzx (y := y) fun i => by
    induction i using Fin.lastCases with
    | last => simp only [Fin.snoc_last]; exact hxy
    | cast i => simp only [Fin.snoc_castSucc]; exact hy i
  set w : Fin (n + 3) → ℝ := Fin.snoc (Fin.snoc z x : Fin (n + 2) → ℝ) y
  obtain ⟨hTdeg, hTev, -⟩ := lagrange_unique w hw fun k => f (w k)
  obtain ⟨hxdeg, hxev, -⟩ :=
    lagrange_unique _ hzx fun k => f ((Fin.snoc z x : Fin (n + 2) → ℝ) k)
  obtain ⟨hydeg, hyev, -⟩ :=
    lagrange_unique _ hzy fun k => f ((Fin.snoc z y : Fin (n + 2) → ℝ) k)
  set T := interpolate univ w fun k => f (w k)
  set Qx := interpolate univ (Fin.snoc z x : Fin (n + 2) → ℝ)
    fun k => f ((Fin.snoc z x : Fin (n + 2) → ℝ) k)
  set Qy := interpolate univ (Fin.snoc z y : Fin (n + 2) → ℝ)
    fun k => f ((Fin.snoc z y : Fin (n + 2) → ℝ) k)
  have hdeg : ∀ Q : ℝ[X], Q.natDegree ≤ n + 1 → (T - Q).natDegree ≤ n + 2 := fun Q hQ =>
    (natDegree_sub_le _ _).trans (max_le hTdeg (by omega))
  have hcT : ∀ Q : ℝ[X], Q.natDegree ≤ n + 1 → (T - Q).coeff (n + 2) = T.coeff (n + 2) :=
    fun Q hQ => by
      rw [coeff_sub, coeff_eq_zero_of_natDegree_lt (p := Q) (by omega), sub_zero]
  have h1 := eq_C_mul_nodal _ hzx (T - Qx) (hdeg Qx hxdeg) fun i => by
    have := hTev i.castSucc
    simp only [w, Fin.snoc_castSucc] at this
    rw [eval_sub, this, hxev i, sub_self]
  have h2 := eq_C_mul_nodal _ hzy (T - Qy) (hdeg Qy hydeg) fun i => by
    rw [eval_sub, hyev i]
    induction i using Fin.lastCases with
    | last =>
      have := hTev (Fin.last (n + 2))
      simp only [w, Fin.snoc_last] at this ⊢
      rw [this, sub_self]
    | cast i =>
      have := hTev i.castSucc.castSucc
      simp only [w, Fin.snoc_castSucc] at this ⊢
      rw [this, sub_self]
  rw [hcT Qx hxdeg] at h1
  rw [hcT Qy hydeg] at h2
  have hdiff : Qy - Qx = C (T.coeff (n + 2) * (y - x)) * nodal univ z := by
    have : Qy - Qx = (T - Qx) - (T - Qy) := by ring
    rw [this, h1, h2, nodal_snoc, nodal_snoc, C_mul, map_sub]
    ring
  have hlead := (nodal_monic (s := univ) (v := z)).coeff_natDegree
  rw [natDegree_nodal, card_univ, Fintype.card_fin] at hlead
  have hco := congrArg (fun p => p.coeff (n + 1)) hdiff
  simp only [coeff_sub, coeff_C_mul, hlead, mul_one] at hco
  have hne : y - x ≠ 0 := sub_ne_zero.mpr hxy.symm
  rw [show remG z f y - remG z f x = Qy.coeff (n + 1) - Qx.coeff (n + 1) from rfl, hco,
    mul_div_assoc, div_self hne, mul_one, divDiff_eq_coeff w hw f]

/-- Mean value for a divided difference with all nodes in `[lo, hi]`. -/
theorem divDiff_mem_image {m : ℕ} (w : Fin (m + 1) → ℝ) (hw : Function.Injective w) (f : ℝ → ℝ)
    {U : Set ℝ} (hU : IsOpen U) (hd : ∀ k < m, DifferentiableOn ℝ (iteratedDeriv k f) U)
    {lo hi : ℝ} (hI : Set.Icc lo hi ⊆ U) (hmem : ∀ i, w i ∈ Set.Icc lo hi) :
    divDiff m w f ∈ (fun u => iteratedDeriv m f u / m.factorial) '' Set.Icc lo hi := by
  have hsub : Set.Icc ((univ.image w).min' (univ_nonempty.image w))
      ((univ.image w).max' (univ_nonempty.image w)) ⊆ Set.Icc lo hi := by
    apply Set.Icc_subset_Icc
    · exact (univ.image w).le_min' _ _ fun a ha => by
        obtain ⟨i, -, rfl⟩ := mem_image.mp ha; exact (hmem i).1
    · exact (univ.image w).max'_le _ _ fun a ha => by
        obtain ⟨i, -, rfl⟩ := mem_image.mp ha; exact (hmem i).2
  obtain ⟨η, hη, h⟩ := dlmf_3_3_36 w hw f hU hd (hsub.trans hI)
  exact ⟨η, hsub hη, h.symm⟩

theorem snoc_mem {m : ℕ} {v : Fin (m + 1) → ℝ} {a : ℝ} {T : Set ℝ} (hv : ∀ i, v i ∈ T)
    (ha : a ∈ T) : ∀ i, (Fin.snoc v a : Fin (m + 2) → ℝ) i ∈ T := fun i => by
  induction i using Fin.lastCases with
  | last => simp only [Fin.snoc_last]; exact ha
  | cast i => simp only [Fin.snoc_castSucc]; exact hv i

/-- **The derivative of the interpolation remainder** (general nodes `z_k ∈ [lo, hi]`, `x` inside):
`R_n′(x) = ω′_{n+1}(x) f^{(n+1)}(ξ₀)/(n+1)! + ω_{n+1}(x) f^{(n+2)}(ξ₁)/(n+2)!` with
`ξ₀, ξ₁ ∈ [lo, hi]`, for `f` that is `n + 2` times differentiable near `[lo, hi]` with
`f^{(n+2)}` continuous on `[lo, hi]`. -/
theorem hasDerivAt_lagrangeRem_mean {n : ℕ} (z : Fin (n + 1) → ℝ) (hz : Function.Injective z)
    (f : ℝ → ℝ) {U : Set ℝ} (hU : IsOpen U)
    (hd : ∀ k ≤ n + 1, DifferentiableOn ℝ (iteratedDeriv k f) U) {lo hi : ℝ}
    (hI : Set.Icc lo hi ⊆ U) (hmem : ∀ i, z i ∈ Set.Icc lo hi)
    (hc : ContinuousOn (iteratedDeriv (n + 2) f) (Set.Icc lo hi)) {x : ℝ}
    (hx : x ∈ Set.Ioo lo hi) :
    ∃ ξ₀ ∈ Set.Icc lo hi, ∃ ξ₁ ∈ Set.Icc lo hi,
      HasDerivAt (lagrangeRem z f)
        ((derivative (nodal univ z)).eval x * (iteratedDeriv (n + 1) f ξ₀ / (n + 1).factorial) +
          (nodal univ z).eval x * (iteratedDeriv (n + 2) f ξ₁ / (n + 2).factorial)) x := by
  set ω := nodal univ z
  set G := remG z f
  set P := interpolate univ z fun k => f (z k)
  have hxI : x ∈ Set.Icc lo hi := Set.Ioo_subset_Icc_self hx
  have hfd : DifferentiableAt ℝ f x := by
    simpa using (hd 0 (by omega)).differentiableAt (hU.mem_nhds (hI hxI))
  have hR : HasDerivAt (lagrangeRem z f) (deriv f x - (derivative P).eval x) x :=
    hfd.hasDerivAt.sub (Polynomial.hasDerivAt P x)
  have hRG : ∀ y, lagrangeRem z f y = ω.eval y * G y := lagrangeRem_eq_nodal_mul_remG z hz f
  have hK1 : IsClosed ((fun u => iteratedDeriv (n + 1) f u / (n + 1).factorial) '' Set.Icc lo hi) :=
    (isCompact_Icc.image_of_continuousOn
      (((hd (n + 1) le_rfl).continuousOn.mono hI).div_const _)).isClosed
  have hK2 : IsClosed ((fun u => iteratedDeriv (n + 2) f u / (n + 2).factorial) '' Set.Icc lo hi) :=
    (isCompact_Icc.image_of_continuousOn (hc.div_const _)).isClosed
  have hGmem : ∀ y ∈ Set.Icc lo hi, (∀ i, z i ≠ y) →
      G y ∈ (fun u => iteratedDeriv (n + 1) f u / (n + 1).factorial) '' Set.Icc lo hi :=
    fun y hy hyn => by
      have hw := snoc_injective hz hyn
      have := divDiff_mem_image _ hw f hU (fun k hk => hd k (by omega)) hI (snoc_mem hmem hy)
      rwa [divDiff_eq_coeff _ hw] at this
  -- points near `x`, other than `x`, are inside `(lo, hi)` and are not nodes
  have hev : ∀ᶠ y in 𝓝[≠] x, y ∈ Set.Ioo lo hi ∧ (∀ i, z i ≠ y) ∧ x ≠ y := by
    have h1 : ∀ᶠ y in 𝓝[≠] x, y ∈ Set.Ioo lo hi :=
      nhdsWithin_le_nhds (Ioo_mem_nhds hx.1 hx.2)
    have hfin : (Set.range z \ {x}).Finite := (Set.finite_range z).sdiff
    have h2 : ∀ᶠ y in 𝓝[≠] x, y ∉ Set.range z \ {x} :=
      nhdsWithin_le_nhds (hfin.isClosed.compl_mem_nhds (fun h => h.2 rfl))
    have h3 : ∀ᶠ y in 𝓝[≠] x, y ∈ ({x}ᶜ : Set ℝ) := self_mem_nhdsWithin
    filter_upwards [h1, h2, h3] with y hy1 hy2 hy3
    refine ⟨hy1, fun i hi => hy2 ⟨⟨i, hi⟩, hy3⟩, fun h => hy3 h.symm⟩
  by_cases hxn : ∃ j, z j = x
  · -- `x` is a node: `ω(x) = 0`
    obtain ⟨j, hj⟩ := hxn
    have hω0 : ω.eval x = 0 := by rw [← hj]; exact eval_nodal_at_node (mem_univ j)
    have hω' : (derivative ω).eval x ≠ 0 := by
      rw [← hj, eval_nodal_derivative_eval_node_eq (mem_univ j), eval_nodal]
      exact prod_ne_zero_iff.mpr fun i hi =>
        sub_ne_zero.mpr fun h => (mem_erase.mp hi).1 (hz h).symm
    have hR0 : lagrangeRem z f x = 0 := by rw [hRG, hω0, zero_mul]
    have tR := hasDerivAt_iff_tendsto_slope.mp hR
    have tω := hasDerivAt_iff_tendsto_slope.mp (Polynomial.hasDerivAt ω x)
    have hGlim : Tendsto G (𝓝[≠] x)
        (𝓝 ((deriv f x - (derivative P).eval x) / (derivative ω).eval x)) := by
      refine (tR.div tω hω').congr' ?_
      filter_upwards [hev, tω.eventually_ne hω'] with y hy hne
      simp only [Pi.div_apply]
      rw [slope_def_field, hω0, sub_zero] at hne
      rw [slope_def_field, slope_def_field, hR0, hω0, sub_zero, sub_zero, hRG]
      have hyx : y - x ≠ 0 := sub_ne_zero.mpr hy.2.2.symm
      have hωy : ω.eval y ≠ 0 := fun h => hne (by rw [h, zero_div])
      field_simp
    have hmem1 := hK1.mem_of_tendsto hGlim (hev.mono fun y hy =>
      hGmem y (Set.Ioo_subset_Icc_self hy.1) hy.2.1)
    obtain ⟨ξ₀, hξ₀, hval⟩ := hmem1
    simp only at hval
    refine ⟨ξ₀, hξ₀, x, hxI, ?_⟩
    convert hR using 1
    rw [hval, hω0, zero_mul, add_zero]
    field_simp
  · -- `x` is not a node: `G` is differentiable at `x` and `R = ω G`
    push Not at hxn
    have hωx : ω.eval x ≠ 0 := by
      rw [eval_nodal]; exact prod_ne_zero_iff.mpr fun i _ => sub_ne_zero.mpr (hxn i).symm
    have hωev : ∀ᶠ y in 𝓝 x, ω.eval y ≠ 0 :=
      (Polynomial.differentiable ω).continuous.continuousAt.eventually_ne hωx
    have hGeq : G =ᶠ[𝓝 x] fun y => lagrangeRem z f y / ω.eval y :=
      hωev.mono fun y hy => by
        show G y = lagrangeRem z f y / ω.eval y
        rw [hRG, mul_div_cancel_left₀ _ hy]
    obtain ⟨g', hg'⟩ : ∃ g', HasDerivAt G g' x :=
      ⟨_, (hR.div (Polynomial.hasDerivAt ω x) hωx).congr_of_eventuallyEq hGeq⟩
    have tG := hasDerivAt_iff_tendsto_slope.mp hg'
    have hmem2 := hK2.mem_of_tendsto tG (hev.mono fun y hy => by
      rw [slope_def_field, remG_slope z hz f hxn hy.2.1 hy.2.2]
      exact divDiff_mem_image _ (snoc_injective (snoc_injective hz hxn) fun i => by
          induction i using Fin.lastCases with
          | last => simp only [Fin.snoc_last]; exact hy.2.2
          | cast i => simp only [Fin.snoc_castSucc]; exact hy.2.1 i)
        f hU (fun k hk => hd k (by omega)) hI
        (snoc_mem (snoc_mem hmem hxI) (Set.Ioo_subset_Icc_self hy.1)))
    obtain ⟨ξ₁, hξ₁, hval1⟩ := hmem2
    obtain ⟨ξ₀, hξ₀, hval0⟩ := hGmem x hxI hxn
    simp only at hval0 hval1
    refine ⟨ξ₀, hξ₀, ξ₁, hξ₁, ?_⟩
    have hRfun : lagrangeRem z f = fun y => ω.eval y * G y := funext hRG
    rw [hRfun]
    convert (Polynomial.hasDerivAt ω x).mul hg' using 1
    rw [hval0, hval1]

/-! ### Equally-spaced nodes: 3.4.1–3.4.2 -/

/-- **DLMF 3.4.2**: the differentiated Lagrangian interpolation coefficients
`B_k^n = dA_k^n/dt` (of the coefficients `A_k^n` with the factor `t − k` cancelled, i.e. the
polynomial form of 3.3.10). -/
noncomputable def lagCoeffD (n : ℕ) (k : ℤ) (t : ℝ) : ℝ := deriv (lagCoeff' n k) t

theorem differentiable_lagCoeff' (n : ℕ) (k : ℤ) : Differentiable ℝ (lagCoeff' n k) := by
  unfold lagCoeff'; fun_prop

/-- **DLMF 3.4.2** with DLMF's `A_k^n` of 3.3.10, away from the node `t = k`. -/
theorem dlmf_3_4_2 {n : ℕ} {k : ℤ} (hk : k ∈ Icc (eqN0 n) (eqN1 n)) {t : ℝ} (ht : t ≠ k) :
    deriv (lagCoeff n k) t = lagCoeffD n k t := by
  refine Filter.EventuallyEq.deriv_eq ?_
  filter_upwards [isOpen_ne.mem_nhds ht] with s hs
  exact lagCoeff_eq hk hs

/-- **DLMF 3.4.1**: `h f′(x₀ + th) = ∑_{k=n₀}^{n₁} B_k^n f_k + h R′_{n,t}`, where
`R′_{n,t} = R_n′(x₀ + th)` is the derivative of the remainder of §3.3 (valid for every real `t`;
DLMF states `n₀ < t < n₁`). -/
theorem dlmf_3_4_1 {x₀ h : ℝ} (hh : h ≠ 0) (n : ℕ) (f : ℝ → ℝ) (t : ℝ)
    (hf : DifferentiableAt ℝ f (x₀ + t * h)) :
    h * deriv f (x₀ + t * h) = ∑ k ∈ Icc (eqN0 n) (eqN1 n), lagCoeffD n k t * f (x₀ + k * h) +
      h * deriv (lagrangeRem (eqNode x₀ h n) f) (x₀ + t * h) := by
  set P := interpolate univ (eqNode x₀ h n) fun k => f (eqNode x₀ h n k)
  have hP : (fun s => P.eval (x₀ + s * h)) =
      fun s => ∑ k ∈ Icc (eqN0 n) (eqN1 n), lagCoeff' n k s * f (x₀ + k * h) := funext fun s => by
    have := dlmf_3_3_7' (x₀ := x₀) hh n f s
    rw [lagrangeRem] at this
    linarith
  have h1 : HasDerivAt (fun s => P.eval (x₀ + s * h)) ((derivative P).eval (x₀ + t * h) * h) t := by
    have := (Polynomial.hasDerivAt P (x₀ + t * h)).comp t
      (((hasDerivAt_id t).mul_const h).const_add x₀)
    simp only [id, one_mul] at this
    exact this
  have h2 : HasDerivAt (fun s => ∑ k ∈ Icc (eqN0 n) (eqN1 n), lagCoeff' n k s * f (x₀ + k * h))
      (∑ k ∈ Icc (eqN0 n) (eqN1 n), lagCoeffD n k t * f (x₀ + k * h)) t :=
    HasDerivAt.fun_sum fun k _ =>
      ((differentiable_lagCoeff' n k) t).hasDerivAt.mul_const _
  rw [hP] at h1
  have hu := h1.unique h2
  have hR : deriv (lagrangeRem (eqNode x₀ h n) f) (x₀ + t * h) =
      deriv f (x₀ + t * h) - (derivative P).eval (x₀ + t * h) :=
    (hf.hasDerivAt.sub (Polynomial.hasDerivAt P _)).deriv
  rw [hR, ← hu]
  ring

/-! ### The remainder 3.4.3–3.4.4 -/

theorem eqNode_mem_Icc {x₀ h : ℝ} (hh : 0 < h) (n : ℕ) (j : Fin (n + 1)) :
    eqNode x₀ h n j ∈ Set.Icc (x₀ + eqN0 n * h) (x₀ + eqN1 n * h) := by
  have hj : (j : ℕ) ≤ n := Nat.lt_succ_iff.mp j.2
  have h1 : (eqN0 n : ℝ) ≤ ((eqN0 n + (j : ℕ) : ℤ) : ℝ) := by
    exact_mod_cast (by omega : eqN0 n ≤ eqN0 n + (j : ℕ))
  have h2 : ((eqN0 n + (j : ℕ) : ℤ) : ℝ) ≤ (eqN1 n : ℝ) := by
    exact_mod_cast (by rw [eqN1_eq]; omega : eqN0 n + (j : ℕ) ≤ eqN1 n)
  constructor <;> simp only [eqNode] <;> nlinarith

/-- `h ω′_{n+1}(x₀ + th) = h^{n+1} (d/dt) ∏_{k=n₀}^{n₁} (t − k)`. -/
theorem eqNode_nodal_deriv {x₀ h : ℝ} (n : ℕ) (t : ℝ) :
    (derivative (nodal univ (eqNode x₀ h n))).eval (x₀ + t * h) * h =
      h ^ (n + 1) * deriv (fun s : ℝ => ∏ k ∈ Icc (eqN0 n) (eqN1 n), (s - k)) t := by
  have h1 := (Polynomial.hasDerivAt (nodal univ (eqNode x₀ h n)) (x₀ + t * h)).comp t
    (((hasDerivAt_id t).mul_const h).const_add x₀)
  have hfun : ((fun x => (nodal univ (eqNode x₀ h n)).eval x) ∘ fun s => x₀ + id s * h) =
      fun s : ℝ => h ^ (n + 1) * ∏ k ∈ Icc (eqN0 n) (eqN1 n), (s - k) :=
    funext fun s => by simp only [Function.comp, id]; exact eqNode_nodal_eval n s
  rw [hfun] at h1
  have hPi : DifferentiableAt ℝ (fun s : ℝ => ∏ k ∈ Icc (eqN0 n) (eqN1 n), (s - (k : ℝ))) t := by
    fun_prop
  have := h1.unique (hPi.hasDerivAt.const_mul (h ^ (n + 1)))
  simpa using this

/-- **DLMF 3.4.3** (corrected; see errata): for `n₀ < t < n₁` and `f` that is `n + 2` times
differentiable near `I = [x_{n₀}, x_{n₁}]` with `f^{(n+2)}` continuous on `I`,
`h R′_{n,t} = h^{n+1}/(n+1)! f^{(n+1)}(ξ₀) (d/dt) ∏ (t − k)
  + h^{n+2}/(n+2)! f^{(n+2)}(ξ₁) ∏ (t − k)`
with `ξ₀, ξ₁ ∈ I`. DLMF's second term lacks the factor `h/(n + 2)`. -/
theorem dlmf_3_4_3 {x₀ h : ℝ} (hh : 0 < h) (n : ℕ) (f : ℝ → ℝ) {U : Set ℝ} (hU : IsOpen U)
    (hd : ∀ k ≤ n + 1, DifferentiableOn ℝ (iteratedDeriv k f) U)
    (hI : Set.Icc (x₀ + eqN0 n * h) (x₀ + eqN1 n * h) ⊆ U)
    (hc : ContinuousOn (iteratedDeriv (n + 2) f) (Set.Icc (x₀ + eqN0 n * h) (x₀ + eqN1 n * h)))
    {t : ℝ} (ht : t ∈ Set.Ioo (eqN0 n : ℝ) (eqN1 n)) :
    ∃ ξ₀ ∈ Set.Icc (x₀ + eqN0 n * h) (x₀ + eqN1 n * h),
      ∃ ξ₁ ∈ Set.Icc (x₀ + eqN0 n * h) (x₀ + eqN1 n * h),
        h * deriv (lagrangeRem (eqNode x₀ h n) f) (x₀ + t * h) =
          h ^ (n + 1) / (n + 1).factorial * (iteratedDeriv (n + 1) f ξ₀ *
              deriv (fun s : ℝ => ∏ k ∈ Icc (eqN0 n) (eqN1 n), (s - k)) t) +
            h ^ (n + 2) / (n + 2).factorial * (iteratedDeriv (n + 2) f ξ₁ *
              ∏ k ∈ Icc (eqN0 n) (eqN1 n), (t - k)) := by
  have hx : x₀ + t * h ∈ Set.Ioo (x₀ + eqN0 n * h) (x₀ + eqN1 n * h) :=
    ⟨by nlinarith [mul_lt_mul_of_pos_right ht.1 hh], by nlinarith [mul_lt_mul_of_pos_right ht.2 hh]⟩
  obtain ⟨ξ₀, hξ₀, ξ₁, hξ₁, hD⟩ := hasDerivAt_lagrangeRem_mean (eqNode x₀ h n)
    (eqNode_injective hh.ne' n) f hU hd hI (eqNode_mem_Icc hh n) hc hx
  refine ⟨ξ₀, hξ₀, ξ₁, hξ₁, ?_⟩
  rw [hD.deriv]
  have ha := eqNode_nodal_eval (x₀ := x₀) (h := h) n t
  have hb := eqNode_nodal_deriv (x₀ := x₀) (h := h) n t
  linear_combination (iteratedDeriv (n + 1) f ξ₀ / (n + 1).factorial) * hb +
    (h * (iteratedDeriv (n + 2) f ξ₁ / (n + 2).factorial)) * ha

/-- **Erratum to 3.4.3**: DLMF's formula fails for `f(x) = x³`, `n = 1`, `x₀ = 0`, `h = 1`,
`t = ½`: `h R′_{1,1/2} = −¼`, while
`h²/2! (f″(ξ₀) (d/dt) t(t − 1) + f‴(ξ₁) t(t − 1)) = −¾` at `t = ½` for every `ξ₀, ξ₁`. -/
theorem dlmf_3_4_3_erratum :
    (1 : ℝ) * deriv (lagrangeRem (eqNode 0 1 1) fun x => x ^ 3) (0 + 1 / 2 * 1) = -1 / 4 ∧
      ∀ ξ₀ ξ₁ : ℝ, (1 : ℝ) ^ (1 + 1) / (1 + 1).factorial *
        (iteratedDeriv (1 + 1) (fun x : ℝ => x ^ 3) ξ₀ *
            deriv (fun s : ℝ => ∏ k ∈ Icc (eqN0 1) (eqN1 1), (s - k)) (1 / 2) +
          iteratedDeriv (1 + 2) (fun x : ℝ => x ^ 3) ξ₁ *
            ∏ k ∈ Icc (eqN0 1) (eqN1 1), ((1 / 2 : ℝ) - k)) = -3 / 4 := by
  have hR : lagrangeRem (eqNode 0 1 1) (fun x : ℝ => x ^ 3) = fun y => y ^ 3 - y :=
    funext fun y => by
      have := dlmf_3_3_14 (x₀ := 0) one_ne_zero (fun x : ℝ => x ^ 3) y
      simp only [zero_add, mul_one] at this
      norm_num at this
      linarith
  have d1 : deriv (fun x : ℝ => x ^ 3) = fun x => 3 * x ^ 2 := funext fun x => by simp
  have d2 : deriv (fun x : ℝ => 3 * x ^ 2) = fun x => 6 * x := funext fun x => by simp; ring
  have d3 : deriv (fun x : ℝ => 6 * x) = fun _ => 6 := funext fun x => by simp
  have hPi : (fun s : ℝ => ∏ k ∈ Icc (eqN0 1) (eqN1 1), (s - k)) = fun s => s * (s - 1) := by
    funext s; rw [eqN0_one, eqN1_one, Icc_zero_one, prod_pair (by norm_num)]; push_cast; ring
  refine ⟨?_, fun ξ₀ ξ₁ => ?_⟩
  · rw [show (0 : ℝ) + 1 / 2 * 1 = 1 / 2 by norm_num, hR,
      ((hasDerivAt_pow 3 (1 / 2 : ℝ)).fun_sub (hasDerivAt_id' (1 / 2 : ℝ))).deriv]
    norm_num
  · have hPi' : deriv (fun s : ℝ => s * (s - 1)) (1 / 2) = 0 := by
      rw [((hasDerivAt_id' _).mul ((hasDerivAt_id' _).sub_const 1)).deriv]; norm_num
    have i2 : iteratedDeriv 2 (fun x : ℝ => x ^ 3) = fun x => 6 * x := by
      rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one, d1, d2]
    have i3 : iteratedDeriv 3 (fun x : ℝ => x ^ 3) = fun _ => 6 := by
      rw [show (3 : ℕ) = 2 + 1 from rfl, iteratedDeriv_succ, i2, d3]
    rw [hPi, hPi', show (1 + 2 : ℕ) = 3 from rfl, show (1 + 1 : ℕ) = 2 from rfl, i2, i3]
    have : ∏ k ∈ Icc (eqN0 1) (eqN1 1), ((1 / 2 : ℝ) - k) = -1 / 4 := by
      rw [eqN0_one, eqN1_one, Icc_zero_one, prod_pair (by norm_num)]; push_cast; norm_num
    rw [this]; norm_num [Nat.factorial]

/-! ### `|(d/dt) ∏_{k=n₀}^{n₁} (t − k)| ≤ n!` on `[n₀, n₁]` -/

/-- `∏_{k=0}^{m−1} (s − k)`. -/
noncomputable def fallProd (m : ℕ) (s : ℝ) : ℝ := ∏ k ∈ range m, (s - k)

theorem fallProd_succ (m : ℕ) (s : ℝ) : fallProd (m + 1) s = fallProd m s * (s - m) := by
  simp only [fallProd, prod_range_succ]

theorem fallProd_succ' (m : ℕ) (s : ℝ) : fallProd (m + 1) s = fallProd m (s - 1) * s := by
  simp only [fallProd, prod_range_succ']
  congr 1
  · exact prod_congr rfl fun k _ => by push_cast; ring
  · simp

theorem differentiable_fallProd (m : ℕ) : Differentiable ℝ (fallProd m) := by
  unfold fallProd; fun_prop

theorem deriv_fallProd_succ (m : ℕ) (t : ℝ) :
    deriv (fallProd (m + 1)) t = deriv (fallProd m) t * (t - m) + fallProd m t := by
  have h : fallProd (m + 1) = fun s => fallProd m s * (s - m) := funext (fallProd_succ m)
  rw [h, ((differentiable_fallProd m t).hasDerivAt.fun_mul
    ((hasDerivAt_id' t).sub_const (m : ℝ))).deriv]
  ring

theorem deriv_fallProd_succ' (m : ℕ) (t : ℝ) :
    deriv (fallProd (m + 1)) t = deriv (fallProd m) (t - 1) * t + fallProd m (t - 1) := by
  have h : fallProd (m + 1) = fun s => fallProd m (s - 1) * s := funext (fallProd_succ' m)
  have h1 : HasDerivAt (fun s => fallProd m (s - 1)) (deriv (fallProd m) (t - 1)) t := by
    have := (differentiable_fallProd m (t - 1)).hasDerivAt.comp t
      ((hasDerivAt_id' t).sub_const (1 : ℝ))
    simpa [Function.comp_def] using this
  rw [h, (h1.fun_mul (hasDerivAt_id' t)).deriv]
  ring

/-- `|∏_{k=0}^{m−1} (t − k)| ≤ m!` for `t ∈ [−1, m]`: peel off the last factor when `t ≤ m`, the
first factor `t` when `t > m`. -/
theorem deriv_fallProd_zero (t : ℝ) : deriv (fallProd 0) t = 0 := by
  have : fallProd 0 = fun _ => 1 := funext fun _ => by simp [fallProd]
  rw [this, deriv_const]

theorem abs_fallProd_le : ∀ (m : ℕ) (t : ℝ), -1 ≤ t → t ≤ m → |fallProd m t| ≤ m.factorial
  | 0, t, _, _ => by simp [fallProd]
  | m + 1, t, h1, h2 => by
    have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    push_cast at h2
    rw [Nat.factorial_succ]
    push_cast
    rcases le_or_gt t m with h | h
    · rw [fallProd_succ, abs_mul]
      have hb : |t - m| ≤ m + 1 := by rw [abs_le]; constructor <;> linarith
      calc |fallProd m t| * |t - m| ≤ m.factorial * (m + 1) :=
            mul_le_mul (abs_fallProd_le m t h1 h) hb (abs_nonneg _) (by positivity)
        _ = (m + 1) * m.factorial := by ring
    · rw [fallProd_succ', abs_mul]
      have hb : |t| ≤ m + 1 := by rw [abs_le]; constructor <;> linarith
      calc |fallProd m (t - 1)| * |t| ≤ m.factorial * (m + 1) :=
            mul_le_mul (abs_fallProd_le m (t - 1) (by linarith) (by linarith)) hb (abs_nonneg _)
              (by positivity)
        _ = (m + 1) * m.factorial := by ring

/-- `|(d/dt) ∏_{k=0}^{n} (t − k)| ≤ n!` for `t ∈ [0, n]`, by induction on `n` with the two
factorizations `p_{n+1}(t) = p_n(t)(t − n − 1)` (for `t ≤ n`) and `p_{n+1}(t) = t p_n(t − 1)`
(for `t ≥ 1`). -/
theorem abs_deriv_fallProd_le : ∀ (n : ℕ) (t : ℝ), 0 ≤ t → t ≤ n →
    |deriv (fallProd (n + 1)) t| ≤ n.factorial
  | 0, t, _, _ => by
    rw [deriv_fallProd_succ, deriv_fallProd_zero]
    simp [fallProd]
  | 1, t, h0, h1 => by
    have hd : deriv (fallProd 1) t = 1 := by
      rw [deriv_fallProd_succ, deriv_fallProd_zero]; simp [fallProd]
    rw [deriv_fallProd_succ, hd, show fallProd 1 t = t by simp [fallProd]]
    push_cast at h1
    rw [Nat.factorial_one, Nat.cast_one, abs_le]
    constructor <;> linarith
  | n + 2, t, h0, h2 => by
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    push_cast at h2
    have hF : ((n + 2).factorial : ℝ) = (n + 2) * (n + 1).factorial := by
      rw [Nat.factorial_succ]; push_cast; ring
    rw [hF]
    rcases le_or_gt t (n + 1) with h | h
    · -- `t ≤ n + 1`: `p′ = p_{n+1}′(t)(t − n − 2) + p_{n+1}(t)`
      rw [deriv_fallProd_succ]
      have hi : |deriv (fallProd (n + 2)) t| ≤ (n + 1).factorial :=
        abs_deriv_fallProd_le (n + 1) t h0 (by push_cast; exact h)
      have hp : |fallProd (n + 2) t| ≤ (n + 1).factorial * t := by
        rw [fallProd_succ', abs_mul, abs_of_nonneg h0]
        exact mul_le_mul_of_nonneg_right
          (abs_fallProd_le (n + 1) (t - 1) (by linarith) (by push_cast; linarith)) h0
      have hb : |t - ((n + 2 : ℕ) : ℝ)| ≤ n + 2 - t := by
        push_cast; rw [abs_le]; constructor <;> linarith
      calc |deriv (fallProd (n + 2)) t * (t - ((n + 2 : ℕ) : ℝ)) + fallProd (n + 2) t|
          ≤ |deriv (fallProd (n + 2)) t| * |t - ((n + 2 : ℕ) : ℝ)| + |fallProd (n + 2) t| := by
            rw [← abs_mul]; exact abs_add_le _ _
        _ ≤ (n + 1).factorial * (n + 2 - t) + (n + 1).factorial * t :=
            add_le_add (mul_le_mul hi hb (abs_nonneg _) (by positivity)) hp
        _ = (n + 2) * (n + 1).factorial := by ring
    · -- `t > n + 1 ≥ 1`: `p′ = p_{n+1}′(t − 1) t + p_{n+1}(t − 1)`
      rw [deriv_fallProd_succ']
      have hi : |deriv (fallProd (n + 2)) (t - 1)| ≤ (n + 1).factorial :=
        abs_deriv_fallProd_le (n + 1) (t - 1) (by linarith) (by push_cast; linarith)
      have hp : |fallProd (n + 2) (t - 1)| ≤ (n + 1).factorial * (n + 2 - t) := by
        rw [fallProd_succ, abs_mul]
        have hb : |t - 1 - ((n + 1 : ℕ) : ℝ)| ≤ n + 2 - t := by
          push_cast; rw [abs_le]; constructor <;> linarith
        exact mul_le_mul (abs_fallProd_le (n + 1) (t - 1) (by linarith) (by push_cast; linarith))
          hb (abs_nonneg _) (by positivity)
      calc |deriv (fallProd (n + 2)) (t - 1) * t + fallProd (n + 2) (t - 1)|
          ≤ |deriv (fallProd (n + 2)) (t - 1)| * |t| + |fallProd (n + 2) (t - 1)| := by
            rw [← abs_mul]; exact abs_add_le _ _
        _ ≤ (n + 1).factorial * t + (n + 1).factorial * (n + 2 - t) :=
            add_le_add (by rw [abs_of_nonneg h0]; exact mul_le_mul_of_nonneg_right hi h0) hp
        _ = (n + 2) * (n + 1).factorial := by ring

/-- `∏_{k=n₀}^{n₁} (s − k) = p_n(s − n₀)`. -/
theorem prod_Icc_eqN_eq_fallProd (n : ℕ) :
    (fun s : ℝ => ∏ k ∈ Icc (eqN0 n) (eqN1 n), (s - k)) =
      fun s => fallProd (n + 1) (s - eqN0 n) :=
  funext fun s => by
    rw [eqN1_eq, ← shiftEmb_map_univ, prod_map, fallProd,
      ← Fin.prod_univ_eq_prod_range (fun j : ℕ => s - eqN0 n - j) (n + 1)]
    exact prod_congr rfl fun j _ => by simp only [shiftEmb_apply]; push_cast; ring

/-- **`|(d/dt) ∏_{k=n₀}^{n₁} (t − k)| ≤ n!` on `[n₀, n₁]`** (the hypothesis behind 3.4.4; the
maximum `n!` is attained at the end points). -/
theorem abs_deriv_prod_Icc_eqN_le (n : ℕ) {t : ℝ} (ht : t ∈ Set.Icc (eqN0 n : ℝ) (eqN1 n)) :
    |deriv (fun s : ℝ => ∏ k ∈ Icc (eqN0 n) (eqN1 n), (s - k)) t| ≤ n.factorial := by
  rw [prod_Icc_eqN_eq_fallProd]
  have hD : HasDerivAt (fun s => fallProd (n + 1) (s - eqN0 n))
      (deriv (fallProd (n + 1)) (t - eqN0 n)) t := by
    have := (differentiable_fallProd (n + 1) (t - eqN0 n)).hasDerivAt.comp t
      ((hasDerivAt_id' t).sub_const ((eqN0 n : ℤ) : ℝ))
    simpa [Function.comp_def] using this
  rw [hD.deriv]
  have h1 : ((eqN1 n : ℤ) : ℝ) = eqN0 n + n := by rw [eqN1_eq]; push_cast; ring
  rw [h1] at ht
  exact abs_deriv_fallProd_le n (t - eqN0 n) (by linarith [ht.1]) (by linarith [ht.2])

/-- **DLMF 3.4.4** (corrected; see errata): for a bounded `t`-set `J ⊆ (n₀, n₁)` containing `t`,
`c_n = c_n(J)` as in 3.3.12,
`h |R′_{n,t}| ≤ h^{n+1} (c_n h |f^{(n+2)}(ξ₁)| + |f^{(n+1)}(ξ₀)|/(n + 1))`
(using `|(d/dt) ∏ (t − k)| ≤ n!` on `[n₀, n₁]`, `abs_deriv_prod_Icc_eqN_le`). DLMF's first term
lacks the factor `h`. -/
theorem dlmf_3_4_4 {x₀ h : ℝ} (hh : 0 < h) (n : ℕ) (f : ℝ → ℝ) {U : Set ℝ} (hU : IsOpen U)
    (hd : ∀ k ≤ n + 1, DifferentiableOn ℝ (iteratedDeriv k f) U)
    (hI : Set.Icc (x₀ + eqN0 n * h) (x₀ + eqN1 n * h) ⊆ U)
    (hc : ContinuousOn (iteratedDeriv (n + 2) f) (Set.Icc (x₀ + eqN0 n * h) (x₀ + eqN1 n * h)))
    {J : Set ℝ} (hJ : J ⊆ Set.Ioo (eqN0 n : ℝ) (eqN1 n)) {t : ℝ} (ht : t ∈ J) :
    ∃ ξ₀ ∈ Set.Icc (x₀ + eqN0 n * h) (x₀ + eqN1 n * h),
      ∃ ξ₁ ∈ Set.Icc (x₀ + eqN0 n * h) (x₀ + eqN1 n * h),
        h * |deriv (lagrangeRem (eqNode x₀ h n) f) (x₀ + t * h)| ≤
          h ^ (n + 1) * (eqBoundCoeff n J * h * |iteratedDeriv (n + 2) f ξ₁| +
            1 / (n + 1) * |iteratedDeriv (n + 1) f ξ₀|) := by
  obtain ⟨ξ₀, hξ₀, ξ₁, hξ₁, hR⟩ := dlmf_3_4_3 hh n f hU hd hI hc (hJ ht)
  refine ⟨ξ₀, hξ₀, ξ₁, hξ₁, ?_⟩
  have hPi' := abs_deriv_prod_Icc_eqN_le n (Set.Ioo_subset_Icc_self (hJ ht))
  set a := iteratedDeriv (n + 1) f ξ₀
  set b := iteratedDeriv (n + 2) f ξ₁
  set p := deriv (fun s : ℝ => ∏ k ∈ Icc (eqN0 n) (eqN1 n), (s - k)) t
  set q := ∏ k ∈ Icc (eqN0 n) (eqN1 n), (t - (k : ℝ))
  set c := eqBoundCoeff n J
  have hcont : Continuous fun t : ℝ => ∏ k ∈ Icc (eqN0 n) (eqN1 n), |t - k| := by fun_prop
  have hbdd : BddAbove ((fun t : ℝ => ∏ k ∈ Icc (eqN0 n) (eqN1 n), |t - k|) '' J) :=
    ((Metric.isBounded_Ioo _ _).subset hJ |>.isCompact_closure.image_of_continuousOn
      hcont.continuousOn).bddAbove.mono (Set.image_mono subset_closure)
  have hN : (0 : ℝ) < n.factorial := by positivity
  have hN1 : (0 : ℝ) < (n + 1).factorial := by positivity
  have hf1 : ((n + 1).factorial : ℝ) = (n + 1) * n.factorial := by
    rw [Nat.factorial_succ]; push_cast; ring
  have hf2 : ((n + 2).factorial : ℝ) = (n + 2) * (n + 1).factorial := by
    rw [show n + 2 = (n + 1) + 1 from rfl, Nat.factorial_succ]; push_cast; ring
  have hq : |q| ≤ (n + 1).factorial * c := by
    have hle := le_csSup hbdd (Set.mem_image_of_mem _ ht)
    rw [abs_prod]
    calc ∏ k ∈ Icc (eqN0 n) (eqN1 n), |t - k| ≤ _ := hle
      _ = (n + 1).factorial * c := by simp only [c, eqBoundCoeff]; field_simp
  have hc0 : 0 ≤ c := by
    by_contra hneg
    push Not at hneg
    have : ((n + 1).factorial : ℝ) * c < 0 := mul_neg_of_pos_of_neg hN1 hneg
    linarith [abs_nonneg q]
  have habs : h * |deriv (lagrangeRem (eqNode x₀ h n) f) (x₀ + t * h)| =
      |h * deriv (lagrangeRem (eqNode x₀ h n) f) (x₀ + t * h)| := by
    rw [abs_mul, abs_of_pos hh]
  rw [habs, hR]
  have hA : |h ^ (n + 1) / (n + 1).factorial * (a * p)| ≤ h ^ (n + 1) * (1 / (n + 1) * |a|) := by
    rw [abs_mul, abs_mul, abs_of_pos (by positivity)]
    calc h ^ (n + 1) / (n + 1).factorial * (|a| * |p|)
        ≤ h ^ (n + 1) / (n + 1).factorial * (|a| * n.factorial) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hPi' (abs_nonneg a)) (by positivity)
      _ = h ^ (n + 1) * (1 / (n + 1) * |a|) := by rw [hf1]; field_simp
  have hB : |h ^ (n + 2) / (n + 2).factorial * (b * q)| ≤ h ^ (n + 1) * (c * h * |b|) := by
    rw [abs_mul, abs_mul, abs_of_pos (by positivity)]
    calc h ^ (n + 2) / (n + 2).factorial * (|b| * |q|)
        ≤ h ^ (n + 2) / (n + 2).factorial * (|b| * ((n + 1).factorial * c)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hq (abs_nonneg b)) (by positivity)
      _ = h ^ (n + 1) * (c * h * |b|) / (n + 2) := by rw [hf2]; field_simp; ring
      _ ≤ h ^ (n + 1) * (c * h * |b|) := div_le_self (by positivity) (by linarith)
  calc |h ^ (n + 1) / (n + 1).factorial * (a * p) + h ^ (n + 2) / (n + 2).factorial * (b * q)|
      ≤ _ := abs_add_le _ _
    _ ≤ h ^ (n + 1) * (1 / (n + 1) * |a|) + h ^ (n + 1) * (c * h * |b|) := add_le_add hA hB
    _ = _ := by ring

end Azurite.DLMF
