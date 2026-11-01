/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Mathlib.Analysis.InnerProductSpace.l2Space

/-!
# DLMF §1.18(i): Hilbert spaces

https://dlmf.nist.gov/1.18.i

DLMF's inner product `⟨u, v⟩` is linear in `u`. Mathlib's `⟪u, v⟫_ℂ` is linear in `v`, so
`dlmfInner u v = ⟪v, u⟫_ℂ`, and the coefficients `cₙ = ⟨v, vₙ⟩` are Mathlib's `⟪vₙ, v⟫`.

* Axioms (i)–(iv): `dlmf_1_18_i_linear`, `dlmf_1_18_i_conj`, `dlmf_1_18_i_nonneg`,
  `dlmf_1_18_i_definite`. Conversely, a form with DLMF's axioms gives Mathlib's
  `InnerProductSpace.Core` (`dlmfInnerCore`). 1.18.1 (`dlmf_1_18_1`).
* Normalized and orthogonal elements, orthonormal sets (`IsOrthonormalSet` ↔ Mathlib's
  `Orthonormal`), and DLMF's Cauchy-sequence definition of a Hilbert space (`IsHilbertSpace` ↔
  `CompleteSpace`).
* 1.18.2–1.18.3: Bessel's inequality.
* 1.18.4–1.18.5: complete orthonormal sets (Parseval for every `v`, `IsCompleteOrthonormal`) are
  exactly Mathlib's Hilbert bases (`isCompleteOrthonormal_iff`). DLMF's definition of
  separability (an at most countable complete orthonormal set, `IsSeparableDLMF`) agrees with the
  topological one (`isSeparableDLMF_iff`). For that, orthonormal sets in a separable space are
  countable (`countable_of_orthonormal_subtype`, disjoint balls of radius `1/2`).
* 1.18.5–1.18.7: square-summable coefficients determine a unique `v = ∑ cₙ vₙ`, with norm
  convergence of the partial sums (`dlmf_1_18_6`).
* 1.18.8–1.18.9: the norm and inner product of `ℓ²` (Mathlib's `lp (fun _ ↦ ℂ) 2`).
* 1.18.10: every infinite-dimensional separable Hilbert space is isometrically isomorphic to `ℓ²`
  by `∑ cₙ vₙ ↦ (cₙ)` (`dlmf_1_18_10`).

No discrepancies with the DLMF were found.
-/

open Set Filter Topology TopologicalSpace
open scoped InnerProductSpace ComplexConjugate ComplexOrder lp

namespace Azurite.DLMF

universe u

/-! ### Inner product spaces -/

section Axioms

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- DLMF §1.18(i): a form `⟨u, v⟩` satisfying DLMF's axioms (i)–(iv), linear in `u`, makes `V`
an inner product space in Mathlib's sense (conjugate-linear in the first slot) via
`inner x y = ⟨y, x⟩`. -/
@[instance_reducible]
noncomputable def dlmfInnerCore (B : V → V → ℂ)
    (hadd : ∀ u w v, B (u + w) v = B u v + B w v) (hsmul : ∀ (a : ℂ) u v, B (a • u) v = a * B u v)
    (hconj : ∀ u v, B u v = conj (B v u)) (hnn : ∀ v, 0 ≤ B v v)
    (hdef : ∀ v, B v v = 0 → v = 0) : InnerProductSpace.Core ℂ V where
  inner x y := B y x
  conj_inner_symm x y := by rw [hconj y x]
  re_inner_nonneg x := (Complex.nonneg_iff.mp (hnn x)).1
  add_left x y z := by
    show B z (x + y) = B z x + B z y
    rw [hconj z, hadd, map_add, ← hconj, ← hconj]
  smul_left x y r := by
    show B y (r • x) = conj r * B y x
    rw [hconj y, hsmul, map_mul, ← hconj]
  definite x h := hdef x h

end Axioms

variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

/-- DLMF's inner product `⟨u, v⟩`, complex linear in `u`; in Mathlib's convention (linear in the
second slot) it is `⟪v, u⟫`. -/
noncomputable def dlmfInner (u v : V) : ℂ := ⟪v, u⟫_ℂ

/-- DLMF §1.18(i)(i): `⟨u, v⟩` is complex linear in `u`. -/
theorem dlmf_1_18_i_linear (a b : ℂ) (u w v : V) :
    dlmfInner (a • u + b • w) v = a * dlmfInner u v + b * dlmfInner w v := by
  simp only [dlmfInner, inner_add_right, inner_smul_right]

/-- DLMF §1.18(i)(ii): `⟨u, v⟩ = conj ⟨v, u⟩`. -/
theorem dlmf_1_18_i_conj (u v : V) : dlmfInner u v = conj (dlmfInner v u) :=
  (inner_conj_symm v u).symm

theorem dlmfInner_self (v : V) : dlmfInner v v = ((‖v‖ ^ 2 : ℝ) : ℂ) := by
  rw [dlmfInner, inner_self_eq_norm_sq_to_K]; norm_cast

/-- DLMF §1.18(i)(iii): `⟨v, v⟩ ≥ 0`. -/
theorem dlmf_1_18_i_nonneg (v : V) : 0 ≤ dlmfInner v v := by
  rw [dlmfInner_self]; exact Complex.zero_le_real.mpr (by positivity)

/-- DLMF §1.18(i)(iv): `⟨v, v⟩ = 0` implies `v = 0`. -/
theorem dlmf_1_18_i_definite {v : V} (h : dlmfInner v v = 0) : v = 0 :=
  inner_self_eq_zero.mp h

/-- DLMF 1.18.1: `‖v‖ = √⟨v, v⟩`. -/
theorem dlmf_1_18_1 (v : V) : ‖v‖ = √(dlmfInner v v).re ∧ ((‖v‖ : ℂ)) ^ 2 = dlmfInner v v := by
  refine ⟨?_, ?_⟩
  · rw [dlmfInner_self, Complex.ofReal_re, Real.sqrt_sq (norm_nonneg v)]
  · rw [dlmfInner_self]; push_cast; ring

/-- DLMF §1.18(i): `v` is normalized if `‖v‖ = 1`. -/
def IsNormalized (v : V) : Prop := ‖v‖ = 1

/-- DLMF §1.18(i): `u` and `v` are orthogonal if `⟨u, v⟩ = 0`. -/
def IsOrthogonalDLMF (u v : V) : Prop := dlmfInner u v = 0

/-- DLMF §1.18(i): an orthonormal set: normalized, pairwise orthogonal elements. -/
def IsOrthonormalSet {ι : Type*} (v : ι → V) : Prop :=
  (∀ i, IsNormalized (v i)) ∧ Pairwise fun i j => IsOrthogonalDLMF (v i) (v j)

theorem isOrthonormalSet_iff {ι : Type*} (v : ι → V) : IsOrthonormalSet v ↔ Orthonormal ℂ v := by
  refine and_congr Iff.rfl ⟨fun h i j hij => ?_, fun h i j hij => ?_⟩
  · exact inner_eq_zero_symm.mp (h hij)
  · exact inner_eq_zero_symm.mp (h hij)

/-- DLMF §1.18(i): `V` is a Hilbert space if every Cauchy sequence (`‖vₘ − vₙ‖ → 0`) converges in
norm. -/
def IsHilbertSpace (V : Type*) [NormedAddCommGroup V] : Prop :=
  ∀ u : ℕ → V, Tendsto (fun p : ℕ × ℕ => ‖u p.1 - u p.2‖) atTop (𝓝 0) →
    ∃ v, Tendsto (fun n => ‖v - u n‖) atTop (𝓝 0)

omit [InnerProductSpace ℂ V] in
theorem isHilbertSpace_iff : IsHilbertSpace V ↔ CompleteSpace V := by
  constructor
  · intro h
    refine Metric.complete_of_cauchySeq_tendsto fun u hu => ?_
    rw [cauchySeq_iff_tendsto_dist_atTop_0] at hu
    simp only [dist_eq_norm] at hu
    obtain ⟨v, hv⟩ := h u hu
    refine ⟨v, tendsto_iff_norm_sub_tendsto_zero.mpr ?_⟩
    simpa only [norm_sub_rev] using hv
  · intro _ u hu
    have hc : CauchySeq u := by
      rw [cauchySeq_iff_tendsto_dist_atTop_0]; simpa only [dist_eq_norm] using hu
    obtain ⟨v, hv⟩ := cauchySeq_tendsto_of_complete hc
    refine ⟨v, ?_⟩
    simpa only [norm_sub_rev] using tendsto_iff_norm_sub_tendsto_zero.mp hv

/-! ### Bessel's inequality and complete orthonormal sets (1.18.2–1.18.5) -/

/-- DLMF 1.18.2–1.18.3: Bessel's inequality `∑ₙ |cₙ|² ≤ ‖v‖²` with `cₙ = ⟨v, vₙ⟩`. -/
theorem dlmf_1_18_2 {ι : Type*} {v : ι → V} (hv : Orthonormal ℂ v) (x : V) :
    Summable (fun i => ‖dlmfInner x (v i)‖ ^ 2) ∧ ∑' i, ‖dlmfInner x (v i)‖ ^ 2 ≤ ‖x‖ ^ 2 :=
  ⟨hv.inner_products_summable x, hv.tsum_inner_products_le x⟩

/-- DLMF §1.18(i): a complete orthonormal set: Parseval's identity 1.18.4 holds for every `v`. -/
def IsCompleteOrthonormal {ι : Type*} (v : ι → V) : Prop :=
  Orthonormal ℂ v ∧ ∀ x, ∑' i, ‖dlmfInner x (v i)‖ ^ 2 = ‖x‖ ^ 2

theorem tsum_norm_sq_hilbertBasis {ι : Type*} (b : HilbertBasis ι ℂ V) (x : V) :
    ∑' i, ‖dlmfInner x (b i)‖ ^ 2 = ‖x‖ ^ 2 := by
  have h := lp.norm_rpow_eq_tsum (p := 2) (by norm_num) (b.repr x)
  rw [b.repr.norm_map] at h
  simp only [ENNReal.toReal_ofNat, Real.rpow_two, b.repr_apply_apply] at h
  exact h.symm

/-- Complete orthonormal sets are exactly Mathlib's Hilbert bases. -/
theorem isCompleteOrthonormal_iff {ι : Type*} (v : ι → V) [CompleteSpace V] :
    IsCompleteOrthonormal v ↔ ∃ b : HilbertBasis ι ℂ V, ⇑b = v := by
  constructor
  · rintro ⟨hv, hp⟩
    have hsp : (Submodule.span ℂ (Set.range v))ᗮ = ⊥ := by
      rw [Submodule.eq_bot_iff]
      intro x hx
      have h0 : ∀ i, dlmfInner x (v i) = 0 := fun i =>
        Submodule.inner_right_of_mem_orthogonal (Submodule.subset_span (Set.mem_range_self i)) hx
      have := hp x
      simp only [h0, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
        tsum_zero] at this
      exact norm_eq_zero.mp (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this.symm)
    exact ⟨HilbertBasis.mkOfOrthogonalEqBot hv hsp, HilbertBasis.coe_mkOfOrthogonalEqBot hv hsp⟩
  · rintro ⟨b, rfl⟩
    exact ⟨b.orthonormal, tsum_norm_sq_hilbertBasis b⟩

/-- DLMF 1.18.4–1.18.5: for a complete orthonormal set, `∑ₙ |cₙ|² = ‖v‖² < ∞`. -/
theorem dlmf_1_18_4 {ι : Type*} {v : ι → V} (hv : IsCompleteOrthonormal v) (x : V) :
    Summable (fun i => ‖dlmfInner x (v i)‖ ^ 2) ∧ ∑' i, ‖dlmfInner x (v i)‖ ^ 2 = ‖x‖ ^ 2 :=
  ⟨hv.1.inner_products_summable x, hv.2 x⟩

/-! ### Separable Hilbert spaces -/

/-- DLMF §1.18(i): `V` is separable if it has an at most countable complete orthonormal set. -/
def IsSeparableDLMF (V : Type u) [NormedAddCommGroup V] [InnerProductSpace ℂ V] : Prop :=
  ∃ (ι : Type u) (_ : Countable ι) (v : ι → V), IsCompleteOrthonormal v

/-- Distinct elements of an orthonormal set are at distance `√2`, so the balls of radius `1/2`
about them are disjoint; in a separable space an orthonormal set is therefore countable. -/
theorem countable_of_orthonormal_subtype [SeparableSpace V] {w : Set V}
    (hw : Orthonormal ℂ ((↑) : w → V)) : w.Countable := by
  refine Set.PairwiseDisjoint.countable_of_isOpen (s := fun x => Metric.ball x (1 / 2))
    (fun x hx y hy hxy => ?_) (fun x _ => Metric.isOpen_ball)
    (fun x _ => ⟨x, Metric.mem_ball_self (by norm_num)⟩)
  rw [Function.onFun, Set.disjoint_left]
  intro z hzx hzy
  have h := hw.2 (show (⟨x, hx⟩ : w) ≠ ⟨y, hy⟩ from fun e => hxy (congrArg Subtype.val e))
  have hx1 := hw.1 ⟨x, hx⟩
  have hy1 := hw.1 ⟨y, hy⟩
  simp only at h hx1 hy1
  have hsq : ‖x - y‖ ^ 2 = 2 := by
    rw [@norm_sub_sq ℂ, hx1, hy1, h]; simp; norm_num
  have hd : ‖x - y‖ < 1 := by
    have := dist_triangle_left x y z
    rw [Metric.mem_ball] at hzx hzy
    rw [← dist_eq_norm]; linarith
  nlinarith [norm_nonneg (x - y)]

/-- DLMF's definition of separability agrees with the topological one. -/
theorem isSeparableDLMF_iff [CompleteSpace V] : IsSeparableDLMF V ↔ SeparableSpace V := by
  constructor
  · rintro ⟨ι, _, v, hv⟩
    obtain ⟨b, rfl⟩ := (isCompleteOrthonormal_iff v).mp hv
    have hs : IsSeparable (Submodule.span ℂ (Set.range b) : Set V) :=
      (Set.countable_range b).isSeparable.span
    have hcl := hs.closure
    rw [← Submodule.topologicalClosure_coe, b.dense_span, Submodule.top_coe] at hcl
    exact isSeparable_univ_iff.mp hcl
  · intro _
    obtain ⟨w, b, hb⟩ := exists_hilbertBasis ℂ V
    have hc : w.Countable := countable_of_orthonormal_subtype (hb ▸ b.orthonormal)
    exact ⟨w, hc.to_subtype, b, (isCompleteOrthonormal_iff _).mpr ⟨b, rfl⟩⟩

/-! ### Expansions (1.18.6–1.18.7) -/

/-- DLMF 1.18.5–1.18.7: if `∑ |cₙ|² < ∞` there is a unique `v` with `⟨v, vₙ⟩ = cₙ`, and
`v = ∑ cₙ vₙ` with convergence in norm: `‖v − ∑_{n=0}^{N} cₙ vₙ‖ → 0`. -/
theorem dlmf_1_18_6 [CompleteSpace V] {v : ℕ → V} (hv : IsCompleteOrthonormal v) {c : ℕ → ℂ}
    (hc : Summable fun n => ‖c n‖ ^ 2) :
    ∃! x : V, (∀ n, dlmfInner x (v n) = c n) ∧ HasSum (fun n => c n • v n) x ∧
      Tendsto (fun N => ‖x - ∑ n ∈ Finset.range (N + 1), c n • v n‖) atTop (𝓝 0) := by
  obtain ⟨b, rfl⟩ := (isCompleteOrthonormal_iff v).mp hv
  have hmem : Memℓp c 2 := memℓp_gen (by simpa using hc)
  let f : ℓ²(ℕ, ℂ) := ⟨c, hmem⟩
  have hcoef : ∀ y : V, (∀ n, dlmfInner y (b n) = c n) ↔ b.repr y = f := fun y => by
    rw [lp.ext_iff, funext_iff]
    simp only [dlmfInner, b.repr_apply_apply]
    rfl
  refine ⟨b.repr.symm f, ⟨(hcoef _).mpr (by simp), b.hasSum_repr_symm f, ?_⟩, ?_⟩
  · have h := ((b.hasSum_repr_symm f).tendsto_sum_nat).comp (tendsto_add_atTop_nat 1)
    refine (tendsto_iff_norm_sub_tendsto_zero.mp h).congr fun N => ?_
    rw [norm_sub_rev]
    rfl
  · rintro y ⟨hy, -, -⟩
    rw [← (hcoef y).mp hy, LinearIsometryEquiv.symm_apply_apply]

/-! ### `ℓ²` (1.18.8–1.18.10) -/

/-- DLMF 1.18.8: `‖v‖² = ∑ |cₙ|² < ∞` in `ℓ²`. -/
theorem dlmf_1_18_8 (v : ℓ²(ℕ, ℂ)) :
    Summable (fun n => ‖v n‖ ^ 2) ∧ ‖v‖ ^ 2 = ∑' n, ‖v n‖ ^ 2 := by
  have h := lp.norm_rpow_eq_tsum (p := 2) (by norm_num) v
  have hs := (lp.memℓp v).summable (p := 2) (by norm_num)
  simp only [ENNReal.toReal_ofNat, Real.rpow_two] at h hs
  exact ⟨hs, h⟩

/-- DLMF 1.18.9: `⟨v, w⟩ = ∑ cₙ conj(dₙ)` in `ℓ²`. -/
theorem dlmf_1_18_9 (v w : ℓ²(ℕ, ℂ)) : dlmfInner v w = ∑' n, v n * conj (w n) := by
  rw [dlmfInner, lp.inner_eq_tsum]
  congr 1

/-- DLMF 1.18.10: every infinite-dimensional separable Hilbert space is isomorphic to `ℓ²` by
`∑ cₙ vₙ ↦ (c₀, c₁, c₂, …)` for a complete orthonormal set `{vₙ}_{n=0}^∞`. -/
theorem dlmf_1_18_10 [CompleteSpace V] [SeparableSpace V] (hinf : ¬ FiniteDimensional ℂ V) :
    ∃ (v : ℕ → V) (e : V ≃ₗᵢ[ℂ] ℓ²(ℕ, ℂ)), IsCompleteOrthonormal v ∧
      (∀ x n, e x n = dlmfInner x (v n)) ∧
        ∀ c : ℓ²(ℕ, ℂ), HasSum (fun n => c n • v n) (e.symm c) := by
  obtain ⟨ι, hι, w, hw⟩ := (isSeparableDLMF_iff (V := V)).mpr inferInstance
  obtain ⟨b, rfl⟩ := (isCompleteOrthonormal_iff w).mp hw
  have hinfι : Infinite ι := by
    by_contra hfin
    rw [not_infinite_iff_finite] at hfin
    have hfg : (Submodule.span ℂ (Set.range b)).FG := Submodule.fg_span (Set.finite_range b)
    have : FiniteDimensional ℂ (Submodule.span ℂ (Set.range b)) :=
      FiniteDimensional.span_of_finite ℂ (Set.finite_range b)
    have htop : Submodule.span ℂ (Set.range b) = ⊤ := by
      rw [← (Submodule.closed_of_finiteDimensional
        (Submodule.span ℂ (Set.range b))).submodule_topologicalClosure_eq,
        b.dense_span]
    exact hinf (Module.finite_def.mpr (htop ▸ hfg))
  obtain ⟨hd⟩ := nonempty_denumerable ι
  let e := Denumerable.eqv ι
  have hon : Orthonormal ℂ (b ∘ e.symm) := b.orthonormal.comp _ e.symm.injective
  have hsp : ⊤ ≤ (Submodule.span ℂ (Set.range (b ∘ e.symm))).topologicalClosure := by
    rw [e.symm.surjective.range_comp, b.dense_span]
  let B := HilbertBasis.mk hon hsp
  have hB : ⇑B = b ∘ e.symm := HilbertBasis.coe_mk hon hsp
  refine ⟨b ∘ e.symm, B.repr, (isCompleteOrthonormal_iff _).mpr ⟨B, hB⟩, fun x n => ?_,
    fun c => ?_⟩
  · rw [B.repr_apply_apply, hB]; rfl
  · have := B.hasSum_repr_symm c
    rwa [hB] at this

end Azurite.DLMF
