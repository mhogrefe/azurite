/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter5.Section14Anderson
import Mathlib.LinearAlgebra.Vandermonde

/-!
# DLMF §5.14: from the ordered region to the cube

For a function on `[0, 1]ⁿ` invariant under permutations of the coordinates,
`∫_{[0,1]ⁿ} f = n! ∫_{1>t₁>⋯>tₙ>0} f` (`integral_cube_eq`): the cube is, up to a null set, the
disjoint union of the `n!` images `{t : t ∘ σ ∈ orderedOpen n}` of the ordered region
(`Tuple.sort`), each of which carries the same integral (coordinate permutations preserve volume).
-/

open Finset MeasureTheory

namespace Azurite.DLMF

variable {n : ℕ}

/-! ### Null hyperplanes -/

theorem volume_linear_level_null {L : (Fin n → ℝ) →ₗ[ℝ] ℝ} (hL : L ≠ 0) (c : ℝ) :
    volume {t : Fin n → ℝ | L t = c} = 0 := by
  by_cases hne : ∃ t₀, L t₀ = c
  · obtain ⟨t₀, ht₀⟩ := hne
    have hker : LinearMap.ker L ≠ ⊤ := fun h => hL (LinearMap.ext fun x => by
      have : x ∈ LinearMap.ker L := h ▸ Submodule.mem_top
      simpa using this)
    have he : {t : Fin n → ℝ | L t = c} = (fun x => x + -t₀) ⁻¹' (LinearMap.ker L) := by
      ext t
      simp only [Set.mem_ofPred_eq, Set.mem_preimage, SetLike.mem_coe, LinearMap.mem_ker, map_add,
        map_neg, ht₀]
      constructor <;> intro h <;> linarith
    rw [he, measure_preimage_add_right, Measure.addHaar_submodule volume _ hker]
  · push Not at hne
    have : {t : Fin n → ℝ | L t = c} = ∅ := Set.eq_empty_of_forall_notMem fun t h => hne t h
    rw [this, measure_empty]

theorem volume_coord_eq_null {i j : Fin n} (hij : i ≠ j) :
    volume {t : Fin n → ℝ | t i = t j} = 0 := by
  set L : (Fin n → ℝ) →ₗ[ℝ] ℝ := LinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) i -
    LinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) j
  have hL : L ≠ 0 := fun h => by
    have := LinearMap.congr_fun h (Pi.single i 1)
    simp [L, hij.symm] at this
  have := volume_linear_level_null hL 0
  convert this using 2
  ext t; simp [L, sub_eq_zero]

/-! ### Permuting coordinates -/

/-- `t ↦ t ∘ σ` as a measurable equivalence. -/
def permMap (σ : Equiv.Perm (Fin n)) : (Fin n → ℝ) ≃ᵐ (Fin n → ℝ) :=
  MeasurableEquiv.piCongrLeft (fun _ => ℝ) σ.symm

theorem permMap_apply (σ : Equiv.Perm (Fin n)) (t : Fin n → ℝ) : permMap σ t = t ∘ σ := by
  funext i
  simp [permMap, MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft_apply_eq_cast]

theorem measurePreserving_permMap (σ : Equiv.Perm (Fin n)) :
    MeasurePreserving (permMap σ) volume volume :=
  volume_measurePreserving_piCongrLeft (fun _ => ℝ) σ.symm

/-- The piece of the cube sorted by `σ`. -/
def orderedPiece (σ : Equiv.Perm (Fin n)) : Set (Fin n → ℝ) := {t | t ∘ σ ∈ orderedOpen n}

theorem orderedPiece_eq (σ : Equiv.Perm (Fin n)) :
    orderedPiece σ = permMap σ ⁻¹' orderedOpen n := by
  ext t; simp [orderedPiece, permMap_apply]

theorem measurableSet_orderedPiece (σ : Equiv.Perm (Fin n)) : MeasurableSet (orderedPiece σ) := by
  rw [orderedPiece_eq]; exact (permMap σ).measurable (measurableSet_orderedOpen n)

/-- A strictly monotone permutation of `Fin n` is the identity. -/
theorem perm_eq_one_of_strictMono {π : Equiv.Perm (Fin n)} (h : StrictMono π) : π = 1 := by
  have e := Subsingleton.elim (StrictMono.orderIsoOfSurjective π h π.surjective) (OrderIso.refl _)
  refine Equiv.ext fun i => ?_
  have := congrArg (fun f : Fin n ≃o Fin n => f i) e
  simpa using this

theorem pairwise_disjoint_orderedPiece :
    Pairwise (Function.onFun Disjoint fun σ : Equiv.Perm (Fin n) => orderedPiece σ) := by
  intro σ τ hστ
  refine Set.disjoint_left.mpr fun t hσ hτ => hστ ?_
  -- `π = σ⁻¹ τ` is strictly monotone
  set π : Equiv.Perm (Fin n) := τ.trans σ.symm
  have hg : StrictAnti (t ∘ σ) := fun i j h => hσ.2 i j h
  have hπ : StrictMono π := fun i j hij => by
    have h1 : t (τ j) < t (τ i) := hτ.2 i j hij
    have h2 : (t ∘ σ) (π j) < (t ∘ σ) (π i) := by simpa [π] using h1
    exact hg.lt_iff_gt.mp h2
  have h1 := perm_eq_one_of_strictMono hπ
  refine Equiv.ext fun i => ?_
  have h := congrArg (fun p : Equiv.Perm (Fin n) => p i) h1
  simp only [π, Equiv.trans_apply, Equiv.Perm.coe_one, id_eq] at h
  exact ((Equiv.symm_apply_eq σ).mp h).symm

/-- Every point of the open cube with distinct coordinates lies in some sorted piece. -/
theorem exists_orderedPiece {t : Fin n → ℝ} (h01 : ∀ i, 0 < t i ∧ t i < 1)
    (hinj : Function.Injective t) : ∃ σ : Equiv.Perm (Fin n), t ∈ orderedPiece σ := by
  set s := Tuple.sort t
  have hmono : StrictMono (t ∘ s) :=
    (Tuple.monotone_sort t).strictMono_of_injective (hinj.comp s.injective)
  refine ⟨Fin.revPerm.trans s, fun i => h01 _, fun i j hij => ?_⟩
  simp only [Function.comp, Equiv.trans_apply, Fin.revPerm_apply]
  exact hmono (Fin.rev_lt_rev.mpr hij)

theorem orderedPiece_subset_cube (σ : Equiv.Perm (Fin n)) :
    orderedPiece σ ⊆ Set.Icc 0 1 := fun t ht => by
  constructor <;> intro i
  · have := (ht.1 (σ.symm i)).1; simp at this; exact this.le
  · have := (ht.1 (σ.symm i)).2; simp at this; exact this.le

theorem volume_cube_diff_pieces :
    volume (Set.Icc (0 : Fin n → ℝ) 1 \ ⋃ σ : Equiv.Perm (Fin n), orderedPiece σ) = 0 := by
  refine measure_mono_null (t := (⋃ i : Fin n, {t : Fin n → ℝ | t i = 0}) ∪
    (⋃ i : Fin n, {t : Fin n → ℝ | t i = 1}) ∪
      ⋃ i : Fin n, ⋃ j : Fin n, {t : Fin n → ℝ | i ≠ j ∧ t i = t j}) ?_ ?_
  · rintro t ⟨⟨h0, h1⟩, hU⟩
    by_contra hN
    simp only [Set.mem_union, Set.mem_iUnion, Set.mem_ofPred_eq, not_or, not_exists, not_and]
      at hN
    obtain ⟨⟨hN0, hN1⟩, hNe⟩ := hN
    have h01 : ∀ i, 0 < t i ∧ t i < 1 := fun i =>
      ⟨lt_of_le_of_ne (h0 i) (Ne.symm (hN0 i)), lt_of_le_of_ne (h1 i) (hN1 i)⟩
    have hinj : Function.Injective t := fun i j h => by
      by_contra hij; exact hNe i j hij h
    obtain ⟨σ, hσ⟩ := exists_orderedPiece h01 hinj
    exact hU (Set.mem_iUnion.mpr ⟨σ, hσ⟩)
  · refine measure_union_null (measure_union_null (measure_iUnion_null fun i => ?_)
      (measure_iUnion_null fun i => ?_)) (measure_iUnion_null fun i => measure_iUnion_null
        fun j => ?_)
    · rw [volume_pi]; exact Measure.pi_hyperplane _ i 0
    · rw [volume_pi]; exact Measure.pi_hyperplane _ i 1
    · by_cases hij : i = j
      · simp [hij]
      · exact measure_mono_null (fun t ht => ht.2) (volume_coord_eq_null hij)

/-- **Symmetrization**: for permutation-invariant `f`,
`∫_{[0,1]ⁿ} f = n! ∫_{1>t₁>⋯>tₙ>0} f`. -/
theorem integral_cube_eq {f : (Fin n → ℝ) → ℂ}
    (hsym : ∀ (σ : Equiv.Perm (Fin n)) t, f (t ∘ σ) = f t)
    (hint : IntegrableOn f (orderedOpen n)) :
    IntegrableOn f (Set.Icc 0 1) ∧
      ∫ t in Set.Icc 0 1, f t = (n.factorial : ℂ) * ∫ t in orderedOpen n, f t := by
  set U := ⋃ σ : Equiv.Perm (Fin n), orderedPiece σ
  have hae : Set.Icc (0 : Fin n → ℝ) 1 =ᵐ[volume] U := ae_eq_set.mpr ⟨volume_cube_diff_pieces,
    by rw [Set.sdiff_eq_empty.mpr (Set.iUnion_subset orderedPiece_subset_cube), measure_empty]⟩
  have hpiece : ∀ σ : Equiv.Perm (Fin n), IntegrableOn f (orderedPiece σ) ∧
      ∫ t in orderedPiece σ, f t = ∫ t in orderedOpen n, f t := fun σ => by
    have hfe : (fun t => f (permMap σ t)) = f := funext fun t => by rw [permMap_apply, hsym]
    rw [orderedPiece_eq]
    constructor
    · rw [← hfe]
      exact ((measurePreserving_permMap σ).integrableOn_comp_preimage
        (permMap σ).measurableEmbedding).mpr hint
    · conv_lhs => rw [← hfe]
      exact (measurePreserving_permMap σ).setIntegral_preimage_emb
        (permMap σ).measurableEmbedding f _
  refine ⟨(integrableOn_finite_iUnion.mpr fun σ => (hpiece σ).1).congr_set_ae hae, ?_⟩
  rw [setIntegral_congr_set hae, integral_iUnion_fintype measurableSet_orderedPiece
    pairwise_disjoint_orderedPiece fun σ => (hpiece σ).1]
  simp_rw [fun σ => (hpiece σ).2]
  rw [sum_const, card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]

/-! ### Selberg's integral for `ℜa, ℜb, ℜc > 0` -/

theorem abs_vandermondeDelta_eq (t : Fin n → ℝ) :
    |vandermondeDelta t| = |(Matrix.vandermonde t).det| := by
  rw [vandermondeDelta, Matrix.det_vandermonde, abs_prod, abs_prod]
  refine prod_congr rfl fun i _ => ?_
  rw [abs_prod, abs_prod]
  exact prod_congr rfl fun j _ => abs_sub_comm _ _

theorem abs_vandermondeDelta_comp (σ : Equiv.Perm (Fin n)) (t : Fin n → ℝ) :
    |vandermondeDelta (t ∘ σ)| = |vandermondeDelta t| := by
  rw [abs_vandermondeDelta_eq, abs_vandermondeDelta_eq,
    show Matrix.vandermonde (t ∘ σ) = (Matrix.vandermonde t).submatrix σ id from by
      ext i j; simp [Matrix.vandermonde_apply], Matrix.det_permute, abs_mul]
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]

theorem jacobiWeight_comp {α β : ℂ} (σ : Equiv.Perm (Fin n)) (t : Fin n → ℝ) :
    jacobiWeight α β (t ∘ σ) = jacobiWeight α β t := by
  simp only [jacobiWeight, Function.comp]
  exact Equiv.prod_comp σ (fun i => (t i : ℂ) ^ (α - 1) * ((1 - t i : ℝ) : ℂ) ^ (β - 1))

theorem ofReal_prod_cpow {ι : Type*} (u : Finset ι) {f : ι → ℝ} (hf : ∀ i ∈ u, 0 ≤ f i) (w : ℂ) :
    ((∏ i ∈ u, f i : ℝ) : ℂ) ^ w = ∏ i ∈ u, ((f i : ℝ) : ℂ) ^ w := by
  classical
  induction u using Finset.induction_on with
  | empty => simp
  | insert a u ha ih =>
    rw [prod_insert ha, prod_insert ha, Complex.ofReal_mul,
      Complex.mul_cpow_ofReal_nonneg (hf a (mem_insert_self a u))
        (prod_nonneg fun i hi => hf i (mem_insert_of_mem hi)),
      ih fun i hi => hf i (mem_insert_of_mem hi)]

/-- The Selberg integrand `∏ tᵢ^{a−1}(1 − tᵢ)^{b−1} |Δ(t)|^{2c}`. -/
noncomputable def selbergF (a b c : ℂ) (t : Fin n → ℝ) : ℂ :=
  jacobiWeight a b t * ((|vandermondeDelta t| : ℝ) : ℂ) ^ (2 * c)

theorem selbergF_comp {a b c : ℂ} (σ : Equiv.Perm (Fin n)) (t : Fin n → ℝ) :
    selbergF a b c (t ∘ σ) = selbergF a b c t := by
  rw [selbergF, selbergF, jacobiWeight_comp, abs_vandermondeDelta_comp]

theorem selbergF_eq_ordF {a b c : ℂ} {t : Fin n → ℝ} (ht : t ∈ orderedOpen n) :
    selbergF a b c t = selbergOrdF a b c t := by
  rw [selbergF, selbergOrdF, vandermondeDelta]
  congr 1
  have hpos : ∀ i, ∀ j ∈ Ioi i, 0 < t i - t j := fun i j hj =>
    sub_pos.mpr (ht.2 i j (mem_Ioi.mp hj))
  rw [abs_of_nonneg (prod_nonneg fun i _ => prod_nonneg fun j hj => (hpos i j hj).le),
    ofReal_prod_cpow _ (fun i _ => prod_nonneg fun j hj => (hpos i j hj).le)]
  exact prod_congr rfl fun i _ => ofReal_prod_cpow _ (fun j hj => (hpos i j hj).le) _

/-- Selberg's integral over the cube for `ℜa, ℜb, ℜc > 0`, in the form `n! · osClosed`. -/
theorem selberg_cube_pos {a b c : ℂ} (ha : 0 < a.re) (hb : 0 < b.re) (hc : 0 < c.re) :
    IntegrableOn (selbergF a b c) (Set.Icc (0 : Fin n → ℝ) 1) ∧
      ∫ t in Set.Icc (0 : Fin n → ℝ) 1, selbergF a b c t =
        (n.factorial : ℂ) * osClosed n a b c := by
  obtain ⟨hI, hV⟩ := ordered_selberg n a b c ha hb hc
  have hI' : IntegrableOn (selbergF a b c) (orderedOpen n) :=
    hI.congr_fun (fun t ht => (selbergF_eq_ordF ht).symm) (measurableSet_orderedOpen n)
  obtain ⟨h1, h2⟩ := integral_cube_eq (fun σ t => selbergF_comp σ t) hI'
  refine ⟨h1, ?_⟩
  rw [h2, setIntegral_congr_fun (measurableSet_orderedOpen n) fun t ht => selbergF_eq_ordF ht, hV]

/-! ### DLMF's form -/

/-- The right side of 5.14.4:
`Γ(1+c)^{−n} ∏_{k=1}^m (a+(n−k)c)/(a+b+(2n−k−1)c) ∏_{k=1}^n Γ(a+(n−k)c)Γ(b+(n−k)c)Γ(1+kc)/
Γ(a+b+(2n−k−1)c)` (with `k ↦ k + 1` over `range`). -/
noncomputable def selbergRHS (n m : ℕ) (a b c : ℂ) : ℂ :=
  (Complex.Gamma (1 + c) ^ n)⁻¹ *
    (∏ k ∈ range m, (a + ((n : ℂ) - (k + 1)) * c) / (a + b + (2 * n - (k + 1) - 1) * c)) *
    ∏ k ∈ range n, Complex.Gamma (a + ((n : ℂ) - (k + 1)) * c) *
      Complex.Gamma (b + ((n : ℂ) - (k + 1)) * c) * Complex.Gamma (1 + (k + 1) * c) /
        Complex.Gamma (a + b + (2 * n - (k + 1) - 1) * c)

theorem prod_range_reflect_cast {M : Type*} [CommMonoid M] (g : ℂ → M) (m : ℕ) :
    ∏ k ∈ range m, g ((m : ℂ) - (k + 1)) = ∏ j ∈ range m, g j := by
  rw [← prod_range_reflect (fun j : ℕ => g j) m]
  refine prod_congr rfl fun k hk => ?_
  have hk' := mem_range.mp hk
  congr 1
  rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
  push_cast; ring

theorem factorial_mul_osClosed (n : ℕ) (a b c : ℂ) :
    (n.factorial : ℂ) * osClosed n a b c = selbergRHS n 0 a b c := by
  have hf : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  rw [osClosed, selbergRHS, prod_range_zero, mul_one, prod_div_distrib, prod_mul_distrib,
    prod_mul_distrib]
  rw [prod_range_reflect_cast (fun x => Complex.Gamma (a + x * c)),
    prod_range_reflect_cast (fun x => Complex.Gamma (b + x * c))]
  have hD : ∏ k ∈ range n, Complex.Gamma (a + b + (2 * n - (k + 1) - 1) * c) =
      ∏ j ∈ range n, Complex.Gamma (a + b + (n + j - 1) * c) := by
    rw [← prod_range_reflect_cast (fun x => Complex.Gamma (a + b + (n + x - 1) * c))]
    refine prod_congr rfl fun k _ => ?_
    congr 1; ring
  rw [hD]
  field_simp
  ring_nf
  rw [show (∏ x ∈ range n, Complex.Gamma (a + ↑x * c)) = ∏ x ∈ range n, Complex.Gamma (a + c * ↑x)
    from prod_congr rfl fun x _ => by rw [mul_comm]]
  ring

/-- **DLMF 5.14.4** with `m = 0` (Selberg's integral) for `ℜa, ℜb, ℜc > 0`:
`∫_{[0,1]ⁿ} |Δ(t)|^{2c} ∏ tₖ^{a−1}(1 − tₖ)^{b−1} dt =
Γ(1+c)^{−n} ∏_{k=1}^n Γ(a+(n−k)c)Γ(b+(n−k)c)Γ(1+kc)/Γ(a+b+(2n−k−1)c)`. -/
theorem dlmf_5_14_4_selberg {a b c : ℂ} (ha : 0 < a.re) (hb : 0 < b.re) (hc : 0 < c.re) :
    ∫ t in Set.Icc (0 : Fin n → ℝ) 1, selbergF a b c t = selbergRHS n 0 a b c := by
  rw [(selberg_cube_pos ha hb hc).2, factorial_mul_osClosed]

end Azurite.DLMF
