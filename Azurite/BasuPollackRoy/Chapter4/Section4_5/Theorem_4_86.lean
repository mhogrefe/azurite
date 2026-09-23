import Azurite.BasuPollackRoy.Chapter4.Section4_5.Lemma_4_87
import Azurite.BasuPollackRoy.Chapter4.Section4_5.Lemma_4_88
import Azurite.BasuPollackRoy.Chapter4.Section4_5.Lemma_4_90
import Azurite.BasuPollackRoy.Chapter4.Section4_5.Lemma_4_91
import Azurite.BasuPollackRoy.Chapter4.Section4_5.Definitions
import Azurite.BasuPollackRoy.Chapter4.Section4_5.Definition_4_89
import Azurite.BasuPollackRoy.Chapter4.Section4_4.Theorem_4_72
import Mathlib.RingTheory.Nullstellensatz
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition

/-!
# BPR §4.5, Theorem 4.86: finiteness characterization of zero-dimensional systems

Let `K` be a field of characteristic zero, `C` an algebraically closed field extension of `K`,
and `𝒫` a finite subset of `K[X₁, …, X_k]`. Then `A = K[X]/Ideal(𝒫, K)` is a finite-dimensional
`K`-vector space of positive dimension if and only if the system `𝒫` is zero-dimensional (i.e.
`Zer(𝒫, Cᵏ)` is a non-empty finite set). Moreover the number of solutions is at most `dim_K A`.
-/

namespace Azurite.BPR.Chapter4

open MvPolynomial

variable {k : ℕ} {K : Type*} [Field K]

/-- **Bridge B1.** `Zer(𝒫, Cᵏ) = zeroLocus C (Ideal(𝒫, C))`. -/
theorem zerOfFinset_eq_zeroLocus (C : Type*) [Field C] [Algebra K C]
    (Ps : Finset (MvPolynomial (Fin k) K)) :
    zerOfFinset C Ps = MvPolynomial.zeroLocus C (idealOfPolysExt C Ps) := by
  classical
  ext x
  rw [MvPolynomial.mem_zeroLocus_iff]
  constructor
  · intro hx p hp
    refine aeval_eq_zero_of_mem_idealOfPolys hp x fun q hq => ?_
    obtain ⟨P, hP, rfl⟩ := Finset.mem_image.mp hq
    rw [MvPolynomial.aeval_map_algebraMap]
    exact hx P hP
  · intro hx P hP
    have hmem : MvPolynomial.map (algebraMap K C) P ∈ idealOfPolysExt C Ps :=
      Ideal.subset_span (Finset.mem_coe.mpr (Finset.mem_image_of_mem _ hP))
    have := hx _ hmem
    rwa [MvPolynomial.aeval_map_algebraMap] at this

section Ext

variable (C : Type*) [Field C] [Algebra K C]

/-- Image of a variable under the quotient map `C[X] → Ā`. -/
noncomputable def xiExt (Ps : Finset (MvPolynomial (Fin k) K)) (i : Fin k) : quotPolysExt C Ps :=
  Ideal.Quotient.mk (idealOfPolysExt C Ps) (X i)

theorem mkₐ_X (Ps : Finset (MvPolynomial (Fin k) K)) (i : Fin k) :
    (Ideal.Quotient.mkₐ C (idealOfPolysExt C Ps)) (X i) = xiExt C Ps i := by
  rw [xiExt, Ideal.Quotient.mkₐ_eq_mk]

/-- **Bridge B2.** `Ā` is module-finite generated as a `C`-algebra. -/
instance instFiniteTypeExt (Ps : Finset (MvPolynomial (Fin k) K)) :
    Algebra.FiniteType C (quotPolysExt C Ps) :=
  Algebra.FiniteType.of_surjective
    (Ideal.Quotient.mkₐ C (idealOfPolysExt C Ps))
    (Ideal.Quotient.mkₐ_surjective C (idealOfPolysExt C Ps))

/-- **Bridge B3.** The images of the variables generate `Ā` as a `C`-algebra. -/
theorem adjoin_range_xiExt (Ps : Finset (MvPolynomial (Fin k) K)) :
    Algebra.adjoin C (Set.range (fun i => xiExt C Ps i)) = ⊤ := by
  have hxi : Set.range (fun i => xiExt C Ps i)
      = (Ideal.Quotient.mkₐ C (idealOfPolysExt C Ps)) '' (Set.range X) := by
    rw [← Set.range_comp]
    congr 1
  rw [hxi, ← AlgHom.map_adjoin, MvPolynomial.adjoin_range_X, Algebra.map_top]
  exact (AlgHom.range_eq_top _).mpr (Ideal.Quotient.mkₐ_surjective C (idealOfPolysExt C Ps))

/-- **Bridge B4.** `Ā` is finite-dimensional over `C` iff every variable image is integral. -/
theorem finiteDimensional_ext_iff_isIntegral (Ps : Finset (MvPolynomial (Fin k) K)) :
    FiniteDimensional C (quotPolysExt C Ps) ↔ ∀ i, IsIntegral C (xiExt C Ps i) := by
  constructor
  · intro hfd i
    have : Module.Finite C (quotPolysExt C Ps) := hfd
    exact IsIntegral.of_finite C _
  · intro hint
    have hfin : Module.Finite C (Algebra.adjoin C (Set.range (fun i => xiExt C Ps i))) :=
      Algebra.finite_adjoin_of_finite_of_isIntegral (Set.finite_range _)
        (fun z hz => by obtain ⟨i, rfl⟩ := hz; exact hint i)
    rw [adjoin_range_xiExt] at hfin
    exact Module.Finite.equiv (Subalgebra.topEquiv.toLinearEquiv)

end Ext

/-- Naturality: an `AlgHom` `f : C[X] →ₐ B` commutes with substituting `X i` into a univariate
polynomial. -/
theorem algHom_aeval_X {C : Type*} [CommRing C] {B : Type*} [CommRing B] [Algebra C B]
    (f : MvPolynomial (Fin k) C →ₐ[C] B) (i : Fin k) (Q : Polynomial C) :
    f (Polynomial.aeval (X i) Q) = Polynomial.aeval (f (X i)) Q :=
  (Polynomial.aeval_algHom_apply f (X i) Q).symm

section IntegralFinite

variable (C : Type*) [Field C] [IsAlgClosed C] [Algebra K C]

/-- **Bridge B5.** Every variable image is integral over `C` iff `Zer(𝒫, Cᵏ)` is finite. -/
theorem isIntegral_iff_finite [CharZero K] (Ps : Finset (MvPolynomial (Fin k) K)) :
    (∀ i, IsIntegral C (xiExt C Ps i)) ↔ (zerOfFinset C Ps).Finite := by
  classical
  constructor
  · -- integral ⟹ finite
    intro hint
    -- choose for each `i` a monic `Q i` annihilating `xiExt C Ps i`
    choose Q hQmonic hQzero using hint
    -- the substituted multivariate poly lies in J, so vanishes on Zer
    have hroot : ∀ i, ∀ x ∈ zerOfFinset C Ps, (Q i).eval (x i) = 0 := by
      intro i x hx
      -- `Polynomial.aeval (X i) (Q i)` lies in J
      have hqJ : Polynomial.aeval (X i) (Q i) ∈ idealOfPolysExt C Ps := by
        rw [← Ideal.Quotient.eq_zero_iff_mem]
        have hh : (Ideal.Quotient.mkₐ C (idealOfPolysExt C Ps)) (Polynomial.aeval (X i) (Q i))
            = Polynomial.aeval (xiExt C Ps i) (Q i) := by
          rw [algHom_aeval_X, mkₐ_X]
        rw [Ideal.Quotient.mkₐ_eq_mk] at hh
        rw [hh]
        exact hQzero i
      rw [zerOfFinset_eq_zeroLocus, MvPolynomial.mem_zeroLocus_iff] at hx
      have hax := hx _ hqJ
      rw [algHom_aeval_X (MvPolynomial.aeval x) i (Q i), MvPolynomial.aeval_X,
        Polynomial.coe_aeval_eq_eval] at hax
      exact hax
    -- Zer ⊆ {x | ∀ i, x i ∈ (Q i).roots.toFinset}, which injects into a finite product
    refine Set.Finite.subset (Set.Finite.pi (fun i => (Q i).roots.toFinset.finite_toSet)) ?_
    intro x hx i _
    rw [Finset.mem_coe, Multiset.mem_toFinset]
    exact Polynomial.mem_roots'.mpr ⟨(hQmonic i).ne_zero, hroot i x hx⟩
  · -- finite ⟹ integral
    intro hfin i
    -- monic univariate poly vanishing at all `x i`
    set Qi : Polynomial C := ∏ x ∈ hfin.toFinset, (Polynomial.X - Polynomial.C (x i)) with hQi
    have hQimonic : Qi.Monic :=
      Polynomial.monic_prod_of_monic _ _ (fun x _ => Polynomial.monic_X_sub_C (x i))
    -- its multivariate substitution
    set pi : MvPolynomial (Fin k) C := Polynomial.aeval (X i) Qi with hpi
    -- `pi` vanishes on `Zer(𝒫, Cᵏ)`
    have hpivanish : ∀ y ∈ zerOfFinset C Ps, MvPolynomial.aeval y pi = 0 := by
      intro y hy
      rw [hpi, algHom_aeval_X (MvPolynomial.aeval y) i Qi, MvPolynomial.aeval_X,
        Polynomial.coe_aeval_eq_eval, hQi, Polynomial.eval_prod]
      refine Finset.prod_eq_zero (hfin.mem_toFinset.mpr hy) ?_
      rw [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, sub_self]
    -- so `pi ∈ J.radical`, i.e. `pi^m ∈ J`
    have hpirad : pi ∈ (idealOfPolysExt C Ps).radical := by
      have : pi ∈ MvPolynomial.vanishingIdeal C (zerOfFinset C Ps) :=
        MvPolynomial.mem_vanishingIdeal_iff.mpr hpivanish
      rw [zerOfFinset_eq_zeroLocus,
        MvPolynomial.vanishingIdeal_zeroLocus_eq_radical] at this
      exact this
    obtain ⟨m, hm⟩ := Ideal.mem_radical_iff.mp hpirad
    -- the integral witness is `Qi ^ m`
    refine ⟨Qi ^ m, hQimonic.pow m, ?_⟩
    -- `aeval (xiExt) (Qi^m) = mk (pi^m) = 0`
    have hkey : Polynomial.aeval (xiExt C Ps i) (Qi ^ m)
        = Ideal.Quotient.mk (idealOfPolysExt C Ps) (pi ^ m) := by
      rw [← mkₐ_X C Ps i,
        ← algHom_aeval_X (Ideal.Quotient.mkₐ C (idealOfPolysExt C Ps)) i (Qi ^ m),
        Ideal.Quotient.mkₐ_eq_mk, hpi, map_pow]
    show Polynomial.aeval (xiExt C Ps i) (Qi ^ m) = 0
    rw [hkey, Ideal.Quotient.eq_zero_iff_mem]
    exact hm

/-- **Bridge N.** `Zer(𝒫, Cᵏ)` is non-empty iff `A = K[X]/Ideal(𝒫, K)` is nontrivial. -/
theorem nonempty_iff_nontrivial [CharZero K] (Ps : Finset (MvPolynomial (Fin k) K)) :
    (zerOfFinset C Ps).Nonempty ↔ Nontrivial (quotPolys Ps) := by
  rw [Ideal.Quotient.nontrivial_iff, Ne, Ideal.eq_top_iff_one,
    mem_idealOfPolys_iff, ← theorem_4_72 (C := C) Ps,
    Set.nonempty_iff_ne_empty, not_iff_not]

/-- **BPR Theorem 4.86.** For `K` of characteristic zero and `C` algebraically closed: `A` is a
finite-dimensional `K`-vector space of positive dimension iff `𝒫` is zero-dimensional, and the
number of solutions is bounded by `dim_K A`. -/
theorem theorem_4_86 [CharZero K] (Ps : Finset (MvPolynomial (Fin k) K)) :
    ((FiniteDimensional K (quotPolys Ps) ∧ 0 < Module.finrank K (quotPolys Ps))
        ↔ IsZeroDimensional C Ps)
      ∧ ∀ hfin : (zerOfFinset C Ps).Finite,
          hfin.toFinset.card ≤ Module.finrank K (quotPolys Ps) := by
  -- `FiniteDimensional K A ↔ Zer finite`
  have hfd : FiniteDimensional K (quotPolys Ps) ↔ (zerOfFinset C Ps).Finite := by
    rw [(lemma_4_88 C Ps).2, finiteDimensional_ext_iff_isIntegral, isIntegral_iff_finite]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · -- forward: fin-dim + positive ⟹ zero-dimensional
    rintro ⟨hfindim, hpos⟩
    have := hfindim
    refine ⟨?_, hfd.mp hfindim⟩
    rw [nonempty_iff_nontrivial (C := C)]
    exact Module.finrank_pos_iff.mp hpos
  · -- backward: zero-dimensional ⟹ fin-dim + positive
    rintro ⟨hne, hfin⟩
    have hfindim : FiniteDimensional K (quotPolys Ps) := hfd.mpr hfin
    have := hfindim
    refine ⟨hfindim, ?_⟩
    rw [Module.finrank_pos_iff, ← nonempty_iff_nontrivial (C := C)]
    exact hne
  · -- bound: #Zer ≤ dim_K A
    intro hfin
    have : FiniteDimensional K (quotPolys Ps) := hfd.mpr hfin
    obtain ⟨i, _, hsep⟩ := lemma_4_90 C Ps hfin
    have hli := lemma_4_91 C Ps _ hsep hfin
    have := hli.fintype_card_le_finrank
    rwa [Fintype.card_fin] at this

end IntegralFinite

end Azurite.BPR.Chapter4
