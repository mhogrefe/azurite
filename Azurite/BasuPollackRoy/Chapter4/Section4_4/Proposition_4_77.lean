import Azurite.BasuPollackRoy.Chapter4.Section4_4.FiniteMappingChain
import Azurite.BasuPollackRoy.Chapter4.Section4_4.Proposition_4_76
import Azurite.BasuPollackRoy.Chapter4.Section4_4.Lemma_4_74
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# BPR Proposition 4.77: Noether normalization

Let `𝒫 = {P₁, …, P_s} ⊂ K[X₁, …, X_k]`. Then either `1 ∈ Ideal(𝒫, K)`, or there is a linear
automorphism `v : K^k → K^k` and `k' ≤ k` such that the projection `Π : C^k → C^{k'}` (forgetting
the last `k - k'` coordinates) is a finite mapping from `v(Zer(𝒫, C^k))` onto `C^{k'}` (`C`
algebraically closed).

As elsewhere in §4.4 we single out `X₀`. A linear change `v` is encoded by an algebra
automorphism `σ` with each `σ(Xᵢ)` homogeneous of degree `1` (`IsLinearAlgAut`); the set
`v(Zer(𝒫))` is `Zer(𝒫.image σ)`, and "finite mapping onto `C^{k'}`" is `IsFiniteMappingChain`
down to the empty target set (`Zer(∅) = C^{k'}`).
-/

namespace Azurite.BPR.Chapter4

open MvPolynomial

open scoped Classical

variable {K : Type*} [Field K]

/-- A *linear* algebra automorphism of `K[X₁, …, X_k]`: one sending each variable to a
homogeneous degree-`1` form (i.e. induced by a linear automorphism of `K^k`). -/
def IsLinearAlgAut {k : ℕ} (σ : MvPolynomial (Fin k) K ≃ₐ[K] MvPolynomial (Fin k) K) : Prop :=
  ∀ i, (σ (X i)).IsHomogeneous 1

/-! ### A linear strengthening of Lemma 4.74 -/

/-- The shear `shearMap a i` is homogeneous of degree `1`. -/
private theorem shearMap_isHomogeneous {n : ℕ} (a : Fin n → K) (i : Fin (n + 1)) :
    (shearMap a i).IsHomogeneous 1 := by
  refine Fin.cases ?_ (fun j => ?_) i
  · rw [shearMap_zero]; exact isHomogeneous_X K 0
  · rw [shearMap_succ]
    refine (isHomogeneous_X K _).add ?_
    have hc : (C (a j) : MvPolynomial (Fin (n + 1)) K).IsHomogeneous 0 :=
      isHomogeneous_C (Fin (n + 1)) (a j)
    simpa using hc.mul (isHomogeneous_X K (0 : Fin (n + 1)))

/-- The shear automorphism `shearEquiv a` is linear. -/
private theorem isLinearAlgAut_shearEquiv {n : ℕ} (a : Fin n → K) :
    IsLinearAlgAut (shearEquiv a) := by
  intro i
  rw [shearEquiv_apply, shearHom, aeval_X]
  exact shearMap_isHomogeneous a i

/-- **Linear strengthening of Lemma 4.74.** There is a *linear* shear under which each nonzero
member of `S` becomes quasi-monic in `X₀`. -/
theorem exists_linear_shear [CharZero K] {n : ℕ}
    (S : Finset (MvPolynomial (Fin (n + 1)) K)) :
    ∃ a : Fin n → K, IsLinearAlgAut (shearEquiv a) ∧
      ∀ P ∈ S, P ≠ 0 → IsQuasiMonic (finSuccEquiv K n (shearHom a P)) := by
  classical
  set B : MvPolynomial (Fin n) K := ∏ P ∈ S.filter (· ≠ 0), topForm P with hB
  have hBne : B ≠ 0 := by
    rw [hB, Finset.prod_ne_zero_iff]
    exact fun P hP => topForm_ne_zero (Finset.mem_filter.mp hP).2
  obtain ⟨a, -, haB⟩ := lemma_4_75 B hBne
  refine ⟨a, isLinearAlgAut_shearEquiv a, fun P hP hP0 => ?_⟩
  refine isQuasiMonic_finSuccEquiv_shearHom a ?_
  intro h0
  refine haB ?_
  rw [hB, map_prod]
  exact Finset.prod_eq_zero (Finset.mem_filter.mpr ⟨hP, hP0⟩) h0

/-! ### Lifting a `Fin m` automorphism to `Fin (m+1)`, fixing `X₀` -/

/-- The values for the lift: `X 0 ↦ X 0`, `X i.succ ↦ rename Fin.succ (f (X i))`. -/
private noncomputable def liftMap {m : ℕ} (f : MvPolynomial (Fin m) K →ₐ[K] MvPolynomial (Fin m) K) :
    Fin (m + 1) → MvPolynomial (Fin (m + 1)) K :=
  Fin.cases (X 0) (fun i => rename Fin.succ (f (X i)))

/-- The algebra hom lifting `f : K[X₁,…,X_m] → K[X₁,…,X_m]` to `K[X₀,…,X_m]`, fixing `X₀`. -/
private noncomputable def liftHom {m : ℕ}
    (f : MvPolynomial (Fin m) K →ₐ[K] MvPolynomial (Fin m) K) :
    MvPolynomial (Fin (m + 1)) K →ₐ[K] MvPolynomial (Fin (m + 1)) K :=
  aeval (liftMap f)

@[simp] private theorem liftMap_zero {m : ℕ}
    (f : MvPolynomial (Fin m) K →ₐ[K] MvPolynomial (Fin m) K) : liftMap f 0 = X 0 := by
  simp [liftMap]

@[simp] private theorem liftMap_succ {m : ℕ}
    (f : MvPolynomial (Fin m) K →ₐ[K] MvPolynomial (Fin m) K) (i : Fin m) :
    liftMap f i.succ = rename Fin.succ (f (X i)) := by
  simp [liftMap]

/-- `liftHom (g ∘ f) = liftHom g ∘ liftHom f`. -/
private theorem liftHom_comp {m : ℕ}
    (f g : MvPolynomial (Fin m) K →ₐ[K] MvPolynomial (Fin m) K) :
    (liftHom g).comp (liftHom f) = liftHom (g.comp f) := by
  apply MvPolynomial.algHom_ext
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [liftHom]
  · simp only [liftHom, AlgHom.comp_apply, aeval_X, liftMap_succ]
    -- `liftHom g (rename Fin.succ (f (X j))) = rename Fin.succ (g (f (X j)))`
    rw [aeval_rename]
    have : (liftMap g ∘ Fin.succ) = fun i => rename Fin.succ (g (X i)) := by
      funext i; simp [liftMap]
    rw [this]
    -- aeval (fun i => rename Fin.succ (g (X i))) (f (X j)) = rename Fin.succ (g (f (X j)))
    rw [show (fun i => rename (R := K) Fin.succ (g (X i)))
          = fun i => (rename Fin.succ).comp g (X i) from rfl]
    rw [← comp_aeval]
    simp [aeval_X_left]

/-- `liftHom` of the identity is the identity. -/
private theorem liftHom_id {m : ℕ} :
    liftHom (AlgHom.id K (MvPolynomial (Fin m) K)) = AlgHom.id K _ := by
  apply MvPolynomial.algHom_ext
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [liftHom]
  · simp [liftHom]

/-- The lift of a `Fin m` algebra automorphism to a `Fin (m+1)` algebra automorphism, fixing
`X₀` and acting as `σ'` on the embedded `X₁, …, X_m`. -/
private noncomputable def liftAut {m : ℕ}
    (σ' : MvPolynomial (Fin m) K ≃ₐ[K] MvPolynomial (Fin m) K) :
    MvPolynomial (Fin (m + 1)) K ≃ₐ[K] MvPolynomial (Fin (m + 1)) K :=
  AlgEquiv.ofAlgHom (liftHom σ'.toAlgHom) (liftHom σ'.symm.toAlgHom)
    (by rw [liftHom_comp]; rw [show σ'.toAlgHom.comp σ'.symm.toAlgHom = AlgHom.id K _ from ?_,
          liftHom_id]
        ext x; simp)
    (by rw [liftHom_comp]; rw [show σ'.symm.toAlgHom.comp σ'.toAlgHom = AlgHom.id K _ from ?_,
          liftHom_id]
        ext x; simp)

@[simp] private theorem liftAut_apply {m : ℕ}
    (σ' : MvPolynomial (Fin m) K ≃ₐ[K] MvPolynomial (Fin m) K) (P : MvPolynomial (Fin (m + 1)) K) :
    liftAut σ' P = liftHom σ'.toAlgHom P := rfl

/-- `liftAut σ'` fixes `X₀`. -/
@[simp] private theorem liftAut_X_zero {m : ℕ}
    (σ' : MvPolynomial (Fin m) K ≃ₐ[K] MvPolynomial (Fin m) K) :
    liftAut σ' (X 0) = X 0 := by simp [liftAut, liftHom]

/-- `liftAut σ'` sends `X i.succ` to `rename Fin.succ (σ' (X i))`. -/
@[simp] private theorem liftAut_X_succ {m : ℕ}
    (σ' : MvPolynomial (Fin m) K ≃ₐ[K] MvPolynomial (Fin m) K) (i : Fin m) :
    liftAut σ' (X i.succ) = rename Fin.succ (σ' (X i)) := by simp [liftAut, liftHom]

/-- Each generator image `liftMap σ' i` is homogeneous of degree `1`, when `σ'` is linear. -/
private theorem liftMap_isHomogeneous {m : ℕ}
    {σ' : MvPolynomial (Fin m) K ≃ₐ[K] MvPolynomial (Fin m) K} (hσ' : IsLinearAlgAut σ')
    (i : Fin (m + 1)) : (liftMap σ'.toAlgHom i).IsHomogeneous 1 := by
  refine Fin.cases ?_ (fun j => ?_) i
  · rw [liftMap_zero]; exact isHomogeneous_X K 0
  · rw [liftMap_succ]; exact (hσ' j).rename_isHomogeneous

/-- `liftAut σ'` maps any homogeneous degree-`1` polynomial to a homogeneous degree-`1`
polynomial. -/
private theorem liftAut_isHomogeneous_one {m : ℕ}
    {σ' : MvPolynomial (Fin m) K ≃ₐ[K] MvPolynomial (Fin m) K} (hσ' : IsLinearAlgAut σ')
    {P : MvPolynomial (Fin (m + 1)) K} (hP : P.IsHomogeneous 1) :
    (liftAut σ' P).IsHomogeneous 1 := by
  rw [liftAut_apply, liftHom]
  have := hP.aeval (liftMap σ'.toAlgHom) (liftMap_isHomogeneous hσ')
  simpa using this

/-- The lift of a linear automorphism is linear. -/
private theorem isLinearAlgAut_liftAut {m : ℕ}
    {σ' : MvPolynomial (Fin m) K ≃ₐ[K] MvPolynomial (Fin m) K} (hσ' : IsLinearAlgAut σ') :
    IsLinearAlgAut (liftAut σ') :=
  fun i => liftAut_isHomogeneous_one hσ' (isHomogeneous_X K i)

/-- A composition (as `AlgEquiv.trans`) of linear automorphisms is linear, provided the second
preserves homogeneous degree-`1` polynomials. -/
private theorem isLinearAlgAut_trans {m : ℕ}
    {τ ρ : MvPolynomial (Fin m) K ≃ₐ[K] MvPolynomial (Fin m) K}
    (hτ : IsLinearAlgAut τ)
    (hρ : ∀ P : MvPolynomial (Fin m) K, P.IsHomogeneous 1 → (ρ P).IsHomogeneous 1) :
    IsLinearAlgAut (τ.trans ρ) :=
  fun i => hρ _ (hτ i)

/-! ### The geometric point map of an algebra hom -/

section PointMap

variable {C : Type*} [CommRing C] [Algebra K C]

/-- The point map of an algebra hom `τ` at a point `x`: `i ↦ aeval x (τ (X i))`. -/
noncomputable def ptMap {N : ℕ} (τ : MvPolynomial (Fin N) K →ₐ[K] MvPolynomial (Fin N) K)
    (x : Fin N → C) : Fin N → C := fun i => aeval x (τ (X i))

/-- `aeval x (τ P) = aeval (ptMap τ x) P`. -/
theorem aeval_comp_algHom {N : ℕ}
    (τ : MvPolynomial (Fin N) K →ₐ[K] MvPolynomial (Fin N) K) (x : Fin N → C)
    (P : MvPolynomial (Fin N) K) :
    aeval x (τ P) = aeval (ptMap τ x) P := by
  have key : (aeval x : MvPolynomial (Fin N) K →ₐ[K] C).comp τ
      = (aeval (ptMap τ x) : MvPolynomial (Fin N) K →ₐ[K] C) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp [ptMap]
  exact DFunLike.congr_fun key P

/-- Membership in the zero set of an image: `x ∈ Zer(Ps.image τ) ↔ ptMap τ x ∈ Zer(Ps)`. -/
theorem mem_zerOfFinset_image {N : ℕ} [DecidableEq (MvPolynomial (Fin N) K)]
    (τ : MvPolynomial (Fin N) K →ₐ[K] MvPolynomial (Fin N) K)
    (Ps : Finset (MvPolynomial (Fin N) K)) (x : Fin N → C) :
    x ∈ zerOfFinset C (Ps.image τ) ↔ ptMap τ x ∈ zerOfFinset C Ps := by
  unfold zerOfFinset
  simp only [Set.mem_ofPred_eq, Finset.mem_image, forall_exists_index, and_imp]
  constructor
  · intro h p hp
    rw [← aeval_comp_algHom]
    exact h (τ p) p hp rfl
  · intro h _ p hp hpq
    rw [← hpq, aeval_comp_algHom]
    exact h p hp

/-- Membership in the zero set of an image by an algebra *equiv*. -/
theorem mem_zerOfFinset_image_equiv {N : ℕ} [DecidableEq (MvPolynomial (Fin N) K)]
    (σ : MvPolynomial (Fin N) K ≃ₐ[K] MvPolynomial (Fin N) K)
    (Ps : Finset (MvPolynomial (Fin N) K)) (x : Fin N → C) :
    x ∈ zerOfFinset C (Ps.image σ) ↔ ptMap σ.toAlgHom x ∈ zerOfFinset C Ps := by
  rw [show (Ps.image σ) = Ps.image σ.toAlgHom from rfl]
  exact mem_zerOfFinset_image σ.toAlgHom Ps x

/-- For an algebra equiv `σ`, `ptMap σ.symm` is a left inverse of `ptMap σ`. -/
private theorem ptMap_symm_ptMap {N : ℕ}
    (σ : MvPolynomial (Fin N) K ≃ₐ[K] MvPolynomial (Fin N) K) (x : Fin N → C) :
    ptMap σ.symm.toAlgHom (ptMap σ.toAlgHom x) = x := by
  funext i
  show aeval (ptMap σ.toAlgHom x) (σ.symm (X i)) = x i
  rw [← aeval_comp_algHom]
  simp

/-- For an algebra equiv `σ`, `ptMap σ` is a left inverse of `ptMap σ.symm`. -/
private theorem ptMap_ptMap_symm {N : ℕ}
    (σ : MvPolynomial (Fin N) K ≃ₐ[K] MvPolynomial (Fin N) K) (x : Fin N → C) :
    ptMap σ.toAlgHom (ptMap σ.symm.toAlgHom x) = x := by
  funext i
  show aeval (ptMap σ.symm.toAlgHom x) (σ (X i)) = x i
  rw [← aeval_comp_algHom]
  simp

/-- The point map of `liftAut σ'` intertwines `Fin.tail` with the point map of `σ'`:
`Fin.tail (ptMap (liftAut σ') x) = ptMap σ' (Fin.tail x)`. -/
private theorem tail_ptMap_liftAut {m : ℕ}
    (σ' : MvPolynomial (Fin m) K ≃ₐ[K] MvPolynomial (Fin m) K) (x : Fin (m + 1) → C) :
    Fin.tail (ptMap (liftAut σ').toAlgHom x) = ptMap σ'.toAlgHom (Fin.tail x) := by
  funext i
  show aeval x (liftAut σ' (X i.succ)) = aeval (Fin.tail x) (σ' (X i))
  rw [liftAut_X_succ, aeval_rename]
  rfl

/-- The point map of `liftAut σ'` fixes the first coordinate. -/
private theorem ptMap_liftAut_zero {m : ℕ}
    (σ' : MvPolynomial (Fin m) K ≃ₐ[K] MvPolynomial (Fin m) K) (x : Fin (m + 1) → C) :
    ptMap (liftAut σ').toAlgHom x 0 = x 0 := by
  show aeval x (liftAut σ' (X 0)) = x 0
  rw [liftAut_X_zero]; simp

end PointMap

/-! ### Quasi-monic is preserved under the lift -/

/-- `finSuccEquiv K m (rename Fin.succ q) = Polynomial.C q`. -/
private theorem finSuccEquiv_rename_succ' {m : ℕ} (q : MvPolynomial (Fin m) K) :
    finSuccEquiv K m (MvPolynomial.rename Fin.succ q) = Polynomial.C q := by
  have key : ((finSuccEquiv K m).toRingHom.comp (MvPolynomial.rename Fin.succ).toRingHom) =
      (Polynomial.C : MvPolynomial (Fin m) K →+* _) := by
    apply MvPolynomial.ringHom_ext
    · intro r; simp [finSuccEquiv_apply]
    · intro i; simp [finSuccEquiv_apply]
  have := DFunLike.congr_fun key q
  simpa using this

/-- `finSuccEquiv` intertwines `liftAut σ'` with the coefficient-wise application of `σ'`:
`finSuccEquiv (liftAut σ' P) = Polynomial.map σ' (finSuccEquiv P)`. -/
private theorem finSuccEquiv_liftAut {m : ℕ}
    (σ' : MvPolynomial (Fin m) K ≃ₐ[K] MvPolynomial (Fin m) K) (P : MvPolynomial (Fin (m + 1)) K) :
    finSuccEquiv K m (liftAut σ' P) =
      Polynomial.map σ'.toAlgHom.toRingHom (finSuccEquiv K m P) := by
  have key : ((finSuccEquiv K m).toAlgHom.toRingHom.comp (liftAut σ').toAlgHom.toRingHom) =
      ((Polynomial.mapRingHom σ'.toAlgHom.toRingHom).comp
        (finSuccEquiv K m).toAlgHom.toRingHom) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
        AlgEquiv.coe_toAlgHom]
      rw [show ((liftAut σ') (C r)) = C r from by simp [liftAut, liftHom]]
      rw [show (finSuccEquiv K m) (C r) = Polynomial.C (C r) from by simp [finSuccEquiv_apply]]
      rw [Polynomial.coe_mapRingHom, Polynomial.map_C]
      simp only [RingHom.coe_coe, AlgEquiv.coe_toAlgHom]
      rw [show σ' (C r) = C r from by rw [← MvPolynomial.algebraMap_eq, AlgEquiv.commutes,
        MvPolynomial.algebraMap_eq]]
    · intro j
      simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
        AlgEquiv.coe_toAlgHom]
      refine Fin.cases ?_ (fun i => ?_) j
      · rw [liftAut_X_zero, finSuccEquiv_X_zero]
        simp [Polynomial.coe_mapRingHom]
      · rw [liftAut_X_succ, finSuccEquiv_rename_succ', finSuccEquiv_X_succ]
        simp [Polynomial.coe_mapRingHom]
  have := DFunLike.congr_fun key P
  simpa [Polynomial.coe_mapRingHom] using this

/-- The lift `liftAut σ'` preserves quasi-monicity (in `X₀`). -/
private theorem isQuasiMonic_liftAut {m : ℕ}
    (σ' : MvPolynomial (Fin m) K ≃ₐ[K] MvPolynomial (Fin m) K)
    {P : MvPolynomial (Fin (m + 1)) K} (hqm : IsQuasiMonic (finSuccEquiv K m P)) :
    IsQuasiMonic (finSuccEquiv K m (liftAut σ' P)) := by
  obtain ⟨hne, c, hc⟩ := hqm
  have hcne : c ≠ 0 := IsQuasiMonic.leadingCoeff_const_ne_zero ⟨hne, c, hc⟩ c hc
  rw [finSuccEquiv_liftAut]
  have hinj : Function.Injective σ'.toAlgHom.toRingHom := σ'.injective
  -- `σ' (C c) = C c`, which is the leading coeff and is nonzero.
  have hσC : σ'.toAlgHom.toRingHom (MvPolynomial.C c) = MvPolynomial.C c := by
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgEquiv.coe_toAlgHom]
    rw [← MvPolynomial.algebraMap_eq, AlgEquiv.commutes, MvPolynomial.algebraMap_eq]
  have hleadne : σ'.toAlgHom.toRingHom (finSuccEquiv K m P).leadingCoeff ≠ 0 := by
    rw [hc, hσC]
    simp [hcne]
  refine ⟨?_, c, ?_⟩
  · intro h
    exact hne ((Polynomial.map_eq_zero_iff hinj).mp h)
  · rw [Polynomial.leadingCoeff_map_of_leadingCoeff_ne_zero σ'.toAlgHom.toRingHom hleadne, hc, hσC]

/-! ### The change-of-variables congruence for single-step finite mappings -/

/-- The inverse of `liftAut σ'` is `liftAut σ'.symm`. -/
private theorem liftAut_symm {m : ℕ}
    (σ' : MvPolynomial (Fin m) K ≃ₐ[K] MvPolynomial (Fin m) K) :
    (liftAut σ').symm = liftAut σ'.symm := by
  ext P
  rfl

/-- **Change of variables for a single-step finite mapping.** If `Fin.tail` is a finite mapping
from `Zer(Pw)` to `Zer(Proj)`, then it is also a finite mapping from `Zer(Pw.image (liftAut σ'))`
to `Zer(Proj.image σ')`, for a linear `σ'`. -/
private theorem isFiniteMapping_congr_lift {m : ℕ}
    {C : Type*} [Field C] [Algebra K C]
    (σ' : MvPolynomial (Fin m) K ≃ₐ[K] MvPolynomial (Fin m) K)
    {Pw : Finset (MvPolynomial (Fin (m + 1)) K)} {Proj : Finset (MvPolynomial (Fin m) K)}
    (h : IsFiniteMapping C Pw Proj) :
    IsFiniteMapping C (Pw.image (liftAut σ')) (Proj.image σ') := by
  classical
  obtain ⟨hsurj, P₀, hP₀mem, hP₀qm⟩ := h
  refine ⟨?_, liftAut σ' P₀, Finset.mem_image_of_mem _ hP₀mem, isQuasiMonic_liftAut σ' hP₀qm⟩
  -- SurjOn: given a target in `Zer(Proj.image σ')`, find a source.
  rintro target htarget
  rw [mem_zerOfFinset_image_equiv] at htarget
  -- `ptMap σ' target ∈ Zer(Proj)`; pull back via the original surjection.
  obtain ⟨z, hz, hztail⟩ := hsurj htarget
  -- The source is the image of `z` under the inverse point map of `liftAut σ'`.
  refine ⟨ptMap (liftAut σ').symm.toAlgHom z, ?_, ?_⟩
  · rw [mem_zerOfFinset_image_equiv, ptMap_ptMap_symm]; exact hz
  · -- `Fin.tail source = target`
    rw [liftAut_symm, tail_ptMap_liftAut, hztail, ptMap_symm_ptMap]

/-! ### Helpers for the main induction -/

/-- Transport an `IsFiniteMapping` along an equality of the codimension. -/
private theorem isFiniteMapping_cast {C : Type*} [Field C] [Algebra K C] {n n' : ℕ} (e : n = n')
    {P : Finset (MvPolynomial (Fin (n + 1)) K)} {Q : Finset (MvPolynomial (Fin n) K)}
    (h : IsFiniteMapping C P Q) : IsFiniteMapping C (e ▸ P) (e ▸ Q) := by
  subst e; exact h

/-- The identity automorphism is linear. -/
private theorem isLinearAlgAut_refl {k : ℕ} :
    IsLinearAlgAut (AlgEquiv.refl : MvPolynomial (Fin k) K ≃ₐ[K] _) :=
  fun i => by simpa using isHomogeneous_X K i

/-- If every member of `T` is the zero polynomial, then `Zer(T) = univ`. -/
private theorem zerOfFinset_eq_univ_of_forall_zero {C : Type*} [CommRing C] [Algebra K C] {k : ℕ}
    {T : Finset (MvPolynomial (Fin k) K)} (h : ∀ p ∈ T, p = 0) :
    zerOfFinset C T = Set.univ := by
  rw [Set.eq_univ_iff_forall]
  intro x p hp
  rw [h p hp]; simp

/-- **BPR Proposition 4.77 (Noether normalization).** For a finite `𝒫 ⊂ K[X₁, …, X_k]` and `C`
automorphism `σ` with `σ(Xᵢ)` linear) and `k' ≤ k` such that the projection forgetting the last
`k - k'` coordinates is a finite mapping from `Zer(𝒫.image σ, C^k)` (`= v(Zer(𝒫))`) onto
`C^{k'}`. -/
theorem proposition_4_77 [CharZero K] {C : Type*} [Field C] [IsAlgClosed C] [Algebra K C] {k : ℕ}
    (Ps : Finset (MvPolynomial (Fin k) K)) :
    (1 : MvPolynomial (Fin k) K) ∈ idealOfPolys Ps ∨
      ∃ (k' d : ℕ) (hk : k = k' + d)
        (σ : MvPolynomial (Fin k) K ≃ₐ[K] MvPolynomial (Fin k) K)
        (T : Finset (MvPolynomial (Fin k') K)),
        IsLinearAlgAut σ ∧ zerOfFinset C T = Set.univ ∧
          IsFiniteMappingChain C k' d (hk ▸ (Ps.image σ)) T := by
  classical
  induction k with
  | zero =>
    -- `Fin 0`: a nonzero member is a unit ⇒ LEFT; otherwise all zero ⇒ RIGHT (k'=0,d=0).
    by_cases hall : ∀ p ∈ Ps, p = 0
    · refine Or.inr ⟨0, 0, rfl, AlgEquiv.refl, Ps.image (AlgEquiv.refl :
        MvPolynomial (Fin 0) K ≃ₐ[K] _), isLinearAlgAut_refl, ?_, ?_⟩
      · apply zerOfFinset_eq_univ_of_forall_zero
        intro p hp
        obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
        simpa using hall q hq
      · simp
    · -- some nonzero `p`; over `Fin 0` it is a unit, so `1 ∈ ideal`.
      push Not at hall
      obtain ⟨p, hp, hp0⟩ := hall
      refine Or.inl ?_
      have hunit : IsUnit p := by
        set e := MvPolynomial.isEmptyAlgEquiv K (Fin 0) with he
        have hep : e p ≠ 0 := fun h => hp0 (e.injective (by simpa using h))
        have : IsUnit (e p) := isUnit_iff_ne_zero.mpr hep
        have := this.map e.symm.toAlgHom
        simpa using this
      rw [idealOfPolys, ← Ideal.eq_top_iff_one]
      exact Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span (Finset.mem_coe.mpr hp)) hunit
  | succ m IH =>
    by_cases hall : ∀ p ∈ Ps, p = 0
    · -- All zero: RIGHT with `k' = m+1`, `d = 0`, identity.
      refine Or.inr ⟨m + 1, 0, rfl, AlgEquiv.refl, Ps.image (AlgEquiv.refl :
        MvPolynomial (Fin (m + 1)) K ≃ₐ[K] _), isLinearAlgAut_refl, ?_, ?_⟩
      · apply zerOfFinset_eq_univ_of_forall_zero
        intro p hp
        obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
        simpa using hall q hq
      · simp
    · -- Some nonzero `P₁`.
      push Not at hall
      obtain ⟨P₁, hP₁mem, hP₁0⟩ := hall
      -- Linear shear making `P₁` quasi-monic.
      obtain ⟨a, hlin, hqm⟩ := exists_linear_shear Ps
      set w : MvPolynomial (Fin (m + 1)) K ≃ₐ[K] _ := shearEquiv a with hw
      have hqm₁ : IsQuasiMonic (finSuccEquiv K m (shearHom a P₁)) := hqm P₁ hP₁mem hP₁0
      -- `Pw = Ps.image w`.
      set Pw : Finset (MvPolynomial (Fin (m + 1)) K) := Ps.image w with hPw
      -- `Pw = insert (w P₁) ((Ps.erase P₁).image w)`.
      have hPwins : Pw = insert (w P₁) ((Ps.erase P₁).image w) := by
        rw [hPw, ← Finset.image_insert, Finset.insert_erase hP₁mem]
      -- Apply Proposition 4.76.
      have hwP₁ : w P₁ = shearHom a P₁ := by rw [hw, shearEquiv_apply]
      obtain ⟨Proj, hProjIdeal, hProjImage, hProjFM⟩ :=
        proposition_4_76 (C := C) (w P₁) (((Ps.erase P₁).image w).toList)
          (by rw [hwP₁]; exact hqm₁)
      -- `insert (w P₁) (toList).toFinset = Pw`.
      have hinsList : insert (w P₁) (((Ps.erase P₁).image w).toList).toFinset = Pw := by
        rw [Finset.toList_toFinset, hPwins]
      rw [hinsList] at hProjIdeal hProjImage hProjFM
      -- IH applied to `Proj`.
      rcases IH Proj with hPone | hPright
      · -- `1 ∈ Ideal(Proj)` ⟹ `1 ∈ Ideal(Ps)`.
        refine Or.inl ?_
        -- First `1 ∈ Ideal(Pw)` via clause (1).
        have h1Pw : (1 : MvPolynomial (Fin (m + 1)) K) ∈ idealOfPolys Pw := by
          rw [mem_idealOfPolys_iff] at hPone
          obtain ⟨A, hA⟩ := hPone
          have : MvPolynomial.rename (Fin.succ) (1 : MvPolynomial (Fin m) K)
              ∈ idealOfPolys Pw := by
            rw [← hA, map_sum]
            apply Ideal.sum_mem
            intro p hp
            rw [map_mul]
            exact Ideal.mul_mem_left _ _ (hProjIdeal p hp)
          simpa using this
        -- Then `1 ∈ Ideal(Ps.image w) = (Ideal Ps).map w`, so `1 ∈ Ideal Ps`.
        rw [hPw] at h1Pw
        rw [idealOfPolys, Finset.coe_image, ← Ideal.map_span, ← idealOfPolys] at h1Pw
        have := Ideal.mem_map_iff_of_surjective w.toRingHom w.surjective |>.mp h1Pw
        obtain ⟨y, hy, hwy⟩ := this
        have hy1 : y = 1 := by
          have := w.injective (a₁ := y) (a₂ := 1) (by simpa using hwy)
          exact this
        rwa [hy1] at hy
      · -- IH RIGHT: build the longer chain.
        obtain ⟨k', d', hk', σ', T', hlinσ', hTuniv, hchain⟩ := hPright
        refine Or.inr ⟨k', d' + 1, by omega, (w.trans (liftAut σ')), T', ?_, hTuniv, ?_⟩
        · -- linearity of `σ = w.trans (liftAut σ')`
          exact isLinearAlgAut_trans hlin (fun P hP => liftAut_isHomogeneous_one hlinσ' hP)
        · -- the chain
          -- First: `Ps.image (w.trans (liftAut σ')) = Pw.image (liftAut σ')`.
          have himg : Ps.image (w.trans (liftAut σ')) = Pw.image (liftAut σ') := by
            rw [hPw, Finset.image_image]
            rfl
          -- The single-step finite mapping after change of variables.
          have hFM : IsFiniteMapping C (Pw.image (liftAut σ')) (Proj.image σ') :=
            isFiniteMapping_congr_lift σ' hProjFM
          -- Now substitute `m = k' + d'` to clear the casts.
          subst hk'
          rw [isFiniteMappingChain_succ]
          refine ⟨Proj.image σ', ?_, hchain⟩
          rw [himg]
          exact hFM

end Azurite.BPR.Chapter4
