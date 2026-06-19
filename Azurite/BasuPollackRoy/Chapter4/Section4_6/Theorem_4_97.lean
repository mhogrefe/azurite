import Azurite.BasuPollackRoy.Chapter4.Section4_6.MultiplicationMap
import Azurite.BasuPollackRoy.Chapter4.Section4_5.Theorem_4_94
import Azurite.BasuPollackRoy.Chapter4.Section4_5.Theorem_4_86
import Azurite.BasuPollackRoy.Chapter4.Section4_5.Proposition_4_92
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.LinearAlgebra.Eigenspace.Zero
import Mathlib.Algebra.CharP.Algebra
import Mathlib.RingTheory.Artinian.Ring
import Mathlib.RingTheory.KrullDimension.Zero
import Mathlib.RingTheory.HopkinsLevitzki

/-!
# BPR §4.6, Theorem 4.97: the characteristic polynomial of `L_f`

The characteristic polynomial of the multiplication map `L_f` on `Ā` factors as
`∏_{x ∈ Zer} (X − f(x))^{μ(x)}`.
-/

namespace Azurite.BPR.Chapter4

open MvPolynomial
open scoped Classical

variable {k : ℕ} {K : Type*} [Field K]

section PiCharpoly

variable {R : Type*} [CommRing R] [IsDomain R]

/-- The block-diagonal endomorphism `(z i) ↦ (g i (z i))` of a finite product of modules. -/
noncomputable def blockEnd {ι : Type*} (M : ι → Type*)
    [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)] (g : ∀ i, Module.End R (M i)) :
    Module.End R (∀ i, M i) :=
  LinearMap.pi (fun i => (g i).comp (LinearMap.proj i))

omit [IsDomain R] in
theorem blockEnd_apply {ι : Type*} (M : ι → Type*)
    [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)] (g : ∀ i, Module.End R (M i))
    (z : ∀ i, M i) (i : ι) : blockEnd M g z i = g i (z i) := rfl

/-- Characteristic polynomial of a block-diagonal endomorphism of a finite product of
finite free modules equals the product of the characteristic polynomials of the blocks. -/
theorem charpoly_pi_eq_prod {ι : Type*} [Fintype ι] (M : ι → Type*)
    [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)] [∀ i, Module.Finite R (M i)]
    [∀ i, Module.Free R (M i)] (g : ∀ i, Module.End R (M i)) :
    (blockEnd M g).charpoly = ∏ i, (g i).charpoly := by
  classical
  -- Property over the index type, quantified over all module families.
  let P : (ι : Type _) → [Fintype ι] → Prop := fun ι _ =>
    ∀ (M : ι → Type _) [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
      [∀ i, Module.Finite R (M i)] [∀ i, Module.Free R (M i)] (g : ∀ i, Module.End R (M i)),
      (blockEnd M g).charpoly = ∏ i, (g i).charpoly
  refine Fintype.induction_empty_option (P := P) ?_ ?_ ?_ ι M g
  · -- transport along an equivalence `α ≃ β`
    intro α β _ e hα M _ _ _ _ g
    haveI : Fintype α := Fintype.ofEquiv β e.symm
    -- reindex the family along `e`
    set φ : ((i' : α) → M (e i')) ≃ₗ[R] ((i : β) → M i) := LinearEquiv.piCongrLeft R M e with hφ
    have happ : ∀ (f : (i' : α) → M (e i')) (a : α), φ f (e a) = f a := by
      intro f a
      exact Equiv.piCongrLeft_apply_apply M e f a
    have hsymm : ∀ (f : (i : β) → M i) (a : α), φ.symm f a = f (e a) := by
      intro f a
      have : φ (φ.symm f) (e a) = f (e a) := by rw [LinearEquiv.apply_symm_apply]
      rw [happ] at this
      exact this
    -- conjugating the reindexed block map by `φ` recovers `blockEnd M g`
    have hconj : φ.conj (blockEnd (fun i' => M (e i')) (fun i' => g (e i')))
        = blockEnd M g := by
      apply LinearMap.ext
      intro f
      apply funext
      intro i
      obtain ⟨a, rfl⟩ := e.surjective i
      rw [LinearEquiv.conj_apply]
      show φ (blockEnd (fun i' => M (e i')) (fun i' => g (e i')) (φ.symm f)) (e a)
          = blockEnd M g f (e a)
      rw [happ, blockEnd_apply, blockEnd_apply, hsymm]
    have hαspec := hα (fun i' => M (e i')) (fun i' => g (e i'))
    rw [← hconj, LinearEquiv.charpoly_conj, hαspec]
    -- `∏ i':α, charpoly (g (e i')) = ∏ i:β, charpoly (g i)`
    exact Finset.prod_equiv e (by simp) (fun i _ => rfl)
  · -- empty
    intro M _ _ _ _ g
    rw [Finset.univ_eq_empty, Finset.prod_empty]
    exact (LinearMap.charpoly_monic _).natDegree_eq_zero.mp
      (by rw [LinearMap.charpoly_natDegree]; exact Module.finrank_zero_of_subsingleton)
  · -- option
    intro α _ hα M _ _ _ _ g
    set e : ((i : Option α) → M i) ≃ₗ[R] M none × ((i : α) → M (some i)) :=
      LinearEquiv.piOptionEquivProd R with he
    -- conjugating the block map by `e` gives the binary `prodMap`.
    have hconj : e.conj (blockEnd M g)
        = (g none).prodMap (blockEnd (fun i => M (some i)) (fun i => g (some i))) := by
      apply LinearMap.ext
      rintro ⟨a, z⟩
      rw [LinearEquiv.conj_apply]
      have hsymm : e.symm (a, z) = fun o => Option.casesOn o a z := rfl
      apply Prod.ext
      · show (blockEnd M g (e.symm (a, z))) none = g none a
        rw [hsymm]; rfl
      · show (fun i => (blockEnd M g (e.symm (a, z))) (some i))
            = blockEnd (fun i => M (some i)) (fun i => g (some i)) z
        funext i
        rw [hsymm]; rfl
    rw [← LinearEquiv.charpoly_conj e (blockEnd M g), hconj,
      LinearMap.charpoly_prodMap, hα, Fintype.prod_option]

end PiCharpoly

section Factor

variable [CharZero K] {C : Type*} [Field C] [IsAlgClosed C] [Algebra K C]
  (Ps : Finset (MvPolynomial (Fin k) K)) (x : Fin k → C) (hx : x ∈ zerOfFinset C Ps)

attribute [local instance] algebraLocalizationAtPoint

omit [CharZero K] [IsAlgClosed C] in
/-- `Ā` is an Artinian ring (being a finite-dimensional `C`-algebra over the field `C`). -/
theorem isArtinianRing_quotPolysExt [Module.Finite C (quotPolysExt C Ps)] :
    IsArtinianRing (quotPolysExt C Ps) :=
  IsArtinianRing.of_finite C (quotPolysExt C Ps)

omit [CharZero K] [IsAlgClosed C] in
/-- The localization map `Ā → Ā_x` is surjective (since `Ā` is Artinian). -/
theorem algebraMap_localizationAtPoint_surjective [Module.Finite C (quotPolysExt C Ps)] :
    Function.Surjective
      (algebraMap (quotPolysExt C Ps) (localizationAtPoint C Ps x hx)) := by
  haveI := isArtinianRing_quotPolysExt Ps (C := C)
  haveI : IsLocalization (evalAtPointSubmonoid C Ps x hx)
      (Localization (evalAtPointSubmonoid C Ps x hx)) := Localization.isLocalization
  exact IsArtinianRing.localization_surjective (evalAtPointSubmonoid C Ps x hx)
    (Localization (evalAtPointSubmonoid C Ps x hx))

/-- `IsScalarTower C Ā Ā_x`: the `C`-algebra structure on `Ā_x` factors through `Ā`. -/
instance isScalarTower_localizationAtPoint :
    IsScalarTower C (quotPolysExt C Ps) (localizationAtPoint C Ps x hx) :=
  ⟨fun c b z => by
    rw [show c • b = algebraMap C (quotPolysExt C Ps) c * b from Algebra.smul_def c b]
    simp only [Algebra.smul_def]
    rw [map_mul, mul_assoc]
    rfl⟩

/-- `Ā_x` is a finite-dimensional `C`-vector space. -/
instance module_finite_localizationAtPoint [Module.Finite C (quotPolysExt C Ps)] :
    Module.Finite C (localizationAtPoint C Ps x hx) :=
  Module.Finite.of_surjective
    ((IsScalarTower.toAlgHom C (quotPolysExt C Ps)
        (localizationAtPoint C Ps x hx)).toLinearMap)
    (algebraMap_localizationAtPoint_surjective Ps x hx)

omit [IsAlgClosed C] [CharZero K] in
/-- The image in `Ā_x` of an element of `Ā` that vanishes at `x` is nilpotent. -/
theorem isNilpotent_algebraMap_localization_of_evalBar_eq_zero
    [Module.Finite C (quotPolysExt C Ps)] (w : quotPolysExt C Ps)
    (hw : evalBar C Ps x hx w = 0) :
    IsNilpotent (algebraMap (quotPolysExt C Ps) (localizationAtPoint C Ps x hx) w) := by
  haveI := isLocalRing_localizationAtPoint C Ps x hx
  haveI := isArtinianRing_quotPolysExt Ps (C := C)
  haveI : IsArtinianRing (localizationAtPoint C Ps x hx) :=
    inferInstanceAs (IsArtinianRing (Localization (evalAtPointSubmonoid C Ps x hx)))
  haveI : Ring.KrullDimLE 0 (localizationAtPoint C Ps x hx) :=
    (isArtinianRing_iff_krullDimLE_zero).mp inferInstance
  -- membership in the maximal ideal of the local Artinian ring `Ā_x`
  letI hP : (RingHom.ker (evalBar C Ps x hx)).IsPrime := RingHom.ker_isPrime (evalBar C Ps x hx)
  haveI : IsLocalization.AtPrime (localizationAtPoint C Ps x hx)
      (RingHom.ker (evalBar C Ps x hx)) :=
    inferInstanceAs (IsLocalization.AtPrime
      (Localization (RingHom.ker (evalBar C Ps x hx)).primeCompl)
      (RingHom.ker (evalBar C Ps x hx)))
  rw [Ring.KrullDimLE.isNilpotent_iff_mem_maximalIdeal,
    IsLocalization.AtPrime.to_map_mem_maximal_iff (localizationAtPoint C Ps x hx)
      (RingHom.ker (evalBar C Ps x hx)) w, RingHom.mem_ker]
  exact hw

omit [IsAlgClosed C] [CharZero K] in
/-- **BPR Theorem 4.97 (per-factor).** The characteristic polynomial of `L_{f,x}` is
`(X − f(x))^{μ(x)}`. -/
theorem charpoly_mulMapLoc_eq [Module.Finite C (quotPolysExt C Ps)]
    (f : quotPolysExt C Ps) :
    (mulMapLoc C Ps x hx f).charpoly
      = (Polynomial.X - Polynomial.C (evalBar C Ps x hx f)) ^ multiplicityOfZero C Ps x hx := by
  set c := evalBar C Ps x hx f with hc
  -- the shifted element `w = f - C c` vanishes at `x`.
  set w : quotPolysExt C Ps := f - algebraMap C (quotPolysExt C Ps) c with hw
  have hwzero : evalBar C Ps x hx w = 0 := by
    rw [hw, map_sub, evalBar_algebraMap, ← hc, sub_self]
  -- `L_{f,x} − c • 1` is multiplication by the (nilpotent) image of `w`.
  have hshift : mulMapLoc C Ps x hx f - c • 1
      = LinearMap.mulLeft C
          (algebraMap (quotPolysExt C Ps) (localizationAtPoint C Ps x hx) w) := by
    apply LinearMap.ext
    intro z
    rw [LinearMap.sub_apply, mulMapLoc_apply, LinearMap.smul_apply, Module.End.one_apply,
      LinearMap.mulLeft_apply, hw, map_sub, sub_mul]
    congr 1
  -- it is nilpotent
  have hnil : IsNilpotent (mulMapLoc C Ps x hx f - c • 1) := by
    rw [hshift, LinearMap.isNilpotent_mulLeft_iff]
    exact isNilpotent_algebraMap_localization_of_evalBar_eq_zero Ps x hx w hwzero
  -- hence its charpoly is `X ^ μ(x)`.
  have hXpow : (mulMapLoc C Ps x hx f - c • 1).charpoly
      = Polynomial.X ^ multiplicityOfZero C Ps x hx :=
    hnil.charpoly_eq_X_pow_finrank
  -- shift back: `charpoly (L_{f,x}).comp (X + C c) = X ^ μ(x)`.
  rw [LinearMap.charpoly_sub_smul] at hXpow
  -- compose with `X - C c`.
  have key := congrArg (fun p => Polynomial.comp p (Polynomial.X - Polynomial.C c)) hXpow
  simp only [Polynomial.comp_assoc] at key
  have hcancel : (Polynomial.X + Polynomial.C c).comp (Polynomial.X - Polynomial.C c)
      = Polynomial.X := by
    simp [Polynomial.add_comp]
  rw [hcancel, Polynomial.comp_X] at key
  rw [key, Polynomial.pow_comp, Polynomial.X_comp]

end Factor

section Main

variable [CharZero K] {C : Type*} [Field C] [IsAlgClosed C] [Algebra K C]

attribute [local instance] algebraLocalizationAtPoint

/-- An element of `Ā` that is nonzero at every zero of `𝒫` is a unit. The candidate inverse is
`u = ∑ₓ eₓ · t(x)⁻¹`: then `t · u` evaluates to `1` at every zero, so `t · u − 1` is nilpotent
(Proposition 4.92's idempotents + the Nullstellensatz) and `t · u` is a unit. -/
theorem isUnit_of_evalBar_ne_zero (Ps : Finset (MvPolynomial (Fin k) K))
    (hfin : (zerOfFinset C Ps).Finite) (t : quotPolysExt C Ps)
    (ht : ∀ (x : Fin k → C) (hx : x ∈ zerOfFinset C Ps), evalBar C Ps x hx t ≠ 0) :
    IsUnit t := by
  classical
  haveI : CharZero C := charZero_of_injective_algebraMap (algebraMap K C).injective
  obtain ⟨e, _hsum, _horth, _hidem, hval1, hval0⟩ := proposition_4_92 (C := C) Ps hfin
  set u : quotPolysExt C Ps :=
    ∑ i : hfin.toFinset,
      e i.1 * algebraMap C (quotPolysExt C Ps)
        (evalBar C Ps i.1 (hfin.mem_toFinset.mp i.2) t)⁻¹ with hu
  have hval : ∀ (z : Fin k → C) (hz : z ∈ zerOfFinset C Ps),
      evalBar C Ps z hz (t * u - 1) = 0 := by
    intro z hz
    have hz' : z ∈ hfin.toFinset := hfin.mem_toFinset.mpr hz
    rw [map_sub, map_one, map_mul, sub_eq_zero]
    have keyu : evalBar C Ps z hz u = (evalBar C Ps z hz t)⁻¹ := by
      rw [hu, map_sum, Finset.sum_eq_single (⟨z, hz'⟩ : hfin.toFinset)]
      · rw [map_mul, hval1 z hz, one_mul, evalBar_algebraMap]
      · intro i _ hi
        have hiz : i.1 ≠ z := fun h => hi (Subtype.ext h)
        rw [map_mul, hval0 i.1 (hfin.mem_toFinset.mp i.2) z hz hiz, zero_mul]
      · intro h; exact absurd (Finset.mem_univ _) h
    rw [keyu, mul_inv_cancel₀ (ht z hz)]
  have hnil : IsNilpotent (t * u - 1) := nilpotent_of_eval_zero Ps (t * u - 1) hval
  have htu : IsUnit (t * u) := by
    have h1 : t * u = 1 + (t * u - 1) := by ring
    rw [h1]; exact hnil.isUnit_one_add
  exact isUnit_of_dvd_unit (dvd_mul_right t u) htu

open Polynomial in
/-- **BPR Theorem 4.97.** The characteristic polynomial of the multiplication map `L_f` on `Ā`
factors as `∏_{x ∈ Zer} (X − f(x))^{μ(x)}`. -/
theorem theorem_4_97 (Ps : Finset (MvPolynomial (Fin k) K))
    (hfin : (zerOfFinset C Ps).Finite) [Module.Finite C (quotPolysExt C Ps)]
    (f : quotPolysExt C Ps) :
    LinearMap.charpoly (mulMapExt C Ps f)
      = ∏ x : hfin.toFinset,
          (Polynomial.X
            - Polynomial.C (evalBar C Ps x.1 (hfin.mem_toFinset.mp x.2) f))
            ^ multiplicityOfZero C Ps x.1 (hfin.mem_toFinset.mp x.2) := by
  classical
  haveI : CharZero C := charZero_of_injective_algebraMap (algebraMap K C).injective
  -- index type and the per-point localizations
  let I := hfin.toFinset
  let M : I → Type _ := fun i => localizationAtPoint C Ps i.1 (hfin.mem_toFinset.mp i.2)
  -- the product decomposition `Φ : Ā ≃ₐ[C] Π Ā_x`.
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : quotPolysExt C Ps ≃ₐ[C] (∀ i : I, M i),
      ∀ (a : quotPolysExt C Ps) (i : I),
        Φ a i = algebraMap (quotPolysExt C Ps) (M i) a := by
    -- the `C`-algebra hom `a ↦ (algebraMap a)_i`
    let toPi : quotPolysExt C Ps →ₐ[C] (∀ i : I, M i) :=
      Pi.algHom C M (fun i => IsScalarTower.toAlgHom C (quotPolysExt C Ps) (M i))
    have htoPi : ∀ (a : quotPolysExt C Ps) (i : I),
        toPi a i = algebraMap (quotPolysExt C Ps) (M i) a := fun a i => by
      show (IsScalarTower.toAlgHom C (quotPolysExt C Ps) (M i)) a = _
      rw [IsScalarTower.toAlgHom_apply]
    -- the complete set of orthogonal idempotents indexed by the zeros
    obtain ⟨e, _hsum, _horth, hidem, hval1, hval0⟩ := proposition_4_92 (C := C) Ps hfin
    -- images of the idempotents in the localizations
    have hImg_self : ∀ i : I, algebraMap (quotPolysExt C Ps) (M i) (e i.1) = 1 := by
      intro i
      have hidemi : IsIdempotentElem (e i.1) := by
        rw [IsIdempotentElem, ← sq]; exact hidem i.1 i.2
      have hmem : e i.1 ∈ evalAtPointSubmonoid C Ps i.1 (hfin.mem_toFinset.mp i.2) := by
        rw [mem_evalAtPointSubmonoid, hval1 i.1 (hfin.mem_toFinset.mp i.2)]
        exact one_ne_zero
      haveI : IsLocalization (evalAtPointSubmonoid C Ps i.1 (hfin.mem_toFinset.mp i.2))
          (M i) :=
        inferInstanceAs (IsLocalization _
          (Localization (evalAtPointSubmonoid C Ps i.1 (hfin.mem_toFinset.mp i.2))))
      show algebraMap (quotPolysExt C Ps) (M i) (e i.1) = 1
      rw [← map_one (algebraMap (quotPolysExt C Ps) (M i))]
      refine (IsLocalization.eq_iff_exists
        (evalAtPointSubmonoid C Ps i.1 (hfin.mem_toFinset.mp i.2)) (M i)).mpr ?_
      exact ⟨⟨e i.1, hmem⟩, by rw [mul_one]; exact hidemi⟩
    have hImg_other : ∀ i j : I, i ≠ j →
        algebraMap (quotPolysExt C Ps) (M i) (e j.1) = 0 := by
      intro i j hij
      have hjne : j.1 ≠ i.1 := fun h => hij (Subtype.ext h.symm)
      -- `e j.1` vanishes at `i.1`, so its image is nilpotent
      have hev : evalBar C Ps i.1 (hfin.mem_toFinset.mp i.2) (e j.1) = 0 :=
        hval0 j.1 (hfin.mem_toFinset.mp j.2) i.1 (hfin.mem_toFinset.mp i.2) hjne
      have hnil : IsNilpotent (algebraMap (quotPolysExt C Ps) (M i) (e j.1)) :=
        isNilpotent_algebraMap_localization_of_evalBar_eq_zero Ps i.1
          (hfin.mem_toFinset.mp i.2) (e j.1) hev
      -- it is also idempotent
      have hidemImg : IsIdempotentElem (algebraMap (quotPolysExt C Ps) (M i) (e j.1)) := by
        show algebraMap (quotPolysExt C Ps) (M i) (e j.1)
            * algebraMap (quotPolysExt C Ps) (M i) (e j.1) = _
        rw [← map_mul, ← sq, hidem j.1 j.2]
      -- nilpotent + idempotent ⟹ 0
      exact hidemImg.eq_zero_of_isNilpotent hnil
    -- choose preimages of the components under the surjective localization maps
    have hsurj : ∀ i : I, Function.Surjective
        (algebraMap (quotPolysExt C Ps) (M i)) := fun i =>
      algebraMap_localizationAtPoint_surjective Ps i.1 (hfin.mem_toFinset.mp i.2)
    -- the inverse `(z i) ↦ ∑ i, e i · (lift of z i)`
    let lift : (∀ i : I, M i) → I → quotPolysExt C Ps :=
      fun z i => Classical.choose (hsurj i (z i))
    have hlift : ∀ (z : ∀ i : I, M i) (i : I),
        algebraMap (quotPolysExt C Ps) (M i) (lift z i) = z i :=
      fun z i => Classical.choose_spec (hsurj i (z i))
    let fromPi : (∀ i : I, M i) → quotPolysExt C Ps :=
      fun z => ∑ i : I, e i.1 * lift z i
    -- `toPi (fromPi z) = z`
    have hright : ∀ z : ∀ i : I, M i, toPi (fromPi z) = z := by
      intro z
      funext j
      rw [htoPi]
      show algebraMap (quotPolysExt C Ps) (M j) (∑ i : I, e i.1 * lift z i) = z j
      rw [map_sum]
      rw [Finset.sum_eq_single j]
      · rw [map_mul, hImg_self j, one_mul, hlift]
      · intro i _ hij
        rw [map_mul, hImg_other j i (fun h => hij h.symm), zero_mul]
      · intro hj; exact absurd (Finset.mem_univ j) hj
    -- `toPi` is surjective (it has the explicit right inverse `fromPi`)
    have hsurjPi : Function.Surjective toPi := Function.RightInverse.surjective hright
    -- `toPi` is injective: if `w ↦ 0` in every `Ā_i`, pick `sᵢ ∈ Sᵢ` with `sᵢ·w = 0`; then
    -- `t := ∑ᵢ eᵢ·sᵢ` is nonzero at every zero, hence a unit, while `t·w = 0`, so `w = 0`.
    have hker : ∀ w : quotPolysExt C Ps, toPi w = 0 → w = 0 := by
      intro w hw
      have hzero : ∀ i : I, algebraMap (quotPolysExt C Ps) (M i) w = 0 := by
        intro i; rw [← htoPi w i, hw]; rfl
      have hSi : ∀ i : I, ∃ s : quotPolysExt C Ps,
          s ∈ evalAtPointSubmonoid C Ps i.1 (hfin.mem_toFinset.mp i.2) ∧ s * w = 0 := by
        intro i
        haveI : IsLocalization
            (evalAtPointSubmonoid C Ps i.1 (hfin.mem_toFinset.mp i.2)) (M i) :=
          inferInstanceAs (IsLocalization _
            (Localization (evalAtPointSubmonoid C Ps i.1 (hfin.mem_toFinset.mp i.2))))
        obtain ⟨m, hm⟩ := (IsLocalization.map_eq_zero_iff
          (evalAtPointSubmonoid C Ps i.1 (hfin.mem_toFinset.mp i.2)) (M i) w).mp (hzero i)
        exact ⟨m.1, m.2, hm⟩
      choose s hs hsw using hSi
      set t : quotPolysExt C Ps := ∑ i : I, e i.1 * s i with ht
      have htne : ∀ (z : Fin k → C) (hz : z ∈ zerOfFinset C Ps),
          evalBar C Ps z hz t ≠ 0 := by
        intro z hz
        have hz' : z ∈ hfin.toFinset := hfin.mem_toFinset.mpr hz
        have key : evalBar C Ps z hz t = evalBar C Ps z hz (s ⟨z, hz'⟩) := by
          rw [ht, map_sum, Finset.sum_eq_single (⟨z, hz'⟩ : I)]
          · rw [map_mul, hval1 z hz, one_mul]
          · intro i _ hi
            have hiz : i.1 ≠ z := fun h => hi (Subtype.ext h)
            rw [map_mul, hval0 i.1 (hfin.mem_toFinset.mp i.2) z hz hiz, zero_mul]
          · intro h; exact absurd (Finset.mem_univ _) h
        rw [key]
        exact (mem_evalAtPointSubmonoid C Ps z hz (s ⟨z, hz'⟩)).mp (hs ⟨z, hz'⟩)
      have htw : t * w = 0 := by
        rw [ht, Finset.sum_mul]
        refine Finset.sum_eq_zero ?_
        intro i _; rw [mul_assoc, hsw i, mul_zero]
      exact ((isUnit_of_evalBar_ne_zero Ps hfin t htne).mul_right_eq_zero).mp htw
    have hinjPi : Function.Injective toPi := fun a b hab =>
      sub_eq_zero.mp (hker (a - b) (by rw [map_sub, hab, sub_self]))
    refine ⟨AlgEquiv.ofBijective toPi ⟨hinjPi, hsurjPi⟩, ?_⟩
    intro a i; rw [AlgEquiv.ofBijective_apply]; exact htoPi a i
  -- conjugating `L_f` by `Φ` gives the block-diagonal multiplication map.
  have hconj : Φ.toLinearEquiv.conj (mulMapExt C Ps f)
      = blockEnd M (fun i => mulMapLoc C Ps i.1 (hfin.mem_toFinset.mp i.2) f) := by
    apply LinearMap.ext
    intro z
    rw [LinearEquiv.conj_apply]
    apply _root_.funext
    intro i
    show Φ (mulMapExt C Ps f (Φ.symm z)) i
        = blockEnd M (fun i => mulMapLoc C Ps i.1 (hfin.mem_toFinset.mp i.2) f) z i
    rw [blockEnd_apply, mulMapExt_apply, hΦ, map_mul, mulMapLoc_apply, ← hΦ (Φ.symm z) i,
      AlgEquiv.apply_symm_apply]
  -- assemble: charpoly invariance + product of per-factor charpolys
  rw [← LinearEquiv.charpoly_conj Φ.toLinearEquiv (mulMapExt C Ps f), hconj,
    charpoly_pi_eq_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  exact charpoly_mulMapLoc_eq Ps i.1 (hfin.mem_toFinset.mp i.2) f

end Main

end Azurite.BPR.Chapter4
