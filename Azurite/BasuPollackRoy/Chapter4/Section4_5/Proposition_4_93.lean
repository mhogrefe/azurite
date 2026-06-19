import Azurite.BasuPollackRoy.Chapter4.Section4_5.LocalizationAtPoint
import Azurite.BasuPollackRoy.Chapter4.Section4_5.Proposition_4_92
import Azurite.BasuPollackRoy.Chapter4.Section4_5.Lemma_4_87
import Mathlib.RingTheory.Idempotents
import Mathlib.RingTheory.Localization.Basic
import Mathlib.RingTheory.Nilpotent.Basic
import Mathlib.Algebra.CharP.Algebra

/-!
# BPR §4.5, Proposition 4.93: the corner ring `eₓ Ā` is the localization `Ā_x`

Let `K` be a field of characteristic zero, `C` an algebraically closed extension of `K`, and `𝒫`
a finite subset of `K[X₁, …, X_k]`. For `x ∈ Zer(𝒫, Cᵏ)`, let `eₓ ∈ Ā` be an idempotent with
`eₓ(x) = 1` and `eₓ(y) = 0` for every other zero `y` (such an `eₓ` exists by Proposition 4.92).
Then the corner ring `eₓ Ā` is isomorphic to the localization `Ā_x` of `Ā` at `x`.
-/

namespace Azurite.BPR.Chapter4

open MvPolynomial
open scoped Classical

variable {k : ℕ} {K : Type*} [Field K]

/-- **BPR Proposition 4.93.** The corner ring `eₓ Ā` is isomorphic to the localization `Ā_x`. -/
theorem proposition_4_93 [CharZero K] {C : Type*} [Field C] [IsAlgClosed C] [Algebra K C] {k : ℕ}
    (Ps : Finset (MvPolynomial (Fin k) K)) (x : Fin k → C) (hx : x ∈ zerOfFinset C Ps)
    (e : quotPolysExt C Ps) (he : IsIdempotentElem e)
    (hex : evalBar C Ps x hx e = 1)
    (hey : ∀ (y : Fin k → C) (hy : y ∈ zerOfFinset C Ps), y ≠ x → evalBar C Ps y hy e = 0) :
    Nonempty (he.Corner ≃+* localizationAtPoint C Ps x hx) := by
  haveI : CharZero C := charZero_of_injective_algebraMap (algebraMap K C).injective
  -- Work with the explicit `Localization` type so the localization type-class machinery applies
  -- (`localizationAtPoint` is definitionally `Localization (evalAtPointSubmonoid …)`).
  show Nonempty (he.Corner ≃+* Localization (evalAtPointSubmonoid C Ps x hx))
  -- Abbreviations matching the proof plan.
  -- `R' := he.Corner`, `Ā := quotPolysExt C Ps`, `Sx := evalAtPointSubmonoid C Ps x hx`,
  -- `Āx := localizationAtPoint C Ps x hx`.
  -- corner element coercion arithmetic (all `rfl`).
  have coe_mul : ∀ a b : he.Corner, (a * b).1 = a.1 * b.1 := fun _ _ => rfl
  have coe_add : ∀ a b : he.Corner, (a + b).1 = a.1 + b.1 := fun _ _ => rfl
  have coe_zero : (0 : he.Corner).1 = (0 : quotPolysExt C Ps) := rfl
  have coe_one : (1 : he.Corner).1 = e := rfl
  -- membership characterization in the corner (commutative case).
  have mem_corner : ∀ r : quotPolysExt C Ps,
      r ∈ Subsemigroup.corner e ↔ e * r = r := by
    intro r
    rw [Subsemigroup.mem_corner_iff he]
    constructor
    · exact fun h => h.1
    · exact fun h => ⟨h, by rw [mul_comm]; exact h⟩
  -- `e * a` is in the corner.
  have mul_mem : ∀ a : quotPolysExt C Ps, e * a ∈ Subsemigroup.corner e := by
    intro a
    rw [mem_corner]
    rw [← mul_assoc, he.eq]
  -- ============ Step 1: the projection ring hom `π : Ā →+* R'` ============
  let π : quotPolysExt C Ps →+* he.Corner :=
  { toFun := fun a => ⟨e * a, mul_mem a⟩
    map_one' := by
      apply Subtype.ext
      show e * 1 = e
      rw [mul_one]
    map_mul' := by
      intro a b
      apply Subtype.ext
      show e * (a * b) = (e * a) * (e * b)
      have : (e * a) * (e * b) = (e * e) * (a * b) := by ring
      rw [this, he.eq]
    map_zero' := by
      apply Subtype.ext
      show e * 0 = 0
      rw [mul_zero]
    map_add' := by
      intro a b
      apply Subtype.ext
      show e * (a + b) = (e * a) + (e * b)
      rw [mul_add] }
  have π_apply : ∀ a, (π a).1 = e * a := fun _ => rfl
  -- ============ Step 2: `π` sends `Sx` to units ============
  have hπunit : ∀ Q : quotPolysExt C Ps, Q ∈ evalAtPointSubmonoid C Ps x hx → IsUnit (π Q) := by
    intro Q hQ
    have hc : evalBar C Ps x hx Q ≠ 0 := (mem_evalAtPointSubmonoid C Ps x hx Q).mp hQ
    set c := evalBar C Ps x hx Q with hcdef
    -- `v := algebraMap C Ā c⁻¹ * Q - 1`
    set v : quotPolysExt C Ps := algebraMap C (quotPolysExt C Ps) c⁻¹ * Q - 1 with hvdef
    -- `evalBar x v = 0`
    have hvx : evalBar C Ps x hx v = 0 := by
      rw [hvdef, map_sub, map_mul, map_one, evalBar_algebraMap, ← hcdef,
        inv_mul_cancel₀ hc, sub_self]
    -- `e * v` evaluates to 0 at every zero.
    have hevz : ∀ (z : Fin k → C) (hz : z ∈ zerOfFinset C Ps),
        evalBar C Ps z hz (e * v) = 0 := by
      intro z hz
      rw [map_mul]
      by_cases hzx : z = x
      · subst hzx
        rw [hvx, mul_zero]
      · rw [hey z hz hzx, zero_mul]
    -- so `e * v` is nilpotent.
    have hnil : IsNilpotent (e * v) := nilpotent_of_eval_zero Ps (e * v) hevz
    -- `π v` is nilpotent: `π (e*v) = π v` and `π` is a ring hom.
    have hπev : π (e * v) = π v := by
      apply Subtype.ext
      show e * (e * v) = e * v
      rw [← mul_assoc, he.eq]
    have hπvnil : IsNilpotent (π v) := by
      rw [← hπev]
      exact hnil.map π
    -- `1 + π v` is a unit.
    have hunit1v : IsUnit (1 + π v) := hπvnil.isUnit_one_add
    -- `1 + v = algebraMap c⁻¹ * Q`, and `π (1 + v) = 1 + π v`.
    have h1v : (1 : quotPolysExt C Ps) + v = algebraMap C (quotPolysExt C Ps) c⁻¹ * Q := by
      rw [hvdef]; ring
    have hπ1v : π (1 + v) = 1 + π v := by rw [map_add, map_one]
    -- `π (algebraMap c⁻¹)` is a unit.
    have hunitinv : IsUnit (π (algebraMap C (quotPolysExt C Ps) c⁻¹)) := by
      refine ⟨⟨π (algebraMap C (quotPolysExt C Ps) c⁻¹),
        π (algebraMap C (quotPolysExt C Ps) c), ?_, ?_⟩, rfl⟩
      · rw [← map_mul, ← map_mul, inv_mul_cancel₀ hc, map_one, map_one]
      · rw [← map_mul, ← map_mul, mul_inv_cancel₀ hc, map_one, map_one]
    -- combine: `1 + π v = π (algebraMap c⁻¹) * π Q` is a unit; divide by the unit.
    have hcombine : (1 : he.Corner) + π v
        = π (algebraMap C (quotPolysExt C Ps) c⁻¹) * π Q := by
      rw [← hπ1v, h1v, map_mul]
    have hunitprod : IsUnit (π (algebraMap C (quotPolysExt C Ps) c⁻¹) * π Q) := by
      rw [← hcombine]; exact hunit1v
    -- `π Q = u⁻¹ * (u * π Q)` is a product of units, where `u := π (am c⁻¹)`.
    obtain ⟨u, hu⟩ := hunitinv
    obtain ⟨w, hw⟩ := hunitprod
    refine ⟨u⁻¹ * w, ?_⟩
    rw [Units.val_mul, hw, ← hu, ← mul_assoc, Units.inv_mul, one_mul]
  -- ============ Step 3: `φ : Āx →+* R'` via universal property ============
  let φ : Localization (evalAtPointSubmonoid C Ps x hx) →+* he.Corner :=
    IsLocalization.lift (S := Localization (evalAtPointSubmonoid C Ps x hx))
      (P := he.Corner) (M := evalAtPointSubmonoid C Ps x hx)
      (g := π) (fun y => hπunit y.1 y.2)
  have φ_eq : ∀ a,
      φ (algebraMap (quotPolysExt C Ps) (Localization (evalAtPointSubmonoid C Ps x hx)) a) = π a :=
    fun a => IsLocalization.lift_eq (fun y => hπunit y.1 y.2) a
  -- `algebraMap Ā Āx e = 1` (since `e/1 = 1/1` because `e ∈ Sx` and `e(e-1) = 0`).
  have he_mem : e ∈ evalAtPointSubmonoid C Ps x hx := by
    rw [mem_evalAtPointSubmonoid]; rw [hex]; exact one_ne_zero
  have hmap_e :
      algebraMap (quotPolysExt C Ps) (Localization (evalAtPointSubmonoid C Ps x hx)) e = 1 := by
    have h1 : algebraMap (quotPolysExt C Ps) (Localization (evalAtPointSubmonoid C Ps x hx)) e
        = algebraMap (quotPolysExt C Ps) (Localization (evalAtPointSubmonoid C Ps x hx)) 1 := by
      refine (IsLocalization.eq_iff_exists (evalAtPointSubmonoid C Ps x hx)
        (Localization (evalAtPointSubmonoid C Ps x hx))).mpr ?_
      refine ⟨⟨e, he_mem⟩, ?_⟩
      show e * e = e * 1
      rw [mul_one, he.eq]
    rw [h1, map_one]
  -- ============ Step 4: the inverse `ψ : R' →+* Āx` ============
  let ψ : he.Corner →+* Localization (evalAtPointSubmonoid C Ps x hx) :=
  { toFun := fun r =>
      algebraMap (quotPolysExt C Ps) (Localization (evalAtPointSubmonoid C Ps x hx)) r.1
    map_one' := by
      show algebraMap (quotPolysExt C Ps) (Localization (evalAtPointSubmonoid C Ps x hx))
        (1 : he.Corner).1 = 1
      rw [coe_one]; exact hmap_e
    map_mul' := by
      intro a b
      show algebraMap _ _ ((a * b).1) = algebraMap _ _ a.1 * algebraMap _ _ b.1
      rw [coe_mul, map_mul]
    map_zero' := by
      show algebraMap (quotPolysExt C Ps) (Localization (evalAtPointSubmonoid C Ps x hx))
        (0 : he.Corner).1 = 0
      rw [coe_zero, map_zero]
    map_add' := by
      intro a b
      show algebraMap _ _ ((a + b).1) = algebraMap _ _ a.1 + algebraMap _ _ b.1
      rw [coe_add, map_add] }
  have ψ_apply : ∀ r : he.Corner,
      ψ r = algebraMap (quotPolysExt C Ps) (Localization (evalAtPointSubmonoid C Ps x hx)) r.1 :=
    fun _ => rfl
  -- ============ Step 5: mutually inverse ============
  -- `φ (ψ r) = r`.
  have hφψ : ∀ r : he.Corner, φ (ψ r) = r := by
    intro r
    rw [ψ_apply, φ_eq]
    apply Subtype.ext
    show e * r.1 = r.1
    exact (mem_corner r.1).mp r.2
  -- `ψ (φ z) = z`: agree after `algebraMap`.
  have hψφ_alg : ∀ a : quotPolysExt C Ps,
      ψ (φ (algebraMap (quotPolysExt C Ps) (Localization (evalAtPointSubmonoid C Ps x hx)) a))
        = algebraMap (quotPolysExt C Ps) (Localization (evalAtPointSubmonoid C Ps x hx)) a := by
    intro a
    rw [φ_eq, ψ_apply]
    show algebraMap (quotPolysExt C Ps) (Localization (evalAtPointSubmonoid C Ps x hx)) (e * a)
      = algebraMap (quotPolysExt C Ps) (Localization (evalAtPointSubmonoid C Ps x hx)) a
    rw [map_mul, hmap_e, one_mul]
  have hψφ : (ψ.comp φ) = RingHom.id (Localization (evalAtPointSubmonoid C Ps x hx)) := by
    refine IsLocalization.ringHom_ext (S := Localization (evalAtPointSubmonoid C Ps x hx))
      (evalAtPointSubmonoid C Ps x hx) ?_
    apply RingHom.ext
    intro a
    show ψ (φ (algebraMap _ _ a)) = RingHom.id _ (algebraMap _ _ a)
    rw [RingHom.id_apply, hψφ_alg]
  -- assemble the equivalence `he.Corner ≃+* Localization (…)`.
  refine ⟨RingEquiv.ofRingHom ψ φ hψφ ?_⟩
  -- `φ.comp ψ = id (he.Corner)`
  apply RingHom.ext
  intro r
  show φ (ψ r) = RingHom.id _ r
  rw [RingHom.id_apply]
  exact hφψ r

end Azurite.BPR.Chapter4
