import Azurite.BasuPollackRoy.Chapter4.Section4_6.HermiteForm
import Azurite.BasuPollackRoy.Chapter4.Section4_6.Remark_4_99
import Azurite.BasuPollackRoy.Chapter4.Section4_6.Theorem_4_98
import Azurite.BasuPollackRoy.Chapter4.Section4_5.Definition_4_89
import Azurite.BasuPollackRoy.Chapter4.Section4_5.Lemma_4_90
import Azurite.BasuPollackRoy.Chapter4.Section4_5.Proposition_4_92
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.Algebra.CharP.Algebra

/-!
# BPR §4.6, Theorem 4.100: `√(Ideal(𝒫, K)) = Rad(Her(𝒫))`

Let `K` be a field of characteristic zero, `C` an algebraically closed extension of `K`, and `𝒫`
a finite subset of `K[X₁, …, X_k]` with `A = K[X]/Ideal(𝒫, K)` finite dimensional and
`Zer(𝒫, Cᵏ)` finite. The radical `Rad(Her(𝒫))` of Hermite's quadratic form is the kernel of the
bilinear map `her(𝒫)`. Theorem 4.100 identifies it with the radical of `Ideal(𝒫, K)`: an element
`f ∈ K[X]` lies in `√(Ideal(𝒫, K))` iff its image in `A` lies in `Rad(Her(𝒫))`.

The bridge to the geometry is the trace formula (Stickelberger, Theorem 4.98) together with
Remark 4.99, which give, for `u, w ∈ A`,
\[
  \mathrm{her}(\mathcal{P})(u, w) \longmapsto
    \sum_{x \in \mathrm{Zer}(\mathcal{P}, C^k)} \mu(x)\, u(x)\, w(x)
\]
after applying the inclusion `K ↪ C` (`hermite_bridge`). With a separating element `a`
(Lemma 4.90) the values `a(x)` are distinct, and a Vandermonde argument forces `u(x) = 0` at every
zero whenever `her(𝒫)(u, ·)` vanishes; nilpotency of the image of `u` in `Ā` (Proposition 4.92)
then descends to `f ∈ √(Ideal(𝒫, K))`.
-/

namespace Azurite.BPR.Chapter4

open MvPolynomial
open scoped Classical

variable {k : ℕ} {K : Type*} [Field K] [CharZero K]
  {C : Type*} [Field C] [IsAlgClosed C] [Algebra K C]

/-- `Rad(Her(𝒫))`, the radical of Hermite's quadratic form: the kernel of `her(𝒫)`. -/
noncomputable def radHermite (Ps : Finset (MvPolynomial (Fin k) K)) :
    Submodule K (quotPolys Ps) := LinearMap.ker (hermiteBilinOne Ps)

omit [CharZero K] in
theorem mem_radHermite (Ps : Finset (MvPolynomial (Fin k) K)) (f : quotPolys Ps) :
    f ∈ radHermite Ps ↔ ∀ g, hermiteBilinOne Ps f g = 0 := by
  rw [radHermite, LinearMap.mem_ker]; constructor
  · intro h g; rw [h]; rfl
  · intro h; exact LinearMap.ext fun g => h g

/-- **Key bridge.** Applying `K ↪ C` to `her(𝒫)(u, w)` gives the geometric sum
`∑_x μ(x) · u(x) · w(x)` over the zeros. -/
theorem hermite_bridge (Ps : Finset (MvPolynomial (Fin k) K))
    [Module.Finite K (quotPolys Ps)] (hfin : (zerOfFinset C Ps).Finite)
    (u w : quotPolys Ps) :
    algebraMap K C (hermiteBilinOne Ps u w)
      = ∑ x : hfin.toFinset,
          multiplicityOfZero C Ps x.1 (hfin.mem_toFinset.mp x.2)
            • (valueAt C Ps u x.1 (hfin.mem_toFinset.mp x.2)
                * valueAt C Ps w x.1 (hfin.mem_toFinset.mp x.2)) := by
  rw [hermiteBilinOne_apply, ← remark_4_99_trace C Ps (u * w)]
  -- `mulMapBaseExt C Ps (u * w) = mulMapExt C Ps (inclExt C Ps (u * w))` by `rfl`
  have hmm : mulMapBaseExt C Ps (u * w) = mulMapExt C Ps (inclExt C Ps (u * w)) := rfl
  rw [hmm, (theorem_4_98 Ps hfin (inclExt C Ps (u * w))).1]
  refine Finset.sum_congr rfl fun x _ => ?_
  congr 1
  rw [map_mul, map_mul]
  rfl

/-- **BPR Theorem 4.100.** `√(Ideal(𝒫, K)) = Rad(Her(𝒫))`: an element `f ∈ K[X]` lies in the
radical of `Ideal(𝒫, K)` iff its image in `A` lies in the radical of Hermite's quadratic form. -/
theorem theorem_4_100 (Ps : Finset (MvPolynomial (Fin k) K))
    [Module.Finite K (quotPolys Ps)] (hfin : (zerOfFinset C Ps).Finite)
    (f : MvPolynomial (Fin k) K) :
    Ideal.Quotient.mk (idealOfPolys Ps) f ∈ radHermite Ps
      ↔ f ∈ (idealOfPolys Ps).radical := by
  haveI : CharZero C := charZero_of_injective_algebraMap (algebraMap K C).injective
  -- abbreviations
  set fA : quotPolys Ps := Ideal.Quotient.mk (idealOfPolys Ps) f with hfA
  -- multiplicities are positive: `Ā_x` is a nonzero finite-dimensional `C`-space (local ring)
  have hmu_pos : ∀ (x : Fin k → C) (hx : x ∈ zerOfFinset C Ps),
      0 < multiplicityOfZero C Ps x hx := by
    intro x hx
    haveI : Nontrivial (localizationAtPoint C Ps x hx) :=
      (isLocalRing_localizationAtPoint C Ps x hx).toNontrivial
    exact Module.finrank_pos
  have hmu_ne : ∀ (x : Fin k → C) (hx : x ∈ zerOfFinset C Ps),
      (multiplicityOfZero C Ps x hx : C) ≠ 0 := by
    intro x hx
    exact Nat.cast_ne_zero.mpr (hmu_pos x hx).ne'
  constructor
  · -- (→) `mk f ∈ radHermite ⟹ f ∈ √Ideal`
    intro hmem
    rw [mem_radHermite] at hmem
    -- `f` vanishes at every zero
    have hvan : ∀ (x : Fin k → C) (hx : x ∈ zerOfFinset C Ps),
        valueAt C Ps fA x hx = 0 := by
      -- a separating element
      obtain ⟨i, _, hsep⟩ := lemma_4_90 (K := K) C Ps hfin
      set a : quotPolys Ps := Ideal.Quotient.mk _ (linearForm (K := K) i) with ha
      -- enumerate the zeros via `Fin n`
      set n : ℕ := hfin.toFinset.card with hn
      let e : Fin n ≃ ↥hfin.toFinset :=
        (Fintype.equivFinOfCardEq (by rw [Fintype.card_coe])).symm
      -- value, multiplicity and `a`-value functions indexed by `Fin n`
      let valF : Fin n → C := fun j =>
        valueAt C Ps fA (e j).1 (hfin.mem_toFinset.mp (e j).2)
      let muF : Fin n → ℕ := fun j =>
        multiplicityOfZero C Ps (e j).1 (hfin.mem_toFinset.mp (e j).2)
      let avalF : Fin n → C := fun j =>
        valueAt C Ps a (e j).1 (hfin.mem_toFinset.mp (e j).2)
      -- `avalF` is injective (separation)
      have haval_inj : Function.Injective avalF := by
        intro j₁ j₂ h
        have := hsep (e j₁).1 (hfin.mem_toFinset.mp (e j₁).2)
          (e j₂).1 (hfin.mem_toFinset.mp (e j₂).2) h
        exact e.injective (Subtype.ext this)
      -- the Vandermonde equations
      have hvand : ∀ (i' : Fin n), ∑ j, (muF j • valF j) * avalF j ^ (i' : ℕ) = 0 := by
        intro i'
        have hzero : hermiteBilinOne Ps fA (a ^ (i' : ℕ)) = 0 := hmem (a ^ (i' : ℕ))
        have hbr := hermite_bridge Ps hfin fA (a ^ (i' : ℕ))
        rw [hzero, map_zero] at hbr
        -- the geometric sum equals our `Fin n`-indexed sum
        have hbr' : (0 : C) = ∑ j : Fin n, (muF j • valF j) * avalF j ^ (i' : ℕ) := by
          rw [hbr, ← Equiv.sum_comp e (fun x : ↥hfin.toFinset =>
            multiplicityOfZero C Ps x.1 (hfin.mem_toFinset.mp x.2)
              • (valueAt C Ps fA x.1 (hfin.mem_toFinset.mp x.2)
                  * valueAt C Ps (a ^ (i' : ℕ)) x.1 (hfin.mem_toFinset.mp x.2)))]
          refine Finset.sum_congr rfl fun j _ => ?_
          show muF j • (valF j
                * valueAt C Ps (a ^ (i' : ℕ)) (e j).1 (hfin.mem_toFinset.mp (e j).2))
              = (muF j • valF j) * avalF j ^ (i' : ℕ)
          rw [show valueAt C Ps (a ^ (i' : ℕ)) (e j).1 (hfin.mem_toFinset.mp (e j).2)
                = avalF j ^ (i' : ℕ) by
                  show evalBar C Ps (e j).1 _ (inclExt C Ps (a ^ (i' : ℕ)))
                    = (evalBar C Ps (e j).1 _ (inclExt C Ps a)) ^ (i' : ℕ)
                  rw [map_pow, map_pow],
            nsmul_eq_mul, nsmul_eq_mul, mul_assoc]
        exact hbr'.symm
      -- Vandermonde: `μ(x) • valF = 0` for every index
      have hkill : (fun j => muF j • valF j) = 0 :=
        Matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero haval_inj hvand
      -- conclude `valF j = 0`, hence `valueAt fA x = 0` for every zero `x`
      have hvalF0 : ∀ j, valF j = 0 := by
        intro j
        have : muF j • valF j = 0 := congrFun hkill j
        rw [nsmul_eq_mul] at this
        rcases mul_eq_zero.mp this with h | h
        · exact absurd h (hmu_ne (e j).1 (hfin.mem_toFinset.mp (e j).2))
        · exact h
      intro x hx
      -- transport back: `x` corresponds to some `Fin n` index through `e`
      have hxT : x ∈ hfin.toFinset := hfin.mem_toFinset.mpr hx
      have := hvalF0 (e.symm ⟨x, hxT⟩)
      simp only [valF, Equiv.apply_symm_apply] at this
      convert this using 2
    -- the image of `f` in `Ā` is nilpotent
    have hnil : IsNilpotent (inclExt C Ps fA) := by
      refine nilpotent_of_eval_zero Ps (inclExt C Ps fA) ?_
      intro z hz
      have := hvan z hz
      rwa [valueAt] at this
    obtain ⟨m, hm⟩ := hnil
    -- `mk (map (algebraMap K C) (f^m)) = 0` in `Ā`
    have hmem' : MvPolynomial.map (algebraMap K C) (f ^ m) ∈ idealOfPolysExt C Ps := by
      rw [← Ideal.Quotient.eq_zero_iff_mem]
      have hpm : (inclExt C Ps fA) ^ m = Ideal.Quotient.mk (idealOfPolysExt C Ps)
          (MvPolynomial.map (algebraMap K C) (f ^ m)) := by
        rw [hfA, inclExt_mk, ← map_pow, ← map_pow]
      rw [← hpm, hm]
    -- descend to `K[X]`
    have hfm : f ^ m ∈ idealOfPolys Ps := mem_idealOfPolys_of_map_mem C hmem'
    exact ⟨m, hfm⟩
  · -- (←) `f ∈ √Ideal ⟹ mk f ∈ radHermite`
    intro hmem
    obtain ⟨m, hfm⟩ := hmem
    -- `f` vanishes at every zero
    have hvan : ∀ (x : Fin k → C) (hx : x ∈ zerOfFinset C Ps),
        valueAt C Ps fA x hx = 0 := by
      intro x hx
      have hpow : (valueAt C Ps fA x hx) ^ m = 0 := by
        rw [hfA, valueAt_mk, ← map_pow]
        exact aeval_eq_zero_of_mem_idealOfPolys hfm x hx
      have hmpos : 0 < m := by
        rcases Nat.eq_zero_or_pos m with rfl | hpos
        · rw [pow_zero] at hpow; exact absurd hpow one_ne_zero
        · exact hpos
      exact pow_eq_zero_iff hmpos.ne' |>.mp hpow
    -- hence `her(𝒫)(fA, g) = 0` for all `g`
    rw [mem_radHermite]
    intro g
    have hbr := hermite_bridge Ps hfin fA g
    have hsum0 : ∑ x : hfin.toFinset,
        multiplicityOfZero C Ps x.1 (hfin.mem_toFinset.mp x.2)
          • (valueAt C Ps fA x.1 (hfin.mem_toFinset.mp x.2)
              * valueAt C Ps g x.1 (hfin.mem_toFinset.mp x.2)) = 0 := by
      refine Finset.sum_eq_zero fun x _ => ?_
      rw [hvan x.1 (hfin.mem_toFinset.mp x.2), zero_mul, smul_zero]
    rw [hsum0] at hbr
    exact (map_eq_zero_iff _ (algebraMap K C).injective).mp hbr

end Azurite.BPR.Chapter4
