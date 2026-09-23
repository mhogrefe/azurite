import Azurite.BasuPollackRoy.Chapter1.Section1_1.ConstructibleQF
import Azurite.BasuPollackRoy.Chapter1.Section1_1.FieldFormula
import Azurite.BasuPollackRoy.Chapter1.Section1_1.Formula
import Azurite.BasuPollackRoy.Chapter1.Section1_1.Realization
import Azurite.BasuPollackRoy.Chapter1.Section1_3.Theorem1_22
import Azurite.BasuPollackRoy.Chapter1.Section1_4.Ext

/-! # BPR Section 1.4 — Exercise 1.12

> **Exercise 1.12.** Show that if `S` is a finite constructible subset of
> `C^k`, then `Ext(S, C')` equals `S` (under the natural inclusion
> `C^k ↪ C'^k`).

The proof follows BPR's hint: write an explicit quantifier-free formula
`finsetFormula T` describing the finite set `T` (a disjunction over `y ∈ T`
of a conjunction of `Xᵢ = C(yᵢ)` atoms). Specialising to `T = hSfin.toFinset`
gives a QF formula whose realisation over `C` is `S` itself, and whose
realisation over `C'` is the image of `S` under `algebraMap C C'`. Combined
with the well-definedness theorem `Ext_eq_realization`, this yields the
exercise.
-/

namespace Azurite.BPR

open _root_.Azurite.BPR.MvPolynomial Polynomial Formula

section PointFormula

variable {D : Type*} [CommRing D]

/-- Atom asserting `Xᵢ = C(cᵢ)`, encoded as `eq_zero (Xᵢ - C cᵢ)`. -/
noncomputable def pointAtomFormula {k : ℕ} (y : Fin k → D) (i : Fin k) :
    Formula (Fin k) (FieldAtom (Fin k) D) :=
  eq_zero (MvPolynomial.X i - MvPolynomial.C (y i))

/-- Quantifier-free formula asserting that the assignment equals `y` over
the algebra map: `⋀ᵢ Xᵢ = C(yᵢ)`. -/
noncomputable def pointFormula {k : ℕ} (y : Fin k → D) :
    Formula (Fin k) (FieldAtom (Fin k) D) :=
  Formula.conjList (List.ofFn (pointAtomFormula y))

theorem pointAtomFormula_isQF {k : ℕ} (y : Fin k → D) (i : Fin k) :
    (pointAtomFormula y i).IsQuantifierFree := by
  trivial

theorem pointFormula_isQF {k : ℕ} (y : Fin k → D) :
    (pointFormula y).IsQuantifierFree := by
  apply Formula.conjList_isQF
  intro Φ hΦ
  simp only [List.mem_ofFn] at hΦ
  obtain ⟨i, rfl⟩ := hΦ
  exact pointAtomFormula_isQF y i

end PointFormula

section PointFormulaRealization

variable {D : Type*} [CommRing D]
variable {K : Type*} [Field K] [Algebra D K]

/-- The realization of `pointAtomFormula y i` over `K` is the set of
assignments `z : Fin k → K` with `z i = algebraMap D K (y i)`. -/
theorem pointAtomFormula_realization {k : ℕ} (y : Fin k → D) (i : Fin k) :
    (pointAtomFormula y i).realization (C := K) =
      { z : Fin k → K | z i = algebraMap D K (y i) } := by
  ext z
  simp only [pointAtomFormula, realization_eq_zero, Set.mem_ofPred_eq,
    map_sub, MvPolynomial.aeval_X, MvPolynomial.aeval_C, sub_eq_zero]

/-- The realization of `pointFormula y` over `K` is the singleton
`{algebraMap D K ∘ y}`. -/
theorem pointFormula_realization {k : ℕ} (y : Fin k → D) :
    (pointFormula y).realization (C := K) =
      { algebraMap D K ∘ y } := by
  ext z
  simp only [pointFormula, realization_conjList, Set.mem_ofPred_eq,
    List.mem_ofFn, Set.mem_singleton_iff]
  constructor
  · intro h
    funext i
    have := h _ ⟨i, rfl⟩
    rw [pointAtomFormula_realization] at this
    exact this
  · intro h Φ ⟨i, hi⟩
    subst hi
    rw [pointAtomFormula_realization]
    show z i = algebraMap D K (y i)
    rw [h]
    rfl

end PointFormulaRealization

section FinsetFormula

variable {D : Type*} [CommRing D]

/-- Quantifier-free formula asserting that the assignment lies in the
finite set `T`: a disjunction over `y ∈ T` of `pointFormula y`. -/
noncomputable def finsetFormula {k : ℕ} (T : Finset (Fin k → D)) :
    Formula (Fin k) (FieldAtom (Fin k) D) :=
  Formula.disjList (T.toList.map pointFormula)

theorem finsetFormula_isQF {k : ℕ} (T : Finset (Fin k → D)) :
    (finsetFormula T).IsQuantifierFree := by
  apply disjList_isQF
  intro Φ hΦ
  simp only [List.mem_map] at hΦ
  obtain ⟨y, _, rfl⟩ := hΦ
  exact pointFormula_isQF y

end FinsetFormula

section FinsetFormulaRealization

variable {D : Type*} [CommRing D]
variable {K : Type*} [Field K] [Algebra D K]

/-- The realization of `finsetFormula T` over `K` is the image of `T`
under `algebraMap D K`. -/
theorem finsetFormula_realization {k : ℕ} (T : Finset (Fin k → D)) :
    (finsetFormula T).realization (C := K) =
      (fun y : Fin k → D => algebraMap D K ∘ y) '' (T : Set (Fin k → D)) := by
  ext z
  simp only [finsetFormula, realization_disjList, Set.mem_ofPred_eq,
    List.mem_map, Finset.mem_toList, Set.mem_image, Finset.mem_coe]
  constructor
  · rintro ⟨Φ, ⟨y, hy_mem, rfl⟩, hz⟩
    rw [pointFormula_realization] at hz
    exact ⟨y, hy_mem, hz.symm⟩
  · rintro ⟨y, hy_mem, hz⟩
    refine ⟨pointFormula y, ⟨y, hy_mem, rfl⟩, ?_⟩
    rw [pointFormula_realization]
    exact hz.symm

end FinsetFormulaRealization

/-! ### Exercise 1.12 -/

section Exercise1_12

variable {C C' : Type*} [Field C] [IsAlgClosed C]
variable [Field C'] [IsAlgClosed C'] [Algebra C C']

/-- **BPR Exercise 1.12.** If `S` is a finite constructible subset of `C^k`,
then `Ext(S, C')` equals the image of `S` under `algebraMap C C'`. -/
theorem exercise_1_12
    {k : ℕ} {S : Set (Fin k → C)} (hS : IsConstructibleSet S)
    (hSfin : S.Finite) :
    Ext (C' := C') S hS =
      (fun y : Fin k → C => (algebraMap C C') ∘ y) '' S := by
  classical
  -- The QF formula describing S as a finite set.
  let T : Finset (Fin k → C) := hSfin.toFinset
  have hT_coe : (T : Set (Fin k → C)) = S := hSfin.coe_toFinset
  let Ψ : Formula (Fin k) (FieldAtom (Fin k) C) := finsetFormula T
  have hΨ_QF : Ψ.IsQuantifierFree := finsetFormula_isQF T
  -- Ψ realizes to S over C: the algebra map C → C is the identity.
  have hΨ_C : Ψ.realization (C := C) = S := by
    show (finsetFormula T).realization (C := C) = S
    rw [finsetFormula_realization]
    rw [hT_coe]
    ext y
    simp only [Set.mem_image]
    constructor
    · rintro ⟨z, hz, rfl⟩
      have : (fun i => (algebraMap C C) (z i)) = z := by
        funext i
        exact Algebra.algebraMap_self_apply (z i)
      rw [show (algebraMap C C) ∘ z = z from this]
      exact hz
    · intro hy
      refine ⟨y, hy, ?_⟩
      funext i
      exact Algebra.algebraMap_self_apply (y i)
  -- Apply well-definedness of Ext.
  have hExt : Ψ.realization (C := C') = Ext (C' := C') S hS :=
    Ext_eq_realization hS hΨ_QF hΨ_C
  -- And Ψ realizes to the image over C'.
  have hΨ_C' : Ψ.realization (C := C') =
      (fun y : Fin k → C => (algebraMap C C') ∘ y) '' S := by
    show (finsetFormula T).realization (C := C') = _
    rw [finsetFormula_realization, hT_coe]
  rw [← hExt, hΨ_C']

end Exercise1_12

end Azurite.BPR
