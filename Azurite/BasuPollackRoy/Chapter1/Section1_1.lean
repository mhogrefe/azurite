import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.Nullstellensatz
import Mathlib.Algebra.MvPolynomial.Polynomial
import Mathlib.Algebra.MvPolynomial.Equiv

/-!
# Basu, Pollack, Roy — *Algorithms in Real Algebraic Geometry*
## Chapter 1: Algebraically Closed Fields
## Section 1.1: Definitions and First Properties

Reference: Basu, S., Pollack, R., & Roy, M.-F.
*Algorithms in Real Algebraic Geometry*. Springer, 2006.

A field K is **algebraically closed** if every polynomial of positive degree
with coefficients in K has a root in K.

This is already formalized in Mathlib as `IsAlgClosed`:

```
/-- An algebraically closed field is one where every polynomial splits. Equivalently, all
non-constant polynomials have a root. See `IsAlgClosed.exists_root` and
`IsAlgClosed.of_exists_root`. -/
class IsAlgClosed (k : Type u) [Field k] : Prop where
  splits : ∀ p : k[X], p.Splits
```

See: `Mathlib.FieldTheory.IsAlgClosed.Basic`

The equivalent characterization via roots (BPR's formulation) is:

```
theorem IsAlgClosed.exists_root [IsAlgClosed k] (p : k[X]) (hp : p.degree ≠ 0) :
    ∃ x, IsRoot p x
```

Key Mathlib API:
- `IsAlgClosed.exists_root`: every nonconstant polynomial has a root
- `IsAlgClosed.of_exists_root`: constructing `IsAlgClosed` from the root property
- `IsAlgClosed.degree_eq_one_of_irreducible`: irreducible polynomials are linear
- `IsAlgClosure`: typeclass for an algebraic closure of a ring
- `IsAlgClosure.equiv`: any two algebraic closures are isomorphic

### Notation: D[X₁, …, Xₖ]

BPR defines polynomials over a ring D in k variables. In Lean, this is:

```
-- D[X₁, …, Xₖ] is expressed as:
MvPolynomial (Fin k) D    -- where [CommSemiring D]

-- The variable Xᵢ (1-indexed in BPR, 0-indexed in Lean):
MvPolynomial.X (i : Fin k)

-- A constant from D:
MvPolynomial.C (d : D)
```

See: `Mathlib.RingTheory.MvPolynomial.Basic`
-/

namespace Azurite.BPR

open MvPolynomial Polynomial

-- C is an algebraically closed field, used throughout BPR Chapter 1.
variable {k : ℕ} {C : Type*} [Field C] [IsAlgClosed C]

/-!
If 𝒫 is a finite subset of C[X₁, …, Xₖ], the **set of zeros** of 𝒫 in Cᵏ is

  Zer(𝒫, Cᵏ) = { x ∈ Cᵏ | ∀ P ∈ 𝒫, P(x) = 0 }

Mathlib already has `MvPolynomial.zeroLocus`, but it takes an `Ideal` rather than
a finite set of polynomials. We define `Zer` to match BPR's notation and prove
it equals Mathlib's `zeroLocus` applied to the spanned ideal.
-/

/-!
### Notation 1.1 (Zero Set)

The set of common zeros of a set of polynomials 𝒫 in Cᵏ.
BPR notation: Zer(𝒫, Cᵏ).
-/
def Zer (𝒫 : Set (MvPolynomial (Fin k) C)) : Set (Fin k → C) :=
  { x | ∀ P ∈ 𝒫, MvPolynomial.eval x P = 0 }

/-- `Zer 𝒫` equals Mathlib's `zeroLocus` of the ideal spanned by 𝒫. -/
theorem zer_eq_zeroLocus (𝒫 : Set (MvPolynomial (Fin k) C)) :
    Zer 𝒫 = MvPolynomial.zeroLocus C (Ideal.span 𝒫) := by
  ext x
  simp only [Zer, MvPolynomial.zeroLocus, Set.mem_setOf_eq, MvPolynomial.mem_zeroLocus_iff]
  constructor
  · intro h p hp
    refine Submodule.span_induction hp h ?_ ?_ ?_
    · simp
    · intro a b ha hb
      simp [ha, hb]
    · intro a p hp
      simp [hp]
  · intro h p hp
    exact h p (Ideal.subset_span hp)

/-!
A subset V of Cᵏ is an **algebraic set** (or **algebraic subset**) if
V = Zer(𝒫, Cᵏ) for some set of polynomials 𝒫 ⊆ C[X₁, …, Xₖ].

This does not appear to exist in Mathlib (Mathlib works with `zeroLocus` of ideals
but does not name the predicate "is an algebraic set" at this level).
-/

/-- A subset V of Cᵏ is algebraic if it is the zero set of some set of polynomials. -/
def IsAlgebraicSet (V : Set (Fin k → C)) : Prop :=
  ∃ 𝒫 : Set (MvPolynomial (Fin k) C), V = Zer 𝒫

/-- Cᵏ is an algebraic set (take 𝒫 = ∅). -/
theorem isAlgebraicSet_univ : IsAlgebraicSet (Set.univ : Set (Fin k → C)) :=
  ⟨∅, by ext x; simp [Zer]⟩

/-!
### Exercise 1.1

An algebraic subset of C (i.e. C¹) is either finite or all of C.
-/

/-- The algebra equivalence MvPolynomial (Fin 1) C ≃ₐ[C] C[X]. -/
noncomputable def mvPolyFinOneEquiv :
    MvPolynomial (Fin 1) C ≃ₐ[C] C[X] :=
  (finSuccEquiv C 0).trans
    (Polynomial.mapAlgEquiv (isEmptyAlgEquiv C (Fin 0)))

/-- MvPolynomial.eval at a constant function factors through
    the one-variable equivalence. -/
theorem eval_eq_polynomial_eval
    (P : MvPolynomial (Fin 1) C) (c : C) :
    MvPolynomial.eval (fun _ => c) P =
      Polynomial.eval c (mvPolyFinOneEquiv P) := by
  simp only [mvPolyFinOneEquiv]
  rw [AlgEquiv.trans_apply, Polynomial.mapAlgEquiv_apply]
  have h := eval_polynomial_eval_finSuccEquiv P
    (MvPolynomial.C c : MvPolynomial (Fin 0) C)
  simp [MvPolynomial.eval_C] at h
  rw [← h]
  congr 1
  simp [Polynomial.eval_map]
  congr 1
  ext x; exact Fin.elim0 x

/-- Exercise 1.1: An algebraic subset of C is either finite
    or all of C. -/
theorem exercise_1_1 (V : Set (Fin 1 → C))
    (hV : IsAlgebraicSet V) :
    V.Finite ∨ V = Set.univ := by
  obtain ⟨𝒫, rfl⟩ := hV
  by_cases h : ∀ P ∈ 𝒫, P = 0
  · -- All polynomials are zero ⟹ Zer 𝒫 = Cᵏ
    right
    ext x
    simp only [Zer, Set.mem_setOf_eq, Set.mem_univ, iff_true]
    intro P hP; rw [h P hP]; simp
  · -- Some P₀ ∈ 𝒫 is nonzero ⟹ Zer 𝒫 ⊆ roots(P₀)
    push_neg at h
    obtain ⟨P₀, hP₀mem, hP₀ne⟩ := h
    left
    apply Set.Finite.subset _ (fun x hx => hx P₀ hP₀mem)
    -- Transfer through (Fin 1 → C) ≃ C
    let e : (Fin 1 → C) ≃ C := Equiv.funUnique (Fin 1) C
    rw [show { x : Fin 1 → C |
          MvPolynomial.eval x P₀ = 0 } =
        e.symm '' { c : C |
          Polynomial.eval c (mvPolyFinOneEquiv P₀) = 0 }
      from by
      ext x
      simp only [e, Equiv.funUnique, Set.mem_setOf_eq,
        Set.mem_image, Equiv.coe_fn_symm_mk]
      constructor
      · intro hx
        exact ⟨x 0, by
          rw [← eval_eq_polynomial_eval]
          convert hx; ext i; exact (Fin.eq_zero i).symm ▸ rfl,
          by ext i; exact (Fin.eq_zero i).symm ▸ rfl⟩
      · rintro ⟨c, hc, rfl⟩
        rw [← eval_eq_polynomial_eval] at hc
        simpa using hc]
    apply Set.Finite.image
    exact Polynomial.finite_setOf_isRoot
      (by intro h; exact hP₀ne (mvPolyFinOneEquiv.injective
        (by rw [h, map_zero])))

/-!
A **basic constructible set** over Cᵏ is a member of the smallest
family of subsets of Cᵏ that includes the algebraic sets and their
complements, and is closed under finite intersections.
-/

/-- A basic constructible subset of Cᵏ. -/
inductive IsBasicConstructibleSet :
    Set (Fin k → C) → Prop where
  | algebraic {V} :
      IsAlgebraicSet V → IsBasicConstructibleSet V
  | compl_algebraic {V} :
      IsAlgebraicSet V → IsBasicConstructibleSet Vᶜ
  | inter {V W} :
      IsBasicConstructibleSet V →
      IsBasicConstructibleSet W →
      IsBasicConstructibleSet (V ∩ W)

/-!
A **constructible set** over Cᵏ is a member of the smallest family of
subsets of Cᵏ that includes the algebraic sets and is closed under
complementation, finite unions, and finite intersections.

We define with complement and intersection only; closure under union
follows by De Morgan.
-/

/-- A constructible subset of Cᵏ. -/
inductive IsConstructibleSet :
    Set (Fin k → C) → Prop where
  | algebraic {V} :
      IsAlgebraicSet V → IsConstructibleSet V
  | compl {V} :
      IsConstructibleSet V → IsConstructibleSet Vᶜ
  | inter {V W} :
      IsConstructibleSet V →
      IsConstructibleSet W →
      IsConstructibleSet (V ∩ W)

/-- Constructible sets are closed under finite union (by De Morgan). -/
theorem IsConstructibleSet.union {V W : Set (Fin k → C)}
    (hV : IsConstructibleSet V)
    (hW : IsConstructibleSet W) :
    IsConstructibleSet (V ∪ W) := by
  rw [Set.union_eq_compl_compl_inter_compl]
  exact .compl (.inter (.compl hV) (.compl hW))

/-!
### Exercise 1.2

A constructible subset of C is either finite or the complement
of a finite set.
-/

/-- Exercise 1.2: A constructible subset of C is either finite
    or cofinite. -/
theorem exercise_1_2 (V : Set (Fin 1 → C))
    (hV : IsConstructibleSet V) :
    V.Finite ∨ Vᶜ.Finite := by
  induction hV with
  | algebraic hA =>
    rcases exercise_1_1 _ hA with hfin | huniv
    · exact Or.inl hfin
    · right; rw [huniv]; simp
  | compl _ ih =>
    rcases ih with h | h
    · exact Or.inr (by rwa [Set.compl_compl])
    · exact Or.inl h
  | inter _ _ ihV ihW =>
    rcases ihV, ihW with ⟨hV | hV, hW | hW⟩
    · exact Or.inl (hV.subset Set.inter_subset_left)
    · exact Or.inl (hV.subset Set.inter_subset_left)
    · exact Or.inl (hW.subset Set.inter_subset_right)
    · right; rw [Set.compl_inter]; exact hV.union hW

/-!
### Exercise 1.3

A constructible set in Cᵏ is a finite union of basic
constructible sets.
-/

/-- V is a finite union of basic constructible sets. -/
inductive IsFinUnionBasicConstructible :
    Set (Fin k → C) → Prop where
  | basic {V} : IsBasicConstructibleSet V →
      IsFinUnionBasicConstructible V
  | union {V W} : IsFinUnionBasicConstructible V →
      IsFinUnionBasicConstructible W →
      IsFinUnionBasicConstructible (V ∪ W)

private theorem compl_basic_fin_union
    {V : Set (Fin k → C)}
    (hV : IsBasicConstructibleSet V) :
    IsFinUnionBasicConstructible Vᶜ := by
  induction hV with
  | algebraic hA => exact .basic (.compl_algebraic hA)
  | compl_algebraic hA =>
    rw [Set.compl_compl]; exact .basic (.algebraic hA)
  | inter _ _ ih₁ ih₂ =>
    rw [Set.compl_inter]; exact .union ih₁ ih₂

private theorem basic_inter_fin_union
    {B W : Set (Fin k → C)}
    (hB : IsBasicConstructibleSet B)
    (hW : IsFinUnionBasicConstructible W) :
    IsFinUnionBasicConstructible (B ∩ W) := by
  induction hW with
  | basic hW' => exact .basic (.inter hB hW')
  | union _ _ ih₁ ih₂ =>
    rw [Set.inter_union_distrib_left]
    exact .union ih₁ ih₂

private theorem inter_fin_union
    {V W : Set (Fin k → C)}
    (hV : IsFinUnionBasicConstructible V)
    (hW : IsFinUnionBasicConstructible W) :
    IsFinUnionBasicConstructible (V ∩ W) := by
  induction hV with
  | basic hB => exact basic_inter_fin_union hB hW
  | union _ _ ih₁ ih₂ =>
    rw [Set.union_inter_distrib_right]
    exact .union (ih₁ hW) (ih₂ hW)

private theorem compl_fin_union {V : Set (Fin k → C)}
    (hV : IsFinUnionBasicConstructible V) :
    IsFinUnionBasicConstructible Vᶜ := by
  induction hV with
  | basic hB => exact compl_basic_fin_union hB
  | union _ _ ih₁ ih₂ =>
    rw [Set.compl_union]; exact inter_fin_union ih₁ ih₂

/-- Exercise 1.3: A constructible set is a finite union of
    basic constructible sets. -/
theorem exercise_1_3 {V : Set (Fin k → C)}
    (hV : IsConstructibleSet V) :
    IsFinUnionBasicConstructible V := by
  induction hV with
  | algebraic hA => exact .basic (.algebraic hA)
  | compl _ ih => exact compl_fin_union ih
  | inter _ _ ih₁ ih₂ => exact inter_fin_union ih₁ ih₂

/-!
### The Language of Fields

Let D be a subring of C. We define first-order formulas in the
language of fields with coefficients in D.

Atoms are `P = 0` where P ∈ D[X₁, …, Xₖ]. The constructors
are `eq_zero`, `not`, `and`, `or`, and `exists_`. We derive
`ne_zero` (= ¬(P = 0)), `forall_` (= ¬∃x, ¬Φ), and `implies`
(= ¬Φ ∨ Ψ) as abbreviations.
-/

/-- First-order formulas in the language of fields with
    coefficients in D. Variables are indexed by type σ. -/
inductive Formula (D : Type*) [CommRing D]
    (σ : Type*) where
  | eq_zero  : MvPolynomial σ D → Formula D σ
  | not      : Formula D σ → Formula D σ
  | and      : Formula D σ → Formula D σ → Formula D σ
  | or       : Formula D σ → Formula D σ → Formula D σ
  | exists_  : σ → Formula D σ → Formula D σ

namespace Formula

/-- P ≠ 0 as a formula. -/
def ne_zero (P : MvPolynomial σ D) : Formula D σ :=
  .not (.eq_zero P)

/-- Universal quantification: ∀x, Φ  :=  ¬∃x, ¬Φ. -/
def forall_ (x : σ) (Φ : Formula D σ) : Formula D σ :=
  .not (.exists_ x (.not Φ))

/-- Implication: Φ ⇒ Ψ  :=  ¬Φ ∨ Ψ. -/
def implies (Φ Ψ : Formula D σ) : Formula D σ :=
  .or (.not Φ) Ψ

variable {D : Type*} [CommRing D] {σ : Type*}

/-- The free variables of a formula. -/
def freeVars [DecidableEq σ] :
    Formula D σ → Finset σ
  | .eq_zero P   => P.vars
  | .not Φ       => Φ.freeVars
  | .and Φ₁ Φ₂   => Φ₁.freeVars ∪ Φ₂.freeVars
  | .or Φ₁ Φ₂    => Φ₁.freeVars ∪ Φ₂.freeVars
  | .exists_ x Φ => Φ.freeVars \ {x}

/-- A sentence is a formula with no free variables. -/
def isSentence [DecidableEq σ] (Φ : Formula D σ) :
    Prop :=
  Φ.freeVars = ∅

/-- A formula is quantifier-free if no quantifier (∃ or ∀)
    appears in it. -/
def IsQuantifierFree : Formula D σ → Prop
  | .eq_zero _   => True
  | .not Φ       => Φ.IsQuantifierFree
  | .and Φ₁ Φ₂   => Φ₁.IsQuantifierFree ∧ Φ₂.IsQuantifierFree
  | .or Φ₁ Φ₂    => Φ₁.IsQuantifierFree ∧ Φ₂.IsQuantifierFree
  | .exists_ _ _ => False

/-- A basic formula is a conjunction of atoms
    (P = 0 or P ≠ 0). -/
inductive IsBasicFormula : Formula D σ → Prop where
  | eq_zero (P : MvPolynomial σ D) :
      IsBasicFormula (.eq_zero P)
  | ne_zero (P : MvPolynomial σ D) :
      IsBasicFormula (.not (.eq_zero P))
  | and {Φ₁ Φ₂} :
      IsBasicFormula Φ₁ → IsBasicFormula Φ₂ →
      IsBasicFormula (.and Φ₁ Φ₂)

theorem IsBasicFormula.isQuantifierFree
    {Φ : Formula D σ} (h : IsBasicFormula Φ) :
    Φ.IsQuantifierFree := by
  induction h with
  | eq_zero _ => trivial
  | ne_zero _ => trivial
  | and _ _ ih₁ ih₂ => exact ⟨ih₁, ih₂⟩

end Formula

end Azurite.BPR
