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

The set of common zeros of a finite set of polynomials 𝒫 in Cᵏ.
BPR notation: Zer(𝒫, Cᵏ).
-/
def Zer (𝒫 : Finset (MvPolynomial (Fin k) C)) : Set (Fin k → C) :=
  { x | ∀ P ∈ 𝒫, MvPolynomial.eval x P = 0 }

/-- `Zer 𝒫` equals Mathlib's `zeroLocus` of the ideal spanned by 𝒫. -/
theorem zer_eq_zeroLocus (𝒫 : Finset (MvPolynomial (Fin k) C)) :
    Zer 𝒫 = MvPolynomial.zeroLocus C (Ideal.span (↑𝒫 : Set _)) := by
  ext x
  simp only [Zer, MvPolynomial.zeroLocus, Set.mem_setOf_eq, MvPolynomial.mem_zeroLocus_iff]
  constructor
  · intro h p hp
    refine Submodule.span_induction hp
      (fun q hq => h q (by exact_mod_cast hq)) ?_ ?_ ?_
    · simp
    · intro a b ha hb
      simp [ha, hb]
    · intro a p hp
      simp [hp]
  · intro h p hp
    exact h p (Ideal.subset_span (by exact_mod_cast hp))

/-!
A subset V of Cᵏ is an **algebraic set** (or **algebraic subset**) if
V = Zer(𝒫, Cᵏ) for some finite set of polynomials 𝒫 ⊆ C[X₁, …, Xₖ].

This does not appear to exist in Mathlib (Mathlib works with `zeroLocus` of ideals
but does not name the predicate "is an algebraic set" at this level).
-/

/-- A subset V of Cᵏ is algebraic if it is the zero set of some finite set of polynomials. -/
def IsAlgebraicSet (V : Set (Fin k → C)) : Prop :=
  ∃ 𝒫 : Finset (MvPolynomial (Fin k) C), V = Zer 𝒫

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

/-!
### Prenex Normal Form

A formula is in **prenex normal form** if it is a sequence
of quantifiers (∀ or ∃) applied to a quantifier-free body:

  (Qu₁ X₁) ⋯ (Quₘ Xₘ) 𝓑(X₁, …, Xₘ, Y₁, …, Yₖ)

Since ∀ is encoded as ¬∃¬ in our syntax, the `forall_`
constructor pattern-matches that encoding.
-/

/-- A formula in prenex normal form. -/
inductive IsPrenex : Formula D σ → Prop where
  | qf {Φ} : Φ.IsQuantifierFree → IsPrenex Φ
  | exists_ {x : σ} {Φ} :
      IsPrenex Φ → IsPrenex (.exists_ x Φ)
  | forall_ {x : σ} {Φ} :
      IsPrenex Φ →
      IsPrenex (.not (.exists_ x (.not Φ)))

/-!
### Realization

The **C-realization** of a formula Φ with free variables
in {Y₁, …, Yₖ}, denoted Reali(Φ, Cᵏ), is the set of
y ∈ Cᵏ such that Φ(y) is true.

Here D is a subring of C (expressed via `[Algebra D C]`),
and `aeval` handles the coercion of coefficients from D to C.
-/

variable {C : Type*} [Field C] [Algebra D C]

/-- The C-realization of a formula: the set of assignments
    y : σ → C such that Φ(y) is true.
    BPR notation: Reali(Φ, Cᵏ). -/
def realization [DecidableEq σ] :
    Formula D σ → Set (σ → C)
  | .eq_zero P   => { y | aeval y P = 0 }
  | .not Φ       => (Φ.realization)ᶜ
  | .and Φ₁ Φ₂   => Φ₁.realization ∩ Φ₂.realization
  | .or Φ₁ Φ₂    => Φ₁.realization ∪ Φ₂.realization
  | .exists_ x Φ =>
    { y | ∃ c : C, Function.update y x c ∈ Φ.realization }

def CEquiv [DecidableEq σ]
    (Φ Ψ : Formula D σ) : Prop :=
  (realization (C := C) Φ) = (realization (C := C) Ψ)

/-!
### Prenex Normal Form Infrastructure

Variable renaming, realization invariance, and the prenex
normal form theorem.
-/

/-- Rename variables in a formula via `f : σ → τ`. -/
def rename (f : σ → τ) : Formula D σ → Formula D τ
  | .eq_zero P   => .eq_zero (P.rename f)
  | .not Φ       => .not (Φ.rename f)
  | .and Φ₁ Φ₂   => .and (Φ₁.rename f) (Φ₂.rename f)
  | .or Φ₁ Φ₂    => .or (Φ₁.rename f) (Φ₂.rename f)
  | .exists_ x Φ => .exists_ (f x) (Φ.rename f)

theorem rename_isQF (f : σ → τ) :
    ∀ (Φ : Formula D σ), Φ.IsQuantifierFree →
    (Φ.rename f).IsQuantifierFree
  | .eq_zero _, _ => trivial
  | .not Φ, h => rename_isQF f Φ h
  | .and Φ₁ Φ₂, ⟨h₁, h₂⟩ =>
    ⟨rename_isQF f Φ₁ h₁, rename_isQF f Φ₂ h₂⟩
  | .or Φ₁ Φ₂, ⟨h₁, h₂⟩ =>
    ⟨rename_isQF f Φ₁ h₁, rename_isQF f Φ₂ h₂⟩

theorem rename_isPrenex (f : σ → τ) {Φ : Formula D σ}
    (h : IsPrenex Φ) : IsPrenex (Φ.rename f) := by
  induction h with
  | qf hqf => exact .qf (rename_isQF f _ hqf)
  | exists_ _ ih => exact .exists_ ih
  | forall_ _ ih => exact .forall_ ih

/-- Quantifier depth of a formula. -/
def quantifierDepth : Formula D σ → ℕ
  | .eq_zero _   => 0
  | .not Φ       => Φ.quantifierDepth
  | .and Φ₁ Φ₂   => Φ₁.quantifierDepth + Φ₂.quantifierDepth
  | .or Φ₁ Φ₂    => Φ₁.quantifierDepth + Φ₂.quantifierDepth
  | .exists_ _ Φ => Φ.quantifierDepth + 1

theorem rename_quantifierDepth (f : σ → τ)
    (Φ : Formula D σ) :
    (Φ.rename f).quantifierDepth = Φ.quantifierDepth := by
  induction Φ with
  | eq_zero => simp [rename, quantifierDepth]
  | not _ ih => simp [rename, quantifierDepth, ih]
  | and _ _ ih₁ ih₂ =>
    simp [rename, quantifierDepth, ih₁, ih₂]
  | or _ _ ih₁ ih₂ =>
    simp [rename, quantifierDepth, ih₁, ih₂]
  | exists_ _ _ ih =>
    simp [rename, quantifierDepth, ih]

theorem rename_realization [DecidableEq σ] [DecidableEq τ]
    (f : σ → τ) (hf : Function.Injective f)
    (Φ : Formula D σ) :
    (Φ.rename f).realization (C := C) =
      (· ∘ f) ⁻¹' Φ.realization := by
  induction Φ with
  | eq_zero P =>
    ext y; simp [rename, realization, aeval_rename]
  | not _ ih =>
    simp [rename, realization, ih, Set.preimage_compl]
  | and _ _ ih₁ ih₂ =>
    simp [rename, realization, ih₁, ih₂,
      Set.preimage_inter]
  | or _ _ ih₁ ih₂ =>
    simp [rename, realization, ih₁, ih₂,
      Set.preimage_union]
  | exists_ x _ ih =>
    ext y
    simp only [rename, realization, Set.mem_setOf_eq,
      Set.mem_preimage, ih]
    constructor <;> rintro ⟨c, hc⟩ <;> refine ⟨c, ?_⟩ <;>
    · convert hc using 1; ext i
      simp [Function.update, hf.eq_iff]

private theorem aeval_update_of_not_mem_vars
    [DecidableEq σ] (P : MvPolynomial σ D)
    (y : σ → C) (x : σ) (c : C) (hx : x ∉ P.vars) :
    aeval (Function.update y x c) P = aeval y P :=
  aeval_eq_aeval_of_forall_mem_vars_eq _ _ _
    (fun v hv => by simp [Function.update_apply,
      show v ≠ x from fun h => hx (h ▸ hv)])

theorem realization_invariant_update [DecidableEq σ]
    (Φ : Formula D σ) (x : σ) (hx : x ∉ Φ.freeVars)
    (y : σ → C) (c : C) :
    y ∈ Φ.realization (C := C) ↔
    Function.update y x c ∈ Φ.realization := by
  induction Φ with
  | eq_zero P =>
    simp only [realization, Set.mem_setOf_eq, freeVars] at *
    rw [aeval_update_of_not_mem_vars P y x c hx]
  | not _ ih =>
    simp only [realization, Set.mem_compl_iff, freeVars] at *
    rw [ih hx]
  | and _ _ ih₁ ih₂ =>
    simp only [realization, Set.mem_inter_iff, freeVars,
      Finset.mem_union, not_or] at *
    rw [ih₁ hx.1, ih₂ hx.2]
  | or _ _ ih₁ ih₂ =>
    simp only [realization, Set.mem_union, freeVars,
      Finset.mem_union, not_or] at *
    rw [ih₁ hx.1, ih₂ hx.2]
  | exists_ z _ ih =>
    simp only [realization, Set.mem_setOf_eq, freeVars,
      Finset.mem_sdiff, Finset.mem_singleton] at *
    push_neg at hx
    constructor <;> rintro ⟨d, hd⟩ <;> refine ⟨d, ?_⟩
    · rw [Function.update_comm (hx.1 rfl).elim]
      rwa [← ih (hx.1 rfl).elim]
    · rw [Function.update_comm (hx.1 rfl).elim] at hd
      rwa [ih (hx.1 rfl).elim]

/-- (∃x, A) ∧ B ≡ ∃x, (A ∧ B) when x ∉ freeVars B. -/
theorem exists_and_equiv [DecidableEq σ]
    (A B : Formula D σ) (x : σ) (hx : x ∉ B.freeVars) :
    (.exists_ x A).realization (C := C) ∩ B.realization =
    (.exists_ x (.and A B)).realization := by
  ext y
  simp only [realization, Set.mem_inter_iff,
    Set.mem_setOf_eq]
  constructor
  · rintro ⟨⟨c, hc⟩, hB⟩
    exact ⟨c, hc,
      (realization_invariant_update B x hx y c).mp hB⟩
  · rintro ⟨c, hA, hB⟩
    exact ⟨⟨c, hA⟩,
      (realization_invariant_update B x hx y c).mpr hB⟩

/-- (∀x, A) ∧ B ≡ ∀x, (A ∧ B) when x ∉ freeVars B. -/
theorem forall_and_equiv [DecidableEq σ]
    (A B : Formula D σ) (x : σ) (hx : x ∉ B.freeVars) :
    (.not (.exists_ x (.not A))).realization (C := C) ∩
      B.realization =
    (.not (.exists_ x (.not (.and A B)))).realization := by
  ext y
  simp only [realization, Set.mem_inter_iff,
    Set.mem_compl_iff, Set.mem_setOf_eq, not_exists,
    not_not]
  constructor
  · rintro ⟨hA, hB⟩ c
    exact ⟨hA c,
      (realization_invariant_update B x hx y c).mp hB⟩
  · intro h
    exact ⟨fun c => (h c).1,
      by have := (h (y x)).2
         rwa [Function.update_self] at this⟩

/-- ∃x,A has same realization as ∃z,(A.rename(swap x z)). -/
theorem exists_rename_swap [DecidableEq σ]
    (A : Formula D σ) (x z : σ) :
    (.exists_ x A).realization (C := C) =
    (.exists_ z (A.rename (Equiv.swap x z))).realization := by
  ext y; simp only [realization, Set.mem_setOf_eq,
    rename_realization _ (Equiv.swap x z).injective,
    Set.mem_preimage]
  constructor <;> rintro ⟨c, hc⟩ <;> exact ⟨c, by
    convert hc using 1; ext i
    simp [Function.update, Equiv.swap_apply_def]
    split_ifs <;> simp_all⟩

/-- ∀x,A has same realization as ∀z,(A.rename(swap x z)). -/
theorem forall_rename_swap [DecidableEq σ]
    (A : Formula D σ) (x z : σ) :
    (.not (.exists_ x (.not A))).realization (C := C) =
    (.not (.exists_ z (.not (A.rename
      (Equiv.swap x z))))).realization := by
  simp only [realization, Set.compl_setOf, not_exists,
    not_not, rename_realization _
      (Equiv.swap x z).injective, Set.mem_preimage]
  ext y; simp only [Set.mem_setOf_eq]
  constructor <;> intro h c <;>
  · have := h c; convert this using 1; ext i
    simp [Function.update, Equiv.swap_apply_def]
    split_ifs <;> simp_all

/-- Given a prenex Ψ, produce a prenex formula with
    realization = Ψ.realizationᶜ. -/
theorem negatePrenex [DecidableEq σ]
    {Ψ : Formula D σ} (hΨ : IsPrenex Ψ) :
    ∃ Ψ', IsPrenex Ψ' ∧
      Ψ'.realization (C := C) = (Ψ.realization)ᶜ := by
  induction hΨ with
  | qf hqf =>
    exact ⟨.not Ψ,
      .qf (by cases Ψ <;> simp_all [IsQuantifierFree]),
      by simp [realization]⟩
  | @exists_ x Ψ' _ ih =>
    obtain ⟨N, hN, hNr⟩ := ih
    exact ⟨.not (.exists_ x (.not N)), .forall_ hN, by
      ext y; simp [realization, Set.mem_compl_iff,
        not_exists]
      constructor
      · intro h c
        rw [← Set.mem_compl_iff, ← hNr]; exact h c
      · intro h c
        rw [hNr, Set.mem_compl_iff]; exact h c⟩
  | @forall_ x Ψ' _ ih =>
    obtain ⟨N, hN, hNr⟩ := ih
    exact ⟨.exists_ x N, .exists_ hN, by
      ext y; simp [realization, Set.mem_compl_iff,
        not_not, not_forall]; push_neg
      constructor
      · rintro ⟨c, hc⟩
        exact ⟨c, by rwa [← Set.mem_compl_iff, ← hNr]⟩
      · rintro ⟨c, hc⟩
        exact ⟨c, by rwa [hNr, Set.mem_compl_iff] at hc⟩⟩

private theorem pull_exists [Infinite σ] [DecidableEq σ]
    (x : σ) (A B : Formula D σ) (hA : IsPrenex A)
    (hB : IsPrenex B)
    (ih : ∀ A' B', IsPrenex A' → IsPrenex B' →
      A'.quantifierDepth + B'.quantifierDepth <
        A.quantifierDepth + 1 + B.quantifierDepth →
      ∃ R, IsPrenex R ∧ R.realization (C := C) =
        A'.realization ∩ B'.realization) :
    ∃ R, IsPrenex R ∧ R.realization (C := C) =
      (.exists_ x A).realization (C := C) ∩
        B.realization := by
  obtain ⟨z, hz⟩ :=
    (A.freeVars ∪ B.freeVars).exists_not_mem
  rw [Finset.mem_union, not_or] at hz
  rw [exists_rename_swap A x z]
  obtain ⟨R, hR, hRr⟩ := ih _ _
    (rename_isPrenex _ hA) hB
    (by rw [rename_quantifierDepth]; omega)
  exact ⟨.exists_ z R, .exists_ hR, by
    ext y; simp [realization, Set.mem_setOf_eq]
    constructor
    · rintro ⟨⟨c, hc⟩, h2⟩; exact ⟨c, by
        rw [hRr, Set.mem_inter_iff]; exact ⟨hc,
        (realization_invariant_update B z hz.2 y c).mp h2⟩⟩
    · rintro ⟨c, hc⟩; rw [hRr, Set.mem_inter_iff] at hc
      exact ⟨⟨c, hc.1⟩,
        (realization_invariant_update B z hz.2 y c).mpr
          hc.2⟩⟩

private theorem pull_forall [Infinite σ] [DecidableEq σ]
    (x : σ) (A B : Formula D σ) (hA : IsPrenex A)
    (hB : IsPrenex B)
    (ih : ∀ A' B', IsPrenex A' → IsPrenex B' →
      A'.quantifierDepth + B'.quantifierDepth <
        A.quantifierDepth + 1 + B.quantifierDepth →
      ∃ R, IsPrenex R ∧ R.realization (C := C) =
        A'.realization ∩ B'.realization) :
    ∃ R, IsPrenex R ∧ R.realization (C := C) =
      (.not (.exists_ x (.not A))).realization (C := C) ∩
        B.realization := by
  obtain ⟨z, hz⟩ :=
    (A.freeVars ∪ B.freeVars).exists_not_mem
  rw [Finset.mem_union, not_or] at hz
  rw [forall_rename_swap A x z]
  obtain ⟨R, hR, hRr⟩ := ih _ _
    (rename_isPrenex _ hA) hB
    (by rw [rename_quantifierDepth]; omega)
  exact ⟨.not (.exists_ z (.not R)), .forall_ hR, by
    ext y; simp [realization, not_exists, not_not]
    constructor
    · rintro ⟨hA', h2⟩ c; rw [hRr, Set.mem_inter_iff]
      exact ⟨hA' c,
        (realization_invariant_update B z hz.2 y c).mp h2⟩
    · intro h
      exact ⟨fun c => (by rw [hRr] at h; exact (h c).1),
        by have := (h (y z)).2
           rw [hRr, Set.mem_inter_iff] at this
           exact (realization_invariant_update B z hz.2
             y _).mpr this.2⟩⟩

/-- Combine two prenex formulas into a prenex conjunction. -/
theorem andPrenex [Infinite σ] [DecidableEq σ]
    (Ψ₁ Ψ₂ : Formula D σ) (hp₁ : IsPrenex Ψ₁)
    (hp₂ : IsPrenex Ψ₂) :
    ∃ R, IsPrenex R ∧ R.realization (C := C) =
      Ψ₁.realization ∩ Ψ₂.realization := by
  induction hd : Ψ₁.quantifierDepth + Ψ₂.quantifierDepth
    using Nat.strongRecOn generalizing Ψ₁ Ψ₂ with
  | _ n ih =>
  match hp₁, hp₂ with
  | .qf h₁, .qf h₂ =>
    exact ⟨.and Ψ₁ Ψ₂, .qf ⟨h₁, h₂⟩, rfl⟩
  | .qf _, .exists_ (x := x) hB =>
    rw [Set.inter_comm]; exact pull_exists x _ Ψ₁ ‹_›
      (.qf ‹_›) fun A' B' hA' hB' hlt =>
        ih _ (by omega) A' B' hA' hB' rfl
  | .qf _, .forall_ (x := x) hB =>
    rw [Set.inter_comm]; exact pull_forall x _ Ψ₁ ‹_›
      (.qf ‹_›) fun A' B' hA' hB' hlt =>
        ih _ (by omega) A' B' hA' hB' rfl
  | .exists_ (x := x) hA, _ =>
    exact pull_exists x _ Ψ₂ ‹_› hp₂
      fun A' B' hA' hB' hlt =>
        ih _ (by omega) A' B' hA' hB' rfl
  | .forall_ (x := x) hA, _ =>
    exact pull_forall x _ Ψ₂ ‹_› hp₂
      fun A' B' hA' hB' hlt =>
        ih _ (by omega) A' B' hA' hB' rfl

/-- Every formula over an infinite variable type is
    C-equivalent to a prenex formula. -/
theorem prenex_normal_form [Infinite σ] [DecidableEq σ]
    (Φ : Formula D σ) :
    ∃ Ψ : Formula D σ, IsPrenex Ψ ∧
      CEquiv (C := C) Φ Ψ := by
  induction Φ with
  | eq_zero P => exact ⟨_, .qf trivial, rfl⟩
  | not Φ ih =>
    obtain ⟨Ψ, hpre, hequiv⟩ := ih
    suffices ∃ Ψ', IsPrenex Ψ' ∧
        Ψ'.realization (C := C) = (Ψ.realization)ᶜ by
      obtain ⟨Ψ', hp, hr⟩ := this
      exact ⟨Ψ', hp, show (.not Φ).realization = _ by
        simp [realization, hequiv, hr]⟩
    clear hequiv Φ
    induction hpre with
    | qf hqf =>
      exact ⟨.not Ψ,
        .qf (by cases Ψ <;> simp_all [IsQuantifierFree]),
        by simp [realization]⟩
    | @exists_ x Ψ' _ ih' =>
      obtain ⟨N, hN, hNr⟩ := ih'
      exact ⟨.not (.exists_ x (.not N)), .forall_ hN, by
        ext y; simp [realization, Set.mem_compl_iff,
          not_exists]
        constructor
        · intro h c
          rw [← Set.mem_compl_iff, ← hNr]; exact h c
        · intro h c
          rw [hNr, Set.mem_compl_iff]; exact h c⟩
    | @forall_ x Ψ' _ ih' =>
      obtain ⟨N, hN, hNr⟩ := ih'
      exact ⟨.exists_ x N, .exists_ hN, by
        ext y; simp [realization, Set.mem_compl_iff,
          not_not, not_forall]; push_neg
        constructor
        · rintro ⟨c, hc⟩
          exact ⟨c, by rwa [← Set.mem_compl_iff, ← hNr]⟩
        · rintro ⟨c, hc⟩
          exact ⟨c, by rwa [hNr, Set.mem_compl_iff] at hc⟩⟩
  | and Φ₁ Φ₂ ih₁ ih₂ =>
    obtain ⟨Ψ₁, hp₁, he₁⟩ := ih₁
    obtain ⟨Ψ₂, hp₂, he₂⟩ := ih₂
    -- Need prenex R with R.real = Ψ₁.real ∩ Ψ₂.real
    suffices ∃ R, IsPrenex R ∧
        R.realization (C := C) =
          Ψ₁.realization ∩ Ψ₂.realization by
      obtain ⟨R, hR, hRr⟩ := this
      exact ⟨R, hR, show (.and Φ₁ Φ₂).realization = _ by
        simp [realization, he₁, he₂, hRr]⟩
    clear he₁ he₂ Φ₁ Φ₂
    -- andPrenex by well-founded induction on qdepth
    induction hd : Ψ₁.quantifierDepth + Ψ₂.quantifierDepth
      using Nat.strongRecOn generalizing Ψ₁ Ψ₂ with
    | _ n ih =>
    match hp₁, hp₂ with
    | .qf h₁, .qf h₂ =>
      exact ⟨.and Ψ₁ Ψ₂, .qf ⟨h₁, h₂⟩, rfl⟩
    | .qf h₁, .exists_ (x := x) (Φ := B) hB =>
      rw [Set.inter_comm]
      obtain ⟨z, hz⟩ := (Ψ₁.freeVars ∪ B.freeVars).exists_not_mem
      rw [Finset.mem_union, not_or] at hz
      rw [exists_rename_swap B x z]
      have hlt : (B.rename (Equiv.swap x z)).quantifierDepth +
          Ψ₁.quantifierDepth < n := by
        rw [rename_quantifierDepth]; omega
      obtain ⟨R, hR, hRr⟩ := ih _ hlt _ _
        (rename_isPrenex _ hB) (.qf h₁) rfl
      exact ⟨.exists_ z R, .exists_ hR, by
        ext y; simp [realization, Set.mem_setOf_eq]
        constructor
        · rintro ⟨⟨c, hc⟩, h1⟩; exact ⟨c, by
            rw [hRr, Set.mem_inter_iff]; exact ⟨hc,
            (realization_invariant_update Ψ₁ z hz.1 y c).mp h1⟩⟩
        · rintro ⟨c, hc⟩; rw [hRr, Set.mem_inter_iff] at hc
          exact ⟨⟨c, hc.1⟩,
            (realization_invariant_update Ψ₁ z hz.1 y c).mpr hc.2⟩⟩
    | .qf h₁, .forall_ (x := x) (Φ := B) hB =>
      rw [Set.inter_comm]
      obtain ⟨z, hz⟩ := (Ψ₁.freeVars ∪ B.freeVars).exists_not_mem
      rw [Finset.mem_union, not_or] at hz
      rw [forall_rename_swap B x z]
      have hlt : (B.rename (Equiv.swap x z)).quantifierDepth +
          Ψ₁.quantifierDepth < n := by
        rw [rename_quantifierDepth]; omega
      obtain ⟨R, hR, hRr⟩ := ih _ hlt _ _
        (rename_isPrenex _ hB) (.qf h₁) rfl
      exact ⟨.not (.exists_ z (.not R)), .forall_ hR, by
        ext y; simp [realization, not_exists, not_not]
        constructor
        · rintro ⟨hA, h1⟩ c; rw [hRr, Set.mem_inter_iff]
          exact ⟨hA c,
            (realization_invariant_update Ψ₁ z hz.1 y c).mp h1⟩
        · intro h; exact ⟨fun c => (by rw [hRr] at h; exact (h c).1),
            by have := (h (y z)).2
               rw [hRr, Set.mem_inter_iff] at this
               exact (realization_invariant_update Ψ₁ z hz.1 y _).mpr this.2⟩⟩
    | .exists_ (x := x) (Φ := A) hA, _ =>
      obtain ⟨z, hz⟩ := (A.freeVars ∪ Ψ₂.freeVars).exists_not_mem
      rw [Finset.mem_union, not_or] at hz
      rw [exists_rename_swap A x z]
      have hlt : (A.rename (Equiv.swap x z)).quantifierDepth +
          Ψ₂.quantifierDepth < n := by
        rw [rename_quantifierDepth]; omega
      obtain ⟨R, hR, hRr⟩ := ih _ hlt _ _
        (rename_isPrenex _ hA) hp₂ rfl
      exact ⟨.exists_ z R, .exists_ hR, by
        ext y; simp [realization, Set.mem_setOf_eq]
        constructor
        · rintro ⟨⟨c, hc⟩, h2⟩; exact ⟨c, by
            rw [hRr, Set.mem_inter_iff]; exact ⟨hc,
            (realization_invariant_update Ψ₂ z hz.2 y c).mp h2⟩⟩
        · rintro ⟨c, hc⟩; rw [hRr, Set.mem_inter_iff] at hc
          exact ⟨⟨c, hc.1⟩,
            (realization_invariant_update Ψ₂ z hz.2 y c).mpr hc.2⟩⟩
    | .forall_ (x := x) (Φ := A) hA, _ =>
      obtain ⟨z, hz⟩ := (A.freeVars ∪ Ψ₂.freeVars).exists_not_mem
      rw [Finset.mem_union, not_or] at hz
      rw [forall_rename_swap A x z]
      have hlt : (A.rename (Equiv.swap x z)).quantifierDepth +
          Ψ₂.quantifierDepth < n := by
        rw [rename_quantifierDepth]; omega
      obtain ⟨R, hR, hRr⟩ := ih _ hlt _ _
        (rename_isPrenex _ hA) hp₂ rfl
      exact ⟨.not (.exists_ z (.not R)), .forall_ hR, by
        ext y; simp [realization, not_exists, not_not]
        constructor
        · rintro ⟨hA', h2⟩ c; rw [hRr, Set.mem_inter_iff]
          exact ⟨hA' c,
            (realization_invariant_update Ψ₂ z hz.2 y c).mp h2⟩
        · intro h; exact ⟨fun c => (by rw [hRr] at h; exact (h c).1),
            by have := (h (y z)).2
               rw [hRr, Set.mem_inter_iff] at this
               exact (realization_invariant_update Ψ₂ z hz.2 y _).mpr this.2⟩⟩
  | or Φ₁ Φ₂ ih₁ ih₂ =>
    -- A ∨ B = ¬(¬A ∧ ¬B)
    obtain ⟨Ψ₁, hp₁, he₁⟩ := ih₁
    obtain ⟨Ψ₂, hp₂, he₂⟩ := ih₂
    -- Negate both prenex formulas
    obtain ⟨N₁, hN₁, hN₁r⟩ := negatePrenex (C := C) hp₁
    obtain ⟨N₂, hN₂, hN₂r⟩ := negatePrenex (C := C) hp₂
    -- Combine ¬Ψ₁ ∧ ¬Ψ₂ into prenex
    obtain ⟨R, hR, hRr⟩ := andPrenex (C := C) N₁ N₂ hN₁ hN₂
    -- Negate the result to get ¬(¬Ψ₁ ∧ ¬Ψ₂)
    obtain ⟨S, hS, hSr⟩ := negatePrenex (C := C) hR
    exact ⟨S, hS, by
      show (.or Φ₁ Φ₂).realization = S.realization
      simp only [realization]
      rw [he₁, he₂, hSr, hRr, hN₁r, hN₂r]
      simp [Set.compl_inter]⟩
  | exists_ x Φ ih =>
    obtain ⟨Ψ, hpre, hequiv⟩ := ih
    exact ⟨.exists_ x Ψ, .exists_ hpre, by
      show (.exists_ x Φ).realization = _
      simp [realization, hequiv]⟩

end Formula

/-!
### Example 1.2

Φ = (∃Y)(XY − 1 = 0) and Ψ = (X ≠ 0) are formulas over ℤ
with Free(Φ) = Free(Ψ) = {X}. Ψ is quantifier-free, and
Φ and Ψ are C-equivalent for any algebraically closed field C.
-/

section Example_1_2

open Formula

/-- Φ = ∃Y, XY - 1 = 0  (0 = X, 1 = Y). -/
def Φ_ex : Formula ℤ (Fin 2) :=
  .exists_ 1 (.eq_zero (X 0 * X 1 - 1))

/-- Ψ = X ≠ 0. -/
def Ψ_ex : Formula ℤ (Fin 2) :=
  Formula.ne_zero (X 0)

theorem freeVars_Φ : Φ_ex.freeVars = {0} := by
  native_decide

theorem freeVars_Ψ : Ψ_ex.freeVars = {0} := by
  native_decide

theorem freeVars_eq : Φ_ex.freeVars = Ψ_ex.freeVars := by
  rw [freeVars_Φ, freeVars_Ψ]

theorem Ψ_qf : Ψ_ex.IsQuantifierFree := trivial

variable {C : Type*} [Field C] [IsAlgClosed C]

/-- Example 1.2: Φ and Ψ are C-equivalent. -/
theorem example_1_2 :
    Formula.CEquiv (C := C) Φ_ex Ψ_ex := by
  unfold CEquiv Φ_ex Ψ_ex ne_zero realization
  ext y
  simp only [Set.mem_setOf_eq, Set.mem_compl_iff]
  constructor
  · rintro ⟨c, hc⟩
    simp [aeval_def, eval₂_mul, eval₂_sub, eval₂_X,
      Function.update_self,
      Function.update_noteq
        (by decide : (0 : Fin 2) ≠ 1)] at hc
    intro h0
    rw [h0, zero_mul, zero_sub] at hc
    exact one_ne_zero (neg_eq_zero.mp hc)
  · intro h
    refine ⟨(y 0)⁻¹, ?_⟩
    simp [aeval_def, eval₂_mul, eval₂_sub, eval₂_X,
      Function.update_self,
      Function.update_noteq
        (by decide : (0 : Fin 2) ≠ 1)]
    rw [mul_inv_cancel₀
      (by simpa [aeval_def, eval₂_X] using h),
      sub_self]

end Example_1_2

/-!
### Constructible ↔ QF-Realizable

A set is constructible if and only if it is the realization of
a quantifier-free formula.
-/

namespace Formula

/-- Conjunction of `eq_zero` atoms from a list. -/
def conjEqZero : List (MvPolynomial σ D) → Formula D σ
  | [] => .eq_zero 0
  | [P] => .eq_zero P
  | P :: Ps => .and (.eq_zero P) (conjEqZero Ps)

theorem conjEqZero_isQF :
    ∀ (L : List (MvPolynomial σ D)),
    (conjEqZero L).IsQuantifierFree
  | [] => trivial
  | [_] => trivial
  | _ :: _ :: Ps =>
    ⟨trivial, conjEqZero_isQF (_ :: Ps)⟩

theorem conjEqZero_realization [DecidableEq σ]
    {C : Type*} [Field C] [Algebra D C] :
    ∀ (L : List (MvPolynomial σ D)),
    (conjEqZero L).realization (C := C) =
      { y | ∀ P ∈ L, aeval y P = 0 }
  | [] => by
    ext y; simp [conjEqZero, realization, map_zero]
  | [P] => by
    ext y; simp [conjEqZero, realization]
  | P :: Q :: Ps => by
    ext y
    simp only [conjEqZero, realization, Set.mem_inter_iff,
      Set.mem_setOf_eq, List.mem_cons]
    rw [show (conjEqZero (Q :: Ps)).realization (C := C) =
      { y | ∀ P ∈ (Q :: Ps), aeval y P = 0 }
      from conjEqZero_realization (Q :: Ps)]
    simp only [Set.mem_setOf_eq]
    constructor
    · rintro ⟨hP, hrest⟩ R hR
      rcases hR with rfl | hR
      · exact hP
      · exact hrest R hR
    · intro h
      exact ⟨h P (Or.inl rfl),
        fun R hR => h R (Or.inr hR)⟩

end Formula

open Formula in
/-- Backward: QF-realizable → constructible. -/
theorem qf_realizable_isConstructible
    {Φ : Formula C (Fin k)} (hqf : Φ.IsQuantifierFree) :
    IsConstructibleSet (Φ.realization (C := C)) := by
  induction Φ with
  | eq_zero P =>
    exact .algebraic ⟨{P}, by
      ext y; simp [Zer, realization, aeval_def]⟩
  | not Φ ih => exact .compl (ih hqf)
  | and Φ₁ Φ₂ ih₁ ih₂ =>
    exact .inter (ih₁ hqf.1) (ih₂ hqf.2)
  | or Φ₁ Φ₂ ih₁ ih₂ =>
    exact (ih₁ hqf.1).union (ih₂ hqf.2)
  | exists_ x Φ _ => exact absurd hqf id

open Formula in
/-- Forward: constructible → QF-realizable. -/
theorem constructible_isQFRealizable
    (V : Set (Fin k → C)) (hV : IsConstructibleSet V) :
    ∃ Φ : Formula C (Fin k), Φ.IsQuantifierFree ∧
      V = Φ.realization (C := C) := by
  induction hV with
  | algebraic hA =>
    obtain ⟨𝒫, rfl⟩ := hA
    exact ⟨conjEqZero 𝒫.toList, conjEqZero_isQF _,
      by rw [conjEqZero_realization]
         ext y; simp [Zer, aeval_def]⟩
  | compl _ ih =>
    obtain ⟨Φ, hqf, rfl⟩ := ih
    exact ⟨.not Φ, hqf, by simp [realization]⟩
  | inter _ _ ih₁ ih₂ =>
    obtain ⟨Φ₁, hqf₁, rfl⟩ := ih₁
    obtain ⟨Φ₂, hqf₂, rfl⟩ := ih₂
    exact ⟨.and Φ₁ Φ₂, ⟨hqf₁, hqf₂⟩,
      by simp [realization]⟩

/-- A set is constructible iff it is the realization of a
    quantifier-free formula. -/
theorem constructible_iff_qfRealizable
    (V : Set (Fin k → C)) :
    IsConstructibleSet V ↔
    ∃ Φ : Formula C (Fin k), Φ.IsQuantifierFree ∧
      V = Φ.realization (C := C) :=
  ⟨constructible_isQFRealizable V,
   fun ⟨Φ, hqf, hV⟩ => hV ▸ qf_realizable_isConstructible hqf⟩

end Azurite.BPR
