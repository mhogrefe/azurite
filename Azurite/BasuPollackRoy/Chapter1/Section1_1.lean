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
If poly_set is a finite subset of C[X₁, …, Xₖ], the **set of zeros** of poly_set in Cᵏ is

  Zer(poly_set, Cᵏ) = { x ∈ Cᵏ | ∀ P ∈ poly_set, P(x) = 0 }

Mathlib already has `MvPolynomial.zeroLocus`, but it takes an `Ideal` rather than
a finite set of polynomials. We define `Zer` to match BPR's notation and prove
it equals Mathlib's `zeroLocus` applied to the spanned ideal.
-/

/-!
### Notation 1.1 (Zero Set)

The set of common zeros of a finite set of polynomials poly_set in Cᵏ.
BPR notation: Zer(poly_set, Cᵏ).
-/
def Zer (poly_set : Finset (MvPolynomial (Fin k) C)) : Set (Fin k → C) :=
  { x | ∀ P ∈ poly_set, MvPolynomial.eval x P = 0 }

omit [IsAlgClosed C] in
/-- `Zer poly_set` equals Mathlib's `zeroLocus` of the ideal spanned by poly_set. -/
theorem zer_eq_zeroLocus (poly_set : Finset (MvPolynomial (Fin k) C)) :
    Zer poly_set = MvPolynomial.zeroLocus C (Ideal.span (↑poly_set : Set (MvPolynomial (Fin k) C))) := by
  ext x
  simp only [Zer, Set.mem_setOf_eq, MvPolynomial.mem_zeroLocus_iff]
  constructor
  · intro h p hp
    have eval_eq : ∀ q : MvPolynomial (Fin k) C,
        MvPolynomial.eval x q = (MvPolynomial.aeval x) q := by
      intro q; simp [MvPolynomial.aeval_def]
    rw [← eval_eq]
    induction hp using Submodule.span_induction with
    | mem q hq => exact h q (Finset.mem_coe.mp hq)
    | zero => simp
    | add a b _ _ ha hb => rw [map_add, ha, hb, add_zero]
    | smul a q _ hq => rw [smul_eq_mul, map_mul, hq, mul_zero]
  · intro h p hp
    have := h p (Ideal.subset_span (Finset.mem_coe.mpr hp))
    simpa [MvPolynomial.aeval_def] using this

/-!
A subset V of Cᵏ is an **algebraic set** (or **algebraic subset**) if
V = Zer(poly_set, Cᵏ) for some finite set of polynomials poly_set ⊆ C[X₁, …, Xₖ].

This does not appear to exist in Mathlib (Mathlib works with `zeroLocus` of ideals
but does not name the predicate "is an algebraic set" at this level).
-/

/-- A subset V of Cᵏ is algebraic if it is the zero set of some finite set of polynomials. -/
def IsAlgebraicSet (V : Set (Fin k → C)) : Prop :=
  ∃ poly_set : Finset (MvPolynomial (Fin k) C), V = Zer poly_set

omit [IsAlgClosed C] in
/-- Cᵏ is an algebraic set (take poly_set = ∅). -/
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

omit [IsAlgClosed C] in
/-- MvPolynomial.eval at a constant function factors through
    the one-variable equivalence. -/
theorem eval_eq_polynomial_eval
    (P : MvPolynomial (Fin 1) C) (c : C) :
    MvPolynomial.eval (fun _ => c) P =
      Polynomial.eval c (mvPolyFinOneEquiv P) := by
  have heq : (fun _ : Fin 1 => c) = Fin.cons c Fin.elim0 :=
    funext (fun i => by fin_cases i; rfl)
  rw [heq, MvPolynomial.eval_eq_eval_mv_eval']
  congr 1

omit [IsAlgClosed C] in
/-- Exercise 1.1: An algebraic subset of C is either finite
    or all of C. -/
theorem exercise_1_1 (V : Set (Fin 1 → C))
    (hV : IsAlgebraicSet V) :
    V.Finite ∨ V = Set.univ := by
  obtain ⟨poly_set, rfl⟩ := hV
  by_cases h : ∀ P ∈ poly_set, P = 0
  · -- All polynomials are zero ⟹ Zer poly_set = Cᵏ
    right
    ext x
    simp only [Zer, Set.mem_setOf_eq, Set.mem_univ, iff_true]
    intro P hP; rw [h P hP]; simp
  · -- Some P₀ ∈ poly_set is nonzero ⟹ Zer poly_set ⊆ roots(P₀)
    push_neg at h
    obtain ⟨P₀, hP₀mem, hP₀ne⟩ := h
    left
    apply Set.Finite.subset (s := { x : Fin 1 → C |
        MvPolynomial.eval x P₀ = 0 })
    · -- {x | eval x P₀ = 0} is finite via transfer to C[X]
      let e : (Fin 1 → C) ≃ C := Equiv.funUnique (Fin 1) C
      have hpne : mvPolyFinOneEquiv P₀ ≠ 0 :=
        fun h => hP₀ne (mvPolyFinOneEquiv.injective (by rw [h, map_zero]))
      rw [show { x : Fin 1 → C | MvPolynomial.eval x P₀ = 0 } =
          e.symm '' { c : C | Polynomial.eval c (mvPolyFinOneEquiv P₀) = 0 }
        from by
        ext x; simp only [Set.mem_setOf_eq, Set.mem_image, e, Equiv.funUnique]
        constructor
        · intro hx
          exact ⟨x 0,
            by rwa [← eval_eq_polynomial_eval, show (fun (_ : Fin 1) => x 0) = x from
              _root_.funext fun ⟨i, hi⟩ => by simp [show i = 0 by omega]],
            _root_.funext fun ⟨i, hi⟩ => by simp [show i = 0 by omega]⟩
        · rintro ⟨c, hc, rfl⟩
          show MvPolynomial.eval _ P₀ = 0
          rw [← eval_eq_polynomial_eval] at hc; simpa using hc]
      exact (Polynomial.finite_setOf_isRoot hpne).image _
    · intro x hx; exact hx P₀ hP₀mem

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

omit [IsAlgClosed C] in
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

omit [IsAlgClosed C] in
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
    · exact Or.inr (by rwa [compl_compl])
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

omit [IsAlgClosed C] in
private theorem compl_basic_fin_union
    {V : Set (Fin k → C)}
    (hV : IsBasicConstructibleSet V) :
    IsFinUnionBasicConstructible Vᶜ := by
  induction hV with
  | algebraic hA => exact .basic (.compl_algebraic hA)
  | compl_algebraic hA =>
    rw [compl_compl]; exact .basic (.algebraic hA)
  | inter _ _ ih₁ ih₂ =>
    rw [Set.compl_inter]; exact .union ih₁ ih₂

omit [IsAlgClosed C] in
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

omit [IsAlgClosed C] in
private theorem inter_fin_union
    {V W : Set (Fin k → C)}
    (hV : IsFinUnionBasicConstructible V)
    (hW : IsFinUnionBasicConstructible W) :
    IsFinUnionBasicConstructible (V ∩ W) := by
  induction hV with
  | basic hB => exact basic_inter_fin_union hB hW
  | union _ _ ih₁ ih₂ =>
    rw [Set.union_inter_distrib_right]
    exact .union ih₁ ih₂

omit [IsAlgClosed C] in
private theorem compl_fin_union {V : Set (Fin k → C)}
    (hV : IsFinUnionBasicConstructible V) :
    IsFinUnionBasicConstructible Vᶜ := by
  induction hV with
  | basic hB => exact compl_basic_fin_union hB
  | union _ _ ih₁ ih₂ =>
    rw [Set.compl_union]; exact inter_fin_union ih₁ ih₂

omit [IsAlgClosed C] in
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
### First-Order Formulas (Generic)

We define first-order formulas generically over an **atom type** `α`.
The connectives are `not`, `and`, `or`, and the quantifier `exists_`.
We derive `forall_` (= ¬∃x, ¬Φ) and `implies` (= ¬Φ ∨ Ψ).

For algebraically closed fields (Chapter 1), atoms are `FieldAtom σ D`,
encoding `P = 0` or `P ≠ 0` via a boolean flag.
For real closed fields (Chapter 2), atoms will encode sign conditions.
-/

/-- First-order formulas over atom type `α`, with variables
    indexed by type `σ`. -/
inductive Formula (σ : Type*) (α : Type*) where
  | atom    : α → Formula σ α
  | not     : Formula σ α → Formula σ α
  | and     : Formula σ α → Formula σ α → Formula σ α
  | or      : Formula σ α → Formula σ α → Formula σ α
  | exists_ : σ → Formula σ α → Formula σ α
  | forall_ : σ → Formula σ α → Formula σ α

namespace Formula

variable {σ : Type*} {α : Type*}

/-- Implication: Φ ⇒ Ψ  :=  ¬Φ ∨ Ψ. -/
def implies (Φ Ψ : Formula σ α) : Formula σ α :=
  .or (.not Φ) Ψ

/-- A formula is quantifier-free if no quantifier (∃ or ∀)
    appears in it. -/
def IsQuantifierFree : Formula σ α → Prop
  | .atom _      => True
  | .not Φ       => Φ.IsQuantifierFree
  | .and Φ₁ Φ₂   => Φ₁.IsQuantifierFree ∧ Φ₂.IsQuantifierFree
  | .or Φ₁ Φ₂    => Φ₁.IsQuantifierFree ∧ Φ₂.IsQuantifierFree
  | .exists_ _ _ => False
  | .forall_ _ _ => False

/-- Quantifier depth of a formula. -/
def quantifierDepth : Formula σ α → ℕ
  | .atom _      => 0
  | .not Φ       => Φ.quantifierDepth
  | .and Φ₁ Φ₂   => Φ₁.quantifierDepth + Φ₂.quantifierDepth
  | .or Φ₁ Φ₂    => Φ₁.quantifierDepth + Φ₂.quantifierDepth
  | .exists_ _ Φ => Φ.quantifierDepth + 1
  | .forall_ _ Φ => Φ.quantifierDepth + 1

/-- A formula in prenex normal form. -/
inductive IsPrenex : Formula σ α → Prop where
  | qf {Φ} : Φ.IsQuantifierFree → IsPrenex Φ
  | exists_ {x : σ} {Φ} :
      IsPrenex Φ → IsPrenex (.exists_ x Φ)
  | forall_ {x : σ} {Φ} :
      IsPrenex Φ → IsPrenex (.forall_ x Φ)

/-- Rename variables in a formula via `f : σ → τ`. -/
noncomputable def rename (f : σ → τ) (renameAtom : α → β) :
    Formula σ α → Formula τ β
  | .atom a      => .atom (renameAtom a)
  | .not Φ       => .not (Φ.rename f renameAtom)
  | .and Φ₁ Φ₂   => .and (Φ₁.rename f renameAtom) (Φ₂.rename f renameAtom)
  | .or Φ₁ Φ₂    => .or (Φ₁.rename f renameAtom) (Φ₂.rename f renameAtom)
  | .exists_ x Φ => .exists_ (f x) (Φ.rename f renameAtom)
  | .forall_ x Φ => .forall_ (f x) (Φ.rename f renameAtom)

/-- Eliminate `forall_` in favour of `¬∃x, ¬Φ`. -/
def eliminateForall : Formula σ α → Formula σ α
  | .atom a      => .atom a
  | .not Φ       => .not Φ.eliminateForall
  | .and Φ₁ Φ₂   => .and Φ₁.eliminateForall Φ₂.eliminateForall
  | .or Φ₁ Φ₂    => .or Φ₁.eliminateForall Φ₂.eliminateForall
  | .exists_ x Φ => .exists_ x Φ.eliminateForall
  | .forall_ x Φ => .not (.exists_ x (.not Φ.eliminateForall))

theorem rename_isQF (f : σ → τ) (ra : α → β) :
    ∀ (Φ : Formula σ α), Φ.IsQuantifierFree →
    (Φ.rename f ra).IsQuantifierFree
  | .atom _, _ => trivial
  | .not Φ, h => rename_isQF f ra Φ h
  | .and Φ₁ Φ₂, ⟨h₁, h₂⟩ =>
    ⟨rename_isQF f ra Φ₁ h₁, rename_isQF f ra Φ₂ h₂⟩
  | .or Φ₁ Φ₂, ⟨h₁, h₂⟩ =>
    ⟨rename_isQF f ra Φ₁ h₁, rename_isQF f ra Φ₂ h₂⟩

theorem rename_isPrenex (f : σ → τ) (ra : α → β)
    {Φ : Formula σ α}
    (h : IsPrenex Φ) : IsPrenex (Φ.rename f ra) := by
  induction h with
  | qf hqf => exact .qf (rename_isQF f ra _ hqf)
  | exists_ _ ih => exact .exists_ ih
  | forall_ _ ih => exact .forall_ ih

theorem rename_quantifierDepth (f : σ → τ) (ra : α → β)
    (Φ : Formula σ α) :
    (Φ.rename f ra).quantifierDepth = Φ.quantifierDepth := by
  induction Φ with
  | atom => simp [rename, quantifierDepth]
  | not _ ih => simp [rename, quantifierDepth, ih]
  | and _ _ ih₁ ih₂ =>
    simp [rename, quantifierDepth, ih₁, ih₂]
  | or _ _ ih₁ ih₂ =>
    simp [rename, quantifierDepth, ih₁, ih₂]
  | exists_ _ _ ih =>
    simp [rename, quantifierDepth, ih]
  | forall_ _ _ ih =>
    simp [rename, quantifierDepth, ih]

/-!
### Atoms for the Language of Fields

For algebraically closed fields, atoms are `P = 0` or `P ≠ 0`,
encoded as a polynomial together with a boolean flag.
-/

end Formula

/-- An atom in the language of fields: a polynomial `P` together
    with `isEq = true` for `P = 0` or `isEq = false` for `P ≠ 0`. -/
structure FieldAtom (σ : Type*) (D : Type*) [CommRing D] where
  poly : MvPolynomial σ D
  isEq : Bool

namespace FieldAtom

variable {σ : Type*} {D : Type*} [CommRing D]

/-- The atom `P = 0`. -/
def eqZero (P : MvPolynomial σ D) : FieldAtom σ D := ⟨P, true⟩

/-- The atom `P ≠ 0`. -/
def neZero (P : MvPolynomial σ D) : FieldAtom σ D := ⟨P, false⟩

/-- Free variables of a field atom. -/
noncomputable def vars [DecidableEq σ] (a : FieldAtom σ D) : Finset σ :=
  a.poly.vars

/-- Rename variables in a field atom. -/
noncomputable def renameVars (f : σ → τ) (a : FieldAtom σ D) :
    FieldAtom τ D :=
  ⟨a.poly.rename f, a.isEq⟩

end FieldAtom

namespace Formula

variable {σ : Type*} {D : Type*} [CommRing D]

/-- P = 0 as a formula. -/
noncomputable def eq_zero (P : MvPolynomial σ D) :
    Formula σ (FieldAtom σ D) :=
  .atom (FieldAtom.eqZero P)

/-- P ≠ 0 as a formula. -/
noncomputable def ne_zero (P : MvPolynomial σ D) :
    Formula σ (FieldAtom σ D) :=
  .atom (FieldAtom.neZero P)

/-- The free variables of a field formula. -/
noncomputable def freeVars [DecidableEq σ] :
    Formula σ (FieldAtom σ D) → Finset σ
  | .atom a      => a.vars
  | .not Φ       => Φ.freeVars
  | .and Φ₁ Φ₂   => Φ₁.freeVars ∪ Φ₂.freeVars
  | .or Φ₁ Φ₂    => Φ₁.freeVars ∪ Φ₂.freeVars
  | .exists_ x Φ => Φ.freeVars \ {x}
  | .forall_ x Φ => Φ.freeVars \ {x}

/-- A sentence is a formula with no free variables. -/
def isSentence [DecidableEq σ] (Φ : Formula σ (FieldAtom σ D)) :
    Prop :=
  Φ.freeVars = ∅

/-- The formula "True": 0 = 0. -/
noncomputable def trueFormula : Formula σ (FieldAtom σ D) :=
  eq_zero 0

/-- The formula "False": 0 ≠ 0. -/
noncomputable def falseFormula : Formula σ (FieldAtom σ D) :=
  ne_zero 0

/-- A basic formula is a conjunction of atoms. -/
inductive IsBasicFormula : Formula σ (FieldAtom σ D) → Prop where
  | atom (a : FieldAtom σ D) :
      IsBasicFormula (.atom a)
  | and {Φ₁ Φ₂} :
      IsBasicFormula Φ₁ → IsBasicFormula Φ₂ →
      IsBasicFormula (.and Φ₁ Φ₂)

theorem IsBasicFormula.isQuantifierFree
    {Φ : Formula σ (FieldAtom σ D)} (h : IsBasicFormula Φ) :
    Φ.IsQuantifierFree := by
  induction h with
  | atom _ => trivial
  | and _ _ ih₁ ih₂ => exact ⟨ih₁, ih₂⟩

/-!
### Realization

The **C-realization** of a formula Φ with free variables
in {Y₁, …, Yₖ}, denoted Reali(Φ, Cᵏ), is the set of
y ∈ Cᵏ such that Φ(y) is true.

Here D is a subring of C (expressed via `[Algebra D C]`),
and `aeval` handles the coercion of coefficients from D to C.
-/

variable {C : Type*} [Field C] [Algebra D C]

/-- The C-realization of a field formula: the set of assignments
    y : σ → C such that Φ(y) is true.
    BPR notation: Reali(Φ, Cᵏ). -/
noncomputable def realization [DecidableEq σ] :
    Formula σ (FieldAtom σ D) → Set (σ → C)
  | .atom a      => if a.isEq then { y | aeval y a.poly = 0 }
                     else { y | aeval y a.poly ≠ 0 }
  | .not Φ       => (Φ.realization)ᶜ
  | .and Φ₁ Φ₂   => Φ₁.realization ∩ Φ₂.realization
  | .or Φ₁ Φ₂    => Φ₁.realization ∪ Φ₂.realization
  | .exists_ x Φ =>
    { y | ∃ c : C, Function.update y x c ∈ Φ.realization }
  | .forall_ x Φ =>
    { y | ∀ c : C, Function.update y x c ∈ Φ.realization }

def CEquiv [DecidableEq σ]
    (Φ Ψ : Formula σ (FieldAtom σ D)) : Prop :=
  (realization (C := C) Φ) = (realization (C := C) Ψ)

@[simp] theorem realization_trueFormula [DecidableEq σ] :
    (trueFormula : Formula σ (FieldAtom σ D)).realization (C := C) =
      Set.univ := by
  ext y; simp [trueFormula, eq_zero, realization, FieldAtom.eqZero, map_zero]

@[simp] theorem realization_falseFormula [DecidableEq σ] :
    (falseFormula : Formula σ (FieldAtom σ D)).realization (C := C) =
      ∅ := by
  ext y; simp [falseFormula, ne_zero, realization, FieldAtom.neZero, map_zero]

@[simp] theorem realization_eq_zero [DecidableEq σ]
    (P : MvPolynomial σ D) :
    (eq_zero P : Formula σ (FieldAtom σ D)).realization (C := C) =
      { y | MvPolynomial.aeval y P = 0 } := by
  simp [eq_zero, realization, FieldAtom.eqZero]

@[simp] theorem realization_ne_zero [DecidableEq σ]
    (P : MvPolynomial σ D) :
    (ne_zero P : Formula σ (FieldAtom σ D)).realization (C := C) =
      { y | MvPolynomial.aeval y P ≠ 0 } := by
  simp [ne_zero, realization, FieldAtom.neZero]
/-!
### Prenex Normal Form Infrastructure

Variable renaming, realization invariance, and the prenex
normal form theorem.
-/


theorem rename_realization [DecidableEq σ] [DecidableEq τ]
    (f : σ → τ) (hf : Function.Injective f)
    (Φ : Formula σ (FieldAtom σ D)) :
    (Φ.rename f (FieldAtom.renameVars f)).realization (C := C) =
      (· ∘ f) ⁻¹' Φ.realization := by
  induction Φ with
  | atom a =>
    ext y; cases a with | mk P b =>
    cases b <;> simp [rename, FieldAtom.renameVars,
      realization, aeval_rename]
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
  | forall_ x _ ih =>
    ext y
    simp only [rename, realization, Set.mem_setOf_eq,
      Set.mem_preimage, ih]
    constructor <;> intro hc <;> intro c <;>
    · have := hc c; convert this using 1; ext i
      simp [Function.update, hf.eq_iff]

private theorem aeval_update_of_not_mem_vars
    [DecidableEq σ] (P : MvPolynomial σ D)
    (y : σ → C) (x : σ) (c : C) (hx : x ∉ P.vars) :
    aeval (Function.update y x c) P = aeval y P := by
  simp only [MvPolynomial.aeval_def]
  apply MvPolynomial.eval₂_congr
  intro i ci hi hci
  have : i ≠ x := by
    intro h; apply hx; subst h
    rw [MvPolynomial.mem_vars]
    exact ⟨ci, P.mem_support_iff.mpr hci, hi⟩
  simp [this]

theorem realization_invariant_update [DecidableEq σ]
    (Φ : Formula σ (FieldAtom σ D)) (x : σ) (hx : x ∉ Φ.freeVars)
    (y : σ → C) (c : C) :
    y ∈ Φ.realization (C := C) ↔
    Function.update y x c ∈ Φ.realization := by
  induction Φ generalizing y with
  | atom a =>
    simp only [realization, freeVars, FieldAtom.vars] at *
    split <;> simp only [Set.mem_setOf_eq] <;>
    rw [aeval_update_of_not_mem_vars a.poly y x c hx]
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
    · by_cases hxz : x = z
      · subst hxz; rwa [Function.update_idem]
      · rw [Function.update_comm hxz]
        rwa [← ih (fun hmem => absurd (hx hmem) hxz)]
    · by_cases hxz : x = z
      · subst hxz; rwa [Function.update_idem] at hd
      · rw [Function.update_comm hxz] at hd
        rwa [ih (fun hmem => absurd (hx hmem) hxz)]
  | forall_ z _ ih =>
    simp only [realization, Set.mem_setOf_eq, freeVars,
      Finset.mem_sdiff, Finset.mem_singleton] at *
    push_neg at hx
    constructor
    · intro hd d
      by_cases hxz : x = z
      · subst hxz; rw [Function.update_idem]; exact hd d
      · rw [Function.update_comm hxz]
        exact (ih (fun hmem => absurd (hx hmem) hxz) _).mp (hd d)
    · intro hd d
      by_cases hxz : x = z
      · subst hxz
        have := hd d; rw [Function.update_idem] at this; exact this
      · have := hd d; rw [Function.update_comm hxz] at this
        exact (ih (fun hmem => absurd (hx hmem) hxz) _).mpr this

/-- (∃x, A) ∧ B ≡ ∃x, (A ∧ B) when x ∉ freeVars B. -/
theorem exists_and_equiv [DecidableEq σ]
    (A B : Formula σ (FieldAtom σ D)) (x : σ) (hx : x ∉ B.freeVars) :
    (Formula.exists_ x A).realization (C := C) ∩ B.realization =
    (Formula.exists_ x (Formula.and A B)).realization := by
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
    (A B : Formula σ (FieldAtom σ D)) (x : σ) (hx : x ∉ B.freeVars) :
    (Formula.forall_ x A).realization (C := C) ∩
      B.realization =
    (Formula.forall_ x (Formula.and A B)).realization := by
  ext y
  simp only [realization, Set.mem_inter_iff, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hA, hB⟩ c
    exact ⟨hA c,
      (realization_invariant_update B x hx y c).mp hB⟩
  · intro h
    exact ⟨fun c => (h c).1,
      by have := (h (y x)).2
         rw [Function.update_eq_self] at this; exact this⟩

/-- Negation of a prenex formula is C-equivalent to a prenex formula. -/
private theorem not_prenex [DecidableEq σ]
    {Ψ : Formula σ (FieldAtom σ D)} (hΨ : IsPrenex Ψ) :
    ∃ Ψ' : Formula σ (FieldAtom σ D), IsPrenex Ψ' ∧
      CEquiv (C := C) (.not Ψ) Ψ' := by
  induction hΨ with
  | qf hqf => exact ⟨.not _, .qf hqf, rfl⟩
  | @exists_ x Φ _ ih =>
    obtain ⟨Φ', hP, hE⟩ := ih
    refine ⟨.forall_ x Φ', .forall_ hP, ?_⟩
    unfold CEquiv at hE ⊢
    have hΦ' : Φ'.realization (C := C) = (Φ.realization (C := C))ᶜ := by
      rw [show (Φ.realization (C := C))ᶜ = (Formula.not Φ).realization (C := C) from rfl]
      exact hE.symm
    simp only [realization]
    ext y; simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_exists]
    exact forall_congr' fun c => by rw [hΦ']; simp
  | @forall_ x Φ _ ih =>
    obtain ⟨Φ', hP, hE⟩ := ih
    refine ⟨.exists_ x Φ', .exists_ hP, ?_⟩
    unfold CEquiv at hE ⊢
    have hΦ' : Φ'.realization (C := C) = (Φ.realization (C := C))ᶜ := by
      rw [show (Φ.realization (C := C))ᶜ = (Formula.not Φ).realization (C := C) from rfl]
      exact hE.symm
    simp only [realization]
    ext y; simp only [Set.mem_setOf_eq, Set.mem_compl_iff, not_forall]
    exact exists_congr fun c => by rw [hΦ']; simp

/-- Renaming the bound variable of ∃x, Φ via a swap preserves realization. -/
private theorem exists_swap_equiv [DecidableEq σ]
    (Φ : Formula σ (FieldAtom σ D)) (x z : σ) (hz : z ∉ Φ.freeVars) :
    CEquiv (C := C) (.exists_ x Φ) (.exists_ z (Φ.rename (Equiv.swap x z) (FieldAtom.renameVars (Equiv.swap x z)))) := by
  unfold CEquiv; simp only [realization]
  ext y; simp only [Set.mem_setOf_eq]
  by_cases hxz : x = z
  · subst hxz
    simp only [Equiv.swap_self]
    exact exists_congr fun c => by
      simp only [Equiv.coe_refl]
      rw [rename_realization id Function.injective_id]; simp
  · have hzx : z ≠ x := Ne.symm hxz
    have key : ∀ c, Function.update y z c ∘ ⇑(Equiv.swap x z) =
        Function.update (Function.update y z (y x)) x c := by
      intro c; ext i; simp only [Function.comp, Function.update_apply]
      split_ifs with h1 h2 h2 <;> simp_all [Equiv.swap_apply_left,
        Equiv.swap_apply_right, Equiv.swap_apply_of_ne_of_ne]
    constructor
    · rintro ⟨c, hc⟩
      refine ⟨c, ?_⟩
      rw [rename_realization (Equiv.swap x z) (Equiv.injective _)]
      simp only [Set.mem_preimage]; rw [key]
      rw [Function.update_comm hzx]
      exact (realization_invariant_update Φ z hz (Function.update y x c) (y x)).mp hc
    · rintro ⟨c, hc⟩
      rw [rename_realization (Equiv.swap x z) (Equiv.injective _)] at hc
      simp only [Set.mem_preimage] at hc; rw [key] at hc
      refine ⟨c, ?_⟩
      rw [Function.update_comm hzx] at hc
      exact (realization_invariant_update Φ z hz (Function.update y x c) (y x)).mpr hc

/-- Renaming the bound variable of ∀x, Φ via a swap preserves realization. -/
private theorem forall_swap_equiv [DecidableEq σ]
    (Φ : Formula σ (FieldAtom σ D)) (x z : σ) (hz : z ∉ Φ.freeVars) :
    CEquiv (C := C) (.forall_ x Φ) (.forall_ z (Φ.rename (Equiv.swap x z) (FieldAtom.renameVars (Equiv.swap x z)))) := by
  unfold CEquiv; simp only [realization]
  ext y; simp only [Set.mem_setOf_eq]
  by_cases hxz : x = z
  · subst hxz
    simp only [Equiv.swap_self]
    exact forall_congr' fun c => by
      simp only [Equiv.coe_refl]
      rw [rename_realization id Function.injective_id]; simp
  · have hzx : z ≠ x := Ne.symm hxz
    have key : ∀ c, Function.update y z c ∘ ⇑(Equiv.swap x z) =
        Function.update (Function.update y z (y x)) x c := by
      intro c; ext i; simp only [Function.comp, Function.update_apply]
      split_ifs with h1 h2 h2 <;> simp_all [Equiv.swap_apply_left,
        Equiv.swap_apply_right, Equiv.swap_apply_of_ne_of_ne]
    constructor
    · intro hc c
      rw [rename_realization (Equiv.swap x z) (Equiv.injective _)]
      simp only [Set.mem_preimage]; rw [key]
      rw [Function.update_comm hzx]
      exact (realization_invariant_update Φ z hz (Function.update y x c) (y x)).mp (hc c)
    · intro hc c
      have hc' := hc c
      rw [rename_realization (Equiv.swap x z) (Equiv.injective _)] at hc'
      simp only [Set.mem_preimage] at hc'; rw [key] at hc'
      rw [Function.update_comm hzx] at hc'
      exact (realization_invariant_update Φ z hz (Function.update y x c) (y x)).mpr hc'

/-- Conjunction of two prenex formulas is C-equivalent to a prenex formula. -/
private theorem and_prenex [Infinite σ] [DecidableEq σ]
    {Ψ₁ Ψ₂ : Formula σ (FieldAtom σ D)} (h₁ : IsPrenex Ψ₁) (h₂ : IsPrenex Ψ₂) :
    ∃ Ψ : Formula σ (FieldAtom σ D), IsPrenex Ψ ∧
      CEquiv (C := C) (.and Ψ₁ Ψ₂) Ψ := by
  have key : ∀ n, (∀ m, m < n → ∀ {Ψ₁ Ψ₂ : Formula σ (FieldAtom σ D)},
      IsPrenex Ψ₁ → IsPrenex Ψ₂ →
      Ψ₁.quantifierDepth + Ψ₂.quantifierDepth = m →
      ∃ Ψ : Formula σ (FieldAtom σ D), IsPrenex Ψ ∧ CEquiv (C := C) (.and Ψ₁ Ψ₂) Ψ) →
    ∀ {Ψ₁ Ψ₂ : Formula σ (FieldAtom σ D)},
      IsPrenex Ψ₁ → IsPrenex Ψ₂ →
      Ψ₁.quantifierDepth + Ψ₂.quantifierDepth = n →
      ∃ Ψ : Formula σ (FieldAtom σ D), IsPrenex Ψ ∧ CEquiv (C := C) (.and Ψ₁ Ψ₂) Ψ := by
    intro n ih Ψ₁ Ψ₂ h₁ h₂ hn
    cases h₁ with
    | qf hqf₁ =>
      cases h₂ with
      | qf hqf₂ => exact ⟨.and _ _, .qf ⟨hqf₁, hqf₂⟩, rfl⟩
      | exists_ hPB =>
        rename_i z B
        obtain ⟨w, hw⟩ := Infinite.exists_notMem_finset (B.freeVars ∪ Ψ₁.freeVars)
        have hwB : w ∉ B.freeVars := fun h => hw (Finset.mem_union_left _ h)
        have hwΨ₁ : w ∉ Ψ₁.freeVars := fun h => hw (Finset.mem_union_right _ h)
        have hswap := exists_swap_equiv (C := C) B z w hwB
        let B' := B.rename (Equiv.swap z w) (FieldAtom.renameVars (Equiv.swap z w))
        have hB'_prenex : IsPrenex B' := rename_isPrenex _ _ hPB
        have hdepth : Ψ₁.quantifierDepth + B'.quantifierDepth < n := by
          show Ψ₁.quantifierDepth + (B.rename (Equiv.swap z w) (FieldAtom.renameVars (Equiv.swap z w))).quantifierDepth < n
          rw [rename_quantifierDepth _ (FieldAtom.renameVars _)]; simp [quantifierDepth] at hn; omega
        obtain ⟨Ψ_inner, hΨP, hΨE⟩ := ih _ hdepth (.qf hqf₁) hB'_prenex rfl
        refine ⟨.exists_ w Ψ_inner, .exists_ hΨP, ?_⟩
        unfold CEquiv at hswap hΨE ⊢
        simp only [realization] at hswap hΨE ⊢
        rw [hswap]
        ext y; simp only [Set.mem_setOf_eq, Set.mem_inter_iff]
        constructor
        · rintro ⟨hΨ₁, ⟨c, hc⟩⟩
          exact ⟨c, hΨE ▸ ⟨(realization_invariant_update Ψ₁ w hwΨ₁ y c).mp hΨ₁, hc⟩⟩
        · rintro ⟨c, hc⟩
          rw [← hΨE] at hc; simp only [Set.mem_inter_iff] at hc
          exact ⟨(realization_invariant_update Ψ₁ w hwΨ₁ y c).mpr hc.1, c, hc.2⟩
      | forall_ hPB =>
        rename_i z B
        obtain ⟨w, hw⟩ := Infinite.exists_notMem_finset (B.freeVars ∪ Ψ₁.freeVars)
        have hwB : w ∉ B.freeVars := fun h => hw (Finset.mem_union_left _ h)
        have hwΨ₁ : w ∉ Ψ₁.freeVars := fun h => hw (Finset.mem_union_right _ h)
        let B' := B.rename (Equiv.swap z w) (FieldAtom.renameVars (Equiv.swap z w))
        have hB'_prenex : IsPrenex B' := rename_isPrenex _ _ hPB
        have hdepth : Ψ₁.quantifierDepth + B'.quantifierDepth < n := by
          show Ψ₁.quantifierDepth + (B.rename (Equiv.swap z w) (FieldAtom.renameVars (Equiv.swap z w))).quantifierDepth < n
          rw [rename_quantifierDepth _ (FieldAtom.renameVars _)]; simp [quantifierDepth] at hn; omega
        obtain ⟨Ψ_inner, hΨP, hΨE⟩ := ih _ hdepth (.qf hqf₁) hB'_prenex rfl
        refine ⟨.forall_ w Ψ_inner, .forall_ hΨP, ?_⟩
        have hswap := forall_swap_equiv (C := C) B z w hwB
        unfold CEquiv at hswap hΨE ⊢
        simp only [realization] at hswap hΨE ⊢
        rw [hswap]
        ext y; simp only [Set.mem_setOf_eq, Set.mem_inter_iff]
        constructor
        · rintro ⟨hΨ₁, hB⟩ c
          rw [← hΨE]; simp only [Set.mem_inter_iff]
          exact ⟨(realization_invariant_update Ψ₁ w hwΨ₁ y c).mp hΨ₁, hB c⟩
        · intro h
          refine ⟨?_, fun c => ?_⟩
          · have := h (y w)
            rw [← hΨE] at this; simp only [Set.mem_inter_iff] at this
            exact (realization_invariant_update Ψ₁ w hwΨ₁ y (y w)).mpr this.1
          · have := h c
            rw [← hΨE] at this; simp only [Set.mem_inter_iff] at this
            exact this.2
    | exists_ hPA =>
      rename_i x A
      obtain ⟨z, hz⟩ := Infinite.exists_notMem_finset (A.freeVars ∪ Ψ₂.freeVars)
      have hzA : z ∉ A.freeVars := fun h => hz (Finset.mem_union_left _ h)
      have hzΨ : z ∉ Ψ₂.freeVars := fun h => hz (Finset.mem_union_right _ h)
      have hswap := exists_swap_equiv (C := C) A x z hzA
      let A' := A.rename (Equiv.swap x z) (FieldAtom.renameVars (Equiv.swap x z))
      have hA'_prenex : IsPrenex A' := rename_isPrenex _ _ hPA
      have hdepth : A'.quantifierDepth + Ψ₂.quantifierDepth < n := by
        show (A.rename (Equiv.swap x z) (FieldAtom.renameVars (Equiv.swap x z))).quantifierDepth + Ψ₂.quantifierDepth < n
        rw [rename_quantifierDepth _ (FieldAtom.renameVars _)]; simp [quantifierDepth] at hn; omega
      obtain ⟨Ψ_inner, hΨP, hΨE⟩ := ih _ hdepth hA'_prenex h₂ rfl
      refine ⟨.exists_ z Ψ_inner, .exists_ hΨP, ?_⟩
      unfold CEquiv at hswap hΨE ⊢
      simp only [realization] at hswap hΨE ⊢
      rw [hswap]
      ext y; simp only [Set.mem_setOf_eq, Set.mem_inter_iff]
      constructor
      · rintro ⟨⟨c, hc⟩, hΨ₂⟩
        exact ⟨c, hΨE ▸ ⟨hc, (realization_invariant_update Ψ₂ z hzΨ y c).mp hΨ₂⟩⟩
      · rintro ⟨c, hc⟩
        rw [← hΨE] at hc; simp only [Set.mem_inter_iff] at hc
        exact ⟨⟨c, hc.1⟩, (realization_invariant_update Ψ₂ z hzΨ y c).mpr hc.2⟩
    | forall_ hPA =>
      rename_i x A
      obtain ⟨z, hz⟩ := Infinite.exists_notMem_finset (A.freeVars ∪ Ψ₂.freeVars)
      have hzA : z ∉ A.freeVars := fun h => hz (Finset.mem_union_left _ h)
      have hzΨ : z ∉ Ψ₂.freeVars := fun h => hz (Finset.mem_union_right _ h)
      have hswap := forall_swap_equiv (C := C) A x z hzA
      let A' := A.rename (Equiv.swap x z) (FieldAtom.renameVars (Equiv.swap x z))
      have hA'_prenex : IsPrenex A' := rename_isPrenex _ _ hPA
      have hdepth : A'.quantifierDepth + Ψ₂.quantifierDepth < n := by
        show (A.rename (Equiv.swap x z) (FieldAtom.renameVars (Equiv.swap x z))).quantifierDepth + Ψ₂.quantifierDepth < n
        rw [rename_quantifierDepth _ (FieldAtom.renameVars _)]; simp [quantifierDepth] at hn; omega
      obtain ⟨Ψ_inner, hΨP, hΨE⟩ := ih _ hdepth hA'_prenex h₂ rfl
      refine ⟨.forall_ z Ψ_inner, .forall_ hΨP, ?_⟩
      unfold CEquiv at hswap hΨE ⊢
      simp only [realization] at hswap hΨE ⊢
      rw [hswap]
      ext y; simp only [Set.mem_setOf_eq, Set.mem_inter_iff]
      constructor
      · rintro ⟨hA, hΨ₂⟩ c
        rw [← hΨE]; simp only [Set.mem_inter_iff]
        exact ⟨hA c, (realization_invariant_update Ψ₂ z hzΨ y c).mp hΨ₂⟩
      · intro h
        refine ⟨fun c => ?_, ?_⟩
        · have := h c
          rw [← hΨE] at this; simp only [Set.mem_inter_iff] at this
          exact this.1
        · have := h (y z); rw [← hΨE] at this; simp only [Set.mem_inter_iff] at this
          exact (realization_invariant_update Ψ₂ z hzΨ y (y z)).mpr this.2
  exact (@Nat.strongRecOn (fun n => ∀ {Ψ₁ Ψ₂ : Formula σ (FieldAtom σ D)},
      IsPrenex Ψ₁ → IsPrenex Ψ₂ →
      Ψ₁.quantifierDepth + Ψ₂.quantifierDepth = n →
      ∃ Ψ : Formula σ (FieldAtom σ D), IsPrenex Ψ ∧ CEquiv (C := C) (.and Ψ₁ Ψ₂) Ψ)
    (Ψ₁.quantifierDepth + Ψ₂.quantifierDepth) key) h₁ h₂ rfl


/-- Every formula over an infinite variable type is
    C-equivalent to a prenex formula. -/
theorem prenex_normal_form [Infinite σ] [DecidableEq σ]
    (Φ : Formula σ (FieldAtom σ D)) :
    ∃ Ψ : Formula σ (FieldAtom σ D), IsPrenex Ψ ∧
      CEquiv (C := C) Φ Ψ := by
  induction Φ with
  | atom a => exact ⟨.atom a, .qf True.intro, rfl⟩
  | not Φ ih =>
    obtain ⟨Ψ, hP, hE⟩ := ih
    obtain ⟨Ψ', hP', hE'⟩ := not_prenex (C := C) hP
    exact ⟨Ψ', hP', by
      unfold CEquiv at hE hE' ⊢
      simp only [realization] at hE' ⊢; rw [hE]; exact hE'⟩
  | and Φ₁ Φ₂ ih₁ ih₂ =>
    obtain ⟨Ψ₁, hP₁, hE₁⟩ := ih₁
    obtain ⟨Ψ₂, hP₂, hE₂⟩ := ih₂
    obtain ⟨Ψ, hP, hE⟩ := and_prenex (C := C) hP₁ hP₂
    exact ⟨Ψ, hP, by
      unfold CEquiv at hE₁ hE₂ hE ⊢
      simp only [realization] at hE ⊢; rw [hE₁, hE₂]; exact hE⟩
  | or Φ₁ Φ₂ ih₁ ih₂ =>
    -- A ∨ B = ¬(¬A ∧ ¬B)
    obtain ⟨Ψ₁, hP₁, hE₁⟩ := ih₁
    obtain ⟨Ψ₂, hP₂, hE₂⟩ := ih₂
    obtain ⟨Ψ₁', hP₁', hE₁'⟩ := not_prenex (C := C) hP₁
    obtain ⟨Ψ₂', hP₂', hE₂'⟩ := not_prenex (C := C) hP₂
    obtain ⟨Ψ_and, hP_and, hE_and⟩ := and_prenex (C := C) hP₁' hP₂'
    obtain ⟨Ψ_final, hP_final, hE_final⟩ := not_prenex (C := C) hP_and
    refine ⟨Ψ_final, hP_final, ?_⟩
    unfold CEquiv at hE₁ hE₂ hE₁' hE₂' hE_and hE_final ⊢
    simp only [realization] at hE₁' hE₂' hE_and hE_final ⊢
    rw [hE₁, hE₂]
    -- Goal: Ψ₁.realization ∪ Ψ₂.realization = Ψ_final.realization
    -- Use De Morgan: A ∪ B = (Aᶜ ∩ Bᶜ)ᶜ
    rw [show Ψ₁.realization (C := C) ∪ Ψ₂.realization (C := C) =
        ((Ψ₁.realization (C := C))ᶜ ∩ (Ψ₂.realization (C := C))ᶜ)ᶜ from by
          simp [Set.compl_inter, compl_compl]]
    rw [hE₁', hE₂', hE_and, hE_final]
  | exists_ x Φ ih =>
    obtain ⟨Ψ, hP, hE⟩ := ih
    refine ⟨.exists_ x Ψ, .exists_ hP, ?_⟩
    unfold CEquiv at hE ⊢; simp only [realization]
    ext y; simp only [Set.mem_setOf_eq]
    exact exists_congr fun c => by rw [← hE]
  | forall_ x Φ ih =>
    obtain ⟨Ψ, hP, hE⟩ := ih
    refine ⟨.forall_ x Ψ, .forall_ hP, ?_⟩
    unfold CEquiv at hE ⊢; simp only [realization]
    ext y; simp only [Set.mem_setOf_eq]
    exact forall_congr' fun c => by rw [← hE]

/-!
### Sentences

Realization depends only on free variables.
A sentence (no free variables) is C-equivalent to True or False.
-/

theorem realization_eq_of_agree_on_freeVars
    [DecidableEq σ]
    (Φ : Formula σ (FieldAtom σ D)) (y₁ y₂ : σ → C)
    (h : ∀ x ∈ Φ.freeVars, y₁ x = y₂ x) :
    y₁ ∈ Φ.realization (C := C) ↔
    y₂ ∈ Φ.realization := by
  induction Φ generalizing y₁ y₂ with
  | atom a =>
    simp only [realization, freeVars, FieldAtom.vars] at *
    have : (MvPolynomial.aeval y₁) a.poly = (MvPolynomial.aeval y₂) a.poly := by
      simp only [MvPolynomial.aeval_def]
      apply MvPolynomial.eval₂_congr
      · intro i c hi hc
        apply h
        rw [MvPolynomial.mem_vars]
        exact ⟨c, MvPolynomial.mem_support_iff.mpr hc, hi⟩
    split <;> simp only [Set.mem_setOf_eq] <;> rw [this]
  | not _ ih =>
    simp only [realization, Set.mem_compl_iff]
    rw [ih _ _ h]
  | and _ _ ih₁ ih₂ =>
    simp only [realization, Set.mem_inter_iff, freeVars] at *
    rw [ih₁ _ _ (fun x hx => h x (Finset.mem_union_left _ hx)),
        ih₂ _ _ (fun x hx => h x (Finset.mem_union_right _ hx))]
  | or _ _ ih₁ ih₂ =>
    simp only [realization, Set.mem_union, freeVars] at *
    rw [ih₁ _ _ (fun x hx => h x (Finset.mem_union_left _ hx)),
        ih₂ _ _ (fun x hx => h x (Finset.mem_union_right _ hx))]
  | exists_ z _ ih =>
    simp only [realization, Set.mem_setOf_eq]
    constructor <;> rintro ⟨c, hc⟩
    · exact ⟨c, (ih _ _ (fun x hx => by
        simp only [Function.update]; split
        · rfl
        · rename_i hne
          exact h x (by simp only [freeVars, Finset.mem_sdiff, Finset.mem_singleton]; exact ⟨hx, hne⟩))).mp hc⟩
    · exact ⟨c, (ih _ _ (fun x hx => by
        simp only [Function.update]; split
        · rfl
        · rename_i hne
          exact h x (by simp only [freeVars, Finset.mem_sdiff, Finset.mem_singleton]; exact ⟨hx, hne⟩))).mpr hc⟩
  | forall_ z _ ih =>
    simp only [realization, Set.mem_setOf_eq]
    constructor <;> intro hc <;> intro c
    · exact (ih _ _ (fun x hx => by
        simp only [Function.update]; split
        · rfl
        · rename_i hne
          exact h x (by simp only [freeVars, Finset.mem_sdiff, Finset.mem_singleton]; exact ⟨hx, hne⟩))).mp (hc c)
    · exact (ih _ _ (fun x hx => by
        simp only [Function.update]; split
        · rfl
        · rename_i hne
          exact h x (by simp only [freeVars, Finset.mem_sdiff, Finset.mem_singleton]; exact ⟨hx, hne⟩))).mpr (hc c)

theorem sentence_trivial_realization [DecidableEq σ]
    (Φ : Formula σ (FieldAtom σ D)) (hΦ : isSentence Φ) :
    Φ.realization (C := C) = ∅ ∨
    Φ.realization (C := C) = Set.univ := by
  by_cases h : ∃ y, y ∈ Φ.realization (C := C)
  · right; ext y'
    obtain ⟨y, hy⟩ := h
    simp only [Set.mem_univ, iff_true]
    exact (realization_eq_of_agree_on_freeVars Φ y y'
      (by simp [isSentence] at hΦ; simp [hΦ])).mp hy
  · left; push_neg at h
    exact Set.subset_eq_empty h rfl

theorem sentence_equiv_true_or_false [DecidableEq σ]
    (Φ : Formula σ (FieldAtom σ D)) (hΦ : isSentence Φ) :
    CEquiv (C := C) Φ trueFormula ∨
    CEquiv (C := C) Φ falseFormula := by
  rcases sentence_trivial_realization (C := C) Φ hΦ with h | h
  · right; show Φ.realization = _
    rw [h, realization_falseFormula]
  · left; show Φ.realization = _
    rw [h, realization_trueFormula]

/-!
### Exercise 1.4: Field Axioms

The field axioms as formulas. The ring axioms
(commutativity, associativity, distributivity, identities)
are tautological polynomial identities. The remaining
non-trivial axioms are:
-/

/-- ∀X₀ ∃X₁, X₀ + X₁ = 0 (additive inverse). -/
noncomputable def additiveInverse : Formula (Fin 2) (FieldAtom (Fin 2) ℤ) :=
  forall_ 0 (.exists_ 1 (eq_zero (X 0 + X 1)))

/-- ∀X₀, X₀ = 0 ∨ ∃X₁, X₀X₁ − 1 = 0
    (multiplicative inverse for nonzero elements). -/
noncomputable def multiplicativeInverse : Formula (Fin 2) (FieldAtom (Fin 2) ℤ) :=
  forall_ 0 (.or (eq_zero (X 0))
    (.exists_ 1 (eq_zero (X 0 * X 1 - 1))))

/-- 1 ≠ 0 (nontriviality). -/
noncomputable def fieldNontriviality : Formula (Fin 2) (FieldAtom (Fin 2) ℤ) :=
  ne_zero 1

theorem additiveInverse_holds :
    additiveInverse.realization (C := C) =
      Set.univ := by
  ext y; simp [additiveInverse, realization]
  intro c
  exact ⟨-c, by simp⟩

theorem multiplicativeInverse_holds :
    multiplicativeInverse.realization (C := C) =
      Set.univ := by
  ext y; simp [multiplicativeInverse, realization]
  intro c; by_cases hc : c = 0
  · subst hc; simp
  · right; exact ⟨c⁻¹, by field_simp [hc]; ring⟩

theorem fieldNontriviality_holds :
    fieldNontriviality.realization (C := C) =
      Set.univ := by
  ext y; simp [fieldNontriviality, ne_zero, realization, FieldAtom.neZero]

/-!
### Algebraic Closure Axiom Φ_d

Φ_d asserts that every monic polynomial of degree d has a
root: ∀Y₁...∀Y_d ∃X, X^d + Y₁X^(d-1) + ... + Y_d = 0.
-/

/-- The generic monic polynomial of degree d:
    X₀^d + X₁ · X₀^(d-1) + X₂ · X₀^(d-2) + ... + X_d.
    Variable 0 is the root variable, variables 1..d are
    coefficients. -/
noncomputable def monicPoly (d : ℕ) :
    MvPolynomial (Fin (d + 1)) ℤ :=
  X 0 ^ d + ∑ i : Fin d,
    X ⟨i + 1, by omega⟩ * X 0 ^ (d - 1 - i)

/-- Φ_d: ∀Y₁ ∀Y₂ ... ∀Y_d ∃X, monicPoly d = 0.
    Example: Φ₂ = ∀Y₁ ∀Y₂ ∃X, X² + Y₁X + Y₂ = 0. -/
noncomputable def phiD (d : ℕ) : Formula (Fin (d + 1)) (FieldAtom (Fin (d + 1)) ℤ) :=
  (List.finRange d).foldr
    (fun i acc => forall_ ⟨i.val + 1, by omega⟩ acc)
    (.exists_ 0 (eq_zero (monicPoly d)))

private theorem realization_forall_of_univ [DecidableEq σ]
    (x : σ) (Φ : Formula σ (FieldAtom σ D))
    (h : Φ.realization (C := C) = Set.univ) :
    (forall_ x Φ).realization (C := C) = Set.univ := by
  ext y; simp [realization, h]

private theorem realization_foldr_forall_of_univ
    [DecidableEq σ] (xs : List σ) (body : Formula σ (FieldAtom σ D))
    (h : body.realization (C := C) = Set.univ) :
    (xs.foldr (fun x acc => forall_ x acc)
      body).realization (C := C) = Set.univ := by
  induction xs with
  | nil => exact h
  | cons x xs ih =>
    simp [List.foldr]
    exact realization_forall_of_univ x _ ih

private theorem realization_finRange_forall_of_univ {n : ℕ}
    (d : ℕ) (g : Fin d → Fin (n + 1)) (body : Formula (Fin (n + 1)) (FieldAtom (Fin (n + 1)) ℤ))
    (h : body.realization (C := C) = Set.univ) :
    ((List.finRange d).foldr (fun i acc => forall_ (g i) acc)
      body).realization (C := C) = Set.univ := by
  induction (List.finRange d) with
  | nil => exact h
  | cons x xs ih =>
    simp only [List.foldr]
    exact realization_forall_of_univ (g x) _ ih

/-- Φ_d holds in any algebraically closed field. -/
theorem phiD_holds [IsAlgClosed C] (d : ℕ) (hd : 0 < d) :
    (phiD d).realization (C := C) = Set.univ := by
  unfold phiD
  apply realization_finRange_forall_of_univ
  ext y
  simp only [realization, Set.mem_setOf_eq, Set.mem_univ, iff_true]
  let q := ∑ i : Fin d,
    Polynomial.C (y ⟨↑i + 1, by omega⟩) * Polynomial.X ^ (d - 1 - (i : ℕ))
  let p : C[X] := Polynomial.X ^ d + q
  -- natDegree q ≤ d - 1
  have hnd : q.natDegree ≤ d - 1 := by
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro i _
    exact le_trans (Polynomial.natDegree_C_mul_X_pow_le _ _) (by omega)
  -- degree q < d
  have hq : q.degree < (d : WithBot ℕ) := by
    by_cases hq0 : q = 0
    · simp [hq0]
    · rw [← Polynomial.natDegree_lt_iff_degree_lt hq0]; omega
  -- p is monic
  have hp : p.Monic := Polynomial.monic_X_pow_add hq
  -- p.natDegree = d
  have hpnd : p.natDegree = d := by
    show (Polynomial.X ^ d + q).natDegree = d
    rw [Polynomial.natDegree_add_eq_left_of_natDegree_lt]
    · simp
    · by_cases hq0 : q = 0
      · simp [hq0, hd]
      · simp; exact lt_of_le_of_lt hnd (by omega)
  -- degree p ≠ 0
  have hdeg : p.degree ≠ 0 := by
    rw [Polynomial.degree_eq_natDegree hp.ne_zero, hpnd]
    exact_mod_cast hd.ne'
  obtain ⟨c, hc⟩ := IsAlgClosed.exists_root p hdeg
  rw [Polynomial.IsRoot] at hc
  refine ⟨c, ?_⟩
  simp only [monicPoly]
  convert hc using 1
  simp [p, q, Polynomial.eval_add, Polynomial.eval_pow,
    Polynomial.eval_X, Polynomial.eval_finset_sum,
    Polynomial.eval_mul, Polynomial.eval_C]

private lemma forall_realization_univ_iff
    {D : Type*} [CommRing D] [Algebra D C]
    {σ : Type*} [DecidableEq σ]
    (x : σ) (Φ : Formula σ (FieldAtom σ D)) :
    (forall_ x Φ).realization (C := C) = Set.univ ↔
    Φ.realization (C := C) = Set.univ := by
  constructor
  · intro h; ext z; simp only [Set.mem_univ, iff_true]
    have hz := (Set.eq_univ_iff_forall.mp h) z
    simp only [realization, Set.mem_setOf_eq] at hz
    convert hz (z x); exact (Function.update_eq_self x z).symm
  · intro h; ext y; simp only [Set.mem_univ, iff_true]
    simp only [realization, Set.mem_setOf_eq]
    intro c; exact Set.eq_univ_iff_forall.mp h _

private lemma phiD_univ_iff (d : ℕ) :
    (phiD d).realization (C := C) = Set.univ ↔
    (Formula.exists_ (0 : Fin (d + 1))
      (Formula.eq_zero (monicPoly d))).realization (C := C) = Set.univ := by
  unfold phiD
  suffices h : ∀ (xs : List (Fin d)) (body : Formula (Fin (d + 1)) (FieldAtom (Fin (d + 1)) ℤ)),
    (xs.foldr (fun i acc => forall_ ⟨i.val + 1, by omega⟩ acc)
      body).realization (C := C) = Set.univ ↔
    body.realization (C := C) = Set.univ from h _ _
  intro xs body; induction xs with
  | nil => exact Iff.rfl
  | cons x xs ih =>
    simp only [List.foldr_cons]
    exact (forall_realization_univ_iff _ _).trans ih

/-- Converse of `phiD_holds`: if Φ_d holds for all d ≥ 1,
    then C is algebraically closed. -/
theorem isAlgClosed_of_phiD_holds
    (h : ∀ d, 0 < d → (phiD d).realization (C := C) = Set.univ) :
    IsAlgClosed C := by
  apply IsAlgClosed.of_exists_root
  intro p hp hirr
  have hd : 0 < p.natDegree := by
    by_contra hle; push_neg at hle
    exact not_irreducible_one
      ((Polynomial.eq_one_of_monic_natDegree_zero hp (by omega)) ▸ hirr)
  set d := p.natDegree with d_def
  have hphi := (phiD_univ_iff d).mp (h d hd)
  have hR := Set.eq_univ_iff_forall.mp hphi
  set y : Fin (d + 1) → C := fun j => p.coeff (d - j.val)
  have hy := hR y
  simp only [realization, Set.mem_setOf_eq] at hy
  obtain ⟨c, hc⟩ := hy
  refine ⟨c, ?_⟩
  simp only [monicPoly] at hc
  have h_upd : ∀ i : Fin d,
    Function.update y (0 : Fin (d + 1)) c ⟨↑i + 1, by omega⟩ =
    p.coeff (d - 1 - (i : ℕ)) := by
    intro i
    rw [Function.update_of_ne (show (⟨↑i + 1, by omega⟩ : Fin (d + 1)) ≠ 0
      from by simp [Fin.ext_iff])]
    simp only [y]; congr 1; omega
  simp only [realization_eq_zero, Set.mem_setOf_eq] at hc
  simp only [map_add, map_pow, MvPolynomial.aeval_X,
    map_sum, map_mul, Function.update_self] at hc
  simp_rw [h_upd] at hc
  rw [← hc]
  conv_lhs => rw [Polynomial.as_sum_range_C_mul_X_pow p]
  simp only [d_def, Polynomial.eval_finset_sum, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  rw [Finset.sum_range_succ,
    show p.coeff p.natDegree = 1 from hp.coeff_natDegree,
    one_mul, add_comm]
  congr 1
  rw [← Finset.sum_range_reflect (fun j => p.coeff j * c ^ j) d]
  symm
  apply Finset.sum_nbij (fun (i : Fin d) => (i : ℕ))
  · intro i _; exact Finset.mem_range.mpr i.isLt
  · intro i₁ i₂ _ _ h; exact Fin.val_injective h
  · intro j hj
    exact ⟨⟨j, Finset.mem_range.mp hj⟩, Finset.mem_univ _, rfl⟩
  · intro _ _; rfl

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
noncomputable def Φ_ex : Formula (Fin 2) (FieldAtom (Fin 2) ℤ) :=
  .exists_ 1 (eq_zero (X 0 * X 1 - 1))

/-- Ψ = X ≠ 0. -/
noncomputable def Ψ_ex : Formula (Fin 2) (FieldAtom (Fin 2) ℤ) :=
  Formula.ne_zero (X 0)

theorem freeVars_Φ : Φ_ex.freeVars = {0} := by
  simp only [Φ_ex, freeVars, eq_zero, FieldAtom.eqZero, FieldAtom.vars]
  ext x; fin_cases x
  · -- x = 0
    simp only [Finset.mem_sdiff, Finset.mem_singleton]
    exact ⟨fun _ => rfl, fun _ =>
      ⟨(MvPolynomial.mem_vars _).mpr
        ⟨Finsupp.single 0 1 + Finsupp.single 1 1,
          MvPolynomial.mem_support_iff.mpr (by
            simp only [MvPolynomial.coeff_sub, MvPolynomial.coeff_one]
            rw [show MvPolynomial.X (0 : Fin 2) * MvPolynomial.X 1 =
              MvPolynomial.monomial (Finsupp.single 0 1 + Finsupp.single 1 1) (1 : ℤ)
              from by simp [MvPolynomial.X, MvPolynomial.monomial_mul]]
            simp only [MvPolynomial.coeff_monomial,
              if_neg (show (0 : (Fin 2) →₀ ℕ) ≠ Finsupp.single 0 1 + Finsupp.single 1 1
                from by intro h; have := DFunLike.congr_fun h 0; simp at this)]
            norm_num),
          by simp [Finsupp.mem_support_iff]⟩, by decide⟩⟩
  · -- x = 1
    simp [Finset.mem_sdiff, Finset.mem_singleton]

theorem freeVars_Ψ : Ψ_ex.freeVars = {0} := by
  simp only [Ψ_ex, ne_zero, freeVars, FieldAtom.neZero, FieldAtom.vars,
    MvPolynomial.vars_X]

theorem freeVars_eq : Φ_ex.freeVars = Ψ_ex.freeVars := by
  rw [freeVars_Φ, freeVars_Ψ]

theorem Ψ_qf : Ψ_ex.IsQuantifierFree := trivial

variable {C : Type*} [Field C] [IsAlgClosed C]

omit [IsAlgClosed C] in
/-- Example 1.2: Φ and Ψ are C-equivalent. -/
theorem example_1_2 :
    Formula.CEquiv (C := C) Φ_ex Ψ_ex := by
  unfold CEquiv Φ_ex Ψ_ex ne_zero realization
  ext y
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨c, hc⟩
    simp only [realization_eq_zero, Set.mem_setOf_eq] at *
    simp only [map_sub, map_mul, map_one, MvPolynomial.aeval_X] at *
    simp only [Function.update_self,
      Function.update_of_ne (by decide : (0 : Fin 2) ≠ 1)] at hc
    intro h0
    simp only [FieldAtom.neZero, MvPolynomial.aeval_X] at h0
    rw [h0, zero_mul, zero_sub] at hc
    exact one_ne_zero (neg_eq_zero.mp hc)
  · intro h
    simp only [realization_eq_zero, Set.mem_setOf_eq] at *
    simp only [map_sub, map_mul, map_one, MvPolynomial.aeval_X] at *
    refine ⟨(y 0)⁻¹, ?_⟩
    simp only [Function.update_self,
      Function.update_of_ne (by decide : (0 : Fin 2) ≠ 1)]
    simp only [FieldAtom.neZero, MvPolynomial.aeval_X] at h
    rw [mul_inv_cancel₀ h, sub_self]

end Example_1_2

/-!
### Constructible ↔ QF-Realizable

A set is constructible if and only if it is the realization of
a quantifier-free formula.
-/

namespace Formula

variable {D : Type*} [CommRing D] {σ : Type*}
variable {C : Type*} [Field C] [Algebra D C]

/-- Conjunction of `eq_zero` atoms from a list. -/
noncomputable def conjEqZero : List (MvPolynomial σ D) → Formula σ (FieldAtom σ D)
  | [] => eq_zero 0
  | [P] => eq_zero P
  | P :: Ps => .and (eq_zero P) (conjEqZero Ps)

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
      { y | ∀ P ∈ L, MvPolynomial.aeval y P = 0 }
  | [] => by
    ext y; simp [conjEqZero, map_zero]
  | [P] => by
    ext y; simp [conjEqZero]
  | P :: Q :: Ps => by
    ext y
    simp only [conjEqZero, realization, Set.mem_inter_iff,
      Set.mem_setOf_eq, List.mem_cons]
    rw [show (conjEqZero (Q :: Ps)).realization (C := C) =
      { y | ∀ P ∈ (Q :: Ps), MvPolynomial.aeval y P = 0 }
      from conjEqZero_realization (Q :: Ps)]
    simp only [Set.mem_setOf_eq]
    constructor
    · rintro ⟨hP, hrest⟩ R hR
      rcases hR with rfl | hR
      · exact hP
      · exact hrest R (List.mem_cons.mpr hR)
    · intro h
      exact ⟨h P (Or.inl rfl),
        fun R hR => h R (Or.inr (List.mem_cons.mp hR))⟩

end Formula

open Formula in
omit [IsAlgClosed C] in
/-- Backward: QF-realizable → constructible. -/
theorem qf_realizable_isConstructible
    {Φ : Formula (Fin k) (FieldAtom (Fin k) C)} (hqf : Φ.IsQuantifierFree) :
    IsConstructibleSet (Φ.realization (C := C)) := by
  induction Φ with
  | atom a =>
    by_cases h : a.isEq = true
    · -- P = 0 case: algebraic set
      exact .algebraic ⟨{a.poly}, by
        ext y; simp [Zer, realization, h, MvPolynomial.aeval_def]⟩
    · -- P ≠ 0 case: complement of algebraic set
      have : (atom a).realization (C := C) =
          ({y | MvPolynomial.eval y a.poly = 0} : Set (Fin k → C))ᶜ := by
        ext y; simp [realization, h, Set.mem_compl_iff, Set.mem_setOf_eq]
      rw [this]
      exact .compl (.algebraic ⟨{a.poly}, by
        ext y; simp [Zer]⟩)
  | not Φ ih => exact .compl (ih hqf)
  | and Φ₁ Φ₂ ih₁ ih₂ =>
    exact .inter (ih₁ hqf.1) (ih₂ hqf.2)
  | or Φ₁ Φ₂ ih₁ ih₂ =>
    exact (ih₁ hqf.1).union (ih₂ hqf.2)
  | exists_ x Φ _ => exact absurd hqf id
  | forall_ x Φ _ => exact absurd hqf id

open Formula in
omit [IsAlgClosed C] in
/-- Forward: constructible → QF-realizable. -/
theorem constructible_isQFRealizable
    (V : Set (Fin k → C)) (hV : IsConstructibleSet V) :
    ∃ Φ : Formula (Fin k) (FieldAtom (Fin k) C), Φ.IsQuantifierFree ∧
      V = Φ.realization (C := C) := by
  induction hV with
  | algebraic hA =>
    obtain ⟨poly_set, rfl⟩ := hA
    exact ⟨conjEqZero poly_set.toList, conjEqZero_isQF _,
      by rw [conjEqZero_realization]
         ext y; simp [Zer, MvPolynomial.aeval_def]⟩
  | compl _ ih =>
    obtain ⟨Φ, hqf, rfl⟩ := ih
    exact ⟨.not Φ, hqf, by simp [realization]⟩
  | inter _ _ ih₁ ih₂ =>
    obtain ⟨Φ₁, hqf₁, rfl⟩ := ih₁
    obtain ⟨Φ₂, hqf₂, rfl⟩ := ih₂
    exact ⟨.and Φ₁ Φ₂, ⟨hqf₁, hqf₂⟩,
      by simp [realization]⟩

omit [IsAlgClosed C] in
/-- A set is constructible iff it is the realization of a
    quantifier-free formula. -/
theorem constructible_iff_qfRealizable
    (V : Set (Fin k → C)) :
    IsConstructibleSet V ↔
    ∃ Φ : Formula (Fin k) (FieldAtom (Fin k) C), Φ.IsQuantifierFree ∧
      V = Φ.realization (C := C) :=
  ⟨constructible_isQFRealizable V,
   fun ⟨_, hqf, hV⟩ => hV ▸ qf_realizable_isConstructible hqf⟩

end Azurite.BPR
