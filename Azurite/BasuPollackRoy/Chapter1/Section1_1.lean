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

end Azurite.BPR
