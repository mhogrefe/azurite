import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.Nullstellensatz

/-!
# Basu, Pollack, Roy — *Algorithms in Real Algebraic Geometry*
## Chapter 1, Section 1.1: Algebraically Closed Fields

Reference: Basu, S., Pollack, R., & Roy, M.-F.
*Algorithms in Real Algebraic Geometry*. Springer, 2006.

### Definition 1.1 (Algebraically Closed Field)

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

open MvPolynomial

-- C is an algebraically closed field, used throughout BPR Chapter 1.
variable {k : ℕ} {C : Type*} [Field C] [IsAlgClosed C]

/-!
### Definition 1.2 (Zero Set)

If 𝒫 is a finite subset of C[X₁, …, Xₖ], the **set of zeros** of 𝒫 in Cᵏ is

  Zer(𝒫, Cᵏ) = { x ∈ Cᵏ | ∀ P ∈ 𝒫, P(x) = 0 }

Mathlib already has `MvPolynomial.zeroLocus`, but it takes an `Ideal` rather than
a finite set of polynomials. We define `Zer` to match BPR's notation and prove
it equals Mathlib's `zeroLocus` applied to the spanned ideal.
-/

/-- The set of common zeros of a set of polynomials 𝒫 in Cᵏ.
    BPR notation: Zer(𝒫, Cᵏ). -/
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

end Azurite.BPR

