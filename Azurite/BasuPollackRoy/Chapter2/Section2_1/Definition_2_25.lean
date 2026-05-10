import Mathlib.Data.Sign.Basic

/-!
# BPR Definition 2.25: Sign Conditions

**Definition 2.25 (BPR).** Let `Q` be a finite subset of `R[X₁, …, Xₖ]`.
A *sign condition* on `Q` is an element of `{0, 1, −1}^Q`, i.e. a mapping
from `Q` to `{0, 1, −1}`.  A *strict sign condition* on `Q` is an element
of `{1, −1}^Q`.  We say that `Q` *realizes* the sign condition `σ` at
`x ∈ Rᵏ` if `sign(Q(x)) = σ(Q)` for every `Q ∈ Q`.

We formalise sign conditions as functions `ι → SignType` indexed by an
arbitrary type `ι` (typically a `Fintype` indexing a family of polynomials).
Realization is defined generically over any evaluation `v : ι → R`;
for polynomials one instantiates `v i = (Q i).eval x`.

The adjacent **Notation 2.26** (the derivative list `Der(P)`) lives in its
own file `Azurite.BasuPollackRoy.Chapter2.Section2_1.Notation_2_26`.
-/

namespace Azurite.BPR

/-- A **sign condition** on a family indexed by `ι` is a mapping `ι → SignType`,
    assigning a sign `0`, `1`, or `−1` to each index (BPR Definition 2.25). -/
abbrev SignCondition (ι : Type*) := ι → SignType

namespace SignCondition

variable {ι : Type*} {R : Type*}

/-- A sign condition is **strict** if it takes only the values `1` and `−1`
    (never `0`). -/
def IsStrict (σ : SignCondition ι) : Prop := ∀ i, σ i ≠ 0

/-- A family of values `v : ι → R` **realizes** sign condition `σ` if
    `sign(v i) = σ(i)` for every `i`.

    For a family `Q` of polynomials and a point `x`, use
    `σ.IsRealizedBy (fun i => (Q i).eval x)`. -/
def IsRealizedBy [Zero R] [Preorder R] [DecidableRel ((· < ·) : R → R → Prop)]
    (σ : SignCondition ι) (v : ι → R) : Prop :=
  ∀ i, SignType.sign (v i) = σ i

/-- The **realization** of sign condition `σ` with respect to a family of
    functions `Q : ι → (X → R)` is the set of points `x` at which `Q`
    realizes `σ`:  `Reali(σ) = { x ∈ Rᵏ | ∀ i, sign(Q_i(x)) = σ(i) }`.

    For polynomials, use `σ.realization (fun i x => (Q i).eval x)`. -/
def realization [Zero R] [Preorder R] [DecidableRel ((· < ·) : R → R → Prop)]
    (σ : SignCondition ι) (Q : ι → (X → R)) : Set X :=
  {x | σ.IsRealizedBy (fun i => Q i x)}

/-- A sign condition `σ` is **realizable** with respect to `Q` if its
    realization is non-empty, i.e. there exists a point where `Q` realizes `σ`. -/
def IsRealizable [Zero R] [Preorder R] [DecidableRel ((· < ·) : R → R → Prop)]
    (σ : SignCondition ι) (Q : ι → (X → R)) : Prop :=
  (σ.realization Q).Nonempty

end SignCondition

end Azurite.BPR
