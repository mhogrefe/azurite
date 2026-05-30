import Azurite.BasuPollackRoy.Chapter1.Section1_1.Realization
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.Algebra.Order.Ring.Defs

/-!
# Atoms and Formulas for the Language of Ordered Fields

BPR Section 2.3 develops formulas over real-closed fields. Where the
algebraically-closed case (Chapter 1) had two atomic predicates `P = 0`
and `P ≠ 0`, the ordered case offers six: `=`, `≠`, `<`, `>`, `≤`, `≥`
applied to a polynomial against `0`. This file mirrors
`Azurite/BasuPollackRoy/Chapter1/Section1_1/FieldFormula.lean` for the
ordered setting.

The six relations are technically redundant (`P < 0` is `¬ (P ≥ 0)`,
`P ≤ 0` is `P < 0 ∨ P = 0`, etc.), but we keep all six so that formulas
remain expressive at the surface level. Algorithms that need a smaller
basis (e.g., sign condition normalisation) can collapse them.

`OrderedFieldAtom` is wired into the generic `AtomVars` and
`AtomRealization` typeclasses from `FieldFormula`/`Realization`, so the
`Formula.freeVars`, `Formula.boundVars`, `Formula.isSentence`, and
`Formula.realization` definitions used in Chapter 1 apply unchanged to
ordered-field formulas.
-/

namespace Azurite.BPR

open MvPolynomial

/-- The six comparison predicates an ordered-field atom can express:
`P = 0`, `P ≠ 0`, `P < 0`, `P > 0`, `P ≤ 0`, `P ≥ 0`. -/
inductive OrderRel where
  | eq
  | ne
  | lt
  | gt
  | le
  | ge
deriving DecidableEq, Repr

/-- An atom in the language of ordered fields: a polynomial `P` together
    with one of the six comparison relations `P R 0`. -/
structure OrderedFieldAtom (σ : Type*) (D : Type*) [CommRing D] where
  poly : MvPolynomial σ D
  rel : OrderRel

namespace OrderedFieldAtom

variable {σ τ : Type*} {D : Type*} [CommRing D]

/-- The atom `P = 0`. -/
def eqZero (P : MvPolynomial σ D) : OrderedFieldAtom σ D := ⟨P, .eq⟩

/-- The atom `P ≠ 0`. -/
def neZero (P : MvPolynomial σ D) : OrderedFieldAtom σ D := ⟨P, .ne⟩

/-- The atom `P < 0`. -/
def ltZero (P : MvPolynomial σ D) : OrderedFieldAtom σ D := ⟨P, .lt⟩

/-- The atom `P > 0`. -/
def gtZero (P : MvPolynomial σ D) : OrderedFieldAtom σ D := ⟨P, .gt⟩

/-- The atom `P ≤ 0`. -/
def leZero (P : MvPolynomial σ D) : OrderedFieldAtom σ D := ⟨P, .le⟩

/-- The atom `P ≥ 0`. -/
def geZero (P : MvPolynomial σ D) : OrderedFieldAtom σ D := ⟨P, .ge⟩

/-- Free variables of an ordered field atom. -/
noncomputable def vars [DecidableEq σ] (a : OrderedFieldAtom σ D) : Finset σ :=
  a.poly.vars

/-- Rename variables in an ordered field atom. -/
noncomputable def renameVars (f : σ → τ) (a : OrderedFieldAtom σ D) :
    OrderedFieldAtom τ D :=
  ⟨a.poly.rename f, a.rel⟩

end OrderedFieldAtom

/-- `OrderedFieldAtom` instance of `AtomVars`: variables of the underlying
polynomial. -/
noncomputable instance {σ : Type*} [DecidableEq σ] {D : Type*} [CommRing D] :
    AtomVars (OrderedFieldAtom σ D) σ where
  vars := OrderedFieldAtom.vars

/-- Unfold `AtomVars.vars` on an `OrderedFieldAtom` to `OrderedFieldAtom.vars`. -/
@[simp] theorem AtomVars.vars_orderedFieldAtom {σ : Type*} [DecidableEq σ]
    {D : Type*} [CommRing D] (a : OrderedFieldAtom σ D) :
    (AtomVars.vars a : Finset σ) = OrderedFieldAtom.vars a := rfl

/-- `OrderedFieldAtom` instance of `AtomRealization` over a linearly-ordered
field `R` that is a `D`-algebra: each of the six relations is interpreted as
the corresponding predicate on `aeval y a.poly`. -/
noncomputable instance {σ : Type*} {D : Type*} [CommRing D]
    {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [Algebra D R] :
    AtomRealization (OrderedFieldAtom σ D) σ R where
  interpret a := match a.rel with
    | .eq => { y | aeval y a.poly = 0 }
    | .ne => { y | aeval y a.poly ≠ 0 }
    | .lt => { y | aeval y a.poly < 0 }
    | .gt => { y | aeval y a.poly > 0 }
    | .le => { y | aeval y a.poly ≤ 0 }
    | .ge => { y | aeval y a.poly ≥ 0 }

namespace Formula

variable {σ : Type*} {D : Type*} [CommRing D]

/-- `P = 0` as a formula. -/
noncomputable def eqZeroO (P : MvPolynomial σ D) :
    Formula σ (OrderedFieldAtom σ D) :=
  .atom (OrderedFieldAtom.eqZero P)

/-- `P ≠ 0` as a formula. -/
noncomputable def neZeroO (P : MvPolynomial σ D) :
    Formula σ (OrderedFieldAtom σ D) :=
  .atom (OrderedFieldAtom.neZero P)

/-- `P < 0` as a formula. -/
noncomputable def ltZeroO (P : MvPolynomial σ D) :
    Formula σ (OrderedFieldAtom σ D) :=
  .atom (OrderedFieldAtom.ltZero P)

/-- `P > 0` as a formula. -/
noncomputable def gtZeroO (P : MvPolynomial σ D) :
    Formula σ (OrderedFieldAtom σ D) :=
  .atom (OrderedFieldAtom.gtZero P)

/-- `P ≤ 0` as a formula. -/
noncomputable def leZeroO (P : MvPolynomial σ D) :
    Formula σ (OrderedFieldAtom σ D) :=
  .atom (OrderedFieldAtom.leZero P)

/-- `P ≥ 0` as a formula. -/
noncomputable def geZeroO (P : MvPolynomial σ D) :
    Formula σ (OrderedFieldAtom σ D) :=
  .atom (OrderedFieldAtom.geZero P)

end Formula

/-!
### Realization over a linearly-ordered field

The realization of an ordered-field formula in an assignment `y : σ → R`
to a linearly-ordered field `R` (a `D`-algebra) sends each atom to the
appropriate predicate on `aeval y a.poly`.

These simp lemmas restate the per-atom realizations for direct rewriting,
now that `Formula.realization` is the generic typeclass-driven version
defined in `Realization.lean`.
-/

namespace Formula

variable {σ : Type*} {D : Type*} [CommRing D]
variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
  [Algebra D R]

@[simp] theorem realization_eqZeroO [DecidableEq σ]
    (P : MvPolynomial σ D) :
    (eqZeroO P : Formula σ (OrderedFieldAtom σ D)).realization (C := R) =
      { y | aeval y P = 0 } := rfl

@[simp] theorem realization_neZeroO [DecidableEq σ]
    (P : MvPolynomial σ D) :
    (neZeroO P : Formula σ (OrderedFieldAtom σ D)).realization (C := R) =
      { y | aeval y P ≠ 0 } := rfl

@[simp] theorem realization_ltZeroO [DecidableEq σ]
    (P : MvPolynomial σ D) :
    (ltZeroO P : Formula σ (OrderedFieldAtom σ D)).realization (C := R) =
      { y | aeval y P < 0 } := rfl

@[simp] theorem realization_gtZeroO [DecidableEq σ]
    (P : MvPolynomial σ D) :
    (gtZeroO P : Formula σ (OrderedFieldAtom σ D)).realization (C := R) =
      { y | aeval y P > 0 } := rfl

@[simp] theorem realization_leZeroO [DecidableEq σ]
    (P : MvPolynomial σ D) :
    (leZeroO P : Formula σ (OrderedFieldAtom σ D)).realization (C := R) =
      { y | aeval y P ≤ 0 } := rfl

@[simp] theorem realization_geZeroO [DecidableEq σ]
    (P : MvPolynomial σ D) :
    (geZeroO P : Formula σ (OrderedFieldAtom σ D)).realization (C := R) =
      { y | aeval y P ≥ 0 } := rfl

/-! ### Tautologies over a linearly ordered field.

BPR remarks that $1 > 0$ is $R$-equivalent to "true" and $1 < 0$ is
$R$-equivalent to "false". In the present setup this is the
specialisation of `realization_gtZeroO` / `realization_ltZeroO` at the
constant polynomial `1`: in any linearly ordered field `1 > 0`, so the
realisation is the whole space; and `1 < 0` is impossible, so the
realisation is empty.
-/

/-- $1 > 0$ realises to `Set.univ`: this is the canonical
ordered-field tautology. -/
@[simp] theorem realization_gtZeroO_one [DecidableEq σ] :
    ((gtZeroO 1 : Formula σ (OrderedFieldAtom σ D)).realization (C := R)) =
      Set.univ := by
  ext y
  simp [realization_gtZeroO, zero_lt_one]

/-- $1 < 0$ realises to `∅`: this is the canonical ordered-field
contradiction. -/
@[simp] theorem realization_ltZeroO_one [DecidableEq σ] :
    ((ltZeroO 1 : Formula σ (OrderedFieldAtom σ D)).realization (C := R)) =
      (∅ : Set (σ → R)) := by
  ext y
  simp [realization_ltZeroO, not_lt.mpr zero_le_one]

end Formula

end Azurite.BPR
