import Azurite.BasuPollackRoy.Chapter1.Section1_1.Notation1_1

/-!
# Constructible Sets

A **basic constructible set** over `Cᵏ` is a member of the smallest family of
subsets of `Cᵏ` that includes the algebraic sets and their complements, and
is closed under finite intersections.

A **constructible set** over `Cᵏ` is a member of the smallest family of subsets
of `Cᵏ` that includes the algebraic sets and is closed under complementation,
finite unions, and finite intersections.

We define `IsConstructibleSet` with complement and intersection only; closure
under union follows by De Morgan.
-/

namespace Azurite.BPR

open MvPolynomial Polynomial

variable {k : ℕ} {C : Type*} [Field C] [IsAlgClosed C]

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

end Azurite.BPR
