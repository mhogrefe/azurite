import Azurite.BasuPollackRoy.Chapter1.Section1_1.ConstructibleSets

/-!
# Exercise 1.3

A constructible set in `Cᵏ` is a finite union of basic constructible sets.

Proof outline: introduce the inductive predicate `IsFinUnionBasicConstructible`,
show that the family of finite unions of basic constructibles is closed under
complement and intersection (so it contains every constructible set), and
conclude `exercise_1_3` by induction on `IsConstructibleSet`. Closure under
complement reduces to the basic-constructible case via De Morgan; closure
under intersection distributes intersection over the unions.
-/

namespace Azurite.BPR

open MvPolynomial Polynomial

variable {k : ℕ} {C : Type*} [Field C] [IsAlgClosed C]

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

end Azurite.BPR
