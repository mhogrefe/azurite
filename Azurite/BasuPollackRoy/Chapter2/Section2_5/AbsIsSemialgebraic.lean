import Azurite.BasuPollackRoy.Chapter2.Section2_5.SemialgebraicFunction

/-! # The absolute value function is semialgebraic

(Not in BPR.) The absolute value `x ↦ |x|` is a semialgebraic function `R → R`. Its graph
`{(x, y) | y = |x|}` splits piecewise as `{x ≥ 0 ∧ y = x} ∪ {x ≤ 0 ∧ y = -x}`, a union of
two basic semialgebraic sets. (No real closedness is needed.)
-/

namespace Azurite.BPR

open MvPolynomial

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]

/-- The absolute value function `x ↦ |x|`, valued in `Fin 1 → R`. -/
noncomputable def absFun : (Fin 1 → R) → (Fin 1 → R) := fun x _ => |x 0|

/-- **The absolute value function `x ↦ |x|` is semialgebraic.** -/
theorem absFun_isSemialgebraicFunction :
    IsSemialgebraicFunction (Set.univ : Set (Fin 1 → R)) (absFun (R := R)) := by
  have hcidx : (Fin.castAdd 1 (0 : Fin 1) : Fin 2) = 0 := Fin.ext rfl
  have hnidx : (Fin.natAdd 1 (0 : Fin 1) : Fin 2) = 1 := Fin.ext rfl
  have hgraph : funGraph (Set.univ : Set (Fin 1 → R)) absFun
      = {z : Fin 2 → R | z 1 = |z 0|} := by
    ext z
    rw [mem_funGraph]
    simp only [Set.mem_univ, true_and, Set.mem_setOf_eq]
    constructor
    · intro hb; simpa [absFun, Function.comp_apply, hcidx, hnidx] using congrFun hb 0
    · intro hz1; funext i; rw [Subsingleton.elim i 0]
      simpa [absFun, Function.comp_apply, hcidx, hnidx] using hz1
  have hsemialg : IsSemialgebraicSet {z : Fin 2 → R | z 1 = |z 0|} := by
    have heq : {z : Fin 2 → R | z 1 = |z 0|}
        = ({z | MvPolynomial.eval z (X 0) ≥ 0} ∩ {z | MvPolynomial.eval z (X 1 - X 0) = 0}) ∪
          ({z | MvPolynomial.eval z (X 0) ≤ 0} ∩ {z | MvPolynomial.eval z (X 1 + X 0) = 0}) := by
      ext z
      simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_inter_iff, MvPolynomial.eval_X,
        map_sub, map_add, sub_eq_zero, ge_iff_le]
      constructor
      · intro h
        rcases le_total 0 (z 0) with hz | hz
        · exact Or.inl ⟨hz, by rw [h, abs_of_nonneg hz]⟩
        · exact Or.inr ⟨hz, by rw [h, abs_of_nonpos hz]; ring⟩
      · rintro (⟨hz, h⟩ | ⟨hz, h⟩)
        · rw [h, abs_of_nonneg hz]
        · rw [abs_of_nonpos hz]; linarith [h]
    rw [heq]
    exact ((IsSemialgebraicSet.geZero _).inter (IsSemialgebraicSet.eqZero _)).union
      ((IsSemialgebraicSet.leZero _).inter (IsSemialgebraicSet.eqZero _))
  show IsSemialgebraicSet (funGraph (Set.univ : Set (Fin 1 → R)) absFun)
  rw [hgraph]; exact hsemialg

end Azurite.BPR
