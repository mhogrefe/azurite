import Azurite.BasuPollackRoy.Chapter2.Section2_5.SemialgebraicFunction
import Mathlib.Basic.Sign.Defs

/-! # The sign function is semialgebraic

(Not in BPR.) The sign function `x ↦ sgn(x)` (with values in `{-1, 0, 1}`) is a semialgebraic
function `R → R`. Its graph splits into three branches
`{x < 0 ∧ y = -1} ∪ {x = 0 ∧ y = 0} ∪ {x > 0 ∧ y = 1}`, each a basic semialgebraic set.
-/

namespace Azurite.BPR

open MvPolynomial

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]

/-- The sign function `x ↦ sgn(x) ∈ {-1, 0, 1}`, valued in `Fin 1 → R`. -/
noncomputable def signFun : (Fin 1 → R) → (Fin 1 → R) :=
  fun x _ => (SignType.sign (x 0) : R)

/-- **The sign function is semialgebraic.** -/
theorem signFun_isSemialgebraicFunction :
    IsSemialgebraicFunction (Set.univ : Set (Fin 1 → R)) (signFun (R := R)) := by
  have hcidx : (Fin.castAdd 1 (0 : Fin 1) : Fin 2) = 0 := Fin.ext rfl
  have hnidx : (Fin.natAdd 1 (0 : Fin 1) : Fin 2) = 1 := Fin.ext rfl
  have hgraph : funGraph (Set.univ : Set (Fin 1 → R)) signFun
      = {z : Fin 2 → R | z 1 = (SignType.sign (z 0) : R)} := by
    ext z
    rw [mem_funGraph]
    simp only [Set.mem_univ, true_and, Set.mem_ofPred_eq]
    constructor
    · intro hb; simpa [signFun, Function.comp_apply, hcidx, hnidx] using congrFun hb 0
    · intro hz1; funext i; rw [Subsingleton.elim i 0]
      simpa [signFun, Function.comp_apply, hcidx, hnidx] using hz1
  have hsemialg : IsSemialgebraicSet {z : Fin 2 → R | z 1 = (SignType.sign (z 0) : R)} := by
    have heq : {z : Fin 2 → R | z 1 = (SignType.sign (z 0) : R)}
        = ({z | MvPolynomial.eval z (X 0) < 0} ∩ {z | MvPolynomial.eval z (X 1 + 1) = 0}) ∪
          (({z | MvPolynomial.eval z (X 0) = 0} ∩ {z | MvPolynomial.eval z (X 1) = 0}) ∪
           ({z | MvPolynomial.eval z (X 0) > 0} ∩ {z | MvPolynomial.eval z (X 1 - 1) = 0})) := by
      ext z
      simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_inter_iff, MvPolynomial.eval_X,
        map_add, map_sub, map_one, sub_eq_zero, gt_iff_lt]
      constructor
      · intro h
        rcases lt_trichotomy (z 0) 0 with hz | hz | hz
        · exact Or.inl ⟨hz, by rw [h, sign_neg hz]; simp⟩
        · exact Or.inr (Or.inl ⟨hz, by rw [h, hz, sign_zero]; simp⟩)
        · exact Or.inr (Or.inr ⟨hz, by rw [h, sign_pos hz]; simp⟩)
      · rintro (⟨hz, h⟩ | ⟨hz, h⟩ | ⟨hz, h⟩)
        · rw [sign_neg hz]; simp only [SignType.coe_neg_one]; linarith
        · rw [hz, sign_zero]; simpa using h
        · rw [sign_pos hz]; simpa using h
    rw [heq]
    exact ((IsSemialgebraicSet.ltZero _).inter (IsSemialgebraicSet.eqZero _)).union
      (((IsSemialgebraicSet.eqZero _).inter (IsSemialgebraicSet.eqZero _)).union
        ((IsSemialgebraicSet.gtZero _).inter (IsSemialgebraicSet.eqZero _)))
  show IsSemialgebraicSet (funGraph (Set.univ : Set (Fin 1 → R)) signFun)
  rw [hgraph]; exact hsemialg

end Azurite.BPR
