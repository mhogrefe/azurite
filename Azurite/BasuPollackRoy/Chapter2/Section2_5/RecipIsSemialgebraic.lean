import Azurite.BasuPollackRoy.Chapter2.Section2_5.SemialgebraicFunction

/-! # The reciprocal function is semialgebraic on `R ∖ {0}`

(Not in BPR.) The inverse function `x ↦ 1/x` is semialgebraic on `R ∖ {0}`: its graph
`{(x, y) | y · x = 1}` is the zero set of `X_2 · X_1 - 1`, hence algebraic. (No real
closedness is needed; this is a purely field-theoretic example.)
-/

namespace Azurite.BPR

open MvPolynomial

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]

/-- The reciprocal function `x ↦ 1/x = x⁻¹`, valued in `Fin 1 → R`. -/
noncomputable def recipFun : (Fin 1 → R) → (Fin 1 → R) := fun x _ => (x 0)⁻¹

omit [IsStrictOrderedRing R] in
/-- **The reciprocal function `x ↦ 1/x` is semialgebraic on `R ∖ {0}`.** Its graph is the
zero set of `X_2 · X_1 - 1`. -/
theorem recipFun_isSemialgebraicFunction :
    IsSemialgebraicFunction {x : Fin 1 → R | x 0 ≠ 0} (recipFun (R := R)) := by
  have hcidx : (Fin.castAdd 1 (0 : Fin 1) : Fin 2) = 0 := Fin.ext rfl
  have hnidx : (Fin.natAdd 1 (0 : Fin 1) : Fin 2) = 1 := Fin.ext rfl
  have hgraph : funGraph {x : Fin 1 → R | x 0 ≠ 0} recipFun
      = {z : Fin 2 → R | MvPolynomial.eval z (X 1 * X 0 - 1) = 0} := by
    ext z
    rw [mem_funGraph]
    simp only [Set.mem_setOf_eq, map_sub, map_mul, MvPolynomial.eval_X, map_one, sub_eq_zero]
    constructor
    · rintro ⟨ha, hb⟩
      have ha0 : z 0 ≠ 0 := by
        have h : (z ∘ Fin.castAdd 1) 0 ≠ 0 := ha
        rwa [Function.comp_apply, hcidx] at h
      have hb0 : z 1 = (z 0)⁻¹ := by
        have h := congrFun hb 0
        simpa only [Function.comp_apply, hcidx, hnidx, recipFun] using h
      rw [hb0, inv_mul_cancel₀ ha0]
    · intro hc
      have ha0 : z 0 ≠ 0 := by
        intro h0; rw [h0, mul_zero] at hc; exact one_ne_zero hc.symm
      refine ⟨?_, ?_⟩
      · show (z ∘ Fin.castAdd 1) 0 ≠ 0
        rwa [Function.comp_apply, hcidx]
      · funext i; rw [Subsingleton.elim i 0]
        show (z ∘ Fin.natAdd 1) 0 = ((z ∘ Fin.castAdd 1) 0)⁻¹
        simp only [Function.comp_apply, hcidx, hnidx]
        exact eq_inv_of_mul_eq_one_left hc
  show IsSemialgebraicSet (funGraph {x : Fin 1 → R | x 0 ≠ 0} recipFun)
  rw [hgraph]
  exact IsSemialgebraicSet.eqZero _

end Azurite.BPR
