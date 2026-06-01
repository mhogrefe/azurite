import Azurite.BasuPollackRoy.Chapter2.Section2_5.SemialgebraicFunction

/-! # Polynomial functions are semialgebraic

(Not in BPR.) A polynomial function `R^n → R`, `x ↦ P(x)` for `P ∈ R[X_1, …, X_n]`, is
semialgebraic: its graph `{(x, t) | t = P(x)} ⊆ R^{n+1}` is the zero set of the polynomial
`X_{last} - P` (with `P`'s variables embedded as the first `n` coordinates), hence algebraic.
-/

namespace Azurite.BPR

open MvPolynomial

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]

/-- The polynomial function `R^n → R` attached to `P`, valued in `Fin 1 → R`. -/
noncomputable def polyFun {n : ℕ} (P : MvPolynomial (Fin n) R) : (Fin n → R) → (Fin 1 → R) :=
  fun x _ => MvPolynomial.eval x P

omit [IsStrictOrderedRing R] in
/-- **A polynomial function from `R^n` to `R` is semialgebraic.** Its graph is the zero set
of `X_{last} - P`. -/
theorem polyFun_isSemialgebraicFunction {n : ℕ} (P : MvPolynomial (Fin n) R) :
    IsSemialgebraicFunction (Set.univ : Set (Fin n → R)) (polyFun P) := by
  set Q : MvPolynomial (Fin (n + 1)) R :=
    MvPolynomial.X (Fin.natAdd n 0) - MvPolynomial.rename (Fin.castAdd 1) P with hQ
  have hQeval : ∀ z : Fin (n + 1) → R,
      MvPolynomial.eval z Q = z (Fin.natAdd n 0) - MvPolynomial.eval (z ∘ Fin.castAdd 1) P := by
    intro z
    rw [hQ, map_sub, MvPolynomial.eval_X, MvPolynomial.eval_rename]
  have hgraph : funGraph (Set.univ : Set (Fin n → R)) (polyFun P)
      = {z : Fin (n + 1) → R | MvPolynomial.eval z Q = 0} := by
    ext z
    simp only [mem_funGraph, Set.mem_univ, true_and, Set.mem_setOf_eq, hQeval, sub_eq_zero]
    constructor
    · intro h; simpa [polyFun] using congrFun h 0
    · intro h; funext i; rw [Subsingleton.elim i 0]; simpa [polyFun] using h
  show IsSemialgebraicSet (funGraph (Set.univ : Set (Fin n → R)) (polyFun P))
  rw [hgraph]
  exact IsSemialgebraicSet.eqZero Q

end Azurite.BPR
