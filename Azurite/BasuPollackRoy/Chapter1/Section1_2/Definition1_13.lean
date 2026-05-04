import Azurite.BasuPollackRoy.Chapter1.Section1_2.Gcd

/-!
# Definition 1.13: Greatest common divisor of a finite family

A polynomial $G \in K[X]$ is a *greatest common divisor* of a finite
family $\mathcal{P} \subseteq K[X]$ if $G$ divides every element of
$\mathcal{P}$ and every common divisor of $\mathcal{P}$ divides $G$.
We compute a representative by folding Mathlib's pairwise gcd over the
list and verify it satisfies the specification.
-/

namespace Azurite.BPR

open Polynomial

variable {K : Type*} [Field K]

/-- BPR Definition 1.13: Greatest common divisor of a finite family of polynomials. -/
def IsListGCD (G : K[X]) (Ps : List K[X]) : Prop :=
  (∀ P ∈ Ps, G ∣ P) ∧ (∀ D, (∀ P ∈ Ps, D ∣ P) → D ∣ G)

/-- Algorithm to obtain the GCD of a family inductively. -/
noncomputable def listGcd (Ps : List K[X]) : K[X] :=
  Ps.foldr gcd 0

/-- The algorithm `listGcd` satisfies the `IsListGCD` specification. -/
theorem listGcd_isListGCD (Ps : List K[X]) : IsListGCD (listGcd Ps) Ps := by
  induction Ps with
  | nil =>
    simp [IsListGCD, listGcd]
  | cons P Ps ih =>
    simp [IsListGCD, listGcd] at *
    constructor
    · constructor
      · exact (gcd_isGCD P (Ps.foldr gcd 0)).1
      · intro P' hP'
        have hG := (gcd_isGCD P (Ps.foldr gcd 0)).2.1
        exact dvd_trans hG (ih.1 P' hP')
    · intro D h1 h2
      exact (gcd_isGCD P (Ps.foldr gcd 0)).2.2 D h1 (ih.2 D h2)

end Azurite.BPR
