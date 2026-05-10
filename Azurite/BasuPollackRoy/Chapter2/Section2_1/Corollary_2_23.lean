import Azurite.BasuPollackRoy.Chapter2.Section2_1.Proposition_2_22

/-!
# BPR Corollary 2.23: Mean Value Theorem

**Corollary 2.23 (BPR).** Let `R` be an ordered field with the intermediate
value property, `P ∈ R[X]`, `a < b`. Then there exists `c ∈ (a, b)` such that
`P(b) - P(a) = (b - a) * P'(c)`.

The proof applies Rolle's theorem (Proposition 2.22) to the linear-interpolant
auxiliary `Q(X) = (P(b) - P(a)) * (X - a) - (b - a) * (P(X) - P(a))`, which
vanishes at both endpoints.
-/

namespace Azurite.BPR.Corollary2_23

open Polynomial Azurite.BPR Azurite.BPR.Theorem2_11 Azurite.BPR.Proposition2_22

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]

/-- **BPR Corollary 2.23 (Mean Value Theorem).** Let `R` be an ordered field with
    the intermediate value property, `P ∈ R[X]`, `a < b`. Then there exists
    `c ∈ (a, b)` such that `P(b) - P(a) = (b - a) * P'(c)`. -/
theorem corollary_2_23 (hIVP : HasIntermediateValueProperty R)
    (P : R[X]) {a b : R} (hab : a < b) :
    ∃ c ∈ Set.Ioo a b, P.eval b - P.eval a = (b - a) * (derivative P).eval c := by
  -- Q(X) = (P(b) - P(a)) * (X - a) - (b - a) * (P(X) - P(a))
  set Q := C (P.eval b - P.eval a) * (X - C a) - C (b - a) * (P - C (P.eval a))
  have hQa : Q.eval a = 0 := by simp [Q]
  have hQb : Q.eval b = 0 := by simp [Q]; ring
  obtain ⟨c, hc, hQ'c⟩ := proposition_2_22 hIVP Q hab hQa hQb
  refine ⟨c, hc, ?_⟩
  -- Q'(X) = (P(b) - P(a)) - (b - a) * P'(X), so Q'(c) = 0 gives the result
  have hQ' : derivative Q = C (P.eval b - P.eval a) - C (b - a) * derivative P := by
    simp [Q, derivative_sub, derivative_mul, derivative_C]
  have hQ'c_eq : (derivative Q).eval c =
      (P.eval b - P.eval a) - (b - a) * (derivative P).eval c := by
    simp [hQ']
  linarith

/-- **Corollary 2.23 (Mean Value Theorem), real closed form.** -/
theorem corollary_2_23_of_isRealClosed
    {R : Type*} [Field R] [IsRealClosed R]
    (P : R[X]) {a b : R} :
    letI : LinearOrder R := IsRealClosed.toLinearOrder
    a < b →
    ∃ c ∈ Set.Ioo a b, P.eval b - P.eval a = (b - a) * (derivative P).eval c := by
  letI : LinearOrder R := IsRealClosed.toLinearOrder
  letI : IsOrderedRing R := IsRealClosed.toIsOrderedRing
  haveI : IsStrictOrderedRing R := IsOrderedRing.toIsStrictOrderedRing R
  haveI : IsAlgClosed (Ri R) := isAlgClosed_Ri
  exact corollary_2_23 theorem_2_11_b_c P

end Azurite.BPR.Corollary2_23
