import Azurite.BasuPollackRoy.Chapter10.Section10_1.SeparablePart

/-!
# BPR §10.1: the gcd-free part

More generally than the separable part, the *gcd-free part* of `P` with
respect to `Q` is the divisor `D` of `P` such that `D·Q = lcm(P, Q)`; it
equals `P/gcd(P, Q)` and is unique up to a multiplicative constant.

Formalized as the predicate `IsGcdFreePart D P Q` (`D` divides `P`, and
`D·Q` is *an* lcm of `P` and `Q` — `Associated` to the Euclidean-domain
`lcm`, since an lcm is itself only determined up to a constant), with the
canonical witness `gcdFreePart P Q = P/gcd(P, Q)`
(`gcdFreePart_isGcdFreePart`; its product with `Q` is literally
`lcm(P, Q) = P·Q/gcd(P, Q)`). Uniqueness (`isGcdFreePart_unique`, for
`Q ≠ 0`) is cancellation of `Q` between two associated products.

The separable part of `P` (Lemma 10.13) is the gcd-free part of `P` with
respect to `P′`.
-/

namespace Azurite.BPR

open Polynomial

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]

/-- `D` is a **gcd-free part** of `P` with respect to `Q`: a divisor of `P`
whose product with `Q` is an lcm of `P` and `Q`. -/
def IsGcdFreePart (D P Q : Polynomial (Ri R)) : Prop :=
  D ∣ P ∧ Associated (D * Q) (EuclideanDomain.lcm P Q)

/-- The canonical gcd-free part: `P/gcd(P, Q)`. -/
noncomputable def gcdFreePart (P Q : Polynomial (Ri R)) : Polynomial (Ri R) :=
  P / EuclideanDomain.gcd P Q

omit [LinearOrder R] [IsStrictOrderedRing R] in
/-- `P/gcd(P, Q)` is a gcd-free part of `P` with respect to `Q` — in fact its
product with `Q` is literally `lcm(P, Q)`. -/
theorem gcdFreePart_isGcdFreePart (P Q : Polynomial (Ri R)) :
    IsGcdFreePart (gcdFreePart P Q) P Q := by
  rcases eq_or_ne (EuclideanDomain.gcd P Q) 0 with hg | hg
  · -- degenerate case `P = Q = 0`
    obtain ⟨hP, hQ⟩ := EuclideanDomain.gcd_eq_zero_iff.mp hg
    subst hP; subst hQ
    refine ⟨dvd_zero _, ?_⟩
    rw [mul_zero]
    simp [EuclideanDomain.lcm]
  · have hfac : EuclideanDomain.gcd P Q * gcdFreePart P Q = P :=
      EuclideanDomain.mul_div_cancel' hg (EuclideanDomain.gcd_dvd_left _ _)
    constructor
    · exact Dvd.intro_left _ hfac
    · have hlcm : EuclideanDomain.lcm P Q = gcdFreePart P Q * Q := by
        have h1 : P * Q = EuclideanDomain.gcd P Q * (gcdFreePart P Q * Q) := by
          rw [← mul_assoc, hfac]
        have h2 : EuclideanDomain.gcd P Q
            * (EuclideanDomain.gcd P Q * (gcdFreePart P Q * Q) / EuclideanDomain.gcd P Q)
            = EuclideanDomain.gcd P Q * (gcdFreePart P Q * Q) :=
          EuclideanDomain.mul_div_cancel' hg ⟨_, rfl⟩
        rw [EuclideanDomain.lcm, h1]
        exact mul_left_cancel₀ hg h2
      rw [hlcm]

omit [LinearOrder R] [IsStrictOrderedRing R] in
/-- **Uniqueness.** The gcd-free part of `P` with respect to `Q ≠ 0` is
unique up to a multiplicative constant. -/
theorem isGcdFreePart_unique {D₁ D₂ P Q : Polynomial (Ri R)} (hQ : Q ≠ 0)
    (h₁ : IsGcdFreePart D₁ P Q) (h₂ : IsGcdFreePart D₂ P Q) :
    ∃ c : Ri R, c ≠ 0 ∧ D₁ = C c * D₂ := by
  obtain ⟨u, hu⟩ := (h₁.2.trans h₂.2.symm)
  have hcancel : D₁ * u = D₂ := by
    have h := hu
    rw [mul_comm D₁ Q, mul_assoc, mul_comm D₂ Q] at h
    exact mul_left_cancel₀ hQ h
  obtain ⟨c, hcu, hCc⟩ := Polynomial.isUnit_iff.mp u⁻¹.isUnit
  refine ⟨c, hcu.ne_zero, ?_⟩
  rw [← hcancel, hCc, mul_comm ((↑u⁻¹ : Polynomial (Ri R))), mul_assoc,
    Units.mul_inv, mul_one]

end Azurite.BPR
