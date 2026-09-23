import Azurite.BasuPollackRoy.Chapter10.Section10_1.Lemma_10_13
import Azurite.BasuPollackRoy.Chapter10.Section10_1.Proposition_10_14

/-!
# BPR Corollary 10.15: subresultants of `(P, P′)` compute the separable part

For nonconstant `P` with `deg(gcd(P, P′)) = j`:

* `corollary_10_15_gcd` — `sResP_j(P, P′)` is a greatest common divisor of
  `P` and `P′`;
* `corollary_10_15_sep` — `sResV_{j−1}(P, P′)` is the separable part of `P`
  (for `1 ≤ j`; at `j = 0` the polynomial is already separable).

Instantiation of Proposition 10.14 at `Q = P′` (the hypotheses `P′ ≠ 0` and
`deg P′ < deg P` hold automatically for nonconstant `P` in characteristic
zero), combined with Lemma 10.13 through the uniqueness of the gcd-free part:
`sResV_{j−1}(P, P′)` is a constant multiple of `P/gcd(P, P′)`, which is the
separable part, and being a separable part is invariant under nonzero
constant multiples (`IsSeparablePart.C_mul_left`).
-/

namespace Azurite.BPR

open Polynomial

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]

omit [LinearOrder R] [IsStrictOrderedRing R] in
/-- **BPR Corollary 10.15, gcd part.** If `deg(gcd(P, P′)) = j`, then
`sResP_j(P, P′)` is a greatest common divisor of `P` and `P′`. -/
theorem corollary_10_15_gcd {P : Polynomial (Ri R)} (hd : 0 < P.natDegree)
    {j : ℕ} (hj : (gcd P (derivative P)).natDegree = j) :
    Associated (Chapter8.sResP P (derivative P) j) (gcd P (derivative P)) := by
  have : CharZero (Ri R) :=
    charZero_of_injective_algebraMap (FaithfulSMul.algebraMap_injective R (Ri R))
  have hP : P ≠ 0 := fun h => by rw [h, Polynomial.natDegree_zero] at hd; omega
  have hP' : derivative P ≠ 0 := fun h => by
    have := Polynomial.derivative_eq_zero.mp h
    omega
  have hpq : (derivative P).natDegree < P.natDegree :=
    Polynomial.natDegree_derivative_lt (by omega)
  exact proposition_10_14_gcd hP hP' hpq hj

omit [LinearOrder R] [IsStrictOrderedRing R] in
/-- **BPR Corollary 10.15, separable part.** If `deg(gcd(P, P′)) = j ≥ 1`,
then `sResV_{j−1}(P, P′)` is the separable part of `P`. -/
theorem corollary_10_15_sep {P : Polynomial (Ri R)} (hd : 0 < P.natDegree)
    {j : ℕ} (hj1 : 1 ≤ j) (hj : (gcd P (derivative P)).natDegree = j) :
    IsSeparablePart (Chapter8.sResV P (derivative P) (j - 1)) P := by
  have : CharZero (Ri R) :=
    charZero_of_injective_algebraMap (FaithfulSMul.algebraMap_injective R (Ri R))
  have hP : P ≠ 0 := fun h => by rw [h, Polynomial.natDegree_zero] at hd; omega
  have hP' : derivative P ≠ 0 := fun h => by
    have := Polynomial.derivative_eq_zero.mp h
    omega
  have hpq : (derivative P).natDegree < P.natDegree :=
    Polynomial.natDegree_derivative_lt (by omega)
  -- `sResV_{j-1}(P, P′)` and `P/gcd(P, P′)` are both gcd-free parts of `P`
  -- with respect to `P′`, so they agree up to a nonzero constant
  have h1 := proposition_10_14_gcdFree hP hP' hpq hj1 hj
  have h2 := gcdFreePart_isGcdFreePart P (derivative P)
  obtain ⟨c, hc, hce⟩ := isGcdFreePart_unique hP' h1 h2
  -- `P/gcd(P, P′)` is the separable part (Lemma 10.13), and the property is
  -- constant-invariant
  have h3 : IsSeparablePart (gcdFreePart P (derivative P)) P := lemma_10_13 hP
  rw [hce]
  exact h3.C_mul_left hc

end Azurite.BPR
