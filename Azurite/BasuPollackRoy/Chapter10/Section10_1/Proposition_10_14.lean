/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.BasuPollackRoy.Chapter10.Section10_1.GcdFreePart
import Azurite.BasuPollackRoy.Chapter8.Section8_3.Proposition_8_42
import Azurite.BasuPollackRoy.Chapter8.Section8_3.Theorem_8_34

/-!
# BPR Proposition 10.14: subresultants compute the gcd and the gcd-free part

For `deg(gcd(P, Q)) = j` (with `q < p`, both nonzero):

* `proposition_10_14_gcd` — `sResP_j(P, Q)` is a greatest common divisor of
  `P` and `Q` (`Associated` to the gcd); this is the gcd branch of
  Theorem 8.34 (`associated_sResP_gcd`), restated here;
* `proposition_10_14_gcdFree` — `sResV_{j−1}(P, Q)` is the gcd-free part of
  `P` with respect to `Q` (`IsGcdFreePart`), for `1 ≤ j`.

BPR's proof of the second part: Theorem 8.34 gives `sResP_{j−1}(P,Q) = 0`,
so by the Bezout identity of Proposition 8.42,

  `sResU_{j−1}(P,Q)·P = −sResV_{j−1}(P,Q)·Q`

is a common multiple of `P` and `Q`, hence a multiple of `lcm(P, Q)`, which
has degree `p + q − j`. By the degree bounds of Proposition 8.42 the product
`sResV_{j−1}·Q` has degree at most `(p − j) + q`, so it is a *constant*
multiple of the lcm — which is the `Associated` clause of `IsGcdFreePart`;
divisibility `sResV_{j−1} ∣ P` follows by cancelling `Q` against
`gcd·lcm = P·Q`. Nonvanishing of `sResV_{j−1}` (needed to start) is
Proposition 8.42(c): its degree is exactly `p − j` since `sRes_j ≠ 0` at the
gcd degree (Proposition 4.26).

`gcd` here is the `GCDMonoid` gcd (as in Chapter 8); the `EuclideanDomain`
gcd/lcm of `IsGcdFreePart` is bridged by `associated_of_dvd_dvd`.
-/

namespace Azurite.BPR

open Polynomial

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]

omit [LinearOrder R] [IsStrictOrderedRing R] in
/-- **BPR Proposition 10.14, gcd part.** If `deg(gcd(P, Q)) = j`, then
`sResP_j(P, Q)` is a greatest common divisor of `P` and `Q`. -/
theorem proposition_10_14_gcd {P Q : Polynomial (Ri R)} (hP : P ≠ 0) (hQ : Q ≠ 0)
    (hpq : Q.natDegree < P.natDegree) {j : ℕ} (hj : (gcd P Q).natDegree = j) :
    Associated (Chapter8.sResP P Q j) (gcd P Q) :=
  Chapter8.associated_sResP_gcd P Q hP hQ hpq hj

omit [LinearOrder R] [IsStrictOrderedRing R] in
/-- **BPR Proposition 10.14, gcd-free part.** If `deg(gcd(P, Q)) = j ≥ 1`,
then `sResV_{j−1}(P, Q)` is the gcd-free part of `P` with respect to `Q`. -/
theorem proposition_10_14_gcdFree {P Q : Polynomial (Ri R)} (hP : P ≠ 0) (hQ : Q ≠ 0)
    (hpq : Q.natDegree < P.natDegree) {j : ℕ} (hj1 : 1 ≤ j)
    (hj : (gcd P Q).natDegree = j) :
    IsGcdFreePart (Chapter8.sResV P Q (j - 1)) P Q := by
  have hjq : j ≤ Q.natDegree :=
    hj ▸ Polynomial.natDegree_le_of_dvd (gcd_dvd_right P Q) hQ
  -- non-defectiveness at the gcd degree: `sRes_j ≠ 0`, so `deg sResV_{j-1} = p - j`
  have hsRes : Azurite.BPR.Chapter4.sRes P Q j ≠ 0 :=
    ((Azurite.BPR.Chapter4.Proposition_4_26 P Q hP hQ j hjq (by omega)).mp hj).2
  obtain ⟨hVnd, hVlc⟩ := Chapter8.sResV_sub_one_natDegree P Q hP hpq hj1 hjq hsRes
  have hVne : Chapter8.sResV P Q (j - 1) ≠ 0 := by
    intro h
    rw [h, Polynomial.leadingCoeff_zero] at hVlc
    exact mul_ne_zero (Polynomial.leadingCoeff_ne_zero.mpr hP) hsRes hVlc.symm
  -- `sResP_{j-1} = 0` (Theorem 8.34) and the Bezout identity (Proposition 8.42)
  have hP0 : Chapter8.sResP P Q (j - 1) = 0 :=
    Chapter8.sResP_eq_zero_of_lt_gcd P Q hP hQ hpq (by omega) (by omega)
  have hbez := Chapter8.sResP_eq_cofactor P Q hQ hpq (show j - 1 ≤ Q.natDegree by omega)
  rw [hP0] at hbez
  have hM : Chapter8.sResV P Q (j - 1) * Q = -(Chapter8.sResU P Q (j - 1) * P) :=
    eq_neg_of_add_eq_zero_right hbez.symm
  -- `sResV_{j-1}·Q` is a common multiple of `P` and `Q`, hence of `lcm(P, Q)`
  have hPd : P ∣ Chapter8.sResV P Q (j - 1) * Q :=
    ⟨-(Chapter8.sResU P Q (j - 1)), by rw [hM]; ring⟩
  have hQd : Q ∣ Chapter8.sResV P Q (j - 1) * Q := dvd_mul_left Q _
  have hlcmd : EuclideanDomain.lcm P Q ∣ Chapter8.sResV P Q (j - 1) * Q :=
    EuclideanDomain.lcm_dvd hPd hQd
  -- degree bookkeeping: both sides have degree `p + q - j`
  have hdegM : (Chapter8.sResV P Q (j - 1) * Q).natDegree
      = P.natDegree + Q.natDegree - j := by
    rw [Polynomial.natDegree_mul hVne hQ, hVnd]
    omega
  have hgcdE : Associated (EuclideanDomain.gcd P Q) (gcd P Q) :=
    associated_of_dvd_dvd
      (dvd_gcd (EuclideanDomain.gcd_dvd_left _ _) (EuclideanDomain.gcd_dvd_right _ _))
      (EuclideanDomain.dvd_gcd (gcd_dvd_left _ _) (gcd_dvd_right _ _))
  have hgcdE_deg : (EuclideanDomain.gcd P Q).natDegree = j := by
    rw [Polynomial.natDegree_eq_of_degree_eq (degree_eq_degree_of_associated hgcdE), hj]
  have hlcm_ne : EuclideanDomain.lcm P Q ≠ 0 := by
    intro h
    have h2 := EuclideanDomain.gcd_mul_lcm P Q
    rw [h, mul_zero] at h2
    exact mul_ne_zero hP hQ h2.symm
  have hgcd_ne : EuclideanDomain.gcd P Q ≠ 0 := fun h =>
    hP (EuclideanDomain.gcd_eq_zero_iff.mp h).1
  have hdeglcm : (EuclideanDomain.lcm P Q).natDegree
      = P.natDegree + Q.natDegree - j := by
    have h2 := congrArg Polynomial.natDegree (EuclideanDomain.gcd_mul_lcm P Q)
    rw [Polynomial.natDegree_mul hgcd_ne hlcm_ne, Polynomial.natDegree_mul hP hQ,
      hgcdE_deg] at h2
    omega
  -- the quotient is a nonzero constant, i.e. a unit
  obtain ⟨c, hc⟩ := hlcmd
  have hcne : c ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hc
    exact mul_ne_zero hVne hQ hc
  have hcdeg : c.natDegree = 0 := by
    have h2 := congrArg Polynomial.natDegree hc
    rw [Polynomial.natDegree_mul hlcm_ne hcne, hdegM, hdeglcm] at h2
    omega
  have hcu : IsUnit c := by
    rw [Polynomial.eq_C_of_natDegree_eq_zero hcdeg, Polynomial.isUnit_C]
    exact isUnit_iff_ne_zero.mpr (fun h => hcne (by
      rw [Polynomial.eq_C_of_natDegree_eq_zero hcdeg, h, Polynomial.C_0]))
  obtain ⟨u, hu⟩ := hcu
  constructor
  · -- divisibility: cancel `Q` against `gcd·lcm = P·Q` to get `sResV·gcdE = P·c`
    have hVg : Chapter8.sResV P Q (j - 1) * EuclideanDomain.gcd P Q = P * c := by
      apply mul_right_cancel₀ hQ
      calc Chapter8.sResV P Q (j - 1) * EuclideanDomain.gcd P Q * Q
          = EuclideanDomain.gcd P Q * EuclideanDomain.lcm P Q * c := by
            rw [show EuclideanDomain.gcd P Q * EuclideanDomain.lcm P Q * c
              = (EuclideanDomain.lcm P Q * c) * EuclideanDomain.gcd P Q from by ring,
              ← hc]
            ring
        _ = P * c * Q := by rw [EuclideanDomain.gcd_mul_lcm]; ring
    refine ⟨EuclideanDomain.gcd P Q * ↑u⁻¹, ?_⟩
    have h2 : Chapter8.sResV P Q (j - 1) * EuclideanDomain.gcd P Q * ↑u⁻¹
        = P * ↑u * ↑u⁻¹ := by rw [hVg, hu]
    rw [mul_assoc, Units.mul_inv_cancel_right] at h2
    exact h2.symm
  · -- `sResV_{j-1}·Q` is associated to the lcm
    exact Associated.symm ⟨u, by rw [hc, hu]⟩

/-- **General-field variant of the gcd-free-part claim** (the semantic core
of Proposition 10.14, over any field): if `deg(gcd(P, Q)) = j ≥ 1`, then
`sResV_{j−1}(P, Q) · gcd(P, Q)` is associated to `P` — i.e. `sResV_{j−1}` is
the gcd-free part of `P` with respect to `Q` up to a multiplicative
constant. Serves the correctness of both the exact-division and the
determinant-fallback computations of the gcd-free part. -/
theorem sResV_gcdFree_associated {K : Type*} [Field K] [DecidableEq K]
    {P Q : Polynomial K} (hP : P ≠ 0) (hQ : Q ≠ 0)
    (hpq : Q.natDegree < P.natDegree) {j : ℕ} (hj1 : 1 ≤ j)
    (hj : (gcd P Q).natDegree = j) :
    Associated (Chapter8.sResV P Q (j - 1) * gcd P Q) P := by
  have hjq : j ≤ Q.natDegree :=
    hj ▸ Polynomial.natDegree_le_of_dvd (gcd_dvd_right P Q) hQ
  have hsRes : Azurite.BPR.Chapter4.sRes P Q j ≠ 0 :=
    ((Azurite.BPR.Chapter4.Proposition_4_26 P Q hP hQ j hjq (by omega)).mp hj).2
  obtain ⟨hVnd, hVlc⟩ := Chapter8.sResV_sub_one_natDegree P Q hP hpq hj1 hjq hsRes
  have hVne : Chapter8.sResV P Q (j - 1) ≠ 0 := by
    intro h
    rw [h, Polynomial.leadingCoeff_zero] at hVlc
    exact mul_ne_zero (Polynomial.leadingCoeff_ne_zero.mpr hP) hsRes hVlc.symm
  have hP0 : Chapter8.sResP P Q (j - 1) = 0 :=
    Chapter8.sResP_eq_zero_of_lt_gcd P Q hP hQ hpq (by omega) (by omega)
  have hbez := Chapter8.sResP_eq_cofactor P Q hQ hpq (show j - 1 ≤ Q.natDegree by omega)
  rw [hP0] at hbez
  have hM : Chapter8.sResV P Q (j - 1) * Q = -(Chapter8.sResU P Q (j - 1) * P) :=
    eq_neg_of_add_eq_zero_right hbez.symm
  have hPd : P ∣ Chapter8.sResV P Q (j - 1) * Q :=
    ⟨-(Chapter8.sResU P Q (j - 1)), by rw [hM]; ring⟩
  have hQd : Q ∣ Chapter8.sResV P Q (j - 1) * Q := dvd_mul_left Q _
  have hlcmd : EuclideanDomain.lcm P Q ∣ Chapter8.sResV P Q (j - 1) * Q :=
    EuclideanDomain.lcm_dvd hPd hQd
  have hdegM : (Chapter8.sResV P Q (j - 1) * Q).natDegree
      = P.natDegree + Q.natDegree - j := by
    rw [Polynomial.natDegree_mul hVne hQ, hVnd]
    omega
  have hgcdE : Associated (EuclideanDomain.gcd P Q) (gcd P Q) :=
    associated_of_dvd_dvd
      (dvd_gcd (EuclideanDomain.gcd_dvd_left _ _) (EuclideanDomain.gcd_dvd_right _ _))
      (EuclideanDomain.dvd_gcd (gcd_dvd_left _ _) (gcd_dvd_right _ _))
  have hgcdE_deg : (EuclideanDomain.gcd P Q).natDegree = j := by
    rw [Polynomial.natDegree_eq_of_degree_eq (degree_eq_degree_of_associated hgcdE), hj]
  have hlcm_ne : EuclideanDomain.lcm P Q ≠ 0 := by
    intro h
    have h2 := EuclideanDomain.gcd_mul_lcm P Q
    rw [h, mul_zero] at h2
    exact mul_ne_zero hP hQ h2.symm
  have hgcd_ne : EuclideanDomain.gcd P Q ≠ 0 := fun h =>
    hP (EuclideanDomain.gcd_eq_zero_iff.mp h).1
  have hdeglcm : (EuclideanDomain.lcm P Q).natDegree
      = P.natDegree + Q.natDegree - j := by
    have h2 := congrArg Polynomial.natDegree (EuclideanDomain.gcd_mul_lcm P Q)
    rw [Polynomial.natDegree_mul hgcd_ne hlcm_ne, Polynomial.natDegree_mul hP hQ,
      hgcdE_deg] at h2
    omega
  obtain ⟨c, hc⟩ := hlcmd
  have hcne : c ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hc
    exact mul_ne_zero hVne hQ hc
  have hcdeg : c.natDegree = 0 := by
    have h2 := congrArg Polynomial.natDegree hc
    rw [Polynomial.natDegree_mul hlcm_ne hcne, hdegM, hdeglcm] at h2
    omega
  have hcu : IsUnit c := by
    rw [Polynomial.eq_C_of_natDegree_eq_zero hcdeg, Polynomial.isUnit_C]
    exact isUnit_iff_ne_zero.mpr (fun h => hcne (by
      rw [Polynomial.eq_C_of_natDegree_eq_zero hcdeg, h, Polynomial.C_0]))
  obtain ⟨u, hu⟩ := hcu
  -- cancel `Q`: `sResV_{j-1} · gcdE = P · c`, with `c` a unit
  have hVg : Chapter8.sResV P Q (j - 1) * EuclideanDomain.gcd P Q = P * c := by
    apply mul_right_cancel₀ hQ
    calc Chapter8.sResV P Q (j - 1) * EuclideanDomain.gcd P Q * Q
        = EuclideanDomain.gcd P Q * EuclideanDomain.lcm P Q * c := by
          rw [show EuclideanDomain.gcd P Q * EuclideanDomain.lcm P Q * c
            = (EuclideanDomain.lcm P Q * c) * EuclideanDomain.gcd P Q from by ring,
            ← hc]
          ring
      _ = P * c * Q := by rw [EuclideanDomain.gcd_mul_lcm]; ring
  have h1 : Associated (Chapter8.sResV P Q (j - 1) * EuclideanDomain.gcd P Q) P := by
    rw [hVg, ← hu]
    exact ⟨u⁻¹, Units.mul_inv_cancel_right P u⟩
  exact ((Associated.refl _).mul_mul hgcdE).symm.trans h1

end Azurite.BPR
