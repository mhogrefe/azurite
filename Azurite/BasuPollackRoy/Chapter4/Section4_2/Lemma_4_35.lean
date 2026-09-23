/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.BasuPollackRoy.Chapter2.Section2_2.Lemma_2_60
import Azurite.BasuPollackRoy.Chapter2.Section2_3.FiberFormula

/-!
# BPR Lemma 4.35: the Cauchy index recursion

For `P` of degree `p` and `Q` of degree `q < p` over a real closed field, with
`R = Rem(P, Q) = P % Q`, BPR Lemma 4.35 states

  `Ind(Q/P) = Ind(−R/Q) + sign(a_p b_q)` if `p − q` is odd,
  `Ind(Q/P) = Ind(−R/Q)`                if `p − q` is even,

where `a_p`, `b_q` are the leading coefficients of `P`, `Q`.

This is BPR Lemma 2.60 (`Azurite.BPR.lemma_2_60`) specialized to the endpoints
`a = −∞`, `b = +∞`, where `Ind(·/·) = Ind(·/·; −∞, +∞)` is `cauchyIndex`:

* `σ(+∞) = sign(P(+∞) · Q(+∞)) = sign(a_p b_q)`;
* `σ(−∞) = sign((−1)^p a_p · (−1)^q b_q) = (−1)^{p+q} sign(a_p b_q)`;

so `σ(+∞) · σ(−∞) = (−1)^{p+q}`, which is `−1` exactly when `p − q` is odd, and
Lemma 2.60's `2·(Ind(Q/P) − Ind(−R/Q)) = σ(+∞) − σ(−∞)` reduces to the claim.
-/

open Polynomial

namespace Azurite.BPR.Chapter4

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]

/-- **BPR Lemma 4.35.** The Cauchy index recursion under Euclidean division:
with `R = P % Q`, `Ind(Q/P) = Ind(−R/Q) + [p − q odd] · sign(a_p b_q)`. -/
theorem lemma_4_35 (P Q : R[X]) (hP : P ≠ 0) (hQ : Q ≠ 0)
    (hpq : Q.natDegree < P.natDegree) :
    cauchyIndex Q P =
      cauchyIndex (-(P % Q)) Q +
        (if Odd (P.natDegree - Q.natDegree)
          then (SignType.sign (P.leadingCoeff * Q.leadingCoeff) : ℤ) else 0) := by
  -- nonzero hypotheses for Lemma 2.60 at the two infinities
  have hb : ExtendedPoint.evalPoly P .posInf * ExtendedPoint.evalPoly Q .posInf ≠ 0 :=
    mul_ne_zero (leadingCoeff_ne_zero.mpr hP) (leadingCoeff_ne_zero.mpr hQ)
  have ha : ExtendedPoint.evalPoly P .negInf * ExtendedPoint.evalPoly Q .negInf ≠ 0 :=
    mul_ne_zero
      (mul_ne_zero (pow_ne_zero _ (by norm_num)) (leadingCoeff_ne_zero.mpr hP))
      (mul_ne_zero (pow_ne_zero _ (by norm_num)) (leadingCoeff_ne_zero.mpr hQ))
  have key := lemma_2_60 hasIVP_of_isRealClosed P Q hP hQ
    ExtendedPoint.negInf ExtendedPoint.posInf (by trivial) ha hb
  -- σ at the two infinities
  have hsp : sigmaPQ P Q .posInf = (SignType.sign (P.leadingCoeff * Q.leadingCoeff) : ℤ) := rfl
  have hsn : sigmaPQ P Q .negInf
      = (-1 : ℤ) ^ (P.natDegree + Q.natDegree) *
          (SignType.sign (P.leadingCoeff * Q.leadingCoeff) : ℤ) := by
    have hev : ((-1 : R) ^ P.natDegree * P.leadingCoeff) *
          ((-1) ^ Q.natDegree * Q.leadingCoeff)
        = (-1) ^ (P.natDegree + Q.natDegree) * (P.leadingCoeff * Q.leadingCoeff) := by
      rw [pow_add]; ring
    show (SignType.sign (((-1) ^ P.natDegree * P.leadingCoeff) *
        ((-1) ^ Q.natDegree * Q.leadingCoeff)) : ℤ) = _
    rw [hev]
    rcases Nat.even_or_odd (P.natDegree + Q.natDegree) with he | ho
    · rw [he.neg_one_pow, one_mul, he.neg_one_pow, one_mul]
    · rw [ho.neg_one_pow, ho.neg_one_pow, neg_one_mul, neg_one_mul, Left.sign_neg]
      push_cast; ring
  rw [hsp, hsn] at key
  rw [cauchyIndex_eq_cauchyIndexOn_negInf_posInf, cauchyIndex_eq_cauchyIndexOn_negInf_posInf]
  rcases Nat.even_or_odd (P.natDegree - Q.natDegree) with hpar | hpar
  · -- p − q even: (−1)^{p+q} = 1, both σ agree, indices equal
    have hpe : Even (P.natDegree + Q.natDegree) := by
      rw [Nat.even_iff] at hpar ⊢; omega
    rw [hpe.neg_one_pow] at key
    rw [ite_eq_right (Nat.not_odd_iff_even.mpr hpar)]
    linarith [key]
  · -- p − q odd: (−1)^{p+q} = −1, σ flips, index gains sign(a_p b_q)
    have hpo : Odd (P.natDegree + Q.natDegree) := by
      rw [Nat.odd_iff] at hpar ⊢; omega
    rw [hpo.neg_one_pow] at key
    rw [ite_eq_left hpar]
    linarith [key]

end Azurite.BPR.Chapter4
