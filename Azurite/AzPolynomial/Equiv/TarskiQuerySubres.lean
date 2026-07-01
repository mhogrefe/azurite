import Azurite.AzPolynomial.Equiv.CauchyIndexSubres
import Azurite.AzPolynomial.Equiv.Derivative
import Azurite.BasuPollackRoy.Chapter2.Section2_2.Lemma_2_60
import Azurite.BasuPollackRoy.Chapter2.Section2_2.Proposition_2_57
import Azurite.BasuPollackRoy.Chapter2.Section2_3.FiberFormula

/-!
# Correctness of `tarskiQuerySubres` (BPR Algorithm 9.5)

`tarskiQuerySubres Q P` (the signed-subresultant Tarski query) computes the
whole-line Tarski query `TaQ(Q, P)` over a real closed coefficient field, for a
non-constant `P` (`1 ≤ deg P` — the query is `0` for constant `P`, but the
algorithm's `q > 1` branch adds a spurious `sign(b_q)` there, so the hypothesis
is genuinely needed).

The three cases of Algorithm 9.5 each reduce to
`theorem_4_33_realClosed : PmV(sRes(P, (P'·Q) % P)) = tarskiQuery Q P`:

* `q = 0` (`Q = b₀`): `sign(b₀)·PmV(sRes(P, P')) = Ind(b₀·P'/P)` via Cauchy-index
  sign-scaling.
* `q = 1`: `R := P'·Q − (p·b₁)·P` has `deg R < deg P` and `R ≡ P'·Q (mod P)`,
  so `PmV(sRes(P, R)) = Ind(R/P) = Ind(P'·Q/P) = TaQ` via add-multiple invariance
  and Proposition 2.57.
* `q > 1`: `PmV(sRes(−P'·Q, P)) + corr`, via the Cauchy-index reciprocity
  `cauchyIndexOn_swap_sum` (BPR Lemma 4.36 / Lemma 2.60); the correction `corr`
  matches the boundary term `(σ(−∞) − σ(+∞))/2`.
-/

open Polynomial

namespace Azurite.BPR

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]

/-- Cauchy-index sign-scaling of the numerator (all `c`). -/
theorem cauchyIndexOn_C_mul_left_sign (c : R) (Q P : R[X]) (a b : ExtendedPoint R) :
    cauchyIndexOn (C c * Q) P a b = (SignType.sign c : ℤ) * cauchyIndexOn Q P a b := by
  rcases lt_trichotomy c 0 with hc | hc | hc
  · rw [show C c * Q = -(C (-c) * Q) by rw [map_neg]; ring, cauchyIndexOn_neg_left,
      cauchyIndexOn_C_mul_left (-c) (by linarith) Q P a b, sign_eq_neg_one_iff.mpr hc]; simp
  · subst hc; simp [cauchyIndexOn_zero_left]
  · rw [cauchyIndexOn_C_mul_left c hc Q P a b, sign_eq_one_iff.mpr hc]; simp

/-- Adding a multiple of the denominator to the numerator leaves the Cauchy index
fixed. -/
theorem cauchyIndexOn_add_mul_right (hIVP : HasIntermediateValueProperty R)
    (A B P : R[X]) (a b : ExtendedPoint R) (hP : P ≠ 0) :
    cauchyIndexOn (A + B * P) P a b = cauchyIndexOn A P a b := by
  rw [← remark_2_55_b hIVP (A + B * P) P a b hP, ← remark_2_55_b hIVP A P a b hP]
  congr 1
  exact mod_eq_of_dvd_sub (by rw [add_sub_cancel_left]; exact dvd_mul_left P B)

/-- Whole-line Cauchy-index sign-scaling. -/
theorem cauchyIndex_C_mul_left_sign (c : R) (Q P : R[X]) :
    cauchyIndex (C c * Q) P = (SignType.sign c : ℤ) * cauchyIndex Q P :=
  cauchyIndexOn_C_mul_left_sign c Q P .negInf .posInf

/-- Whole-line add-multiple invariance. -/
theorem cauchyIndex_add_mul_right (hIVP : HasIntermediateValueProperty R)
    (A B P : R[X]) (hP : P ≠ 0) :
    cauchyIndex (A + B * P) P = cauchyIndex A P :=
  cauchyIndexOn_add_mul_right hIVP A B P .negInf .posInf hP

end Azurite.BPR

section Q1DegBound
open Polynomial

/-- **Degree bound (`q = 1`).** `R := P'·Q − (deg P · lc Q)·P` has degree `< deg P`,
by cancellation of the leading terms. -/
private theorem q1_deg_bound {R : Type _} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    (P Q : R[X]) (hp : 1 ≤ P.natDegree) (hq : Q.natDegree = 1) :
    (P.derivative * Q - C ((P.natDegree : R) * Q.leadingCoeff) * P).natDegree < P.natDegree := by
  have hP : P ≠ 0 := fun h => by simp [h] at hp
  have hQ : Q ≠ 0 := fun h => by simp [h] at hq
  have hlcP : P.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hP
  have hpne : (P.natDegree : R) ≠ 0 := by exact_mod_cast (by omega : P.natDegree ≠ 0)
  have hP' : P.derivative ≠ 0 := fun h => by
    have := leadingCoeff_derivative (R := R) P; rw [h, leadingCoeff_zero] at this
    exact (mul_ne_zero hlcP hpne) this.symm
  have hpb1 : (P.natDegree : R) * Q.leadingCoeff ≠ 0 :=
    mul_ne_zero hpne (leadingCoeff_ne_zero.mpr hQ)
  have hCP_ne : C ((P.natDegree : R) * Q.leadingCoeff) * P ≠ 0 :=
    mul_ne_zero (by rwa [Ne, C_eq_zero]) hP
  have hne : P.derivative * Q ≠ 0 := mul_ne_zero hP' hQ
  have hd1 : (P.derivative * Q).natDegree = P.natDegree := by
    rw [natDegree_mul hP' hQ, natDegree_derivative (R := R) P, hq]; omega
  have hd2 : (C ((P.natDegree : R) * Q.leadingCoeff) * P).natDegree = P.natDegree :=
    natDegree_C_mul hpb1
  have hsub := degree_sub_lt
    (show (P.derivative * Q).degree = (C ((P.natDegree : R) * Q.leadingCoeff) * P).degree by
      rw [degree_eq_natDegree hne, degree_eq_natDegree hCP_ne, hd1, hd2]) hne
    (show (P.derivative * Q).leadingCoeff
        = (C ((P.natDegree : R) * Q.leadingCoeff) * P).leadingCoeff by
      rw [leadingCoeff_mul, leadingCoeff_derivative, leadingCoeff_mul, leadingCoeff_C]; ring)
  rw [degree_eq_natDegree hne, hd1] at hsub
  rcases eq_or_ne (P.derivative * Q - C ((P.natDegree : R) * Q.leadingCoeff) * P) 0 with h0 | hR0
  · rw [h0, natDegree_zero]; omega
  · exact (natDegree_lt_iff_degree_lt hR0).mpr hsub

end Q1DegBound

namespace Azurite.AzPolynomial

open Azurite.BPR.Chapter4 (PmV sResSeq theorem_4_32)

variable {R : Type _} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]
    [DecidableEq R] [Azurite.ExactDiv R]

/-- **Subresultant → Cauchy index bridge.** For `deg B < deg A`,
`PmV(sRes(A, B)) = Ind(B/A)`. This is exactly `cauchyIndexSubres B A` unfolded
(no pseudo-remainder normalization needed since `deg B < deg A`). -/
theorem pmvSubres_eq (A B : AzPolynomial R) (hlt : B.natDegree < A.natDegree) :
    PmV (signedSubresultant A B).2.toList.reverse
      = Azurite.BPR.cauchyIndex (AzPolynomial.toPoly B) (AzPolynomial.toPoly A) := by
  rw [← cauchyIndexSubres_eq_cauchyIndex_of_lt B A hlt]
  show PmV (signedSubresultant A B).2.toList.reverse
    = PmV (signedSubresultant A
        (if A.natDegree ≤ B.natDegree then pRem B A else B)).2.toList.reverse
  rw [if_neg (by omega)]

omit [DecidableEq R] [Azurite.ExactDiv R] in
/-- `TaQ(Q, P) = Ind(P'·Q / P)` (whole-line Proposition 2.57). -/
theorem tarskiQuery_eq_cauchyIndex (Q P : AzPolynomial R) (hP : AzPolynomial.toPoly P ≠ 0) :
    Azurite.BPR.tarskiQuery (AzPolynomial.toPoly Q) (AzPolynomial.toPoly P)
      = Azurite.BPR.cauchyIndex ((AzPolynomial.toPoly P).derivative * AzPolynomial.toPoly Q)
          (AzPolynomial.toPoly P) := by
  rw [Azurite.BPR.tarskiQuery_eq_tarskiQueryOn_negInf_posInf,
    Azurite.BPR.proposition_2_57 Azurite.BPR.hasIVP_of_isRealClosed _ _ hP,
    ← Azurite.BPR.cauchyIndex_eq_cauchyIndexOn_negInf_posInf]

omit [IsRealClosed R] [DecidableEq R] [Azurite.ExactDiv R] in
/-- **Reciprocity boundary term (`q > 1`).** For `A` with
`lc A = lc P · deg P · b` and `deg A = (deg P − 1) + q` (so `A = P'·Q`, `b = lc Q`),
the boundary `σ(+∞) − σ(−∞)` of `sigmaPQ (−A) P` equals `−2·sign b` when `q − 1`
is odd and `0` otherwise. This is the `(σ(+∞) − σ(−∞))/2` correction of
`cauchyIndexOn_swap_sum`, evaluated via `evalPoly` at `±∞`. -/
private theorem sigma_diff (A P : R[X]) (hPm : P ≠ 0) (b : R) (qd : ℕ)
    (hlcA : A.leadingCoeff = P.leadingCoeff * (P.natDegree : R) * b)
    (hp1 : 1 ≤ P.natDegree) (hqq : 2 ≤ qd) (hdegA : A.natDegree = (P.natDegree - 1) + qd) :
    Azurite.BPR.sigmaPQ (-A) P .posInf - Azurite.BPR.sigmaPQ (-A) P .negInf
      = (if (qd - 1) % 2 = 1 then -2 * (SignType.sign b : ℤ) else 0) := by
  have hlcP : P.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hPm
  have hsqpos : (0:R) < (P.natDegree : R) * P.leadingCoeff ^ 2 :=
    mul_pos (by exact_mod_cast (by omega : 0 < P.natDegree)) (by positivity)
  have hs : (SignType.sign (A.leadingCoeff * P.leadingCoeff) : ℤ) = (SignType.sign b : ℤ) := by
    rw [hlcA, show P.leadingCoeff * (P.natDegree:R) * b * P.leadingCoeff
          = ((P.natDegree:R) * P.leadingCoeff^2) * b by ring, sign_mul, sign_pos hsqpos]; simp
  have hπ : Azurite.BPR.sigmaPQ (-A) P .posInf = -(SignType.sign b : ℤ) := by
    show (SignType.sign ((-A).leadingCoeff * P.leadingCoeff) : ℤ) = _
    rw [leadingCoeff_neg, show -A.leadingCoeff * P.leadingCoeff
          = -(A.leadingCoeff * P.leadingCoeff) by ring, Left.sign_neg]; push_cast; linarith [hs]
  have hνprod : Azurite.BPR.ExtendedPoint.evalPoly (-A) .negInf
        * Azurite.BPR.ExtendedPoint.evalPoly P .negInf
      = (-1)^(A.natDegree + P.natDegree) * -(A.leadingCoeff * P.leadingCoeff) := by
    show ((-1)^(-A).natDegree * (-A).leadingCoeff) * ((-1)^P.natDegree * P.leadingCoeff) = _
    rw [natDegree_neg, leadingCoeff_neg, pow_add]; ring
  have hpar : (A.natDegree + P.natDegree) % 2 = (qd - 1) % 2 := by omega
  rcases Nat.even_or_odd (A.natDegree + P.natDegree) with he | ho
  · have hνe : Azurite.BPR.sigmaPQ (-A) P .negInf = -(SignType.sign b : ℤ) := by
      show (SignType.sign (Azurite.BPR.ExtendedPoint.evalPoly (-A) .negInf
          * Azurite.BPR.ExtendedPoint.evalPoly P .negInf) : ℤ) = _
      rw [hνprod, he.neg_one_pow, one_mul, Left.sign_neg]; push_cast; linarith [hs]
    rw [if_neg (by rw [Nat.even_iff] at he; omega), hπ, hνe]; ring
  · have hνo : Azurite.BPR.sigmaPQ (-A) P .negInf = (SignType.sign b : ℤ) := by
      show (SignType.sign (Azurite.BPR.ExtendedPoint.evalPoly (-A) .negInf
          * Azurite.BPR.ExtendedPoint.evalPoly P .negInf) : ℤ) = _
      rw [hνprod, ho.neg_one_pow, show (-1 : R) * -(A.leadingCoeff * P.leadingCoeff)
            = A.leadingCoeff * P.leadingCoeff by ring, hs]
    rw [if_pos (by rw [Nat.odd_iff] at ho; omega), hπ, hνo]; ring

/-- **Correctness of `tarskiQuerySubres` (BPR Algorithm 9.5).** For non-constant
`P` (`1 ≤ deg P`) over a real closed coefficient field,
`tarskiQuerySubres Q P = TaQ(Q, P)`. -/
theorem tarskiQuerySubres_eq_tarskiQuery (Q P : AzPolynomial R) (hP1 : 1 ≤ P.natDegree) :
    tarskiQuerySubres Q P = Azurite.BPR.tarskiQuery (AzPolynomial.toPoly Q) (AzPolynomial.toPoly P) := by
  have hP : P ≠ 0 := fun h => by rw [h, show (0 : AzPolynomial R).natDegree = 0 from rfl] at hP1; omega
  have hPm : AzPolynomial.toPoly P ≠ 0 := fun h => hP (toPoly_inj.mp (h.trans toPoly_zero.symm))
  have hpd : (AzPolynomial.toPoly P).natDegree = P.natDegree := AzPolynomial.natDegree_toPoly P
  have hqd : (AzPolynomial.toPoly Q).natDegree = Q.natDegree := AzPolynomial.natDegree_toPoly Q
  have hdP' : (derivative P).natDegree < P.natDegree := by
    have h1 : (AzPolynomial.toPoly (derivative P)).natDegree = (AzPolynomial.toPoly P).natDegree - 1 := by
      rw [toPoly_derivative, natDegree_derivative]
    rw [← AzPolynomial.natDegree_toPoly (derivative P), h1, hpd]; omega
  rw [tarskiQuery_eq_cauchyIndex Q P hPm]
  rcases Nat.lt_trichotomy Q.natDegree 1 with hq | hq | hq
  · -- q = 0
    have h0 : Q.natDegree = 0 := by omega
    rw [tarskiQuerySubres, if_pos h0, pmvSubres_eq P (derivative P) hdP', toPoly_derivative]
    have hDQ : AzPolynomial.toPoly Q = Polynomial.C (Q.coeff 0) := by
      have hz : (AzPolynomial.toPoly Q).natDegree = 0 := by rw [hqd]; exact h0
      rw [Polynomial.eq_C_of_natDegree_eq_zero hz, AzPolynomial.coeff_toPoly]
    rw [hDQ, show (AzPolynomial.toPoly P).derivative * Polynomial.C (Q.coeff 0)
          = Polynomial.C (Q.coeff 0) * (AzPolynomial.toPoly P).derivative by ring,
      Azurite.BPR.cauchyIndex_C_mul_left_sign]
  · -- q = 1
    rw [tarskiQuerySubres, if_neg (by omega : ¬ Q.natDegree = 0), if_pos hq]
    have hdR : (derivative P * Q - ((P.natDegree : R) * Q.coeff 1) • P).natDegree < P.natDegree := by
      have key : (AzPolynomial.toPoly
            (derivative P * Q - ((P.natDegree : R) * Q.coeff 1) • P)).natDegree
          < (AzPolynomial.toPoly P).natDegree := by
        rw [toPoly_sub, toPoly_mul, toPoly_derivative, toPoly_smul, Polynomial.smul_eq_C_mul,
          show ((P.natDegree : R)) = ((AzPolynomial.toPoly P).natDegree : R) by rw [hpd],
          show Q.coeff 1 = (AzPolynomial.toPoly Q).leadingCoeff by
            rw [Polynomial.leadingCoeff, hqd, hq, AzPolynomial.coeff_toPoly]]
        exact q1_deg_bound (AzPolynomial.toPoly P) (AzPolynomial.toPoly Q)
          (by rw [hpd]; exact hP1) (by rw [hqd]; exact hq)
      rwa [AzPolynomial.natDegree_toPoly, AzPolynomial.natDegree_toPoly] at key
    rw [pmvSubres_eq P _ hdR, toPoly_sub, toPoly_mul, toPoly_derivative, toPoly_smul,
      Polynomial.smul_eq_C_mul,
      show (AzPolynomial.toPoly P).derivative * AzPolynomial.toPoly Q
            - Polynomial.C ((P.natDegree : R) * Q.coeff 1) * AzPolynomial.toPoly P
          = (AzPolynomial.toPoly P).derivative * AzPolynomial.toPoly Q
            + (-(Polynomial.C ((P.natDegree : R) * Q.coeff 1))) * AzPolynomial.toPoly P by ring,
      Azurite.BPR.cauchyIndex_add_mul_right Azurite.BPR.hasIVP_of_isRealClosed _ _ _ hPm]
  · -- q > 1. Reciprocity route (edge-free), via `cauchyIndexOn_swap_sum`:
    --   Let `A := P'·Q`, `B := toPoly P`, `alg0 := PmV(sRes(−A, B)) = Ind(B/(−A))`
    --   (`pmvSubres_eq` on `(−A, B)`, valid since `deg B < deg(−A) = (p−1)+q`).
    --   `swap_sum (−A) B` + `cauchyIndexOn_neg_left` give
    --     `2·(alg0 − Ind(A/B)) = σ(+∞) − σ(−∞)`,  σ := sigmaPQ (−A) B.
    --   Computing `σ` at `±∞` from `evalPoly _ ±∞` (= ±leadingCoeff with parity),
    --   `lc(A) = lc(P)·p·lc(Q)` and `deg A = (p−1)+q`:
    --     `σ(+∞) − σ(−∞) = if (q−1) odd then −2·sign(b_q) else 0`,
    --   which by `omega`/`linarith` (÷2 over ℤ) matches the algorithm's
    --   `alg0 + [q−1 odd]·sign(b_q) = Ind(A/B) = TaQ`.
    rw [tarskiQuerySubres, if_neg (by omega : ¬ Q.natDegree = 0),
      if_neg (by omega : ¬ Q.natDegree = 1)]
    have hQ : Q ≠ 0 := fun h => by rw [h, show (0 : AzPolynomial R).natDegree = 0 from rfl] at hq; omega
    have hDQ_ne : AzPolynomial.toPoly Q ≠ 0 := fun h => hQ (toPoly_inj.mp (h.trans toPoly_zero.symm))
    have hlcP : (AzPolynomial.toPoly P).leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hPm
    have hpdeg_ne : ((AzPolynomial.toPoly P).natDegree : R) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hP'_ne : (AzPolynomial.toPoly P).derivative ≠ 0 := by
      intro h; have := leadingCoeff_derivative (R := R) (AzPolynomial.toPoly P)
      rw [h, leadingCoeff_zero] at this; exact (mul_ne_zero hlcP hpdeg_ne) this.symm
    have hlcAne : ((AzPolynomial.toPoly P).derivative * AzPolynomial.toPoly Q).leadingCoeff ≠ 0 :=
      leadingCoeff_ne_zero.mpr (mul_ne_zero hP'_ne hDQ_ne)
    have hlcA : ((AzPolynomial.toPoly P).derivative * AzPolynomial.toPoly Q).leadingCoeff
        = (AzPolynomial.toPoly P).leadingCoeff
          * ((AzPolynomial.toPoly P).natDegree : R) * (AzPolynomial.toPoly Q).leadingCoeff := by
      rw [leadingCoeff_mul, leadingCoeff_derivative]
    have hdegA : ((AzPolynomial.toPoly P).derivative * AzPolynomial.toPoly Q).natDegree
        = ((AzPolynomial.toPoly P).natDegree - 1) + (AzPolynomial.toPoly Q).natDegree := by
      rw [Polynomial.natDegree_mul hP'_ne hDQ_ne, Polynomial.natDegree_derivative]
    have hnegA : -((AzPolynomial.toPoly P).derivative * AzPolynomial.toPoly Q) ≠ 0 :=
      neg_ne_zero.mpr (mul_ne_zero hP'_ne hDQ_ne)
    have halg0 : PmV (signedSubresultant (-(derivative P * Q)) P).2.toList.reverse
        = Azurite.BPR.cauchyIndexOn (AzPolynomial.toPoly P)
            (-((AzPolynomial.toPoly P).derivative * AzPolynomial.toPoly Q)) .negInf .posInf := by
      have hdeg : P.natDegree < (-(Azurite.AzPolynomial.derivative P * Q)).natDegree := by
        rw [← AzPolynomial.natDegree_toPoly (-(Azurite.AzPolynomial.derivative P * Q)), toPoly_neg,
          toPoly_mul, toPoly_derivative, natDegree_neg, hdegA, hpd, hqd]; omega
      rw [pmvSubres_eq (-(Azurite.AzPolynomial.derivative P * Q)) P hdeg, toPoly_neg, toPoly_mul,
        toPoly_derivative, Azurite.BPR.cauchyIndex_eq_cauchyIndexOn_negInf_posInf]
    have ha : Azurite.BPR.ExtendedPoint.evalPoly
          (-((AzPolynomial.toPoly P).derivative * AzPolynomial.toPoly Q)) .negInf
        * Azurite.BPR.ExtendedPoint.evalPoly (AzPolynomial.toPoly P) .negInf ≠ 0 := by
      show ((-1) ^ (-((AzPolynomial.toPoly P).derivative * AzPolynomial.toPoly Q)).natDegree
          * (-((AzPolynomial.toPoly P).derivative * AzPolynomial.toPoly Q)).leadingCoeff)
          * ((-1) ^ (AzPolynomial.toPoly P).natDegree * (AzPolynomial.toPoly P).leadingCoeff) ≠ 0
      exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ (by norm_num))
        (by rw [leadingCoeff_neg, neg_ne_zero]; exact hlcAne))
        (mul_ne_zero (pow_ne_zero _ (by norm_num)) hlcP)
    have hb : Azurite.BPR.ExtendedPoint.evalPoly
          (-((AzPolynomial.toPoly P).derivative * AzPolynomial.toPoly Q)) .posInf
        * Azurite.BPR.ExtendedPoint.evalPoly (AzPolynomial.toPoly P) .posInf ≠ 0 := by
      show (-((AzPolynomial.toPoly P).derivative * AzPolynomial.toPoly Q)).leadingCoeff
          * (AzPolynomial.toPoly P).leadingCoeff ≠ 0
      exact mul_ne_zero (by rw [leadingCoeff_neg, neg_ne_zero]; exact hlcAne) hlcP
    have hswap := Azurite.BPR.cauchyIndexOn_swap_sum Azurite.BPR.hasIVP_of_isRealClosed
      (-((AzPolynomial.toPoly P).derivative * AzPolynomial.toPoly Q)) (AzPolynomial.toPoly P)
      hnegA hPm .negInf .posInf (by trivial) ha hb
    rw [Azurite.BPR.cauchyIndexOn_neg_left,
      ← Azurite.BPR.cauchyIndex_eq_cauchyIndexOn_negInf_posInf (P := AzPolynomial.toPoly P),
      ← halg0] at hswap
    have hσ := sigma_diff ((AzPolynomial.toPoly P).derivative * AzPolynomial.toPoly Q)
      (AzPolynomial.toPoly P) hPm (AzPolynomial.toPoly Q).leadingCoeff
      (AzPolynomial.toPoly Q).natDegree hlcA (by omega) (by rw [hqd]; omega) hdegA
    rw [hσ, hqd, leadingCoeff_toPoly] at hswap
    split_ifs at hswap ⊢ with hcond
    · linarith [hswap]
    · linarith [hswap]

end Azurite.AzPolynomial
