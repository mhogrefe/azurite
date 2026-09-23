import Azurite.BasuPollackRoy.Chapter8.Section8_3.Proposition_8_39
import Azurite.BasuPollackRoy.Chapter4.Section4_2.Proposition_4_26

/-!
# BPR Theorem 8.34 (Structure Theorem for Signed Subresultants) — inductive part

The base case (`q < j ≤ p`) is `sResP_natDegree_sub_one_rem` in `Proposition_8_39`.
The remainder of the proof of Theorem 8.34 is an induction on the length of the signed
remainder sequence of `P, Q`: the theorem for `P, Q` is reduced to the theorem for
`Q, -R` (where `R = P % Q`), using:

* for `j ≤ r := deg R`, proportionality of `sResP_j(P,Q)` and `sResP_j(Q,-R)` with factor
  `ε_{p-q} b_q^{p-r}` — this is `proposition_8_39` (for `j < q-1`);
* the boundary relation `sResP_{q-1}(P,Q) = ε_{p-q} b_q^{p-q+1} · sResP_{q-1}(Q,-R)`
  (this file, `sResP_natDegree_sub_one_propto`), which feeds the "`sResP_{q-1}(P,Q)` is
  proportional to `sResP_{q-1}(Q,-R)`" fact of the inductive step.

This file develops the reusable bridge lemmas between the `P,Q`- and `Q,-R`-subresultants.
-/

namespace Azurite.BPR.Chapter8

open Polynomial
open Azurite.BPR.Chapter4 (ε)

variable {K : Type*} [Field K]

/-- `sResP_{p-1}(P,Q) = Q` for **all** `q < p` (not just `q+1 < p`): defective top via the
    `sResP_{p-1} =` (second argument) convention, non-defective top (`q = p-1`) via the
    closing-note value `ε₁ b⁰ Q = Q`. -/
theorem sResP_pm1_eq_Q (P Q : K[X]) (hQ : Q ≠ 0) (hpq : Q.natDegree < P.natDegree) :
    sResP P Q (P.natDegree - 1) = Q := by
  rcases eq_or_lt_of_le (Nat.succ_le_of_lt hpq) with h | h
  · have hpq1 : P.natDegree - 1 = Q.natDegree := by omega
    rw [hpq1, sResP_eq_of_natDegree P Q hpq hQ,
      show P.natDegree - Q.natDegree = 1 from by omega]
    simp [Azurite.BPR.Chapter4.ε]
  · exact sResP_eq_self_Q P Q h

/-- **Extended base case** (`q < p`, including the non-defective top `q = p-1`):
    `sResP_{q-1}(P,Q) = -Rem(s_q · t_{p-1} · P, Q)`. -/
theorem sResP_natDegree_sub_one_rem' (P Q : K[X]) (hQ : Q ≠ 0) (hR0 : P % Q ≠ 0)
    (hpq : Q.natDegree < P.natDegree) (hq1 : 1 ≤ Q.natDegree) :
    sResP P Q (Q.natDegree - 1)
      = -((C (Azurite.BPR.Chapter4.sRes P Q Q.natDegree)
            * C (sResP P Q (P.natDegree - 1)).leadingCoeff
            * sResP P Q P.natDegree) % sResP P Q (P.natDegree - 1)) := by
  rw [sResP_natDegree_sub_one P Q hQ hR0 hpq hq1, sResP_pm1_eq_Q P Q hQ hpq,
    sResP_eq_self P Q hpq, sRes_natDegree P Q hpq hQ, ← C_mul, rem_C_mul]
  congr 1
  rw [smul_eq_C_mul, zsmul_eq_mul, zsmul_eq_mul, ← C_eq_intCast, pow_succ, C_mul, C_mul, C_mul]
  ring

/-- Scaling the divisor by a nonzero constant does not change the remainder:
    `A % (C c * B) = A % B` for `c ≠ 0` (`C c` is a unit). -/
theorem mod_C_mul_right (A B : K[X]) {c : K} (hc : c ≠ 0) : A % (C c * B) = A % B := by
  rcases eq_or_ne B 0 with rfl | hB
  · simp
  have hCB : C c * B ≠ 0 := mul_ne_zero (by simpa using hc) hB
  have hdeg : (A % B).degree < (C c * B).degree := by
    rw [degree_mul, degree_C hc, zero_add]; exact degree_mod_lt A hB
  have hdvd : (C c * B) ∣ (B * (A / B)) :=
    ⟨C c⁻¹ * (A / B), by rw [mul_mul_mul_comm, ← C_mul, mul_inv_cancel₀ hc, map_one, one_mul]⟩
  conv_lhs => rw [← EuclideanDomain.div_add_mod A B]
  rw [Polynomial.add_mod, EuclideanDomain.mod_eq_zero.mpr hdvd, zero_add,
    (mod_eq_self_iff hCB).mpr hdeg]

/-- Combined remainder scaling: `(α • A) % (β • B) = α • (A % B)` for `β ≠ 0`. -/
theorem mod_smul_smul (A B : K[X]) (α : K) {β : K} (hβ : β ≠ 0) :
    (α • A) % (β • B) = α • (A % B) := by
  rw [smul_eq_C_mul α, smul_eq_C_mul β, mod_C_mul_right (C α * A) B hβ, rem_C_mul,
    ← smul_eq_C_mul]

/-- `Chapter4.sRes Q (-R) Q.natDegree = Q.leadingCoeff` (BPR's `s'_q`; the top-index
    signed subresultant of the first polynomial is its leading coefficient). -/
theorem sRes_top_eq_leadingCoeff (P Q : K[X]) (hqp : Q.natDegree < P.natDegree) :
    Azurite.BPR.Chapter4.sRes P Q P.natDegree = P.leadingCoeff := by
  rw [Azurite.BPR.Chapter4.sRes, ite_eq_right (by omega), ite_eq_left hqp, ite_eq_left rfl]

/-- **Boundary value for the swapped pair.** For `R ≠ 0` with `deg R < deg Q`, the
    `(q-1)`-st signed subresultant of `Q, -R` is `-R`: it is `-R` by the
    `sResP_{p-1} = ` (second argument) convention when `deg R < q-1`, and by the
    closing-note value (`ε₁ b^0 (-R) = -R`) when `deg R = q-1`. -/
theorem sResP_negR_natDegree_sub_one (Q R : K[X]) (hR0 : R ≠ 0)
    (hrq : R.natDegree < Q.natDegree) :
    sResP Q (-R) (Q.natDegree - 1) = -R := by
  have hneg : (-R).natDegree = R.natDegree := natDegree_neg R
  rcases eq_or_lt_of_le (Nat.le_sub_one_of_lt hrq) with heq | hlt
  · -- `R.natDegree = Q.natDegree - 1`: closing-note region.
    rw [← heq, ← hneg,
      sResP_eq_of_natDegree Q (-R) (by rw [hneg]; exact hrq) (neg_ne_zero.mpr hR0)]
    have h1 : Q.natDegree - (-R).natDegree = 1 := by rw [hneg]; omega
    rw [h1]
    simp [Azurite.BPR.Chapter4.ε]
  · -- `R.natDegree < Q.natDegree - 1`: `sResP_{p-1} = ` second-argument convention.
    exact sResP_eq_self_Q Q (-R) (by rw [hneg]; omega)

/-- **Boundary proportionality (inductive step).**
    `sResP_{q-1}(P,Q) = ε_{p-q} b_q^{p-q+1} · sResP_{q-1}(Q,-R)`, with `R = P % Q`.
    The two sides are `±` of the base-case value `ε_{p-q} b_q^{p-q+1} R`. -/
theorem sResP_natDegree_sub_one_propto (P Q : K[X]) (hQ : Q ≠ 0) (hR0 : P % Q ≠ 0)
    (hpq : Q.natDegree < P.natDegree) (hq1 : 1 ≤ Q.natDegree) :
    sResP P Q (Q.natDegree - 1)
      = (ε (P.natDegree - Q.natDegree) : ℤ)
        • (Q.leadingCoeff ^ (P.natDegree - Q.natDegree + 1)
            • sResP Q (-(P % Q)) (Q.natDegree - 1)) := by
  have hrq : (P % Q).natDegree < Q.natDegree :=
    natDegree_lt_natDegree hR0 (degree_mod_lt P hQ)
  rw [sResP_natDegree_sub_one P Q hQ hR0 hpq hq1,
    sResP_negR_natDegree_sub_one Q (P % Q) hR0 hrq, smul_neg]
  exact (smul_neg _ _).symm

/-- **Unified `j ≤ r` proportionality (BPR's first half of the inductive step).**
    For `j ≤ r := deg(P % Q)`, the `P,Q`- and `Q,-R`-subresultants are proportional with
    factor `ε_{p-q} b_q^{p-r}`. This subsumes `proposition_8_39` (`j < q-1`) and the
    boundary case `j = q-1` (which forces `r = q-1`, via `sResP_natDegree_sub_one_propto`). -/
theorem sResP_propto_le_r (P Q : K[X]) (hQ : Q ≠ 0) (hR0 : P % Q ≠ 0)
    (hpq : Q.natDegree < P.natDegree) {j : ℕ} (hj : j ≤ (P % Q).natDegree) :
    sResP P Q j
      = (ε (P.natDegree - Q.natDegree) : ℤ)
        • (Q.leadingCoeff ^ (P.natDegree - (P % Q).natDegree) • sResP Q (-(P % Q)) j) := by
  have hrq : (P % Q).natDegree < Q.natDegree :=
    natDegree_lt_natDegree hR0 (degree_mod_lt P hQ)
  rcases lt_or_ge j (Q.natDegree - 1) with hlt | hge
  · exact proposition_8_39 P Q hQ hR0 hpq j hlt
  · -- `q-1 ≤ j ≤ r < q` forces `j = r = q-1`.
    have hjeq : j = Q.natDegree - 1 := by omega
    have hreq : (P % Q).natDegree = Q.natDegree - 1 := by omega
    subst hjeq
    rw [sResP_natDegree_sub_one_propto P Q hQ hR0 hpq (by omega),
      show P.natDegree - (P % Q).natDegree = P.natDegree - Q.natDegree + 1 from by omega]

/-- **Bridge `t_{q-1} = ε_{p-q} b_q^{p-q+1} t'_{q-1}`** (leading coefficients of the
    boundary proportionality `sResP_natDegree_sub_one_propto`). Here `t'_{q-1}` is the
    leading coefficient of `sResP_{q-1}(Q,-R)`. -/
theorem leadingCoeff_sResP_natDegree_sub_one_swap (P Q : K[X]) (hQ : Q ≠ 0) (hR0 : P % Q ≠ 0)
    (hpq : Q.natDegree < P.natDegree) (hq1 : 1 ≤ Q.natDegree) :
    (sResP P Q (Q.natDegree - 1)).leadingCoeff
      = (ε (P.natDegree - Q.natDegree) : ℤ)
        • (Q.leadingCoeff ^ (P.natDegree - Q.natDegree + 1)
            • (sResP Q (-(P % Q)) (Q.natDegree - 1)).leadingCoeff) := by
  have hεK : IsUnit ((ε (P.natDegree - Q.natDegree) : ℤ) : K) := by
    rw [Azurite.BPR.Chapter4.ε]; push_cast; exact (isUnit_one.neg).pow _
  have hbu : IsUnit (Q.leadingCoeff ^ (P.natDegree - Q.natDegree + 1)) :=
    isUnit_iff_ne_zero.mpr (pow_ne_zero _ (leadingCoeff_ne_zero.mpr hQ))
  rw [sResP_natDegree_sub_one_propto P Q hQ hR0 hpq hq1]
  simp only [← Int.cast_smul_eq_zsmul K]
  rw [leadingCoeff_smul_of_smul_regular _ (hεK.isSMulRegular K),
    leadingCoeff_smul_of_smul_regular _ (hbu.isSMulRegular K)]

/-- **Transport of `t_j = lcof(sResP_j)` across a Euclidean step**, for interior indices
    `j < q-1`: `t_j(P,Q) = ε_{p-q} b_q^{p-r} t_j(Q,-R)` (leading coefficients of the `j ≤ r`
    proportionality, Proposition 8.39). -/
theorem leadingCoeff_sResP_swap (P Q : K[X]) (hQ : Q ≠ 0) (hR0 : P % Q ≠ 0)
    (hpq : Q.natDegree < P.natDegree) {j : ℕ} (hj : j < Q.natDegree - 1) :
    (sResP P Q j).leadingCoeff
      = (ε (P.natDegree - Q.natDegree) : ℤ)
        • (Q.leadingCoeff ^ (P.natDegree - (P % Q).natDegree)
            • (sResP Q (-(P % Q)) j).leadingCoeff) := by
  have hεK : IsUnit ((ε (P.natDegree - Q.natDegree) : ℤ) : K) := by
    rw [Azurite.BPR.Chapter4.ε]; push_cast; exact (isUnit_one.neg).pow _
  have hbu : IsUnit (Q.leadingCoeff ^ (P.natDegree - (P % Q).natDegree)) :=
    isUnit_iff_ne_zero.mpr (pow_ne_zero _ (leadingCoeff_ne_zero.mpr hQ))
  rw [proposition_8_39 P Q hQ hR0 hpq j hj]
  simp only [← Int.cast_smul_eq_zsmul K]
  rw [leadingCoeff_smul_of_smul_regular _ (hεK.isSMulRegular K),
    leadingCoeff_smul_of_smul_regular _ (hbu.isSMulRegular K)]

/-- **Bridge `s_r = ε_{p-q} b_q^{p-r} s'_r`** (coefficient at `X^r` of the `j ≤ r`
    proportionality `sResP_propto_le_r`, at `j = r := deg(P % Q)`). Here `s'_r` is
    `sRes_r(Q,-R)`. -/
theorem sRes_swap_natDegree_mod (P Q : K[X]) (hQ : Q ≠ 0) (hR0 : P % Q ≠ 0)
    (hpq : Q.natDegree < P.natDegree) :
    Azurite.BPR.Chapter4.sRes P Q (P % Q).natDegree
      = (ε (P.natDegree - Q.natDegree) : ℤ)
        • (Q.leadingCoeff ^ (P.natDegree - (P % Q).natDegree)
            • Azurite.BPR.Chapter4.sRes Q (-(P % Q)) (P % Q).natDegree) := by
  have hrq : (P % Q).natDegree < Q.natDegree :=
    natDegree_lt_natDegree hR0 (degree_mod_lt P hQ)
  rw [← coeff_sResP P Q hpq (by omega), sResP_propto_le_r P Q hQ hR0 hpq (le_refl _)]
  simp only [← Int.cast_smul_eq_zsmul K]
  rw [Polynomial.coeff_smul, Polynomial.coeff_smul,
    coeff_sResP Q (-(P % Q)) (by rw [natDegree_neg]; exact hrq) (le_of_lt hrq)]

/-- **Theorem 8.34, inductive-step identity (generic case `r < j ≤ q`).**
    `s_q · t_{p-1} · sResP_{r-1}(P,Q) = -Rem(s_r · t_{q-1} · sResP_{p-1}(P,Q), sResP_{q-1}(P,Q))`,
    with `R = P % Q`, `r = deg R`. Both sides equal `b_q^{2p-q-r+1} · sResP_{r-1}(Q,-R)`. -/
theorem sResP_inductive_step_identity (P Q : K[X]) (hQ : Q ≠ 0) (hR0 : P % Q ≠ 0)
    (hpq : Q.natDegree < P.natDegree)
    (hr1 : 1 ≤ (P % Q).natDegree)
    (hR'0 : Q % (-(P % Q)) ≠ 0) :
    C (Azurite.BPR.Chapter4.sRes P Q Q.natDegree)
        * C (sResP P Q (P.natDegree - 1)).leadingCoeff
        * sResP P Q ((P % Q).natDegree - 1)
      = -((C (Azurite.BPR.Chapter4.sRes P Q (P % Q).natDegree)
            * C (sResP P Q (Q.natDegree - 1)).leadingCoeff
            * sResP P Q (P.natDegree - 1)) % sResP P Q (Q.natDegree - 1)) := by
  have hb : Q.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hQ
  have hpq' : Q.natDegree < P.natDegree := hpq
  have hrq : (P % Q).natDegree < Q.natDegree :=
    natDegree_lt_natDegree hR0 (degree_mod_lt P hQ)
  have he : ((ε (P.natDegree - Q.natDegree) : ℤ) : K)
      * ((ε (P.natDegree - Q.natDegree) : ℤ) : K) = 1 := by
    rw [← Int.cast_mul, Azurite.BPR.Chapter4.ε, ← pow_add,
      Even.neg_one_pow ⟨_, rfl⟩, Int.cast_one]
  have hsq : Azurite.BPR.Chapter4.sRes P Q Q.natDegree
      = ((ε (P.natDegree - Q.natDegree) : ℤ) : K)
        * Q.leadingCoeff ^ (P.natDegree - Q.natDegree) := by
    rw [sRes_natDegree P Q hpq' hQ, ← Int.cast_smul_eq_zsmul K, smul_eq_mul]
  -- LHS reduces to `b^{2p-q-r+1} • sResP_{r-1}(Q,-R)`.
  have hLHS : C (Azurite.BPR.Chapter4.sRes P Q Q.natDegree)
        * C (sResP P Q (P.natDegree - 1)).leadingCoeff
        * sResP P Q ((P % Q).natDegree - 1)
      = Q.leadingCoeff ^ (2 * P.natDegree - Q.natDegree - (P % Q).natDegree + 1)
          • sResP Q (-(P % Q)) ((P % Q).natDegree - 1) := by
    rw [sResP_pm1_eq_Q P Q hQ hpq, hsq,
      sResP_propto_le_r P Q hQ hR0 hpq' (show (P % Q).natDegree - 1 ≤ (P % Q).natDegree from by omega),
      ← Int.cast_smul_eq_zsmul K, ← C_mul, ← smul_eq_C_mul, smul_smul, smul_smul]
    congr 1
    have hrw : ((ε (P.natDegree - Q.natDegree) : ℤ) : K) * Q.leadingCoeff ^ (P.natDegree - Q.natDegree)
          * Q.leadingCoeff * ((ε (P.natDegree - Q.natDegree) : ℤ) : K)
          * Q.leadingCoeff ^ (P.natDegree - (P % Q).natDegree)
        = (((ε (P.natDegree - Q.natDegree) : ℤ) : K) * ((ε (P.natDegree - Q.natDegree) : ℤ) : K))
          * (Q.leadingCoeff ^ (P.natDegree - Q.natDegree) * Q.leadingCoeff
              * Q.leadingCoeff ^ (P.natDegree - (P % Q).natDegree)) := by ring
    rw [hrw, he, one_mul, ← pow_succ, ← pow_add]
    congr 1
    omega
  have hRHS : -((C (Azurite.BPR.Chapter4.sRes P Q (P % Q).natDegree)
            * C (sResP P Q (Q.natDegree - 1)).leadingCoeff
            * sResP P Q (P.natDegree - 1)) % sResP P Q (Q.natDegree - 1))
      = Q.leadingCoeff ^ (2 * P.natDegree - Q.natDegree - (P % Q).natDegree + 1)
          • sResP Q (-(P % Q)) ((P % Q).natDegree - 1) := by
    rw [sResP_pm1_eq_Q P Q hQ hpq, sRes_swap_natDegree_mod P Q hQ hR0 hpq',
      leadingCoeff_sResP_natDegree_sub_one_swap P Q hQ hR0 hpq' (by omega),
      sResP_natDegree_sub_one_propto P Q hQ hR0 hpq' (by omega)]
    simp only [← Int.cast_smul_eq_zsmul K, smul_eq_mul]
    rw [← C_mul, ← smul_eq_C_mul, smul_smul]
    have hεne : ((ε (P.natDegree - Q.natDegree) : ℤ) : K) ≠ 0 :=
      left_ne_zero_of_mul_eq_one he
    rw [mod_smul_smul Q (sResP Q (-(P % Q)) (Q.natDegree - 1)) _
      (mul_ne_zero hεne (pow_ne_zero (P.natDegree - Q.natDegree + 1) hb))]
    have hbase := sResP_natDegree_sub_one_rem' Q (-(P % Q)) (neg_ne_zero.mpr hR0) hR'0
      (by rw [natDegree_neg]; exact hrq) (by rw [natDegree_neg]; exact hr1)
    rw [natDegree_neg, sResP_eq_self Q (-(P % Q)) (by rw [natDegree_neg]; omega),
      ← C_mul, rem_C_mul, ← smul_eq_C_mul] at hbase
    have hα : ((ε (P.natDegree - Q.natDegree) : ℤ) : K)
          * (Q.leadingCoeff ^ (P.natDegree - (P % Q).natDegree)
              * Azurite.BPR.Chapter4.sRes Q (-(P % Q)) (P % Q).natDegree)
          * (((ε (P.natDegree - Q.natDegree) : ℤ) : K)
              * (Q.leadingCoeff ^ (P.natDegree - Q.natDegree + 1)
                  * (sResP Q (-(P % Q)) (Q.natDegree - 1)).leadingCoeff))
        = Q.leadingCoeff ^ (2 * P.natDegree - Q.natDegree - (P % Q).natDegree + 1)
          * (Azurite.BPR.Chapter4.sRes Q (-(P % Q)) (P % Q).natDegree
              * (sResP Q (-(P % Q)) (Q.natDegree - 1)).leadingCoeff) := by
      have h1 : ((ε (P.natDegree - Q.natDegree) : ℤ) : K)
            * (Q.leadingCoeff ^ (P.natDegree - (P % Q).natDegree)
                * Azurite.BPR.Chapter4.sRes Q (-(P % Q)) (P % Q).natDegree)
            * (((ε (P.natDegree - Q.natDegree) : ℤ) : K)
                * (Q.leadingCoeff ^ (P.natDegree - Q.natDegree + 1)
                    * (sResP Q (-(P % Q)) (Q.natDegree - 1)).leadingCoeff))
          = (((ε (P.natDegree - Q.natDegree) : ℤ) : K) * ((ε (P.natDegree - Q.natDegree) : ℤ) : K))
            * ((Q.leadingCoeff ^ (P.natDegree - (P % Q).natDegree)
                * Q.leadingCoeff ^ (P.natDegree - Q.natDegree + 1))
              * (Azurite.BPR.Chapter4.sRes Q (-(P % Q)) (P % Q).natDegree
                  * (sResP Q (-(P % Q)) (Q.natDegree - 1)).leadingCoeff)) := by ring
      rw [h1, he, one_mul, ← pow_add,
        show (P.natDegree - (P % Q).natDegree) + (P.natDegree - Q.natDegree + 1)
          = 2 * P.natDegree - Q.natDegree - (P % Q).natDegree + 1 from by omega]
    have hkey : (Azurite.BPR.Chapter4.sRes Q (-(P % Q)) (P % Q).natDegree
          * (sResP Q (-(P % Q)) (Q.natDegree - 1)).leadingCoeff)
          • (Q % sResP Q (-(P % Q)) (Q.natDegree - 1))
        = -(sResP Q (-(P % Q)) ((P % Q).natDegree - 1)) := by
      rw [hbase, neg_neg]
    rw [hα, mul_smul, hkey, smul_neg, neg_neg]
  rw [hLHS, hRHS]

/-! ### The gcd branch of Theorem 8.34 -/

section DvdPdetRing
variable {D : Type*} [CommRing D]

/-- If a polynomial `d` divides every member of the family, it divides `pdet_{m,n}`
    (which is, by Remark 8.30, a `D`-linear combination of the family). -/
theorem dvd_pdetRing {m n : ℕ} (hm : 0 < m) (hmn : m ≤ n) (F : Fin m → D[X])
    (hF : ∀ r, (F r).degree < (n : WithBot ℕ)) (d : D[X]) (hd : ∀ r, d ∣ F r) :
    d ∣ pdetRing n F := by
  obtain ⟨c, hc⟩ := pdetRing_eq_linear_combination hm hmn
    (fun r => ⟨F r, Polynomial.mem_degreeLT.mpr (hF r)⟩)
  have hc' : pdetRing n F = ∑ i, C (c i) * F i := hc
  rw [hc']
  exact Finset.dvd_sum (fun i _ => (hd i).mul_left _)

end DvdPdetRing

/-- **`gcd P Q ∣ sResP P Q ℓ`** for `ℓ ≤ q`: each row of the Sylvester–Habicht family
    is a multiple of `P` or of `Q`, hence of `gcd P Q`. -/
theorem gcd_dvd_sResP (P Q : K[X]) (hP : P ≠ 0) (hQ : Q ≠ 0)
    (hpq : Q.natDegree < P.natDegree) {ℓ : ℕ} (hℓ : ℓ ≤ Q.natDegree) :
    gcd P Q ∣ sResP P Q ℓ := by
  rw [sResP, ite_eq_left hℓ]
  refine dvd_pdetRing (by omega) (by omega) _ ?_ (gcd P Q) ?_
  · -- each row has degree `< P.natDegree + Q.natDegree - ℓ`
    intro r
    have hr2 := r.isLt
    by_cases hr : (r : ℕ) < Q.natDegree - ℓ
    · rw [ite_eq_left hr,
        Polynomial.degree_eq_natDegree (mul_ne_zero (pow_ne_zero _ Polynomial.X_ne_zero) hP),
        natDegree_X_pow_mul _ hP]
      exact_mod_cast
        (show P.natDegree + (Q.natDegree - ℓ - 1 - (r : ℕ)) < P.natDegree + Q.natDegree - ℓ from by omega)
    · rw [ite_eq_right hr,
        Polynomial.degree_eq_natDegree (mul_ne_zero (pow_ne_zero _ Polynomial.X_ne_zero) hQ),
        natDegree_X_pow_mul _ hQ]
      exact_mod_cast
        (show Q.natDegree + ((r : ℕ) - (Q.natDegree - ℓ)) < P.natDegree + Q.natDegree - ℓ from by omega)
  · -- `gcd P Q` divides each row
    intro r
    by_cases hr : (r : ℕ) < Q.natDegree - ℓ
    · rw [ite_eq_left hr]; exact (gcd_dvd_left P Q).mul_left _
    · rw [ite_eq_right hr]; exact (gcd_dvd_right P Q).mul_left _

/-- **Theorem 8.34, gcd branch — vanishing below the gcd degree.** For `ℓ < deg(gcd)`,
    `sResP P Q ℓ = 0` (it is divisible by `gcd` yet has degree `≤ ℓ < deg gcd`). -/
theorem sResP_eq_zero_of_lt_gcd (P Q : K[X]) (hP : P ≠ 0) (hQ : Q ≠ 0)
    (hpq : Q.natDegree < P.natDegree) {ℓ : ℕ} (hℓ : ℓ ≤ Q.natDegree)
    (hlt : ℓ < (gcd P Q).natDegree) : sResP P Q ℓ = 0 := by
  by_contra h
  have hdvd := gcd_dvd_sResP P Q hP hQ hpq hℓ
  have h1 : (gcd P Q).natDegree ≤ (sResP P Q ℓ).natDegree := Polynomial.natDegree_le_of_dvd hdvd h
  have h2 : (sResP P Q ℓ).natDegree ≤ ℓ :=
    Polynomial.natDegree_le_iff_degree_le.mpr (sResP_degree_le P Q hpq hℓ)
  omega

/-- **Theorem 8.34, gcd branch — identification.** When `deg(gcd P Q) = j`, the `j`-th
    signed subresultant is associate to `gcd P Q` (and has degree exactly `j`). -/
theorem associated_sResP_gcd (P Q : K[X]) (hP : P ≠ 0) (hQ : Q ≠ 0)
    (hpq : Q.natDegree < P.natDegree) {j : ℕ} (hj : (gcd P Q).natDegree = j) :
    Associated (sResP P Q j) (gcd P Q) := by
  classical
  have hgcd_ne : gcd P Q ≠ 0 := fun h => hP (by simpa using (gcd_eq_zero_iff P Q).mp h |>.1)
  have hjq : j ≤ Q.natDegree :=
    hj ▸ Polynomial.natDegree_le_of_dvd (gcd_dvd_right P Q) hQ
  have hsRes : Azurite.BPR.Chapter4.sRes P Q j ≠ 0 :=
    ((Azurite.BPR.Chapter4.Proposition_4_26 P Q hP hQ j hjq (by omega)).mp hj).2
  have hcoeff : (sResP P Q j).coeff j = Azurite.BPR.Chapter4.sRes P Q j :=
    coeff_sResP P Q hpq (by omega)
  have hdvd := gcd_dvd_sResP P Q hP hQ hpq hjq
  obtain ⟨c, hc⟩ := hdvd
  have hsResP_ne : sResP P Q j ≠ 0 := fun h => hsRes (by rw [← hcoeff, h, coeff_zero])
  have hc_ne : c ≠ 0 := by rintro rfl; rw [mul_zero] at hc; exact hsResP_ne hc
  have hdeg_sResP : (sResP P Q j).natDegree = j :=
    le_antisymm (Polynomial.natDegree_le_iff_degree_le.mpr (sResP_degree_le P Q hpq hjq))
      (Polynomial.le_natDegree_of_ne_zero (hcoeff ▸ hsRes))
  have hc0 : c.natDegree = 0 := by
    have := Polynomial.natDegree_mul hgcd_ne hc_ne
    rw [← hc, hdeg_sResP, hj] at this; omega
  have huc : IsUnit c := Polynomial.isUnit_iff_degree_eq_zero.mpr
    (by rw [Polynomial.degree_eq_natDegree hc_ne, hc0]; rfl)
  exact hc ▸ associated_mul_unit_left (gcd P Q) c huc

/-! ### The defective-gap structure of one Euclidean step

When the remainder `R = P % Q` has degree `r < q-1`, the step `(P,Q) → (Q,-R)` is
*defective*: BPR's defective block is the gap `r < ℓ < q-1`, where the subresultants
vanish, and the pair `sResP_r(P,Q)`, `sResP_{q-1}(P,Q)` is proportional.  Both facts
transport from `(Q,-R)` — whose own convention places these indices in its top gap —
via Proposition 8.39, with no induction. -/

/-- **Theorem 8.34, defective gap — vanishing.** For `r := deg(P % Q) < ℓ < q-1`,
    `sResP_ℓ(P,Q) = 0`: by Proposition 8.39 it is proportional to `sResP_ℓ(Q,-R)`, which
    lies in the convention gap of `(Q,-R)` (`q' = r < ℓ < q-1 = p'-1`) and so vanishes. -/
theorem sResP_eq_zero_of_step_gap (P Q : K[X]) (hQ : Q ≠ 0) (hR0 : P % Q ≠ 0)
    (hpq : Q.natDegree < P.natDegree) {ℓ : ℕ}
    (hlo : (P % Q).natDegree < ℓ) (hhi : ℓ < Q.natDegree - 1) : sResP P Q ℓ = 0 := by
  rw [proposition_8_39 P Q hQ hR0 hpq ℓ hhi,
    sResP_eq_zero Q (-(P % Q)) (by rw [natDegree_neg]; exact hlo) (by omega) (by omega)]
  simp

/-- A nonzero scalar multiple is associate to the original polynomial. -/
theorem associated_smul_left (x : K[X]) {s : K} (hs : s ≠ 0) : Associated (s • x) x := by
  rw [smul_eq_C_mul, mul_comm]
  exact associated_mul_unit_left x (C s) (isUnit_C.mpr (isUnit_iff_ne_zero.mpr hs))

/-- **Theorem 8.34, defective gap — proportionality.** When the step is defective
    (`r := deg(P % Q) < q-1`), the subresultants `sResP_r(P,Q)` and `sResP_{q-1}(P,Q)`
    are proportional: both are nonzero scalar multiples of `R = P % Q`
    (`sResP_{q-1}` by the base-case value; `sResP_r` by Proposition 8.39 plus the
    closing-note value of `sResP_r(Q,-R)`), hence associate. -/
theorem sResP_step_proportional (P Q : K[X]) (hQ : Q ≠ 0) (hR0 : P % Q ≠ 0)
    (hpq : Q.natDegree < P.natDegree) (hdef : (P % Q).natDegree < Q.natDegree - 1) :
    Associated (sResP P Q (P % Q).natDegree) (sResP P Q (Q.natDegree - 1)) := by
  have hrq : (P % Q).natDegree < Q.natDegree := by omega
  have hb : Q.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hQ
  have hεne : ((ε (P.natDegree - Q.natDegree) : ℤ) : K) ≠ 0 := by
    rw [Azurite.BPR.Chapter4.ε]; push_cast; exact pow_ne_zero _ (by norm_num)
  have hεne' : ((ε (Q.natDegree - (P % Q).natDegree) : ℤ) : K) ≠ 0 := by
    rw [Azurite.BPR.Chapter4.ε]; push_cast; exact pow_ne_zero _ (by norm_num)
  have hlcR : (-(P % Q)).leadingCoeff ≠ 0 := by
    rw [leadingCoeff_neg, neg_ne_zero]; exact leadingCoeff_ne_zero.mpr hR0
  have hA1 : Associated (sResP P Q (Q.natDegree - 1)) (P % Q) := by
    rw [sResP_natDegree_sub_one P Q hQ hR0 hpq (by omega), ← Int.cast_smul_eq_zsmul K,
      smul_smul, ← neg_smul]
    exact associated_smul_left _ (neg_ne_zero.mpr (mul_ne_zero hεne (pow_ne_zero _ hb)))
  have hA2 : Associated (sResP P Q (P % Q).natDegree) (P % Q) := by
    rw [proposition_8_39 P Q hQ hR0 hpq _ hdef,
      show (P % Q).natDegree = (-(P % Q)).natDegree from (natDegree_neg _).symm,
      sResP_eq_of_natDegree Q (-(P % Q)) (by rw [natDegree_neg]; exact hrq) (neg_ne_zero.mpr hR0),
      ← smul_eq_C_mul, ← Int.cast_smul_eq_zsmul K, ← Int.cast_smul_eq_zsmul K,
      smul_smul, smul_smul, smul_smul, smul_neg, ← neg_smul]
    refine associated_smul_left _ (neg_ne_zero.mpr ?_)
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero hεne (pow_ne_zero _ hb))
      (by rw [natDegree_neg]; exact hεne')) (pow_ne_zero _ hlcR)
  exact hA2.trans hA1.symm

/-! ### Block-chain anchor: the gcd is the bottom of the subresultant chain

The signed subresultant sequence forms a chain of blocks terminating at `gcd P Q`.  These
lemmas anchor the bottom of that chain: `gcd P Q` divides *every* subresultant, every
nonzero subresultant has degree at least `deg(gcd P Q)`, and `sResP_{deg gcd}` is itself
nonzero (associate to the gcd).  (The full block-chain — that the nonzero indices are
exactly the remainder-sequence degrees and their predecessors — is a separate development
built on the remainder sequence.) -/

/-- `gcd P Q` divides `sResP P Q m` for **every** index `m`: in the determinant range
    `m ≤ q` by `gcd_dvd_sResP`; at the conventional top indices `m = p` (`= P`) and
    `m = p-1` (`= Q`); and in the top gap (`sResP_m = 0`). -/
theorem gcd_dvd_sResP_all (P Q : K[X]) (hP : P ≠ 0) (hQ : Q ≠ 0)
    (hpq : Q.natDegree < P.natDegree) (m : ℕ) : gcd P Q ∣ sResP P Q m := by
  rcases Nat.lt_or_ge m (Q.natDegree + 1) with hm | hm
  · exact gcd_dvd_sResP P Q hP hQ hpq (Nat.lt_succ_iff.mp hm)
  · by_cases hmp : m = P.natDegree
    · rw [hmp, sResP_eq_self P Q hpq]; exact gcd_dvd_left P Q
    · by_cases hmp1 : m = P.natDegree - 1
      · rw [hmp1, sResP_eq_self_Q P Q (by omega)]; exact gcd_dvd_right P Q
      · rw [sResP_eq_zero P Q (by omega) hmp hmp1]; exact dvd_zero _

/-- Every nonzero signed subresultant has degree at least `deg(gcd P Q)`. -/
theorem natDegree_gcd_le_natDegree_sResP (P Q : K[X]) (hP : P ≠ 0) (hQ : Q ≠ 0)
    (hpq : Q.natDegree < P.natDegree) {m : ℕ} (hm : sResP P Q m ≠ 0) :
    (gcd P Q).natDegree ≤ (sResP P Q m).natDegree :=
  Polynomial.natDegree_le_of_dvd (gcd_dvd_sResP_all P Q hP hQ hpq m) hm

/-- The subresultant at index `deg(gcd P Q)` is nonzero (it is associate to `gcd P Q`):
    the bottom of the chain is attained. -/
theorem sResP_natDegree_gcd_ne_zero (P Q : K[X]) (hP : P ≠ 0) (hQ : Q ≠ 0)
    (hpq : Q.natDegree < P.natDegree) : sResP P Q (gcd P Q).natDegree ≠ 0 := by
  have hgcd_ne : gcd P Q ≠ 0 := fun h => hP (by simpa using (gcd_eq_zero_iff P Q).mp h |>.1)
  exact fun h => hgcd_ne ((associated_sResP_gcd P Q hP hQ hpq rfl).eq_zero_iff.mp h)

/-- **Top-step termination criterion.** The chain terminates at the top index `q-1`
    (`sResP_{q-1} = 0`) iff `Q ∣ P`: the forward direction is the base-case value
    `sResP_{q-1} = -ε_{p-q} b_q^{p-q+1} (P % Q)` (nonzero when `P % Q ≠ 0`); the converse
    is `Q ∣ P ⟹ deg(gcd) = q ⟹ q-1 < deg(gcd)`, so `sResP_{q-1}` vanishes below the gcd. -/
theorem sResP_natDegree_sub_one_eq_zero_iff (P Q : K[X]) (hP : P ≠ 0) (hQ : Q ≠ 0)
    (hpq : Q.natDegree < P.natDegree) (hq1 : 1 ≤ Q.natDegree) :
    sResP P Q (Q.natDegree - 1) = 0 ↔ Q ∣ P := by
  have hgcd_ne : gcd P Q ≠ 0 := fun h => hP (by simpa using (gcd_eq_zero_iff P Q).mp h |>.1)
  constructor
  · intro h
    by_contra hdvd
    have hR0 : P % Q ≠ 0 := fun hR => hdvd (EuclideanDomain.mod_eq_zero.mp hR)
    have hεne : ((ε (P.natDegree - Q.natDegree) : ℤ) : K) ≠ 0 := by
      rw [Azurite.BPR.Chapter4.ε]; push_cast; exact pow_ne_zero _ (by norm_num)
    rw [sResP_natDegree_sub_one P Q hQ hR0 hpq hq1, neg_eq_zero,
      ← Int.cast_smul_eq_zsmul K, smul_eq_zero, smul_eq_zero] at h
    rcases h with h | h | h
    · exact hεne h
    · exact pow_ne_zero _ (leadingCoeff_ne_zero.mpr hQ) h
    · exact hR0 h
  · intro hdvd
    have hgcd_q : (gcd P Q).natDegree = Q.natDegree :=
      le_antisymm (Polynomial.natDegree_le_of_dvd (gcd_dvd_right P Q) hQ)
        (Polynomial.natDegree_le_of_dvd (dvd_gcd hdvd dvd_rfl) hgcd_ne)
    exact sResP_eq_zero_of_lt_gcd P Q hP hQ hpq (by omega) (by omega)

/-! ### Depth-general chain: the predecessor-vanishing criterion

`sResP_{j-1} = 0 ⟺ deg(gcd) = j` for every non-defective degree `j` (`sRes_j ≠ 0`), by
well-founded induction on `deg Q`.  The Euclidean step `P,Q → Q,-R` transports both the
vanishing pattern (Proposition 8.39, scaling by a nonzero constant) and the gcd degree. -/

/-- `deg(sResP_{q-1}(P,Q)) = deg(P % Q)` (the base-case value `-ε b^{p-q+1} (P%Q)`). -/
theorem natDegree_sResP_natDegree_sub_one (P Q : K[X]) (hQ : Q ≠ 0) (hR0 : P % Q ≠ 0)
    (hpq : Q.natDegree < P.natDegree) (hq1 : 1 ≤ Q.natDegree) :
    (sResP P Q (Q.natDegree - 1)).natDegree = (P % Q).natDegree := by
  have hεne : ((ε (P.natDegree - Q.natDegree) : ℤ) : K) ≠ 0 := by
    rw [Azurite.BPR.Chapter4.ε]; push_cast; exact pow_ne_zero _ (by norm_num)
  rw [sResP_natDegree_sub_one P Q hQ hR0 hpq hq1, natDegree_neg, ← Int.cast_smul_eq_zsmul K,
    smul_smul, natDegree_smul _ (mul_ne_zero hεne (pow_ne_zero _ (leadingCoeff_ne_zero.mpr hQ)))]

/-- The signed subresultant coefficient `sRes_j(P,Q)` vanishes in the gap `r < j < q`
    (`r = deg(P % Q)`): for `r < j < q-1` because `sResP_j = 0`, and for `j = q-1` because
    `deg(sResP_{q-1}) = r < q-1`. -/
theorem sRes_eq_zero_of_step_gap (P Q : K[X]) (hQ : Q ≠ 0) (hR0 : P % Q ≠ 0)
    (hpq : Q.natDegree < P.natDegree) {j : ℕ} (hlo : (P % Q).natDegree < j)
    (hhi : j < Q.natDegree) : Azurite.BPR.Chapter4.sRes P Q j = 0 := by
  have hb : Q.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hQ
  have hεne : ((ε (P.natDegree - Q.natDegree) : ℤ) : K) ≠ 0 := by
    rw [Azurite.BPR.Chapter4.ε]; push_cast; exact pow_ne_zero _ (by norm_num)
  rw [← coeff_sResP P Q hpq (by omega)]
  apply coeff_eq_zero_of_degree_lt
  rcases eq_or_lt_of_le (show j ≤ Q.natDegree - 1 from by omega) with hj | hj
  · have hne : sResP P Q (Q.natDegree - 1) ≠ 0 := by
      rw [sResP_natDegree_sub_one P Q hQ hR0 hpq (by omega), neg_ne_zero,
        ← Int.cast_smul_eq_zsmul K, smul_smul]
      exact smul_ne_zero (mul_ne_zero hεne (pow_ne_zero _ hb)) hR0
    rw [hj, Polynomial.degree_eq_natDegree hne,
      natDegree_sResP_natDegree_sub_one P Q hQ hR0 hpq (by omega)]
    exact_mod_cast (show (P % Q).natDegree < Q.natDegree - 1 from by omega)
  · rw [sResP_eq_zero_of_step_gap P Q hQ hR0 hpq hlo hj]
    simp

/-- `deg(gcd(P,Q)) = deg(gcd(Q,-R))` — the gcd degree is invariant under one Euclidean
    step (`gcd(P,Q) ~ gcd(Q, P % Q) ~ gcd(Q, -(P % Q))`). -/
theorem natDegree_gcd_step (P Q : K[X]) (hP : P ≠ 0) (hQ : Q ≠ 0) :
    (gcd P Q).natDegree = (gcd Q (-(P % Q))).natDegree := by
  have hgcd1 : gcd P Q ≠ 0 := fun h => hP (by simpa using (gcd_eq_zero_iff P Q).mp h |>.1)
  have hgcd2 : gcd Q (-(P % Q)) ≠ 0 :=
    fun h => hQ (by simpa using (gcd_eq_zero_iff Q (-(P % Q))).mp h |>.1)
  have hmod : P % Q = P - Q * (P / Q) := by
    have := EuclideanDomain.div_add_mod P Q; linear_combination this
  refine le_antisymm (Polynomial.natDegree_le_of_dvd ?_ hgcd2)
    (Polynomial.natDegree_le_of_dvd ?_ hgcd1)
  · refine dvd_gcd (gcd_dvd_right P Q) (dvd_neg.mpr ?_)
    rw [hmod]; exact dvd_sub (gcd_dvd_left P Q) ((gcd_dvd_right P Q).mul_right _)
  · refine dvd_gcd ?_ (gcd_dvd_left Q _)
    have hR : gcd Q (-(P % Q)) ∣ P % Q := dvd_neg.mp (gcd_dvd_right Q _)
    have key : gcd Q (-(P % Q)) ∣ Q * (P / Q) + P % Q :=
      dvd_add ((gcd_dvd_left Q _).mul_right _) hR
    rwa [EuclideanDomain.div_add_mod P Q] at key

/-- **Transport of `sRes_j` across a Euclidean step**, for `j ≤ r := deg(P % Q)`:
    `sRes_j(P,Q) = ε_{p-q} b_q^{p-r} sRes_j(Q,-R)`. -/
theorem sRes_swap_le (P Q : K[X]) (hQ : Q ≠ 0) (hR0 : P % Q ≠ 0)
    (hpq : Q.natDegree < P.natDegree) {j : ℕ} (hj : j ≤ (P % Q).natDegree) :
    Azurite.BPR.Chapter4.sRes P Q j
      = (ε (P.natDegree - Q.natDegree) : ℤ)
        • (Q.leadingCoeff ^ (P.natDegree - (P % Q).natDegree)
            • Azurite.BPR.Chapter4.sRes Q (-(P % Q)) j) := by
  have hrq : (P % Q).natDegree < Q.natDegree :=
    natDegree_lt_natDegree hR0 (degree_mod_lt P hQ)
  rw [← coeff_sResP P Q hpq (by omega), sResP_propto_le_r P Q hQ hR0 hpq hj]
  simp only [← Int.cast_smul_eq_zsmul K]
  rw [Polynomial.coeff_smul, Polynomial.coeff_smul,
    coeff_sResP Q (-(P % Q)) (by rw [natDegree_neg]; exact hrq) (by omega)]

/-- `sResP_q(P,Q)` is non-defective: `deg(sResP_q) = q` (the closing-note value
    `ε b^{p-q-1} Q` has degree `deg Q = q`). -/
theorem natDegree_sResP_natDegree (P Q : K[X]) (hQ : Q ≠ 0)
    (hpq : Q.natDegree < P.natDegree) : (sResP P Q Q.natDegree).natDegree = Q.natDegree := by
  have hεne : ((ε (P.natDegree - Q.natDegree) : ℤ) : K) ≠ 0 := by
    rw [Azurite.BPR.Chapter4.ε]; push_cast; exact pow_ne_zero _ (by norm_num)
  rw [sResP_eq_of_natDegree P Q hpq hQ, ← Int.cast_smul_eq_zsmul K, natDegree_smul _ hεne,
    natDegree_C_mul (pow_ne_zero _ (leadingCoeff_ne_zero.mpr hQ))]

/-- **Depth-general block proportionality (the block induction).**  For `m ≤ q` with
    `sResP_m(P,Q) ≠ 0`, the subresultant `sResP_m` is associate to the non-defective
    representative `sResP_{deg(sResP_m)}` at its own degree.  By well-founded induction on
    `deg Q`: trivial when non-defective; the single-step block (`m = q-1`) is
    `sResP_step_proportional`; the gap is excluded; and `m ≤ r` transports to `Q,-R`. -/
theorem sResP_block_associated (P Q : K[X]) (hP : P ≠ 0) (hQ : Q ≠ 0)
    (hpq : Q.natDegree < P.natDegree) {m : ℕ} (hmq : m ≤ Q.natDegree) (hm : sResP P Q m ≠ 0) :
    Associated (sResP P Q (sResP P Q m).natDegree) (sResP P Q m) := by
  suffices key : ∀ n, ∀ P Q : K[X], P ≠ 0 → Q ≠ 0 → Q.natDegree = n →
      Q.natDegree < P.natDegree → ∀ m, m ≤ Q.natDegree → sResP P Q m ≠ 0 →
      Associated (sResP P Q (sResP P Q m).natDegree) (sResP P Q m) from
    key Q.natDegree P Q hP hQ rfl hpq m hmq hm
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro P Q hP hQ hn hpq m hmq hm
    have hb : Q.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hQ
    have hεne : ((ε (P.natDegree - Q.natDegree) : ℤ) : K) ≠ 0 := by
      rw [Azurite.BPR.Chapter4.ε]; push_cast; exact pow_ne_zero _ (by norm_num)
    have hjm : (sResP P Q m).natDegree ≤ m :=
      Polynomial.natDegree_le_iff_degree_le.mpr (sResP_degree_le P Q hpq hmq)
    by_cases hjeq : (sResP P Q m).natDegree = m
    · rw [hjeq]
    · have hmq' : m < Q.natDegree := lt_of_le_of_ne hmq (by
        rintro rfl; exact hjeq (natDegree_sResP_natDegree P Q hQ hpq))
      have hR : P % Q ≠ 0 := by
        rintro hR0
        have hgcdq : (gcd P Q).natDegree = Q.natDegree :=
          le_antisymm (Polynomial.natDegree_le_of_dvd (gcd_dvd_right P Q) hQ)
            (Polynomial.natDegree_le_of_dvd
              (dvd_gcd (EuclideanDomain.mod_eq_zero.mp hR0) dvd_rfl)
              (fun h => hP (by simpa using (gcd_eq_zero_iff P Q).mp h |>.1)))
        exact hm (sResP_eq_zero_of_lt_gcd P Q hP hQ hpq hmq (by omega))
      have hrq : (P % Q).natDegree < Q.natDegree :=
        natDegree_lt_natDegree hR (degree_mod_lt P hQ)
      by_cases hmqm1 : m = Q.natDegree - 1
      · subst hmqm1
        have hr_lt : (P % Q).natDegree < Q.natDegree - 1 := by
          have := natDegree_sResP_natDegree_sub_one P Q hQ hR hpq (by omega); omega
        rw [natDegree_sResP_natDegree_sub_one P Q hQ hR hpq (by omega)]
        exact sResP_step_proportional P Q hQ hR hpq hr_lt
      · by_cases hmr : m ≤ (P % Q).natDegree
        · have hmlt : m < Q.natDegree - 1 := by omega
          have hSm' : sResP Q (-(P % Q)) m ≠ 0 := fun h => hm (by
            rw [proposition_8_39 P Q hQ hR hpq m hmlt, h]; simp)
          have hjeq' : (sResP P Q m).natDegree = (sResP Q (-(P % Q)) m).natDegree := by
            rw [proposition_8_39 P Q hQ hR hpq m hmlt, ← Int.cast_smul_eq_zsmul K, smul_smul,
              natDegree_smul _ (mul_ne_zero hεne (pow_ne_zero _ hb))]
          have hj'lt : (sResP Q (-(P % Q)) m).natDegree < Q.natDegree - 1 := by
            rw [← hjeq']; exact lt_of_le_of_lt hjm hmlt
          rw [hjeq', proposition_8_39 P Q hQ hR hpq (sResP Q (-(P % Q)) m).natDegree hj'lt,
            proposition_8_39 P Q hQ hR hpq m hmlt]
          simp only [← Int.cast_smul_eq_zsmul K, smul_smul]
          rw [smul_eq_C_mul, smul_eq_C_mul]
          exact Associated.mul_left _ (ih (P % Q).natDegree (hn ▸ hrq) Q (-(P % Q)) hQ
            (neg_ne_zero.mpr hR) (Polynomial.natDegree_neg _) (by rw [natDegree_neg]; exact hrq) m
            (by rw [natDegree_neg]; exact hmr) hSm')
        · exact absurd (sResP_eq_zero_of_step_gap P Q hQ hR hpq (by omega) (by omega)) hm

/-- **Depth-general predecessor-vanishing criterion (the chain induction).**  For every
    *non-defective* degree `j` (`sRes_j ≠ 0`, `1 ≤ j ≤ q`),
    `sResP_{j-1}(P,Q) = 0 ⟺ deg(gcd P Q) = j`.  Proved by well-founded induction on `deg Q`:
    `j = q` is the top-step criterion; `r < j < q` is vacuous (`sRes_j = 0`); and `j ≤ r`
    transports to `Q,-R` (vanishing by Proposition 8.39, gcd degree by `natDegree_gcd_step`)
    and applies the induction hypothesis. -/
theorem sResP_pred_eq_zero_iff (P Q : K[X]) (hP : P ≠ 0) (hQ : Q ≠ 0)
    (hpq : Q.natDegree < P.natDegree) {j : ℕ} (hj1 : 1 ≤ j) (hjq : j ≤ Q.natDegree)
    (hsRes : Azurite.BPR.Chapter4.sRes P Q j ≠ 0) :
    sResP P Q (j - 1) = 0 ↔ (gcd P Q).natDegree = j := by
  suffices key : ∀ n, ∀ P Q : K[X], P ≠ 0 → Q ≠ 0 → Q.natDegree = n →
      Q.natDegree < P.natDegree → ∀ j, 1 ≤ j → j ≤ Q.natDegree →
      Azurite.BPR.Chapter4.sRes P Q j ≠ 0 →
      (sResP P Q (j - 1) = 0 ↔ (gcd P Q).natDegree = j) from
    key Q.natDegree P Q hP hQ rfl hpq j hj1 hjq hsRes
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro P Q hP hQ hn hpq j hj1 hjq hsRes
    have hq1 : 1 ≤ Q.natDegree := le_trans hj1 hjq
    have hgcd_ne : gcd P Q ≠ 0 := fun h => hP (by simpa using (gcd_eq_zero_iff P Q).mp h |>.1)
    have hb : Q.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hQ
    have hεne : ((ε (P.natDegree - Q.natDegree) : ℤ) : K) ≠ 0 := by
      rw [Azurite.BPR.Chapter4.ε]; push_cast; exact pow_ne_zero _ (by norm_num)
    have hdvd_iff : Q ∣ P ↔ (gcd P Q).natDegree = Q.natDegree := by
      constructor
      · intro hdvd
        exact le_antisymm (Polynomial.natDegree_le_of_dvd (gcd_dvd_right P Q) hQ)
          (Polynomial.natDegree_le_of_dvd (dvd_gcd hdvd dvd_rfl) hgcd_ne)
      · intro hg
        obtain ⟨c, hc⟩ := gcd_dvd_right P Q
        have hc_ne : c ≠ 0 := fun h => hQ (by rw [hc, h, mul_zero])
        have hc0 : c.natDegree = 0 := by
          have := Polynomial.natDegree_mul hgcd_ne hc_ne; rw [← hc, hg] at this; omega
        have huc : IsUnit c := Polynomial.isUnit_iff_degree_eq_zero.mpr
          (by rw [Polynomial.degree_eq_natDegree hc_ne, hc0]; rfl)
        have hassoc : Associated Q (gcd P Q) := by
          have h := associated_mul_unit_left (gcd P Q) c huc
          rwa [← hc] at h
        exact hassoc.dvd.trans (gcd_dvd_left P Q)
    by_cases hjeq : j = Q.natDegree
    · subst hjeq
      rw [sResP_natDegree_sub_one_eq_zero_iff P Q hP hQ hpq hq1, hdvd_iff]
    · by_cases hR : P % Q = 0
      · exfalso; apply hsRes
        have hg : (gcd P Q).natDegree = Q.natDegree :=
          hdvd_iff.mp (EuclideanDomain.mod_eq_zero.mp hR)
        rw [← coeff_sResP P Q hpq (by omega),
          sResP_eq_zero_of_lt_gcd P Q hP hQ hpq hjq (by omega)]
        simp
      · have hrq : (P % Q).natDegree < Q.natDegree :=
          natDegree_lt_natDegree hR (degree_mod_lt P hQ)
        by_cases hjr : j ≤ (P % Q).natDegree
        · have hsRes' : Azurite.BPR.Chapter4.sRes Q (-(P % Q)) j ≠ 0 := fun h => hsRes (by
            rw [sRes_swap_le P Q hQ hR hpq hjr, h, smul_zero, smul_zero])
          have hih := ih (P % Q).natDegree (hn ▸ hrq) Q (-(P % Q)) hQ (neg_ne_zero.mpr hR)
            (Polynomial.natDegree_neg _) (by rw [natDegree_neg]; exact hrq) j hj1
            (by rw [natDegree_neg]; exact hjr) hsRes'
          rw [natDegree_gcd_step P Q hP hQ, ← hih,
            proposition_8_39 P Q hQ hR hpq (j - 1) (by omega),
            ← Int.cast_smul_eq_zsmul K, smul_eq_zero, smul_eq_zero]
          constructor
          · rintro (h | h | h)
            · exact absurd h hεne
            · exact absurd h (pow_ne_zero _ hb)
            · exact h
          · intro h; exact Or.inr (Or.inr h)
        · exact absurd (sRes_eq_zero_of_step_gap P Q hQ hR hpq (by omega) (by omega)) hsRes

/-- **Theorem 8.34, gcd branch — verbatim form.**  At a non-defective degree `j`
    (`sRes_j ≠ 0`), if the predecessor subresultant vanishes (`sResP_{j-1} = 0`), then
    `sResP_j` is associate to `gcd P Q` and all lower subresultants vanish — BPR's
    "`sResP_{j-1} = 0 ⟹ sResP_{i-1} = gcd ∧ sResP_ℓ = 0` for `ℓ ≤ j-1`".  The chain
    induction (`sResP_pred_eq_zero_iff`) supplies the missing link `deg gcd = j`. -/
theorem theorem_8_34_gcd_branch (P Q : K[X]) (hP : P ≠ 0) (hQ : Q ≠ 0)
    (hpq : Q.natDegree < P.natDegree) {j : ℕ} (hj1 : 1 ≤ j) (hjq : j ≤ Q.natDegree)
    (hsRes : Azurite.BPR.Chapter4.sRes P Q j ≠ 0) (hzero : sResP P Q (j - 1) = 0) :
    Associated (sResP P Q j) (gcd P Q) ∧ ∀ ℓ, ℓ < j → sResP P Q ℓ = 0 := by
  have hg : (gcd P Q).natDegree = j :=
    (sResP_pred_eq_zero_iff P Q hP hQ hpq hj1 hjq hsRes).mp hzero
  refine ⟨?_, fun ℓ hℓ => ?_⟩
  · rw [← hg]; exact associated_sResP_gcd P Q hP hQ hpq rfl
  · exact sResP_eq_zero_of_lt_gcd P Q hP hQ hpq (le_trans hℓ.le hjq) (hg ▸ hℓ)

/-- **Theorem 8.34, gcd branch — fully general (defective index).**  For *any* index `m ≤ q`
    with `sResP_m(P,Q) ≠ 0` of degree `j ≥ 1`, if `sResP_{j-1} = 0` then `sResP_m` itself
    (defective or not) is associate to `gcd P Q`, and all lower subresultants vanish.  This
    is BPR's gcd branch verbatim, with `m = i-1`: the block proportionality
    (`sResP_block_associated`) relates `sResP_m` to its non-defective representative
    `sResP_j` (whence `sRes_j ≠ 0`), and the chain induction gives `deg gcd = j`. -/
theorem theorem_8_34_gcd_branch_general (P Q : K[X]) (hP : P ≠ 0) (hQ : Q ≠ 0)
    (hpq : Q.natDegree < P.natDegree) {m j : ℕ} (hmq : m ≤ Q.natDegree) (hm : sResP P Q m ≠ 0)
    (hdeg : (sResP P Q m).natDegree = j) (hj1 : 1 ≤ j) (hzero : sResP P Q (j - 1) = 0) :
    Associated (sResP P Q m) (gcd P Q) ∧ ∀ ℓ, ℓ < j → sResP P Q ℓ = 0 := by
  have hblock : Associated (sResP P Q j) (sResP P Q m) := by
    rw [← hdeg]; exact sResP_block_associated P Q hP hQ hpq hmq hm
  have hSj_ne : sResP P Q j ≠ 0 := fun h => hm (hblock.eq_zero_iff.mp h)
  have hjm : j ≤ m := by
    rw [← hdeg]; exact Polynomial.natDegree_le_iff_degree_le.mpr (sResP_degree_le P Q hpq hmq)
  have h2 : j ≤ (sResP P Q j).natDegree := by
    have h := Polynomial.natDegree_le_of_dvd hblock.symm.dvd hSj_ne
    rwa [hdeg] at h
  have hdegj : (sResP P Q j).natDegree = j :=
    le_antisymm ((Polynomial.natDegree_le_of_dvd hblock.dvd hm).trans_eq hdeg) h2
  have hsResj : Azurite.BPR.Chapter4.sRes P Q j ≠ 0 := by
    rw [← coeff_sResP P Q hpq (by omega)]
    have hc : (sResP P Q j).coeff j = (sResP P Q j).leadingCoeff := by
      rw [Polynomial.leadingCoeff, hdegj]
    rw [hc]; exact Polynomial.leadingCoeff_ne_zero.mpr hSj_ne
  have hg : (gcd P Q).natDegree = j :=
    (sResP_pred_eq_zero_iff P Q hP hQ hpq hj1 (by omega) hsResj).mp hzero
  have hgcd_assoc : Associated (sResP P Q j) (gcd P Q) := by
    rw [← hg]; exact associated_sResP_gcd P Q hP hQ hpq rfl
  refine ⟨hblock.symm.trans hgcd_assoc, fun ℓ hℓ => ?_⟩
  exact sResP_eq_zero_of_lt_gcd P Q hP hQ hpq (le_trans hℓ.le (by omega)) (by rw [hg]; exact hℓ)

/-! ### Depth-general recurrence: transporting `(★)` through a Euclidean step -/

theorem recurrence_lhs_transport (P Q : K[X]) (hQ : Q ≠ 0) (hR0 : P % Q ≠ 0)
    (hpq : Q.natDegree < P.natDegree) (hq1 : 1 ≤ Q.natDegree)
    (hr'lt : (Q % (-(P % Q))).natDegree - 1 < Q.natDegree - 1) :
    C (Azurite.BPR.Chapter4.sRes P Q (P % Q).natDegree)
        * C (sResP P Q (Q.natDegree - 1)).leadingCoeff
        * sResP P Q ((Q % (-(P % Q))).natDegree - 1)
      = (((ε (P.natDegree - Q.natDegree) : ℤ) : K)
          * Q.leadingCoeff ^ (2 * (P.natDegree - (P % Q).natDegree)
              + (P.natDegree - Q.natDegree + 1)))
        • (C (Azurite.BPR.Chapter4.sRes Q (-(P % Q)) (P % Q).natDegree)
            * C (sResP Q (-(P % Q)) (Q.natDegree - 1)).leadingCoeff
            * sResP Q (-(P % Q)) ((Q % (-(P % Q))).natDegree - 1)) := by
  have he : ((ε (P.natDegree - Q.natDegree) : ℤ) : K)
      * ((ε (P.natDegree - Q.natDegree) : ℤ) : K) = 1 := by
    rw [← Int.cast_mul, Azurite.BPR.Chapter4.ε, ← pow_add, Even.neg_one_pow ⟨_, rfl⟩, Int.cast_one]
  rw [sRes_swap_natDegree_mod P Q hQ hR0 hpq,
    leadingCoeff_sResP_natDegree_sub_one_swap P Q hQ hR0 hpq hq1,
    proposition_8_39 P Q hQ hR0 hpq ((Q % (-(P % Q))).natDegree - 1) hr'lt]
  simp only [← Int.cast_smul_eq_zsmul K, smul_eq_mul, smul_eq_C_mul, ← C_mul, ← mul_assoc]
  congr 1
  rw [Polynomial.C_inj, show 2 * (P.natDegree - (P % Q).natDegree) + (P.natDegree - Q.natDegree + 1)
    = (P.natDegree - (P % Q).natDegree) + (P.natDegree - Q.natDegree + 1)
      + (P.natDegree - (P % Q).natDegree) from by omega, pow_add, pow_add]
  linear_combination (((ε (P.natDegree - Q.natDegree) : ℤ) : K)
    * Q.leadingCoeff ^ (P.natDegree - (P % Q).natDegree)
    * Q.leadingCoeff ^ (P.natDegree - Q.natDegree + 1)
    * Q.leadingCoeff ^ (P.natDegree - (P % Q).natDegree)
    * Azurite.BPR.Chapter4.sRes Q (-(P % Q)) (P % Q).natDegree
    * (sResP Q (-(P % Q)) (Q.natDegree - 1)).leadingCoeff) * he

theorem recurrence_rhs_transport (P Q : K[X]) (hQ : Q ≠ 0) (hR0 : P % Q ≠ 0)
    (hpq : Q.natDegree < P.natDegree) (hq1 : 1 ≤ Q.natDegree)
    (hr'r : (Q % (-(P % Q))).natDegree ≤ (P % Q).natDegree)
    (hr1lt : (P % Q).natDegree - 1 < Q.natDegree - 1) :
    -((C (Azurite.BPR.Chapter4.sRes P Q (Q % (-(P % Q))).natDegree)
          * C (sResP P Q ((P % Q).natDegree - 1)).leadingCoeff
          * sResP P Q (Q.natDegree - 1)) % sResP P Q ((P % Q).natDegree - 1))
      = (((ε (P.natDegree - Q.natDegree) : ℤ) : K)
          * Q.leadingCoeff ^ (2 * (P.natDegree - (P % Q).natDegree)
              + (P.natDegree - Q.natDegree + 1)))
        • (-((C (Azurite.BPR.Chapter4.sRes Q (-(P % Q)) (Q % (-(P % Q))).natDegree)
            * C (sResP Q (-(P % Q)) ((P % Q).natDegree - 1)).leadingCoeff
            * sResP Q (-(P % Q)) (Q.natDegree - 1)) % sResP Q (-(P % Q)) ((P % Q).natDegree - 1))) := by
  have he : ((ε (P.natDegree - Q.natDegree) : ℤ) : K)
      * ((ε (P.natDegree - Q.natDegree) : ℤ) : K) = 1 := by
    rw [← Int.cast_mul, Azurite.BPR.Chapter4.ε, ← pow_add, Even.neg_one_pow ⟨_, rfl⟩, Int.cast_one]
  have hεne : ((ε (P.natDegree - Q.natDegree) : ℤ) : K) ≠ 0 := left_ne_zero_of_mul_eq_one he
  rw [sRes_swap_le P Q hQ hR0 hpq hr'r,
    leadingCoeff_sResP_swap P Q hQ hR0 hpq hr1lt,
    sResP_natDegree_sub_one_propto P Q hQ hR0 hpq hq1,
    proposition_8_39 P Q hQ hR0 hpq ((P % Q).natDegree - 1) hr1lt]
  simp only [← Int.cast_smul_eq_zsmul K, smul_eq_mul, smul_eq_C_mul, ← C_mul, ← mul_assoc]
  rw [mod_C_mul_right _ _ (mul_ne_zero hεne (pow_ne_zero _ (leadingCoeff_ne_zero.mpr hQ))),
    rem_C_mul]
  conv_rhs => rw [rem_C_mul, mul_neg, ← mul_assoc, ← C_mul]
  congr 2
  rw [Polynomial.C_inj, show 2 * (P.natDegree - (P % Q).natDegree) + (P.natDegree - Q.natDegree + 1)
    = (P.natDegree - (P % Q).natDegree) + (P.natDegree - Q.natDegree + 1)
      + (P.natDegree - (P % Q).natDegree) from by omega, pow_add, pow_add]
  linear_combination (((ε (P.natDegree - Q.natDegree) : ℤ) : K)
    * Q.leadingCoeff ^ (P.natDegree - (P % Q).natDegree)
    * Q.leadingCoeff ^ (P.natDegree - (P % Q).natDegree)
    * Q.leadingCoeff ^ (P.natDegree - Q.natDegree + 1)
    * Azurite.BPR.Chapter4.sRes Q (-(P % Q)) (Q % (-(P % Q))).natDegree
    * (sResP Q (-(P % Q)) ((P % Q).natDegree - 1)).leadingCoeff) * he

/-- **Depth-general recurrence — one transport step.**  Given the structure-theorem
    recurrence for the pair `Q, -R` (in its own subresultants), the corresponding recurrence
    holds for `P, Q` *in `P,Q`'s subresultants*, at the next chain level (relating
    `sResP_{r'-1}`, `sResP_{q-1}`, `sResP_{r-1}` with `r = deg R`, `r' = deg(Q % -R)`):
    `s_r t_{q-1} sResP_{r'-1}(P,Q) = -Rem(s_{r'} t_{r-1} sResP_{q-1}(P,Q), sResP_{r-1}(P,Q))`.
    Both sides scale by `ε_{p-q}² b^{...}` relative to the `Q,-R` recurrence (Proposition 8.39
    and the boundary/coefficient bridges).  Iterating from the base recurrence
    `sResP_inductive_step_identity` realizes BPR's recurrence at every depth. -/
theorem recurrence_transport (P Q : K[X]) (hQ : Q ≠ 0) (hR0 : P % Q ≠ 0)
    (hpq : Q.natDegree < P.natDegree) (hq1 : 1 ≤ Q.natDegree)
    (hr'r : (Q % (-(P % Q))).natDegree ≤ (P % Q).natDegree)
    (hr'lt : (Q % (-(P % Q))).natDegree - 1 < Q.natDegree - 1)
    (hr1lt : (P % Q).natDegree - 1 < Q.natDegree - 1)
    (hrec : C (Azurite.BPR.Chapter4.sRes Q (-(P % Q)) (P % Q).natDegree)
          * C (sResP Q (-(P % Q)) (Q.natDegree - 1)).leadingCoeff
          * sResP Q (-(P % Q)) ((Q % (-(P % Q))).natDegree - 1)
        = -((C (Azurite.BPR.Chapter4.sRes Q (-(P % Q)) (Q % (-(P % Q))).natDegree)
            * C (sResP Q (-(P % Q)) ((P % Q).natDegree - 1)).leadingCoeff
            * sResP Q (-(P % Q)) (Q.natDegree - 1)) % sResP Q (-(P % Q)) ((P % Q).natDegree - 1))) :
    C (Azurite.BPR.Chapter4.sRes P Q (P % Q).natDegree)
        * C (sResP P Q (Q.natDegree - 1)).leadingCoeff
        * sResP P Q ((Q % (-(P % Q))).natDegree - 1)
      = -((C (Azurite.BPR.Chapter4.sRes P Q (Q % (-(P % Q))).natDegree)
          * C (sResP P Q ((P % Q).natDegree - 1)).leadingCoeff
          * sResP P Q (Q.natDegree - 1)) % sResP P Q ((P % Q).natDegree - 1)) := by
  rw [recurrence_lhs_transport P Q hQ hR0 hpq hq1 hr'lt, hrec,
    ← recurrence_rhs_transport P Q hQ hR0 hpq hq1 hr'r hr1lt]

/-- **Depth-general recurrence — fully assembled per-pair step.**  For a sufficiently
    generic pair `(P,Q)` (the next two remainders nonzero with the BPR degree gaps), the
    structure-theorem recurrence holds one chain level below the top, in `(P,Q)`'s own
    subresultants:
    `s_r t_{q-1} sResP_{r'-1}(P,Q) = -Rem(s_{r'} t_{r-1} sResP_{q-1}(P,Q), sResP_{r-1}(P,Q))`,
    with `r = deg(P % Q)`, `r' = deg(Q % -R)`.  Obtained by transporting the base recurrence
    (`sResP_inductive_step_identity`) for `Q, -R` through one step (`recurrence_transport`).
    Applying this — and the base recurrence — to every pair of the remainder sequence
    realizes BPR's recurrence at all depths. -/
theorem sResP_recurrence_step (P Q : K[X]) (hQ : Q ≠ 0) (hR0 : P % Q ≠ 0)
    (hpq : Q.natDegree < P.natDegree) (hq1 : 1 ≤ Q.natDegree)
    (hR'0 : Q % (-(P % Q)) ≠ 0) (hr1 : 1 ≤ (P % Q).natDegree)
    (hrq1 : (P % Q).natDegree + 1 < Q.natDegree) (hr'1 : 1 ≤ (Q % (-(P % Q))).natDegree)
    (hr'r1 : (Q % (-(P % Q))).natDegree + 1 < (P % Q).natDegree)
    (hR''0 : (-(P % Q)) % (-(Q % (-(P % Q)))) ≠ 0) :
    C (Azurite.BPR.Chapter4.sRes P Q (P % Q).natDegree)
        * C (sResP P Q (Q.natDegree - 1)).leadingCoeff
        * sResP P Q ((Q % (-(P % Q))).natDegree - 1)
      = -((C (Azurite.BPR.Chapter4.sRes P Q (Q % (-(P % Q))).natDegree)
          * C (sResP P Q ((P % Q).natDegree - 1)).leadingCoeff
          * sResP P Q (Q.natDegree - 1)) % sResP P Q ((P % Q).natDegree - 1)) := by
  have hrec := sResP_inductive_step_identity Q (-(P % Q)) (neg_ne_zero.mpr hR0) hR'0
    (by rw [natDegree_neg]; omega) hr'1 hR''0
  rw [natDegree_neg] at hrec
  exact recurrence_transport P Q hQ hR0 hpq hq1 (by omega) (by omega) (by omega) hrec

/-! ### Uniform deep transport (all indices below `q-1`) -/

/-- LHS of a recurrence at a deep triple (`j, k ≤ r` and `i-1, k-1 < q-1`) transports by the
    uniform factor `ε_{p-q} b_q^{3(p-r)}` (all three factors use Proposition 8.39's interior
    bridges). -/
theorem general_lhs_transport (P Q : K[X]) (hQ : Q ≠ 0) (hR0 : P % Q ≠ 0)
    (hpq : Q.natDegree < P.natDegree) {i j k : ℕ} (hjr : j ≤ (P % Q).natDegree)
    (hi1 : i - 1 < Q.natDegree - 1) (hk1 : k - 1 < Q.natDegree - 1) :
    C (Azurite.BPR.Chapter4.sRes P Q j) * C (sResP P Q (i - 1)).leadingCoeff * sResP P Q (k - 1)
      = (((ε (P.natDegree - Q.natDegree) : ℤ) : K)
          * Q.leadingCoeff ^ (3 * (P.natDegree - (P % Q).natDegree)))
        • (C (Azurite.BPR.Chapter4.sRes Q (-(P % Q)) j)
            * C (sResP Q (-(P % Q)) (i - 1)).leadingCoeff * sResP Q (-(P % Q)) (k - 1)) := by
  have he : ((ε (P.natDegree - Q.natDegree) : ℤ) : K)
      * ((ε (P.natDegree - Q.natDegree) : ℤ) : K) = 1 := by
    rw [← Int.cast_mul, Azurite.BPR.Chapter4.ε, ← pow_add, Even.neg_one_pow ⟨_, rfl⟩, Int.cast_one]
  rw [sRes_swap_le P Q hQ hR0 hpq hjr, leadingCoeff_sResP_swap P Q hQ hR0 hpq hi1,
    proposition_8_39 P Q hQ hR0 hpq (k - 1) hk1]
  simp only [← Int.cast_smul_eq_zsmul K, smul_eq_mul, smul_eq_C_mul, ← C_mul, ← mul_assoc]
  congr 1
  rw [Polynomial.C_inj, show 3 * (P.natDegree - (P % Q).natDegree)
    = (P.natDegree - (P % Q).natDegree) + (P.natDegree - (P % Q).natDegree)
      + (P.natDegree - (P % Q).natDegree) from by omega, pow_add, pow_add]
  linear_combination (((ε (P.natDegree - Q.natDegree) : ℤ) : K)
    * Q.leadingCoeff ^ (P.natDegree - (P % Q).natDegree)
    * Q.leadingCoeff ^ (P.natDegree - (P % Q).natDegree)
    * Q.leadingCoeff ^ (P.natDegree - (P % Q).natDegree)
    * Azurite.BPR.Chapter4.sRes Q (-(P % Q)) j
    * (sResP Q (-(P % Q)) (i - 1)).leadingCoeff) * he

/-- RHS of a recurrence at a deep triple transports by the same uniform factor. -/
theorem general_rhs_transport (P Q : K[X]) (hQ : Q ≠ 0) (hR0 : P % Q ≠ 0)
    (hpq : Q.natDegree < P.natDegree) {i j k : ℕ} (hkr : k ≤ (P % Q).natDegree)
    (hj1 : j - 1 < Q.natDegree - 1) (hi1 : i - 1 < Q.natDegree - 1) :
    -((C (Azurite.BPR.Chapter4.sRes P Q k) * C (sResP P Q (j - 1)).leadingCoeff
          * sResP P Q (i - 1)) % sResP P Q (j - 1))
      = (((ε (P.natDegree - Q.natDegree) : ℤ) : K)
          * Q.leadingCoeff ^ (3 * (P.natDegree - (P % Q).natDegree)))
        • (-((C (Azurite.BPR.Chapter4.sRes Q (-(P % Q)) k)
            * C (sResP Q (-(P % Q)) (j - 1)).leadingCoeff
            * sResP Q (-(P % Q)) (i - 1)) % sResP Q (-(P % Q)) (j - 1))) := by
  have he : ((ε (P.natDegree - Q.natDegree) : ℤ) : K)
      * ((ε (P.natDegree - Q.natDegree) : ℤ) : K) = 1 := by
    rw [← Int.cast_mul, Azurite.BPR.Chapter4.ε, ← pow_add, Even.neg_one_pow ⟨_, rfl⟩, Int.cast_one]
  have hεne : ((ε (P.natDegree - Q.natDegree) : ℤ) : K) ≠ 0 := left_ne_zero_of_mul_eq_one he
  rw [sRes_swap_le P Q hQ hR0 hpq hkr, leadingCoeff_sResP_swap P Q hQ hR0 hpq hj1,
    proposition_8_39 P Q hQ hR0 hpq (i - 1) hi1, proposition_8_39 P Q hQ hR0 hpq (j - 1) hj1]
  simp only [← Int.cast_smul_eq_zsmul K, smul_eq_mul, smul_eq_C_mul, ← C_mul, ← mul_assoc]
  rw [mod_C_mul_right _ _ (mul_ne_zero hεne (pow_ne_zero _ (leadingCoeff_ne_zero.mpr hQ))),
    rem_C_mul]
  conv_rhs => rw [rem_C_mul, mul_neg, ← mul_assoc, ← C_mul]
  congr 2
  rw [Polynomial.C_inj, show 3 * (P.natDegree - (P % Q).natDegree)
    = (P.natDegree - (P % Q).natDegree) + (P.natDegree - (P % Q).natDegree)
      + (P.natDegree - (P % Q).natDegree) from by omega, pow_add, pow_add]
  linear_combination (((ε (P.natDegree - Q.natDegree) : ℤ) : K)
    * Q.leadingCoeff ^ (P.natDegree - (P % Q).natDegree)
    * Q.leadingCoeff ^ (P.natDegree - (P % Q).natDegree)
    * Q.leadingCoeff ^ (P.natDegree - (P % Q).natDegree)
    * Azurite.BPR.Chapter4.sRes Q (-(P % Q)) k
    * (sResP Q (-(P % Q)) (j - 1)).leadingCoeff) * he

/-- The deep recurrence transports: given the `(Q,-R)` recurrence at a deep triple, the
    `(P,Q)` recurrence at the same triple holds (uniform scaling, both sides). -/
theorem general_recurrence_transport (P Q : K[X]) (hQ : Q ≠ 0) (hR0 : P % Q ≠ 0)
    (hpq : Q.natDegree < P.natDegree) {i j k : ℕ}
    (hjr : j ≤ (P % Q).natDegree) (hkr : k ≤ (P % Q).natDegree)
    (hi1 : i - 1 < Q.natDegree - 1) (hj1 : j - 1 < Q.natDegree - 1) (hk1 : k - 1 < Q.natDegree - 1)
    (hrec : C (Azurite.BPR.Chapter4.sRes Q (-(P % Q)) j)
          * C (sResP Q (-(P % Q)) (i - 1)).leadingCoeff * sResP Q (-(P % Q)) (k - 1)
        = -((C (Azurite.BPR.Chapter4.sRes Q (-(P % Q)) k)
            * C (sResP Q (-(P % Q)) (j - 1)).leadingCoeff
            * sResP Q (-(P % Q)) (i - 1)) % sResP Q (-(P % Q)) (j - 1))) :
    C (Azurite.BPR.Chapter4.sRes P Q j) * C (sResP P Q (i - 1)).leadingCoeff * sResP P Q (k - 1)
      = -((C (Azurite.BPR.Chapter4.sRes P Q k) * C (sResP P Q (j - 1)).leadingCoeff
          * sResP P Q (i - 1)) % sResP P Q (j - 1)) := by
  rw [general_lhs_transport P Q hQ hR0 hpq hjr hi1 hk1, hrec,
    ← general_rhs_transport P Q hQ hR0 hpq hkr hj1 hi1]

/-- **Depth-general defective-block gap (the gap induction).**  For `m ≤ q` with
    `sResP_m(P,Q) ≠ 0` of degree `d = deg(sResP_m) < m`, every interior index
    `d < ℓ < m` of the defective block has `sResP_ℓ(P,Q) = 0`.  Same well-founded
    induction on `deg Q` as `sResP_block_associated`: vacuous when non-defective, the
    top step (`m = q-1`) is `sResP_eq_zero_of_step_gap`, the range `r < m < q-1` is
    excluded (it would force `sResP_m = 0`), and `m ≤ r` transports to `Q,-R`. -/
theorem sResP_block_gap (P Q : K[X]) (hP : P ≠ 0) (hQ : Q ≠ 0)
    (hpq : Q.natDegree < P.natDegree) {m : ℕ} (hmq : m ≤ Q.natDegree) (hm : sResP P Q m ≠ 0)
    {ℓ : ℕ} (hlo : (sResP P Q m).natDegree < ℓ) (hhi : ℓ < m) : sResP P Q ℓ = 0 := by
  suffices key : ∀ n, ∀ P Q : K[X], P ≠ 0 → Q ≠ 0 → Q.natDegree = n → Q.natDegree < P.natDegree →
      ∀ m, m ≤ Q.natDegree → sResP P Q m ≠ 0 → ∀ ℓ, (sResP P Q m).natDegree < ℓ → ℓ < m →
      sResP P Q ℓ = 0 from
    key Q.natDegree P Q hP hQ rfl hpq m hmq hm ℓ hlo hhi
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro P Q hP hQ hn hpq m hmq hm ℓ hlo hhi
    have hb : Q.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hQ
    have hεne : ((ε (P.natDegree - Q.natDegree) : ℤ) : K) ≠ 0 := by
      rw [Azurite.BPR.Chapter4.ε]; push_cast; exact pow_ne_zero _ (by norm_num)
    have hmq' : m < Q.natDegree := lt_of_le_of_ne hmq (by
      rintro rfl; rw [natDegree_sResP_natDegree P Q hQ hpq] at hlo; omega)
    have hR : P % Q ≠ 0 := by
      rintro hR0
      have hgcdq : (gcd P Q).natDegree = Q.natDegree :=
        le_antisymm (Polynomial.natDegree_le_of_dvd (gcd_dvd_right P Q) hQ)
          (Polynomial.natDegree_le_of_dvd
            (dvd_gcd (EuclideanDomain.mod_eq_zero.mp hR0) dvd_rfl)
            (fun h => hP (by simpa using (gcd_eq_zero_iff P Q).mp h |>.1)))
      exact hm (sResP_eq_zero_of_lt_gcd P Q hP hQ hpq hmq (by omega))
    have hrq : (P % Q).natDegree < Q.natDegree :=
      natDegree_lt_natDegree hR (degree_mod_lt P hQ)
    by_cases hmqm1 : m = Q.natDegree - 1
    · subst hmqm1
      rw [natDegree_sResP_natDegree_sub_one P Q hQ hR hpq (by omega)] at hlo
      exact sResP_eq_zero_of_step_gap P Q hQ hR hpq hlo hhi
    · by_cases hmr : m ≤ (P % Q).natDegree
      · have hmlt : m < Q.natDegree - 1 := by omega
        have hℓlt : ℓ < Q.natDegree - 1 := by omega
        have hSm' : sResP Q (-(P % Q)) m ≠ 0 := fun h => hm (by
          rw [proposition_8_39 P Q hQ hR hpq m hmlt, h]; simp)
        have hjeq' : (sResP P Q m).natDegree = (sResP Q (-(P % Q)) m).natDegree := by
          rw [proposition_8_39 P Q hQ hR hpq m hmlt, ← Int.cast_smul_eq_zsmul K, smul_smul,
            natDegree_smul _ (mul_ne_zero hεne (pow_ne_zero _ hb))]
        have hℓ0 : sResP Q (-(P % Q)) ℓ = 0 :=
          ih (P % Q).natDegree (hn ▸ hrq) Q (-(P % Q)) hQ (neg_ne_zero.mpr hR)
            (Polynomial.natDegree_neg _) (by rw [natDegree_neg]; exact hrq) m
            (by rw [natDegree_neg]; exact hmr) hSm' ℓ (by rw [← hjeq']; exact hlo) hhi
        rw [proposition_8_39 P Q hQ hR hpq ℓ hℓlt, hℓ0]; simp
      · exact absurd (sResP_eq_zero_of_step_gap P Q hQ hR hpq (by omega) (by omega)) hm

/-! ### The monolithic statement -/

/-- BPR's `s_j` with the convention `s_p = 1`. -/
noncomputable def sBPR (P Q : K[X]) (j : ℕ) : K :=
  if j = P.natDegree then 1 else Azurite.BPR.Chapter4.sRes P Q j

/-- BPR's `t_j = lcof(sResP_j)` with the convention `t_p = 1`. -/
noncomputable def tBPR (P Q : K[X]) (j : ℕ) : K :=
  if j = P.natDegree then 1 else (sResP P Q j).leadingCoeff

/-- **BPR Theorem 8.34 (Structure Theorem for Signed Subresultants) — monolithic form.**
    Let `0 ≤ j < i ≤ p+1` with `sResP_{i-1}(P,Q)` nonzero of degree `j` (and `1 ≤ j`).  Then:

    * **gcd branch** — if `sResP_{j-1}(P,Q) = 0`, then `sResP_{i-1}(P,Q)` is associate to
      `gcd(P,Q)`, and `sResP_ℓ(P,Q) = 0` for all `ℓ < j`;
    * **recurrence branch** — if `sResP_{j-1}(P,Q) ≠ 0` of degree `k`, then
      `s_j t_{i-1} sResP_{k-1}(P,Q) = -Rem(s_k t_{j-1} sResP_{i-1}(P,Q), sResP_{j-1}(P,Q))`,
      and moreover if `k < j-1` the gap subresultants vanish (`sResP_ℓ = 0` for `k < ℓ < j-1`)
      and `sResP_k(P,Q)` is proportional (associate) to `sResP_{j-1}(P,Q)`. -/
theorem theorem_8_34_monolithic (P Q : K[X]) (hP : P ≠ 0) (hQ : Q ≠ 0)
    (hpq : Q.natDegree < P.natDegree) (hq1 : 1 ≤ Q.natDegree) {i j : ℕ} (hj1 : 1 ≤ j) (hji : j < i)
    (hip : i ≤ P.natDegree + 1) (hne : sResP P Q (i - 1) ≠ 0)
    (hdeg : (sResP P Q (i - 1)).natDegree = j) :
    (sResP P Q (j - 1) = 0 →
        Associated (sResP P Q (i - 1)) (gcd P Q) ∧ ∀ ℓ, ℓ < j → sResP P Q ℓ = 0)
    ∧ (∀ k, sResP P Q (j - 1) ≠ 0 → (sResP P Q (j - 1)).natDegree = k →
        C (sBPR P Q j) * C (tBPR P Q (i - 1)) * (if k = 0 then 0 else sResP P Q (k - 1))
          = -((C (sBPR P Q k) * C (tBPR P Q (j - 1)) * sResP P Q (i - 1)) % sResP P Q (j - 1))
        ∧ (k < j - 1 →
            (∀ ℓ, k < ℓ → ℓ < j - 1 → sResP P Q ℓ = 0)
            ∧ Associated (sResP P Q k) (sResP P Q (j - 1)))) := by
  suffices key : ∀ n, ∀ P Q : K[X], P ≠ 0 → Q ≠ 0 → Q.natDegree < P.natDegree → 1 ≤ Q.natDegree →
      Q.natDegree = n → ∀ i j, 1 ≤ j → j < i → i ≤ P.natDegree + 1 → sResP P Q (i - 1) ≠ 0 →
      (sResP P Q (i - 1)).natDegree = j →
      (sResP P Q (j - 1) = 0 →
          Associated (sResP P Q (i - 1)) (gcd P Q) ∧ ∀ ℓ, ℓ < j → sResP P Q ℓ = 0)
      ∧ (∀ k, sResP P Q (j - 1) ≠ 0 → (sResP P Q (j - 1)).natDegree = k →
          C (sBPR P Q j) * C (tBPR P Q (i - 1)) * (if k = 0 then 0 else sResP P Q (k - 1))
            = -((C (sBPR P Q k) * C (tBPR P Q (j - 1)) * sResP P Q (i - 1)) % sResP P Q (j - 1))
          ∧ (k < j - 1 →
              (∀ ℓ, k < ℓ → ℓ < j - 1 → sResP P Q ℓ = 0)
              ∧ Associated (sResP P Q k) (sResP P Q (j - 1)))) from
    key Q.natDegree P Q hP hQ hpq hq1 rfl i j hj1 hji hip hne hdeg
  clear hP hQ hpq hq1 hne hdeg hj1 hji hip i j
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro P Q hP hQ hpq hq1 hn i j hj1 hji hip hne hdeg
  have hgcd_ne : gcd P Q ≠ 0 := fun h => hP (by simpa using (gcd_eq_zero_iff P Q).mp h |>.1)
  refine ⟨fun hzero => ?_, fun k hk0 hkdeg => ⟨?_, fun hkj => ?_⟩⟩
  · -- gcd branch
    by_cases hiq : i - 1 ≤ Q.natDegree
    · exact theorem_8_34_gcd_branch_general P Q hP hQ hpq hiq hne hdeg hj1 hzero
    · by_cases hip2 : i - 1 = P.natDegree
      · exfalso
        have hjp : j = P.natDegree := by rw [hip2, sResP_eq_self P Q hpq] at hdeg; exact hdeg.symm
        rw [hjp, sResP_pm1_eq_Q P Q hQ hpq] at hzero
        exact hQ hzero
      · have hip3 : i - 1 = P.natDegree - 1 := by
          by_contra h; exact hne (sResP_eq_zero P Q (by omega) hip2 h)
        have hjq : j = Q.natDegree := by
          rw [hip3, sResP_pm1_eq_Q P Q hQ hpq] at hdeg; exact hdeg.symm
        rw [hjq] at hzero
        have hdvd : Q ∣ P :=
          (sResP_natDegree_sub_one_eq_zero_iff P Q hP hQ hpq (by omega)).mp hzero
        have hgq : (gcd P Q).natDegree = Q.natDegree :=
          le_antisymm (Polynomial.natDegree_le_of_dvd (gcd_dvd_right P Q) hQ)
            (Polynomial.natDegree_le_of_dvd (dvd_gcd hdvd dvd_rfl) hgcd_ne)
        refine ⟨?_, fun ℓ hℓ => sResP_eq_zero_of_lt_gcd P Q hP hQ hpq (by omega) (by omega)⟩
        rw [hip3, sResP_pm1_eq_Q P Q hQ hpq]
        obtain ⟨c, hc⟩ := gcd_dvd_right P Q
        have hc_ne : c ≠ 0 := fun h => hQ (by rw [hc, h, mul_zero])
        have hc0 : c.natDegree = 0 := by
          have := Polynomial.natDegree_mul hgcd_ne hc_ne; rw [← hc, hgq] at this; omega
        have huc : IsUnit c := Polynomial.isUnit_iff_degree_eq_zero.mpr
          (by rw [Polynomial.degree_eq_natDegree hc_ne, hc0]; rfl)
        have h := associated_mul_unit_left (gcd P Q) c huc; rwa [← hc] at h
  · -- recurrence branch
    by_cases hk0' : k = 0
    · -- k = 0: BPR's terminus convention `sResP_{-1} = 0`.  `sResP_{j-1}` is then a nonzero
      -- constant (a unit), so the LHS is `0` and the remainder on the RHS also vanishes.
      subst hk0'
      rw [ite_eq_left rfl, mul_zero]
      have hunit : IsUnit (sResP P Q (j - 1)) := Polynomial.isUnit_iff_degree_eq_zero.mpr (by
        rw [Polynomial.degree_eq_natDegree hk0, hkdeg]; simp)
      rw [EuclideanDomain.mod_eq_zero.mpr hunit.dvd, neg_zero]
    rw [ite_eq_right hk0']
    have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk0'
    by_cases hip2 : i - 1 = P.natDegree
    · -- i-1 = p: base case (s_p = t_p = 1), with terminal sub-case `Q ∣ P`
      have hjp : j = P.natDegree := by rw [hip2, sResP_eq_self P Q hpq] at hdeg; exact hdeg.symm
      have hQj : sResP P Q (j - 1) = Q := by rw [hjp, sResP_pm1_eq_Q P Q hQ hpq]
      have hkq : k = Q.natDegree := by rw [hQj] at hkdeg; exact hkdeg.symm
      have hsk : sBPR P Q k = Azurite.BPR.Chapter4.sRes P Q k := by
        rw [sBPR, ite_eq_right (show k ≠ P.natDegree by omega)]
      have htj : tBPR P Q (j - 1) = (sResP P Q (j - 1)).leadingCoeff := by
        rw [tBPR, ite_eq_right (show j - 1 ≠ P.natDegree by omega)]
      rw [sBPR, ite_eq_left hjp, tBPR, ite_eq_left hip2, hsk, htj, hip2]
      simp only [map_one, one_mul]
      by_cases hR0 : P % Q = 0
      · -- terminal: both sides vanish
        have hgq : (gcd P Q).natDegree = Q.natDegree :=
          le_antisymm (Polynomial.natDegree_le_of_dvd (gcd_dvd_right P Q) hQ)
            (Polynomial.natDegree_le_of_dvd
              (dvd_gcd (EuclideanDomain.mod_eq_zero.mp hR0) dvd_rfl) hgcd_ne)
        rw [hkq, hQj, sResP_eq_zero_of_lt_gcd P Q hP hQ hpq (by omega) (by omega),
          sResP_eq_self P Q hpq,
          EuclideanDomain.mod_eq_zero.mpr ((EuclideanDomain.mod_eq_zero.mp hR0).mul_left _),
          neg_zero]
      · rw [hkq, hjp]
        exact sResP_natDegree_sub_one_rem' P Q hQ hR0 hpq (by omega)
    · -- i-1 < p: genuine `s`/`t`
      have hi1p : i - 1 < P.natDegree := by omega
      have hjle : j ≤ i - 1 := by
        rw [← hdeg]
        rcases Nat.lt_or_ge (i - 1) (Q.natDegree + 1) with h | h
        · exact Polynomial.natDegree_le_iff_degree_le.mpr (sResP_degree_le P Q hpq (by omega))
        · have hip3 : i - 1 = P.natDegree - 1 := by
            by_contra hc; exact hne (sResP_eq_zero P Q (by omega) hip2 hc)
          rw [hip3, sResP_pm1_eq_Q P Q hQ hpq]; omega
      have hjq : j ≤ Q.natDegree := by
        rcases Nat.lt_or_ge (i - 1) (Q.natDegree + 1) with h | h
        · omega
        · have hip3 : i - 1 = P.natDegree - 1 := by
            by_contra hc; exact hne (sResP_eq_zero P Q (by omega) hip2 hc)
          rw [hip3, sResP_pm1_eq_Q P Q hQ hpq] at hdeg; omega
      have hkle : k ≤ j - 1 := by
        rw [← hkdeg]
        exact Polynomial.natDegree_le_iff_degree_le.mpr (sResP_degree_le P Q hpq (by omega))
      rw [sBPR, ite_eq_right (show j ≠ P.natDegree by omega), tBPR, ite_eq_right (show i - 1 ≠ P.natDegree by omega),
        sBPR, ite_eq_right (show k ≠ P.natDegree by omega), tBPR, ite_eq_right (show j - 1 ≠ P.natDegree by omega)]
      by_cases hiq2 : i - 1 ≤ Q.natDegree - 1
      · -- i-1 ≤ q-1 ⟹ P % Q ≠ 0
        have hR0 : P % Q ≠ 0 := by
          intro h
          have hgq : (gcd P Q).natDegree = Q.natDegree :=
            le_antisymm (Polynomial.natDegree_le_of_dvd (gcd_dvd_right P Q) hQ)
              (Polynomial.natDegree_le_of_dvd
                (dvd_gcd (EuclideanDomain.mod_eq_zero.mp h) dvd_rfl) hgcd_ne)
          exact hne (sResP_eq_zero_of_lt_gcd P Q hP hQ hpq (by omega) (by omega))
        have hrq : (P % Q).natDegree < Q.natDegree :=
          natDegree_lt_natDegree hR0 (degree_mod_lt P hQ)
        have hb : Q.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hQ
        have hεne : ((ε (P.natDegree - Q.natDegree) : ℤ) : K) ≠ 0 := by
          rw [Azurite.BPR.Chapter4.ε]; push_cast; exact pow_ne_zero _ (by norm_num)
        by_cases hi1q : i - 1 < Q.natDegree - 1
        · -- DEEP: all indices below q-1, transport from (Q,-R) via the IH
          have hir : i - 1 ≤ (P % Q).natDegree := by
            by_contra h
            exact hne (sResP_eq_zero_of_step_gap P Q hQ hR0 hpq (by omega) hi1q)
          have hsi : sResP Q (-(P % Q)) (i - 1) ≠ 0 := fun h => hne (by
            rw [proposition_8_39 P Q hQ hR0 hpq (i - 1) (by omega), h]; simp)
          have hsdeg : (sResP Q (-(P % Q)) (i - 1)).natDegree = j := by
            rw [← hdeg, proposition_8_39 P Q hQ hR0 hpq (i - 1) (by omega),
              ← Int.cast_smul_eq_zsmul K, smul_smul, natDegree_smul _ (mul_ne_zero hεne (pow_ne_zero _ hb))]
          have hQk : sResP Q (-(P % Q)) (j - 1) ≠ 0 := fun h => hk0 (by
            rw [proposition_8_39 P Q hQ hR0 hpq (j - 1) (by omega), h]; simp)
          have hQkdeg : (sResP Q (-(P % Q)) (j - 1)).natDegree = k := by
            rw [← hkdeg, proposition_8_39 P Q hQ hR0 hpq (j - 1) (by omega),
              ← Int.cast_smul_eq_zsmul K, smul_smul, natDegree_smul _ (mul_ne_zero hεne (pow_ne_zero _ hb))]
          have hih2 := ih (P % Q).natDegree (by omega) Q (-(P % Q)) hQ (neg_ne_zero.mpr hR0)
            (by rw [natDegree_neg]; exact hrq) (by rw [natDegree_neg]; omega)
            (Polynomial.natDegree_neg _) i j hj1 hji (by omega) hsi hsdeg
          obtain ⟨hrec, _⟩ := hih2.2 k hQk hQkdeg
          rw [ite_eq_right hk0', sBPR, ite_eq_right (show j ≠ Q.natDegree by omega),
            tBPR, ite_eq_right (show i - 1 ≠ Q.natDegree by omega),
            sBPR, ite_eq_right (show k ≠ Q.natDegree by omega),
            tBPR, ite_eq_right (show j - 1 ≠ Q.natDegree by omega)] at hrec
          exact general_recurrence_transport P Q hQ hR0 hpq (by omega) (by omega)
            (by omega) (by omega) (by omega) hrec
        · -- i-1 = q-1: boundary, transport (Q,-R)'s top recurrence via the IH
          have hi1eq : i - 1 = Q.natDegree - 1 := by omega
          have hjr : j = (P % Q).natDegree := by
            rw [← hdeg, hi1eq, natDegree_sResP_natDegree_sub_one P Q hQ hR0 hpq (by omega)]
          have hgcd_ne' : gcd Q (-(P % Q)) ≠ 0 :=
            fun hc => hQ (by simpa using (gcd_eq_zero_iff Q (-(P % Q))).mp hc |>.1)
          have hR'0 : Q % (-(P % Q)) ≠ 0 := by
            intro h
            have hdvd : -(P % Q) ∣ Q := EuclideanDomain.mod_eq_zero.mp h
            have hgq' : (gcd Q (-(P % Q))).natDegree = (P % Q).natDegree := by
              rw [show (P % Q).natDegree = (-(P % Q)).natDegree from (natDegree_neg _).symm]
              exact le_antisymm
                (Polynomial.natDegree_le_of_dvd (gcd_dvd_right Q _) (neg_ne_zero.mpr hR0))
                (Polynomial.natDegree_le_of_dvd (dvd_gcd hdvd dvd_rfl) hgcd_ne')
            apply hk0
            rw [show j - 1 = (P % Q).natDegree - 1 from by omega]
            exact sResP_eq_zero_of_lt_gcd P Q hP hQ hpq (by omega)
              (by rw [natDegree_gcd_step P Q hP hQ, hgq']; omega)
          have hk_eq : k = (Q % (-(P % Q))).natDegree := by
            rw [← hkdeg, show j - 1 = (P % Q).natDegree - 1 from by omega,
              proposition_8_39 P Q hQ hR0 hpq ((P % Q).natDegree - 1) (by omega),
              ← Int.cast_smul_eq_zsmul K, smul_smul,
              natDegree_smul _ (mul_ne_zero hεne (pow_ne_zero _ hb)),
              show (P % Q).natDegree - 1 = (-(P % Q)).natDegree - 1 from by rw [natDegree_neg],
              natDegree_sResP_natDegree_sub_one Q (-(P % Q)) (neg_ne_zero.mpr hR0) hR'0
                (by rw [natDegree_neg]; exact hrq) (by rw [natDegree_neg]; omega)]
          have hsQ : sResP Q (-(P % Q)) (Q.natDegree - 1) = -(P % Q) :=
            sResP_pm1_eq_Q Q (-(P % Q)) (neg_ne_zero.mpr hR0) (by rw [natDegree_neg]; exact hrq)
          have hih2 := ih (P % Q).natDegree (by omega) Q (-(P % Q)) hQ (neg_ne_zero.mpr hR0)
            (by rw [natDegree_neg]; exact hrq) (by rw [natDegree_neg]; omega)
            (Polynomial.natDegree_neg _) Q.natDegree (P % Q).natDegree (by omega) (by omega) (by omega)
            (by rw [hsQ]; exact neg_ne_zero.mpr hR0) (by rw [hsQ, natDegree_neg])
          have hQk : sResP Q (-(P % Q)) ((P % Q).natDegree - 1) ≠ 0 := fun h => hk0 (by
            rw [show j - 1 = (P % Q).natDegree - 1 from by omega,
              proposition_8_39 P Q hQ hR0 hpq ((P % Q).natDegree - 1) (by omega), h]; simp)
          have hQkdeg : (sResP Q (-(P % Q)) ((P % Q).natDegree - 1)).natDegree = k := by
            rw [show (P % Q).natDegree - 1 = (-(P % Q)).natDegree - 1 from by rw [natDegree_neg],
              natDegree_sResP_natDegree_sub_one Q (-(P % Q)) (neg_ne_zero.mpr hR0) hR'0
                (by rw [natDegree_neg]; exact hrq) (by rw [natDegree_neg]; omega), hk_eq]
          obtain ⟨hrec, _⟩ := hih2.2 k hQk hQkdeg
          rw [ite_eq_right hk0', sBPR, ite_eq_right (show (P % Q).natDegree ≠ Q.natDegree by omega),
            tBPR, ite_eq_right (show Q.natDegree - 1 ≠ Q.natDegree by omega),
            sBPR, ite_eq_right (show k ≠ Q.natDegree by omega),
            tBPR, ite_eq_right (show (P % Q).natDegree - 1 ≠ Q.natDegree by omega)] at hrec
          rw [hjr, hi1eq, hk_eq, show (P % Q).natDegree - 1 = (P % Q).natDegree - 1 from rfl]
          exact recurrence_transport P Q hQ hR0 hpq (by omega) (by omega) (by omega) (by omega)
            (by rw [← hk_eq]; exact hrec)
      · -- i-1 ≥ q: i-1 ∈ {q, p-1}, j = q
        have hi1cases : i - 1 = Q.natDegree ∨ i - 1 = P.natDegree - 1 := by
          rcases eq_or_lt_of_le (show Q.natDegree ≤ i - 1 from by omega) with h | h
          · exact Or.inl h.symm
          · exact Or.inr (by by_contra hc; exact hne (sResP_eq_zero P Q (by omega) (by omega) hc))
        have hjq2 : j = Q.natDegree := by
          rcases hi1cases with h | h
          · rw [← hdeg, h, natDegree_sResP_natDegree P Q hQ hpq]
          · rw [← hdeg, h, sResP_pm1_eq_Q P Q hQ hpq]
        have hR0 : P % Q ≠ 0 := by
          intro hR0
          have hgq : (gcd P Q).natDegree = Q.natDegree :=
            le_antisymm (Polynomial.natDegree_le_of_dvd (gcd_dvd_right P Q) hQ)
              (Polynomial.natDegree_le_of_dvd
                (dvd_gcd (EuclideanDomain.mod_eq_zero.mp hR0) dvd_rfl) hgcd_ne)
          exact hk0 (by rw [hjq2]; exact sResP_eq_zero_of_lt_gcd P Q hP hQ hpq (by omega) (by omega))
        have hrq : (P % Q).natDegree < Q.natDegree :=
          natDegree_lt_natDegree hR0 (degree_mod_lt P hQ)
        have hkr : k = (P % Q).natDegree := by
          rw [← hkdeg, hjq2, natDegree_sResP_natDegree_sub_one P Q hQ hR0 hpq (by omega)]
        have hr1 : 1 ≤ (P % Q).natDegree := hkr ▸ hk1
        by_cases hR'0 : Q % (-(P % Q)) = 0
        · -- terminal-2: Q % (-R) = 0, so deg gcd = r; LHS `sResP_{k-1}` vanishes, RHS `Rem` vanishes
          have hdvd : -(P % Q) ∣ Q := EuclideanDomain.mod_eq_zero.mp hR'0
          have hgcd_ne' : gcd Q (-(P % Q)) ≠ 0 :=
            fun hc => hQ (by simpa using (gcd_eq_zero_iff Q (-(P % Q))).mp hc |>.1)
          have hgr : (gcd P Q).natDegree = (P % Q).natDegree := by
            rw [natDegree_gcd_step P Q hP hQ,
              show (P % Q).natDegree = (-(P % Q)).natDegree from (natDegree_neg _).symm]
            exact le_antisymm
              (Polynomial.natDegree_le_of_dvd (gcd_dvd_right Q _) (neg_ne_zero.mpr hR0))
              (Polynomial.natDegree_le_of_dvd (dvd_gcd hdvd dvd_rfl) hgcd_ne')
          have hassoc : Associated (gcd P Q) (sResP P Q (j - 1)) :=
            Polynomial.associated_of_dvd_of_natDegree_le
              (gcd_dvd_sResP_all P Q hP hQ hpq _) hk0 (le_of_eq (by rw [hkdeg, hgr, hkr]))
          have hjdvd : sResP P Q (j - 1) ∣ sResP P Q (i - 1) :=
            hassoc.symm.dvd.trans (gcd_dvd_sResP_all P Q hP hQ hpq _)
          have hLHS0 : sResP P Q ((P % Q).natDegree - 1) = 0 :=
            sResP_eq_zero_of_lt_gcd P Q hP hQ hpq (by omega) (by rw [hgr]; omega)
          rw [hkr, hLHS0, mul_zero,
            EuclideanDomain.mod_eq_zero.mpr (hjdvd.mul_left _), neg_zero]
        · -- ★ case: `Q % (-R) ≠ 0`, the inductive-step identity applies
          have hstar := sResP_inductive_step_identity P Q hQ hR0 hpq hr1 hR'0
          rcases hi1cases with h | h
          · -- i-1 = q: `sResP_q = C w * Q`, the recurrence is `C w ·` the identity
            obtain ⟨w, hsResPq⟩ : ∃ w : K, sResP P Q (i - 1) = C w * Q :=
              ⟨_, by rw [h, sResP_eq_of_natDegree P Q hpq hQ, ← Int.cast_smul_eq_zsmul K,
                smul_eq_C_mul, ← mul_assoc, ← C_mul]⟩
            rw [sResP_pm1_eq_Q P Q hQ hpq] at hstar
            rw [hjq2, hkr, hsResPq,
              show (C w * Q).leadingCoeff = w * Q.leadingCoeff from by
                rw [leadingCoeff_mul, leadingCoeff_C],
              C_mul,
              show C (Azurite.BPR.Chapter4.sRes P Q (P % Q).natDegree)
                    * C (sResP P Q (Q.natDegree - 1)).leadingCoeff * (C w * Q)
                  = C w * (C (Azurite.BPR.Chapter4.sRes P Q (P % Q).natDegree)
                    * C (sResP P Q (Q.natDegree - 1)).leadingCoeff * Q) from by ring,
              rem_C_mul]
            linear_combination C w * hstar
          · -- i-1 = p-1: `sResP_{i-1} = sResP_{p-1}`, the identity holds verbatim
            rw [hjq2, hkr, h]; exact hstar
  · -- proportionality: the defective block at `j-1` (degree `k < j-1`)
    by_cases hip2 : i - 1 = P.natDegree
    · -- i-1 = p: `j = p`, `sResP_{j-1} = Q` of degree `k = q`; top defective block
      have hεne : ((ε (P.natDegree - Q.natDegree) : ℤ) : K) ≠ 0 := by
        rw [Azurite.BPR.Chapter4.ε]; push_cast; exact pow_ne_zero _ (by norm_num)
      have hjp : j = P.natDegree := by rw [← hdeg, hip2, sResP_eq_self P Q hpq]
      have hkq : k = Q.natDegree := by rw [← hkdeg, hjp, sResP_pm1_eq_Q P Q hQ hpq]
      refine ⟨fun ℓ hℓlo hℓhi => ?_, ?_⟩
      · exact sResP_eq_zero P Q (by rw [← hkq]; exact hℓlo) (by omega) (by omega)
      · obtain ⟨w, hsResPq, hwne⟩ : ∃ w : K, sResP P Q Q.natDegree = C w * Q ∧ w ≠ 0 :=
          ⟨_, by rw [sResP_eq_of_natDegree P Q hpq hQ, ← Int.cast_smul_eq_zsmul K, smul_eq_C_mul,
              ← mul_assoc, ← C_mul],
            mul_ne_zero hεne (pow_ne_zero _ (leadingCoeff_ne_zero.mpr hQ))⟩
        rw [hkq, hjp, sResP_pm1_eq_Q P Q hQ hpq, hsResPq]
        exact associated_unit_mul_left Q (C w) (isUnit_C.mpr (isUnit_iff_ne_zero.mpr hwne))
    · -- i-1 < p: `j ≤ q`; transport the block lemmas
      have hjq : j ≤ Q.natDegree := by
        by_cases hiq : i - 1 ≤ Q.natDegree
        · rw [← hdeg]
          exact le_trans
            (Polynomial.natDegree_le_iff_degree_le.mpr (sResP_degree_le P Q hpq hiq)) hiq
        · have hip3 : i - 1 = P.natDegree - 1 := by
            by_contra hc; exact hne (sResP_eq_zero P Q (by omega) hip2 hc)
          rw [← hdeg, hip3, sResP_pm1_eq_Q P Q hQ hpq]
      refine ⟨fun ℓ hℓlo hℓhi => ?_, ?_⟩
      · exact sResP_block_gap P Q hP hQ hpq (by omega) hk0 (by rw [hkdeg]; exact hℓlo) hℓhi
      · have hA := sResP_block_associated P Q hP hQ hpq (show j - 1 ≤ Q.natDegree from by omega) hk0
        rw [hkdeg] at hA; exact hA

/-! ### The packaged structure theorem (top-step specialization of the monolith) -/

/-- **BPR Theorem 8.34 (Structure Theorem for Signed Subresultants).**  Packaged form,
    over a field `K`, for `deg Q < deg P`.  Two structural conclusions:

  * **gcd branch** (always): the signed subresultants below `deg(gcd P Q)` vanish, and the
    one at index `deg(gcd P Q)` is associate to `gcd P Q`.  (This is BPR's `sResP_{j-1} = 0
    ⟹ sResP_{i-1} = gcd, sResP_ℓ = 0 for ℓ ≤ j-1`, stated via `deg gcd`; faithfully an
    associateness, since our `sResP` is not normalized.)

  * **recurrence branch** (for *any* Euclidean step `P,Q → Q,-R`, `R = P % Q`, with `R ≠ 0`):
    the structure-theorem recurrence
    `s_q t_{p-1} sResP_{r-1}(P,Q) = -Rem(s_r t_{q-1} sResP_{p-1}(P,Q), sResP_{q-1}(P,Q))`
    holds (with BPR's terminus convention `sResP_{-1} = 0` when `r = 0` — the coprime
    bottom, encoded as `if r = 0 then 0 else sResP_{r-1}`), the subresultants in the degree
    gap `r < ℓ < q-1` vanish, and `sResP_r(P,Q)` is proportional to `sResP_{q-1}(P,Q)`.

  This is the `i = p, j = q` specialization of `theorem_8_34_monolithic`; the only hypothesis
  on the recurrence branch is `P % Q ≠ 0` (it needs neither `1 ≤ r` nor `Q % (-R) ≠ 0` —
  both the coprime terminus `r = 0` and the terminal `Q % (-R) = 0` are covered). -/
theorem theorem_8_34 (P Q : K[X]) (hP : P ≠ 0) (hQ : Q ≠ 0)
    (hpq : Q.natDegree < P.natDegree) :
    -- gcd branch (unconditional):
    ((∀ ℓ, ℓ < (gcd P Q).natDegree → sResP P Q ℓ = 0)
        ∧ Associated (sResP P Q (gcd P Q).natDegree) (gcd P Q))
    ∧ -- recurrence branch (any Euclidean step with nonzero remainder):
    (P % Q ≠ 0 →
      (C (Azurite.BPR.Chapter4.sRes P Q Q.natDegree)
            * C (sResP P Q (P.natDegree - 1)).leadingCoeff
            * (if (P % Q).natDegree = 0 then 0 else sResP P Q ((P % Q).natDegree - 1))
          = -((C (Azurite.BPR.Chapter4.sRes P Q (P % Q).natDegree)
              * C (sResP P Q (Q.natDegree - 1)).leadingCoeff
              * sResP P Q (P.natDegree - 1)) % sResP P Q (Q.natDegree - 1)))
      ∧ (∀ ℓ, (P % Q).natDegree < ℓ → ℓ < Q.natDegree - 1 → sResP P Q ℓ = 0)
      ∧ Associated (sResP P Q (P % Q).natDegree) (sResP P Q (Q.natDegree - 1))) := by
  refine ⟨⟨fun ℓ hℓ => ?_, associated_sResP_gcd P Q hP hQ hpq rfl⟩, fun hR0 => ?_⟩
  · exact sResP_eq_zero_of_lt_gcd P Q hP hQ hpq
      (le_trans hℓ.le (Polynomial.natDegree_le_of_dvd (gcd_dvd_right P Q) hQ)) hℓ
  · -- specialize the monolith at `i = p`, `j = q` (so `sResP_{i-1} = sResP_{p-1} = Q`)
    have hq1 : 1 ≤ Q.natDegree := by
      rcases Nat.eq_zero_or_pos Q.natDegree with h | h
      · exact absurd (EuclideanDomain.mod_eq_zero.mpr
          ((Polynomial.isUnit_iff_degree_eq_zero.mpr
            (by rw [Polynomial.degree_eq_natDegree hQ, h]; simp)).dvd)) hR0
      · exact h
    have hrq : (P % Q).natDegree < Q.natDegree :=
      natDegree_lt_natDegree hR0 (degree_mod_lt P hQ)
    have hQpm1 : sResP P Q (P.natDegree - 1) = Q := sResP_pm1_eq_Q P Q hQ hpq
    have hk0 : sResP P Q (Q.natDegree - 1) ≠ 0 := fun h =>
      hR0 (EuclideanDomain.mod_eq_zero.mpr
        ((sResP_natDegree_sub_one_eq_zero_iff P Q hP hQ hpq hq1).mp h))
    have hkdeg : (sResP P Q (Q.natDegree - 1)).natDegree = (P % Q).natDegree :=
      natDegree_sResP_natDegree_sub_one P Q hQ hR0 hpq hq1
    obtain ⟨heq, hprop⟩ := (theorem_8_34_monolithic P Q hP hQ hpq hq1
      (i := P.natDegree) (j := Q.natDegree) hq1 hpq (by omega)
      (by rw [hQpm1]; exact hQ) (by rw [hQpm1])).2 (P % Q).natDegree hk0 hkdeg
    refine ⟨?_, ?_, ?_⟩
    · rw [sBPR, ite_eq_right (show Q.natDegree ≠ P.natDegree by omega),
        tBPR, ite_eq_right (show P.natDegree - 1 ≠ P.natDegree by omega),
        sBPR, ite_eq_right (show (P % Q).natDegree ≠ P.natDegree by omega),
        tBPR, ite_eq_right (show Q.natDegree - 1 ≠ P.natDegree by omega)] at heq
      exact heq
    · exact fun ℓ h1 h2 => (hprop (by omega)).1 ℓ h1 h2
    · by_cases hrq1 : (P % Q).natDegree < Q.natDegree - 1
      · exact (hprop hrq1).2
      · rw [show (P % Q).natDegree = Q.natDegree - 1 from by omega]

end Azurite.BPR.Chapter8
