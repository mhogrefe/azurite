import Azurite.BasuPollackRoy.Chapter8.Section8_3.Corollary_8_35

/-!
# BPR Proposition 8.46: defective-block structure (proportionality core)

In a defective block — `sResP_j(P,Q)` non-defective of degree `j`, and `sResP_{j-1}(P,Q)`
nonzero of degree `k ≤ j-1` — the non-defective representative `sResP_k(P,Q)` at the bottom of
the block is an explicit scalar multiple of `sResP_{j-1}(P,Q)`:

  `sResP_k = (s_k / t_{j-1}) · sResP_{j-1}`,

where `s_k = sRes_k(P,Q)` is the leading coefficient of `sResP_k` (non-defective) and
`t_{j-1}` is the leading coefficient of the defective `sResP_{j-1}`.  This is the proportionality
heart of Proposition 8.46.

BPR's full statement makes the constant explicit via the auxiliary sequence
`S_{j-1-δ} = ((-1)^δ t_{j-1} S_{j-δ}) / s_j` (`S_{j-1} = sResP_{j-1}`), giving
`sResP_k = S_k = (-1)^{(j-k-1)(j-k)/2} (t_{j-1}/s_j)^{j-k-1} sResP_{j-1}`.  Equating the two forms
amounts to the scalar identity
  `s_k = (-1)^{(j-k-1)(j-k)/2} t_{j-1}^{j-k} / s_j^{j-k-1}`,
which BPR extracts from the polynomial determinants of the monomial-augmented matrices
`M_{j-1-δ}`.  That determinant computation is not yet formalized; the proportionality below is
the part provable from the structure theorem (Theorem 8.34 / `sResP_block_associated`).
-/

namespace Azurite.BPR.Chapter8

open Polynomial

variable {K : Type*} [Field K]

/-- Two associate polynomials differ by the constant ratio of their leading coefficients:
    `a = C(lcof a / lcof b) · b`. -/
theorem eq_C_leadingCoeff_ratio_mul_of_associated {a b : K[X]} (hb : b ≠ 0)
    (hab : Associated a b) :
    a = C (a.leadingCoeff / b.leadingCoeff) * b := by
  obtain ⟨u, hu⟩ := hab
  obtain ⟨c, hc0, hcu⟩ := Polynomial.isUnit_iff.mp u.isUnit
  have hcne : c ≠ 0 := hc0.ne_zero
  have ha0 : a ≠ 0 := fun h => hb (by rw [← hu, h, zero_mul])
  have hla : a.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr ha0
  have hca : b = C c * a := by rw [← hu, ← hcu]; ring
  have hlb : b.leadingCoeff = c * a.leadingCoeff := by
    rw [hca, Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C]
  rw [hlb, hca, ← mul_assoc, ← Polynomial.C_mul,
    show a.leadingCoeff / (c * a.leadingCoeff) * c = 1 by field_simp, Polynomial.C_1, one_mul]

/-- Pure-algebra core of the base case: the explicit `q-1` values, substituted, collapse to an
    identity that holds once `ε(q-r)` is recognized as the sign `(-1)^{(q-r-1)(q-r)/2}`.  The
    exponents are passed with their additive relations so `ring` sees no nat-subtraction. -/
private theorem star_base_alg (pr pq pq1 qr qr1 hf : ℕ) (epsE epsD1 b mc : K)
    (h1 : pr = pq + qr) (h2 : pq1 = pq + 1) (h3 : qr = qr1 + 1)
    (heps : epsD1 = (-1 : K) ^ hf) :
    epsE * b ^ pr * epsD1 * mc ^ qr * (epsE * b ^ pq) ^ qr1
      = (-1 : K) ^ hf * (epsE * b ^ pq1 * mc) ^ qr := by
  subst h1 h2 h3 heps; ring

/-- **BPR Proposition 8.46, base case `j = q` (cleared identity (★')).**  When the first step is
    defective (`r := deg(P%Q) < q-1`), `sRes_r · sRes_q^{q-r-1} = (-1)^{(q-r-1)(q-r)/2} · t_{q-1}^{q-r}`. -/
private theorem star_base (P Q : K[X]) (hQ : Q ≠ 0)
    (hpq : Q.natDegree < P.natDegree) (hq1 : 1 ≤ Q.natDegree) (hR0 : P % Q ≠ 0)
    (hr : (P % Q).natDegree < Q.natDegree - 1) :
    Azurite.BPR.Chapter4.sRes P Q (P % Q).natDegree
        * Azurite.BPR.Chapter4.sRes P Q Q.natDegree
            ^ (Q.natDegree - (P % Q).natDegree - 1)
      = (-1 : K) ^ ((Q.natDegree - (P % Q).natDegree - 1) * (Q.natDegree - (P % Q).natDegree) / 2)
        * (sResP P Q (Q.natDegree - 1)).leadingCoeff ^ (Q.natDegree - (P % Q).natDegree) := by
  have hsq : Azurite.BPR.Chapter4.sRes P Q Q.natDegree
      = (↑(Chapter4.ε (P.natDegree - Q.natDegree)) : K)
        * Q.leadingCoeff ^ (P.natDegree - Q.natDegree) := by
    rw [sRes_natDegree P Q hpq hQ, zsmul_eq_mul]
  have htq1 : (sResP P Q (Q.natDegree - 1)).leadingCoeff
      = (↑(Chapter4.ε (P.natDegree - Q.natDegree)) : K)
        * Q.leadingCoeff ^ (P.natDegree - Q.natDegree + 1) * (-(P % Q).leadingCoeff) := by
    rw [leadingCoeff_sResP_natDegree_sub_one_swap P Q hQ hR0 hpq hq1,
      sResP_pm1_eq_Q Q (-(P % Q)) (neg_ne_zero.mpr hR0) (by rw [natDegree_neg]; omega),
      leadingCoeff_neg, zsmul_eq_mul, smul_eq_mul]
    ring
  have hsr : Azurite.BPR.Chapter4.sRes P Q (P % Q).natDegree
      = (↑(Chapter4.ε (P.natDegree - Q.natDegree)) : K)
        * Q.leadingCoeff ^ (P.natDegree - (P % Q).natDegree)
        * (↑(Chapter4.ε (Q.natDegree - (P % Q).natDegree)) : K)
        * (-(P % Q).leadingCoeff) ^ (Q.natDegree - (P % Q).natDegree) := by
    rw [← coeff_sResP P Q hpq (show (P % Q).natDegree ≤ P.natDegree by omega),
      sResP_propto_le_r P Q hQ hR0 hpq (le_refl _),
      ← Int.cast_smul_eq_zsmul K, smul_smul, Polynomial.coeff_smul, smul_eq_mul,
      coeff_sResP Q (-(P % Q)) (by rw [natDegree_neg]; omega) (by omega),
      show (P % Q).natDegree = (-(P % Q)).natDegree from (natDegree_neg _).symm,
      sRes_natDegree Q (-(P % Q)) (by rw [natDegree_neg]; omega) (neg_ne_zero.mpr hR0),
      zsmul_eq_mul, natDegree_neg, leadingCoeff_neg]
    ring
  have heps : (↑(Chapter4.ε (Q.natDegree - (P % Q).natDegree)) : K)
      = (-1 : K) ^ ((Q.natDegree - (P % Q).natDegree - 1) * (Q.natDegree - (P % Q).natDegree) / 2) := by
    rw [Chapter4.ε]; push_cast; congr 1; rw [Nat.mul_comm]
  rw [hsr, hsq, htq1]
  exact star_base_alg (P.natDegree - (P % Q).natDegree) (P.natDegree - Q.natDegree)
    (P.natDegree - Q.natDegree + 1) (Q.natDegree - (P % Q).natDegree)
    (Q.natDegree - (P % Q).natDegree - 1)
    ((Q.natDegree - (P % Q).natDegree - 1) * (Q.natDegree - (P % Q).natDegree) / 2)
    _ _ _ _ (by omega) rfl (by omega) heps

/-- Reduction scaling for `sRes` at indices `≤ r`: both `(P,Q)` and `(Q,-R)` values differ by the
    common factor `μ = ε(p-q)·b^{p-r}`. -/
private theorem sRes_scale (P Q : K[X]) (hQ : Q ≠ 0) (hR0 : P % Q ≠ 0)
    (hpq : Q.natDegree < P.natDegree) {i : ℕ} (hi : i ≤ (P % Q).natDegree) :
    Azurite.BPR.Chapter4.sRes P Q i
      = (↑(Chapter4.ε (P.natDegree - Q.natDegree)) : K)
        * Q.leadingCoeff ^ (P.natDegree - (P % Q).natDegree)
        * Azurite.BPR.Chapter4.sRes Q (-(P % Q)) i := by
  have hrq : (P % Q).natDegree < Q.natDegree := natDegree_lt_natDegree hR0 (degree_mod_lt P hQ)
  rw [← coeff_sResP P Q hpq (show i ≤ P.natDegree by omega),
    sResP_propto_le_r P Q hQ hR0 hpq hi,
    ← Int.cast_smul_eq_zsmul K, smul_smul, Polynomial.coeff_smul, smul_eq_mul,
    coeff_sResP Q (-(P % Q)) (by rw [natDegree_neg]; omega) (by omega)]

/-- Reduction scaling for `lcof(sResP)` at indices `≤ r`. -/
private theorem lcof_scale (P Q : K[X]) (hQ : Q ≠ 0) (hR0 : P % Q ≠ 0)
    (hpq : Q.natDegree < P.natDegree) {i : ℕ} (hi : i ≤ (P % Q).natDegree) :
    (sResP P Q i).leadingCoeff
      = (↑(Chapter4.ε (P.natDegree - Q.natDegree)) : K)
        * Q.leadingCoeff ^ (P.natDegree - (P % Q).natDegree)
        * (sResP Q (-(P % Q)) i).leadingCoeff := by
  rw [sResP_propto_le_r P Q hQ hR0 hpq hi, ← Int.cast_smul_eq_zsmul K, smul_smul,
    smul_eq_C_mul, Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C]

/-- Reduction preserves degrees at indices `≤ r`. -/
private theorem natDegree_sResP_scale (P Q : K[X]) (hQ : Q ≠ 0) (hR0 : P % Q ≠ 0)
    (hpq : Q.natDegree < P.natDegree) {i : ℕ} (hi : i ≤ (P % Q).natDegree) :
    (sResP P Q i).natDegree = (sResP Q (-(P % Q)) i).natDegree := by
  have hεne : ((Chapter4.ε (P.natDegree - Q.natDegree) : ℤ) : K) ≠ 0 := by
    rw [Chapter4.ε]; push_cast; exact pow_ne_zero _ (by norm_num)
  have hb : Q.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hQ
  rw [sResP_propto_le_r P Q hQ hR0 hpq hi, ← Int.cast_smul_eq_zsmul K, smul_smul,
    natDegree_smul _ (mul_ne_zero hεne (pow_ne_zero _ hb))]

/-- **BPR Proposition 8.46, the cleared block identity (★').**  In a defective block
    (`sResP_j(P,Q)` non-defective of degree `j`, `sResP_{j-1}(P,Q)` of degree `k`),
    `sRes_k · sRes_j^{j-k-1} = (-1)^{(j-k-1)(j-k)/2} · t_{j-1}^{j-k}`.  Proved by strong induction
    on `deg Q`: trivial when `k = j-1`, the explicit `star_base` when `j = q`, and the Euclidean
    reduction `(P,Q) → (Q,-R)` (where every factor scales by the common `μ`, so the identity is
    preserved) otherwise. -/
theorem sRes_block_identity (P Q : K[X]) (hP : P ≠ 0) (hQ : Q ≠ 0)
    (hpq : Q.natDegree < P.natDegree) {j k : ℕ} (hjq : j ≤ Q.natDegree) (hj1 : 1 ≤ j)
    (hjnd : (sResP P Q j).natDegree = j) (hk0 : sResP P Q (j - 1) ≠ 0)
    (hkdeg : (sResP P Q (j - 1)).natDegree = k) :
    Azurite.BPR.Chapter4.sRes P Q k * Azurite.BPR.Chapter4.sRes P Q j ^ (j - k - 1)
      = (-1 : K) ^ ((j - k - 1) * (j - k) / 2) * (sResP P Q (j - 1)).leadingCoeff ^ (j - k) := by
  suffices key : ∀ n, ∀ P Q : K[X], P ≠ 0 → Q ≠ 0 → Q.natDegree = n →
      Q.natDegree < P.natDegree → ∀ j k, j ≤ Q.natDegree → 1 ≤ j →
      (sResP P Q j).natDegree = j → sResP P Q (j - 1) ≠ 0 →
      (sResP P Q (j - 1)).natDegree = k →
      Azurite.BPR.Chapter4.sRes P Q k * Azurite.BPR.Chapter4.sRes P Q j ^ (j - k - 1)
        = (-1 : K) ^ ((j - k - 1) * (j - k) / 2) * (sResP P Q (j - 1)).leadingCoeff ^ (j - k) from
    key Q.natDegree P Q hP hQ rfl hpq j k hjq hj1 hjnd hk0 hkdeg
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro P Q hP hQ hn hpq j k hjq hj1 hjnd hk0 hkdeg
  have hq1 : 1 ≤ Q.natDegree := le_trans hj1 hjq
  have hjm : k ≤ j - 1 := by
    have := Polynomial.natDegree_le_iff_degree_le.mpr
      (sResP_degree_le P Q hpq (show j - 1 ≤ Q.natDegree by omega))
    rw [hkdeg] at this; omega
  by_cases hkj : k = j - 1
  · -- trivial: `sRes_{j-1} = t_{j-1}` (non-defective `sResP_{j-1}`)
    subst hkj
    rw [show j - (j - 1) - 1 = 0 by omega, show j - (j - 1) = 1 by omega]
    simp only [pow_zero, mul_one, Nat.zero_div, pow_one, one_mul]
    exact (leadingCoeff_sResP_eq_sRes P Q hpq (by omega)
      (show IsNonDefective P Q (j - 1) from by
        rw [IsNonDefective, Polynomial.degree_eq_natDegree hk0, hkdeg])).symm
  · have hkj' : k < j - 1 := lt_of_le_of_ne hjm hkj
    have hR : P % Q ≠ 0 := by
      rintro hR0
      have hgcdq : (gcd P Q).natDegree = Q.natDegree :=
        le_antisymm (Polynomial.natDegree_le_of_dvd (gcd_dvd_right P Q) hQ)
          (Polynomial.natDegree_le_of_dvd
            (dvd_gcd (EuclideanDomain.mod_eq_zero.mp hR0) dvd_rfl)
            (fun h => hP (by simpa using (gcd_eq_zero_iff P Q).mp h |>.1)))
      exact hk0 (sResP_eq_zero_of_lt_gcd P Q hP hQ hpq (show j - 1 ≤ Q.natDegree by omega)
        (show j - 1 < (gcd P Q).natDegree by rw [hgcdq]; omega))
    have hrq : (P % Q).natDegree < Q.natDegree := natDegree_lt_natDegree hR (degree_mod_lt P hQ)
    by_cases hjqeq : j = Q.natDegree
    · -- base case `j = q`
      have hkr : k = (P % Q).natDegree :=
        hkdeg.symm.trans (by rw [hjqeq]; exact natDegree_sResP_natDegree_sub_one P Q hQ hR hpq hq1)
      subst hjqeq; subst hkr
      exact star_base P Q hQ hpq hq1 hR (by omega)
    · by_cases hjr : j ≤ (P % Q).natDegree
      · -- reduction `(P,Q) → (Q,-R)`
        have hkr : k ≤ (P % Q).natDegree := by omega
        have hj1r : j - 1 ≤ (P % Q).natDegree := by omega
        have hSj' : sResP Q (-(P % Q)) (j - 1) ≠ 0 := fun h => hk0 (by
          rw [sResP_propto_le_r P Q hQ hR hpq hj1r, h]; simp)
        have hIH := ih (P % Q).natDegree (by omega) Q (-(P % Q)) hQ (neg_ne_zero.mpr hR)
          (by rw [natDegree_neg]) (by rw [natDegree_neg]; exact hrq) j k
          (by rw [natDegree_neg]; exact hjr) hj1
          (by rw [← natDegree_sResP_scale P Q hQ hR hpq hjr]; exact hjnd) hSj'
          (by rw [← natDegree_sResP_scale P Q hQ hR hpq hj1r]; exact hkdeg)
        rw [sRes_scale P Q hQ hR hpq hkr, sRes_scale P Q hQ hR hpq hjr,
          lcof_scale P Q hQ hR hpq hj1r]
        obtain ⟨μ, hμ⟩ : ∃ μ : K, (↑(Chapter4.ε (P.natDegree - Q.natDegree)) : K)
          * Q.leadingCoeff ^ (P.natDegree - (P % Q).natDegree) = μ := ⟨_, rfl⟩
        rw [hμ, mul_pow, mul_pow, show μ ^ (j - k) = μ ^ (j - k - 1) * μ from by
          rw [← pow_succ]; congr 1; omega]
        linear_combination (μ ^ (j - k - 1) * μ) * hIH
      · -- gap `r < j ≤ q-1`: contradicts non-defectiveness
        exfalso
        rcases eq_or_lt_of_le (show j ≤ Q.natDegree - 1 by omega) with hjeq | hjlt
        · rw [hjeq, natDegree_sResP_natDegree_sub_one P Q hQ hR hpq hq1] at hjnd; omega
        · rw [sResP_eq_zero_of_step_gap P Q hQ hR hpq (by omega) (by omega),
            Polynomial.natDegree_zero] at hjnd
          omega

/-- **BPR Proposition 8.46 (proportionality core).**  If `sResP_{j-1}(P,Q)` is nonzero of degree
    `k`, then the non-defective representative `sResP_k(P,Q)` at the bottom of its block satisfies
    `sResP_k = C(s_k / t_{j-1}) · sResP_{j-1}`, with `s_k = sRes_k(P,Q)` and
    `t_{j-1} = lcof(sResP_{j-1}(P,Q))`. -/
theorem sResP_realized_eq (P Q : K[X]) (hP : P ≠ 0) (hQ : Q ≠ 0)
    (hpq : Q.natDegree < P.natDegree) (hq1 : 1 ≤ Q.natDegree) {j k : ℕ}
    (hjq : j ≤ Q.natDegree) (hj1 : 1 ≤ j)
    (hk0 : sResP P Q (j - 1) ≠ 0) (hkdeg : (sResP P Q (j - 1)).natDegree = k) :
    sResP P Q k
      = C (Azurite.BPR.Chapter4.sRes P Q k / (sResP P Q (j - 1)).leadingCoeff)
          * sResP P Q (j - 1) := by
  -- `k < j` (degree of `sResP_{j-1}` is `≤ j-1`), so `k ≤ q`.
  have hkj : k < j := by
    have := Polynomial.natDegree_le_iff_degree_le.mpr
      (sResP_degree_le P Q hpq (show j - 1 ≤ Q.natDegree by omega))
    rw [hkdeg] at this; omega
  have hkq : k ≤ Q.natDegree := by omega
  -- `sResP_k` is the non-defective representative at degree `k`: degree `k`, nonzero.
  obtain ⟨hndk, hk0'⟩ := sResP_natDegree_realized P Q hP hQ hpq hq1 hk0
  rw [hkdeg] at hndk hk0'
  -- `sResP_k` is associate to `sResP_{j-1}` (block proportionality, Theorem 8.34).
  have hassoc : Associated (sResP P Q k) (sResP P Q (j - 1)) := by
    have := sResP_block_associated P Q hP hQ hpq (show j - 1 ≤ Q.natDegree by omega) hk0
    rwa [hkdeg] at this
  -- The proportionality constant is the leading-coefficient ratio; `lcof(sResP_k) = sRes_k`.
  have hlck : (sResP P Q k).leadingCoeff = Azurite.BPR.Chapter4.sRes P Q k :=
    leadingCoeff_sResP_eq_sRes P Q hpq hkq
      (show (sResP P Q k).degree = (k : WithBot ℕ) from by
        rw [Polynomial.degree_eq_natDegree hk0', hndk])
  rw [← hlck]
  exact eq_C_leadingCoeff_ratio_mul_of_associated hk0 hassoc

/-- **BPR Proposition 8.46 (full, explicit constant).**  In a defective block (`sResP_j(P,Q)`
    non-defective of degree `j`, `sResP_{j-1}(P,Q)` nonzero of degree `k`), the non-defective
    representative `sResP_k(P,Q)` at the bottom equals `S_k`:
    `sResP_k = (-1)^{(j-k-1)(j-k)/2} · (t_{j-1}/s_j)^{j-k-1} · sResP_{j-1}`,
    with `t_{j-1} = lcof(sResP_{j-1})` and `s_j = sRes_j`. -/
theorem proposition_8_46 (P Q : K[X]) (hP : P ≠ 0) (hQ : Q ≠ 0)
    (hpq : Q.natDegree < P.natDegree) (hq1 : 1 ≤ Q.natDegree) {j k : ℕ}
    (hjq : j ≤ Q.natDegree) (hj1 : 1 ≤ j) (hjnd : (sResP P Q j).natDegree = j)
    (hk0 : sResP P Q (j - 1) ≠ 0) (hkdeg : (sResP P Q (j - 1)).natDegree = k) :
    sResP P Q k
      = C ((-1 : K) ^ ((j - k - 1) * (j - k) / 2)
          * ((sResP P Q (j - 1)).leadingCoeff / Azurite.BPR.Chapter4.sRes P Q j) ^ (j - k - 1))
        * sResP P Q (j - 1) := by
  have hkj : k < j := by
    have := Polynomial.natDegree_le_iff_degree_le.mpr
      (sResP_degree_le P Q hpq (show j - 1 ≤ Q.natDegree by omega))
    rw [hkdeg] at this; omega
  have ht : (sResP P Q (j - 1)).leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hk0
  have hsj0 : sResP P Q j ≠ 0 := fun h => by rw [h, Polynomial.natDegree_zero] at hjnd; omega
  have hsj : Azurite.BPR.Chapter4.sRes P Q j ≠ 0 :=
    (isNonDefective_iff_sRes_ne_zero P Q hpq hjq).mp
      (by rw [IsNonDefective, Polynomial.degree_eq_natDegree hsj0, hjnd])
  have hid := sRes_block_identity P Q hP hQ hpq hjq hj1 hjnd hk0 hkdeg
  rw [show (sResP P Q (j - 1)).leadingCoeff ^ (j - k)
      = (sResP P Q (j - 1)).leadingCoeff ^ (j - k - 1) * (sResP P Q (j - 1)).leadingCoeff from by
      rw [← pow_succ]; congr 1; omega] at hid
  rw [sResP_realized_eq P Q hP hQ hpq hq1 hjq hj1 hk0 hkdeg]
  congr 2
  rw [div_pow, ← mul_div_assoc, div_eq_div_iff ht (pow_ne_zero _ hsj)]
  linear_combination hid

end Azurite.BPR.Chapter8
