import Azurite.BasuPollackRoy.Chapter8.Section8_3.Corollary_8_35
import Azurite.BasuPollackRoy.Chapter1.Section1_2.Lemma1_11

/-!
# BPR Corollary 8.38

The general (defective-allowed) correspondence between signed subresultants and the signed
remainder sequence: if `SRemS_{ℓ-1}` and `SRemS_ℓ` are two successive nonzero polynomials of
the signed remainder sequence, of degrees `d(ℓ-1)` and `d(ℓ)`, then both
`sResP_{d(ℓ-1)-1}(P,Q)` and `sResP_{d(ℓ)}(P,Q)` are proportional to `SRemS_ℓ(P,Q)`.

Proved by (two-step) induction on `ℓ`, carrying both proportionalities.  The step applies the
Structure Theorem recurrence at `(i,j,k) = (d(ℓ-2), d(ℓ-1), d(ℓ))`, turning
`sResP_{d(ℓ)-1}` into a remainder of the two preceding subresultants, then transports through
the induction hypotheses and the defining recurrence of the signed remainder sequence.
-/

namespace Azurite.BPR.Chapter8

open Polynomial

variable {K : Type*} [Field K]

/-- From `C a · x = C b · y` with `a, b ≠ 0`, the polynomials `x` and `y` are associate. -/
theorem associated_of_C_mul_eq {a b : K} (ha : a ≠ 0) (hb : b ≠ 0) {x y : K[X]}
    (h : C a * x = C b * y) : Associated x y := by
  have hx : x = C (a⁻¹ * b) * y := by
    rw [C_mul, mul_assoc, ← h, ← mul_assoc, ← C_mul, inv_mul_cancel₀ ha, map_one, one_mul]
  rw [hx]
  exact associated_unit_mul_left y (C (a⁻¹ * b))
    (isUnit_C.mpr (isUnit_iff_ne_zero.mpr (mul_ne_zero (inv_ne_zero ha) hb)))

/-- Proportionality is preserved by the Euclidean remainder: if `a ~ a'` and `b ~ b'`, then
    `a % b ~ a' % b'` (units of `K[X]` are nonzero constants, which factor through `%`). -/
theorem Associated.rem {a a' b b' : K[X]} (ha : Associated a a') (hb : Associated b b') :
    Associated (a % b) (a' % b') := by
  obtain ⟨u, rfl⟩ := ha
  obtain ⟨v, rfl⟩ := hb
  obtain ⟨cu, hcu0, hcu⟩ := Polynomial.isUnit_iff.mp u.isUnit
  obtain ⟨cv, hcv0, hcv⟩ := Polynomial.isUnit_iff.mp v.isUnit
  rw [← hcu, ← hcv, mul_comm a (C cu), mul_comm b (C cv), rem_C_mul,
    mod_C_mul_right _ _ hcv0.ne_zero]
  exact (associated_unit_mul_left (a % b) (C cu) (isUnit_C.mpr hcu0)).symm

/-- A polynomial is associate to its negation. -/
theorem associated_neg (a : K[X]) : Associated (-a) a := by
  rw [← neg_one_mul]; exact associated_unit_mul_left a (-1) isUnit_one.neg

/-- For a non-defective index `j ≤ q`, the signed subresultant coefficient `s_j` is nonzero. -/
theorem sBPR_ne_of_nondef (P Q : K[X]) (hpq : Q.natDegree < P.natDegree) {j : ℕ}
    (hjq : j ≤ Q.natDegree) (hne : sResP P Q j ≠ 0) (hnd : (sResP P Q j).natDegree = j) :
    sBPR P Q j ≠ 0 := by
  rw [sBPR, ite_eq_right (by omega : j ≠ P.natDegree),
    ← leadingCoeff_sResP_eq_sRes P Q hpq hjq
      (show (sResP P Q j).degree = (j : WithBot ℕ) from by
        rw [Polynomial.degree_eq_natDegree hne, hnd])]
  exact Polynomial.leadingCoeff_ne_zero.mpr hne

/-- For `j ≠ p` with `sResP_j ≠ 0`, the leading coefficient `t_j` is nonzero. -/
theorem tBPR_ne_of_ne (P Q : K[X]) {j : ℕ} (hjp : j ≠ P.natDegree) (hne : sResP P Q j ≠ 0) :
    tBPR P Q j ≠ 0 := by
  rw [tBPR, ite_eq_right hjp]; exact Polynomial.leadingCoeff_ne_zero.mpr hne

/-- **BPR Corollary 8.38.**  If `SRemS_{ℓ-1}(P,Q)` and `SRemS_ℓ(P,Q)` are two successive
    nonzero polynomials of the signed remainder sequence, of degrees `d(ℓ-1)` and `d(ℓ)`,
    then both `sResP_{d(ℓ-1)-1}(P,Q)` and `sResP_{d(ℓ)}(P,Q)` are proportional to
    `SRemS_ℓ(P,Q)`. -/
theorem corollary_8_38 (P Q : K[X]) (hP : P ≠ 0) (hQ : Q ≠ 0)
    (hpq : Q.natDegree < P.natDegree) (hq1 : 1 ≤ Q.natDegree)
    {ℓ : ℕ} (hℓ1 : 1 ≤ ℓ) (hℓne : SRemS P Q ℓ ≠ 0) :
    Associated (sResP P Q ((SRemS P Q (ℓ - 1)).natDegree - 1)) (SRemS P Q ℓ)
    ∧ Associated (sResP P Q (SRemS P Q ℓ).natDegree) (SRemS P Q ℓ) := by
  have hprev : ∀ n, SRemS P Q (n + 1) ≠ 0 → SRemS P Q n ≠ 0 := by
    intro n hn1 hn0
    rcases n with _ | n'
    · exact hP (by rw [← SRemS_fst (P := P) (Q := Q)]; exact hn0)
    · exact hn1 (SRemS_zero_ge P Q n' hn0 (n' + 2) (by omega))
  have hdec : ∀ n, SRemS P Q (n + 1) ≠ 0 →
      (SRemS P Q (n + 1)).natDegree < (SRemS P Q n).natDegree := by
    intro n hn1
    rcases n with _ | n'
    · rw [SRemS_fst, SRemS_snd]; exact hpq
    · exact Polynomial.natDegree_lt_natDegree hn1
        (degree_SRemS_chain_lt P Q (n' + 1) (by omega) (hprev (n' + 1) hn1))
  have hd_le_q : ∀ n, SRemS P Q (n + 1) ≠ 0 → (SRemS P Q (n + 1)).natDegree ≤ Q.natDegree := by
    intro n
    induction n with
    | zero => intro _; exact le_of_eq (by rw [SRemS_snd])
    | succ n' ih =>
      intro hn1
      have h1 := hdec (n' + 1) hn1
      have h2 := ih (hprev (n' + 1) hn1)
      omega
  have hd_le_p : ∀ n, SRemS P Q n ≠ 0 → (SRemS P Q n).natDegree ≤ P.natDegree := by
    intro n hn
    rcases n with _ | n'
    · exact le_of_eq (by rw [SRemS_fst])
    · have := hd_le_q n' hn; omega
  suffices key : ∀ N, 1 ≤ N → SRemS P Q N ≠ 0 →
      Associated (sResP P Q ((SRemS P Q (N - 1)).natDegree - 1)) (SRemS P Q N)
      ∧ Associated (sResP P Q (SRemS P Q N).natDegree) (SRemS P Q N) from key ℓ hℓ1 hℓne
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro hN1 hNne
  rcases N with _ | _ | _ | m
  · exact absurd hN1 (by omega)
  · -- N = 1
    refine ⟨?_, ?_⟩
    · show Associated (sResP P Q ((SRemS P Q 0).natDegree - 1)) (SRemS P Q 1)
      rw [SRemS_fst, sResP_pm1_eq_Q P Q hQ hpq, SRemS_snd]
    · show Associated (sResP P Q (SRemS P Q 1).natDegree) (SRemS P Q 1)
      rw [SRemS_snd]
      obtain ⟨w, hw, hw0⟩ : ∃ w : K, sResP P Q Q.natDegree = C w * Q ∧ w ≠ 0 :=
        ⟨_, by rw [sResP_eq_of_natDegree P Q hpq hQ, ← Int.cast_smul_eq_zsmul K, smul_eq_C_mul,
            ← mul_assoc, ← C_mul],
          mul_ne_zero (by rw [Azurite.BPR.Chapter4.ε]; push_cast; exact pow_ne_zero _ (by norm_num))
            (pow_ne_zero _ (Polynomial.leadingCoeff_ne_zero.mpr hQ))⟩
      rw [hw]
      exact associated_unit_mul_left Q (C w) (isUnit_C.mpr (isUnit_iff_ne_zero.mpr hw0))
  · -- N = 2
    have hS1ne : SRemS P Q 1 ≠ 0 := by rw [SRemS_snd]; exact hQ
    have hSRemS2 : SRemS P Q 2 = -(P % Q) := by
      rw [show (2 : ℕ) = 0 + 2 from rfl, SRemS_ss P Q 0 hS1ne, SRemS_fst, SRemS_snd]
    have hR0 : P % Q ≠ 0 := fun h => hNne (by rw [hSRemS2, h, neg_zero])
    have hA2 : Associated (sResP P Q (Q.natDegree - 1)) (SRemS P Q 2) := by
      rw [hSRemS2]
      obtain ⟨c, hc, hc0⟩ : ∃ c : K, sResP P Q (Q.natDegree - 1) = C c * (P % Q) ∧ c ≠ 0 :=
        ⟨_, by rw [sResP_natDegree_sub_one P Q hQ hR0 hpq hq1, ← Int.cast_smul_eq_zsmul K,
            smul_smul, smul_eq_C_mul, ← neg_mul, ← map_neg],
          neg_ne_zero.mpr (mul_ne_zero
            (by rw [Azurite.BPR.Chapter4.ε]; push_cast; exact pow_ne_zero _ (by norm_num))
            (pow_ne_zero _ (Polynomial.leadingCoeff_ne_zero.mpr hQ)))⟩
      rw [hc]
      exact (associated_unit_mul_left (P % Q) (C c) (isUnit_C.mpr (isUnit_iff_ne_zero.mpr hc0))).trans
        (associated_neg (P % Q)).symm
    refine ⟨?_, ?_⟩
    · show Associated (sResP P Q ((SRemS P Q 1).natDegree - 1)) (SRemS P Q 2)
      rw [SRemS_snd]; exact hA2
    · show Associated (sResP P Q (SRemS P Q 2).natDegree) (SRemS P Q 2)
      have hne2 : sResP P Q (Q.natDegree - 1) ≠ 0 := fun h => hNne (hA2.eq_zero_iff.mp h)
      have hdeg2 : (sResP P Q (Q.natDegree - 1)).natDegree = (SRemS P Q 2).natDegree :=
        Polynomial.natDegree_eq_of_degree_eq (Polynomial.degree_eq_degree_of_associated hA2)
      have hblock := sResP_block_associated P Q hP hQ hpq (show Q.natDegree - 1 ≤ Q.natDegree by omega) hne2
      rw [hdeg2] at hblock
      exact hblock.trans hA2
  · -- N = m + 3 (inductive step)
    show Associated (sResP P Q ((SRemS P Q (m + 2)).natDegree - 1)) (SRemS P Q (m + 3))
      ∧ Associated (sResP P Q (SRemS P Q (m + 3)).natDegree) (SRemS P Q (m + 3))
    have hSm2 : SRemS P Q (m + 2) ≠ 0 := hprev (m + 2) hNne
    have hSm1 : SRemS P Q (m + 1) ≠ 0 := hprev (m + 1) hSm2
    have hSm : SRemS P Q m ≠ 0 := hprev m hSm1
    obtain ⟨hA_m1, hB_m1⟩ := ih (m + 1) (by omega) (by omega) hSm1
    obtain ⟨hA_m2, hB_m2⟩ := ih (m + 2) (by omega) (by omega) hSm2
    have hd2_pos : 1 ≤ (SRemS P Q (m + 2)).natDegree := by
      rcases Nat.eq_zero_or_pos (SRemS P Q (m + 2)).natDegree with hc | hc
      · exfalso; apply hNne
        have hunit : IsUnit (SRemS P Q (m + 2)) :=
          Polynomial.isUnit_iff_degree_eq_zero.mpr (by rw [Polynomial.degree_eq_natDegree hSm2, hc]; simp)
        rw [show (m + 3) = (m + 1) + 2 from rfl, SRemS_ss P Q (m + 1) hSm2,
          EuclideanDomain.mod_eq_zero.mpr hunit.dvd, neg_zero]
      · exact hc
    have hdm_le_p : (SRemS P Q m).natDegree ≤ P.natDegree := hd_le_p m hSm
    have hdm1_le_q : (SRemS P Q (m + 1)).natDegree ≤ Q.natDegree := hd_le_q m hSm1
    have hdm2_le_q : (SRemS P Q (m + 2)).natDegree ≤ Q.natDegree := hd_le_q (m + 1) hSm2
    have hji1 : (SRemS P Q (m + 1)).natDegree < (SRemS P Q m).natDegree := hdec m hSm1
    have hji2 : (SRemS P Q (m + 2)).natDegree < (SRemS P Q (m + 1)).natDegree := hdec (m + 1) hSm2
    have hne_i : sResP P Q ((SRemS P Q m).natDegree - 1) ≠ 0 :=
      fun h => hSm1 (hA_m1.eq_zero_iff.mp h)
    have hdeg_i : (sResP P Q ((SRemS P Q m).natDegree - 1)).natDegree = (SRemS P Q (m + 1)).natDegree :=
      Polynomial.natDegree_eq_of_degree_eq (Polynomial.degree_eq_degree_of_associated hA_m1)
    have hne_j : sResP P Q ((SRemS P Q (m + 1)).natDegree - 1) ≠ 0 :=
      fun h => hSm2 (hA_m2.eq_zero_iff.mp h)
    have hdeg_j : (sResP P Q ((SRemS P Q (m + 1)).natDegree - 1)).natDegree = (SRemS P Q (m + 2)).natDegree :=
      Polynomial.natDegree_eq_of_degree_eq (Polynomial.degree_eq_degree_of_associated hA_m2)
    have hndm1 : (sResP P Q (SRemS P Q (m + 1)).natDegree).natDegree = (SRemS P Q (m + 1)).natDegree :=
      Polynomial.natDegree_eq_of_degree_eq (Polynomial.degree_eq_degree_of_associated hB_m1)
    have hne_dm1 : sResP P Q (SRemS P Q (m + 1)).natDegree ≠ 0 := fun h => hSm1 (hB_m1.eq_zero_iff.mp h)
    have hndm2 : (sResP P Q (SRemS P Q (m + 2)).natDegree).natDegree = (SRemS P Q (m + 2)).natDegree :=
      Polynomial.natDegree_eq_of_degree_eq (Polynomial.degree_eq_degree_of_associated hB_m2)
    have hne_dm2 : sResP P Q (SRemS P Q (m + 2)).natDegree ≠ 0 := fun h => hSm2 (hB_m2.eq_zero_iff.mp h)
    have hmono := (theorem_8_34_monolithic P Q hP hQ hpq hq1
      (i := (SRemS P Q m).natDegree) (j := (SRemS P Q (m + 1)).natDegree)
      (by omega) (by omega) (by omega) hne_i hdeg_i).2
      (SRemS P Q (m + 2)).natDegree hne_j hdeg_j
    obtain ⟨hmono, _⟩ := hmono
    rw [ite_eq_right (by omega : ¬ (SRemS P Q (m + 2)).natDegree = 0), ← C_mul, ← C_mul, rem_C_mul,
      ← mul_neg] at hmono
    have hαβ1 : sBPR P Q (SRemS P Q (m + 1)).natDegree
        * tBPR P Q ((SRemS P Q m).natDegree - 1) ≠ 0 :=
      mul_ne_zero (sBPR_ne_of_nondef P Q hpq hdm1_le_q hne_dm1 hndm1)
        (tBPR_ne_of_ne P Q (by omega) hne_i)
    have hαβ2 : sBPR P Q (SRemS P Q (m + 2)).natDegree
        * tBPR P Q ((SRemS P Q (m + 1)).natDegree - 1) ≠ 0 :=
      mul_ne_zero (sBPR_ne_of_nondef P Q hpq hdm2_le_q hne_dm2 hndm2)
        (tBPR_ne_of_ne P Q (by omega) hne_j)
    have hA3 : Associated (sResP P Q ((SRemS P Q (m + 2)).natDegree - 1)) (SRemS P Q (m + 3)) := by
      have key1 := associated_of_C_mul_eq hαβ1 hαβ2 hmono
      rw [show (m + 3) = (m + 1) + 2 from rfl, SRemS_ss P Q (m + 1) hSm2]
      exact key1.trans ((associated_neg _).trans
        ((Associated.rem hA_m1 hA_m2).trans (associated_neg _).symm))
    refine ⟨hA3, ?_⟩
    have hne_A3 : sResP P Q ((SRemS P Q (m + 2)).natDegree - 1) ≠ 0 :=
      fun h => hNne (hA3.eq_zero_iff.mp h)
    have hdeg_A3 : (sResP P Q ((SRemS P Q (m + 2)).natDegree - 1)).natDegree
        = (SRemS P Q (m + 3)).natDegree :=
      Polynomial.natDegree_eq_of_degree_eq (Polynomial.degree_eq_degree_of_associated hA3)
    have hblock := sResP_block_associated P Q hP hQ hpq
      (show (SRemS P Q (m + 2)).natDegree - 1 ≤ Q.natDegree by omega) hne_A3
    rw [hdeg_A3] at hblock
    exact hblock.trans hA3

end Azurite.BPR.Chapter8
