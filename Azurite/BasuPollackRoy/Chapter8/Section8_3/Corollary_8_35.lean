import Azurite.BasuPollackRoy.Chapter8.Section8_3.Theorem_8_34

/-!
# BPR Corollary 8.35

A consequence of the Structure Theorem (`theorem_8_34_monolithic`): in the setting where
`sResP_{i-1}(P,Q) ≠ 0` is of degree `j`, if `sResP_{j-1}(P,Q)` is of degree `k`, then

  `s_j² sResP_{k-1}(P,Q) = -Rem(s_k t_{j-1} sResP_j(P,Q), sResP_{j-1}(P,Q))`,

with BPR's terminus convention `sResP_{-1} = 0` at `k = 0`.  The conclusion uses the regular
representative `sResP_j` (in place of the possibly-defective `sResP_{i-1}`) and `s_j²` (in
place of `s_j t_{i-1}`).

The proof reapplies the recurrence at `i = j+1`, where `sResP_{i-1} = sResP_j`, so that
`t_{i-1} = t_j = s_j` (the leading coefficient of the non-defective `sResP_j`).  The
underlying structural fact — *the regular representative at a realized degree is
non-defective* — is isolated as `sResP_natDegree_realized`.
-/

namespace Azurite.BPR.Chapter8

open Polynomial

variable {K : Type*} [Field K]

/-- The **regular representative at a realized degree is non-defective**: if `sResP_n ≠ 0`,
    then the subresultant at its own degree, `sResP_{deg(sResP_n)}`, has degree exactly
    `deg(sResP_n)` and is itself nonzero (it is the non-defective top of the block containing
    `sResP_n`).  By block proportionality for `n ≤ q`; for `n > q` a nonzero `sResP_n` forces
    `n ∈ {p-1, p}` (else it would be in a degree gap), where it is `Q`/`P` directly. -/
theorem sResP_natDegree_realized (P Q : K[X]) (hP : P ≠ 0) (hQ : Q ≠ 0)
    (hpq : Q.natDegree < P.natDegree) (hq1 : 1 ≤ Q.natDegree) {n : ℕ}
    (hn : sResP P Q n ≠ 0) :
    (sResP P Q (sResP P Q n).natDegree).natDegree = (sResP P Q n).natDegree
      ∧ sResP P Q (sResP P Q n).natDegree ≠ 0 := by
  by_cases hnq : n ≤ Q.natDegree
  · have hA := sResP_block_associated P Q hP hQ hpq hnq hn
    refine ⟨Polynomial.natDegree_eq_of_degree_eq
      (Polynomial.degree_eq_degree_of_associated hA), fun h => hn ?_⟩
    rw [h] at hA
    exact (associated_zero_iff_eq_zero _).mp hA.symm
  · by_cases hnp2 : n = P.natDegree
    · rw [hnp2, sResP_eq_self P Q hpq, sResP_eq_self P Q hpq]; exact ⟨rfl, hP⟩
    · have heq : n = P.natDegree - 1 := by
        by_contra hc; exact hn (sResP_eq_zero P Q (by omega) hnp2 hc)
      rw [heq, sResP_pm1_eq_Q P Q hQ hpq]
      have hqdeg : (sResP P Q Q.natDegree).natDegree = Q.natDegree :=
        natDegree_sResP_natDegree P Q hQ hpq
      exact ⟨hqdeg, fun h => by rw [h, Polynomial.natDegree_zero] at hqdeg; omega⟩

/-- **BPR Corollary 8.35.**  In the setting of Theorem 8.34 (`sResP_{i-1}(P,Q) ≠ 0` of degree
    `j`), if `sResP_{j-1}(P,Q)` is of degree `k` (`1 ≤ k`), then
    `s_j² sResP_{k-1}(P,Q) = -Rem(s_k t_{j-1} sResP_j(P,Q), sResP_{j-1}(P,Q))`,
    using BPR's terminus convention `sResP_{-1} = 0` at `k = 0`.

    Immediate from Theorem 8.34: the realized degree `j` is non-defective
    (`sResP_natDegree_realized`), so its regular representative `sResP_j` has leading
    coefficient `t_j = s_j`; applying the monolithic recurrence at `i = j+1` (where
    `sResP_{i-1} = sResP_j`) turns `s_j t_{i-1}` into `s_j²`. -/
theorem corollary_8_35 (P Q : K[X]) (hP : P ≠ 0) (hQ : Q ≠ 0)
    (hpq : Q.natDegree < P.natDegree) (hq1 : 1 ≤ Q.natDegree)
    {i j : ℕ} (hj1 : 1 ≤ j) (hji : j < i) (hip : i ≤ P.natDegree + 1)
    (hne : sResP P Q (i - 1) ≠ 0) (hdeg : (sResP P Q (i - 1)).natDegree = j)
    {k : ℕ} (hk0 : sResP P Q (j - 1) ≠ 0) (hkdeg : (sResP P Q (j - 1)).natDegree = k)
    (hk1 : 1 ≤ k) :
    C (sBPR P Q j) ^ 2 * sResP P Q (k - 1)
      = -((C (sBPR P Q k) * C (tBPR P Q (j - 1)) * sResP P Q j) % sResP P Q (j - 1)) := by
  -- `sResP_j` is the non-defective representative at degree `j`
  obtain ⟨hndj, hsj⟩ := sResP_natDegree_realized P Q hP hQ hpq hq1 hne
  rw [hdeg] at hndj hsj
  have hjp : j ≤ P.natDegree := by
    by_contra h; exact hsj (sResP_eq_zero P Q (by omega) (by omega) (by omega))
  -- `t_j = s_j` (non-defective): trivial at `j = p` (both `= 1`), else `leadingCoeff = sRes`
  have htj : tBPR P Q j = sBPR P Q j := by
    by_cases hjpe : j = P.natDegree
    · rw [tBPR, if_pos hjpe, sBPR, if_pos hjpe]
    · rw [tBPR, if_neg hjpe, sBPR, if_neg hjpe]
      have hjq : j ≤ Q.natDegree := by
        by_contra hjq'
        by_cases hjpm1 : j = P.natDegree - 1
        · rw [hjpm1, sResP_pm1_eq_Q P Q hQ hpq] at hndj; omega
        · exact hsj (sResP_eq_zero P Q (by omega) hjpe hjpm1)
      exact leadingCoeff_sResP_eq_sRes P Q hpq hjq
        (show (sResP P Q j).degree = (j : WithBot ℕ) from by
          rw [Polynomial.degree_eq_natDegree hsj, hndj])
  -- apply the monolith at `i = j+1`, where `sResP_{i-1} = sResP_j`
  have hmono := (theorem_8_34_monolithic P Q hP hQ hpq hq1 (i := j + 1) (j := j)
    hj1 (by omega) (by omega) (by rw [Nat.add_sub_cancel]; exact hsj)
    (by rw [Nat.add_sub_cancel]; exact hndj)).2 k hk0 hkdeg
  obtain ⟨hmono, _⟩ := hmono
  simp only [Nat.add_sub_cancel] at hmono
  rw [if_neg (show ¬ k = 0 by omega), htj] at hmono
  rw [pow_two]; exact hmono

end Azurite.BPR.Chapter8
