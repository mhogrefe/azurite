import Azurite.BasuPollackRoy.Chapter4.Section4_2.Lemma_4_35
import Azurite.BasuPollackRoy.Chapter4.Section4_2.Lemma_4_36
import Azurite.BasuPollackRoy.Chapter2.Section2_2.Theorem_2_58

/-!
# BPR Theorem 4.32: `PmV(sRes(P, Q)) = Ind(Q/P)`

The generalized permanences-minus-variations of the signed subresultant
sequence of `P` and `Q` equals the Cauchy index of `Q/P` (over a real closed
field), with `deg Q < deg P`.

The proof is by induction on the length of the signed remainder sequence —
equivalently, strong induction on `deg Q`. Both the `PmV`-recursion
(Lemma 4.36) and the Cauchy-index recursion (Lemma 4.35) have the *same*
Euclidean-step correction `[p−q odd]·sign(a_p b_q)`, so the inductive step is
`PmV(sRes(P,Q)) = PmV(sRes(Q,−R)) + corr = Ind(−R/Q) + corr = Ind(Q/P)` once the
induction hypothesis identifies `PmV(sRes(Q,−R)) = Ind(−R/Q)`.

The base case `R = P % Q = 0` (i.e. `Q ∣ P`) is handled directly: on the index
side `Ind(Q/P) = Ind(0/Q) + corr = corr` (`cauchyIndexOn_zero_left`); on the
`PmV` side the defective subresultants `sRes_j(P,Q)` vanish for `j < q`
(`sRes_eq_zero_of_rem_zero`, since the `R`-rows of `M'` are zero), so the only
contribution is the `p → q` bridge term, which is again `corr`
(`eps_sign_sResp_sResq`).
-/

namespace Azurite.BPR.Chapter4

-- Use the root `Polynomial` namespace explicitly: the Chapter 2 import chain
-- defines `Polynomial.*` extensions inside `Azurite.BPR`, which would otherwise
-- shadow it and disable the scoped `R[X]` notation (parsing `K[X]` as `getElem`).
open _root_.Polynomial

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

omit [IsStrictOrderedRing K] in
/-- If every entry after the head is zero, `PmV` is zero (the `dropWhile`
collapses to the empty list). -/
theorem PmV_cons_all_zero (a : K) (l : List K) (h : ∀ x ∈ l, x = 0) :
    PmV (a :: l) = 0 := by
  have hdrop : l.dropWhile (fun x => decide (x = 0)) = [] := by
    rw [List.dropWhile_eq_nil_iff]
    intro x hx; simp [h x hx]
  rw [PmV]
  split
  · rfl
  · next sq tl hh => rw [hdrop] at hh; exact absurd hh (by simp)

omit [LinearOrder K] [IsStrictOrderedRing K] in
/-- **The defective subresultants vanish when `Q ∣ P`.** If `R = P % Q = 0`, then
`sRes_j(P, Q) = 0` for all `j < q`: in `M' = E·SyHa` the `R`-rows are zero, so
its determinant — which equals `sRes_j(P, Q)` — vanishes. -/
theorem sRes_eq_zero_of_rem_zero (P Q : K[X]) {j : ℕ} (hQ : Q ≠ 0)
    (hR : P % Q = 0) (hjq : j < Q.natDegree) (hqp : Q.natDegree < P.natDegree) :
    sRes P Q j = 0 := by
  rw [← MpMatrix_det_eq_sRes P Q j hQ (le_of_lt hjq) hqp]
  refine Matrix.det_eq_zero_of_row_eq_zero ⟨0, ?_⟩ ?_
  · omega
  · intro k
    simp only [MpMatrix, Matrix.of_apply]
    rw [if_pos (show (0 : ℕ) < Q.natDegree - j by omega), hR, mul_zero, Polynomial.coeff_zero]

/-- **The `p → q` bridge term equals `sign(a_p b_q)`.** Using `sRes_p = a_p` and
`sRes_q = ε_{p-q} b_q^{p-q}`, the bridge contribution
`[p−q odd] ε_{p-q}·sign(sRes_p·sRes_q)` simplifies to `[p−q odd]·sign(a_p b_q)`.
(Extracted from the assembly of Lemma 4.36, reused in the base case here.) -/
theorem eps_sign_sResp_sResq (P Q : K[X]) (hQ : Q ≠ 0) (hqp : Q.natDegree < P.natDegree) :
    (if Odd (P.natDegree - Q.natDegree) then
        ε (P.natDegree - Q.natDegree) *
          (SignType.sign (sRes P Q P.natDegree * sRes P Q Q.natDegree) : ℤ) else 0)
      = (if Odd (P.natDegree - Q.natDegree)
          then (SignType.sign (P.leadingCoeff * Q.leadingCoeff) : ℤ) else 0) := by
  have hbq : Q.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hQ
  have hsp : sRes P Q P.natDegree = P.leadingCoeff := by
    rw [sRes, if_neg (by omega), if_pos hqp, if_pos rfl]
  have hsq : sRes P Q Q.natDegree
      = ((ε (P.natDegree - Q.natDegree) : ℤ) : K) * Q.leadingCoeff ^ (P.natDegree - Q.natDegree) :=
    sRes_q_eq P Q hQ hqp
  by_cases hodd : Odd (P.natDegree - Q.natDegree)
  · rw [if_pos hodd, if_pos hodd, hsp, hsq,
      show P.leadingCoeff * (((ε (P.natDegree - Q.natDegree) : ℤ) : K) *
          Q.leadingCoeff ^ (P.natDegree - Q.natDegree))
        = ((ε (P.natDegree - Q.natDegree) : ℤ) : K) *
          (P.leadingCoeff * Q.leadingCoeff ^ (P.natDegree - Q.natDegree)) by ring,
      sign_mul, SignType.coe_mul, sign_eps, ← mul_assoc, ε_mul_self, one_mul,
      sign_mul, SignType.coe_mul, sign_pow_odd Q.leadingCoeff hbq hodd,
      ← SignType.coe_mul, ← sign_mul]
  · rw [if_neg hodd, if_neg hodd]

variable [IsRealClosed K]

/-- **BPR Theorem 4.32.** `PmV(sRes(P, Q)) = Ind(Q/P)` over a real closed field,
for `deg Q < deg P`. Proved by strong induction on `deg Q` (i.e. on the length
of the signed remainder sequence): the inductive step combines Lemma 4.36 (the
`PmV` Euclidean step), the induction hypothesis applied to `(Q, −R)`, and
Lemma 4.35 (the Cauchy-index Euclidean step), which share the same correction
term; the base case `Q ∣ P` is computed directly. -/
theorem theorem_4_32 (P Q : K[X]) (hQ : Q ≠ 0) (hqp : Q.natDegree < P.natDegree) :
    PmV (sResSeq P Q) = cauchyIndex Q P := by
  suffices key : ∀ n : ℕ, ∀ P Q : K[X], Q ≠ 0 → Q.natDegree = n →
      Q.natDegree < P.natDegree → PmV (sResSeq P Q) = cauchyIndex Q P from
    key Q.natDegree P Q hQ rfl hqp
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro P Q hQ hn hqp
    have hP : P ≠ 0 := by rintro rfl; simp at hqp
    by_cases hR : P % Q = 0
    · -- base case: `Q ∣ P`
      have hbq : Q.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hQ
      have hsq_ne : sRes P Q Q.natDegree ≠ 0 := by
        rw [sRes_q_eq P Q hQ hqp]
        exact mul_ne_zero (eps_cast_ne _) (pow_ne_zero _ hbq)
      have hzero : PmV (partialSeq P Q Q.natDegree) = 0 := by
        rw [partialSeq_eq_cons]
        apply PmV_cons_all_zero
        intro x hx
        simp only [List.mem_map, List.mem_range] at hx
        obtain ⟨i, hi, rfl⟩ := hx
        exact sRes_eq_zero_of_rem_zero P Q hQ hR (by omega) hqp
      have hPmV : PmV (sResSeq P Q) =
          (if Odd (P.natDegree - Q.natDegree)
            then (SignType.sign (P.leadingCoeff * Q.leadingCoeff) : ℤ) else 0) := by
        show PmV (partialSeq P Q P.natDegree) = _
        rw [PmV_partialSeq_bridge P Q hqp hsq_ne
              (fun j hj hjp => sRes_eq_zero_of_gap P Q hj hjp),
            hzero, zero_add, eps_sign_sResp_sResq P Q hQ hqp]
      rw [hPmV, lemma_4_35 P Q hP hQ hqp, hR, neg_zero,
          cauchyIndex_eq_cauchyIndexOn_negInf_posInf, cauchyIndexOn_zero_left, zero_add]
    · -- inductive step
      have hrq : (P % Q).natDegree < Q.natDegree :=
        Polynomial.natDegree_lt_natDegree hR (Polynomial.degree_mod_lt P hQ)
      rw [lemma_4_36 P Q hQ hR hrq hqp,
        ih (P % Q).natDegree (hn ▸ hrq) Q (-(P % Q)) (neg_ne_zero.mpr hR)
          (Polynomial.natDegree_neg _) (by rw [Polynomial.natDegree_neg]; exact hrq),
        lemma_4_35 P Q hP hQ hqp]

end Azurite.BPR.Chapter4
