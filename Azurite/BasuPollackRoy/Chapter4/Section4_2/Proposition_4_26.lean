import Azurite.BasuPollackRoy.Chapter4.Section4_2.Proposition_4_25

/-!
# BPR Proposition 4.26: deg(gcd) = j ↔ sRes pattern

Over a field `K`, for `j` in the BPR range, the gcd of `P` and `Q` has
degree exactly `j` if and only if the first `j` signed subresultant
coefficients vanish and the `j`-th does not.

## Proof

This is a direct corollary of Lemma 4.24 (vanishing subresultant
criterion) and Proposition 4.25 (`deg gcd ≥ j ↔ sRes_0 = ⋯ =
sRes_{j-1} = 0`).

* **Forward** (`deg gcd = j → ...`): from `deg gcd = j` and
  Proposition 4.25, the first `j` coefficients vanish. For
  `sRes_j ≠ 0`: assume `sRes_j = 0`, apply Lemma 4.24 to obtain
  `U, V ≠ 0`; the divisibility `gcd | U·P + V·Q` together with the
  Proposition 1.5 degree identity forces a contradiction with
  `deg gcd = j` whether or not `U·P + V·Q` vanishes.
* **Reverse** (`... → deg gcd = j`): Proposition 4.25 gives
  `deg gcd ≥ j`. The upper bound `deg gcd ≤ j` splits on whether
  `j < deg Q`. If yes, use the bridge
  `exists_UV_zero_iff_gcd_natDegree_ge` at `j + 1` plus
  Lemma 4.24 to derive `sRes_j = 0`, contradicting the hypothesis.
  If `j = deg Q`, the bound `deg gcd ≤ deg Q = j` is automatic
  (from `gcd | Q`).
-/

namespace Azurite.BPR.Chapter4

open Polynomial

variable {K : Type*} [Field K] [DecidableEq K]

/-- **BPR Proposition 4.26.** Over a field `K`, for `j` in the BPR
    range,

      `(gcd P Q).natDegree = j` ↔
        `(∀ i < j, sRes P Q i = 0) ∧ sRes P Q j ≠ 0`. -/
theorem Proposition_4_26 (P Q : K[X]) (hP : P ≠ 0) (hQ : Q ≠ 0)
    (j : ℕ) (hj_q : j ≤ Q.natDegree) (hj_p : j < P.natDegree) :
    (gcd P Q).natDegree = j ↔
      (∀ i, i < j → sRes P Q i = 0) ∧ sRes P Q j ≠ 0 := by
  have h_gcd_le_Q : (gcd P Q).natDegree ≤ Q.natDegree :=
    Polynomial.natDegree_le_of_dvd (gcd_dvd_right P Q) hQ
  have h_lcm_gcd := lcm_natDegree_eq P Q hP hQ
  constructor
  · -- Forward: `deg gcd = j → ...`.
    intro h_gcd_eq
    have h_gcd_ge : (gcd P Q).natDegree ≥ j := by omega
    refine ⟨(Proposition_4_25 P Q hP hQ j hj_q hj_p).mpr h_gcd_ge, ?_⟩
    intro h_sres
    -- Lemma 4.24 at j: get U V.
    obtain ⟨U, V, hU, hV, hUq, hVp, h_lt⟩ :=
      (Lemma_4_24 P Q j hj_q hj_p hP hQ).mp h_sres
    have h_U_natDeg : U.natDegree < Q.natDegree - j := by
      rw [Polynomial.degree_eq_natDegree hU] at hUq
      exact_mod_cast hUq
    have h_V_natDeg : V.natDegree < P.natDegree - j := by
      rw [Polynomial.degree_eq_natDegree hV] at hVp
      exact_mod_cast hVp
    -- Two sub-cases on whether `U * P + V * Q = 0`.
    by_cases h_UV_zero : U * P + V * Q = 0
    · -- `U * P + V * Q = 0`. Then `lcm | U * P` gives a degree bound
      -- that contradicts `deg gcd = j` via Proposition 1.5.
      have h_UP_ne : U * P ≠ 0 := mul_ne_zero hU hP
      have h_UP_dvd_P : P ∣ U * P := ⟨U, by ring⟩
      have h_UP_dvd_Q : Q ∣ U * P := by
        rw [show U * P = -(V * Q) from by linear_combination h_UV_zero]
        exact ⟨-V, by ring⟩
      have h_lcm_dvd : lcm P Q ∣ U * P := lcm_dvd h_UP_dvd_P h_UP_dvd_Q
      have h_deg_le : (lcm P Q).natDegree ≤ (U * P).natDegree :=
        Polynomial.natDegree_le_of_dvd h_lcm_dvd h_UP_ne
      have h_UP_deg : (U * P).natDegree = U.natDegree + P.natDegree :=
        Polynomial.natDegree_mul hU hP
      omega
    · -- `U * P + V * Q ≠ 0`. Then `gcd | U * P + V * Q` gives
      -- `deg gcd ≤ deg(U·P + V·Q) < j`, contradicting `deg gcd = j`.
      have h_div : (gcd P Q) ∣ U * P + V * Q := by
        apply dvd_add
        · exact (gcd_dvd_left P Q).mul_left U
        · exact (gcd_dvd_right P Q).mul_left V
      have h_deg_le : (gcd P Q).natDegree ≤ (U * P + V * Q).natDegree :=
        Polynomial.natDegree_le_of_dvd h_div h_UV_zero
      have h_UV_natDeg : (U * P + V * Q).natDegree < j := by
        rw [Polynomial.degree_eq_natDegree h_UV_zero] at h_lt
        exact_mod_cast h_lt
      omega
  · -- Reverse: `... → deg gcd = j`.
    rintro ⟨h_all_zero, h_sres_ne⟩
    have h_gcd_ge : (gcd P Q).natDegree ≥ j :=
      (Proposition_4_25 P Q hP hQ j hj_q hj_p).mp h_all_zero
    by_cases h_j_lt_q : j < Q.natDegree
    · -- `j + 1 ≤ Q.natDegree` and `j + 1 ≤ P.natDegree`.
      -- Show `deg gcd ≤ j` by contradiction.
      by_contra h_gcd_ne_j
      have h_gcd_gt : (gcd P Q).natDegree > j := by
        push Not at h_gcd_ne_j; omega
      have h_gcd_ge_j1 : (gcd P Q).natDegree ≥ j + 1 := h_gcd_gt
      -- Bridge at `j+1` gives `U, V ≠ 0` with `U·P + V·Q = 0`.
      obtain ⟨U, V, hU, hV, hUq, hVp, h_UV_zero⟩ :=
        (exists_UV_zero_iff_gcd_natDegree_ge P Q hP hQ (j + 1)
          (by omega) (by omega)).mpr h_gcd_ge_j1
      -- Lemma 4.24 (reverse) at `j` then gives `sRes_j = 0`, contradiction.
      apply h_sres_ne
      refine (Lemma_4_24 P Q j hj_q hj_p hP hQ).mpr
        ⟨U, V, hU, hV, ?_, ?_, ?_⟩
      · rw [Polynomial.degree_eq_natDegree hU]
        have : U.natDegree < Q.natDegree - j := by omega
        exact_mod_cast this
      · rw [Polynomial.degree_eq_natDegree hV]
        have : V.natDegree < P.natDegree - j := by omega
        exact_mod_cast this
      · rw [h_UV_zero, Polynomial.degree_zero]
        exact WithBot.bot_lt_coe j
    · -- `j = Q.natDegree`. `deg gcd ≤ Q.natDegree = j` is automatic.
      push Not at h_j_lt_q
      omega

end Azurite.BPR.Chapter4
