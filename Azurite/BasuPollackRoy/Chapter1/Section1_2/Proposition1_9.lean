import Azurite.BasuPollackRoy.Chapter1.Section1_2.Lemma1_11
import Azurite.BasuPollackRoy.Chapter1.Section1_2.Proposition1_8
import Azurite.BasuPollackRoy.Chapter1.Section1_2.SRemSTermination

/-!
# Proposition 1.9

If $G$ is a greatest common divisor of $P$ and $Q$ in $K[X]$ with
$\deg G < \deg P$ and $\deg G < \deg Q$, then there exist $U, V \in
K[X]$ such that $U P + V Q = G$, with degree bounds
$\deg U < \deg Q - \deg G$ and $\deg V < \deg P - \deg G$.

The construction comes from the Bezout coefficients of the extended
signed remainder sequence (Lemma 1.11).
-/

namespace Azurite.BPR

open Polynomial

variable {K : Type*} [Field K]

open Classical in
/-- BPR Proposition 1.9 (Helper): Assumes deg Q ≤ deg P -/
theorem proposition_1_9_aux {P Q G : K[X]}
    (hP : P ≠ 0) (hQ : Q ≠ 0)
    (hle : Q.degree ≤ P.degree)
    (hG : IsGCD G P Q)
    (hnd_g : G.natDegree < Q.natDegree) :
    ∃ U V : K[X],
      U * P + V * Q = G ∧
      U.natDegree < Q.natDegree - G.natDegree ∧
      V.natDegree < P.natDegree - G.natDegree := by
  obtain ⟨k, hk_def⟩ : ∃ k, k = sremTermIndex P Q := ⟨_, rfl⟩
  have hk : SRemS P Q (k + 1) = 0 := hk_def ▸ SRemS_sremTermIndex_succ_eq_zero P Q hP
  have hk_ne : SRemS P Q k ≠ 0 := hk_def ▸ SRemS_sremTermIndex_ne_zero P Q hP
  have hGk := prop_1_8 hk hk_ne
  have hassoc := isGCD_associated hG hGk
  obtain ⟨c, hc⟩ := hassoc.symm
  have hG_nd : G.natDegree = (SRemS P Q k).natDegree := by
    rw [← hc, Polynomial.natDegree_mul hk_ne (Units.ne_zero c),
        Polynomial.natDegree_coe_units c]; omega
  have hk2 : k ≥ 2 := by

    cases k with
    | zero =>
      have : G.natDegree = P.natDegree := by simp [SRemS_fst] at hG_nd; exact hG_nd
      have h1 := Polynomial.natDegree_le_natDegree hle
      omega
    | succ k' =>
      cases k' with
      | zero =>
        have : G.natDegree = Q.natDegree := by simp [SRemS_snd] at hG_nd; exact hG_nd
        omega
      | succ k'' => omega
  refine ⟨SRemU P Q k * ↑c, SRemV P Q k * ↑c, ?_, ?_, ?_⟩
  · have hbez := lemma_1_11_bezout P Q k
    calc SRemU P Q k * ↑c * P + SRemV P Q k * ↑c * Q
      _ = (SRemU P Q k * P + SRemV P Q k * Q) * ↑c := by ring
      _ = SRemS P Q k * ↑c := by rw [hbez]
      _ = G := hc
  · obtain ⟨k', rfl⟩ : ∃ k', k = k' + 2 := ⟨k - 2, by omega⟩
    have hk1_ne : SRemS P Q (k' + 1) ≠ 0 :=
      SRemS_ne_zero_of_le P Q (k' + 2) (k' + 1) hk hk_ne (by omega) (by omega)
    have hdegU := lemma_1_11_degU P Q (k' + 2) (k' + 1) hk hk_ne (by omega) (by omega) hP hQ hle
    rcases Nat.eq_zero_or_pos k' with rfl | hk'
    · -- k = 2
      have h1 : SRemS P Q 1 ≠ 0 := by simp [SRemS_snd]; exact hQ
      have hne_u : SRemU P Q 2 ≠ 0 := by
        rw [SRemU_ss P Q 0 h1]
        simp [SRemU, SRemS]
      rw [Polynomial.natDegree_mul hne_u (Units.ne_zero c),
          Polynomial.natDegree_coe_units c, add_zero, hdegU, hG_nd]
      -- Goal: Q.natDegree - SRemS P Q 1.natDegree < Q.natDegree - SRemS P Q 2.natDegree
      -- SRemS P Q 1 is Q, so Q.natDegree - Q.natDegree = 0
      -- We need 0 < Q.natDegree - SRemS P Q 2.natDegree, which is SRemS(2) < Q
      have hqnd : (SRemS P Q 1).natDegree = Q.natDegree := by simp [SRemS_snd]
      rw [hqnd, Nat.sub_self]
      apply Nat.sub_pos_of_lt
      rw [← hG_nd]; exact hnd_g
    · -- k > 2 (so k' > 0)
      have hk1_lt_q : (SRemS P Q (k' + 1)).natDegree < Q.natDegree := by
        have := natDegree_SRemS_lt_of_lt P Q 0 k' hk' (fun l hl1 hl2 =>
          SRemS_ne_zero_of_le P Q (k' + 2) l hk hk_ne (by omega) (by omega))
        simp [SRemS_snd] at this; exact this
      have hne_u : SRemU P Q (k' + 2) ≠ 0 := by
        intro heq; rw [heq, Polynomial.natDegree_zero] at hdegU
        exact absurd hdegU (ne_of_gt (Nat.sub_pos_of_lt hk1_lt_q)).symm
      rw [Polynomial.natDegree_mul hne_u (Units.ne_zero c),
          Polynomial.natDegree_coe_units c, add_zero, hdegU, hG_nd]
      have h_strict : (SRemS P Q (k' + 2)).natDegree < (SRemS P Q (k' + 1)).natDegree :=
        Polynomial.natDegree_lt_natDegree hk_ne (degree_SRemS_lt P Q k' hk1_ne)
      exact Nat.sub_lt_sub_left (lt_trans h_strict hk1_lt_q) h_strict
  · obtain ⟨k', rfl⟩ : ∃ k', k = k' + 2 := ⟨k - 2, by omega⟩
    have hk1_ne : SRemS P Q (k' + 1) ≠ 0 :=
      SRemS_ne_zero_of_le P Q (k' + 2) (k' + 1) hk hk_ne (by omega) (by omega)
    have hdegV := lemma_1_11_degV P Q (k' + 2) (k' + 1) hk hk_ne (by omega) (by omega) hP hQ hle
    rcases Nat.eq_zero_or_pos k' with rfl | hk'
    · -- k = 2
      -- We must show (SRemV 2 * c).natDegree < P.natDegree - G.natDegree
      have h1 : (SRemS P Q 1).natDegree = Q.natDegree := by simp [SRemS_snd]
      have hG_lt_P : G.natDegree < P.natDegree :=
        lt_of_lt_of_le hnd_g (Polynomial.natDegree_le_natDegree hle)
      by_cases hV : SRemV P Q 2 = 0
      · rw [hV, zero_mul, Polynomial.natDegree_zero]
        exact Nat.sub_pos_of_lt hG_lt_P
      · rw [Polynomial.natDegree_mul hV (Units.ne_zero c),
            Polynomial.natDegree_coe_units c, add_zero, hdegV, h1]
        exact Nat.sub_lt_sub_left hG_lt_P hnd_g
    · -- k > 2 (so k' > 0)
      have hk1_lt_q : (SRemS P Q (k' + 1)).natDegree < Q.natDegree := by
        have := natDegree_SRemS_lt_of_lt P Q 0 k' hk' (fun l hl1 hl2 =>
          SRemS_ne_zero_of_le P Q (k' + 2) l hk hk_ne (by omega) (by omega))
        simp [SRemS_snd] at this; exact this
      have hk1_lt_p : (SRemS P Q (k' + 1)).natDegree < P.natDegree :=
        lt_of_lt_of_le hk1_lt_q (Polynomial.natDegree_le_natDegree hle)
      have hne_v : SRemV P Q (k' + 2) ≠ 0 := by
        intro heq; rw [heq, Polynomial.natDegree_zero] at hdegV
        exact absurd hdegV (ne_of_gt (Nat.sub_pos_of_lt hk1_lt_p)).symm
      rw [Polynomial.natDegree_mul hne_v (Units.ne_zero c),
          Polynomial.natDegree_coe_units c, add_zero, hdegV, hG_nd]
      have h_strict : (SRemS P Q (k' + 2)).natDegree < (SRemS P Q (k' + 1)).natDegree :=
        Polynomial.natDegree_lt_natDegree hk_ne (degree_SRemS_lt P Q k' hk1_ne)
      exact Nat.sub_lt_sub_left (lt_trans h_strict hk1_lt_p) h_strict

/-- BPR Proposition 1.9: If G is a greatest common divisor of P and Q,
    and G is a proper divisor in terms of degree (deg G < deg P and deg G < deg Q),
    then there exist U and V with U·P + V·Q = G such that
    natDeg(U) < natDeg(Q) − natDeg(G) and natDeg(V) < natDeg(P) − natDeg(G). -/
theorem proposition_1_9 {P Q G : K[X]}
    (hP : P ≠ 0) (hQ : Q ≠ 0)
    (hG : IsGCD G P Q)
    (hnd_gP : G.natDegree < P.natDegree)
    (hnd_gQ : G.natDegree < Q.natDegree) :
    ∃ U V : K[X],
      U * P + V * Q = G ∧
      U.natDegree < Q.natDegree - G.natDegree ∧
      V.natDegree < P.natDegree - G.natDegree := by
  by_cases hle : Q.degree ≤ P.degree
  · exact proposition_1_9_aux hP hQ hle hG hnd_gQ
  · have hle' : P.degree ≤ Q.degree := by
      push Not at hle; exact le_of_lt hle
    have hG' : IsGCD G Q P := hG.symm
    obtain ⟨U, V, hbez, hdegU, hdegV⟩ := proposition_1_9_aux hQ hP hle' hG' hnd_gP
    refine ⟨V, U, ?_, hdegV, hdegU⟩
    rw [add_comm, hbez]

end Azurite.BPR
