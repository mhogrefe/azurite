import Azurite.BasuPollackRoy.Chapter1.Section1_2.Lcm
import Azurite.BasuPollackRoy.Chapter1.Section1_2.Lemma1_11
import Azurite.BasuPollackRoy.Chapter1.Section1_2.SRemSTermination

/-!
# Proposition 1.12

For nonzero $P$ and $Q$ in $K[X]$, the polynomial $\lcode{SRemU}\,P\,Q\;
(k+1) \cdot P$ — where $k = \lcode{sremTermIndex}\,P\,Q$ — equals
$-\lcode{SRemV}\,P\,Q\;(k+1) \cdot Q$ and is a least common multiple of
$P$ and $Q$.

The key auxiliary identity is the unimodularity of the U/V cofactor
sequence: $U_n V_{n+1} - V_n U_{n+1} = 1$ on every prefix where the
SRemS sequence is nonzero. (This is unnumbered in BPR; BPR's Lemma
1.10 (b) states the analogous identity as $(-1)^i$ for a sign-shifted
recurrence; with the sign convention here it simplifies to $1$.)
-/

namespace Azurite.BPR

open Polynomial

variable {K : Type*} [Field K]

/-- Determinant identity: `SRemU n * SRemV (n+1) - SRemV n * SRemU (n+1) = 1`,
    valid on any prefix where `SRemS i ≠ 0` for all `i ≤ n`.
    Unnumbered in BPR; the analogous BPR statement appears in its Lemma 1.10
    with a $(-1)^i$ sign that arises from a different recurrence convention. -/
lemma sremUV_det_eq_one {P Q : K[X]} (n : ℕ) (hn : ∀ i ≤ n, SRemS P Q i ≠ 0) :
    SRemU P Q n * SRemV P Q (n + 1) - SRemV P Q n * SRemU P Q (n + 1) = 1 := by
  induction n generalizing P Q with
  | zero =>
    dsimp [SRemU, SRemV]
    ring
  | succ n ih =>
    have hn_ne : SRemS P Q (n + 1) ≠ 0 := hn (n + 1) (by omega)
    have hn_ne' : ∀ i ≤ n, SRemS P Q i ≠ 0 := fun i hi => hn i (by omega)
    have ih_app := ih hn_ne'
    have H_U : SRemU P Q (n + 2) = - SRemU P Q n + (SRemS P Q n / SRemS P Q (n + 1)) * SRemU P Q (n + 1) := by
      rw [SRemU, if_neg hn_ne]
    have H_V : SRemV P Q (n + 2) = - SRemV P Q n + (SRemS P Q n / SRemS P Q (n + 1)) * SRemV P Q (n + 1) := by
      rw [SRemV, if_neg hn_ne]
    rw [H_U, H_V]
    calc SRemU P Q (n + 1) * (-SRemV P Q n + SRemS P Q n / SRemS P Q (n + 1) * SRemV P Q (n + 1)) - SRemV P Q (n + 1) * (-SRemU P Q n + SRemS P Q n / SRemS P Q (n + 1) * SRemU P Q (n + 1))
      _ = SRemU P Q n * SRemV P Q (n + 1) - SRemV P Q n * SRemU P Q (n + 1) := by ring
      _ = 1 := by rw [ih_app]

theorem proposition_1_12 {P Q: K[X]} (hP : P ≠ 0) (_hQ : Q ≠ 0) :
    (SRemU P Q (sremTermIndex P Q + 1) * P = - SRemV P Q (sremTermIndex P Q + 1) * Q) ∧
    IsLCM (SRemU P Q (sremTermIndex P Q + 1) * P) P Q := by
  obtain ⟨k, hk_def⟩ : ∃ x, x = sremTermIndex P Q := ⟨_, rfl⟩
  have hk : SRemS P Q (k + 1) = 0 := hk_def ▸ SRemS_sremTermIndex_succ_eq_zero P Q hP
  have hk_ne : SRemS P Q k ≠ 0 := hk_def ▸ SRemS_sremTermIndex_ne_zero P Q hP
  have h_le : ∀ i ≤ k, SRemS P Q i ≠ 0 := hk_def ▸ SRemS_ne_zero_of_le_sremTermIndex P Q hP
  rw [← hk_def]
  constructor
  · have hbez : SRemS P Q (k + 1) = SRemU P Q (k + 1) * P + SRemV P Q (k + 1) * Q :=
      lemma_1_11_bezout P Q (k + 1)
    rw [hk] at hbez
    calc SRemU P Q (k + 1) * P = SRemU P Q (k + 1) * P + SRemV P Q (k + 1) * Q - SRemV P Q (k + 1) * Q := by ring
      _ = 0 - SRemV P Q (k + 1) * Q := by rw [← hbez]
      _ = - SRemV P Q (k + 1) * Q := by ring
  · constructor
    · exact dvd_mul_left P (SRemU P Q (k + 1))
    · constructor
      · have hbez : SRemS P Q (k + 1) = SRemU P Q (k + 1) * P + SRemV P Q (k + 1) * Q :=
          lemma_1_11_bezout P Q (k + 1)
        rw [hk] at hbez
        have H1 : SRemU P Q (k + 1) * P = - SRemV P Q (k + 1) * Q := by
          calc SRemU P Q (k + 1) * P = SRemU P Q (k + 1) * P + SRemV P Q (k + 1) * Q - SRemV P Q (k + 1) * Q := by ring
            _ = 0 - SRemV P Q (k + 1) * Q := by rw [← hbez]
            _ = - SRemV P Q (k + 1) * Q := by ring
        rw [H1]
        exact dvd_mul_left Q (- SRemV P Q (k + 1))
      · intro D hDP hDQ
        obtain ⟨A, hA⟩ := hDP
        obtain ⟨B, hB⟩ := hDQ
        have hbez : SRemS P Q (k + 1) = SRemU P Q (k + 1) * P + SRemV P Q (k + 1) * Q :=
          lemma_1_11_bezout P Q (k + 1)
        rw [hk] at hbez
        have H1 : SRemV P Q (k + 1) * Q = - SRemU P Q (k + 1) * P := by
          calc SRemV P Q (k + 1) * Q = SRemV P Q (k + 1) * Q + SRemU P Q (k + 1) * P - SRemU P Q (k + 1) * P := by ring
            _ = (SRemU P Q (k + 1) * P + SRemV P Q (k + 1) * Q) - SRemU P Q (k + 1) * P := by ring
            _ = 0 - SRemU P Q (k + 1) * P := by rw [← hbez]
            _ = - SRemU P Q (k + 1) * P := by ring
        have H_alg : D = (- B * SRemU P Q k - A * SRemV P Q k) * (SRemU P Q (k + 1) * P) := by
          calc D = D * 1 := by ring
            _ = D * (SRemU P Q k * SRemV P Q (k + 1) - SRemV P Q k * SRemU P Q (k + 1)) := by
                rw [← sremUV_det_eq_one k h_le]
            _ = D * SRemU P Q k * SRemV P Q (k + 1) - D * SRemV P Q k * SRemU P Q (k + 1) := by ring
            _ = (Q * B) * SRemU P Q k * SRemV P Q (k + 1) - (P * A) * SRemV P Q k * SRemU P Q (k + 1) := by
                have h1 : D * SRemU P Q k * SRemV P Q (k + 1) = (Q * B) * SRemU P Q k * SRemV P Q (k + 1) := by rw [hB]
                have h2 : D * SRemV P Q k * SRemU P Q (k + 1) = (P * A) * SRemV P Q k * SRemU P Q (k + 1) := by rw [hA]
                rw [h1, h2]
            _ = B * SRemU P Q k * (SRemV P Q (k + 1) * Q) - A * SRemV P Q k * (SRemU P Q (k + 1) * P) := by ring
            _ = B * SRemU P Q k * (- SRemU P Q (k + 1) * P) - A * SRemV P Q k * (SRemU P Q (k + 1) * P) := by
                rw [H1]
            _ = (- B * SRemU P Q k - A * SRemV P Q k) * (SRemU P Q (k + 1) * P) := by ring
        have H_d : D = (SRemU P Q (k + 1) * P) * (- B * SRemU P Q k - A * SRemV P Q k) := by
          calc D = (- B * SRemU P Q k - A * SRemV P Q k) * (SRemU P Q (k + 1) * P) := H_alg
            _ = (SRemU P Q (k + 1) * P) * (- B * SRemU P Q k - A * SRemV P Q k) := by ring
        exact ⟨_, H_d⟩

end Azurite.BPR
