import Azurite.BasuPollackRoy.Chapter4.Section4_2.Proposition_4_28
import Azurite.BasuPollackRoy.Chapter4.Section4_2.Proposition_4_26

/-!
# BPR Proposition 4.30: deg(gcd(P, P')) = j ↔ sDisc pattern

For `P : K[X]` with `0 < p := P.natDegree` and `0 ≤ j < p`,

  `deg(gcd(P, P')) = j ↔ sDisc_0(P) = ⋯ = sDisc_{j-1}(P) = 0 ∧
                          sDisc_j(P) ≠ 0`.

## Proof

A direct corollary of Proposition 4.26 (gcd-degree in terms of
`sRes`) and Proposition 4.28 (`a_p · sDisc = sRes`): for `0 ≤ i < p`,
`sDisc_i(P) = 0` in `C` iff `sRes_i(P, P') = 0` in `K` (since
`a_p ≠ 0` and `algebraMap K C` is injective).
-/

namespace Azurite.BPR.Chapter4

open Polynomial

variable {K : Type*} [Field K] [DecidableEq K] [CharZero K]
variable {C : Type*} [Field C] [Algebra K C] [IsAlgClosed C]

omit [DecidableEq K] in
private lemma sDisc_eq_zero_iff_sRes_eq_zero (P : K[X]) (hP : 0 < P.natDegree)
    (i : ℕ) (hi : i < P.natDegree) :
    sDisc (C := C) P i = 0 ↔ sRes P P.derivative i = 0 := by
  have hP_ne : P ≠ 0 := fun h => by rw [h] at hP; simp at hP
  have h_a_ne : P.leadingCoeff ≠ 0 :=
    Polynomial.leadingCoeff_ne_zero.mpr hP_ne
  have h_alg_a_ne : (algebraMap K C) P.leadingCoeff ≠ 0 :=
    (map_ne_zero (algebraMap K C)).mpr h_a_ne
  have h_prop28 := proposition_4_28 (C := C) P hP (P.natDegree - i)
    (by omega) (by omega)
  rw [show P.natDegree - (P.natDegree - i) = i from by omega] at h_prop28
  -- h_prop28: alg(a_p) * sDisc P i = alg(sRes P P' i).
  constructor
  · intro h_sDisc
    have h_alg_sRes : (algebraMap K C) (sRes P P.derivative i) = 0 := by
      rw [← h_prop28, h_sDisc, mul_zero]
    exact (map_eq_zero_iff (algebraMap K C) (algebraMap K C).injective).mp h_alg_sRes
  · intro h_sRes
    have h_alg_sRes : (algebraMap K C) (sRes P P.derivative i) = 0 := by
      rw [h_sRes, (algebraMap K C).map_zero]
    have : (algebraMap K C) P.leadingCoeff * sDisc P i = 0 := by
      rw [h_prop28, h_alg_sRes]
    exact (mul_eq_zero.mp this).resolve_left h_alg_a_ne

/-- **BPR Proposition 4.30.** For `P : K[X]` of positive degree and
    `0 ≤ j < P.natDegree`,

      `deg(gcd(P, P')) = j ↔ sDisc_0(P) = ⋯ = sDisc_{j-1}(P) = 0 ∧
                              sDisc_j(P) ≠ 0`. -/
theorem Proposition_4_30 (P : K[X]) (hP : 0 < P.natDegree)
    (j : ℕ) (hj : j < P.natDegree) :
    (gcd P P.derivative).natDegree = j ↔
      (∀ i, i < j → (sDisc P i : C) = 0) ∧ (sDisc P j : C) ≠ 0 := by
  have hP_ne : P ≠ 0 := fun h => by rw [h] at hP; simp at hP
  have hp_deriv : P.derivative.natDegree = P.natDegree - 1 :=
    Polynomial.natDegree_eq_of_degree_eq_some
      (Polynomial.degree_derivative_eq P hP)
  have hP'_ne : P.derivative ≠ 0 := by
    intro h
    have h_deg := Polynomial.degree_derivative_eq P hP
    rw [h, Polynomial.degree_zero] at h_deg
    exact (WithBot.bot_ne_coe h_deg).elim
  have hj_q : j ≤ P.derivative.natDegree := by rw [hp_deriv]; omega
  have h_prop26 := Proposition_4_26 P P.derivative hP_ne hP'_ne j hj_q hj
  rw [h_prop26]
  constructor
  · rintro ⟨h_all_sRes, h_sRes_ne⟩
    refine ⟨?_, ?_⟩
    · intro i hi
      exact (sDisc_eq_zero_iff_sRes_eq_zero (C := C) P hP i (by omega)).mpr
        (h_all_sRes i hi)
    · intro h_sDisc
      exact h_sRes_ne ((sDisc_eq_zero_iff_sRes_eq_zero (C := C) P hP j hj).mp h_sDisc)
  · rintro ⟨h_all_sDisc, h_sDisc_ne⟩
    refine ⟨?_, ?_⟩
    · intro i hi
      exact (sDisc_eq_zero_iff_sRes_eq_zero (C := C) P hP i (by omega)).mp
        (h_all_sDisc i hi)
    · intro h_sRes
      exact h_sDisc_ne
        ((sDisc_eq_zero_iff_sRes_eq_zero (C := C) P hP j hj).mpr h_sRes)

end Azurite.BPR.Chapter4
