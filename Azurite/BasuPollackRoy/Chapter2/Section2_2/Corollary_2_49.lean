import Azurite.BasuPollackRoy.Chapter2.Section2_2.Lemma_2_48

/-!
# BPR Corollary 2.49

Every root of `P` is a virtual root of `P`, the virtual multiplicity is at
least the root multiplicity, and their difference is even.

Lemma 2.48 itself lives in
`Azurite.BasuPollackRoy.Chapter2.Section2_2.Lemma_2_48`.

The proof parallels the induction in `lemma_2_48`, but invokes the unnumbered
virtual-multiplicity corollaries (`virtualMultiplicity_derivative_of_root` and
`virtualMultiplicity_diff_of_not_root`) directly — these are the building
blocks that Lemma 2.48 itself is based on.
-/

namespace Azurite.BPR.Lemma_2_48

open Polynomial Azurite.BPR Azurite.BPR.VirtualRoots

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]

/-- **BPR Corollary 2.49.** Every root of `P` is a virtual root of `P`, the
    virtual multiplicity is at least the root multiplicity, and their difference
    is even. -/
theorem corollary_2_49
    (hIVP : HasIntermediateValueProperty R)
    {P : R[X]} (hP : P ≠ 0) (c : R) :
    P.rootMultiplicity c ≤ virtualMultiplicity hIVP hP c ∧
      Even (virtualMultiplicity hIVP hP c - P.rootMultiplicity c) := by
  -- Strong form: prove `∃ k, v(P, c) = μ(P, c) + 2k` by induction on degree.
  suffices H : ∀ (n : ℕ) (P : R[X]) (hP : P ≠ 0), P.natDegree = n → ∀ c,
      ∃ k : ℕ, virtualMultiplicity hIVP hP c =
        P.rootMultiplicity c + 2 * k by
    obtain ⟨k, hk⟩ := H P.natDegree P hP rfl c
    exact ⟨by omega, k, by omega⟩
  intro n
  induction n with
  | zero =>
    intro P hP hn c
    refine ⟨0, ?_⟩
    have hPc : P.eval c ≠ 0 := by
      intro h
      apply hP
      have hPC : P = C (P.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero hn
      rw [hPC, Polynomial.eval_C] at h
      rw [hPC, h, Polynomial.C_0]
    have hrm : P.rootMultiplicity c = 0 :=
      Polynomial.rootMultiplicity_eq_zero hPc
    have hvm : virtualMultiplicity hIVP hP c = 0 := by
      unfold virtualMultiplicity
      rw [virtualRoots_eq_nil_of_natDegree_zero hIVP hP hn]
      rfl
    omega
  | succ n ih =>
    intro P hP hn c
    have hpos : 1 ≤ P.natDegree := by rw [hn]; omega
    have hdP : derivative P ≠ 0 := by
      intro h
      have := Polynomial.derivative_eq_zero.mp h
      rw [hn] at this; omega
    have hdP_deg : (derivative P).natDegree = n := by
      have h := Polynomial.natDegree_eq_of_degree_eq_some
        (Polynomial.degree_derivative (Nat.lt_of_lt_of_le Nat.zero_lt_one hpos).ne')
      rw [hn] at h; omega
    obtain ⟨k', hk'⟩ := ih (derivative P) hdP hdP_deg c
    by_cases hPc : P.eval c = 0
    · -- Root case: `μ(P,c) = μ(P',c) + 1` and `v(P,c) = v(P',c) + 1`.
      refine ⟨k', ?_⟩
      have h46 := virtualMultiplicity_derivative_of_root hIVP hP hdP hPc
      have hrm_pos : 0 < P.rootMultiplicity c :=
        (Polynomial.rootMultiplicity_pos hP).mpr hPc
      have hmu : (derivative P).rootMultiplicity c = P.rootMultiplicity c - 1 :=
        Polynomial.derivative_rootMultiplicity_of_root hPc
      unfold virtualMultiplicity at h46 hk' ⊢
      omega
    · -- Non-root case: `μ(P,c) = 0`; use the trichotomy on `ν` parity.
      have hrm : P.rootMultiplicity c = 0 :=
        Polynomial.rootMultiplicity_eq_zero hPc
      have h46 := virtualMultiplicity_diff_of_not_root hIVP hP hdP hPc
      set ν := (derivative P).rootMultiplicity c with hν_def
      unfold virtualMultiplicity at hk' ⊢
      rw [hrm]
      by_cases hν_even : Even ν
      · rw [if_pos hν_even] at h46
        obtain ⟨j, hj⟩ := hν_even
        refine ⟨j + k', ?_⟩
        unfold virtualMultiplicity at h46
        omega
      · rw [if_neg hν_even] at h46
        obtain ⟨j, hj⟩ := Nat.not_even_iff_odd.mp hν_even
        by_cases hsign : 0 < P.eval c * ((⇑derivative)^[ν + 1] P).eval c
        · rw [if_pos hsign] at h46
          refine ⟨j + k' + 1, ?_⟩
          unfold virtualMultiplicity at h46
          omega
        · rw [if_neg hsign] at h46
          refine ⟨j + k', ?_⟩
          unfold virtualMultiplicity at h46
          omega

end Azurite.BPR.Lemma_2_48
