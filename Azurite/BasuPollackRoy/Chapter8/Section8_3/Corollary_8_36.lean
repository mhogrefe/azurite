/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.BasuPollackRoy.Chapter8.Section8_3.Theorem_8_34

/-!
# BPR Corollary 8.36

The **last nonzero signed subresultant** of `P` and `Q` (the nonzero `sResP_j(P,Q)` of
lowest index, i.e. with `sResP_ℓ(P,Q) = 0` for all `ℓ < j`) is **non-defective** and a
**greatest common divisor** of `P` and `Q`.

This is the bottom of the subresultant chain.  By the gcd branch of the Structure Theorem
(`theorem_8_34`), the subresultants below `deg(gcd P Q)` vanish and `sResP_{deg gcd}` is
associate to `gcd(P,Q)`; hence the lowest nonzero index `j` is exactly `deg(gcd P Q)`, where
the subresultant has degree `j` (non-defective) and is a gcd.  (BPR derive the same via an
`i` with `deg(sResP_{i-1}) = j` and proportionality; the gcd-branch lemmas give it directly
and also cover the coprime case `j = 0`.)
-/

namespace Azurite.BPR.Chapter8

open Polynomial

variable {K : Type*} [Field K]

/-- **BPR Corollary 8.36.**  If `sResP_j(P,Q) ≠ 0` and `sResP_ℓ(P,Q) = 0` for all `ℓ < j`
    (so `sResP_j` is the last nonzero signed subresultant), then `sResP_j(P,Q)` is
    non-defective (degree exactly `j`) and is a greatest common divisor of `P` and `Q`. -/
theorem corollary_8_36 (P Q : K[X]) (hP : P ≠ 0) (hQ : Q ≠ 0)
    (hpq : Q.natDegree < P.natDegree)
    {j : ℕ} (hsj : sResP P Q j ≠ 0) (hlow : ∀ ℓ, ℓ < j → sResP P Q ℓ = 0) :
    IsNonDefective P Q j ∧ Associated (sResP P Q j) (gcd P Q) := by
  have hdq : (gcd P Q).natDegree ≤ Q.natDegree :=
    Polynomial.natDegree_le_of_dvd (gcd_dvd_right P Q) hQ
  have hd_ne : sResP P Q (gcd P Q).natDegree ≠ 0 := sResP_natDegree_gcd_ne_zero P Q hP hQ hpq
  -- the lowest nonzero index `j` is exactly `deg(gcd P Q)`
  have hjeq : j = (gcd P Q).natDegree := by
    refine le_antisymm ?_ ?_
    · by_contra h; exact hd_ne (hlow _ (by omega))
    · by_contra h
      exact hsj (sResP_eq_zero_of_lt_gcd P Q hP hQ hpq (by omega) (by omega))
  have hjq : j ≤ Q.natDegree := by rw [hjeq]; exact hdq
  -- non-defective: `deg(gcd) ≤ deg(sResP_j) ≤ j = deg(gcd)`
  have hnd : (sResP P Q j).natDegree = j := by
    have h1 : (sResP P Q j).natDegree ≤ j :=
      Polynomial.natDegree_le_iff_degree_le.mpr (sResP_degree_le P Q hpq hjq)
    have h2 := natDegree_gcd_le_natDegree_sResP P Q hP hQ hpq hsj
    omega
  refine ⟨show (sResP P Q j).degree = (j : WithBot ℕ) from by
      rw [Polynomial.degree_eq_natDegree hsj, hnd], ?_⟩
  rw [hjeq]; exact associated_sResP_gcd P Q hP hQ hpq rfl

end Azurite.BPR.Chapter8
