/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.BasuPollackRoy.Chapter8.Section8_3.Corollary_8_35
import Azurite.BasuPollackRoy.Chapter1.Section1_2.Definition1_7

/-!
# BPR Corollary 8.37

When all signed subresultants `sResP_j(P,Q)` (`j = 0, …, p`) are non-defective, the signed
subresultant polynomials are proportional, *up to a square*, to the signed remainder
sequence `SRemS_ℓ(P,Q)`:

  `sResP_{p-ℓ}(P,Q) = a² · SRemS_ℓ(P,Q)`  for some `a ≠ 0`.

Proved by (two-step) induction on `ℓ`: the cases `ℓ = 0, 1` are `sResP_p = P = SRemS_0` and
`sResP_{p-1} = Q = SRemS_1`; the step uses the non-defective specialization of
Corollary 8.35, `s_j² sResP_{j-2} = -Rem(s_{j-1}² sResP_j, sResP_{j-1})`, together with the
defining recurrence of the signed remainder sequence.
-/

namespace Azurite.BPR.Chapter8

open Polynomial

variable {K : Type*} [Field K]

/-- The **non-defective specialization of Corollary 8.35**: when `sResP_j` and `sResP_{j-1}`
    are both non-defective (`2 ≤ j ≤ p`), the recurrence has a square on each side:
    `s_j² sResP_{j-2} = -Rem(s_{j-1}² sResP_j, sResP_{j-1})`.  (In the non-defective case
    `t_{j-1} = s_{j-1}`, turning the mixed `s_{j-1} t_{j-1}` of Corollary 8.35 into
    `s_{j-1}²`.) -/
theorem corollary_8_35_nondefective (P Q : K[X]) (hP : P ≠ 0) (hQ : Q ≠ 0)
    (hpq : Q.natDegree < P.natDegree) (hq1 : 1 ≤ Q.natDegree)
    {j : ℕ} (hj2 : 2 ≤ j) (hjp : j ≤ P.natDegree) (hj1q : j - 1 ≤ Q.natDegree)
    (hndj : (sResP P Q j).natDegree = j) (hndj1 : (sResP P Q (j - 1)).natDegree = j - 1) :
    C (sBPR P Q j) ^ 2 * sResP P Q (j - 2)
      = -((C (sBPR P Q (j - 1)) ^ 2 * sResP P Q j) % sResP P Q (j - 1)) := by
  have hsj : sResP P Q j ≠ 0 := fun h => by rw [h, Polynomial.natDegree_zero] at hndj; omega
  have hsj1 : sResP P Q (j - 1) ≠ 0 := fun h => by
    rw [h, Polynomial.natDegree_zero] at hndj1; omega
  have htj1 : tBPR P Q (j - 1) = sBPR P Q (j - 1) := by
    rw [tBPR, ite_eq_right (show j - 1 ≠ P.natDegree by omega),
      sBPR, ite_eq_right (show j - 1 ≠ P.natDegree by omega)]
    exact leadingCoeff_sResP_eq_sRes P Q hpq hj1q
      (show (sResP P Q (j - 1)).degree = ((j - 1 : ℕ) : WithBot ℕ) from by
        rw [Polynomial.degree_eq_natDegree hsj1, hndj1])
  have hcor := corollary_8_35 P Q hP hQ hpq hq1 (i := j + 1) (j := j)
    (by omega) (by omega) (by omega) (by rw [Nat.add_sub_cancel]; exact hsj)
    (by rw [Nat.add_sub_cancel]; exact hndj) (k := j - 1) hsj1 hndj1 (by omega)
  rw [show j - 1 - 1 = j - 2 from by omega, htj1, ← pow_two] at hcor
  exact hcor

/-- **BPR Corollary 8.37.**  When every signed subresultant `sResP_j(P,Q)` (`j = 0, …, p`)
    is non-defective, the signed subresultant polynomials are proportional, *up to a square*,
    to the signed remainder sequence: for `ℓ ≤ p` there is a nonzero `a` with
    `sResP_{p-ℓ}(P,Q) = a² · SRemS_ℓ(P,Q)`. -/
theorem corollary_8_37 (P Q : K[X]) (hP : P ≠ 0) (hQ : Q ≠ 0)
    (hpq : Q.natDegree < P.natDegree)
    (hnd : ∀ j, j ≤ P.natDegree → IsNonDefective P Q j)
    {ℓ : ℕ} (hℓ : ℓ ≤ P.natDegree) :
    ∃ a : K, a ≠ 0 ∧ sResP P Q (P.natDegree - ℓ) = C (a ^ 2) * SRemS P Q ℓ := by
  have hnd_deg : ∀ j, j ≤ P.natDegree → (sResP P Q j).natDegree = j :=
    fun j hj => Polynomial.natDegree_eq_of_degree_eq_some (hnd j hj)
  have hnd_ne : ∀ j, j ≤ P.natDegree → sResP P Q j ≠ 0 := by
    intro j hj h
    have hd : (sResP P Q j).degree = (j : WithBot ℕ) := hnd j hj
    rw [h, Polynomial.degree_zero] at hd
    exact absurd hd (by simp)
  have hq : Q.natDegree = P.natDegree - 1 := by
    have h := hnd_deg (P.natDegree - 1) (by omega)
    rwa [sResP_pm1_eq_Q P Q hQ hpq] at h
  have hsBPR_ne : ∀ j, j ≤ P.natDegree → sBPR P Q j ≠ 0 := by
    intro j hj
    by_cases hjp : j = P.natDegree
    · rw [sBPR, ite_eq_left hjp]; exact one_ne_zero
    · rw [sBPR, ite_eq_right hjp,
        ← leadingCoeff_sResP_eq_sRes P Q hpq (by omega) (hnd j hj)]
      exact Polynomial.leadingCoeff_ne_zero.mpr (hnd_ne j hj)
  -- two-step induction on `ℓ`
  suffices key : ∀ ℓ, ℓ ≤ P.natDegree → ∃ a : K, a ≠ 0 ∧
      sResP P Q (P.natDegree - ℓ) = C (a ^ 2) * SRemS P Q ℓ from key ℓ hℓ
  intro ℓ
  induction ℓ using Nat.strong_induction_on with
  | _ ℓ ih =>
  intro hℓp
  match ℓ, ih, hℓp with
  | 0, _, _ =>
    exact ⟨1, one_ne_zero, by
      rw [Nat.sub_zero, sResP_eq_self P Q hpq, SRemS_fst, one_pow, map_one, one_mul]⟩
  | 1, _, _ =>
    exact ⟨1, one_ne_zero, by
      rw [sResP_pm1_eq_Q P Q hQ hpq, SRemS_snd, one_pow, map_one, one_mul]⟩
  | m + 2, ih, hℓp =>
    -- recurrence at `j = p - m`; produces `sResP_{p-(m+2)}` from `sResP_{p-m}`, `sResP_{p-(m+1)}`
    have hcor := corollary_8_35_nondefective P Q hP hQ hpq (by omega) (j := P.natDegree - m)
      (by omega) (by omega) (by omega) (hnd_deg _ (by omega)) (hnd_deg _ (by omega))
    rw [show P.natDegree - m - 2 = P.natDegree - (m + 2) from by omega,
        show P.natDegree - m - 1 = P.natDegree - (m + 1) from by omega] at hcor
    obtain ⟨c, hc_ne, hc⟩ := ih m (by omega) (by omega)
    obtain ⟨b, hb_ne, hb⟩ := ih (m + 1) (by omega) (by omega)
    -- `SRemS_{m+1} ≠ 0`, so the remainder-sequence recurrence applies at `m`
    have hSm1_ne : SRemS P Q (m + 1) ≠ 0 := fun h =>
      hnd_ne (P.natDegree - (m + 1)) (by omega) (by rw [hb, h, mul_zero])
    have hsrem : SRemS P Q m % SRemS P Q (m + 1) = -SRemS P Q (m + 2) := by
      rw [show SRemS P Q (m + 2) = -(SRemS P Q m % SRemS P Q (m + 1)) from by
        rw [SRemS, ite_eq_right hSm1_ne], neg_neg]
    rw [hc, hb] at hcor
    -- simplify the right-hand side to `C(t² c²) · SRemS_{m+2}`, `t = sBPR_{p-(m+1)}`
    have hrhs : -((C (sBPR P Q (P.natDegree - (m + 1))) ^ 2 * (C (c ^ 2) * SRemS P Q m))
            % (C (b ^ 2) * SRemS P Q (m + 1)))
        = C (sBPR P Q (P.natDegree - (m + 1)) ^ 2 * c ^ 2) * SRemS P Q (m + 2) := by
      rw [show C (sBPR P Q (P.natDegree - (m + 1))) ^ 2 * (C (c ^ 2) * SRemS P Q m)
            = C (sBPR P Q (P.natDegree - (m + 1)) ^ 2 * c ^ 2) * SRemS P Q m from by
          rw [← C_pow, ← mul_assoc, ← C_mul],
        rem_C_mul, mod_C_mul_right _ _ (pow_ne_zero 2 hb_ne), hsrem, mul_neg, neg_neg]
    rw [hrhs] at hcor
    -- divide by `C(sBPR_{p-m})²`; the proportionality constant is the square of
    -- `sBPR_{p-(m+1)} · c / sBPR_{p-m}`
    have hsm_ne : sBPR P Q (P.natDegree - m) ≠ 0 := hsBPR_ne _ (by omega)
    refine ⟨sBPR P Q (P.natDegree - (m + 1)) * c * (sBPR P Q (P.natDegree - m))⁻¹,
      mul_ne_zero (mul_ne_zero (hsBPR_ne _ (by omega)) hc_ne) (inv_ne_zero hsm_ne), ?_⟩
    apply mul_left_cancel₀ (pow_ne_zero 2 (show C (sBPR P Q (P.natDegree - m)) ≠ 0 by
      rwa [Ne, Polynomial.C_eq_zero]))
    rw [hcor]
    conv_rhs => rw [← C_pow, ← mul_assoc, ← C_mul]
    congr 1
    rw [Polynomial.C_inj]
    field_simp

end Azurite.BPR.Chapter8
