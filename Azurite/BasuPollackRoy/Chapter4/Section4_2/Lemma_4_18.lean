/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.BasuPollackRoy.Chapter4.Section4_2.ResEqResultant

/-!
# BPR Lemma 4.18 (Res part): resultant under a Euclidean step

For polynomials `P, Q` with `P = C·Q + R` and `deg R < deg Q ≤ deg P`,
BPR Lemma 4.18 asserts

  `Res(P, Q) = (-1)^{p·q} · b_q^{p-r} · Res(Q, R)`,

where `p, q, r` are the natural degrees of `P, Q, R` and `b_q` is the
leading coefficient of `Q`.

## Strategy

Our `Res P Q` agrees with Mathlib's
`Polynomial.resultant P Q P.natDegree Q.natDegree` via the
`Res_eq_resultant` bridge. The identity then follows from three Mathlib
facts —
`Polynomial.resultant_add_mul_left` (kills the `C·Q` term),
`Polynomial.resultant_comm` (gives the `(-1)^{p·q}` factor), and
`Polynomial.resultant_add_right_deg` (gives the `b_q^{p-r}` factor) —
chained at the Mathlib level and transported back across the bridge.
-/

namespace Azurite.BPR.Chapter4

open Polynomial

variable {D : Type*} [CommRing D]

/-! ### Lemma 4.18 (Res part) -/

/-- **BPR Lemma 4.18 (Res part).** For `P = C·Q + R` with `R.natDegree ≤
    P.natDegree` and `C.natDegree + Q.natDegree ≤ P.natDegree`,

      `Res(P, Q) = (-1)^{p·q} · b_q^{p-r} · Res(Q, R)`,

    where `p := P.natDegree`, `q := Q.natDegree`, `r := R.natDegree`,
    and `b_q := Q.leadingCoeff`.

    The hypothesis `C.natDegree + Q.natDegree ≤ P.natDegree` is exactly
    BPR's ``$C$ is the quotient of $P/Q$'' (when `deg R < deg Q ≤ deg P`,
    we have `deg(C·Q) = deg P` and so `deg C + deg Q = deg P`).
    The hypothesis `R.natDegree ≤ P.natDegree` is implied by
    `R.natDegree < Q.natDegree ≤ P.natDegree` in BPR's setting. -/
theorem Lemma_4_18_Res (P Q C R : D[X])
    (h_C : C.natDegree + Q.natDegree ≤ P.natDegree)
    (h_R : R.natDegree ≤ P.natDegree)
    (h_decomp : P = C * Q + R) :
    Res P Q =
      (-1) ^ (P.natDegree * Q.natDegree) *
        Q.leadingCoeff ^ (P.natDegree - R.natDegree) * Res Q R := by
  -- Bridge both resultants to Mathlib's `Polynomial.resultant`.
  rw [Res_eq_resultant P Q, Res_eq_resultant Q R]
  -- Rewrite ONLY the first arg of the LHS resultant (the polynomial `P`):
  -- replace it with `R + Q * C`, leaving `P.natDegree` intact.
  have h_decomp' : P = R + Q * C := by rw [h_decomp]; ring
  nth_rewrite 1 [h_decomp']
  -- Apply `resultant_add_mul_left` to kill the `Q * C` term.
  rw [Polynomial.resultant_add_mul_left R Q C P.natDegree Q.natDegree h_C le_rfl]
  -- Apply `resultant_comm` to introduce `(-1)^{p*q}` and swap.
  rw [Polynomial.resultant_comm R Q P.natDegree Q.natDegree]
  -- Rewrite `P.natDegree = R.natDegree + (P.natDegree - R.natDegree)`,
  -- then apply `resultant_add_right_deg` to introduce `b_q^{p-r}`.
  rw [show P.natDegree = R.natDegree + (P.natDegree - R.natDegree) from by omega]
  rw [Polynomial.resultant_add_right_deg Q R Q.natDegree R.natDegree
        (P.natDegree - R.natDegree) le_rfl]
  rw [show R.natDegree + (P.natDegree - R.natDegree) - R.natDegree =
        P.natDegree - R.natDegree from by omega]
  -- `Q.coeff Q.natDegree = Q.leadingCoeff`.
  rw [show Q.coeff Q.natDegree = Q.leadingCoeff from rfl]
  ring

/-! ### BPR notation Θ and Lemma 4.18 (Θ part) -/

section Theta

variable {K : Type*} [Field K]

/-- BPR's Θ symbol (asymmetric form): `Θ(P, Q) := a_p^q · ∏_i Q(x_i)`,
    the product taken over the multiset of roots `x_i` of `P`. For
    polynomials that split over `K`, this matches BPR's symmetric formula
    `Θ(P, Q) = a_p^q b_q^p ∏(x_i - y_j)`, since
    `Q.eval x = b_q · ∏_j (x - y_j)`. -/
noncomputable def Θ (P Q : K[X]) (q : ℕ) : K :=
  P.leadingCoeff ^ q * (P.roots.map Q.eval).prod

/-- When `P` splits and `Q.natDegree ≤ q`, the BPR symbol `Θ(P, Q)`
    coincides with Mathlib's resultant `resultant P Q P.natDegree q`. -/
theorem Θ_eq_resultant (P Q : K[X]) (q : ℕ) (hP : P.Splits)
    (hQ : Q.natDegree ≤ q) :
    Θ P Q q = Polynomial.resultant P Q P.natDegree q := by
  unfold Θ
  exact (Polynomial.resultant_eq_prod_eval P Q q hQ hP).symm

/-- **BPR Lemma 4.18 (Θ part).** Under the same algebraic hypotheses as
    the Res part plus the splitting hypotheses on `P` and `Q`,

      `Θ(P, Q) = (-1)^{p·q} · b_q^{p-r} · Θ(Q, R)`. -/
theorem Lemma_4_18_Theta (P Q C R : K[X])
    (h_C : C.natDegree + Q.natDegree ≤ P.natDegree)
    (h_R : R.natDegree ≤ P.natDegree)
    (h_P_splits : P.Splits) (h_Q_splits : Q.Splits)
    (h_decomp : P = C * Q + R) :
    Θ P Q Q.natDegree =
      (-1) ^ (P.natDegree * Q.natDegree) *
        Q.leadingCoeff ^ (P.natDegree - R.natDegree) * Θ Q R R.natDegree := by
  rw [Θ_eq_resultant P Q Q.natDegree h_P_splits le_rfl,
      Θ_eq_resultant Q R R.natDegree h_Q_splits le_rfl]
  have h_decomp' : P = R + Q * C := by rw [h_decomp]; ring
  nth_rewrite 1 [h_decomp']
  rw [Polynomial.resultant_add_mul_left R Q C P.natDegree Q.natDegree h_C le_rfl]
  rw [Polynomial.resultant_comm R Q P.natDegree Q.natDegree]
  rw [show P.natDegree = R.natDegree + (P.natDegree - R.natDegree) from by omega]
  rw [Polynomial.resultant_add_right_deg Q R Q.natDegree R.natDegree
        (P.natDegree - R.natDegree) le_rfl]
  rw [show R.natDegree + (P.natDegree - R.natDegree) - R.natDegree =
        P.natDegree - R.natDegree from by omega]
  rw [show Q.coeff Q.natDegree = Q.leadingCoeff from rfl]
  ring

end Theta

end Azurite.BPR.Chapter4
