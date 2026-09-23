/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.RingTheory.EuclideanDomain

/-!
# Remark 1.4

Two consequences of Euclidean division over a field $K$:

1. Scaling the dividend and the divisor by nonzero constants $a, b \in K$
   commutes with taking the remainder up to scaling:
   $\operatorname{Rem}(a P, b Q) = a \cdot \operatorname{Rem}(P, Q)$.
2. At a root $x$ of $Q$, evaluating the remainder of $P$ by $Q$ at $x$
   recovers $P(x)$: $\operatorname{Rem}(P, Q)(x) = P(x)$.
-/

namespace Azurite.BPR

open Polynomial

variable {K : Type*} [Field K]

/-- Remark 1.4, first part. Rem(aP, bQ) = a · Rem(P, Q) for a, b ∈ K with b ≠ 0. -/
theorem rem_C_mul_C_mul (a b : K) (hb : b ≠ 0) (P Q : K[X]) (hQ : Q ≠ 0) :
    Polynomial.C a * P % (Polynomial.C b * Q) = Polynomial.C a * (P % Q) := by
  simp only [mod_def, leadingCoeff_mul, leadingCoeff_C]
  rw [mul_inv, Polynomial.C_mul]
  have hNorm : Polynomial.C b * Q * (Polynomial.C b⁻¹ * Polynomial.C Q.leadingCoeff⁻¹) =
      Q * Polynomial.C Q.leadingCoeff⁻¹ := by
    calc Polynomial.C b * Q * (Polynomial.C b⁻¹ * Polynomial.C Q.leadingCoeff⁻¹)
        = (Polynomial.C b * Polynomial.C b⁻¹) *
          (Q * Polynomial.C Q.leadingCoeff⁻¹) := by ring
      _ = Q * Polynomial.C Q.leadingCoeff⁻¹ := by
          rw [← Polynomial.C_mul, mul_inv_cancel₀ hb, Polynomial.C_1, one_mul]
  rw [hNorm]
  set M := Q * Polynomial.C Q.leadingCoeff⁻¹
  have hM : M.Monic := monic_mul_leadingCoeff_inv hQ
  have hdvd : M ∣ (Polynomial.C a * P - Polynomial.C a * (P %ₘ M)) := by
    rw [← mul_sub]
    have : P - P %ₘ M = M * (P /ₘ M) := by
      have h := modByMonic_add_div P M
      calc P - P %ₘ M = (P %ₘ M + M * (P /ₘ M)) - P %ₘ M := by rw [h]
        _ = M * (P /ₘ M) := by ring
    rw [this]; exact ⟨Polynomial.C a * (P /ₘ M), by ring⟩
  rw [modByMonic_eq_of_dvd_sub hM hdvd, modByMonic_eq_self_iff hM]
  calc (Polynomial.C a * (P %ₘ M)).degree
      ≤ (P %ₘ M).degree := by
        by_cases ha : a = 0 <;> simp_all
    _ < M.degree := degree_modByMonic_lt P hM

/-- Remark 1.4, second part. At a root x of Q, Rem(P, Q)(x) = P(x). -/
theorem eval_mod_at_root (P Q : K[X]) (x : K) (hx : Polynomial.eval x Q = 0) :
    Polynomial.eval x (P % Q) = Polynomial.eval x P := by
  have h := EuclideanDomain.div_add_mod P Q
  have : Polynomial.eval x P = Polynomial.eval x (Q * (P / Q) + P % Q) := by rw [h]
  rw [this, eval_add, eval_mul, hx, zero_mul, zero_add]

end Azurite.BPR
