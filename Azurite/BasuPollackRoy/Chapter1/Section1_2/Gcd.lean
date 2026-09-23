/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.RingTheory.EuclideanDomain
import Mathlib.Tactic.LinearCombination

/-!
# Section 1.2: Greatest Common Divisor (Definition 1.8)

A *greatest common divisor* of $P$ and $Q$ in $K[X]$ is a polynomial
$G \in K[X]$ such that $G$ divides both $P$ and $Q$, and any common
divisor of $P$ and $Q$ divides $G$. This is a relation, not a function
— GCDs are unique only up to units (nonzero scalars in $K[X]$). In
Mathlib, `GCDMonoid.gcd` picks a canonical representative via the
`EuclideanDomain` instance on `K[X]`.
-/

namespace Azurite.BPR

open Polynomial

variable {K : Type*} [Field K]

open Classical in
noncomputable instance gcdMonoidPolynomial : GCDMonoid K[X] :=
  EuclideanDomain.gcdMonoid K[X]

/-- BPR Definition 1.8: G is a greatest common divisor of P and Q. -/
def IsGCD (G P Q : K[X]) : Prop :=
  G ∣ P ∧ G ∣ Q ∧ ∀ D : K[X], D ∣ P → D ∣ Q → D ∣ G

theorem IsGCD.symm {G P Q : K[X]} (h : IsGCD G P Q) : IsGCD G Q P :=
  ⟨h.2.1, h.1, fun D hQ hP => h.2.2 D hP hQ⟩

/-- Mathlib's `gcd P Q` satisfies the BPR IsGCD relation. -/
theorem gcd_isGCD (P Q : K[X]) : IsGCD (gcd P Q) P Q :=
  ⟨gcd_dvd_left P Q, gcd_dvd_right P Q, fun _ hP hQ => dvd_gcd hP hQ⟩

/-- Any two GCDs in the BPR sense are associates (differ by a unit in K[X]). -/
theorem isGCD_associated {G₁ G₂ P Q : K[X]}
    (h₁ : IsGCD G₁ P Q) (h₂ : IsGCD G₂ P Q) :
    Associated G₁ G₂ :=
  associated_of_dvd_dvd (h₂.2.2 G₁ h₁.1 h₁.2.1) (h₁.2.2 G₂ h₂.1 h₂.2.1)

/-- P is a GCD of P and 0. -/
theorem isGCD_self_zero (P : K[X]) : IsGCD P P 0 :=
  ⟨dvd_refl P, dvd_zero P, fun _ hP _ => hP⟩

/-- Any two GCDs of P and Q divide each other. -/
theorem isGCD_dvd_dvd {G₁ G₂ P Q : K[X]}
    (h₁ : IsGCD G₁ P Q) (h₂ : IsGCD G₂ P Q) :
    G₁ ∣ G₂ ∧ G₂ ∣ G₁ :=
  ⟨h₂.2.2 G₁ h₁.1 h₁.2.1, h₁.2.2 G₂ h₂.1 h₂.2.1⟩

/-- Any two GCDs of P and Q have the same degree. -/
theorem isGCD_degree_eq {G₁ G₂ P Q : K[X]}
    (h₁ : IsGCD G₁ P Q) (h₂ : IsGCD G₂ P Q) :
    G₁.degree = G₂.degree := by
  have ⟨h12, h21⟩ := isGCD_dvd_dvd h₁ h₂
  exact degree_eq_degree_of_associated (associated_of_dvd_dvd h12 h21)

/-- The degree of the GCD of P and Q. Well-defined since any two GCDs
    have the same degree (by `isGCD_degree_eq`). -/
noncomputable def degGcd (P Q : K[X]) : WithBot ℕ := (gcd P Q).degree

/-- Any IsGCD witness has the same degree as `degGcd P Q`. -/
theorem isGCD_degree_eq_degGcd {G P Q : K[X]} (h : IsGCD G P Q) :
    G.degree = degGcd P Q :=
  isGCD_degree_eq h (gcd_isGCD P Q)

/-- Negating a polynomial doesn't affect GCD. -/
theorem IsGCD.neg_right {G P Q : K[X]} (h : IsGCD G P Q) : IsGCD G P (-Q) :=
  ⟨h.1, dvd_neg.mpr h.2.1, fun E hEP hEQ => h.2.2 E hEP (dvd_neg.mp hEQ)⟩

theorem IsGCD.of_neg_right {G P Q : K[X]} (h : IsGCD G P (-Q)) : IsGCD G P Q :=
  neg_neg Q ▸ h.neg_right

theorem isGCD_neg_right_iff {G P Q : K[X]} : IsGCD G P (-Q) ↔ IsGCD G P Q :=
  ⟨IsGCD.of_neg_right, IsGCD.neg_right⟩

/-- GCD is preserved under pseudo-division: if `C(c) * P = A * Q + R`
    with `c ≠ 0` (so `C(c)` is a unit in `K[X]`), then
    `IsGCD G P Q ↔ IsGCD G Q R`. This is the key step that lets GCD be
    computed by iterated pseudo-remainders. -/
theorem isGCD_of_pseudo_div {G P Q R A : K[X]} {c : K} (hc : c ≠ 0)
    (h : Polynomial.C c * P = A * Q + R) :
    IsGCD G P Q ↔ IsGCD G Q R := by
  have hunit : IsUnit (Polynomial.C c) :=
    Polynomial.isUnit_C.mpr (IsUnit.mk0 c hc)
  have hR : R = Polynomial.C c * P - A * Q := by linear_combination -h
  constructor
  · -- Forward: IsGCD G P Q → IsGCD G Q R
    rintro ⟨hGP, hGQ, hmax⟩
    refine ⟨hGQ, ?_, fun E hEQ hER => hmax E ?_ hEQ⟩
    · -- G ∣ R
      rw [hR]; exact dvd_sub (dvd_mul_of_dvd_right hGP _) (dvd_mul_of_dvd_right hGQ _)
    · -- E ∣ P
      exact hunit.dvd_mul_left.mp (h ▸ dvd_add (dvd_mul_of_dvd_right hEQ _) hER)
  · -- Backward: IsGCD G Q R → IsGCD G P Q
    rintro ⟨hGQ, hGR, hmax⟩
    refine ⟨?_, hGQ, fun E hEP hEQ => hmax E hEQ ?_⟩
    · -- G ∣ P
      exact hunit.dvd_mul_left.mp (h ▸ dvd_add (dvd_mul_of_dvd_right hGQ _) hGR)
    · -- E ∣ R
      rw [hR]; exact dvd_sub (dvd_mul_of_dvd_right hEP _) (dvd_mul_of_dvd_right hEQ _)

end Azurite.BPR
