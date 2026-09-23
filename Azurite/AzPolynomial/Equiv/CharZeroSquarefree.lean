/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.RingTheory.Polynomial.Content
import Mathlib.Algebra.Squarefree.Basic

/-!
# Squarefree ⇒ coprime-with-derivative over a char-0 UFD (primitive case)

Over a *field*, a polynomial is squarefree iff it is coprime with its derivative
(`Polynomial.Separable`), via `PerfectField.separable_iff_squarefree`. That
equivalence is **false** over a non-field char-0 UFD: e.g. `2·X ∈ ℤ[X]` is
squarefree but `IsCoprime (2X) 2` fails.

The Yun square-free-factorization correctness only ever applies this fact to
**primitive** squarefree polynomials (the multiplicity classes of a primitive
input). For those, the "no repeated irreducible factor" argument goes through
*elementarily* over any char-0 UFD — no `Separable`, no `PerfectField`:

* an irreducible factor `q` of a primitive `p` has positive degree (a constant
  irreducible would divide the primitive content, hence be a unit);
* if `p` is squarefree, `q` occurs exactly once, so `q ∣ p'` would force
  `q ∣ q'`, impossible since `q' ≠ 0` (char 0, `deg q ≥ 1`) has strictly smaller
  degree.

This is the crux enabler for generalizing Yun's algorithm correctness from
`[Field K]` to a char-0 UFD coefficient ring (unblocking the multivariate Yun,
which runs the univariate algorithm over the *non-field* tower ring
`AzMvPolynomial n AzInt ord`).
-/

open Polynomial

/-- An irreducible factor of a **primitive squarefree** polynomial over a char-0
UFD does not divide its derivative — the elementary degree/content replacement
for the field-only `Squarefree → Separable`. -/
theorem primitive_squarefree_irreducible_not_dvd_derivative
    {R : Type _} [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R] [CharZero R]
    {p : Polynomial R} (hprim : p.IsPrimitive) (hsq : Squarefree p)
    {q : Polynomial R} (hq : Irreducible q) (hqp : q ∣ p) :
    ¬ q ∣ derivative p := by
  intro hqd
  obtain ⟨B, hB⟩ := hqp
  have hprime : Prime q := (UniqueFactorizationMonoid.irreducible_iff_prime).mp hq
  -- `q` occurs exactly once in `p`, so `q ∤ B`
  have hqB : ¬ q ∣ B := by
    rintro ⟨C, hC⟩
    exact hq.not_isUnit (hsq q ⟨C, by rw [hB, hC]; ring⟩)
  have hderiv : derivative p = derivative q * B + q * derivative B := by
    rw [hB, derivative_mul]
  -- from `q ∣ p' = q'·B + q·B'`, get `q ∣ q'·B`
  have hqqB : q ∣ derivative q * B := by
    have hsub := dvd_sub hqd (dvd_mul_right q (derivative B))
    rwa [hderiv, add_sub_cancel_right] at hsub
  rcases hprime.dvd_mul.mp hqqB with hqq' | hqB'
  · -- `q ∣ q'` is impossible: constant `q` contradicts primitivity, else degrees
    by_cases hdeg : q.natDegree = 0
    · have hqC : q = C (q.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero hdeg
      have hu : IsUnit (q.coeff 0) := hprim _ (hqC ▸ (⟨B, hB⟩ : q ∣ p))
      exact hq.not_isUnit (hqC ▸ hu.map C)
    · have hq'0 : derivative q ≠ 0 := derivative_ne_zero.mpr hdeg
      have h1 : q.natDegree ≤ (derivative q).natDegree := natDegree_le_of_dvd hqq' hq'0
      have h2 : (derivative q).natDegree < q.natDegree := natDegree_derivative_lt hdeg
      omega
  · exact hqB hqB'

/-- **`IsRelPrime` with the derivative** for a primitive squarefree polynomial over
a char-0 UFD — the direct char-0-UFD replacement for `Polynomial.Separable`
(= `IsCoprime p p'`, which needs a field). Every common divisor of `p` and `p'`
is a unit, since any non-unit common divisor would have an irreducible factor
dividing both, contradicting the previous lemma. -/
theorem primitive_squarefree_isRelPrime_derivative
    {R : Type _} [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R] [CharZero R]
    {p : Polynomial R} (hprim : p.IsPrimitive) (hsq : Squarefree p) :
    IsRelPrime p (derivative p) := by
  intro d hdp hdp'
  by_contra hu
  have hp0 : p ≠ 0 := hsq.ne_zero
  have hd0 : d ≠ 0 := fun h => hp0 (by simpa [h] using hdp)
  obtain ⟨q, hq, hqd⟩ := WfDvdMonoid.exists_irreducible_factor hu hd0
  exact primitive_squarefree_irreducible_not_dvd_derivative hprim hsq hq
    (hqd.trans hdp) (hqd.trans hdp')
