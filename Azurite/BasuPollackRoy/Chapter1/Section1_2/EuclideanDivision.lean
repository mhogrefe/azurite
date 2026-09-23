/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.RingTheory.EuclideanDomain
import Mathlib.RingTheory.Localization.FractionRing

/-!
# Section 1.2: Euclidean Division (preparation for Proposition 1.5)

In this section, $C$ is an algebraically closed field, $D$ is a subring
of $C$, and $K$ is the quotient field of $D$.

If $Q \ne 0$, the *remainder* $\operatorname{Rem}(P, Q)$ is the unique
polynomial $R \in K[X]$ of degree smaller than $\deg Q$ such that
$P = A Q + R$ for some $A \in K[X]$. The *quotient*
$\operatorname{Quo}(P, Q)$ is $A$.

In Mathlib, Euclidean division for polynomials over a field is
provided by the `EuclideanDomain` instance on `Polynomial K` (via
`Polynomial.instEuclideanDomain`). The operators `/` and `%` give
quotient and remainder, with:

- `EuclideanDomain.div_add_mod`: `P = Q * (P / Q) + P % Q`
- `Polynomial.degree_mod_lt`: `(P % Q).degree < Q.degree` for `Q ≠ 0`

There is also `Polynomial.divByMonic` (`/ₘ`) and `Polynomial.modByMonic`
(`%ₘ`) which work over any ring but require the divisor to be monic.
-/

namespace Azurite.BPR

open Polynomial

variable {D : Type*} [CommRing D]
variable {K : Type*} [Field K] [Algebra D K] [IsFractionRing D K]

/-- Quo(P, Q): the quotient in the Euclidean division of P by Q,
    computed in K[X] after mapping from D[X]. -/
noncomputable def Quo (K : Type*) [Field K] [Algebra D K] [IsFractionRing D K]
    (P Q : D[X]) : K[X] :=
  (P.map (algebraMap D K)) / (Q.map (algebraMap D K))

/-- Rem(P, Q): the remainder in the Euclidean division of P by Q,
    computed in K[X] after mapping from D[X]. -/
noncomputable def Rem (K : Type*) [Field K] [Algebra D K] [IsFractionRing D K]
    (P Q : D[X]) : K[X] :=
  (P.map (algebraMap D K)) % (Q.map (algebraMap D K))

/-- Euclidean division equation: P = Q · Quo(P,Q) + Rem(P,Q) in K[X]. -/
theorem map_eq_mul_quo_add_rem (P Q : D[X]) :
    P.map (algebraMap D K) =
    Q.map (algebraMap D K) * Quo K P Q + Rem K P Q :=
  (EuclideanDomain.div_add_mod _ _).symm

/-- deg(Rem(P, Q)) < deg(Q) when Q ≠ 0. -/
theorem degree_rem_lt (P Q : D[X]) (hQ : Q ≠ 0) :
    (Rem K P Q).degree < (Q.map (algebraMap D K)).degree :=
  Polynomial.degree_mod_lt _
    ((Polynomial.map_ne_zero_iff (IsFractionRing.injective D K)).mpr hQ)

end Azurite.BPR
