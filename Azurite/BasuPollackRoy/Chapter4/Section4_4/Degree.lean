/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# BPR §4.4.2 (Hilbert's Nullstellensatz) — degree and homogeneity

The opening definitions of BPR §4.4.2 are all provided by Mathlib; this module anchors the
relevant declarations in the Azurite import graph for the blueprint:

* the **degree of a monomial** `X^α = X_k^{α_k} ⋯ X_1^{α_1}` is the sum of the degrees with
  respect to each variable, `∑_i α_i`; this is `MvPolynomial.totalDegree` of the monomial, with
  `MvPolynomial.totalDegree_monomial : c ≠ 0 → (monomial s c).totalDegree = s.sum (fun _ e => e)`;
* the **degree of a polynomial** `P` in `k` variables, denoted `deg(P)`, is the maximum degree
  of its monomials, `MvPolynomial.totalDegree P = P.support.sup (fun s => s.sum fun _ e => e)`;
* a polynomial is **homogeneous** (of degree `n`) if all its monomials have the same degree `n`:
  `MvPolynomial.IsHomogeneous φ n` (= `IsWeightedHomogeneous 1 φ n`), with
  `MvPolynomial.IsHomogeneous.totalDegree_le : φ.IsHomogeneous n → φ.totalDegree ≤ n`.
-/
