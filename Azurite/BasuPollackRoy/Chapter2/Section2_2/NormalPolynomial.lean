/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Mathlib.Algebra.Polynomial.Degree.Defs

/-!
# BPR Definition: Normal polynomial

A polynomial `A = a_p X^p + ⋯ + a_0` with non-negative coefficients is *normal* if:
(a) `a_p > 0`,
(b) `a_k² ≥ a_{k-1} · a_{k+1}` for all indices `k` (log-concavity),
(c) `a_j > 0` and `a_h > 0` with `j < h` imply `a_{j+1}, …, a_{h-1}` are all `> 0`
    (contiguous positive support),
with the convention `a_i = 0` for `i < 0` or `i > p`.

Under this convention the log-concavity condition at `k = 0` reads
`a_0² ≥ 0 · a_1 = 0` and at `k = p` reads `a_p² ≥ a_{p-1} · 0 = 0`, both automatic;
the substantive content is `1 ≤ k ≤ p - 1`. We state it as
`a_k · a_{k+2} ≤ a_{k+1}²` for all `k : ℕ` — equivalent, and avoids `ℕ`-subtraction.
-/

namespace Azurite.BPR

open Polynomial

variable {R : Type*}

/-- **BPR Definition (normal polynomial).**
`P` is *normal* if every coefficient is non-negative, the leading coefficient is
strictly positive, the coefficient sequence is log-concave, and its positive support
is contiguous (no interior zeros between two positive coefficients). -/
structure IsNormal [CommSemiring R] [PartialOrder R] (P : R[X]) : Prop where
  /-- (BPR prefix) All coefficients are non-negative. -/
  coeff_nonneg : ∀ i, 0 ≤ P.coeff i
  /-- (BPR condition a) The leading coefficient is strictly positive. -/
  leading_pos : 0 < P.leadingCoeff
  /-- (BPR condition b) Log-concavity: `a_k · a_{k+2} ≤ a_{k+1}^2` for all `k`.
      Equivalent to BPR's `a_k² ≥ a_{k-1} · a_{k+1}` for `1 ≤ k ≤ p - 1`; the
      boundary cases `k = 0` and `k = p` are automatic under the convention
      `a_i = 0` for `i < 0` or `i > p`. -/
  log_concave : ∀ k, P.coeff k * P.coeff (k + 2) ≤ P.coeff (k + 1) ^ 2
  /-- (BPR condition c) Contiguous positive support: no interior gaps. -/
  no_gap : ∀ {j h : ℕ}, j < h → 0 < P.coeff j → 0 < P.coeff h →
    ∀ {i : ℕ}, j < i → i < h → 0 < P.coeff i

end Azurite.BPR
