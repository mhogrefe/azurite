/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzPolynomial.Expand
import Azurite.AzPolynomial.Equiv.Add
import Azurite.AzPolynomial.Equiv.Monomial
import Azurite.AzPolynomial.Equiv.Eval
import Mathlib.Algebra.Polynomial.Expand

/-!
# Equivalence: AzPolynomial.expand ↔ Polynomial.expand

Proves that `AzPolynomial.expand p n` agrees with Mathlib's
`Polynomial.expand R n` and establishes the nth-root property: `z` is a root of
`P(X^n)` iff `z^n` is a root of `P`. Mathlib's `expand` API (`expand_eval`,
`map_expand`, `natDegree_expand`, …) supplies every proof.

## Main results

- `toPoly_expand` — `toPoly (expand p n) = Polynomial.expand R n (toPoly p)`
- `ofPoly_expand` — `(ofPoly q).expand n = ofPoly (Polynomial.expand R n q)`
- `eval_expand` — `eval z (toPoly (expand p n)) = eval (z^n) (toPoly p)`
- `isRoot_expand_iff` — root at `z` ↔ root of `P` at `z^n` (unconditional)
- `isRoot_expand_map_iff` — same across any `f : R →+* S` (unconditional —
  spreading coefficients merges nothing, so no field or injectivity is needed)
- `natDegree_expand` — degree multiplies by `n` (unconditional)
- `leadingCoeff_expand`, `expand_eq_zero_iff` — for `0 < n`
- `expand_one` — `expand p 1 = p`
-/

set_option autoImplicit false

open Polynomial

namespace Azurite.AzPolynomial

variable {R : Type _} [CommRing R] [DecidableEq R]

/-- **Structural spec.** `toPoly (expand p n) = Polynomial.expand R n (toPoly p)`. -/
theorem toPoly_expand (p : AzPolynomial R) (n : ℕ) :
    AzPolynomial.toPoly (p.expand n) = Polynomial.expand R n (AzPolynomial.toPoly p) := by
  rcases eq_or_ne p 0 with rfl | hp
  · rw [zero_expand, toPoly_zero, map_zero]
  · rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [expand_zero p hp, Polynomial.expand_zero, toPoly_C, eval_toPoly]
    · ext j
      rw [AzPolynomial.coeff_toPoly, coeff_expand p hn, Polynomial.coeff_expand hn,
        AzPolynomial.coeff_toPoly]

/-- **`ofPoly` version.** -/
theorem ofPoly_expand (q : Polynomial R) (n : ℕ) :
    (AzPolynomial.ofPoly q).expand n = AzPolynomial.ofPoly (Polynomial.expand R n q) := by
  rw [← toPoly_inj, toPoly_expand, toPoly_ofPoly, toPoly_ofPoly]

/-- **Evaluation identity.** `P(X^n)` evaluated at `z` is `P(z^n)`. -/
theorem eval_expand (p : AzPolynomial R) (n : ℕ) (z : R) :
    Polynomial.eval z (AzPolynomial.toPoly (p.expand n))
      = Polynomial.eval (z ^ n) (AzPolynomial.toPoly p) := by
  rw [toPoly_expand, Polynomial.expand_eval]

/-- **nth-root property.** `z` is a root of `P(X^n)` iff `z^n` is a root of `P`
— unconditionally. -/
theorem isRoot_expand_iff (p : AzPolynomial R) (n : ℕ) (z : R) :
    Polynomial.IsRoot (AzPolynomial.toPoly (p.expand n)) z ↔
    Polynomial.IsRoot (AzPolynomial.toPoly p) (z ^ n) := by
  simp only [Polynomial.IsRoot, eval_expand]

/-- **nth-root property across a ring homomorphism.**

    For any `f : R →+* S` (no field or injectivity hypotheses), `z` is a root
    of `map f (toPoly (expand p n))` iff `z^n` is a root of `map f (toPoly p)`.

    **Application:** if `P ∈ ℤ[X]` is a defining polynomial of an algebraic
    number `α`, then `expand P n` is a defining polynomial of every `n`-th root
    of `α`. -/
theorem isRoot_expand_map_iff {S : Type _} [CommRing S]
    (f : R →+* S) (p : AzPolynomial R) (n : ℕ) (z : S) :
    Polynomial.IsRoot (Polynomial.map f (AzPolynomial.toPoly (p.expand n))) z ↔
    Polynomial.IsRoot (Polynomial.map f (AzPolynomial.toPoly p)) (z ^ n) := by
  simp only [Polynomial.IsRoot, toPoly_expand, Polynomial.map_expand, Polynomial.expand_eval]

/-- The degree multiplies by `n` (unconditionally: `deg · 0 = 0` covers `n = 0`). -/
theorem natDegree_expand (p : AzPolynomial R) (n : ℕ) :
    (p.expand n).natDegree = p.natDegree * n := by
  rw [← AzPolynomial.natDegree_toPoly, toPoly_expand, Polynomial.natDegree_expand,
    AzPolynomial.natDegree_toPoly]

/-- For `0 < n`, the leading coefficient is unchanged. -/
theorem leadingCoeff_expand (p : AzPolynomial R) {n : ℕ} (hn : 0 < n) :
    (p.expand n).leadingCoeff = p.leadingCoeff := by
  rw [← leadingCoeff_toPoly, toPoly_expand, Polynomial.leadingCoeff_expand hn,
    leadingCoeff_toPoly]

/-- For `0 < n`, expansion preserves nonvanishing. -/
theorem expand_eq_zero_iff (p : AzPolynomial R) {n : ℕ} (hn : 0 < n) :
    p.expand n = 0 ↔ p = 0 := by
  rw [← toPoly_inj (q := 0), toPoly_zero, toPoly_expand, Polynomial.expand_eq_zero hn,
    ← toPoly_zero, toPoly_inj]

/-- `expand p 1 = p`. -/
@[simp] theorem expand_one (p : AzPolynomial R) : p.expand 1 = p := by
  rw [← toPoly_inj, toPoly_expand, Polynomial.expand_one]

end Azurite.AzPolynomial
