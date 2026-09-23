/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

/-
  **Implementation paper, §4 opening and Test (4.2): the `n − 1`
  side of the Lucas–Lehmer stage.**

  The Lucas–Lehmer stage lets §5 select fewer `q`-primes, and is
  cheap next to the Jacobi-sum tests.  The early-exit condition
  (4.1) — `n < max(f⁻, f⁺)·f⁻·f⁺·B³` lets the stage prove
  primality outright, a refinement (dropping a factor 2) of the
  classical bound; its proof is deferred by the paper to
  Remark (4.5), where we will meet it with the C&P §4.1/§4.2
  BLS-combination inventory.

  **Test (4.2)** (for odd, not necessarily prime `p ∣ n − 1`):
  search the first 50 primes for `x` with
  `x^((n−1)/p) ≢ 1 (mod n)` (none found ⟹ the test *fails* — a
  give-up branch, cap 50); check `x^(n−1) ≡ 1 (mod n)` (else
  composite, by Fermat — Mathlib's
  `ZMod.pow_card_sub_one_eq_one`); accumulate
  `prod ← prod·(x^((n−1)/p) − 1) mod n`, and if `prod` becomes
  `0`, the *old* `prod` shared a factor with `n` and `n` is
  composite — the verdict `zmod_mul_ne_zero_of_prime` below: for
  prime `n` the ring `ℤ/n` has no zero divisors, so a vanishing
  product convicts.  (Generator-side, `gcd(old prod, n)` then
  *extracts* the factor.)

  The structural identification: **Test (4.2) is the
  (10.4)-check-suite of Method (10.3) at `f = 1`, `F = ℤ/nℤ`** —
  the found `x` is the `β`, `x^(n−1) = 1` is the first check,
  `ρ = id` trivializes `ρ(β) = β^n`, and the `prod`-mechanism
  certifies the unit conditions `x^((n−1)/p) − 1 ∈ F^*`
  collectively (a product is a unit only if every factor is).
  Consequently the flag-side elements
  `β_{p^l}^i = x^(i(n−1)/p^l)` handed to step (i2a) satisfy the
  `lambdaHom`-input condition — `β_{p^l}^1` is a zero of
  `Φ_{p^l}` in `ℤ/n` — as a *verbatim instance* of the (10.3)
  root lemma: `beta_zero_of_cyclotomic` below.
-/
import Azurite.CohenLenstra.Method_10_3

namespace Azurite

namespace CL

open Polynomial

/-- **The (4.2) `prod`-verdict**: over a prime modulus, a product
of nonzero residues is nonzero — so `prod = 0` proves `n`
composite (the old `prod` shared a factor with `n`). -/
theorem zmod_mul_ne_zero_of_prime {n : ℕ} (hn : n.Prime)
    {a b : ZMod n} (ha : a ≠ 0) (hb : b ≠ 0) : a * b ≠ 0 := by
  have : Fact n.Prime := ⟨hn⟩
  exact mul_ne_zero ha hb

/-- **The (4.2) → (i2a) hand-off**: the data certified by
Test (4.2) — `p^l ∣ n − 1`, `x^(n−1) = 1`, and the unit condition
`x^((n−1)/p) − 1 ∈ (ℤ/n)^*` (from the `prod`-mechanism) — makes
`β_{p^l} = x^((n−1)/p^l)` a zero of `Φ_{p^l}` in `ℤ/nℤ`: exactly
the `lambdaHom`-input of Method (10.3) at `f = 1`, by the root
lemma `eval₂_cyclotomic_prime_pow_eq_zero`. -/
theorem beta_zero_of_cyclotomic {n p l : ℕ} (hp : p.Prime)
    (hl : 0 < l) {x : ZMod n} (hdvd : p ^ l ∣ n - 1)
    (hx1 : x ^ (n - 1) = 1)
    (hunit : IsUnit (x ^ ((n - 1) / p) - 1)) :
    Polynomial.eval₂ (Int.castRingHom (ZMod n))
      (x ^ ((n - 1) / p ^ l)) (cyclotomic (p ^ l) ℤ) = 0 :=
  eval₂_cyclotomic_prime_pow_eq_zero hp hl hdvd hx1 hunit

end CL

end Azurite
