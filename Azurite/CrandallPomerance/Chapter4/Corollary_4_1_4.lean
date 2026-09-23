/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

/-
  Crandall–Pomerance, Corollary 4.1.4: if `n − 1 = F·R`, the witness `a`
  satisfies the Pocklington conditions (4.3), and `F ≥ √n`, then `n` is
  prime.

  By Pocklington (Theorem 4.1.3) every prime factor of `n` is
  `≡ 1 (mod F)`, hence exceeds `F ≥ √n`.  A composite `n` would have a
  prime factor at most `√n` (its least one), contradiction.

  `F ≥ √n` is stated as `n ≤ F²` — the exact natural-number form of the
  real inequality.  The composite-side fact is Mathlib's
  `Nat.minFac_sq_le_self`, the same least-prime-factor bound that closed
  the prime-sieve invariant.
-/
import Azurite.CrandallPomerance.Chapter4.Theorem_4_1_3

namespace Azurite

namespace CP

/-- **Pocklington primality certificate** (Crandall–Pomerance
Corollary 4.1.4): if `n − 1 = F·R`, the witness `a` satisfies
`a^(n−1) = 1` in `ZMod n` and `a^((n−1)/q) − 1` is a unit of `ZMod n`
for every prime `q ∣ F`, and `n ≤ F²` (i.e. `F ≥ √n`), then `n` is
prime. -/
theorem corollary_4_1_4 {n F R : ℕ} (hn : 1 < n) (hsplit : n - 1 = F * R)
    (a : ZMod n) (ha : a ^ (n - 1) = 1)
    (hunit : ∀ q : ℕ, q.Prime → q ∣ F → IsUnit (a ^ ((n - 1) / q) - 1))
    (hFn : n ≤ F ^ 2) : n.Prime := by
  by_contra hcomp
  have hF2 : 2 ≤ F := by
    by_contra hF1
    have : F ^ 2 ≤ 1 ^ 2 := Nat.pow_le_pow_left (by omega) 2
    omega
  -- the least prime factor of a composite `n` is at most `√n ≤ F` …
  set p := n.minFac with hpdef
  have hp : p.Prime := Nat.minFac_prime (by omega)
  have hple : p ^ 2 ≤ n := Nat.minFac_sq_le_self (by omega) hcomp
  have hpF : p ≤ F := by
    have := hFn.trans' hple
    exact (Nat.pow_le_pow_iff_left two_ne_zero).mp this
  -- … but Pocklington forces it past `F`
  have hmod : p % F = 1 % F :=
    pocklington hn hsplit a ha hunit p hp (Nat.minFac_dvd n)
  have hp2 := hp.two_le
  rw [Nat.mod_eq_of_lt (by omega : 1 < F)] at hmod
  rcases Nat.lt_or_ge p F with hlt | hge
  · rw [Nat.mod_eq_of_lt hlt] at hmod
    omega
  · rw [le_antisymm hpF hge, Nat.mod_self] at hmod
    omega

end CP

end Azurite

-- ── Tests ────────────────────────────────────────────────────────────────────

/-! A worked certificate: `97` is prime via `96 = 32·3`, `F = 32 ≥ √97`,
witness `5` (a quadratic nonresidue mod `97`, so `5^48 = −1 ≠ 1`).  The
only prime dividing `F = 2^5` is `2`, and the kernel checks both power
conditions. -/

set_option maxRecDepth 4096 in
example : Nat.Prime 97 := by
  apply Azurite.CP.corollary_4_1_4 (F := 32) (R := 3) (a := 5)
    (by norm_num) (by norm_num) (by decide)
  · intro q hq hqF
    have hq2 : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp
      (hq.dvd_of_dvd_pow ((by norm_num : (32 : ℕ) = 2 ^ 5) ▸ hqF))
    subst hq2
    -- `5^48 = −1` mod 97, so the element is `−2`, with explicit inverse `48`
    exact IsUnit.of_mul_eq_one (48 : ZMod 97) (by decide)
  · norm_num
