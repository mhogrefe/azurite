/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

/-
  **Implementation paper, Remarks (4.5)–(4.8).**

  **(4.5)**: the Lucas–Lehmer test has *also* proved condition
  [2, (6.4)] — our finite-level `∀ D, ∃ l, r ≡ n^l (mod p^D)` for
  every prime `r ∣ n` — at `p = 2`: by (4.4)(c1) and Proposition
  (7.24) for `n ≡ 1 (mod 4)` (`cond_6_4_two_of_c1`), and by
  (4.4)(c2) and Proposition (10.8) for `n ≡ 3 (mod 4)`
  (`cond_6_4_two_of_c2`; the (c2) check is the (10.8) hypothesis
  by `root_pow_eq_neg_one_iff_dvd`).  Where this is not proved, `n`
  is composite (unless the test failed).  "This easily implies the
  slight improvement (4.1)": the 2-adic confinement lets the
  classical bound drop its factor `2`; the proof lives with the
  divisor-confinement statement of (5.2), where we take it up.

  Condition (6.4) also holds for the *odd* primes `p ∣ f⁻·f⁺`,
  by (4.2)/(4.3) and Proposition (10.7) — explaining the
  `λ_p`-initialization of (1.3)(g).  The `f⁻`-half is proved here
  (`cond_6_4_of_test_4_2`): Test (4.2)'s certified data
  (`x^(n−1) = 1`, `x^((n−1)/p) − 1` a unit by (4.4)(f)) is a
  Pocklington certificate for `F = p^(v_p(n−1))`, so every prime
  `r ∣ n` has `r ≡ 1 (mod p^(v_p(n−1)))` — the `f = 1`,
  `i = 0` confinement input of (10.7).  The `f⁺`-half — Test (4.3)
  giving `r ≡ ±1 (mod p^(v_p(n+1)))`, the `f = 2` input of (10.7)
  — needs the order of a norm-one element of `A ⊗ ℤ/r` to divide
  `r − 1` or `r + 1` (with the double-root case excluded), which is
  (5.2)'s content; deferred there.

  **(4.6)** (prose): the `flag_{p^k}` and `β_{p^k}^i` are kept for
  step (i) of (1.3); a flag replaces the Jacobi-sum test in
  `ℤ[ζ_{p^k}]/nℤ[ζ_{p^k}]` by the cheaper test in `ℤ/nℤ`
  ([2, §10] = our `lambdaHom` route).  The analogous speed-up for
  `p ∣ n + 1`, `p ∣ t` was not implemented — a design option for
  our rail (the (c2) ring `A` would play `F`, with `ρ` the
  conjugation and `f = 2`).

  **(4.7)** (prose): after the Lucas–Lehmer test the primes
  `p ∈ l⁻ ∪ l⁺` can be dropped from the candidate `q`-primes of
  (1.3)(f) — they are already handled on the `s₁`-side.

  **(4.8)** (prose): the exponentiations of the Lucas–Lehmer test
  use the `2^m`-ary method (3.6), with squarings and
  multiplications carried out in `A` for Test (4.3) and (4.4)(c2)
  (Remark (4.9) awaited) — our `slidingWindowPow` is generic over
  `Mul`/`Square`, exactly Remark (3.8)'s design, so the same
  proven routine serves `ℤ/nℤ` and `A`.
-/
import Azurite.CohenLenstra.Impl_4_4
import Azurite.CohenLenstra.Lemma_7_23
import Azurite.CrandallPomerance.Chapter4.Theorem_4_1_3

namespace Azurite

namespace CL

open Polynomial

/-- **(4.5), `p = 2`, `n ≡ 1 (mod 4)`**: the (c1) witness
`a^((n−1)/2) ≡ −1 (mod n)` gives condition (6.4) at `p = 2` for
every prime `r ∣ n`, by Proposition (7.24). -/
theorem cond_6_4_two_of_c1 {n : ℕ} (hn1 : 1 < n) (hmod : n % 4 = 1)
    {a : ℤ} (ha : ((a : ZMod n)) ^ ((n - 1) / 2) = -1) :
    ∀ r : ℕ, r.Prime → r ∣ n → ∀ D : ℕ, ∃ l : ℕ,
      r ≡ n ^ l [MOD 2 ^ D] := by
  intro r hr hrn
  have ha' : Int.ModEq (n : ℤ) (a ^ ((n - 1) / 2)) (-1) := by
    rw [← ZMod.intCast_eq_intCast_iff]
    push_cast
    exact ha
  exact proposition_7_24 hn1 hmod ha' hr hrn

/-- **(4.5), `p = 2`, `n ≡ 3 (mod 4)`**: the (c2) check
`α^(n+1) = −1` in `A = (ℤ/n)[T]/(T² − uT − 1)` gives condition
(6.4) at `p = 2` for every prime `r ∣ n`, by Proposition (10.8). -/
theorem cond_6_4_two_of_c2 {n : ℕ} {u : ZMod n} (hn3 : n % 4 = 3)
    (hα : (AdjoinRoot.root (X ^ 2 - C u * X - C (1 : ZMod n)
      : Polynomial (ZMod n))) ^ (n + 1) = -1) :
    ∀ r : ℕ, r.Prime → r ∣ n → ∀ D : ℕ, ∃ l : ℕ,
      r ≡ n ^ l [MOD 2 ^ D] :=
  proposition_10_8 hn3 ((root_pow_eq_neg_one_iff_dvd u (n + 1)).mp hα)

/-- **(4.5), odd `p ∣ f⁻`**: Test (4.2)'s certified data for an odd
prime `p ∣ n − 1` — `x^(n−1) = 1` and `x^((n−1)/p) − 1` a unit (by
(4.4)(f)) — is a Pocklington certificate for `F = p^(v_p(n−1))`,
so `r ≡ 1 (mod p^(v_p(n−1)))` for every prime `r ∣ n`, and
Proposition (10.7) at `f = 1` yields condition (6.4) at `p`. -/
theorem cond_6_4_of_test_4_2 {n p : ℕ} (hn1 : 1 < n) (hp : p.Prime)
    (hp2 : p ≠ 2) (hpd : p ∣ n - 1) {x : ZMod n}
    (hx1 : x ^ (n - 1) = 1) (hunit : IsUnit (x ^ ((n - 1) / p) - 1)) :
    ∀ r : ℕ, r.Prime → r ∣ n → ∀ D : ℕ, ∃ l : ℕ,
      r ≡ n ^ l [MOD p ^ D] := by
  intro r hr hrn
  set c := (n - 1).factorization p with hc
  have hFdvd : p ^ c ∣ n - 1 := Nat.ordProj_dvd _ p
  -- Pocklington with `F = p^c`
  have hpock := CP.pocklington hn1 (Nat.mul_div_cancel' hFdvd).symm x hx1
    (fun q hq hqF => by
      have hqp : q = p :=
        (Nat.prime_dvd_prime_iff_eq hq hp).mp (hq.dvd_of_dvd_pow hqF)
      rw [hqp]
      exact hunit)
  have hr1 : r ≡ 1 [MOD p ^ c] := hpock r hr hrn
  -- Proposition (10.7) at `f = 1`
  have hpn : ¬ p ∣ n := by
    intro hdn
    have h1 : p ∣ n - (n - 1) := Nat.dvd_sub hdn hpd
    rw [show n - (n - 1) = 1 by omega] at h1
    exact hp.one_lt.ne' (Nat.dvd_one.mp h1)
  refine proposition_10_7 hp hn1 hpn one_pos ?_ ?_ ⟨0, zero_lt_one, ?_⟩
  · rwa [pow_one]
  · intro h
    exact absurd h hp2
  · rw [pow_one, pow_zero]
    exact hr1

end CL

end Azurite
