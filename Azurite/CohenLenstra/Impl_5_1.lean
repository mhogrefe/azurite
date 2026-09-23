/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

/-
  **Implementation paper, §5 opening and (5.1): combining the
  Lucas–Lehmer test with the Jacobi-sum stage — the cost model.**

  By [5, §8] the Lucas–Lehmer test combines with the primality
  test of [2, §12].  Let `t` be as in (1.1)(a), and assume for now
  that every prime `p ∣ t` satisfies [2, (6.4)], written `p`-adically
  as

    **(5.1)**  for every prime `r ∣ n` there is `l_p(r) ∈ ℤ_p` with
               `r^(p−1) = (n^(p−1))^(l_p(r))` in `1 + pℤ_p`

  — our finite-level rendering `∀ D, ∃ l, r ≡ n^l (mod p^D)`
  (Theorem (6.3)'s hypothesis form; the two are equivalent by the
  `p`-adic-limit discussion in `Theorem_6_3.lean`).  By (4.5) it
  holds for `p = 2` (`cond_6_4_two_of_c1`/`cond_6_4_two_of_c2`);
  for the other primes `p ∣ t` that need it, `λ_p` of (1.3)(g) is
  set to true as soon as (5.1) is proved for `p`, and successful
  termination of (1.3) means all `λ_p` are true — justifying the
  assumption.

  **Costs.**  For every prime power `p^k ≥ 2` dividing `t`, a cost
  `c_{p^k} ∈ ℤ` estimates (say in milliseconds) the running time of
  step (1.3)(i) for `p^k` and one `q`-prime with `k = v_p(q−1)`;
  the `u`-th powering of (i2) dominates, done in `ℤ/nℤ` if
  `flag_{p^k}` is true ((i2a)) and in `ℤ[ζ_{p^k}]/nℤ[ζ_{p^k}]`
  otherwise ((i2b)), so `c_{p^k} = c_{p^k}(flag_{p^k})` with the two
  values determined empirically as functions of the bit length of
  `n` (as in the Fortran implementation).  The cost of a `q`-prime is

    `w(q) = Σ_{p ∣ q−1, k = v_p(q−1)} c_{p^k}`

  — defined here computably as `qCost c q`, with `c : ℕ → ℕ → ℕ`
  the table `(p, k) ↦ c_{p^k}` (the flag dependence lives inside
  `c`), the prime factors from `Nat.primeFactors` and the exponent
  from the computable `padicValNat`.  Also needed: `c_ftd`, the
  empirical running time of one iteration of the final trial
  division (1.3)(l1)–(l3), in the same units.

  **Standing assumption on `f⁻·f⁺`**: `v_p(f⁻f⁺) = v_p(n² − 1)` for
  every prime `p ∣ t`, i.e. the trial division strips the primes of
  `t` completely from `n ∓ 1` — which holds iff every prime of `t`
  is `≤ B`; for the Fortran `t = 55440 = 2⁴·3²·5·7·11` this means
  `B ≥ 11` (guarded below).
-/
import Azurite.CohenLenstra.Impl_4_9

namespace Azurite

namespace CL

/-- **The cost `w(q)` of a `q`-prime**: `Σ_{p ∣ q−1} c_{p^(v_p(q−1))}`,
for a cost table `c (p, k) = c_{p^k}`. -/
def qCost (c : ℕ → ℕ → ℕ) (q : ℕ) : ℕ :=
  ∑ p ∈ (q - 1).primeFactors, c p (padicValNat p (q - 1))

-- With `c_{p^k} = p^k`, `w(13) = 2² + 3 = 7` and `w(7) = 2 + 3 = 5`.
#guard qCost (fun p k => p ^ k) 13 = 7
#guard qCost (fun p k => p ^ k) 7 = 5
#guard qCost (fun p k => p ^ k) 2 = 0

-- The primes of the Fortran `t = 55440` are `2, 3, 5, 7, 11`, so the
-- standing assumption `v_p(f⁻f⁺) = v_p(n² − 1)` needs `B ≥ 11`.
#guard Nat.primeFactorsList 55440 = [2, 2, 2, 2, 3, 3, 5, 7, 11]

end CL

end Azurite
