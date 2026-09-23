/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

/-
  **Implementation paper, §2: trial division.**

  Algorithm (2.1) serves two purposes: catching small factors of
  `n`, and factoring the smooth parts of `n² − 1` for the
  Lucas–Lehmer stage.  Its trick is that a *single* reduction
  `(n+1) mod p` per prime classifies which of `n − 1, n, n + 1`
  the prime divides — one division serves all of `n³ − n`:

    `(n+1) ≡ 1 (mod p)` ⟹ `p ∣ n` (halt with a divisor);
    `(n+1) ≡ 0 (mod p)` ⟹ `p ∣ n + 1` (strip from `r⁺`, add to `I⁺`);
    `(n+1) ≡ 2 (mod p)` ⟹ `p ∣ n − 1` (strip from `r⁻`, add to `I⁻`),

  proved here as `trial_division_detect`.  Starting from the
  largest *odd* factors of `n ∓ 1`, the sweep leaves `r∓` as the
  odd `B`-rough parts and `f∓ = (n ∓ 1)/r∓` as the factored parts
  — the inputs of (1.3)(e)/(f).

  **Remark (2.2)**: with `B ≥ 55441 = t + 1` (as in practice) the
  gcd-screen (1.3)(a) is redundant: every prime of `t·e(t)` is
  `≤ t + 1` — for odd `q ∣ e(t)` because `q − 1 ∣ t`
  (`sub_one_dvd_of_dvd_e`) — so the trial division already
  witnesses any common factor.  Proved as `prime_dvd_e_le`.

  **Remarks (2.3)/(2.4)** (prose): the paired-modulus
  micro-optimization (`(n+1) mod (p₁p₂)` then two single-single
  reductions; 2% on the Cyber) — a rail option for `AzNat`
  division; the abandoned Pollard-ρ enrichment of `r∓` (never
  found a factor `> B`), with the referee's suggestion of
  `p ± 1`/ECM — generator-side options for enlarging `f∓`.  The
  packed prime-difference table (differences `≤ 1000` below
  `10^6`, four per 48-bit word) is a table-representation note;
  our rail has the proven bitpacked `AzNat` sieve.
-/
import Azurite.CohenLenstra.Theorem_6_3

namespace Azurite

namespace CL

/-- **The (2.1) three-way detection**: the single reduction
`(n+1) mod p` classifies which of `n`, `n+1`, `n−1` the prime
divides. -/
theorem trial_division_detect {n p : ℕ} (hn : 1 ≤ n) :
    ((n + 1) % p = 1 → p ∣ n)
      ∧ ((n + 1) % p = 0 → p ∣ n + 1)
      ∧ ((n + 1) % p = 2 → p ∣ n - 1) := by
  have hdm := Nat.div_add_mod (n + 1) p
  refine ⟨fun h1 => ⟨(n + 1) / p, by omega⟩,
    fun h0 => ⟨(n + 1) / p, by omega⟩,
    fun h2 => ⟨(n + 1) / p, by omega⟩⟩

/-- **The (2.2) redundancy fact**: every prime dividing `e(t)` is
`≤ t + 1`, so a trial-division bound `B ≥ t + 1` subsumes the
gcd-screen (1.3)(a). -/
theorem prime_dvd_e_le {t q : ℕ} (ht : t ≠ 0) (hq : q.Prime)
    (h : q ∣ e t) : q ≤ t + 1 := by
  have hd := sub_one_dvd_of_dvd_e ht hq h
  have h2 := hq.two_le
  have hle : q - 1 ≤ t := Nat.le_of_dvd (by omega) hd
  omega

end CL

end Azurite
