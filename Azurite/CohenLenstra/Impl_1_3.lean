/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

/-
  **Implementation paper, (1.3)(d)–(f): flags, the Lucas–Lehmer
  stage, and the `s = s₁·s₂` selection.**

  (d) For each prime power `p^k ∣ t`, `flag_{p^k}` records whether
      `n ≡ 1 (mod p^k)` — the §10 `f = 1` distinction: flagged
      prime powers get the trivial-`F` route (`F = ℤ/nℤ`,
      `ρ = id`) and are handled by the `n ± 1` machinery instead
      of Jacobi sums.  (The `n ≡ −1 (mod p^k)` analogue was not
      implemented; cf. the forthcoming Remark (4.6).)

  (e) The "Lucas–Lehmer test" (4.4) — the combined `n ± 1` stage,
      §4 awaited — with four outcomes: *fails* ⟹ (1.3) reports
      failure (the give-up branch of our `Option Bool` target);
      *composite proven* ⟹ halt; *primality proven* ⟹ halt (the
      BLS-style outright proofs when `f^±` is large — our C&P
      §4.1/§4.2 inventory); else it hands over, for each flagged
      `p^k`, elements `β_{p^k} ∈ ℤ/nℤ` with `β_{p^k}` a zero of
      `Φ_{p^k}` — exactly the (10.3)-data at `F = ZMod n`: our
      `lambdaHom`/`mKernel` instantiate directly with `z = β`.
      Moreover a passed (4.4) confines divisors:
      `∀ r ∣ n, ∃ i, r ≡ n^i (mod f^−·f^+)` (and mod any number
      built from its primes; proof awaited at (5.2)).

  (f) Algorithm (5.5) selects `s = s₁·s₂ > n^(1/2)` and a new
      `t ∣ old t`, with `s₁` built from primes of `f^−·f^+`
      (handled by the Lucas–Lehmer stage) and `s₂` coprime to
      `s₁`, built from primes of `e(t)` (handled by Jacobi sums).
      The closing claim — `n^t ≡ 1 (mod s)` — is proved here
      (`pow_even_modEq_one_mul`): the `s₂`-side comes from
      Proposition (4.1) (our `pow_t_mod_eq_one` route), and the
      `s₁`-side holds because `s₁ ∣ (n−1)(n+1) = n² − 1` and `t`
      is *even* — the reason for the (1.1)(a) even-`t` delta —
      with the coprime CRT-combination closing the product.

  **(g)–(i3): the Jacobi-sum stage.**

  (g) `λ_p` is declared for *odd* `p ∣ t` only, initialized true
      if `n^(p−1) ≢ 1 (mod p²)` (the (7.18)-branch) **or**
      `p ∣ f^−·f^+` (new vs 1984: such `p` are handled by the
      Lucas–Lehmer stage; explanation at Remark (4.5)).  No `λ₂`
      exists: `f^−` carries the full 2-power of `n − 1` (the
      unfactored parts `r^∓` are odd), so `p = 2` is always on
      the Lucas–Lehmer side.

  (i1) The per-`(p,q)` quantities are recomputed mod `n` from the
      raw tables: (i1a) odd `p`: `j₀ = j^θ`, `j_v = j^(α(v))` —
      the products of Theorem (8.5) and `prod_pow_alphac_decomp`;
      (i1b) `p^k = 2`: constants; (i1c) `p^k = 4`:
      `j₀ = j²·q`, `j₁ = 1`, and `j₃ = j²` — **correcting the
      erratum in the 1984 paper's (12.1)(b2e), which had
      `j₃ = j`**: the exponent check against (9.6) is
      `b2e_erratum_exponents` below (our Theorem (9.5) formalized
      (9.6) directly and was never exposed to the error);
      (i1d) `p = 2, k ≥ 3`: `(j*·j)^θ`, `(j*·j)^(α(v))`, with the
      `(j#)²`-factor for `v ∈ L − M` — the (9.11)/(9.20)-products
      of Theorems (9.10)/(9.19), with `j*·j` the 1984 triple
      Jacobi sum.

  (i2) The flag-split test: (i2a) for `n ≡ 1 (mod p^k)`, apply
      `λ : ℤ[ζ_{p^k}]/(n) → ℤ/n`, `ζ ↦ β_{p^k}`, and test
      `λ(j₀)^u·λ(j_v) = β^h` *in `ℤ/n`* — the (10.3) `f = 1`
      route: congruence mod `𝔪 = ker λ` is equality after `λ`,
      exactly our `mKernel` design, with the ring work collapsing
      into `ℤ/n`; (i2b) otherwise the full
      `j₀^u·j_v ≡ ζ^h (mod nℤ[ζ_{p^k}])` test of 1984.  In both,
      "no `h` ⟹ composite" is the completeness half (prime `n`
      passes), deferred as before.

  (i3) `h ≢ 0 (mod p)` with `p` odd sets `λ_p` true — the
      Theorem (7.19) primitive-root route.
-/
import Azurite.CohenLenstra.Impl_1_1

namespace Azurite

namespace CL

/-- **The (1.3)(f) claim**: `n^t ≡ 1 (mod s₁·s₂)` for even `t`,
`s₁ ∣ (n−1)(n+1)` (the `f^−·f^+`-side, where `n² ≡ 1`), and the
`s₂`-side congruence supplied by Proposition (4.1).  The even-`t`
requirement of (1.1)(a) is exactly what the `n+1`-side needs. -/
theorem pow_even_modEq_one_mul {n t s₁ s₂ : ℕ} (hn : 1 ≤ n)
    (ht : 2 ∣ t) (hs1 : s₁ ∣ (n - 1) * (n + 1))
    (hs2 : n ^ t ≡ 1 [MOD s₂]) (hco : Nat.Coprime s₁ s₂) :
    n ^ t ≡ 1 [MOD s₁ * s₂] := by
  have h1 : n ^ t ≡ 1 [MOD s₁] := by
    obtain ⟨u, rfl⟩ := ht
    have hsq : n ^ 2 ≡ 1 [MOD s₁] := by
      have heq : (n - 1) * (n + 1) = n ^ 2 - 1 := by
        obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
        simp only [Nat.add_sub_cancel]
        have h2 : (m + 1) ^ 2 = m * m + 2 * m + 1 := by ring
        have h3 : m * (m + 1 + 1) = m * m + 2 * m := by ring
        omega
      rw [heq] at hs1
      exact ((Nat.modEq_iff_dvd'
        (Nat.one_le_pow _ _ (by omega))).mpr hs1).symm
    calc n ^ (2 * u) = (n ^ 2) ^ u := by rw [pow_mul]
      _ ≡ 1 ^ u [MOD s₁] := hsq.pow u
      _ = 1 := one_pow u
  exact (Nat.modEq_and_modEq_iff_modEq_mul hco).mp ⟨h1, hs2⟩

/-- **The (i1c)-erratum check**: for `n ≡ 3 (mod 4)` with
`n = 4u + 3`, the corrected table `j₀ = j²q, j₃ = j²` yields
`j₀^u·j₃ = j^(2u+2)·q^u` with exponents `(n+1)/2` and `(n−3)/4` —
matching test (9.6) (our Theorem (9.5)); the 1984 entry `j₃ = j`
would give the wrong exponent `2u + 1`. -/
theorem b2e_erratum_exponents {n : ℕ} (hn : n % 4 = 3) :
    2 * (n / 4) + 2 = (n + 1) / 2 ∧ n / 4 = (n - 3) / 4 := by
  omega

end CL

end Azurite
