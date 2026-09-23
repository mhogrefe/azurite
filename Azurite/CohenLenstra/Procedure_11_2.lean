/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

/-
  **Cohen–Lenstra (11.2): the odd-`p` procedure for condition
  (6.4).**

  For an odd prime `p ∣ t`, either prove `n` composite or prove
  (6.4).  If Method (10.3) built `𝔪_{p,k}`, Proposition (10.7)
  already suffices.  Otherwise, the dispatch — each pass-branch an
  instantiation of an already-proven theorem:

  (a) If `n^(p−1) ≢ 1 (mod p²)`, then (6.4) holds by
      Proposition (7.18) (`proposition_7_18`).

  (b) If some `q ∣ s` with `p ∣ q − 1` has `χ_{p,q}` satisfying
      (7.9) with a *primitive* `p^k`-th root `ζ` (`k = v_p(q−1)`) —
      already computed in stage (11.1)(b), reusable because
      Theorem (8.5) preserves the root (Remark (8.9)(b), our
      same-`ζ'` conclusion) — then (6.4) holds by Theorem (7.19)
      (`theorem_7_19`).

  (c) Failing both: test whether `n` is a `p`-th power of an
      integer.  If so, `n` is composite
      (`not_prime_of_eq_pow`, this file) and the procedure halts.
      [The computable `p`-th-root extraction is a §12–13 rail item;
      the abstract procedure needs only this soundness lemma.]

  (d) Otherwise find a prime `q` (not necessarily dividing `s`)
      with `q ≡ 1 (mod p)` and `n^((q−1)/p) ≢ 1 (mod q)` — their
      (11.3); existence for non-`p`-th-power `n` is
      Remark (11.4)(a).

  (e) If `q ∣ s`, then `n` is composite (Remark (11.4)(b)).  If
      `q ∤ s` (and `q ∤ n`), test (7.9) for a character mod `q` of
      order `p` (so `k = 1`) via Theorem (8.5), with
      `ζ ∈ U_p` primitive: a pass gives (6.4) by Theorem (7.19),
      and a failure again proves `n` composite
      (Remark (11.4)(b)).

  The two composite-verdict claims of step (e) are deferred by the
  paper to Remark (11.4), formalized with the next piece.
-/
import Azurite.CohenLenstra.Proposition_7_18

namespace Azurite

namespace CL

/-- **Step (11.2)(c)**: a proper power is composite — if
`n = a^k` with `k ≥ 2` and `n > 1`, then `n` is not prime. -/
theorem not_prime_of_eq_pow {n a k : ℕ} (hn : 1 < n) (hk : 2 ≤ k)
    (ha : n = a ^ k) : ¬ n.Prime := by
  intro hpr
  have ha1 : a ≠ 1 := by
    rintro rfl
    rw [one_pow] at ha
    omega
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [zero_pow (by omega : k ≠ 0)] at ha
    omega
  have hdvd : a ∣ n := ha ▸ dvd_pow_self a (by omega : k ≠ 0)
  rcases (hpr.eq_one_or_self_of_dvd a hdvd) with h1 | hself
  · exact ha1 h1
  · -- `a = n` forces `n^(k−1) = 1`, impossible for `k ≥ 2`
    subst hself
    have hlt : a < a ^ k := by
      calc a = a ^ 1 := (pow_one a).symm
        _ < a ^ k := Nat.pow_lt_pow_right (by omega) (by omega)
    omega

end CL

end Azurite
