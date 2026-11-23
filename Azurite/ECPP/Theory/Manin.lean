/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Mathlib.Tactic

/-!
# Manin's proof of the Hasse bound: the arithmetic end

After Chahal and Osserman, *The Riemann hypothesis for elliptic curves*, Amer. Math. Monthly
115 (2008), §4.3.  There, for `E : y² = x³ + ax + b` over `𝔽_q` and the twist
`E_λ : λ y² = x³ + ax + b`, `λ = t³ + at + b`, over `K = 𝔽_q(t)`, the points

  `P_n = (t^q, λ^((q−1)/2)) + n (t, 1)` of `E_λ(K)`

have a degree `d(n)` (the degree of the numerator of `x(P_n)`, `0` at `O`), and

* the **Basic Identity** (19): `d(n − 1) + d(n + 1) = 2 d(n) + 2`;
* **Theorem 1** (20): `d(−1) − d(0) − 1 = N_q − q`, and `d(0) = q`;

so that (Theorem 2) `d(n) = n² − (N_q − q) n + q`, a quadratic that is `≥ 0` at every integer,
whence `(N_q − q)² ≤ 4q`.

This file has the last step, which is arithmetic: `degree_quadratic` (Theorem 2) and
`sq_le_of_degree` (the conclusion).  The Basic Identity and Theorem 1 are not yet formalized;
the article does not prove the Basic Identity (it refers to Chahal, *Manin's proof of the
Hasse inequality revisited*, Nieuw Arch. Wiskd. 13 (1995)).
-/

namespace Azurite.ECPP

/-- **Theorem 2**: a function on `ℤ` with `d(n − 1) + d(n + 1) = 2 d(n) + 2` is the quadratic
`n² − (d(−1) − d(0) − 1) n + d(0)`. -/
theorem degree_quadratic {d : ℤ → ℤ} (hrec : ∀ n, d (n - 1) + d (n + 1) = 2 * d n + 2)
    (n : ℤ) : d n = n ^ 2 - (d (-1) - d 0 - 1) * n + d 0 := by
  have key : ∀ n : ℤ, d n = n ^ 2 - (d (-1) - d 0 - 1) * n + d 0 ∧
      d (n + 1) = (n + 1) ^ 2 - (d (-1) - d 0 - 1) * (n + 1) + d 0 := by
    intro n
    induction n using Int.induction_on with
    | zero =>
      have h := hrec 0
      simp only [zero_sub, zero_add] at h
      refine ⟨by ring, ?_⟩
      simp only [zero_add]
      linarith
    | succ k ih =>
      obtain ⟨h1, h2⟩ := ih
      refine ⟨h2, ?_⟩
      have h := hrec ((k : ℤ) + 1)
      rw [add_sub_cancel_right] at h
      linarith
    | pred k ih =>
      obtain ⟨h1, h2⟩ := ih
      have e : (-(k : ℤ) - 1 + 1) = -(k : ℤ) := by ring
      rw [e]
      refine ⟨?_, h1⟩
      have h := hrec (-(k : ℤ))
      rw [h2] at h
      linarith
  exact (key n).1

/-- A quadratic `n² − c n + q` that is nonnegative at every integer has `c² ≤ 4q`, unless
`q` is a product of two consecutive integers. -/
theorem sq_le_of_quadratic_nonneg {c q : ℤ} (hq : ∀ n : ℤ, q ≠ n * (n + 1))
    (h : ∀ n : ℤ, 0 ≤ n ^ 2 - c * n + q) : c ^ 2 ≤ 4 * q := by
  by_contra hlt
  push Not at hlt
  have hn := h (c / 2)
  have hdm := Int.emod_add_mul_ediv c 2
  rcases Int.emod_two_eq_zero_or_one c with hr | hr
  · rw [hr] at hdm
    nlinarith
  · rw [hr] at hdm
    refine hq (c / 2) ?_
    nlinarith

/-- **The conclusion of Manin's proof**: from the Basic Identity, `d ≥ 0`, `d(0) = q` and
`d(−1) − d(0) − 1 = c`, the bound `c² ≤ 4q` — for `q` no product of two consecutive
integers. -/
theorem sq_le_of_degree {d : ℤ → ℤ} {q c : ℤ} (hnn : ∀ n, 0 ≤ d n)
    (hrec : ∀ n, d (n - 1) + d (n + 1) = 2 * d n + 2) (h0 : d 0 = q)
    (hc : d (-1) - d 0 - 1 = c) (hq : ∀ n : ℤ, q ≠ n * (n + 1)) : c ^ 2 ≤ 4 * q := by
  refine sq_le_of_quadratic_nonneg hq fun n => ?_
  have := degree_quadratic hrec n
  rw [hc, h0] at this
  rw [← this]
  exact hnn n

/-- An odd prime is no product of two consecutive integers. -/
theorem prime_ne_mul_succ {p : ℕ} (hp : p.Prime) (h2 : p ≠ 2) (n : ℤ) :
    (p : ℤ) ≠ n * (n + 1) := by
  intro h
  have heven : Even (n * (n + 1)) := Int.even_mul_succ_self n
  rw [← h] at heven
  have : Even p := by exact_mod_cast heven
  exact h2 ((Nat.Prime.even_iff hp).mp this)

end Azurite.ECPP
