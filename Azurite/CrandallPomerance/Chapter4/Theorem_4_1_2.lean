/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

/-
  Crandall–Pomerance, Theorem 4.1.2 (Pépin test): for `k ≥ 1`, the Fermat
  number `F_k = 2^(2^k) + 1` is prime IF AND ONLY IF
  `3^((F_k − 1)/2) ≡ −1 (mod F_k)`.

  Mathlib has the sufficiency direction (`Nat.pepin_primality'`, a direct
  consequence of Lucas's theorem with witness `3`); this file supplies the
  necessity direction and assembles the iff.

  Necessity is Euler's criterion plus quadratic reciprocity: for `k ≥ 1`,
  `2^(2^k) = 4^(2^(k−1))` and `4^m ≡ 4 (mod 12)`, so `F_k ≡ 5 (mod 12)`.
  Then `F_k ≡ 1 (mod 4)` lets reciprocity flip the Legendre symbol with no
  sign, and `F_k ≡ 2 (mod 3)` reduces it to `(2 | 3) = −1` (2 is not a
  square mod 3).  So `3` is a quadratic nonresidue mod the prime `F_k`,
  and Euler's criterion (`legendreSym.eq_pow`) turns the symbol into the
  half-exponent power.

  The `k ≥ 1` hypothesis is genuinely needed: `F_0 = 3` is prime, but
  `3 ≡ 0 (mod F_0)` so the test power is `0`, not `−1`.
-/
import Mathlib.NumberTheory.Fermat
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity

namespace Azurite

namespace CP

/-- `4^(m+1) ≡ 4 (mod 12)`. -/
private theorem four_pow_succ_mod_twelve : ∀ m : ℕ, 4 ^ (m + 1) % 12 = 4
  | 0 => rfl
  | m + 1 => by
    have ih := four_pow_succ_mod_twelve m
    rw [pow_succ, Nat.mul_mod, ih]

/-- For `k ≥ 1`, the Fermat number `F_k` is `5` mod `12`. -/
theorem fermatNumber_mod_twelve {k : ℕ} (hk : 1 ≤ k) :
    Nat.fermatNumber k % 12 = 5 := by
  obtain ⟨m, hm⟩ : ∃ m, 2 ^ (k - 1) = m + 1 :=
    ⟨2 ^ (k - 1) - 1, by have := Nat.one_le_two_pow (n := k - 1); omega⟩
  have hsplit : 2 ^ 2 ^ k = 4 ^ (m + 1) := by
    rw [← hm, show (4 : ℕ) = 2 ^ 2 from rfl, ← pow_mul]
    congr 1
    rw [← pow_succ']
    congr 1
    omega
  have h4 := four_pow_succ_mod_twelve m
  rw [Nat.fermatNumber, hsplit]
  omega

/-- **Necessity in the Pépin test** (Crandall–Pomerance Theorem 4.1.2, the
"only if"): if `F_k` is prime with `k ≥ 1`, then
`3^((F_k − 1)/2) ≡ −1 (mod F_k)`.  By quadratic reciprocity `3` is a
nonresidue mod `F_k` (as `F_k ≡ 5 (mod 12)`), so Euler's criterion pins
the half-exponent power to `−1`. -/
theorem pepin_necessity {k : ℕ} (hk : 1 ≤ k)
    (hp : (Nat.fermatNumber k).Prime) :
    3 ^ ((Nat.fermatNumber k - 1) / 2) = (-1 : ZMod (Nat.fermatNumber k)) := by
  set p := Nat.fermatNumber k with hpdef
  have : Fact p.Prime := ⟨hp⟩
  have h12 : p % 12 = 5 := fermatNumber_mod_twelve hk
  -- the Legendre symbol `(3 | p)` is `−1`
  have hleg : legendreSym p 3 = -1 := by
    have hflip := legendreSym.quadratic_reciprocity_one_mod_four
      (p := p) (q := 3) (by omega) (by decide)
    norm_num at hflip
    rw [← hflip, legendreSym.mod,
      show ((p : ℤ) % ((3 : ℕ) : ℤ)) = 2 by push_cast; omega]
    decide
  -- Euler's criterion turns the symbol into the half-exponent power
  have heuler := legendreSym.eq_pow p 3
  rw [hleg] at heuler
  have hexp : (p - 1) / 2 = p / 2 := by omega
  rw [hexp]
  push_cast at heuler
  exact heuler.symm

/-- **The Pépin test** (Crandall–Pomerance Theorem 4.1.2): for `k ≥ 1`,
the Fermat number `F_k = 2^(2^k) + 1` is prime if and only if
`3^((F_k − 1)/2) ≡ −1 (mod F_k)`.  Sufficiency is Mathlib's
`Nat.pepin_primality'` (Lucas with witness `3`); necessity is
`pepin_necessity`. -/
theorem theorem_4_1_2 {k : ℕ} (hk : 1 ≤ k) :
    (Nat.fermatNumber k).Prime ↔
      3 ^ ((Nat.fermatNumber k - 1) / 2) = (-1 : ZMod (Nat.fermatNumber k)) :=
  ⟨pepin_necessity hk, Nat.pepin_primality' k⟩

end CP

end Azurite

-- ── Tests ────────────────────────────────────────────────────────────────────

/-! The iff in action on the small Fermat primes: `F_1 = 5` and `F_2 = 17`
via the test power, computed by the kernel. -/

section Tests

open Azurite.CP

example : (Nat.fermatNumber 1).Prime :=
  (theorem_4_1_2 (by norm_num)).mpr (by decide)

example : (Nat.fermatNumber 2).Prime :=
  (theorem_4_1_2 (by norm_num)).mpr (by decide)

end Tests
