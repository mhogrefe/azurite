/-
  **Implementation paper, (4.4): the Lucas–Lehmer test.**

  `prod ∈ ℤ/nℤ` starts at `1` and accumulates the numbers whose
  coprimality with `n` is checked *once*, at the end (step (f)).
  The test *fails* if it or a sub-test (4.2)/(4.3) fails (the
  give-up branch); it *halts* as soon as `n` is proved composite;
  otherwise `n` *passes*, and if (4.1) holds `n` is proved prime.

  (a) Test (4.2) for every prime `p ∈ l⁻` (the odd primes `≤ B`
      of `n − 1`); (b) if (4.1) holds and `r⁻ ≠ 1`, Test (4.2) with
      `p = r⁻` (the tests allow composite `p`).
  (c) The ring `A` of Test (4.3):
      (c1) `n ≡ 1 (mod 4)`: `u = 0`, `a` a prime among the first 50
      with `a^((n−1)/2) ≡ −1 (mod n)` (none ⟹ fail);
      `A = (ℤ/n)[T]/(T² − a)`.  For the flagged `2^l ∣ t`, set
      `β_{2^l}^i = a^(i(n−1)/2^l)`.
      (c2) `n ≡ 3 (mod 4)`: `a = 1`, `u ∈ {1,…,50}` with Jacobi
      symbol `((u²+4)/n) = −1` (none ⟹ fail);
      `A = (ℤ/n)[T]/(T² − uT − 1)`; verify `α^(n+1) = −1` in `A`
      (else composite).
  (d) Test (4.3) for every prime `p ∈ l⁺`; (e) if (4.1) holds and
      `r⁺ ≠ 1`, Test (4.3) with `p = r⁺`.
  (f) Check `gcd(prod, n) = 1` (else a nontrivial divisor is found);
      report *pass*, and *prime* if (4.1) holds.

  Formalized here:

  * **(f) is what certifies the unit conditions**: `gcd(prod, n) = 1`
    makes `prod` a unit of `ℤ/n` (`isUnit_of_val_coprime`), and
    every factor of a unit product is a unit
    (`isUnit_of_isUnit_prod`) — exactly the `hunit` hypothesis of
    `beta_zero_of_cyclotomic` for each flagged odd `p^l`, and the
    unit-coordinate input of the (5.2) confinement.  The lazy
    zero-check inside (4.2)/(4.3) is only an early exit.
  * **(c1) meets Test (4.3)'s soundness hypothesis**: for prime
    `n ≡ 1 (mod 4)`, `a^((n−1)/2) = −1` forces the Legendre symbol
    `(a/n) = −1` (Euler's criterion), hence
    `((0² + 4a)/n) = (4/n)(a/n) = −1` (`jacobiSym_c1_of_euler`) —
    so `quadNorm_one_pow_eq_one` applies to `A = (ℤ/n)[T]/(T² − a)`.
  * **(c1) hands over the `p = 2` data with no gcd needed**:
    `a^((n−1)/2) = −1` gives `a^(n−1) = 1` and
    `a^((n−1)/2) − 1 = −2`, a unit for odd `n`; so
    `β_{2^l} = a^((n−1)/2^l)` is a zero of `Φ_{2^l}`
    (`beta_two_zero_of_cyclotomic`, via `beta_zero_of_cyclotomic`).
    (For `n ≡ 3 (mod 4)` only `flag_2` can be true, with
    `β_2 = −1` a constant — the (i1b) case.)
  * **(c2)'s check is Procedure (11.5)/(10.8)**: for prime `n`,
    `α^(n+1) = N(α) = −a` (`root_pow_card_succ_eq_neg`, from
    `pow_card_succ_eq_quadNorm` at `x = α`), so `α^(n+1) ≠ −1`
    convicts `n`; and a *pass* is literally the hypothesis of
    Proposition (10.8) — `α^(n+1) = −1` in `A` iff
    `T² − uT − 1 ∣ T^(n+1) + 1` (`root_pow_eq_neg_one_iff_dvd`),
    which settles condition (6.4) at `p = 2` for all of
    `n ≡ 3 (mod 4)`.  This is why the 1987 algorithm has no `λ₂`.
-/
import Azurite.CohenLenstra.Impl_4_3

namespace Azurite

namespace CL

open Polynomial

/-- **The (f) extraction, monoid level**: every factor of a unit
product is a unit. -/
theorem isUnit_of_isUnit_prod {M ι : Type _} [CommMonoid M]
    {s : Finset ι} {f : ι → M} (h : IsUnit (∏ i ∈ s, f i)) {i : ι}
    (hi : i ∈ s) : IsUnit (f i) :=
  isUnit_of_dvd_unit (Finset.dvd_prod_of_mem f hi) h

/-- **The (f) check**: `gcd(prod, n) = 1` makes `prod` a unit of
`ℤ/nℤ`. -/
theorem isUnit_of_val_coprime {n : ℕ} [NeZero n] {x : ZMod n}
    (h : Nat.Coprime x.val n) : IsUnit x := by
  have := (ZMod.isUnit_iff_coprime x.val n).mpr h
  rwa [ZMod.natCast_zmod_val] at this

/-- **(c1) meets the (4.3) hypothesis**: for prime `n ≡ 1 (mod 4)`,
`a^((n−1)/2) ≡ −1 (mod n)` forces the Jacobi symbol
`((0² + 4a)/n) = −1` (Euler's criterion for `(a/n)`, and
`(4/n) = 1`). -/
theorem jacobiSym_c1_of_euler {n : ℕ} (hn : n.Prime) (hn1 : n % 4 = 1)
    {a : ℤ} (ha : ((a : ZMod n)) ^ ((n - 1) / 2) = -1) :
    jacobiSym ((0 : ℤ) ^ 2 + 4 * a) n = -1 := by
  haveI : Fact n.Prime := ⟨hn⟩
  have hn5 : 5 ≤ n := by
    have := hn.two_le
    omega
  -- Euler's criterion: a square `a = c²` would give `a^((n−1)/2) = 1`
  have h2 : 2 ∣ n - 1 := by omega
  have hleg : legendreSym n a = -1 := by
    rw [legendreSym.eq_neg_one_iff]
    rintro ⟨c, hc⟩
    have hc0 : c ≠ 0 := by
      rintro rfl
      rw [mul_zero] at hc
      rw [hc, zero_pow (by omega)] at ha
      have h1 : ((1 : ℤ) : ZMod n) = 0 := by
        push_cast
        linear_combination ha
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h1
      have := Int.le_of_dvd one_pos h1
      omega
    have hpow : (c * c) ^ ((n - 1) / 2) = 1 := by
      rw [← sq, ← pow_mul, Nat.mul_div_cancel' h2]
      exact ZMod.pow_card_sub_one_eq_one hc0
    rw [← hc, ha] at hpow
    have h1 : ((2 : ℤ) : ZMod n) = 0 := by
      push_cast
      linear_combination -hpow
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h1
    have := Int.le_of_dvd two_pos h1
    omega
  -- `(4a/n) = (2/n)²·(a/n) = (a/n)`
  have hJa : jacobiSym a n = -1 := by
    rw [← jacobiSym.legendreSym.to_jacobiSym]
    exact hleg
  have hcop : (2 : ℤ).gcd n = 1 := by
    have h2 : Nat.Coprime 2 n := by
      rw [Nat.coprime_primes Nat.prime_two hn]
      omega
    exact_mod_cast h2
  have h4 : jacobiSym 4 n = 1 := by
    rw [show (4 : ℤ) = 2 ^ 2 by norm_num, jacobiSym.pow_left]
    exact jacobiSym.sq_one hcop
  rw [show (0 : ℤ) ^ 2 + 4 * a = 4 * a by ring, jacobiSym.mul_left, h4,
    hJa]
  norm_num

/-- **(c1) hands over the `p = 2` flag data**: for odd `n` with
`2^l ∣ n − 1` and `a^((n−1)/2) = −1`, the element
`β_{2^l} = a^((n−1)/2^l)` is a zero of `Φ_{2^l}` in `ℤ/nℤ` — no
`prod`/gcd needed, since `a^((n−1)/2) − 1 = −2` is a unit. -/
theorem beta_two_zero_of_cyclotomic {n l : ℕ} (hodd : n % 2 = 1)
    (hl : 0 < l) {x : ZMod n} (hdvd : 2 ^ l ∣ n - 1)
    (hx : x ^ ((n - 1) / 2) = -1) :
    Polynomial.eval₂ (Int.castRingHom (ZMod n))
      (x ^ ((n - 1) / 2 ^ l)) (cyclotomic (2 ^ l) ℤ) = 0 := by
  have h2 : 2 ∣ n - 1 := by omega
  have hx1 : x ^ (n - 1) = 1 := by
    rw [← Nat.div_mul_cancel h2, pow_mul, hx]
    norm_num
  have hunit : IsUnit (x ^ ((n - 1) / 2) - 1) := by
    rw [hx, show (-1 - 1 : ZMod n) = -(2 : ℕ) by push_cast; ring]
    refine IsUnit.neg ?_
    rw [ZMod.isUnit_iff_coprime, Nat.coprime_two_left]
    exact Nat.odd_iff.mpr hodd
  exact beta_zero_of_cyclotomic Nat.prime_two hl hdvd hx1 hunit

/-- **The (c2) verdict**: for prime `n` and `((u² + 4a)/n) = −1`,
`α^(n+1) = N(α) = −a` in `A`; so (at `a = 1`) `α^(n+1) ≠ −1`
proves `n` composite. -/
theorem root_pow_card_succ_eq_neg {n : ℕ} (hn : n.Prime) {u a : ℤ}
    (hJ : jacobiSym (u ^ 2 + 4 * a) n = -1) :
    (AdjoinRoot.root (X ^ 2 - C ((u : ZMod n)) * X - C ((a : ZMod n))
        : Polynomial (ZMod n))) ^ (n + 1)
      = - algebraMap (ZMod n) (QuadRing (ZMod n) (u : ZMod n) (a : ZMod n))
          (a : ZMod n) := by
  have h := pow_card_succ_eq_quadNorm hn hJ 0 1
  rw [map_zero, map_one, zero_add, one_mul] at h
  rw [h, quadNorm, ← map_neg]
  congr 1
  ring

/-- **(c2) passes ⟹ Proposition (10.8) applies**: `α^m = −1` in
`R[T]/(T² − uT − 1)` iff `T² − uT − 1 ∣ T^m + 1` — the hypothesis
`hxi` of `proposition_10_8` is exactly the (c2) check. -/
theorem root_pow_eq_neg_one_iff_dvd {R : Type _} [CommRing R] (u : R)
    (m : ℕ) :
    (AdjoinRoot.root (X ^ 2 - C u * X - C (1 : R) : Polynomial R)) ^ m
        = -1
      ↔ (X ^ 2 - C u * X - 1 : Polynomial R) ∣ X ^ m + 1 := by
  rw [C_1, ← AdjoinRoot.mk_eq_zero, map_add, map_one, map_pow,
    AdjoinRoot.mk_X, add_eq_zero_iff_eq_neg]

end CL

end Azurite
