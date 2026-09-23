/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

/-
  Crandall–Pomerance, Theorem 4.2.8: the cube-root strengthening of
  Morrison's `n + 1` test — the `n + 1` analogue of
  Brillhart–Lehmer–Selfridge (Theorem 4.1.5).

  With `f, Δ` as in (4.12), `n` positive, `gcd(n, 2b) = 1`, and
  `(Δ/n) = −1`, suppose `n + 1 = F·R` with `F > n^(1/3) + 1` (in
  integers: `n < (F − 1)³`) and the Morrison conditions (4.14) hold.
  Write `R = r₁F + r₀` in base `F`.  Then `n` is prime IF AND ONLY IF
  neither `x² + r₀x − r₁` nor `x² + (r₀ − F)x − r₁ − 1` has a positive
  integral root.

  When `R < F` we have `r₁ = 0` and neither quadratic can have a
  positive root, so this theorem contains the final assertion of
  Theorem 4.2.3 (`morrison_test`) — but it reaches all the way down to
  cube-root-sized `F`.

  Composite direction: by Theorem 4.2.3 every prime factor `p` of `n`
  satisfies `p ≡ (Δ/p) (mod F)`, hence `p ≥ F − 1`; three factors
  would exceed `(F − 1)³ > n`, so `n = pq`, and multiplying the Jacobi
  symbols, `(Δ/p) = 1` and `(Δ/q) = −1` after a swap: `p = cF + 1`,
  `q = dF − 1` with `1 ≤ c, d ≤ F − 1` (else `n ≥ (F² + 1)(F − 1)` or
  `n ≥ (F + 1)(F² − 1)`, both exceeding `(F − 1)³`).  Matching base-`F`
  digits of `R = cdF + (d − c)` gives `d = c + r₀ − iF` for `i = 0` or
  `1`, and then `c` is a positive root of `x² + (r₀ − iF)x − r₁ − i`.

  Prime direction: a positive root `c` of either quadratic undoes that
  algebra exactly — with `d := c + r₀ − iF` one computes
  `(cF + 1)(dF − 1) = (r₁F + r₀)F − 1 = n` on the nose (uniformly in
  `i`!), and positivity of `n` forces `d ≥ 1`, exhibiting a
  nontrivial factorization.
-/
import Azurite.CrandallPomerance.Chapter4.Theorem_4_2_3

namespace Azurite

namespace CP

/-- Base-`F` digit uniqueness over `ℤ`: two representations
`x·F + y = x'·F + y'` with both remainders in `[0, F)` agree. -/
private theorem digit_eq {F x x' y y' : ℤ} (hF : 0 < F)
    (hy0 : 0 ≤ y) (hyF : y < F) (hy'0 : 0 ≤ y') (hy'F : y' < F)
    (h : x * F + y = x' * F + y') : x = x' ∧ y = y' := by
  rcases lt_trichotomy x x' with hx | hx | hx
  · exfalso
    have h1 : 1 ≤ x' - x := by omega
    have := mul_le_mul_of_nonneg_right h1 hF.le
    nlinarith
  · exact ⟨hx, by rw [hx] at h; omega⟩
  · exfalso
    have h1 : 1 ≤ x - x' := by omega
    have := mul_le_mul_of_nonneg_right h1 hF.le
    nlinarith

/-- A composite `n < (F − 1)³` all of whose prime factors are at least
`F − 1` is a product of exactly two primes. -/
private theorem two_prime_factors_lower {n F : ℕ} (hn : 1 < n)
    (hcomp : ¬n.Prime) (hlt : n < (F - 1) ^ 3)
    (hfac : ∀ p : ℕ, p.Prime → p ∣ n → F - 1 ≤ p) :
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ n = p * q := by
  obtain ⟨p, hp, m, hm⟩ : ∃ p, p.Prime ∧ ∃ m, n = p * m :=
    ⟨n.minFac, Nat.minFac_prime (by omega), n / n.minFac,
      (Nat.mul_div_cancel' n.minFac_dvd).symm⟩
  have hm1 : m ≠ 1 := by
    rintro rfl
    rw [mul_one] at hm
    exact hcomp (hm ▸ hp)
  obtain ⟨r, hr, k, hk⟩ : ∃ r, r.Prime ∧ ∃ k, m = r * k :=
    ⟨m.minFac, Nat.minFac_prime hm1, m / m.minFac,
      (Nat.mul_div_cancel' m.minFac_dvd).symm⟩
  rcases eq_or_ne k 1 with rfl | hk1
  · exact ⟨p, r, hp, hr, by rw [hm, hk, mul_one]⟩
  exfalso
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hk
    rw [hk, mul_zero] at hm
    omega
  have ht : k.minFac.Prime := Nat.minFac_prime hk1
  have h1 : F - 1 ≤ p := hfac _ hp ⟨m, hm⟩
  have h2 : F - 1 ≤ r := hfac _ hr ⟨p * k, by rw [hm, hk]; ring⟩
  have h3 : F - 1 ≤ k.minFac :=
    hfac _ ht (k.minFac_dvd.trans ⟨p * r, by rw [hm, hk]; ring⟩)
  have h3' : F - 1 ≤ k := h3.trans (Nat.minFac_le (by omega))
  have hbig : (F - 1) ^ 3 ≤ n := by
    calc (F - 1) ^ 3 = (F - 1) * ((F - 1) * (F - 1)) := by ring
    _ ≤ p * (r * k) := Nat.mul_le_mul h1 (Nat.mul_le_mul h2 h3')
    _ = n := by rw [hm, hk]
  omega

/-- A positive integral root of `x² + (r₀ − iF)x − r₁ − i` yields the
explicit factorization `n = (cF + 1)((c + r₀ − iF)F − 1)`, uniformly
in `i`; so `n` is composite.  This is the prime direction of
Theorem 4.2.8 in contrapositive form. -/
private theorem not_prime_of_root {n F r₁ r₀ : ℕ} {i : ℤ} (hF : 3 ≤ F)
    (hdig : n + 1 = (r₁ * F + r₀) * F) {c : ℤ} (hc : 0 < c)
    (hroot : c ^ 2 + ((r₀ : ℤ) - i * F) * c - r₁ - i = 0) :
    ¬n.Prime := by
  have hFz : (3 : ℤ) ≤ F := by exact_mod_cast hF
  have hn1 : ((n : ℤ) + 1) = ((r₁ : ℤ) * F + r₀) * F := by
    exact_mod_cast hdig
  have hfact : ((c * F + 1) * ((c + r₀ - i * F) * F - 1) : ℤ) = n := by
    linear_combination ((F : ℤ)) ^ 2 * hroot - hn1
  have hcF0 : (0 : ℤ) ≤ c * F := mul_nonneg hc.le (by omega)
  -- positivity of `n` forces the second factor positive
  have hd1 : 1 ≤ c + (r₀ : ℤ) - i * F := by
    by_contra hd
    push Not at hd
    have hB2 : (c + (r₀ : ℤ) - i * F) * F - 1 ≤ -1 := by
      have : (c + (r₀ : ℤ) - i * F) * F ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg (by omega) (by omega)
      omega
    have hmul := mul_le_mul_of_nonneg_left hB2 (by omega : (0 : ℤ) ≤ c * F + 1)
    rw [hfact, show (c * F + 1) * (-1 : ℤ) = -(c * F) - 1 by ring] at hmul
    have := Int.natCast_nonneg n
    omega
  -- transfer the factorization to `ℕ`
  obtain ⟨d', hd'⟩ : ∃ d' : ℕ, (c + (r₀ : ℤ) - i * F) = d' :=
    ⟨(c + (r₀ : ℤ) - i * F).toNat, (Int.toNat_of_nonneg (by omega)).symm⟩
  lift c to ℕ using hc.le with c'
  have hc1 : 0 < c' := by exact_mod_cast hc
  have hd1' : 0 < d' := by exact_mod_cast hd' ▸ hd1
  rw [hd'] at hfact
  have hgeB : 1 ≤ d' * F := Nat.mul_pos hd1' (by omega)
  have hfactN : (c' * F + 1) * (d' * F - 1) = n := by
    have hcast : (((c' * F + 1) * (d' * F - 1) : ℕ) : ℤ) = ((n : ℕ) : ℤ) := by
      push_cast [hgeB]
      linear_combination hfact
    exact_mod_cast hcast
  rw [← hfactN]
  have hcF : F ≤ c' * F := Nat.le_mul_of_pos_left F hc1
  have hdF : F ≤ d' * F := Nat.le_mul_of_pos_left F hd1'
  exact Nat.not_prime_mul (by omega) (by omega)

/-- **Crandall–Pomerance Theorem 4.2.8**: the `n + 1` test at
cube-root-sized `F`.  Under the Morrison hypotheses (4.14) with
`n + 1 = (r₁F + r₀)·F`, `r₀ < F`, and `F > n^(1/3) + 1` (in integers,
`n < (F − 1)³`), `n` is prime if and only if neither `x² + r₀x − r₁`
nor `x² + (r₀ − F)x − r₁ − 1` has a positive integral root.  When
`R = (n+1)/F < F` the quadratics trivially have no positive roots, so
this contains `morrison_test`. -/
theorem theorem_4_2_8 {a b : ℤ} {n F r₁ r₀ : ℕ} (hn : 0 < n)
    (hcop : IsCoprime (n : ℤ) (2 * b))
    (hjac : jacobiSym (a ^ 2 - 4 * b) n = -1)
    (hdig : n + 1 = (r₁ * F + r₀) * F) (hr₀ : r₀ < F)
    (hcube : n < (F - 1) ^ 3)
    (hU : (n : ℤ) ∣ lucasU a b (n + 1))
    (hq : ∀ q : ℕ, q.Prime → q ∣ F →
      IsCoprime (n : ℤ) (lucasU a b ((n + 1) / q))) :
    n.Prime ↔
      (¬∃ c : ℤ, 0 < c ∧ c ^ 2 + r₀ * c - r₁ = 0) ∧
      (¬∃ c : ℤ, 0 < c ∧ c ^ 2 + ((r₀ : ℤ) - F) * c - r₁ - 1 = 0) := by
  -- `n = 1` is impossible: `(Δ/1) = 1 ≠ −1`
  have hn2 : 2 ≤ n := by
    rcases Nat.lt_or_ge n 2 with h | h
    · interval_cases n
      rw [jacobiSym.one_right] at hjac
      omega
    · exact h
  have hF3 : 3 ≤ F := by
    by_contra h
    push Not at h
    have h13 : (F - 1) ^ 3 ≤ 1 := by
      calc (F - 1) ^ 3 ≤ 1 ^ 3 := Nat.pow_le_pow_left (by omega) 3
      _ = 1 := one_pow 3
    omega
  have hFz : (3 : ℤ) ≤ F := by exact_mod_cast hF3
  constructor
  · -- prime ⟹ no positive roots
    intro hprime
    constructor
    · rintro ⟨c, hc0, hc⟩
      exact not_prime_of_root (i := 0) hF3 hdig hc0
        (by linear_combination hc) hprime
    · rintro ⟨c, hc0, hc⟩
      exact not_prime_of_root (i := 1) hF3 hdig hc0
        (by linear_combination hc) hprime
  · -- no positive roots ⟹ prime
    rintro ⟨hno0, hno1⟩
    by_contra hcomp
    have : NeZero n := ⟨by omega⟩
    -- `Δ` is coprime to `n` (the Jacobi symbol is nonzero) …
    have hΔn : Int.gcd (a ^ 2 - 4 * b) n = 1 := by
      by_contra h
      have h0 : jacobiSym (a ^ 2 - 4 * b) n = 0 :=
        jacobiSym.eq_zero_iff_not_coprime.mpr h
      rw [hjac] at h0
      norm_num at h0
    have hΔn' : Nat.Coprime (a ^ 2 - 4 * b).natAbs n := by
      rwa [Int.gcd, Int.natAbs_natCast] at hΔn
    -- … hence `(Δ/p) = ±1` for every prime factor `p`
    have hJpm : ∀ p : ℕ, p.Prime → p ∣ n →
        jacobiSym (a ^ 2 - 4 * b) p = 1 ∨
          jacobiSym (a ^ 2 - 4 * b) p = -1 := by
      intro p hp hpn
      exact jacobiSym.eq_one_or_neg_one (by
        rw [Int.gcd, Int.natAbs_natCast]
        exact hΔn'.coprime_dvd_right hpn)
    have hp423 := theorem_4_2_3 hn hcop hjac
      ⟨r₁ * F + r₀, by rw [hdig]; ring⟩ hU hq
    -- every prime factor is at least `F − 1`
    have hlow : ∀ p : ℕ, p.Prime → p ∣ n → F - 1 ≤ p := by
      intro p hp hpn
      have hdvd := hp423 p hp hpn
      have hp2 : (2 : ℤ) ≤ p := by exact_mod_cast hp.two_le
      have h1F : 1 ≤ F := by omega
      rcases hJpm p hp hpn with h1 | h1 <;> rw [h1] at hdvd <;>
          obtain ⟨t, ht⟩ := hdvd
      · -- `F ∣ p − 1`, `p ≥ 2` ⟹ `p ≥ F + 1`
        have ht1 : 1 ≤ t := by
          by_contra htn
          push Not at htn
          have : (F : ℤ) * t ≤ 0 :=
            mul_nonpos_of_nonneg_of_nonpos (by omega) (by omega)
          omega
        have hFt := mul_le_mul_of_nonneg_left ht1 (by omega : (0 : ℤ) ≤ F)
        rw [mul_one] at hFt
        zify [h1F]
        omega
      · -- `F ∣ p + 1` ⟹ `p ≥ F − 1`
        have ht' : (p : ℤ) + 1 = F * t := by linear_combination ht
        have ht1 : 1 ≤ t := by
          by_contra htn
          push Not at htn
          have : (F : ℤ) * t ≤ 0 :=
            mul_nonpos_of_nonneg_of_nonpos (by omega) (by omega)
          omega
        have hFt := mul_le_mul_of_nonneg_left ht1 (by omega : (0 : ℤ) ≤ F)
        rw [mul_one] at hFt
        zify [h1F]
        omega
    -- exactly two prime factors, with split Jacobi symbols
    obtain ⟨P, Q, hP, hQ, hnPQ, hJP, hJQ⟩ :
        ∃ P Q : ℕ, P.Prime ∧ Q.Prime ∧ n = P * Q ∧
          jacobiSym (a ^ 2 - 4 * b) P = 1 ∧
          jacobiSym (a ^ 2 - 4 * b) Q = -1 := by
      obtain ⟨p, q, hp, hq, hpq⟩ :=
        two_prime_factors_lower (by omega) hcomp hcube hlow
      have : NeZero p := ⟨hp.pos.ne'⟩
      have : NeZero q := ⟨hq.pos.ne'⟩
      have hmul : (-1 : ℤ) = jacobiSym (a ^ 2 - 4 * b) p
          * jacobiSym (a ^ 2 - 4 * b) q := by
        rw [← hjac, hpq, jacobiSym.mul_right]
      rcases hJpm p hp ⟨q, hpq⟩ with h1 | h1 <;>
          rcases hJpm q hq ⟨p, by rw [hpq]; ring⟩ with h2 | h2
      · rw [h1, h2] at hmul
        norm_num at hmul
      · exact ⟨p, q, hp, hq, hpq, h1, h2⟩
      · exact ⟨q, p, hq, hp, by rw [hpq]; ring, h2, h1⟩
      · rw [h1, h2] at hmul
        norm_num at hmul
    -- `P = cF + 1`, `Q = dF − 1` with `1 ≤ c, d ≤ F − 1`
    have hPF := hp423 P hP ⟨Q, hnPQ⟩
    have hQF := hp423 Q hQ ⟨P, by rw [hnPQ]; ring⟩
    rw [hJP] at hPF
    rw [hJQ] at hQF
    obtain ⟨c, hc⟩ := hPF
    obtain ⟨d, hd⟩ := hQF
    have hd' : (Q : ℤ) + 1 = F * d := by linear_combination hd
    have hPz : (2 : ℤ) ≤ P := by exact_mod_cast hP.two_le
    have hQz : (2 : ℤ) ≤ Q := by exact_mod_cast hQ.two_le
    have hnz : (n : ℤ) = P * Q := by exact_mod_cast hnPQ
    have hcube' : (n : ℤ) < ((F : ℤ) - 1) ^ 3 := by
      have h1F : (1 : ℕ) ≤ F := by omega
      zify [h1F] at hcube
      exact hcube
    have hc1 : 1 ≤ c := by
      by_contra h
      push Not at h
      have : (F : ℤ) * c ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (by omega) (by omega)
      omega
    have hd1 : 1 ≤ d := by
      by_contra h
      push Not at h
      have : (F : ℤ) * d ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (by omega) (by omega)
      omega
    have hFc := mul_le_mul_of_nonneg_left hc1 (by omega : (0 : ℤ) ≤ F)
    have hFd := mul_le_mul_of_nonneg_left hd1 (by omega : (0 : ℤ) ≤ F)
    rw [mul_one] at hFc hFd
    have hPlow : (F : ℤ) + 1 ≤ P := by omega
    have hQlow : (F : ℤ) - 1 ≤ Q := by omega
    have hcF : c ≤ (F : ℤ) - 1 := by
      by_contra hcx
      push Not at hcx
      -- `c ≥ F` gives `P ≥ F² + 1`, so `n ≥ (F² + 1)(F − 1) > (F − 1)³`
      have hFF : (F : ℤ) * F ≤ F * c :=
        mul_le_mul_of_nonneg_left (by omega) (by omega)
      have hPbig : (F : ℤ) * F + 1 ≤ P := by omega
      nlinarith [mul_le_mul hPbig hQlow (by omega) (by omega : (0 : ℤ) ≤ P)]
    have hdF : d ≤ (F : ℤ) - 1 := by
      by_contra hdx
      push Not at hdx
      -- `d ≥ F` gives `Q ≥ F² − 1`, so `n ≥ (F + 1)(F² − 1) > (F − 1)³`
      have hFF : (F : ℤ) * F ≤ F * d :=
        mul_le_mul_of_nonneg_left (by omega) (by omega)
      have hQbig : (F : ℤ) * F - 1 ≤ Q := by omega
      nlinarith [mul_le_mul hPlow hQbig (by nlinarith : (0 : ℤ) ≤ F * F - 1)
        (by omega : (0 : ℤ) ≤ P)]
    -- match base-`F` digits of `R = cdF + (d − c)`
    have hn1z : ((n : ℤ) + 1) = ((r₁ : ℤ) * F + r₀) * F := by
      exact_mod_cast hdig
    have hkey : (r₁ : ℤ) * F + r₀ = (c * d) * F + (d - c) := by
      have hexp : (n : ℤ) + 1 = ((c * d) * F + (d - c)) * F := by
        rw [hnz]
        linear_combination (Q : ℤ) * hc + ((F : ℤ) * c + 1) * hd'
      exact mul_right_cancel₀ (by omega : (F : ℤ) ≠ 0)
        (hn1z.symm.trans hexp)
    have hr₀z : ((r₀ : ℤ)) < F := by exact_mod_cast hr₀
    by_cases hcd : c ≤ d
    · -- `d ≥ c`: digits are `(cd, d − c)` — root of the `i = 0` quadratic
      obtain ⟨h1, h2⟩ := digit_eq (by omega) (by positivity) hr₀z
        (by omega) (by omega) hkey
      exact hno0 ⟨c, by omega, by linear_combination c * h2 - h1⟩
    · -- `d < c`: digits are `(cd − 1, d − c + F)` — root of `i = 1`
      push Not at hcd
      have hkey' : (r₁ : ℤ) * F + r₀ = (c * d - 1) * F + (d - c + F) := by
        linear_combination hkey
      obtain ⟨h1, h2⟩ := digit_eq (by omega) (by positivity) hr₀z
        (by omega) (by omega) hkey'
      exact hno1 ⟨c, by omega, by linear_combination c * h2 - h1⟩

section Examples

/-- `127` is prime by the cube-root `n + 1` test with Fibonacci
`(a, b) = (1, −1)`: `Δ = 5`, `(5/127) = −1`, `128 = 8 · 16` with
`F = 8` well below the `√127`-reach of `morrison_test` (which needs
`F ≥ 13`), digits `(r₁, r₀) = (2, 0)`, and the two quadratics
`x² − 2` and `x² − 8x − 3` have no positive integral roots. -/
example : Nat.Prime 127 := by
  have h := theorem_4_2_8 (a := 1) (b := -1) (n := 127) (F := 8)
    (r₁ := 2) (r₀ := 0)
    (by norm_num)
    (by rw [Int.isCoprime_iff_gcd_eq_one]; decide)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by set_option maxRecDepth 8192 in decide)
    (by
      intro q hq hqF
      have hq8 : q ≤ 8 := Nat.le_of_dvd (by norm_num) hqF
      have hq2 : 2 ≤ q := hq.two_le
      interval_cases q
      · rw [Int.isCoprime_iff_gcd_eq_one]
        set_option maxRecDepth 8192 in decide
      · exact absurd hqF (by decide)
      · exact absurd hq (by decide)
      · exact absurd hqF (by decide)
      · exact absurd hq (by decide)
      · exact absurd hqF (by decide)
      · exact absurd hq (by decide))
  refine h.mpr ⟨?_, ?_⟩
  · rintro ⟨c, hc0, hc⟩
    push_cast at hc
    have hub : c ≤ 2 := by
      by_contra hx
      push Not at hx
      nlinarith [mul_nonneg (by omega : (0 : ℤ) ≤ c - 3) hc0.le]
    interval_cases c <;> norm_num at hc
  · rintro ⟨c, hc0, hc⟩
    push_cast at hc
    have hub : c ≤ 9 := by
      by_contra hx
      push Not at hx
      nlinarith [mul_nonneg (by omega : (0 : ℤ) ≤ c - 10) hc0.le]
    interval_cases c <;> norm_num at hc

/-- `119 = 7 · 17` passes the Morrison conditions (4.14) for
`(a, b) = (3, −1)`, `Δ = 13`, `F = 8` — yet it is composite, and the
`i = 1` quadratic `x² − x − 2` catches it: the root `c = 2` reveals
the factor `2 · 8 + 1 = 17`. -/
example : ¬Nat.Prime 119 := by
  intro hprime
  have h := theorem_4_2_8 (a := 3) (b := -1) (n := 119) (F := 8)
    (r₁ := 1) (r₀ := 7)
    (by norm_num)
    (by rw [Int.isCoprime_iff_gcd_eq_one]; decide)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by norm_num)
    (by set_option maxRecDepth 8192 in decide)
    (by
      intro q hq hqF
      have hq8 : q ≤ 8 := Nat.le_of_dvd (by norm_num) hqF
      have hq2 : 2 ≤ q := hq.two_le
      interval_cases q
      · rw [Int.isCoprime_iff_gcd_eq_one]
        set_option maxRecDepth 8192 in decide
      · exact absurd hqF (by decide)
      · exact absurd hq (by decide)
      · exact absurd hqF (by decide)
      · exact absurd hq (by decide)
      · exact absurd hqF (by decide)
      · exact absurd hq (by decide))
  exact (h.mp hprime).2 ⟨2, by norm_num, by norm_num⟩

end Examples

end CP

end Azurite
