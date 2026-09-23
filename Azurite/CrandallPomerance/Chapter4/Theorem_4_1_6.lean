/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

/-
  Crandall–Pomerance, Theorem 4.1.6 (Konyagin–Pomerance): suppose
  `n ≥ 214`, `n − 1 = F·R` with `F` fully factored, the Pocklington
  conditions (4.3) hold for a witness, and `n^(3/10) ≤ F < n^(1/3)`
  (in integers: `F³ < n` and `n³ ≤ F¹⁰`).  Write `n = c₄F² + c₁F + 1`
  with `c₁ < F` (in the book `c₄ = c₃F + c₂` collects the top two base-F
  digits).  Then `n` is prime if and only if

  (1) `(c₁ + tF)² + 4t − 4c₄` is not a square for `t = 0, 1, …, 5`, and
  (2) for a rational approximation `u/v` to `c₁/F` with `v` maximal
      subject to `v < F²/√n` (the book: a continued-fraction
      convergent), and `d = ⌊c₄v/F + 1/2⌋`, the cubic
      `vx³ + (uF − c₁v)x² + (c₄v − dF + u)x − d` has no integer root
      `a` with `aF + 1` a nontrivial factor of `n`.

  A factored part of only `n^(3/10)` still decides primality!  The proof
  uses just two properties of `(u, v)`: `v < F²/√n` (stated
  as `v²n < F⁴`), and `|uF − c₁v| ≤ √n/F` (stated as
  `(uF − c₁v)²F² ≤ n`; for the book's convergent this follows from
  `|c₁/F − u/v| ≤ 1/(vv')` with `v' ≥ F²/√n`, and it holds trivially
  when `u/v = c₁/F`).  We therefore take such a pair as given, and `d`
  by its integer formula `d = (2c₄v + F) / (2F)`.

  Sketch (composite ⟹ ¬(1) ∨ ¬(2)): `n` composite means
  `n = (a₁F + 1)(a₂F + 1)` with `1 ≤ a₁ ≤ a₂` (each prime factor is
  `1 (mod F)` by Pocklington, and a product of such is again
  `1 (mod F)`).  Matching digits: `a₁ + a₂ = c₁ + tF` and
  `a₁a₂ = c₄ − t` for some `t ≥ 0` (4.4).  If `t ≤ 5`, then
  `(c₁ + tF)² + 4t − 4c₄ = (a₂ − a₁)²` refutes (1).  So `t ≥ 6`, whence
  `a₂ ≥ 3F`, `3a₁F³ < n` (4.5), and `tF³ < n` with `6F³ < n` (4.6).
  The identity (4.7)/(4.8) gives, for `D = a₁u + a₁tv`,
  `DF − c₄v = a₁(uF − c₁v) + (a₁² − t)v`, and the bounds make
  `2|DF − c₄v| < F` — i.e. `D` is the nearest integer to `c₄v/F`, so
  `D = d`.  Substituting `a₁tv = d − a₁u` into `a₁v·(4.7)` shows `a₁` is
  an integer root of the cubic with `a₁F + 1` a nontrivial factor,
  refuting (2).

  (Prime ⟹ (1) ∧ (2)): (2) is immediate (no nontrivial factors).  For
  (1): a square `(c₁ + tF)² + 4t − 4c₄ = s²` factors
  `n = (uF + 1)(vF + 1)` with `uv = c₄ − t ≥ 1` (here `n ≥ 214` enters:
  `n³ ≤ F¹⁰` and `214³ > 5¹⁰` force `F ≥ 6 > t`, and `c₄ ≥ F > t`),
  contradicting primality.
-/
import Azurite.CrandallPomerance.Chapter4.Theorem_4_1_3
import Mathlib.Tactic.LinearCombination

namespace Azurite

namespace CP

/-- A positive number all of whose prime factors are `1 (mod F)` is
itself `1 (mod F)`. -/
private theorem modEq_one_of_forall_prime {F : ℕ} :
    ∀ m : ℕ, 0 < m → (∀ r : ℕ, r.Prime → r ∣ m → r ≡ 1 [MOD F]) →
      m ≡ 1 [MOD F] := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro hm hfac
    rcases eq_or_ne m 1 with rfl | hm1
    · rfl
    obtain ⟨r, hr, k, hk⟩ : ∃ r, r.Prime ∧ ∃ k, m = r * k :=
      ⟨m.minFac, Nat.minFac_prime hm1, m / m.minFac,
        (Nat.mul_div_cancel' m.minFac_dvd).symm⟩
    have hk0 : 0 < k := by
      rcases Nat.eq_zero_or_pos k with rfl | h
      · rw [mul_zero] at hk
        omega
      · exact h
    have hklt : k < m := by
      have hr2 := hr.two_le
      calc k < 2 * k := by omega
      _ ≤ r * k := Nat.mul_le_mul_right _ hr2
      _ = m := hk.symm
    have h1 : r ≡ 1 [MOD F] := hfac r hr ⟨k, hk⟩
    have h2 : k ≡ 1 [MOD F] :=
      ih k hklt hk0 (fun s hs hsk => hfac s hs (hsk.trans ⟨r, by rw [hk]; ring⟩))
    calc m = r * k := hk
    _ ≡ 1 * 1 [MOD F] := h1.mul h2
    _ = 1 := one_mul 1

/-- Unpack `x ≡ 1 (mod F)` with `x > 1` into `x = wF + 1`, `w ≥ 1`. -/
private theorem eq_mul_add_one {F x : ℕ} (hF : 2 ≤ F) (hx : 1 < x)
    (h : x ≡ 1 [MOD F]) : ∃ w : ℕ, 1 ≤ w ∧ x = w * F + 1 := by
  have hmod : x % F = 1 := by
    have := h
    unfold Nat.ModEq at this
    rwa [Nat.mod_eq_of_lt (by omega : 1 < F)] at this
  have hdm := Nat.div_add_mod x F
  rw [hmod] at hdm
  refine ⟨x / F, ?_, ?_⟩
  · rcases Nat.eq_zero_or_pos (x / F) with h0 | h1
    · rw [h0, Nat.mul_zero, Nat.zero_add] at hdm
      omega
    · exact h1
  · rw [Nat.mul_comm] at hdm
    omega

/-- A composite `n` all of whose prime factors are `1 (mod F)` splits as
`(a₁F + 1)(a₂F + 1)` with `1 ≤ a₁ ≤ a₂`. -/
private theorem composite_split {n F : ℕ} (hF : 2 ≤ F) (hn : 1 < n)
    (hcomp : ¬n.Prime)
    (hfac : ∀ p : ℕ, p.Prime → p ∣ n → p ≡ 1 [MOD F]) :
    ∃ a₁ a₂ : ℕ, 1 ≤ a₁ ∧ a₁ ≤ a₂ ∧ n = (a₁ * F + 1) * (a₂ * F + 1) := by
  obtain ⟨p, hp, m, hm⟩ : ∃ p, p.Prime ∧ ∃ m, n = p * m :=
    ⟨n.minFac, Nat.minFac_prime (by omega), n / n.minFac,
      (Nat.mul_div_cancel' n.minFac_dvd).symm⟩
  have hm1 : 1 < m := by
    rcases Nat.lt_or_ge m 2 with h | h
    · interval_cases m
      · rw [mul_zero] at hm
        omega
      · rw [mul_one] at hm
        exact absurd (hm ▸ hp) hcomp
    · exact h
  have hpmod : p ≡ 1 [MOD F] := hfac p hp ⟨m, hm⟩
  have hmmod : m ≡ 1 [MOD F] :=
    modEq_one_of_forall_prime m (by omega)
      (fun r hr hrm => hfac r hr (hrm.trans ⟨p, by rw [hm]; ring⟩))
  obtain ⟨w₁, hw₁, hpw⟩ := eq_mul_add_one hF hp.one_lt hpmod
  obtain ⟨w₂, hw₂, hmw⟩ := eq_mul_add_one hF hm1 hmmod
  rcases le_total w₁ w₂ with hle | hle
  · exact ⟨w₁, w₂, hw₁, hle, by rw [hm, hpw, hmw]⟩
  · exact ⟨w₂, w₁, hw₂, hle, by rw [hm, hpw, hmw]; ring⟩

/-- A natural number strictly between consecutive squares is not a square
(as an integer). -/
theorem not_isSquare_intCast_of_lt_of_lt {m k : ℕ} (h1 : k ^ 2 < m)
    (h2 : m < (k + 1) ^ 2) : ¬IsSquare ((m : ℕ) : ℤ) := by
  rintro ⟨r, hr⟩
  have h := congrArg Int.natAbs hr
  rw [Int.natAbs_natCast, Int.natAbs_mul] at h
  set j := r.natAbs with hj
  rcases Nat.lt_or_ge j (k + 1) with hle | hlt
  · have hle' : j ≤ k := by omega
    have : j * j ≤ k * k := Nat.mul_le_mul hle' hle'
    have hk2 : k * k = k ^ 2 := by ring
    omega
  · have : (k + 1) * (k + 1) ≤ j * j := Nat.mul_le_mul hlt hlt
    have hk2 : (k + 1) * (k + 1) = (k + 1) ^ 2 := by ring
    omega

/-- For prime `n = c₄F² + c₁F + 1` in the KP setting (`6 ≤ F ≤ c₄`,
`c₁ < F`), no shifted discriminant `(c₁ + tF)² + 4t − 4c₄` with `t ≤ 5`
is a square: a square would factor `n` nontrivially. -/
private theorem prime_kp_disc_not_square {n F c₁ c₄ : ℕ} (hF6 : 6 ≤ F)
    (hc4F : F ≤ c₄) (hrep : n = c₄ * F ^ 2 + c₁ * F + 1)
    (hprime : n.Prime) :
    ∀ t : ℕ, t ≤ 5 → ¬IsSquare (((c₁ : ℤ) + t * F) ^ 2 + 4 * t - 4 * c₄) := by
  intro t ht hsq
  obtain ⟨r, hr⟩ := hsq
  set σ := c₁ + t * F with hσ
  have hct : t < c₄ := by omega
  -- transfer to ℕ: `σ² + 4t = s² + 4c₄`
  set s := r.natAbs with hsdef
  have hs2 : ((s : ℤ)) ^ 2 = r * r := by
    rw [sq]
    exact_mod_cast Int.natAbs_mul_self
  have hznat : σ ^ 2 + 4 * t = s ^ 2 + 4 * c₄ := by
    have hz : ((σ ^ 2 + 4 * t : ℕ) : ℤ) = ((s ^ 2 + 4 * c₄ : ℕ) : ℤ) := by
      push_cast
      rw [show ((s : ℤ)) ^ 2 = r * r from hs2]
      rw [hσ]
      push_cast
      linarith
    exact_mod_cast hz
  have hsσ : s ≤ σ := by
    have : s ^ 2 ≤ σ ^ 2 := by omega
    exact (Nat.pow_le_pow_iff_left two_ne_zero).mp this
  have hprodF : (σ + s) * (σ - s) = 4 * (c₄ - t) := by
    have h1 : σ ^ 2 - s ^ 2 = 4 * (c₄ - t) := by omega
    rw [Nat.sq_sub_sq] at h1
    exact h1
  have hpar : (σ + s) % 2 = 0 ∧ (σ - s) % 2 = 0 := by
    have hE : Even ((σ + s) * (σ - s)) := ⟨2 * (c₄ - t), by omega⟩
    rcases Nat.even_mul.mp hE with h | h <;> rw [Nat.even_iff] at h <;>
      constructor <;> omega
  obtain ⟨e₁, he₁⟩ : ∃ e₁, σ + s = 2 * e₁ := ⟨(σ + s) / 2, by omega⟩
  obtain ⟨e₂, he₂⟩ : ∃ e₂, σ - s = 2 * e₂ := ⟨(σ - s) / 2, by omega⟩
  have hprod : e₁ * e₂ = c₄ - t := by
    have h4 : 4 * (e₁ * e₂) = 4 * (c₄ - t) := by
      rw [← hprodF, he₁, he₂]
      ring
    exact Nat.eq_of_mul_eq_mul_left (by omega) h4
  have hsum : e₁ + e₂ = σ := by omega
  have he₂pos : 1 ≤ e₂ := by
    rcases Nat.eq_zero_or_pos e₂ with h0 | h
    · rw [h0, mul_zero] at hprod
      omega
    · exact h
  have he₁pos : 1 ≤ e₁ := by omega
  -- rebuild `n` from the shifted digits, then factor
  have hrep' : n = (c₄ - t) * F ^ 2 + σ * F + 1 := by
    have hσF : σ * F = c₁ * F + t * F ^ 2 := by
      rw [hσ]
      ring
    have hswap : (c₄ - t) * F ^ 2 + t * F ^ 2 = c₄ * F ^ 2 := by
      rw [← Nat.add_mul, Nat.sub_add_cancel hct.le]
    omega
  have hfact : n = (e₁ * F + 1) * (e₂ * F + 1) := by
    rw [hrep', ← hprod, ← hsum]
    ring
  rw [hfact] at hprime
  have hx1 : e₁ * F + 1 ≠ 1 := by
    intro h
    rcases Nat.mul_eq_zero.mp (by omega : e₁ * F = 0) with h' | h' <;> omega
  have hy1 : e₂ * F + 1 ≠ 1 := by
    intro h
    rcases Nat.mul_eq_zero.mp (by omega : e₂ * F = 0) with h' | h' <;> omega
  exact Nat.not_prime_mul hx1 hy1 hprime

/-- The composite-side core of Konyagin–Pomerance: a composite `n` in the
KP setting whose shifted discriminants pass condition (1) decomposes as
`(a₁F + 1)(a₂F + 1)` with `t ≥ 6` in the digit matching, whence the
small factor obeys `3a₁F³ < n` (and `tF³ < n`). -/
private theorem kp_small_factor {n F R c₁ c₄ : ℕ} (hn : 214 ≤ n)
    (hsplit : n - 1 = F * R) (a : ZMod n) (ha : a ^ (n - 1) = 1)
    (hunit : ∀ q : ℕ, q.Prime → q ∣ F → IsUnit (a ^ ((n - 1) / q) - 1))
    (hlo : n ^ 3 ≤ F ^ 10)
    (hc1 : c₁ < F) (hrep : n = c₄ * F ^ 2 + c₁ * F + 1)
    (h1 : ∀ t : ℕ, t ≤ 5 →
      ¬IsSquare (((c₁ : ℤ) + t * F) ^ 2 + 4 * t - 4 * c₄))
    (hcomp : ¬n.Prime) :
    ∃ a₁ a₂ t : ℕ, 1 ≤ a₁ ∧ a₁ ≤ a₂ ∧
      n = (a₁ * F + 1) * (a₂ * F + 1) ∧ 6 ≤ t ∧
      a₁ + a₂ = c₁ + t * F ∧ a₁ * a₂ + t = c₄ ∧
      3 * a₁ * F ^ 3 < n ∧ t * F ^ 3 < n := by
  have hn1 : 1 < n := by omega
  have hF6 : 6 ≤ F := by
    by_contra h
    have hF5 : F ≤ 5 := by omega
    have h1' : F ^ 10 ≤ 5 ^ 10 := Nat.pow_le_pow_left hF5 10
    have h2' : 214 ^ 3 ≤ n ^ 3 := Nat.pow_le_pow_left hn 3
    norm_num at h1' h2'
    omega
  -- decompose: `n = (a₁F + 1)(a₂F + 1)`, `1 ≤ a₁ ≤ a₂`
  obtain ⟨a₁, a₂, ha₁, ha₁₂, hfact⟩ :=
    composite_split (by omega) hn1 hcomp
      (fun p hp hpd => pocklington hn1 hsplit a ha hunit p hp hpd)
  -- digit matching (4.4): `a₁ + a₂ = c₁ + tF`, `a₁a₂ + t = c₄`
  have hE : a₁ * a₂ * F + (a₁ + a₂) = c₄ * F + c₁ := by
    have hexp : n = a₁ * a₂ * F ^ 2 + (a₁ + a₂) * F + 1 := by
      rw [hfact]
      ring
    have hFeq : F * (a₁ * a₂ * F + (a₁ + a₂)) + 1 =
        F * (c₄ * F + c₁) + 1 := by
      calc F * (a₁ * a₂ * F + (a₁ + a₂)) + 1
          = a₁ * a₂ * F ^ 2 + (a₁ + a₂) * F + 1 := by ring
      _ = n := hexp.symm
      _ = c₄ * F ^ 2 + c₁ * F + 1 := hrep
      _ = F * (c₄ * F + c₁) + 1 := by ring
    exact Nat.eq_of_mul_eq_mul_left (by omega) (Nat.add_right_cancel hFeq)
  have hsummod : (a₁ + a₂) % F = c₁ := by
    have h1' : (a₁ * a₂ * F + (a₁ + a₂)) % F = (a₁ + a₂) % F :=
      Nat.mul_add_mod' _ _ _
    have h2' : (c₄ * F + c₁) % F = c₁ := Nat.mul_add_mod_of_lt hc1
    rw [← h1', hE, h2']
  obtain ⟨t, ht⟩ : ∃ t, a₁ + a₂ = c₁ + t * F := by
    have hdm := Nat.div_add_mod (a₁ + a₂) F
    rw [hsummod] at hdm
    refine ⟨(a₁ + a₂) / F, ?_⟩
    rw [Nat.mul_comm ((a₁ + a₂) / F) F]
    omega
  have hprod : a₁ * a₂ + t = c₄ := by
    have h1' : a₁ * a₂ * F + t * F = c₄ * F := by omega
    have h2' : (a₁ * a₂ + t) * F = c₄ * F := by
      calc (a₁ * a₂ + t) * F = a₁ * a₂ * F + t * F := by ring
      _ = c₄ * F := h1'
    exact Nat.eq_of_mul_eq_mul_right (by omega) h2'
  -- `t ≥ 6` by condition (1)
  have ht6 : 6 ≤ t := by
    by_contra hlt
    apply h1 t (by omega)
    refine ⟨(a₂ : ℤ) - (a₁ : ℤ), ?_⟩
    have htz : ((a₁ : ℤ) + a₂) = c₁ + t * F := by exact_mod_cast ht
    have hpz : ((a₁ : ℤ) * a₂) + t = c₄ := by exact_mod_cast hprod
    linear_combination (-((a₁ : ℤ) + a₂ + c₁ + t * F)) * htz + 4 * hpz
  -- the inequality kit: `a₂ ≥ 3F`, `3a₁F³ < n`, `tF³ < n`
  have ha₂3F : 3 * F ≤ a₂ := by
    have h6F : 6 * F ≤ t * F := Nat.mul_le_mul_right F ht6
    omega
  have hsumle : a₁ + a₂ ≤ a₁ * a₂ + 1 := by
    zify at ha₁ ha₁₂ ⊢
    nlinarith [mul_nonneg (by linarith : (0 : ℤ) ≤ (a₁ : ℤ) - 1)
      (by linarith : (0 : ℤ) ≤ (a₂ : ℤ) - 1)]
  have h3aF : 3 * a₁ * F ^ 3 < n := by
    have h1' : a₁ * (3 * F) * F ^ 2 ≤ a₁ * a₂ * F ^ 2 :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ ha₂3F)
    have h2' : a₁ * a₂ * F ^ 2 < n := by
      have hexp : n = a₁ * a₂ * F ^ 2 + (a₁ + a₂) * F + 1 := by
        rw [hfact]
        ring
      omega
    calc 3 * a₁ * F ^ 3 = a₁ * (3 * F) * F ^ 2 := by ring
    _ ≤ a₁ * a₂ * F ^ 2 := h1'
    _ < n := h2'
  have htF3 : t * F ^ 3 < n := by
    have h1' : t * F < c₄ := by omega
    have h2' : t * F * F ^ 2 < c₄ * F ^ 2 :=
      mul_lt_mul_of_pos_right h1' (by positivity)
    have h3' : c₄ * F ^ 2 < n := by omega
    calc t * F ^ 3 = t * F * F ^ 2 := by ring
    _ < c₄ * F ^ 2 := h2'
    _ < n := h3'
  exact ⟨a₁, a₂, t, ha₁, ha₁₂, hfact, ht6, ht, hprod, h3aF, htF3⟩

/-- **The Konyagin–Pomerance test** (Crandall–Pomerance Theorem 4.1.6):
suppose `n ≥ 214`, `n − 1 = F·R`, the witness `a` satisfies the
Pocklington conditions, and `n^(3/10) ≤ F < n^(1/3)` (in integers:
`F³ < n` and `n³ ≤ F¹⁰`).  Write `n = c₄F² + c₁F + 1` with `c₁ < F`,
and let `u, v` be a rational approximation to `c₁/F` with
`v²n < F⁴` (that is, `v < F²/√n`) and `(uF − c₁v)²F² ≤ n` (that is,
`|uF − c₁v| ≤ √n/F`; the book's continued-fraction convergent qualifies),
and let `d = ⌊c₄v/F + 1/2⌋ = (2c₄v + F)/(2F)`.  Then `n` is prime if
and only if (1) `(c₁ + tF)² + 4t − 4c₄` is not a square for
`t = 0, …, 5`, and (2) the cubic `vx³ + (uF − c₁v)x² + (c₄v − dF + u)x
− d` has no integer root `x` with `xF + 1` a nontrivial factor of
`n`. -/
theorem theorem_4_1_6 {n F R c₁ c₄ u v d : ℕ} (hn : 214 ≤ n)
    (hsplit : n - 1 = F * R) (a : ZMod n) (ha : a ^ (n - 1) = 1)
    (hunit : ∀ q : ℕ, q.Prime → q ∣ F → IsUnit (a ^ ((n - 1) / q) - 1))
    (hhi : F ^ 3 < n) (hlo : n ^ 3 ≤ F ^ 10)
    (hc1 : c₁ < F) (hrep : n = c₄ * F ^ 2 + c₁ * F + 1)
    (hv2 : v ^ 2 * n < F ^ 4)
    (happrox : ((u : ℤ) * F - c₁ * v) ^ 2 * F ^ 2 ≤ n)
    (hd : d = (2 * c₄ * v + F) / (2 * F)) :
    n.Prime ↔
      ((∀ t : ℕ, t ≤ 5 →
          ¬IsSquare (((c₁ : ℤ) + t * F) ^ 2 + 4 * t - 4 * c₄)) ∧
        ¬∃ x : ℤ, (v : ℤ) * x ^ 3 + ((u : ℤ) * F - c₁ * v) * x ^ 2
              + ((c₄ : ℤ) * v - d * F + u) * x - d = 0
            ∧ (x * F + 1) ∣ (n : ℤ) ∧ 1 < x * F + 1 ∧ x * F + 1 < n) := by
  have hn1 : 1 < n := by omega
  -- `F ≥ 6`: from `n³ ≤ F¹⁰` and `214³ > 5¹⁰` (this is where `n ≥ 214`
  -- earns its keep)
  have hF6 : 6 ≤ F := by
    by_contra h
    have hF5 : F ≤ 5 := by omega
    have h1 : F ^ 10 ≤ 5 ^ 10 := Nat.pow_le_pow_left hF5 10
    have h2 : 214 ^ 3 ≤ n ^ 3 := Nat.pow_le_pow_left hn 3
    norm_num at h1 h2
    omega
  -- `c₄ ≥ F`, since `n > F³` and the low digits are less than `F²`
  have hc4F : F ≤ c₄ := by
    have h1 : c₁ * F + 1 ≤ F ^ 2 := by
      have : c₁ * F < F * F := mul_lt_mul_of_pos_right hc1 (by omega)
      have hFF : F * F = F ^ 2 := by ring
      omega
    have h2 : (F - 1) * F ^ 2 < c₄ * F ^ 2 := by
      have hF3 : (F - 1) * F ^ 2 + F ^ 2 = F ^ 3 := by
        have : (F - 1) + 1 = F := by omega
        calc (F - 1) * F ^ 2 + F ^ 2 = ((F - 1) + 1) * F ^ 2 := by ring
        _ = F * F ^ 2 := by rw [this]
        _ = F ^ 3 := by ring
      omega
    have := lt_of_mul_lt_mul_right h2 (Nat.zero_le (F ^ 2))
    omega
  constructor
  · -- prime ⟹ (1) ∧ (2)
    intro hprime
    constructor
    · exact prime_kp_disc_not_square hF6 hc4F hrep hprime
    · -- (2): a prime has no nontrivial factor at all
      rintro ⟨x, _, hdvd, hgt, hlt⟩
      set z := x * (F : ℤ) + 1 with hz
      have hz0 : 0 ≤ z := by omega
      set m := z.toNat with hm
      have hzm : (m : ℤ) = z := Int.toNat_of_nonneg hz0
      have hmn : m ∣ n := by
        have : (m : ℤ) ∣ (n : ℤ) := hzm ▸ hdvd
        exact_mod_cast this
      rcases (Nat.Prime.eq_one_or_self_of_dvd hprime m hmn) with h1 | h1
      · rw [h1] at hzm
        omega
      · rw [h1] at hzm
        omega
  · -- (1) ∧ (2) ⟹ prime
    rintro ⟨h1, h2⟩
    by_contra hcomp
    obtain ⟨a₁, a₂, t, ha₁, ha₁₂, hfact, ht6, ht, hprod, h3aF, htF3⟩ :=
      kp_small_factor hn hsplit a ha hunit hlo hc1 hrep h1 hcomp
    -- the ℤ identity (4.7)/(4.8): `DF − c₄v = a₁(uF − c₁v) + (a₁² − t)v`
    have htz : ((a₁ : ℤ) + a₂) = c₁ + t * F := by exact_mod_cast ht
    have hpz : ((a₁ : ℤ) * a₂) + t = c₄ := by exact_mod_cast hprod
    have h47z : (a₁ : ℤ) * c₁ + a₁ * t * F = a₁ ^ 2 + c₄ - t := by
      linear_combination (-(a₁ : ℤ)) * htz + hpz
    set D : ℕ := a₁ * u + a₁ * t * v with hD
    set E : ℤ := (D : ℤ) * F - (c₄ : ℤ) * v with hEdef
    have hEid : E = (a₁ : ℤ) * ((u : ℤ) * F - c₁ * v)
        + ((a₁ : ℤ) ^ 2 - t) * v := by
      rw [hEdef, hD]
      push_cast
      linear_combination (v : ℤ) * h47z
    -- absolute-value bounds
    set W : ℕ := ((u : ℤ) * F - c₁ * v).natAbs with hW
    set Y : ℕ := ((a₁ : ℤ) ^ 2 - t).natAbs with hY
    have hWn : W ^ 2 * F ^ 2 ≤ n := by
      have hcast : ((W : ℤ)) ^ 2 = ((u : ℤ) * F - c₁ * v) ^ 2 := by
        rw [hW, Int.natCast_natAbs, sq_abs]
      have h1 : ((W : ℤ)) ^ 2 * (F : ℤ) ^ 2 ≤ (n : ℤ) := by
        rw [hcast]
        exact happrox
      exact_mod_cast h1
    -- Term 1: `3·(a₁W) ≤ F` from `9(a₁W)²F⁸ ≤ n³ ≤ F¹⁰`
    have h9a : 9 * a₁ ^ 2 * F ^ 6 < n ^ 2 := by
      have h := Nat.pow_lt_pow_left h3aF two_ne_zero
      calc 9 * a₁ ^ 2 * F ^ 6 = (3 * a₁ * F ^ 3) ^ 2 := by ring
      _ < n ^ 2 := h
    have hX3 : 3 * (a₁ * W) ≤ F := by
      have hXsq : (3 * (a₁ * W)) ^ 2 * F ^ 8 ≤ F ^ 2 * F ^ 8 := by
        calc (3 * (a₁ * W)) ^ 2 * F ^ 8
            = (9 * a₁ ^ 2 * F ^ 6) * (W ^ 2 * F ^ 2) := by ring
        _ ≤ n ^ 2 * n := Nat.mul_le_mul h9a.le hWn
        _ = n ^ 3 := by ring
        _ ≤ F ^ 10 := hlo
        _ = F ^ 2 * F ^ 8 := by ring
      have h2 : (3 * (a₁ * W)) ^ 2 ≤ F ^ 2 :=
        Nat.le_of_mul_le_mul_right hXsq (by positivity)
      exact (Nat.pow_le_pow_iff_left two_ne_zero).mp h2
    -- Term 2: `6·(Yv) < F` from `36(Yv)²F¹²n < F¹⁴n`
    have hY6 : 6 * Y * F ^ 6 ≤ n ^ 2 := by
      rcases le_total (t : ℤ) ((a₁ : ℤ) ^ 2) with hcase | hcase
      · have hYa : Y ≤ a₁ ^ 2 := by
          have hz : ((Y : ℕ) : ℤ) = (a₁ : ℤ) ^ 2 - t := by
            rw [hY]
            exact Int.natAbs_of_nonneg (by linarith)
          have h1 : ((Y : ℕ) : ℤ) ≤ ((a₁ ^ 2 : ℕ) : ℤ) := by
            rw [hz]
            push_cast
            linarith
          exact_mod_cast h1
        calc 6 * Y * F ^ 6 ≤ 9 * a₁ ^ 2 * F ^ 6 :=
              Nat.mul_le_mul_right (F ^ 6)
                (Nat.mul_le_mul (by norm_num : (6 : ℕ) ≤ 9) hYa)
        _ ≤ n ^ 2 := h9a.le
      · have hYt : Y ≤ t := by
          have hz : ((Y : ℕ) : ℤ) = (t : ℤ) - (a₁ : ℤ) ^ 2 := by
            rw [hY, ← Int.natAbs_neg, neg_sub]
            exact Int.natAbs_of_nonneg (by linarith)
          have h1 : ((Y : ℕ) : ℤ) ≤ ((t : ℕ) : ℤ) := by
            rw [hz]
            have : (0 : ℤ) ≤ (a₁ : ℤ) ^ 2 := by positivity
            linarith
          exact_mod_cast h1
        have h6t : 6 * Y ≤ t * t := by
          calc 6 * Y ≤ 6 * t := Nat.mul_le_mul_left 6 hYt
          _ ≤ t * t := Nat.mul_le_mul_right t ht6
        calc 6 * Y * F ^ 6 ≤ t * t * F ^ 6 :=
              Nat.mul_le_mul_right _ h6t
        _ = (t * F ^ 3) ^ 2 := by ring
        _ ≤ n ^ 2 := Nat.pow_le_pow_left htF3.le 2
    have hYv : 6 * (Y * v) < F := by
      have hbig : (6 * (Y * v)) ^ 2 * (F ^ 12 * n) < F ^ 2 * (F ^ 12 * n) := by
        calc (6 * (Y * v)) ^ 2 * (F ^ 12 * n)
            = (6 * Y * F ^ 6) ^ 2 * (v ^ 2 * n) := by ring
        _ ≤ (n ^ 2) ^ 2 * (v ^ 2 * n) :=
            Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hY6 2)
        _ < (n ^ 2) ^ 2 * F ^ 4 :=
            mul_lt_mul_of_pos_left hv2 (by positivity)
        _ = n ^ 3 * (n * F ^ 4) := by ring
        _ ≤ F ^ 10 * (n * F ^ 4) := Nat.mul_le_mul_right _ hlo
        _ = F ^ 2 * (F ^ 12 * n) := by ring
      have h2 : (6 * (Y * v)) ^ 2 < F ^ 2 :=
        lt_of_mul_lt_mul_right hbig (Nat.zero_le _)
      exact (Nat.pow_lt_pow_iff_left two_ne_zero).mp h2
    -- the nearest-integer bound: `2|E| < F`
    have hEabs : E.natAbs ≤ a₁ * W + Y * v := by
      calc E.natAbs
          = ((a₁ : ℤ) * ((u : ℤ) * F - c₁ * v)
              + ((a₁ : ℤ) ^ 2 - t) * v).natAbs := by rw [hEid]
      _ ≤ ((a₁ : ℤ) * ((u : ℤ) * F - c₁ * v)).natAbs
            + (((a₁ : ℤ) ^ 2 - t) * v).natAbs := Int.natAbs_add_le _ _
      _ = a₁ * W + Y * v := by
          rw [Int.natAbs_mul, Int.natAbs_mul, hW, hY]
          simp [Int.natAbs_natCast]
    have h2E : 2 * E.natAbs < F := by
      have h6 : 6 * E.natAbs < 3 * F := by
        have := hEabs
        omega
      omega
    -- so `D` is the nearest integer to `c₄v/F`, hence `D = d`
    have hEbound : 2 * |E| < (F : ℤ) := by
      have h1 : ((2 * E.natAbs : ℕ) : ℤ) < ((F : ℕ) : ℤ) := by exact_mod_cast h2E
      rw [← Int.natCast_natAbs]
      push_cast at h1 ⊢
      linarith
    have hlt1 : 2 * c₄ * v < 2 * D * F + F := by
      have hz : -(F : ℤ) < 2 * E := by
        have := neg_abs_le E
        linarith
      rw [hEdef] at hz
      have h1 : ((2 * c₄ * v : ℕ) : ℤ) < ((2 * D * F + F : ℕ) : ℤ) := by
        push_cast
        linarith
      exact_mod_cast h1
    have hlt2 : 2 * D * F < 2 * c₄ * v + F := by
      have hz : 2 * E < (F : ℤ) := by
        have := le_abs_self E
        linarith
      rw [hEdef] at hz
      have h1 : ((2 * D * F : ℕ) : ℤ) < ((2 * c₄ * v + F : ℕ) : ℤ) := by
        push_cast
        linarith
      exact_mod_cast h1
    have hDd : D = d := by
      have hdm := Nat.div_add_mod (2 * c₄ * v + F) (2 * F)
      rw [← hd] at hdm
      set M := (2 * c₄ * v + F) % (2 * F) with hM
      have hmodlt : M < 2 * F := Nat.mod_lt _ (by omega)
      -- hdm : 2 * F * d + M = 2 * c₄ * v + F
      have hDle : D ≤ d := by
        have h1 : 2 * F * D < 2 * F * (d + 1) := by
          calc 2 * F * D = 2 * D * F := by ring
          _ < 2 * c₄ * v + F := hlt2
          _ = 2 * F * d + M := hdm.symm
          _ < 2 * F * d + 2 * F := by omega
          _ = 2 * F * (d + 1) := by ring
        have := Nat.lt_of_mul_lt_mul_left h1
        omega
      have hdle : d ≤ D := by
        have h1 : 2 * F * d < 2 * F * (D + 1) := by
          calc 2 * F * d ≤ 2 * F * d + M := by omega
          _ = 2 * c₄ * v + F := hdm
          _ < 2 * D * F + F + F := by omega
          _ = 2 * F * (D + 1) := by ring
        have := Nat.lt_of_mul_lt_mul_left h1
        omega
      omega
    -- `a₁` is an integer root of the cubic, and `a₁F + 1` a nontrivial
    -- factor: condition (2) is refuted
    apply h2
    refine ⟨(a₁ : ℤ), ?_, ?_, ?_, ?_⟩
    · have hdz : (d : ℤ) = (a₁ : ℤ) * u + a₁ * t * v := by
        rw [← hDd, hD]
        push_cast
        ring
      linear_combination (-(a₁ : ℤ) * v) * h47z + (-(F : ℤ) * a₁ - 1) * hdz
    · refine ⟨(a₂ : ℤ) * F + 1, ?_⟩
      have hfz : (n : ℤ) = ((a₁ : ℤ) * F + 1) * ((a₂ : ℤ) * F + 1) := by
        exact_mod_cast hfact
      exact hfz
    · have ha₁z : (1 : ℤ) ≤ (a₁ : ℤ) := by exact_mod_cast ha₁
      have hFz : (1 : ℤ) ≤ (F : ℤ) := by exact_mod_cast (by omega : 1 ≤ F)
      have h11 : (1 : ℤ) * 1 ≤ (a₁ : ℤ) * F :=
        mul_le_mul ha₁z hFz zero_le_one (by linarith)
      linarith
    · have h1 : a₁ * F + 1 < n := by
        have h2 : 2 ≤ a₂ * F + 1 := by
          have : 1 * 1 ≤ a₂ * F := Nat.mul_le_mul (by omega) (by omega)
          omega
        have h3 : (a₁ * F + 1) * 1 < (a₁ * F + 1) * (a₂ * F + 1) :=
          mul_lt_mul_of_pos_left (by omega) (by omega)
        rw [mul_one] at h3
        omega
      have : ((a₁ * F + 1 : ℕ) : ℤ) < ((n : ℕ) : ℤ) := by exact_mod_cast h1
      push_cast at this
      omega


/-- **Konyagin–Pomerance, divisor-bound form**: same setting as
`theorem_4_1_6`, but with condition (2) replaced by the bare bounded
divisor condition its proof actually delivers — no approximation pair
`(u, v)` or cubic needed.  `n` is prime iff (1) the six shifted
discriminants are non-squares and (2') `n` has no factor `xF + 1` with
`0 < x` and `3xF³ < n` (a search range of size about `n^(1/10)`).  This
is the form a checker can discharge by direct scan; the cubic of
condition (2) is the sub-linear refinement of that scan. -/
theorem theorem_4_1_6' {n F R c₁ c₄ : ℕ} (hn : 214 ≤ n)
    (hsplit : n - 1 = F * R) (a : ZMod n) (ha : a ^ (n - 1) = 1)
    (hunit : ∀ q : ℕ, q.Prime → q ∣ F → IsUnit (a ^ ((n - 1) / q) - 1))
    (hhi : F ^ 3 < n) (hlo : n ^ 3 ≤ F ^ 10)
    (hc1 : c₁ < F) (hrep : n = c₄ * F ^ 2 + c₁ * F + 1) :
    n.Prime ↔
      ((∀ t : ℕ, t ≤ 5 →
          ¬IsSquare (((c₁ : ℤ) + t * F) ^ 2 + 4 * t - 4 * c₄)) ∧
        ¬∃ x : ℕ, 0 < x ∧ 3 * x * F ^ 3 < n ∧ (x * F + 1) ∣ n) := by
  have hn1 : 1 < n := by omega
  have hF6 : 6 ≤ F := by
    by_contra h
    have hF5 : F ≤ 5 := by omega
    have h1 : F ^ 10 ≤ 5 ^ 10 := Nat.pow_le_pow_left hF5 10
    have h2 : 214 ^ 3 ≤ n ^ 3 := Nat.pow_le_pow_left hn 3
    norm_num at h1 h2
    omega
  have hc4F : F ≤ c₄ := by
    have h1 : c₁ * F + 1 ≤ F ^ 2 := by
      have : c₁ * F < F * F := mul_lt_mul_of_pos_right hc1 (by omega)
      have hFF : F * F = F ^ 2 := by ring
      omega
    have h2 : (F - 1) * F ^ 2 < c₄ * F ^ 2 := by
      have hF3 : (F - 1) * F ^ 2 + F ^ 2 = F ^ 3 := by
        have : (F - 1) + 1 = F := by omega
        calc (F - 1) * F ^ 2 + F ^ 2 = ((F - 1) + 1) * F ^ 2 := by ring
        _ = F * F ^ 2 := by rw [this]
        _ = F ^ 3 := by ring
      omega
    have := lt_of_mul_lt_mul_right h2 (Nat.zero_le (F ^ 2))
    omega
  constructor
  · intro hprime
    refine ⟨prime_kp_disc_not_square hF6 hc4F hrep hprime, ?_⟩
    rintro ⟨x, hx, hxF, hdvd⟩
    -- `xF + 1` would be a nontrivial factor
    have hne1 : x * F + 1 ≠ 1 := by
      have : 1 * 1 ≤ x * F := Nat.mul_le_mul hx (by omega)
      omega
    have hlt : x * F + 1 < n := by
      have h1 : x * F ≤ x * F ^ 3 := Nat.mul_le_mul_left x
        (Nat.le_self_pow three_ne_zero F)
      have h2 : x * F ^ 3 ≤ 3 * x * F ^ 3 := by
        have := Nat.mul_le_mul_right (x * F ^ 3) (by omega : 1 ≤ 3)
        calc x * F ^ 3 = 1 * (x * F ^ 3) := (one_mul _).symm
        _ ≤ 3 * (x * F ^ 3) := this
        _ = 3 * x * F ^ 3 := by ring
      have h0 : 1 * 1 ≤ x * F ^ 3 :=
        Nat.mul_le_mul hx (Nat.one_le_pow _ _ (by omega))
      have hk : 3 * x * F ^ 3 = 3 * (x * F ^ 3) := by ring
      omega
    rcases (Nat.Prime.eq_one_or_self_of_dvd hprime _ hdvd) with h | h <;> omega
  · rintro ⟨h1, h2⟩
    by_contra hcomp
    obtain ⟨a₁, a₂, t, ha₁, ha₁₂, hfact, ht6, ht, hprod, h3aF, htF3⟩ :=
      kp_small_factor hn hsplit a ha hunit hlo hc1 hrep h1 hcomp
    exact h2 ⟨a₁, by omega, h3aF, ⟨a₂ * F + 1, hfact⟩⟩

end CP

end Azurite

-- ── Tests ────────────────────────────────────────────────────────────────────

/-! A worked Konyagin–Pomerance certificate: `223` is prime via
`222 = 6·37` — `F = 6` lies between `223^(3/10) ≈ 5.06` and
`223^(1/3) ≈ 6.06`, below the reach of both Pocklington's corollary and
BLS.  Witness `3` (inverses `111` and `87` for the two unit conditions);
digits `c₄ = 6`, `c₁ = 1`; approximation `u/v = 0/1` to `1/6` with
`d = 1`.  The six shifted discriminants `−23, 29, 153, 349, 617, 957`
are non-squares, and the cubic `x³ − x² − 1` has no positive integer
root. -/

open Azurite.CP in
set_option maxRecDepth 8192 in
example : Nat.Prime 223 := by
  refine (theorem_4_1_6 (F := 6) (R := 37) (c₁ := 1) (c₄ := 6) (u := 0)
    (v := 1) (d := 1) (by norm_num) (by norm_num) (3 : ZMod 223) (by decide)
    ?_ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)).mpr ⟨?_, ?_⟩
  · intro q hq hqF
    have hq23 : q = 2 ∨ q = 3 := by
      have hle : q ≤ 6 := Nat.le_of_dvd (by norm_num) hqF
      interval_cases q <;> revert hqF hq <;> decide
    rcases hq23 with rfl | rfl
    · exact IsUnit.of_mul_eq_one (111 : ZMod 223) (by decide)
    · exact IsUnit.of_mul_eq_one (87 : ZMod 223) (by decide)
  · intro t ht
    interval_cases t
    · exact _root_.not_isSquare_of_neg (by norm_num)
    · norm_num
      exact_mod_cast not_isSquare_intCast_of_lt_of_lt (k := 5) (by norm_num)
        (by norm_num)
    · norm_num
      exact_mod_cast not_isSquare_intCast_of_lt_of_lt (k := 12) (by norm_num)
        (by norm_num)
    · norm_num
      exact_mod_cast not_isSquare_intCast_of_lt_of_lt (k := 18) (by norm_num)
        (by norm_num)
    · norm_num
      exact_mod_cast not_isSquare_intCast_of_lt_of_lt (k := 24) (by norm_num)
        (by norm_num)
    · norm_num
      exact_mod_cast not_isSquare_intCast_of_lt_of_lt (k := 30) (by norm_num)
        (by norm_num)
  · rintro ⟨x, hroot, hdvd, hgt, hlt⟩
    norm_num at hroot
    have hx1 : 1 ≤ x := by omega
    rcases eq_or_lt_of_le hx1 with rfl | hx2
    · norm_num at hroot
    · have hx2' : 2 ≤ x := hx2
      nlinarith [hroot, hx2', sq_nonneg (x - 2),
        mul_nonneg (by linarith : (0 : ℤ) ≤ x - 2) (sq_nonneg x)]
