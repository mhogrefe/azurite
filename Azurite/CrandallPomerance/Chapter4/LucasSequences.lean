/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

/-
  Crandall–Pomerance §4.2: Lucas sequences.

  With `a, b ∈ ℤ`, `f(x) = x² − ax + b` and `Δ = a² − 4b` (4.12), the
  book defines (4.13)

    `U_k = (x^k − (a−x)^k) / (x − (a−x))  (mod f(x))`,
    `V_k = x^k + (a−x)^k                  (mod f(x))`,

  and remarks that `U_k, V_k` are integers (degree-0 mod `f`).  We take
  the equivalent recurrence as the DEFINITION — `U_0 = 0`, `U_1 = 1`,
  `V_0 = 2`, `V_1 = a`, and `W_{k+2} = a·W_{k+1} − b·W_k` — so that the
  sequences are manifestly integer-valued and computable, and prove the
  book's characterization as a theorem: for ANY commutative ring and
  any `α, β` with `α + β = a` and `α·β = b`,

    `U_k · (α − β) = α^k − β^k`  and  `V_k = α^k + β^k`,

  specialized to `ℤ[x]/(f)` (Mathlib's `AdjoinRoot`) with `α` the image
  of `x` and `β` the image of `a − x` — exactly (4.13), with the
  division realized as the exact multiplicative identity.  The
  discriminant enters through `(α − β)² = Δ`.

  Definition 4.2.1: for `gcd(n, 2bΔ) = 1`, the RANK OF APPEARANCE
  `r_f(n)` is the least positive `r` with `U_r ≡ 0 (mod n)`.  We define
  it unconditionally as an `sInf` (with value `0` when no such `r`
  exists); the gcd hypothesis is what will guarantee existence.

  Fibonacci (`a = 1, b = −1`, where `U` = Fibonacci and `V` = the Lucas
  numbers) and `a = 3, b = 2` (roots `2, 1`, where `U_k = 2^k − 1`)
  serve as test instances.
-/
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Order.Lattice.Nat

namespace Azurite

namespace CP

/-- The Lucas sequence `U_k` for `f(x) = x² − ax + b`: `U_0 = 0`,
`U_1 = 1`, `U_{k+2} = a·U_{k+1} − b·U_k`. -/
def lucasU (a b : ℤ) : ℕ → ℤ
  | 0 => 0
  | 1 => 1
  | k + 2 => a * lucasU a b (k + 1) - b * lucasU a b k

/-- The companion Lucas sequence `V_k`: `V_0 = 2`, `V_1 = a`,
`V_{k+2} = a·V_{k+1} − b·V_k`. -/
def lucasV (a b : ℤ) : ℕ → ℤ
  | 0 => 2
  | 1 => a
  | k + 2 => a * lucasV a b (k + 1) - b * lucasV a b k

@[simp] theorem lucasU_zero (a b : ℤ) : lucasU a b 0 = 0 := rfl
@[simp] theorem lucasU_one (a b : ℤ) : lucasU a b 1 = 1 := rfl
theorem lucasU_add_two (a b : ℤ) (k : ℕ) :
    lucasU a b (k + 2) = a * lucasU a b (k + 1) - b * lucasU a b k := rfl

@[simp] theorem lucasV_zero (a b : ℤ) : lucasV a b 0 = 2 := rfl
@[simp] theorem lucasV_one (a b : ℤ) : lucasV a b 1 = a := rfl
theorem lucasV_add_two (a b : ℤ) (k : ℕ) :
    lucasV a b (k + 2) = a * lucasV a b (k + 1) - b * lucasV a b k := rfl

section GenericRing

variable {R : Type*} [CommRing R] {a b : ℤ} {α β : R}

/-- The discriminant identity: if `α + β = a` and `αβ = b`, then
`(α − β)² = Δ = a² − 4b`. -/
theorem sub_sq_eq_disc (hs : α + β = (a : R)) (hp : α * β = (b : R)) :
    (α - β) ^ 2 = ((a ^ 2 - 4 * b : ℤ) : R) := by
  push_cast
  linear_combination (α + β + (a : R)) * hs - 4 * hp

/-- **Binet in an arbitrary commutative ring** (`V` half): if
`α + β = a` and `αβ = b`, then `V_k = α^k + β^k`. -/
theorem lucasV_spec (hs : α + β = (a : R)) (hp : α * β = (b : R)) :
    ∀ k : ℕ, ((lucasV a b k : ℤ) : R) = α ^ k + β ^ k := by
  intro k
  induction k using Nat.twoStepInduction with
  | zero =>
    simp only [lucasV_zero]
    push_cast
    ring
  | one =>
    simp only [lucasV_one, pow_one]
    exact hs.symm
  | more k ih1 ih2 =>
    rw [lucasV_add_two]
    push_cast
    rw [ih1, ih2]
    linear_combination (-(α ^ (k + 1) + β ^ (k + 1))) * hs
      + (α ^ k + β ^ k) * hp

/-- **Binet in an arbitrary commutative ring** (`U` half), in exact
multiplicative form: if `α + β = a` and `αβ = b`, then
`U_k · (α − β) = α^k − β^k`. -/
theorem lucasU_spec (hs : α + β = (a : R)) (hp : α * β = (b : R)) :
    ∀ k : ℕ, ((lucasU a b k : ℤ) : R) * (α - β) = α ^ k - β ^ k := by
  intro k
  induction k using Nat.twoStepInduction with
  | zero =>
    simp only [lucasU_zero]
    push_cast
    ring
  | one =>
    simp only [lucasU_one, pow_one]
    push_cast
    ring
  | more k ih1 ih2 =>
    rw [lucasU_add_two]
    push_cast
    linear_combination (a : R) * ih2 - (b : R) * ih1
      - (α ^ (k + 1) - β ^ (k + 1)) * hs + (α ^ k - β ^ k) * hp

end GenericRing

section AdjoinRoot

open Polynomial

variable (a b : ℤ)

/-- The book's `f(x) = x² − ax + b` (4.12). -/
noncomputable def lucasPoly : ℤ[X] := X ^ 2 - C a * X + C b

/-- The image of `x` in `ℤ[x]/(f)`. -/
noncomputable def lucasRoot : AdjoinRoot (lucasPoly a b) :=
  AdjoinRoot.root _

/-- In `ℤ[x]/(f)`, the images of `x` and `a − x` sum to `a`. -/
theorem lucasRoot_add (a b : ℤ) :
    lucasRoot a b + ((a : AdjoinRoot (lucasPoly a b)) - lucasRoot a b)
      = (a : AdjoinRoot (lucasPoly a b)) := by
  ring

/-- In `ℤ[x]/(f)`, the images of `x` and `a − x` multiply to `b`
(the content of `x·(a − x) ≡ b (mod x² − ax + b)`). -/
theorem lucasRoot_mul (a b : ℤ) :
    lucasRoot a b * ((a : AdjoinRoot (lucasPoly a b)) - lucasRoot a b)
      = (b : AdjoinRoot (lucasPoly a b)) := by
  have h0 : AdjoinRoot.mk (lucasPoly a b) (X ^ 2 - C a * X + C b) = 0 :=
    AdjoinRoot.mk_self
  simp only [map_add, map_sub, map_pow, map_mul, AdjoinRoot.mk_X,
    eq_intCast, map_intCast] at h0
  rw [show AdjoinRoot.root (lucasPoly a b) = lucasRoot a b from rfl] at h0
  linear_combination -h0

/-- **The book's (4.13), `V` half**: in `ℤ[x]/(f)`,
`V_k = x^k + (a − x)^k`. -/
theorem lucasV_eq_adjoinRoot (k : ℕ) :
    ((lucasV a b k : ℤ) : AdjoinRoot (lucasPoly a b))
      = (lucasRoot a b) ^ k
        + ((a : AdjoinRoot (lucasPoly a b)) - lucasRoot a b) ^ k :=
  lucasV_spec (lucasRoot_add a b) (lucasRoot_mul a b) k

/-- **The book's (4.13), `U` half**, with the division by `x − (a − x)`
realized as an exact multiplicative identity: in `ℤ[x]/(f)`,
`U_k · (x − (a − x)) = x^k − (a − x)^k`. -/
theorem lucasU_mul_adjoinRoot (k : ℕ) :
    ((lucasU a b k : ℤ) : AdjoinRoot (lucasPoly a b))
        * (lucasRoot a b
          - ((a : AdjoinRoot (lucasPoly a b)) - lucasRoot a b))
      = (lucasRoot a b) ^ k
        - ((a : AdjoinRoot (lucasPoly a b)) - lucasRoot a b) ^ k :=
  lucasU_spec (lucasRoot_add a b) (lucasRoot_mul a b) k

end AdjoinRoot

/-- **Rank of appearance** (Crandall–Pomerance Definition 4.2.1): the
least positive `r` with `U_r ≡ 0 (mod n)` — as an `sInf`, so the value
is `0` when no such `r` exists.  Existence is guaranteed when
`gcd(n, 2bΔ) = 1` (proven later in the chapter). -/
noncomputable def rankApp (a b : ℤ) (n : ℕ) : ℕ :=
  sInf {r : ℕ | 0 < r ∧ (n : ℤ) ∣ lucasU a b r}

/-- When some positive rank exists, the rank of appearance is positive
and `n ∣ U_{r_f(n)}`. -/
theorem rankApp_mem {a b : ℤ} {n : ℕ}
    (h : ∃ r : ℕ, 0 < r ∧ (n : ℤ) ∣ lucasU a b r) :
    0 < rankApp a b n ∧ (n : ℤ) ∣ lucasU a b (rankApp a b n) :=
  Nat.sInf_mem h

/-- Minimality: no smaller positive index works. -/
theorem rankApp_min {a b : ℤ} {n r : ℕ} (hr : 0 < r)
    (hdvd : (n : ℤ) ∣ lucasU a b r) : rankApp a b n ≤ r :=
  Nat.sInf_le ⟨hr, hdvd⟩

/-! ### The addition formula and the divisibility-sequence property -/

theorem lucasU_two (a b : ℤ) : lucasU a b 2 = a := by
  rw [show 2 = 0 + 2 from rfl, lucasU_add_two]
  simp

/-- The addition formula
`U_{m+1+n} = U_{m+1}·U_{n+1} − b·U_m·U_n`. -/
theorem lucasU_addition (a b : ℤ) (m n : ℕ) :
    lucasU a b (m + 1 + n) = lucasU a b (m + 1) * lucasU a b (n + 1)
      - b * lucasU a b m * lucasU a b n := by
  induction n using Nat.twoStepInduction generalizing m with
  | zero => simp
  | one =>
    rw [show m + 1 + 1 = m + 2 from rfl, lucasU_add_two,
      show (1 : ℕ) + 1 = 2 from rfl, lucasU_two]
    simp only [lucasU_one]
    ring
  | more n ih1 ih2 =>
    rw [show m + 1 + (n + 2) = (m + 1 + n) + 2 by ring, lucasU_add_two,
      ih1 m, show m + 1 + n + 1 = m + 1 + (n + 1) by ring, ih2 m,
      show n + 1 + 1 = n + 2 from rfl, show n + 2 + 1 = (n + 1) + 2 from rfl,
      lucasU_add_two a b (n + 1), lucasU_add_two a b n]
    ring

/-- **`(U_k)` is a divisibility sequence**: `k ∣ j → U_k ∣ U_j`
(allowing `U_k = U_j = 0`). -/
theorem lucasU_dvd_lucasU (a b : ℤ) {k j : ℕ} (h : k ∣ j) :
    lucasU a b k ∣ lucasU a b j := by
  obtain ⟨m, rfl⟩ := h
  induction m with
  | zero => simp
  | succ m ih =>
    rcases Nat.eq_zero_or_pos (k * m) with h0 | hpos
    · rw [Nat.mul_succ, h0, Nat.zero_add]
    · obtain ⟨t, ht⟩ : ∃ t, k * m = t + 1 := ⟨k * m - 1, by omega⟩
      rw [Nat.mul_succ, ht, lucasU_addition]
      refine dvd_sub ?_ ?_
      · exact Dvd.dvd.mul_right (by rw [← ht]; exact ih) _
      · exact Dvd.dvd.mul_left (dvd_refl _) _

/-- A common divisor of two consecutive `U`'s that is coprime to `b`
is a unit (descend the recurrence to `U_1 = 1`). -/
theorem isUnit_of_dvd_lucasU_consecutive {a b d : ℤ}
    (hb : IsCoprime d b) :
    ∀ k : ℕ, d ∣ lucasU a b k → d ∣ lucasU a b (k + 1) → IsUnit d := by
  intro k
  induction k with
  | zero =>
    intro _ h1
    rw [lucasU_one] at h1
    exact isUnit_of_dvd_one h1
  | succ k ih =>
    intro hk1 hk2
    have hbU : d ∣ b * lucasU a b k := by
      have heq : b * lucasU a b k
          = a * lucasU a b (k + 1) - lucasU a b (k + 2) := by
        rw [lucasU_add_two]
        ring
      rw [heq]
      exact dvd_sub (hk1.mul_left a) hk2
    exact ih (hb.dvd_of_dvd_mul_left hbU) hk1

/-- **The rank-divisibility characterization** (the book's remark after
Definition 4.2.1): if `gcd(n, b) = 1` and some positive rank exists,
then `U_j ≡ 0 (mod n)` if and only if `r_f(n) ∣ j`. -/
theorem dvd_lucasU_iff_rankApp_dvd {a b : ℤ} {n : ℕ}
    (hb : IsCoprime (n : ℤ) b)
    (hex : ∃ r : ℕ, 0 < r ∧ (n : ℤ) ∣ lucasU a b r) (j : ℕ) :
    (n : ℤ) ∣ lucasU a b j ↔ rankApp a b n ∣ j := by
  obtain ⟨hrpos, hrdvd⟩ := rankApp_mem hex
  set r := rankApp a b n with hr
  constructor
  · intro hj
    by_contra hnd
    -- write `j = r·q + s` with `0 < s < r`
    have hdm := Nat.div_add_mod j r
    set q := j / r with hq
    set s := j % r with hs
    have hslt : s < r := Nat.mod_lt _ hrpos
    have hspos : 0 < s := by
      rcases Nat.eq_zero_or_pos s with h0 | h
      · exact absurd (Nat.dvd_of_mod_eq_zero h0) hnd
      · exact h
    rcases Nat.eq_zero_or_pos q with hq0 | hqpos
    · -- `j = s < r` directly contradicts minimality
      rw [hq0, Nat.mul_zero, Nat.zero_add] at hdm
      have := rankApp_min hspos (hdm ▸ hj)
      omega
    -- `A := r·q ≥ 1`; the addition formula peels off `U_A`
    obtain ⟨t, ht⟩ : ∃ t, r * q = t + 1 :=
      ⟨r * q - 1, by have := Nat.mul_le_mul hrpos hqpos; omega⟩
    have hA : (n : ℤ) ∣ lucasU a b (r * q) :=
      hrdvd.trans (lucasU_dvd_lucasU a b ⟨q, rfl⟩)
    have hadd := lucasU_addition a b t s
    rw [← ht, hdm] at hadd
    -- so `n ∣ b·U_t·U_s`
    have hbts : (n : ℤ) ∣ b * lucasU a b t * lucasU a b s := by
      have : b * lucasU a b t * lucasU a b s
          = lucasU a b (r * q) * lucasU a b (s + 1) - lucasU a b j := by
        rw [hadd]
        ring
      rw [this]
      exact dvd_sub (hA.mul_right _) hj
    -- `n` is coprime to `b` and to `U_t` (consecutive to `U_A ≡ 0`)
    have hUt : IsCoprime (n : ℤ) (lucasU a b t) := by
      rw [Int.isCoprime_iff_gcd_eq_one]
      by_contra hg
      have hgdvd1 : ((Int.gcd (n : ℤ) (lucasU a b t) : ℤ)) ∣ (n : ℤ) :=
        Int.gcd_dvd_left _ _
      have hgdvd2 : ((Int.gcd (n : ℤ) (lucasU a b t) : ℤ))
          ∣ lucasU a b t := Int.gcd_dvd_right _ _
      have hgb : IsCoprime ((Int.gcd (n : ℤ) (lucasU a b t) : ℤ)) b :=
        IsCoprime.of_isCoprime_of_dvd_left hb hgdvd1
      have hunit := isUnit_of_dvd_lucasU_consecutive hgb t hgdvd2
        (by rw [show t + 1 = r * q from ht.symm]
            exact hgdvd1.trans hA)
      rw [Int.isUnit_iff] at hunit
      rcases hunit with h1 | h1 <;> omega
    have hUs : (n : ℤ) ∣ lucasU a b s :=
      (hb.mul_right hUt).dvd_of_dvd_mul_left hbts
    have := rankApp_min hspos hUs
    omega
  · intro hrj
    exact hrdvd.trans (lucasU_dvd_lucasU a b hrj)

/-! ### `U`–`V` identities: the norm invariant, `V² − ΔU² = 4bᵐ`, and
the doubling formula -/

/-- `V_m = 2U_{m+1} − a·U_m`. -/
theorem lucasV_eq_two_mul_sub (a b : ℤ) (m : ℕ) :
    lucasV a b m = 2 * lucasU a b (m + 1) - a * lucasU a b m := by
  induction m using Nat.twoStepInduction with
  | zero => simp
  | one =>
    rw [lucasV_one, lucasU_one, lucasU_two]
    ring
  | more m ih1 ih2 =>
    rw [lucasV_add_two, ih1, ih2, show m + 2 + 1 = (m + 1) + 2 from rfl,
      lucasU_add_two a b (m + 1), lucasU_add_two a b m]
    ring

/-- The norm invariant `U_{m+1}² − a·U_{m+1}U_m + b·U_m² = bᵐ` (the
norm of `α^m` in disguise). -/
theorem lucasU_norm (a b : ℤ) (m : ℕ) :
    lucasU a b (m + 1) ^ 2 - a * lucasU a b (m + 1) * lucasU a b m
      + b * lucasU a b m ^ 2 = b ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show m + 1 + 1 = m + 2 from rfl, lucasU_add_two, pow_succ]
    linear_combination b * ih

/-- **`V_m² − Δ·U_m² = 4bᵐ`** — the fundamental quadratic relation. -/
theorem lucasV_sq_sub_disc_mul_sq (a b : ℤ) (m : ℕ) :
    lucasV a b m ^ 2 - (a ^ 2 - 4 * b) * lucasU a b m ^ 2
      = 4 * b ^ m := by
  rw [lucasV_eq_two_mul_sub]
  linear_combination 4 * lucasU_norm a b m

/-- **The doubling formula** `U_{2m} = U_m · V_m`. -/
theorem lucasU_two_mul (a b : ℤ) (m : ℕ) :
    lucasU a b (2 * m) = lucasU a b m * lucasV a b m := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  obtain ⟨t, rfl⟩ : ∃ t, m = t + 1 := ⟨m - 1, by omega⟩
  rw [show 2 * (t + 1) = t + 1 + (t + 1) by ring, lucasU_addition,
    lucasV_eq_two_mul_sub, show t + 1 + 1 = t + 2 from rfl,
    lucasU_add_two]
  ring

/-- **The `V`-doubling formula** `V_{2m} = V_m² − 2bᵐ`. -/
theorem lucasV_two_mul (a b : ℤ) (m : ℕ) :
    lucasV a b (2 * m) = lucasV a b m ^ 2 - 2 * b ^ m := by
  have h1 := lucasU_addition a b m m
  have h2 := lucasU_two_mul a b m
  have h3 := lucasU_norm a b m
  rw [lucasV_eq_two_mul_sub, show 2 * m + 1 = m + 1 + m by ring, h1, h2,
    lucasV_eq_two_mul_sub a b m]
  linear_combination -2 * h3

end CP

end Azurite

-- ── Tests ────────────────────────────────────────────────────────────────────

/-! Sanity instances: `a = 1, b = −1` gives Fibonacci (`U`) and the
Lucas numbers (`V`); `a = 3, b = 2` has roots `2, 1`, so `U_k = 2^k − 1`
and `V_k = 2^k + 1`. -/

section Tests

open Azurite.CP

example : lucasU 1 (-1) 10 = 55 := by decide      -- fib 10
example : lucasV 1 (-1) 10 = 123 := by decide     -- Lucas number L₁₀
example : lucasU 3 2 5 = 31 := by decide          -- 2⁵ − 1
example : lucasV 3 2 5 = 33 := by decide          -- 2⁵ + 1
example : lucasU 1 (-1) 8 = 21 := by decide       -- fib 8 = 21 = 3·7

end Tests
