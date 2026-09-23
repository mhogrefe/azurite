/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.Algorithm.FastPow
import Mathlib.Data.Nat.Log

/-!
# Sliding-Window Exponentiation

This file implements **left-to-right sliding-window exponentiation** for any type with `Mul`,
`One`, and a `Square` operation. Like `fastPow` it uses `O(log n)` squarings, but it trades a
small precomputation for fewer multiplications, which pays off for larger exponents.

## Algorithm

Scan the exponent from the most-significant bit. Precompute the **odd** powers
`a^1, a^3, …, a^(2^w - 1)` (there are `2^(w-1)` of them). Then repeatedly:
- skip a `0` bit by squaring the running accumulator;
- at a `1` bit, grab the longest window of at most `w` bits that *ends* in a set bit (so its
  value `d` is odd), square the accumulator once per window bit, and multiply by the
  precomputed `a^d`.

Because each window ends in a set bit, its value is odd and indexes the odd-power table, and the
trailing zeros between windows become shared squarings of the accumulator — so the total is still
`O(log n)` squarings.

## Window width

`slidingWindowSize n` grows with the bit-length `b = bitLen n`. Increasing the window from `w` to
`w+1` doubles the precompute (`2^(w-1)` extra odd powers) but saves roughly `b / ((w+1)(w+2))`
multiplications, so it is worthwhile once `b > 2^(w-1)·(w+1)·(w+2)`. That gives the thresholds
`w = 1` for `b ≤ 6`, then `2, 3, 4, …` at `b = 24, 80, 240, …`.

For the exponent `3` (`b = 2`) this picks `w = 1`, and with the leading-window initialization the
computation is exactly `a²` then `a²·a` — **one squaring and one multiplication**.

## Main definitions

- `Azurite.slidingWindowSize n`: window width chosen from `bitLen n`.
- `Azurite.slidingWindowPow a n`: computes `a ^ n`.

The existing `fastPow` is intentionally kept; the two algorithms can be benchmarked against each
other.
-/

namespace Azurite

variable {M : Type _}

/-- Bit-length of `n`: the number of bits in its binary representation, so that
`2 ^ (bitLen n - 1) ≤ n < 2 ^ bitLen n` for `n ≥ 1`. (`Nat.size` is unavailable in this
toolchain; `Nat.log 2 n + 1` is the same for `n ≥ 1` and comes with usable lemmas.) -/
def bitLen (n : ℕ) : ℕ := Nat.log 2 n + 1

/-- Sliding-window width as a function of the exponent's bit-length `bitLen n`.

Thresholds come from balancing the `2^(w-1)`-entry odd-power precompute against the
`≈ b/(w+1)` window multiplies: widen from `w` to `w+1` once `b > 2^(w-1)·(w+1)·(w+2)`. -/
def slidingWindowSize (n : ℕ) : ℕ :=
  let b := bitLen n
  if b ≤ 6 then 1
  else if b ≤ 24 then 2
  else if b ≤ 80 then 3
  else if b ≤ 240 then 4
  else if b ≤ 672 then 5
  else if b ≤ 1792 then 6
  else if b ≤ 4608 then 7
  else 8

/-- Strip factors of `2`: `oddShift m = (t, d)` with `m = d * 2 ^ t` and `d` odd (for `m ≥ 1`).
`t` is the number of trailing zero bits and `d` the odd part. -/
def oddShift (m : ℕ) : ℕ × ℕ :=
  if m % 2 = 1 then (0, m)
  else if m = 0 then (0, 0)
  else
    let p := oddShift (m / 2)
    (p.1 + 1, p.2)
termination_by m
decreasing_by exact Nat.div_lt_self (by omega) (by omega)

/-- Square `x` exactly `k` times: `squareN x k = x ^ (2 ^ k)` in a monoid. -/
def squareN [Mul M] [Square M] (x : M) (k : ℕ) : M :=
  match k with
  | 0 => x
  | k + 1 => squareN (Square.square x) k

/-- Push `cur·asq, cur·asq², …` onto `acc`, `k` times (building successive odd powers). -/
def oddPowersGo [Mul M] (asq cur : M) (acc : Array M) (k : ℕ) : Array M :=
  match k with
  | 0 => acc
  | k + 1 =>
    let c := cur * asq
    oddPowersGo asq c (acc.push c) k

/-- Table of odd powers `#[a^1, a^3, …, a^(2^w - 1)]` (size `2^(w-1)`).
For `w ≤ 1` this is just `#[a]`, avoiding even the single squaring of `a`. -/
def mkOddPowerTable [Mul M] [Square M] (a : M) (w : ℕ) : Array M :=
  let k := 2 ^ (w - 1)
  if k ≤ 1 then #[a]
  else oddPowersGo (Square.square a) a #[a] (k - 1)

/-- Sliding-window main loop over a `len`-bit window of the exponent `n` (with `n < 2 ^ len`).
`result` holds `a ^ (high bits already consumed)`; the loop returns `result ^ (2 ^ len) * a ^ n`. -/
def swPowAux [Mul M] [Square M] (table : Array M) (w : ℕ) (result : M) (n len : ℕ) : M :=
  match len with
  | 0 => result
  | len + 1 =>
    if n < 2 ^ len then
      -- top bit (position `len`) is `0`: shift the accumulator up by squaring.
      swPowAux table w (Square.square result) n len
    else
      -- top bit is set: grab a window of at most `w` bits ending in a set bit.
      let L0 := min w (len + 1)
      let winRaw := n / 2 ^ (len + 1 - L0)
      let p := oddShift winRaw
      let L := max 1 (L0 - p.1)
      let d := p.2
      swPowAux table w (squareN result L * table.getD ((d - 1) / 2) result)
        (n % 2 ^ (len + 1 - L)) (len + 1 - L)
termination_by len
decreasing_by
  · omega
  · have h1 : 1 ≤ max 1 (min w (len + 1) - (oddShift (n / 2 ^ (len + 1 - min w (len + 1)))).1) :=
      le_max_left _ _
    omega

/-- **Sliding-window exponentiation.** Computes `a ^ n` using a window whose width grows with `n`
(`slidingWindowSize`), precomputing the `2^(w-1)` odd powers `a^1, …, a^(2^w-1)`.

The first (most-significant) window initializes the accumulator directly from the table, so no
squarings or multiplications are wasted on the identity. -/
def slidingWindowPow [Mul M] [One M] [Square M] (a : M) (n : ℕ) : M :=
  if n = 0 then 1
  else
    let w := slidingWindowSize n
    let table := mkOddPowerTable a w
    let s := bitLen n
    let L0 := min w s
    let winRaw := n / 2 ^ (s - L0)
    let p := oddShift winRaw
    let L := max 1 (L0 - p.1)
    let d := p.2
    swPowAux table w (table.getD ((d - 1) / 2) a) (n % 2 ^ (s - L)) (s - L)

-- ═══════════════════════════════════════════════════════════════════
-- Correctness
-- ═══════════════════════════════════════════════════════════════════

/-- Squaring `k` times raises to the `2 ^ k` power. -/
theorem squareN_eq [Monoid M] [Square M] (x : M) (k : ℕ) : squareN x k = x ^ (2 ^ k) := by
  induction k generalizing x with
  | zero => simp [squareN]
  | succ k ih =>
    rw [squareN, ih, Square.square_eq, ← pow_two, ← pow_mul]
    congr 1
    rw [pow_succ']

/-- `oddShift m = (t, d)` factors `m = d · 2 ^ t` with `d` odd, for `m ≥ 1`. -/
theorem oddShift_spec :
    ∀ m : ℕ, 1 ≤ m → m = (oddShift m).2 * 2 ^ (oddShift m).1 ∧ (oddShift m).2 % 2 = 1 := by
  intro m
  induction m using Nat.strongRecOn with
  | ind m ih =>
    intro hm
    rw [oddShift]
    by_cases h2 : m % 2 = 1
    · rw [ite_eq_left h2]
      exact ⟨by simp, h2⟩
    · rw [ite_eq_right h2, ite_eq_right (show m ≠ 0 by omega)]
      have hhalf : 1 ≤ m / 2 := by omega
      obtain ⟨heq, hodd⟩ := ih (m / 2) (by omega) hhalf
      refine ⟨?_, hodd⟩
      simp only [pow_succ, ← mul_assoc, ← heq]
      omega

/-- The `i`-th entry produced by `oddPowersGo asq cur acc k`: the prefix `acc` is copied, and
each subsequent entry is `cur · asq ^ (j+1)`. -/
theorem oddPowersGo_getD [Monoid M] (asq : M) :
    ∀ (k i : ℕ) (cur : M) (acc : Array M) (v : M), i < acc.size + k →
      (oddPowersGo asq cur acc k).getD i v =
        if h : i < acc.size then acc[i] else cur * asq ^ (i - acc.size + 1) := by
  intro k
  induction k with
  | zero =>
    intro i cur acc v hi
    rw [oddPowersGo, dite_eq_left (show i < acc.size by omega)]
    exact (Array.getElem_eq_getD v).symm
  | succ k ih =>
    intro i cur acc v hi
    rw [oddPowersGo]
    have hpush : (acc.push (cur * asq)).size = acc.size + 1 := by simp
    have hi' : i < (acc.push (cur * asq)).size + k := by rw [hpush]; omega
    rw [ih i (cur * asq) (acc.push (cur * asq)) v hi']
    simp only [hpush]
    by_cases hlt : i < acc.size
    · rw [dite_eq_left hlt, dite_eq_left (show i < acc.size + 1 by omega), Array.getElem_push_lt]
    · by_cases heq : i = acc.size
      · subst heq
        rw [dite_eq_right hlt, dite_eq_left (show acc.size < acc.size + 1 by omega), Array.getElem_push_eq]
        simp
      · rw [dite_eq_right hlt, dite_eq_right (show ¬ i < acc.size + 1 by omega), mul_assoc, ← pow_succ']
        congr 2
        omega

/-- Table lookup: `mkOddPowerTable a w` has `a ^ (2j+1)` at index `j` (for `j < 2^(w-1)`). -/
theorem mkOddPowerTable_getD [Monoid M] [Square M] (a : M) (w : ℕ) (j : ℕ)
    (hj : j < 2 ^ (w - 1)) (v : M) :
    (mkOddPowerTable a w).getD j v = a ^ (2 * j + 1) := by
  rw [mkOddPowerTable]
  by_cases hk : 2 ^ (w - 1) ≤ 1
  · rw [ite_eq_left hk]
    have hj0 : j = 0 := by omega
    subst hj0
    simp [Array.getD]
  · rw [ite_eq_right hk, Square.square_eq, ← pow_two]
    have hsize : (#[a] : Array M).size = 1 := rfl
    have hi : j < (#[a] : Array M).size + (2 ^ (w - 1) - 1) := by rw [hsize]; omega
    rw [oddPowersGo_getD (a ^ 2) (2 ^ (w - 1) - 1) j a #[a] v hi]
    by_cases hj0 : j < 1
    · have : j = 0 := by omega
      subst this
      rw [dite_eq_left (by rw [hsize]; omega)]
      simp
    · rw [dite_eq_right (by rw [hsize]; omega), hsize, show j - 1 + 1 = j from by omega, ← pow_mul,
        ← pow_succ']

/-- The sliding-window loop invariant, with the accumulator a power of `a` (so no commutativity
is needed): `swPowAux table w (a^h) n len = a ^ (h · 2^len + n)`, given `n < 2^len` and a table
of the odd powers of `a`. -/
theorem swPowAux_eq [Monoid M] [Square M] (a : M) (w : ℕ) (hw : 1 ≤ w) (table : Array M)
    (htable : ∀ d : ℕ, d % 2 = 1 → d < 2 ^ w → ∀ fb : M, table.getD ((d - 1) / 2) fb = a ^ d) :
    ∀ (len h n : ℕ), n < 2 ^ len → swPowAux table w (a ^ h) n len = a ^ (h * 2 ^ len + n) := by
  intro len
  induction len using Nat.strongRecOn with
  | ind len ih =>
    intro h n hn
    obtain _ | len := len
    · rw [swPowAux]
      have : n = 0 := by simpa using hn
      subst this; simp
    · rw [swPowAux]
      by_cases htop : n < 2 ^ len
      · rw [ite_eq_left htop,
          show Square.square (a ^ h) = a ^ (h * 2) by rw [Square.square_eq, ← pow_two, ← pow_mul],
          ih len (by omega) (h * 2) n htop]
        congr 1
        rw [pow_succ, mul_assoc, mul_comm 2 (2 ^ len)]
      · rw [ite_eq_right htop]
        extract_lets L0 winRaw p L d
        have hL0 : L0 = min w (len + 1) := rfl
        have hwinRaw : winRaw = n / 2 ^ (len + 1 - L0) := rfl
        have hL : L = max 1 (L0 - p.1) := rfl
        have hd : d = p.2 := rfl
        have hL0_pos : 1 ≤ L0 := by rw [hL0]; omega
        have hL0_le : L0 ≤ len + 1 := by rw [hL0]; exact min_le_right _ _
        have hL0_le_w : L0 ≤ w := by rw [hL0]; exact min_le_left _ _
        have hge : 2 ^ (L0 - 1) ≤ winRaw := by
          rw [hwinRaw, Nat.le_div_iff_mul_le (Nat.two_pow_pos _), ← pow_add,
            show L0 - 1 + (len + 1 - L0) = len by omega]
          omega
        have hpos : 1 ≤ winRaw := le_trans (Nat.one_le_two_pow) hge
        have hlt : winRaw < 2 ^ L0 := by
          rw [hwinRaw, Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← pow_add,
            show L0 + (len + 1 - L0) = len + 1 by omega]
          exact hn
        obtain ⟨heqw, hdodd⟩ := oddShift_spec winRaw hpos
        rw [← hd] at heqw hdodd
        have hd_ge1 : 1 ≤ d := by omega
        have hpow_le : 2 ^ p.1 ≤ winRaw := by
          rw [heqw]; exact Nat.le_mul_of_pos_left _ (by omega)
        have ht_lt : p.1 < L0 :=
          (Nat.pow_lt_pow_iff_right (by omega)).mp (lt_of_le_of_lt hpow_le hlt)
        have hL_eq : L = L0 - p.1 := by rw [hL, max_eq_right (by omega)]
        have hd_le : d ≤ winRaw := by
          rw [heqw]; exact Nat.le_mul_of_pos_right d (Nat.two_pow_pos _)
        have hd_lt : d < 2 ^ w :=
          lt_of_le_of_lt hd_le (lt_of_lt_of_le hlt (Nat.pow_le_pow_right (by omega) hL0_le_w))
        have hexp : len + 1 - L = (len + 1 - L0) + p.1 := by rw [hL_eq]; omega
        have key : d = n / 2 ^ (len + 1 - L) := by
          have hd_eq : d = winRaw / 2 ^ p.1 := by
            rw [heqw, Nat.mul_div_cancel _ (Nat.two_pow_pos _)]
          rw [hd_eq, hwinRaw, Nat.div_div_eq_div_mul, ← pow_add, hexp]
        have decomp : d * 2 ^ (len + 1 - L) + n % 2 ^ (len + 1 - L) = n := by
          rw [key]; exact Nat.div_add_mod' n (2 ^ (len + 1 - L))
        have hL_le : L ≤ len + 1 := by rw [hL_eq]; omega
        have hlen'_lt : len + 1 - L < len + 1 := by omega
        have hrem_lt : n % 2 ^ (len + 1 - L) < 2 ^ (len + 1 - L) := Nat.mod_lt n (Nat.two_pow_pos _)
        rw [squareN_eq, ← pow_mul, htable d hdodd hd_lt (a ^ h), ← pow_add,
          ih (len + 1 - L) hlen'_lt (h * 2 ^ L + d) (n % 2 ^ (len + 1 - L)) hrem_lt]
        congr 1
        rw [add_mul, mul_assoc, ← pow_add, show L + (len + 1 - L) = len + 1 by omega,
          add_assoc, decomp]

/-- The chosen window width is always at least `1`. -/
theorem one_le_slidingWindowSize (n : ℕ) : 1 ≤ slidingWindowSize n := by
  rw [slidingWindowSize]
  split_ifs <;> omega

/-- **Correctness of sliding-window exponentiation:** `slidingWindowPow a n = a ^ n`. -/
theorem slidingWindowPow_eq_pow [Monoid M] [Square M] (a : M) (n : ℕ) :
    slidingWindowPow a n = a ^ n := by
  rw [slidingWindowPow]
  by_cases hn0 : n = 0
  · subst hn0; simp
  · rw [ite_eq_right hn0]
    extract_lets w table s L0 winRaw p L d
    have hw : 1 ≤ w := one_le_slidingWindowSize n
    have hn1 : 1 ≤ n := by omega
    have hs_def : s = Nat.log 2 n + 1 := rfl
    have hs_pos : 1 ≤ s := by omega
    have hs_lo : 2 ^ (s - 1) ≤ n := by
      rw [show s - 1 = Nat.log 2 n by omega]; exact Nat.pow_log_le_self 2 hn0
    have hs_hi : n < 2 ^ s := by rw [hs_def]; exact Nat.lt_pow_succ_log_self (by omega) n
    -- window extraction at the full frame `s`
    have hL0 : L0 = min w s := rfl
    have hwinRaw : winRaw = n / 2 ^ (s - L0) := rfl
    have hL : L = max 1 (L0 - p.1) := rfl
    have hd : d = p.2 := rfl
    have hL0_pos : 1 ≤ L0 := by rw [hL0]; omega
    have hL0_le : L0 ≤ s := by rw [hL0]; exact min_le_right _ _
    have hL0_le_w : L0 ≤ w := by rw [hL0]; exact min_le_left _ _
    have hge : 2 ^ (L0 - 1) ≤ winRaw := by
      rw [hwinRaw, Nat.le_div_iff_mul_le (Nat.two_pow_pos _), ← pow_add,
        show L0 - 1 + (s - L0) = s - 1 by omega]
      exact hs_lo
    have hpos : 1 ≤ winRaw := le_trans (Nat.one_le_two_pow) hge
    have hlt : winRaw < 2 ^ L0 := by
      rw [hwinRaw, Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← pow_add,
        show L0 + (s - L0) = s by omega]
      exact hs_hi
    obtain ⟨heqw, hdodd⟩ := oddShift_spec winRaw hpos
    rw [← hd] at heqw hdodd
    have hpow_le : 2 ^ p.1 ≤ winRaw := by rw [heqw]; exact Nat.le_mul_of_pos_left _ (by omega)
    have ht_lt : p.1 < L0 := (Nat.pow_lt_pow_iff_right (by omega)).mp (lt_of_le_of_lt hpow_le hlt)
    have hL_eq : L = L0 - p.1 := by rw [hL, max_eq_right (by omega)]
    have hd_le : d ≤ winRaw := by rw [heqw]; exact Nat.le_mul_of_pos_right d (Nat.two_pow_pos _)
    have hd_lt : d < 2 ^ w :=
      lt_of_le_of_lt hd_le (lt_of_lt_of_le hlt (Nat.pow_le_pow_right (by omega) hL0_le_w))
    have hexp : s - L = (s - L0) + p.1 := by rw [hL_eq]; omega
    have key : d = n / 2 ^ (s - L) := by
      have hd_eq : d = winRaw / 2 ^ p.1 := by rw [heqw, Nat.mul_div_cancel _ (Nat.two_pow_pos _)]
      rw [hd_eq, hwinRaw, Nat.div_div_eq_div_mul, ← pow_add, hexp]
    have decomp : d * 2 ^ (s - L) + n % 2 ^ (s - L) = n := by
      rw [key]; exact Nat.div_add_mod' n (2 ^ (s - L))
    have hrem_lt : n % 2 ^ (s - L) < 2 ^ (s - L) := Nat.mod_lt n (Nat.two_pow_pos _)
    -- the odd-power table is correct
    have htable : ∀ d' : ℕ, d' % 2 = 1 → d' < 2 ^ w → ∀ fb : M,
        table.getD ((d' - 1) / 2) fb = a ^ d' := by
      intro d' hodd' hlt' fb
      have h2w : 2 ^ w = 2 * 2 ^ (w - 1) := by rw [← pow_succ']; congr 1; omega
      have hbound : (d' - 1) / 2 < 2 ^ (w - 1) := by omega
      have hget := mkOddPowerTable_getD a w ((d' - 1) / 2) hbound fb
      rw [show 2 * ((d' - 1) / 2) + 1 = d' by omega] at hget
      exact hget
    rw [htable d hdodd hd_lt a, swPowAux_eq a w hw table htable (s - L) d (n % 2 ^ (s - L)) hrem_lt,
      decomp]

-- ═══════════════════════════════════════════════════════════════════
-- Transport along a multiplicative map
-- ═══════════════════════════════════════════════════════════════════

/-! These lemmas let a wrapper type whose `^` is *defined* as `slidingWindowPow` relate its power to
the reference power on a Mathlib type via a multiplicative map `f` (such as `toPoly`/`toMat`),
without the source type being a `Monoid` — exactly the role `map_fastPow` plays for `fastPow`. -/

section Transport

variable {M N : Type*}

/-- `f` commutes with `Array.getD` after mapping the array. -/
theorem map_getD (f : M → N) (t : Array M) (i : ℕ) (v : M) :
    f (t.getD i v) = (t.map f).getD i (f v) := by
  rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?, Array.getElem?_map]
  cases t[i]? <;> simp

/-- `f` commutes with `squareN` when it commutes with squaring. -/
theorem map_squareN [Mul M] [Square M] [Mul N] [Square N] (f : M → N)
    (hsq : ∀ x, f (Square.square x) = Square.square (f x)) (x : M) (k : ℕ) :
    f (squareN x k) = squareN (f x) k := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih => show f (squareN (Square.square x) k) = squareN (Square.square (f x)) k
                 rw [ih, hsq]

/-- `f` commutes with `oddPowersGo` (mapping the accumulator). -/
theorem map_oddPowersGo [Mul M] [Mul N] (f : M → N) (hmul : ∀ a b : M, f (a * b) = f a * f b)
    (asq : M) : ∀ (k : ℕ) (cur : M) (acc : Array M),
      (oddPowersGo asq cur acc k).map f = oddPowersGo (f asq) (f cur) (acc.map f) k := by
  intro k
  induction k with
  | zero => intro cur acc; rfl
  | succ k ih =>
    intro cur acc
    show (oddPowersGo asq (cur * asq) (acc.push (cur * asq)) k).map f
        = oddPowersGo (f asq) (f cur * f asq) ((acc.map f).push (f cur * f asq)) k
    rw [ih, hmul, Array.map_push, hmul]

/-- `f` commutes with `mkOddPowerTable` when it commutes with squaring. -/
theorem map_mkOddPowerTable [Mul M] [Square M] [Mul N] [Square N] (f : M → N)
    (hmul : ∀ a b : M, f (a * b) = f a * f b) (hsq : ∀ x, f (Square.square x) = Square.square (f x))
    (a : M) (w : ℕ) : (mkOddPowerTable a w).map f = mkOddPowerTable (f a) w := by
  rw [mkOddPowerTable, mkOddPowerTable]
  have hsing : (#[a] : Array M).map f = #[f a] := by simp
  by_cases hk : 2 ^ (w - 1) ≤ 1
  · rw [ite_eq_left hk, ite_eq_left hk, hsing]
  · rw [ite_eq_right hk, ite_eq_right hk, map_oddPowersGo f hmul, hsq, hsing]

/-- `f` commutes with the sliding-window loop (mapping the table). -/
theorem map_swPowAux [Mul M] [Square M] [Mul N] [Square N] (f : M → N)
    (hmul : ∀ a b : M, f (a * b) = f a * f b) (hsq : ∀ x, f (Square.square x) = Square.square (f x))
    (w : ℕ) (t : Array M) :
    ∀ (result : M) (n len : ℕ),
      f (swPowAux t w result n len) = swPowAux (t.map f) w (f result) n len := by
  intro result n len
  induction len using Nat.strongRecOn generalizing result n with
  | ind len ih =>
    obtain _ | len := len
    · simp [swPowAux]
    · rw [swPowAux, swPowAux]
      by_cases htop : n < 2 ^ len
      · rw [ite_eq_left htop, ite_eq_left htop, ih len (by omega) (Square.square result) n, hsq]
      · rw [ite_eq_right htop, ite_eq_right htop]
        simp only []
        have hL : 1 ≤ max 1 (min w (len + 1) - (oddShift (n / 2 ^ (len + 1 - min w (len + 1)))).fst) :=
          le_max_left _ _
        generalize hLdef :
          max 1 (min w (len + 1) - (oddShift (n / 2 ^ (len + 1 - min w (len + 1)))).fst) = L at *
        generalize (oddShift (n / 2 ^ (len + 1 - min w (len + 1)))).snd = d
        rw [ih (len + 1 - L) (by omega) (squareN result L * t.getD ((d - 1) / 2) result)
              (n % 2 ^ (len + 1 - L)), hmul, map_squareN f hsq, map_getD f]

/-- **`slidingWindowPow` transported along a multiplicative map.** For `f : M → N` preserving `1`
and `*` (with `N` a `Monoid`), `f (slidingWindowPow a n) = (f a) ^ n`. This is how a wrapper type
relates its `slidingWindowPow`-based power to the reference power on a Mathlib type, without the
source type being a `Monoid`. -/
theorem map_slidingWindowPow [Mul M] [One M] [Square M] [Monoid N] [Square N]
    (f : M → N) (hone : f 1 = 1) (hmul : ∀ a b : M, f (a * b) = f a * f b) (a : M) (n : ℕ) :
    f (slidingWindowPow a n) = (f a) ^ n := by
  have hsq : ∀ x : M, f (Square.square x) = Square.square (f x) := fun x => by
    rw [Square.square_eq, hmul, Square.square_eq]
  rw [← slidingWindowPow_eq_pow (f a) n]
  by_cases hn : n = 0
  · subst hn; simp [slidingWindowPow, hone]
  · rw [slidingWindowPow, slidingWindowPow, ite_eq_right hn, ite_eq_right hn]
    simp only []
    rw [map_swPowAux f hmul hsq, map_getD f]
    simp only [map_mkOddPowerTable f hmul hsq]

end Transport

-- ═══════════════════════════════════════════════════════════════════
-- Tests
-- ═══════════════════════════════════════════════════════════════════

section Tests

#guard slidingWindowPow (2 : ℕ) 0 = 1
#guard slidingWindowPow (2 : ℕ) 1 = 2
#guard slidingWindowPow (2 : ℕ) 3 = 8
#guard slidingWindowPow (2 : ℕ) 10 = 1024
#guard slidingWindowPow (3 : ℕ) 5 = 243
#guard slidingWindowPow (3 : ℕ) 3 = 27
#guard slidingWindowPow (5 : ℕ) 3 = 125
#guard slidingWindowPow (1 : ℕ) 100 = 1
#guard slidingWindowPow (7 : ℕ) 13 = 96889010407
#guard slidingWindowPow (2 : ℕ) 64 = 18446744073709551616

-- Cross-check against `fastPow` over a range of bases and exponents.
#guard (List.range 40).all (fun n => (List.range 6).all (fun a => slidingWindowPow (a : ℕ) n == fastPow (a : ℕ) n))

-- Cross-check against the reference power for a few larger exponents.
#guard [100, 255, 256, 1000, 4095].all (fun n => slidingWindowPow (3 : ℕ) n == 3 ^ n)

/-- A symbolic value recording the exact tree of binary multiplications performed (squaring goes
through the default `Square` instance, i.e. `x * x`, so it shows up as a `mul` node too). -/
inductive PowExpr where
  | base
  | mul (x y : PowExpr)
  deriving DecidableEq, Repr

instance : Mul PowExpr := ⟨PowExpr.mul⟩
instance : One PowExpr := ⟨PowExpr.base⟩

/-- Total number of binary multiplications (including squarings) in the operation tree. -/
def PowExpr.opCount : PowExpr → ℕ
  | .base => 0
  | .mul x y => x.opCount + y.opCount + 1

-- Cubing is exactly `(a · a) · a`: one squaring (`a · a`) followed by one multiplication.
#guard slidingWindowPow PowExpr.base 3 = .mul (.mul .base .base) .base
#guard (slidingWindowPow PowExpr.base 3).opCount = 2

end Tests

end Azurite
