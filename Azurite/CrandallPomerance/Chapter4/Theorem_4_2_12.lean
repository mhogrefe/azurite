/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

/-
  Crandall–Pomerance, Algorithm 4.2.11 and Theorem 4.2.12 (Lenstra):
  divisors in residue classes.  Given `n, r, s` with `0 < r < s < n`
  and `gcd(r, s) = 1`, the algorithm finds ALL divisors of `n` that
  are `≡ r (mod s)`, by developing Euclidean chains `(aᵢ), (bᵢ), (cᵢ)`
  from `(a₀, a₁) = (s, r'r* mod s)`, `(b₀, b₁) = (0, 1)` (where
  `r* = r⁻¹ mod s` and `r' = nr* mod s`), and, for each index `i ≤ t`
  and each candidate `c ≡ cᵢ (mod s)` in a small window, solving the
  system (4.16): `xaᵢ + ybᵢ = c`, `(xs + r)(ys + r') = n`.

  Theorem 4.2.12 is the correctness claim.  Its heart is the WINDOW
  LEMMA: for the true coefficient pair (`d = xs + r`,
  `n/d = ys + r'`), some index `i` has `Sᵢ := xaᵢ + ybᵢ` inside the
  window — `|Sᵢ| < s` for an even `i`, or
  `2aᵢbᵢ ≤ Sᵢ ≤ xy + aᵢbᵢ < aᵢbᵢ + n/s²` for an odd `i`.

  TWO MORE CORRECTIONS TO THE BOOK (numerically validated over 466 000
  divisor instances before formalizing):

  * The book's odd-index window is `2aᵢbᵢ < c`, STRICT.  That misses
    divisors: for `(n, r, s) = (50, 1, 4)` the divisor `5 = 1·4 + 1`
    has chain `a = (4, 2, 0)`, `b = (0, 1, −2)` and
    `S₀ = 4, S₁ = 4 = 2a₁b₁, S₂ = −4` — no strict window contains any
    `Sᵢ`, so Algorithm 4.2.11 as printed reports only `{1, 25}` for
    the divisors of `50` that are `≡ 1 (mod 4)`.  (The book's proof
    silently uses strict inequalities `x > b_{i+1}`, `y > a_{i+1}`
    that fail in the boundary case.)  The correct window is CLOSED on
    the left: `2aᵢbᵢ ≤ c`.

  * The book initializes `c₁ := (nr* − ra₁)/s mod s`.  That is wrong
    whenever `s ∤ r'r*`: the correct value (the one making the
    congruence (4.20) `xaᵢ + ybᵢ ≡ cᵢ (mod s)` hold at `i = 1`) is
    `c₁ := r*·(n − rr')/s mod s`; the book's expression exceeds it by
    `r·⌊r'r*/s⌋ (mod s)`.  For `(n, r, s) = (91, 2, 5)` (divisor `7`):
    correct `c₁ ≡ 1`, book's `c₁ ≡ 3`, while `xa₁ + yb₁ = 6 ≡ 1`.

  We also note the book's statement needs `s ∤ n` (else `a₁ = 0` and
  the Euclidean chain cannot start, its odd-index convention being
  violated immediately); we take that as a hypothesis.

  The chain is built by a structural double-step iteration `lstep` on
  states carrying `(a_{2k}, a_{2k+1}, b_{2k}, b_{2k+1}, c_{2k},
  c_{2k+1})`, with a fuel-based step count (kernel-reducible — no
  well-founded recursion).  Even steps take the floor quotient
  (`0 ≤ aᵢ < aᵢ₋₁`), odd steps the ceiling-minus-one quotient
  (`0 < aᵢ ≤ aᵢ₋₁`), so the chain terminates at an even `t` with
  `a_t = 0` and all quotients are `≥ 1` — which is what drives the
  sign pattern (4.19) and the alternating identity (4.18).
-/
import Mathlib.Data.Int.GCD
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

namespace Azurite

namespace CP

/-! ### The Euclidean chain of Algorithm 4.2.11 -/

/-- The state of the chain at an even index `2k`: the values
`a_{2k}, a_{2k+1}` (natural numbers) and `b_{2k}, b_{2k+1}`,
`c_{2k}, c_{2k+1}` (integers).  Once `a_{2k} = 0` (the terminal index
`t = 2k`), the odd-slot values are unused. -/
structure LenstraState where
  a0 : ℕ
  a1 : ℕ
  b0 : ℤ
  b1 : ℤ
  c0 : ℤ
  c1 : ℤ

/-- One double-step of the Euclidean chain: from index `2k` to
`2k + 2`.  The even substep uses the floor quotient (remainder in
`[0, a_{2k+1})`); if it hits `0` the chain has terminated and the
state freezes; otherwise the odd substep uses the largest quotient
with a POSITIVE remainder (remainder in `(0, a_{2k+2}]`). -/
def lstep (σ : LenstraState) : LenstraState :=
  if σ.a0 = 0 then σ
  else if σ.a0 % σ.a1 = 0 then
    ⟨0, 0, σ.b0 - (σ.a0 / σ.a1 : ℕ) * σ.b1, 0,
      σ.c0 - (σ.a0 / σ.a1 : ℕ) * σ.c1, 0⟩
  else
    ⟨σ.a0 % σ.a1,
      σ.a1 - (σ.a1 - 1) / (σ.a0 % σ.a1) * (σ.a0 % σ.a1),
      σ.b0 - (σ.a0 / σ.a1 : ℕ) * σ.b1,
      σ.b1 - ((σ.a1 - 1) / (σ.a0 % σ.a1) : ℕ)
        * (σ.b0 - (σ.a0 / σ.a1 : ℕ) * σ.b1),
      σ.c0 - (σ.a0 / σ.a1 : ℕ) * σ.c1,
      σ.c1 - ((σ.a1 - 1) / (σ.a0 % σ.a1) : ℕ)
        * (σ.c0 - (σ.a0 / σ.a1 : ℕ) * σ.c1)⟩

/-- The chain state after `k` double-steps, from the initial state
`(a₀, a₁, b₀, b₁, c₀, c₁) = (s, a₁, 0, 1, 0, c₁)`. -/
def lchain (s a₁ : ℕ) (c₁ : ℤ) : ℕ → LenstraState
  | 0 => ⟨s, a₁, 0, 1, 0, c₁⟩
  | k + 1 => lstep (lchain s a₁ c₁ k)

/-- Fuel-based search for the first `k` with `a_{2k} = 0` (the fuel
`s` always suffices, since the even-index values strictly decrease). -/
def lKAux (s a₁ : ℕ) (c₁ : ℤ) : ℕ → ℕ → ℕ
  | 0, k => k
  | fuel + 1, k =>
      if (lchain s a₁ c₁ k).a0 = 0 then k else lKAux s a₁ c₁ fuel (k + 1)

/-- The number of double-steps of the chain. -/
def lK (s a₁ : ℕ) (c₁ : ℤ) : ℕ := lKAux s a₁ c₁ s 0

/-- The terminal index `t` of the chain (even, with `a_t = 0`). -/
def lT (s a₁ : ℕ) (c₁ : ℤ) : ℕ := 2 * lK s a₁ c₁

/-- The sequence `(aᵢ)` of Algorithm 4.2.11, as integers. -/
def lA (s a₁ : ℕ) (c₁ : ℤ) (i : ℕ) : ℤ :=
  if i % 2 = 0 then ((lchain s a₁ c₁ (i / 2)).a0 : ℤ)
  else ((lchain s a₁ c₁ (i / 2)).a1 : ℤ)

/-- The sequence `(bᵢ)` of Algorithm 4.2.11. -/
def lB (s a₁ : ℕ) (c₁ : ℤ) (i : ℕ) : ℤ :=
  if i % 2 = 0 then (lchain s a₁ c₁ (i / 2)).b0
  else (lchain s a₁ c₁ (i / 2)).b1

/-- The sequence `(cᵢ)` of Algorithm 4.2.11 (with the CORRECTED
initialization `c₁` supplied by the caller). -/
def lC (s a₁ : ℕ) (c₁ : ℤ) (i : ℕ) : ℤ :=
  if i % 2 = 0 then (lchain s a₁ c₁ (i / 2)).c0
  else (lchain s a₁ c₁ (i / 2)).c1

section StepAccessors

variable {σ : LenstraState}

private theorem lstep_frozen (h0 : σ.a0 = 0) : lstep σ = σ := by
  rw [lstep, ite_eq_left h0]

private theorem lstep_a0_term (h0 : σ.a0 ≠ 0) (hγ : σ.a0 % σ.a1 = 0) :
    (lstep σ).a0 = 0 := by
  rw [lstep, ite_eq_right h0, ite_eq_left hγ]

private theorem lstep_a0 (h0 : σ.a0 ≠ 0) (hγ : σ.a0 % σ.a1 ≠ 0) :
    (lstep σ).a0 = σ.a0 % σ.a1 := by
  rw [lstep, ite_eq_right h0, ite_eq_right hγ]

private theorem lstep_a1 (h0 : σ.a0 ≠ 0) (hγ : σ.a0 % σ.a1 ≠ 0) :
    (lstep σ).a1
      = σ.a1 - (σ.a1 - 1) / (σ.a0 % σ.a1) * (σ.a0 % σ.a1) := by
  rw [lstep, ite_eq_right h0, ite_eq_right hγ]

private theorem lstep_b0 (h0 : σ.a0 ≠ 0) :
    (lstep σ).b0 = σ.b0 - (σ.a0 / σ.a1 : ℕ) * σ.b1 := by
  rw [lstep, ite_eq_right h0]
  by_cases hγ : σ.a0 % σ.a1 = 0
  · rw [ite_eq_left hγ]
  · rw [ite_eq_right hγ]

private theorem lstep_b1 (h0 : σ.a0 ≠ 0) (hγ : σ.a0 % σ.a1 ≠ 0) :
    (lstep σ).b1 = σ.b1 - ((σ.a1 - 1) / (σ.a0 % σ.a1) : ℕ)
      * (σ.b0 - (σ.a0 / σ.a1 : ℕ) * σ.b1) := by
  rw [lstep, ite_eq_right h0, ite_eq_right hγ]

private theorem lstep_c0 (h0 : σ.a0 ≠ 0) :
    (lstep σ).c0 = σ.c0 - (σ.a0 / σ.a1 : ℕ) * σ.c1 := by
  rw [lstep, ite_eq_right h0]
  by_cases hγ : σ.a0 % σ.a1 = 0
  · rw [ite_eq_left hγ]
  · rw [ite_eq_right hγ]

private theorem lstep_c1 (h0 : σ.a0 ≠ 0) (hγ : σ.a0 % σ.a1 ≠ 0) :
    (lstep σ).c1 = σ.c1 - ((σ.a1 - 1) / (σ.a0 % σ.a1) : ℕ)
      * (σ.c0 - (σ.a0 / σ.a1 : ℕ) * σ.c1) := by
  rw [lstep, ite_eq_right h0, ite_eq_right hγ]

end StepAccessors

section ChainSpec

variable {s a₁ : ℕ} {c₁ : ℤ}

/-- The invariant carried along the chain: while the even-index value
is nonzero, the odd slot holds a value in `(0, a_{2k}]`. -/
private theorem lchain_inv (h1 : 0 < a₁) (h1s : a₁ ≤ s) :
    ∀ k, (lchain s a₁ c₁ k).a0 ≠ 0 →
      0 < (lchain s a₁ c₁ k).a1 ∧
        (lchain s a₁ c₁ k).a1 ≤ (lchain s a₁ c₁ k).a0 := by
  intro k
  induction k with
  | zero => exact fun _ => ⟨h1, h1s⟩
  | succ k ih =>
    intro hk
    rw [lchain] at hk ⊢
    by_cases h0 : (lchain s a₁ c₁ k).a0 = 0
    · rw [lstep_frozen h0] at hk ⊢
      exact ih hk
    · obtain ⟨hpos, hle⟩ := ih h0
      by_cases hγ : (lchain s a₁ c₁ k).a0 % (lchain s a₁ c₁ k).a1 = 0
      · rw [lstep_a0_term h0 hγ] at hk
        exact absurd rfl hk
      · have hγlt : (lchain s a₁ c₁ k).a0 % (lchain s a₁ c₁ k).a1
            < (lchain s a₁ c₁ k).a1 := Nat.mod_lt _ hpos
        have hγpos : 0 < (lchain s a₁ c₁ k).a0 % (lchain s a₁ c₁ k).a1 :=
          Nat.pos_of_ne_zero hγ
        have hdm := Nat.div_add_mod ((lchain s a₁ c₁ k).a1 - 1)
          ((lchain s a₁ c₁ k).a0 % (lchain s a₁ c₁ k).a1)
        have hmlt : ((lchain s a₁ c₁ k).a1 - 1)
            % ((lchain s a₁ c₁ k).a0 % (lchain s a₁ c₁ k).a1)
            < (lchain s a₁ c₁ k).a0 % (lchain s a₁ c₁ k).a1 :=
          Nat.mod_lt _ hγpos
        rw [Nat.mul_comm] at hdm
        obtain ⟨Q, hQ⟩ : ∃ Q, ((lchain s a₁ c₁ k).a1 - 1)
            / ((lchain s a₁ c₁ k).a0 % (lchain s a₁ c₁ k).a1)
            * ((lchain s a₁ c₁ k).a0 % (lchain s a₁ c₁ k).a1) = Q := ⟨_, rfl⟩
        rw [lstep_a0 h0 hγ, lstep_a1 h0 hγ, hQ]
        rw [hQ] at hdm
        omega

/-- While nonzero, the even-index values strictly decrease with each
double-step. -/
private theorem lchain_dec (h1 : 0 < a₁) (h1s : a₁ ≤ s) :
    ∀ k, (lchain s a₁ c₁ k).a0 ≠ 0 →
      (lchain s a₁ c₁ (k + 1)).a0 < (lchain s a₁ c₁ k).a0 := by
  intro k hk
  obtain ⟨hpos, hle⟩ := lchain_inv h1 h1s k hk
  rw [lchain]
  by_cases hγ : (lchain s a₁ c₁ k).a0 % (lchain s a₁ c₁ k).a1 = 0
  · rw [lstep_a0_term hk hγ]
    omega
  · rw [lstep_a0 hk hγ]
    have h1' := Nat.mod_lt (lchain s a₁ c₁ k).a0 hpos
    omega

/-- The chain terminates within the fuel bound. -/
private theorem lchain_reaches_zero (h1 : 0 < a₁) (h1s : a₁ ≤ s) :
    ∀ fuel k, (lchain s a₁ c₁ k).a0 ≤ fuel →
      (lchain s a₁ c₁ (lKAux s a₁ c₁ fuel k)).a0 = 0 := by
  intro fuel
  induction fuel with
  | zero =>
    intro k hk
    rw [lKAux]
    omega
  | succ fuel ih =>
    intro k hk
    rw [lKAux]
    by_cases h0 : (lchain s a₁ c₁ k).a0 = 0
    · rwa [ite_eq_left h0]
    · rw [ite_eq_right h0]
      exact ih (k + 1) (by have := lchain_dec h1 h1s k h0; omega)

/-- The step count `lK` reaches a zero and is minimal. -/
private theorem lK_spec (h1 : 0 < a₁) (h1s : a₁ ≤ s) :
    (lchain s a₁ c₁ (lK s a₁ c₁)).a0 = 0 ∧
      ∀ k < lK s a₁ c₁, (lchain s a₁ c₁ k).a0 ≠ 0 := by
  constructor
  · exact lchain_reaches_zero h1 h1s s 0 (by simp [lchain])
  · have haux : ∀ fuel k₀, (∀ k < k₀, (lchain s a₁ c₁ k).a0 ≠ 0) →
        ∀ k < lKAux s a₁ c₁ fuel k₀, (lchain s a₁ c₁ k).a0 ≠ 0 := by
      intro fuel
      induction fuel with
      | zero =>
        intro k₀ hk₀ k hk
        rw [lKAux] at hk
        exact hk₀ k hk
      | succ fuel ih =>
        intro k₀ hk₀ k hk
        rw [lKAux] at hk
        by_cases h0 : (lchain s a₁ c₁ k₀).a0 = 0
        · rw [ite_eq_left h0] at hk
          exact hk₀ k hk
        · rw [ite_eq_right h0] at hk
          refine ih (k₀ + 1) ?_ k hk
          intro j hj
          rcases Nat.lt_or_ge j k₀ with h | h
          · exact hk₀ j h
          · have hj' : j = k₀ := by omega
            rwa [hj']
    exact haux s 0 (by omega)

end ChainSpec

/-! ### The abstract window-walk lemma -/

section Walk

variable {s : ℕ} {A B : ℕ → ℤ} {t : ℕ}

/-- Discrete intermediate-value boundary: a predicate true at `0` and
false at `m` flips somewhere. -/
private theorem boundary {P : ℕ → Prop} {m : ℕ} (h0 : P 0) (hm : ¬P m) :
    ∃ k < m, P k ∧ ¬P (k + 1) := by
  induction m with
  | zero => exact absurd h0 hm
  | succ m ih =>
    by_cases hPm : P m
    · exact ⟨m, by omega, hPm, hm⟩
    · obtain ⟨k, hk, h1, h2⟩ := ih hPm
      exact ⟨k, by omega, h1, h2⟩

/-- The sign pattern (4.19): `b₀ = 0`, `bᵢ ≤ −1` for even `i ≥ 2`,
`bᵢ ≥ 1` for odd `i` — all consequences of `q ≥ 1` in the
recurrence. -/
private theorem sign_pattern (hB0 : B 0 = 0) (hB1 : B 1 = 1)
    (hrec : ∀ i, i + 2 ≤ t → ∃ q : ℤ, 1 ≤ q ∧
      A (i + 2) = A i - q * A (i + 1) ∧ B (i + 2) = B i - q * B (i + 1)) :
    ∀ i ≤ t, (i = 0 → B i = 0) ∧ (i % 2 = 0 → i ≠ 0 → B i ≤ -1) ∧
      (i % 2 = 1 → 1 ≤ B i) := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hit
    match i with
    | 0 => exact ⟨fun _ => hB0, fun _ h => absurd rfl h, by omega⟩
    | 1 => exact ⟨by omega, by omega, fun _ => hB1.ge⟩
    | (j + 2) =>
      obtain ⟨q, hq, _, hBrec⟩ := hrec j hit
      have hj := ih j (by omega) (by omega)
      have hj1 := ih (j + 1) (by omega) (by omega)
      refine ⟨by omega, ?_, ?_⟩
      · intro hev _
        have hBj : B j ≤ 0 := by
          rcases eq_or_ne j 0 with rfl | hj0
          · rw [hB0]
          · linarith [hj.2.1 (by omega) hj0]
        have hBj1 : 1 ≤ B (j + 1) := hj1.2.2 (by omega)
        have hmul : 1 * 1 ≤ q * B (j + 1) :=
          mul_le_mul hq hBj1 (by norm_num) (by omega)
        rw [hBrec]
        linarith
      · intro hodd
        have hBj : 1 ≤ B j := hj.2.2 (by omega)
        have hBj1 : B (j + 1) ≤ -1 := hj1.2.1 (by omega) (by omega)
        have hmul : q * B (j + 1) ≤ 1 * (-1) := by nlinarith
        rw [hBrec]
        linarith

/-- The alternating identity (4.18):
`b_{i+1}aᵢ − a_{i+1}bᵢ = ±s`, with sign `(−1)^i`. -/
private theorem alternating_identity (hA0 : A 0 = (s : ℤ))
    (hB0 : B 0 = 0) (hB1 : B 1 = 1)
    (hrec : ∀ i, i + 2 ≤ t → ∃ q : ℤ, 1 ≤ q ∧
      A (i + 2) = A i - q * A (i + 1) ∧ B (i + 2) = B i - q * B (i + 1)) :
    ∀ i, i < t → B (i + 1) * A i - A (i + 1) * B i
      = if i % 2 = 0 then (s : ℤ) else -s := by
  intro i
  induction i with
  | zero =>
    intro _
    rw [hA0, hB0, hB1, ite_eq_left rfl]
    ring
  | succ i ih =>
    intro hit
    obtain ⟨q, _, hArec, hBrec⟩ := hrec i (by omega)
    have h0 := ih (by omega)
    rcases Nat.even_or_odd i with ⟨m, hm⟩ | ⟨m, hm⟩
    · rw [ite_eq_left (by omega)] at h0
      rw [ite_eq_right (by omega), hArec, hBrec]
      linear_combination -h0
    · rw [ite_eq_right (by omega)] at h0
      rw [ite_eq_left (by omega), hArec, hBrec]
      linear_combination -h0

/-- **The window lemma** (the heart of Theorem 4.2.12): for any
`x, y ≥ 0` there is an index `i ≤ t` with `Sᵢ = xaᵢ + ybᵢ` in the
window — `|Sᵢ| < s` for even `i`, or `2aᵢbᵢ ≤ Sᵢ ≤ xy + aᵢbᵢ` for odd
`i` (note the CLOSED left end, correcting the book's strict
inequality). -/
private theorem window_walk (hs : 0 < s) (hA0 : A 0 = (s : ℤ))
    (hB0 : B 0 = 0) (hB1 : B 1 = 1) (ht : t % 2 = 0) (ht0 : 0 < t)
    (hAt : A t = 0) (hApos : ∀ i < t, 0 < A i)
    (hrec : ∀ i, i + 2 ≤ t → ∃ q : ℤ, 1 ≤ q ∧
      A (i + 2) = A i - q * A (i + 1) ∧ B (i + 2) = B i - q * B (i + 1))
    {x y : ℤ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    ∃ i ≤ t, (i % 2 = 0 ∧ |x * A i + y * B i| < s) ∨
      (i % 2 = 1 ∧ 2 * (A i * B i) ≤ x * A i + y * B i ∧
        x * A i + y * B i ≤ x * y + A i * B i) := by
  have hsign := sign_pattern hB0 hB1 hrec
  have halt := alternating_identity hA0 hB0 hB1 hrec
  have hAnn : ∀ i ≤ t, 0 ≤ A i := by
    intro i hi
    rcases eq_or_lt_of_le hi with rfl | h
    · rw [hAt]
    · exact (hApos i h).le
  have hS0 : 0 ≤ x * A 0 + y * B 0 := by
    rw [hA0, hB0]
    have h0 : 0 ≤ x * s := mul_nonneg hx (by positivity)
    omega
  have hBt : B t ≤ 0 := by
    rcases eq_or_ne t 0 with rfl | ht0'
    · rw [hB0]
    · linarith [(hsign t le_rfl).2.1 ht ht0']
  have hSt : x * A t + y * B t ≤ 0 := by
    rw [hAt]
    have h0 : y * B t ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hy hBt
    omega
  rcases eq_or_lt_of_le hSt with hSt0 | hStneg
  · exact ⟨t, le_rfl, Or.inl ⟨ht, by
      rw [hSt0, abs_zero]
      exact_mod_cast hs⟩⟩
  obtain ⟨k, hkm, hPk, hPk1⟩ := boundary
    (P := fun k => 0 ≤ x * A (2 * k) + y * B (2 * k))
    (by simpa using hS0) (m := t / 2) (by
      have he : 2 * (t / 2) = t := by omega
      rw [he]
      omega)
  have hi2t : 2 * k + 2 ≤ t := by omega
  have hSi : 0 ≤ x * A (2 * k) + y * B (2 * k) := hPk
  have hSi2 : x * A (2 * k + 2) + y * B (2 * k + 2) < 0 := by
    have he : 2 * (k + 1) = 2 * k + 2 := by omega
    rw [he] at hPk1
    omega
  by_cases hwin1 : x * A (2 * k) + y * B (2 * k) < s
  · exact ⟨2 * k, by omega, Or.inl ⟨by omega, by
      rw [abs_of_nonneg hSi]
      exact hwin1⟩⟩
  by_cases hwin2 : -(s : ℤ) < x * A (2 * k + 2) + y * B (2 * k + 2)
  · exact ⟨2 * k + 2, hi2t, Or.inl ⟨by omega, by
      rw [abs_of_neg hSi2]
      omega⟩⟩
  push Not at hwin1 hwin2
  -- the hard case: `S_{2k} ≥ s`, `S_{2k+2} ≤ −s`; the odd window at
  -- `2k + 1` catches the pair
  have hBi : B (2 * k) ≤ 0 := by
    rcases eq_or_ne (2 * k) 0 with h0 | h0
    · rw [h0, hB0]
    · linarith [(hsign (2 * k) (by omega)).2.1 (by omega) h0]
  have hBi1 : 1 ≤ B (2 * k + 1) :=
    (hsign (2 * k + 1) (by omega)).2.2 (by omega)
  have hBi2 : B (2 * k + 2) ≤ -1 :=
    (hsign (2 * k + 2) hi2t).2.1 (by omega) (by omega)
  have hAi : 0 < A (2 * k) := hApos _ (by omega)
  have hAi1 : 0 < A (2 * k + 1) := hApos _ (by omega)
  have hAi2 : 0 ≤ A (2 * k + 2) := hAnn _ hi2t
  have halt_i : B (2 * k + 1) * A (2 * k) - A (2 * k + 1) * B (2 * k)
      = s := by
    have h0 := halt (2 * k) (by omega)
    rwa [ite_eq_left (by omega)] at h0
  have halt_i1 : B (2 * k + 2) * A (2 * k + 1)
      - A (2 * k + 2) * B (2 * k + 1) = -s := by
    have h0 := halt (2 * k + 1) (by omega)
    rwa [ite_eq_right (by omega)] at h0
  -- `x ≥ b_{i+1}` and `y ≥ a_{i+1}`
  have hxB : B (2 * k + 1) ≤ x := by
    have h1 : y * B (2 * k) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hy hBi
    have h2 : (s : ℤ) ≤ x * A (2 * k) := by omega
    have h3 : A (2 * k + 1) * B (2 * k) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hAi1.le hBi
    have h4 : B (2 * k + 1) * A (2 * k) ≤ x * A (2 * k) := by omega
    exact le_of_mul_le_mul_right h4 hAi
  have hyA : A (2 * k + 1) ≤ y := by
    have h1 : 0 ≤ x * A (2 * k + 2) := mul_nonneg hx hAi2
    have h2 : y * B (2 * k + 2) ≤ -(s : ℤ) := by omega
    have h3 : 0 ≤ A (2 * k + 2) * B (2 * k + 1) := by positivity
    have h4 : y * B (2 * k + 2) ≤ B (2 * k + 2) * A (2 * k + 1) := by
      omega
    nlinarith [h4, hBi2]
  refine ⟨2 * k + 1, by omega, Or.inr ⟨by omega, ?_, ?_⟩⟩
  · have h1 : B (2 * k + 1) * A (2 * k + 1) ≤ x * A (2 * k + 1) :=
      mul_le_mul_of_nonneg_right hxB hAi1.le
    have h2 : A (2 * k + 1) * B (2 * k + 1) ≤ y * B (2 * k + 1) :=
      mul_le_mul_of_nonneg_right hyA (by omega)
    nlinarith [h1, h2]
  · have h0 : 0 ≤ (x - B (2 * k + 1)) * (y - A (2 * k + 1)) :=
      mul_nonneg (by omega) (by omega)
    nlinarith [h0]

end Walk

/-! ### Bridging the concrete chain to the abstract hypotheses -/

section Bridge

variable {s a₁ : ℕ} {c₁ : ℤ}

private theorem lA_zero : lA s a₁ c₁ 0 = s := by
  rw [lA, ite_eq_left (by norm_num), lchain]

private theorem lA_one : lA s a₁ c₁ 1 = a₁ := by
  rw [lA, ite_eq_right (by norm_num), lchain]

private theorem lB_zero : lB s a₁ c₁ 0 = 0 := by
  rw [lB, ite_eq_left (by norm_num), lchain]

private theorem lB_one : lB s a₁ c₁ 1 = 1 := by
  rw [lB, ite_eq_right (by norm_num), lchain]

private theorem lC_zero : lC s a₁ c₁ 0 = 0 := by
  rw [lC, ite_eq_left (by norm_num), lchain]

private theorem lC_one : lC s a₁ c₁ 1 = c₁ := by
  rw [lC, ite_eq_right (by norm_num), lchain]

private theorem lT_even : lT s a₁ c₁ % 2 = 0 := by
  rw [lT]
  omega

private theorem lT_pos (hs : 0 < s) (h1 : 0 < a₁) (h1s : a₁ ≤ s) :
    0 < lT s a₁ c₁ := by
  rw [lT]
  rcases Nat.eq_zero_or_pos (lK s a₁ c₁) with h0 | h
  · exfalso
    have hz := (lK_spec (c₁ := c₁) h1 h1s).1
    rw [h0] at hz
    have h2 : (lchain s a₁ c₁ 0).a0 = s := rfl
    omega
  · omega

private theorem lA_T (h1 : 0 < a₁) (h1s : a₁ ≤ s) :
    lA s a₁ c₁ (lT s a₁ c₁) = 0 := by
  rw [lA, lT, ite_eq_left (by omega)]
  have h2 : 2 * lK s a₁ c₁ / 2 = lK s a₁ c₁ := by omega
  rw [h2, (lK_spec h1 h1s).1]
  norm_num

private theorem lA_pos (h1 : 0 < a₁) (h1s : a₁ ≤ s) :
    ∀ i < lT s a₁ c₁, 0 < lA s a₁ c₁ i := by
  intro i hi
  rw [lT] at hi
  have hne : (lchain s a₁ c₁ (i / 2)).a0 ≠ 0 :=
    (lK_spec h1 h1s).2 (i / 2) (by omega)
  rcases Nat.even_or_odd i with he | ho
  · rw [lA, ite_eq_left (Nat.even_iff.mp he)]
    have := Nat.pos_of_ne_zero hne
    exact_mod_cast this
  · rw [lA, ite_eq_right (by have := Nat.odd_iff.mp ho; omega)]
    have := (lchain_inv h1 h1s (i / 2) hne).1
    exact_mod_cast this

/-- The joint recurrence for the three concrete sequences, with all
quotients at least `1`. -/
private theorem l_rec (h1 : 0 < a₁) (h1s : a₁ ≤ s) :
    ∀ i, i + 2 ≤ lT s a₁ c₁ → ∃ q : ℤ, 1 ≤ q ∧
      lA s a₁ c₁ (i + 2) = lA s a₁ c₁ i - q * lA s a₁ c₁ (i + 1) ∧
      lB s a₁ c₁ (i + 2) = lB s a₁ c₁ i - q * lB s a₁ c₁ (i + 1) ∧
      lC s a₁ c₁ (i + 2) = lC s a₁ c₁ i - q * lC s a₁ c₁ (i + 1) := by
  intro i hi
  rw [lT] at hi
  rcases Nat.even_or_odd i with ⟨k, hk⟩ | ⟨k, hk⟩
  · -- even `i = 2k`: the even substep of the double-step `k → k+1`
    subst hk
    have hk1 : k < lK s a₁ c₁ := by omega
    have h0 : (lchain s a₁ c₁ k).a0 ≠ 0 := (lK_spec h1 h1s).2 k hk1
    obtain ⟨hpos, hle⟩ := lchain_inv (c₁ := c₁) h1 h1s k h0
    have hq1 : 1 ≤ (lchain s a₁ c₁ k).a0 / (lchain s a₁ c₁ k).a1 :=
      Nat.one_le_div_iff hpos |>.mpr hle
    refine ⟨((lchain s a₁ c₁ k).a0 / (lchain s a₁ c₁ k).a1 : ℕ), by
      exact_mod_cast hq1, ?_, ?_, ?_⟩
    · -- `a`-recurrence
      have hidx0 : (k + k) % 2 = 0 := by omega
      have hidx1 : (k + k + 1) % 2 = 1 := by omega
      have hidx2 : (k + k + 2) % 2 = 0 := by omega
      rw [lA, lA, lA, ite_eq_left hidx2, ite_eq_left hidx0, ite_eq_right (by omega),
        show (k + k + 2) / 2 = k + 1 by omega,
        show (k + k) / 2 = k by omega,
        show (k + k + 1) / 2 = k by omega, lchain]
      have hdm := Nat.div_add_mod (lchain s a₁ c₁ k).a0 (lchain s a₁ c₁ k).a1
      have hz : ((lchain s a₁ c₁ k).a1 : ℤ)
          * ((lchain s a₁ c₁ k).a0 / (lchain s a₁ c₁ k).a1 : ℕ)
          + ((lchain s a₁ c₁ k).a0 % (lchain s a₁ c₁ k).a1 : ℕ)
          = ((lchain s a₁ c₁ k).a0 : ℤ) := by exact_mod_cast hdm
      by_cases hγ : (lchain s a₁ c₁ k).a0 % (lchain s a₁ c₁ k).a1 = 0
      · rw [lstep_a0_term h0 hγ]
        rw [hγ] at hz
        push_cast at hz ⊢
        linear_combination hz
      · rw [lstep_a0 h0 hγ]
        linear_combination hz
    · -- `b`-recurrence
      have hidx0 : (k + k) % 2 = 0 := by omega
      have hidx2 : (k + k + 2) % 2 = 0 := by omega
      rw [lB, lB, lB, ite_eq_left hidx2, ite_eq_left hidx0, ite_eq_right (by omega),
        show (k + k + 2) / 2 = k + 1 by omega,
        show (k + k) / 2 = k by omega,
        show (k + k + 1) / 2 = k by omega, lchain, lstep_b0 h0]
    · -- `c`-recurrence
      have hidx0 : (k + k) % 2 = 0 := by omega
      have hidx2 : (k + k + 2) % 2 = 0 := by omega
      rw [lC, lC, lC, ite_eq_left hidx2, ite_eq_left hidx0, ite_eq_right (by omega),
        show (k + k + 2) / 2 = k + 1 by omega,
        show (k + k) / 2 = k by omega,
        show (k + k + 1) / 2 = k by omega, lchain, lstep_c0 h0]
  · -- odd `i = 2k + 1`: the odd substep of the double-step `k → k+1`
    subst hk
    have hk2 : k + 1 < lK s a₁ c₁ := by omega
    have h0 : (lchain s a₁ c₁ k).a0 ≠ 0 :=
      (lK_spec h1 h1s).2 k (by omega)
    have h0' : (lchain s a₁ c₁ (k + 1)).a0 ≠ 0 :=
      (lK_spec h1 h1s).2 (k + 1) hk2
    obtain ⟨hpos, hle⟩ := lchain_inv (c₁ := c₁) h1 h1s k h0
    have hγ : (lchain s a₁ c₁ k).a0 % (lchain s a₁ c₁ k).a1 ≠ 0 := by
      intro hγ0
      rw [lchain, lstep_a0_term h0 hγ0] at h0'
      exact h0' rfl
    have hγlt : (lchain s a₁ c₁ k).a0 % (lchain s a₁ c₁ k).a1
        < (lchain s a₁ c₁ k).a1 := Nat.mod_lt _ hpos
    have hγpos : 0 < (lchain s a₁ c₁ k).a0 % (lchain s a₁ c₁ k).a1 :=
      Nat.pos_of_ne_zero hγ
    have hq1 : 1 ≤ ((lchain s a₁ c₁ k).a1 - 1)
        / ((lchain s a₁ c₁ k).a0 % (lchain s a₁ c₁ k).a1) :=
      Nat.one_le_div_iff hγpos |>.mpr (by omega)
    refine ⟨(((lchain s a₁ c₁ k).a1 - 1)
      / ((lchain s a₁ c₁ k).a0 % (lchain s a₁ c₁ k).a1) : ℕ), by
      exact_mod_cast hq1, ?_, ?_, ?_⟩
    · have hidx1 : (2 * k + 1) % 2 = 1 := by omega
      have hidx3 : (2 * k + 1 + 2) % 2 = 1 := by omega
      rw [lA, lA, lA, ite_eq_right (by omega), ite_eq_right (by omega),
        ite_eq_left (by omega),
        show (2 * k + 1 + 2) / 2 = k + 1 by omega,
        show (2 * k + 1) / 2 = k by omega,
        show (2 * k + 1 + 1) / 2 = k + 1 by omega, lchain,
        lstep_a1 h0 hγ, lstep_a0 h0 hγ]
      have hdm := Nat.div_add_mod ((lchain s a₁ c₁ k).a1 - 1)
        ((lchain s a₁ c₁ k).a0 % (lchain s a₁ c₁ k).a1)
      rw [Nat.mul_comm] at hdm
      obtain ⟨Q, hQ⟩ : ∃ Q, ((lchain s a₁ c₁ k).a1 - 1)
          / ((lchain s a₁ c₁ k).a0 % (lchain s a₁ c₁ k).a1)
          * ((lchain s a₁ c₁ k).a0 % (lchain s a₁ c₁ k).a1) = Q := ⟨_, rfl⟩
      have hQz : ((((lchain s a₁ c₁ k).a1 - 1)
          / ((lchain s a₁ c₁ k).a0 % (lchain s a₁ c₁ k).a1) : ℕ) : ℤ)
          * (((lchain s a₁ c₁ k).a0 % (lchain s a₁ c₁ k).a1 : ℕ) : ℤ)
          = (Q : ℤ) := by exact_mod_cast hQ
      rw [hQ] at hdm
      rw [hQ, hQz]
      omega
    · rw [lB, lB, lB, ite_eq_right (by omega), ite_eq_right (by omega),
        ite_eq_left (by omega),
        show (2 * k + 1 + 2) / 2 = k + 1 by omega,
        show (2 * k + 1) / 2 = k by omega,
        show (2 * k + 1 + 1) / 2 = k + 1 by omega, lchain,
        lstep_b1 h0 hγ, lstep_b0 h0]
    · rw [lC, lC, lC, ite_eq_right (by omega), ite_eq_right (by omega),
        ite_eq_left (by omega),
        show (2 * k + 1 + 2) / 2 = k + 1 by omega,
        show (2 * k + 1) / 2 = k by omega,
        show (2 * k + 1 + 1) / 2 = k + 1 by omega, lchain,
        lstep_c1 h0 hγ, lstep_c0 h0]

end Bridge

/-! ### The congruence (4.20) and the main theorem -/

/-- The congruence (4.20), abstractly: a quantity satisfying the same
recurrence as the `cᵢ` and agreeing with them modulo `s` at the two
base indices agrees modulo `s` everywhere. -/
private theorem congruence_chain {s : ℕ} {A B C : ℕ → ℤ} {t : ℕ}
    (hrec : ∀ i, i + 2 ≤ t → ∃ q : ℤ, 1 ≤ q ∧
      A (i + 2) = A i - q * A (i + 1) ∧ B (i + 2) = B i - q * B (i + 1) ∧
      C (i + 2) = C i - q * C (i + 1))
    {x y : ℤ} (h0 : (s : ℤ) ∣ x * A 0 + y * B 0 - C 0)
    (h1 : (s : ℤ) ∣ x * A 1 + y * B 1 - C 1) :
    ∀ i ≤ t, (s : ℤ) ∣ x * A i + y * B i - C i := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hit
    match i with
    | 0 => exact h0
    | 1 => exact h1
    | (j + 2) =>
      obtain ⟨q, _, hA, hB, hC⟩ := hrec j hit
      have d0 := ih j (by omega) (by omega)
      have d1 := ih (j + 1) (by omega) (by omega)
      have hkey : x * A (j + 2) + y * B (j + 2) - C (j + 2)
          = (x * A j + y * B j - C j)
            - q * (x * A (j + 1) + y * B (j + 1) - C (j + 1)) := by
        rw [hA, hB, hC]
        ring
      rw [hkey]
      exact dvd_sub d0 (Dvd.dvd.mul_left d1 q)

/-! ### Theorem 4.2.12 -/

/-- **The congruence (4.20)** for the concrete chain, with the
CORRECTED initialization `c₁ = r*·(n − rr')/s`: for any divisor pair
`(xs + r)(ys + r') = n`, the value `xaᵢ + ybᵢ` is `≡ cᵢ (mod s)` at
every index.  This is what lets Algorithm 4.2.11 enumerate only
`c ≡ cᵢ (mod s)` in each window. -/
theorem lenstra_congruence {n r s rs r' a₁ : ℕ} {c₁ : ℤ}
    (hs1 : 1 < s) (hinv : r * rs % s = 1)
    (hr' : r' = n * rs % s) (ha₁ : a₁ = r' * rs % s)
    (hc₁ : c₁ = (rs : ℤ) * (((n : ℤ) - r * r') / s))
    (h1 : 0 < a₁) (h1s : a₁ ≤ s)
    {x y : ℕ} (hprod : (x * s + r) * (y * s + r') = n) :
    ∀ i ≤ lT s a₁ c₁,
      (s : ℤ) ∣ (x : ℤ) * lA s a₁ c₁ i + y * lB s a₁ c₁ i
        - lC s a₁ c₁ i := by
  refine congruence_chain (l_rec (c₁ := c₁) h1 h1s) ?_ ?_
  · rw [lA_zero, lB_zero, lC_zero]
    exact ⟨x, by ring⟩
  · rw [lA_one, lB_one, lC_one]
    -- `s ∣ n − rr'`, and the exact division defining `c₁`
    have hmodeq : r * r' ≡ n [MOD s] := by
      calc r * r' ≡ r * (n * rs) [MOD s] := by
            refine Nat.ModEq.mul_left r ?_
            rw [hr']
            exact Nat.mod_modEq _ _
      _ = n * (r * rs) := by ring
      _ ≡ n * 1 [MOD s] := by
            refine Nat.ModEq.mul_left n ?_
            unfold Nat.ModEq
            rw [hinv, Nat.mod_eq_of_lt hs1]
      _ = n := by ring
    have hdvd_nr : (s : ℤ) ∣ (n : ℤ) - r * r' := by
      have h0 := hmodeq.dvd
      push_cast at h0
      exact h0
    have hM : (s : ℤ) * (((n : ℤ) - r * r') / s) = (n : ℤ) - r * r' :=
      Int.mul_ediv_cancel' hdvd_nr
    have hprodz : ((x : ℤ) * s + r) * ((y : ℤ) * s + r') = n := by
      exact_mod_cast hprod
    have hMval : ((n : ℤ) - r * r') / s
        = (x : ℤ) * y * s + x * r' + y * r := by
      refine mul_left_cancel₀ (show (s : ℤ) ≠ 0 by omega) ?_
      rw [hM]
      linear_combination -hprodz
    have hk₁ : r' * rs = s * (r' * rs / s) + a₁ := by
      rw [ha₁]
      exact (Nat.div_add_mod _ _).symm
    have hk₂ : r * rs = s * (r * rs / s) + 1 := by
      conv_lhs => rw [← Nat.div_add_mod (r * rs) s]
      rw [hinv]
    have hk₁z : (r' : ℤ) * rs = s * ((r' * rs / s : ℕ) : ℤ) + a₁ := by
      exact_mod_cast hk₁
    have hk₂z : (r : ℤ) * rs = s * ((r * rs / s : ℕ) : ℤ) + 1 := by
      exact_mod_cast hk₂
    rw [hc₁, hMval]
    refine ⟨-(x : ℤ) * (r' * rs / s : ℕ) - y * (r * rs / s : ℕ)
      - rs * x * y, ?_⟩
    linear_combination (-(x : ℤ)) * hk₁z - (y : ℤ) * hk₂z

/-- **Crandall–Pomerance Theorem 4.2.12 (Lenstra), corrected**: the
divisors of `n` congruent to `r (mod s)` are exactly the numbers
`xs + r` arising from nonnegative solutions of the system (4.16) whose
value `c = xaᵢ + ybᵢ` lies in a window — `|c| < s` at an even index,
or `2aᵢbᵢ ≤ c < aᵢbᵢ + n/s²` at an odd index (left end CLOSED,
correcting the book).  Together with `lenstra_congruence`, this is the
correctness of Algorithm 4.2.11. -/
theorem theorem_4_2_12 {n r s rs r' a₁ : ℕ} {c₁ : ℤ} (hr : 0 < r)
    (hrs : r < s) (hsn : s < n) (hinv : r * rs % s = 1) (hns : ¬s ∣ n)
    (hr' : r' = n * rs % s) (ha₁ : a₁ = r' * rs % s)
    (_hc₁ : c₁ = (rs : ℤ) * (((n : ℤ) - r * r') / s)) (d : ℕ) :
    d ∣ n ∧ d % s = r ↔
      ∃ x y : ℕ, d = x * s + r ∧ (x * s + r) * (y * s + r') = n ∧
        ∃ i ≤ lT s a₁ c₁,
          (i % 2 = 0 ∧
            |(x : ℤ) * lA s a₁ c₁ i + y * lB s a₁ c₁ i| < s) ∨
          (i % 2 = 1 ∧
            2 * (lA s a₁ c₁ i * lB s a₁ c₁ i)
              ≤ (x : ℤ) * lA s a₁ c₁ i + y * lB s a₁ c₁ i ∧
            (s : ℤ) ^ 2 * ((x : ℤ) * lA s a₁ c₁ i + y * lB s a₁ c₁ i
              - lA s a₁ c₁ i * lB s a₁ c₁ i) < n) := by
  have hs1 : 1 < s := by omega
  have hs0 : 0 < s := by omega
  -- `rs` is invertible mod `s`, hence `r', a₁ ∈ (0, s)`
  have hrs_cop : Nat.Coprime rs s := by
    have h3' : r * rs = s * (r * rs / s) + 1 := by
      conv_lhs => rw [← Nat.div_add_mod (r * rs) s]
      rw [hinv]
    have h1' : Nat.gcd rs s ∣ r * rs :=
      Dvd.dvd.mul_left (Nat.gcd_dvd_left rs s) r
    have h2' : Nat.gcd rs s ∣ s * (r * rs / s) :=
      Dvd.dvd.mul_right (Nat.gcd_dvd_right rs s) _
    have hg : Nat.gcd rs s ∣ 1 := by
      have := Nat.dvd_sub h1' h2'
      rwa [show r * rs - s * (r * rs / s) = 1 by omega] at this
    exact Nat.dvd_one.mp hg
  have hr'lt : r' < s := by
    rw [hr']
    exact Nat.mod_lt _ hs0
  have hr'pos : 0 < r' := by
    rcases Nat.eq_zero_or_pos r' with h0 | h
    · exfalso
      rw [hr'] at h0
      have hdvd : s ∣ n * rs := Nat.dvd_of_mod_eq_zero h0
      exact hns (hrs_cop.symm.dvd_of_dvd_mul_right hdvd)
    · exact h
  have ha₁lt : a₁ < s := by
    rw [ha₁]
    exact Nat.mod_lt _ hs0
  have ha₁pos : 0 < a₁ := by
    rcases Nat.eq_zero_or_pos a₁ with h0 | h
    · exfalso
      rw [ha₁] at h0
      have hdvd : s ∣ r' * rs := Nat.dvd_of_mod_eq_zero h0
      have hsr' : s ∣ r' := hrs_cop.symm.dvd_of_dvd_mul_right hdvd
      have := Nat.le_of_dvd hr'pos hsr'
      omega
    · exact h
  constructor
  · rintro ⟨hdvd, hmod⟩
    obtain ⟨e, he⟩ := hdvd
    have hd0 : 0 < d := by
      rcases Nat.eq_zero_or_pos d with h0 | h
      · rw [h0, Nat.zero_mod] at hmod
        omega
      · exact h
    have he0 : 0 < e := by
      rcases Nat.eq_zero_or_pos e with h0 | h
      · rw [h0, mul_zero] at he
        omega
      · exact h
    have hx : d = d / s * s + r := by
      have h1' := Nat.div_add_mod d s
      have h2' : d / s * s = s * (d / s) := Nat.mul_comm _ _
      omega
    -- `e ≡ r' (mod s)` via `ZMod s`
    have hemod : e % s = r' := by
      have hdz : ((d : ℕ) : ZMod s) = ((r : ℕ) : ZMod s) :=
        (ZMod.natCast_eq_natCast_iff _ _ _).mpr (by
          unfold Nat.ModEq
          rw [hmod, Nat.mod_eq_of_lt hrs])
      have hiz : ((r * rs : ℕ) : ZMod s) = ((1 : ℕ) : ZMod s) :=
        (ZMod.natCast_eq_natCast_iff _ _ _).mpr (by
          unfold Nat.ModEq
          rw [hinv, Nat.mod_eq_of_lt hs1])
      have hez : ((e : ℕ) : ZMod s) = ((n * rs : ℕ) : ZMod s) := by
        push_cast at hdz hiz ⊢
        calc (e : ZMod s) = e * ((r : ZMod s) * rs) := by
              rw [hiz]
              ring
        _ = ((d : ZMod s) * e) * rs := by
              rw [hdz]
              ring
        _ = (n : ZMod s) * rs := by
              rw [show ((d : ZMod s)) * e = ((n : ℕ) : ZMod s) from by
                rw [he]
                push_cast
                ring]
      have hfin := (ZMod.natCast_eq_natCast_iff _ _ _).mp hez
      rw [hr']
      exact hfin
    have hy : e = e / s * s + r' := by
      have h1' := Nat.div_add_mod e s
      have h2' : e / s * s = s * (e / s) := Nat.mul_comm _ _
      omega
    have hprod : (d / s * s + r) * (e / s * s + r') = n := by
      rw [← hx, ← hy, he]
    -- the window walk
    have hrecAB : ∀ i, i + 2 ≤ lT s a₁ c₁ → ∃ q : ℤ, 1 ≤ q ∧
        lA s a₁ c₁ (i + 2) = lA s a₁ c₁ i - q * lA s a₁ c₁ (i + 1) ∧
        lB s a₁ c₁ (i + 2) = lB s a₁ c₁ i - q * lB s a₁ c₁ (i + 1) := by
      intro i hi
      obtain ⟨q, hq, hA, hB, -⟩ := l_rec (c₁ := c₁) ha₁pos ha₁lt.le i hi
      exact ⟨q, hq, hA, hB⟩
    obtain ⟨i, hi, hwin⟩ := window_walk (A := lA s a₁ c₁) (B := lB s a₁ c₁)
      hs0 lA_zero lB_zero lB_one lT_even
      (lT_pos hs0 ha₁pos ha₁lt.le) (lA_T ha₁pos ha₁lt.le)
      (lA_pos ha₁pos ha₁lt.le) hrecAB
      (x := (d / s : ℕ)) (y := (e / s : ℕ)) (by positivity) (by positivity)
    refine ⟨d / s, e / s, hx, hprod, i, hi, ?_⟩
    rcases hwin with ⟨hev, habs⟩ | ⟨hodd, hlow, hup⟩
    · exact Or.inl ⟨hev, habs⟩
    · refine Or.inr ⟨hodd, hlow, ?_⟩
      -- `s²(c − ab) ≤ s²xy < n`
      have hprodz : ((d / s : ℕ) * (s : ℤ) + r)
          * ((e / s : ℕ) * (s : ℤ) + r') = n := by
        exact_mod_cast hprod
      have hxys : (s : ℤ) ^ 2 * ((d / s : ℕ) * (e / s : ℕ)) < n := by
        have h1' : 0 ≤ ((d / s : ℕ) : ℤ) * r' * s := by positivity
        have h2' : 0 ≤ ((e / s : ℕ) : ℤ) * r * s := by positivity
        have h3' : (1 : ℤ) ≤ (r : ℤ) * r' := by
          have : (1 : ℤ) * 1 ≤ (r : ℤ) * r' :=
            mul_le_mul (by exact_mod_cast hr) (by exact_mod_cast hr'pos)
              (by norm_num) (by positivity)
          omega
        nlinarith [hprodz]
      have hmono : (s : ℤ) ^ 2 * ((d / s : ℕ) * lA s a₁ c₁ i
          + (e / s : ℕ) * lB s a₁ c₁ i - lA s a₁ c₁ i * lB s a₁ c₁ i)
          ≤ (s : ℤ) ^ 2 * ((d / s : ℕ) * (e / s : ℕ)) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        omega
      omega
  · rintro ⟨x, y, hd, hprod, -⟩
    constructor
    · exact ⟨y * s + r', by rw [hd, ← hprod]⟩
    · rw [hd, Nat.mul_add_mod', Nat.mod_eq_of_lt hrs]

section Example

-- `(n, r, s) = (91, 2, 5)`, `rs = 3`: `r' = 3`, `a₁ = 4`,
-- corrected `c₁ = 3·(91 − 6)/5 = 51`; the chain is
-- `a = (5, 4, 1, 1, 0)`, `b = (0, 1, −1, 4, −5)`, `t = 4`.
example : lT 5 4 51 = 4 := by decide

example : lA 5 4 51 2 = 1 ∧ lB 5 4 51 2 = -1 ∧ lB 5 4 51 4 = -5 := by
  decide

-- the divisor `7 = 1·5 + 2` of `91` (cofactor `13 = 2·5 + 3`) is
-- caught by the even window at `i = 2`, where `S₂ = 1·1 + 2·(−1) = −1`
example : |(1 : ℤ) * lA 5 4 51 2 + 2 * lB 5 4 51 2| < 5 := by decide

-- and the congruence (4.20) holds there: `S₂ ≡ c₂ (mod 5)`
example : (5 : ℤ) ∣ (1 : ℤ) * lA 5 4 51 2 + 2 * lB 5 4 51 2
    - lC 5 4 51 2 := by decide

-- the full statement, instantiated: `7` is discovered
example : ∃ x y : ℕ, 7 = x * 5 + 2 ∧ (x * 5 + 2) * (y * 5 + 3) = 91 ∧
    ∃ i ≤ lT 5 4 51,
      (i % 2 = 0 ∧ |(x : ℤ) * lA 5 4 51 i + y * lB 5 4 51 i| < 5) ∨
      (i % 2 = 1 ∧ 2 * (lA 5 4 51 i * lB 5 4 51 i)
          ≤ (x : ℤ) * lA 5 4 51 i + y * lB 5 4 51 i ∧
        (5 : ℤ) ^ 2 * ((x : ℤ) * lA 5 4 51 i + y * lB 5 4 51 i
          - lA 5 4 51 i * lB 5 4 51 i) < 91) := by
  have h := (theorem_4_2_12 (n := 91) (r := 2) (s := 5) (rs := 3)
    (r' := 3) (a₁ := 4) (c₁ := 51) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) 7).mp ⟨by norm_num, by norm_num⟩
  exact h

end Example

/-! ### The computable Algorithm 4.2.11 -/

/-- Integer square-root test: `some w` (with `w ≥ 0`) iff `D = w²`. -/
def intSqrt? (D : ℤ) : Option ℤ :=
  if D < 0 then none
  else if Nat.sqrt D.toNat * Nat.sqrt D.toNat = D.toNat
    then some (Nat.sqrt D.toNat) else none

/-- Verify a candidate `u` and report it as a divisor: the checks are
exactly the reported property, so soundness of the whole algorithm is
immediate. -/
def reportIfDivisor (n r s : ℕ) (u : ℤ) : List ℕ :=
  if 0 < u ∧ u.toNat ∣ n ∧ u.toNat % s = r then [u.toNat] else []

/-- Solve the system (4.16) at one `(i, c)`: `xaᵢ + ybᵢ = c`,
`(xs + r)(ys + r') = n`.  For `aᵢ ≠ 0`, substituting `u = xs + r`
gives the quadratic `aᵢu² − Ru + bᵢn = 0` with
`R = cs + aᵢr + bᵢr'`, whose discriminant must be the square
`(2aᵢu − R)²`; for `aᵢ = 0` (only at `i = t`) the system is linear
in `y`.  Every candidate root is verified before being reported. -/
def solveSystem (n r r' s : ℕ) (a b c : ℤ) : List ℕ :=
  if a = 0 then
    if b = 0 then []
    else if b ∣ c ∧ 0 ≤ c / b then
      if 0 < c / b * (s : ℤ) + r' ∧ (c / b * (s : ℤ) + r').toNat ∣ n then
        reportIfDivisor n r s ((n / (c / b * (s : ℤ) + r').toNat : ℕ) : ℤ)
      else []
    else []
  else
    match intSqrt? ((c * s + a * r + b * r') ^ 2 - 4 * a * b * n) with
    | none => []
    | some w =>
      (if 2 * a ∣ c * s + a * r + b * r' + w then
        reportIfDivisor n r s ((c * s + a * r + b * r' + w) / (2 * a))
       else []) ++
      (if 2 * a ∣ c * s + a * r + b * r' - w then
        reportIfDivisor n r s ((c * s + a * r + b * r' - w) / (2 * a))
       else [])

/-- The candidates `c ≡ cᵢ (mod s)` in the even window `(−s, s)`. -/
def evenWindow (s : ℕ) (cᵢ : ℤ) : List ℤ :=
  if cᵢ % s = 0 then [0] else [cᵢ % s, cᵢ % s - s]

/-- The candidates `c ≡ cᵢ (mod s)` in the (corrected, left-closed)
odd window `2aᵢbᵢ ≤ c < aᵢbᵢ + n/s²`. -/
def oddWindow (n s : ℕ) (a b cᵢ : ℤ) : List ℤ :=
  (List.range (n / s ^ 3 + 1)).filterMap fun (j : ℕ) =>
    if (s : ℤ) ^ 2 * ((2 * (a * b) + (cᵢ - 2 * (a * b)) % s + (j : ℤ) * s)
        - a * b) < n
    then some (2 * (a * b) + (cᵢ - 2 * (a * b)) % s + (j : ℤ) * s)
    else none

/-- **Algorithm 4.2.11 (corrected)**: the list of all divisors of `n`
congruent to `r (mod s)`, given a modular inverse `rs` of `r` mod `s`
(possibly with repetitions; `mem_lenstraDivisors` is the spec). -/
def lenstraChainArgs (n r s rs : ℕ) : ℕ × ℤ :=
  (n * rs % s * rs % s,
    (rs : ℤ) * (((n : ℤ) - r * ((n * rs % s : ℕ) : ℤ)) / s))

def lenstraDivisors (n r s rs : ℕ) : List ℕ :=
  (List.range (lT s (lenstraChainArgs n r s rs).1
      (lenstraChainArgs n r s rs).2 + 1)).flatMap fun i =>
    ((if i % 2 = 0 then
        evenWindow s (lC s (lenstraChainArgs n r s rs).1
          (lenstraChainArgs n r s rs).2 i)
      else oddWindow n s
        (lA s (lenstraChainArgs n r s rs).1 (lenstraChainArgs n r s rs).2 i)
        (lB s (lenstraChainArgs n r s rs).1 (lenstraChainArgs n r s rs).2 i)
        (lC s (lenstraChainArgs n r s rs).1
          (lenstraChainArgs n r s rs).2 i)).flatMap
      fun c => solveSystem n r (n * rs % s) s
        (lA s (lenstraChainArgs n r s rs).1 (lenstraChainArgs n r s rs).2 i)
        (lB s (lenstraChainArgs n r s rs).1 (lenstraChainArgs n r s rs).2 i)
        c)

section AlgorithmSpec

/-- Membership in `reportIfDivisor`, unfolded. -/
private theorem mem_reportIfDivisor {n r s : ℕ} {u : ℤ} {d : ℕ} :
    d ∈ reportIfDivisor n r s u ↔
      (0 < u ∧ u.toNat ∣ n ∧ u.toNat % s = r) ∧ d = u.toNat := by
  rw [reportIfDivisor]
  split_ifs with h
  · simp [h]
  · simp [h]

/-- Soundness of the solver: everything reported is a divisor in the
right class. -/
private theorem solveSystem_sound {n r r' s : ℕ} {a b c : ℤ} {d : ℕ}
    (hd : d ∈ solveSystem n r r' s a b c) : d ∣ n ∧ d % s = r := by
  rw [solveSystem] at hd
  by_cases ha : a = 0
  · rw [ite_eq_left ha] at hd
    by_cases hb : b = 0
    · rw [ite_eq_left hb] at hd
      exact absurd hd List.not_mem_nil
    · rw [ite_eq_right hb] at hd
      by_cases hbc : b ∣ c ∧ 0 ≤ c / b
      · rw [ite_eq_left hbc] at hd
        by_cases hv : 0 < c / b * (s : ℤ) + r'
            ∧ (c / b * (s : ℤ) + r').toNat ∣ n
        · rw [ite_eq_left hv] at hd
          obtain ⟨⟨-, h5, h6⟩, rfl⟩ := mem_reportIfDivisor.mp hd
          exact ⟨h5, h6⟩
        · rw [ite_eq_right hv] at hd
          exact absurd hd List.not_mem_nil
      · rw [ite_eq_right hbc] at hd
        exact absurd hd List.not_mem_nil
  · rw [ite_eq_right ha] at hd
    rcases hmatch : intSqrt? ((c * s + a * r + b * r') ^ 2
        - 4 * a * b * n) with - | w
    · rw [hmatch] at hd
      exact absurd hd List.not_mem_nil
    · rw [hmatch] at hd
      rcases List.mem_append.mp hd with h | h <;> split_ifs at h with h'
      · obtain ⟨⟨-, h5, h6⟩, rfl⟩ := mem_reportIfDivisor.mp h
        exact ⟨h5, h6⟩
      · exact absurd h List.not_mem_nil
      · obtain ⟨⟨-, h5, h6⟩, rfl⟩ := mem_reportIfDivisor.mp h
        exact ⟨h5, h6⟩
      · exact absurd h List.not_mem_nil

/-- `Nat.sqrt` is exact on squares. -/
private theorem nat_sqrt_sq (a : ℕ) : Nat.sqrt (a * a) = a := by
  have h1 : a ≤ Nat.sqrt (a * a) := Nat.le_sqrt.mpr (le_refl _)
  have h2 : Nat.sqrt (a * a) < a + 1 := by
    rw [Nat.sqrt_lt]
    nlinarith
  omega

/-- `intSqrt?` detects every square. -/
private theorem intSqrt_sq (z : ℤ) : intSqrt? (z ^ 2) = some |z| := by
  rw [intSqrt?]
  have h0 : (z ^ 2).toNat = z.natAbs * z.natAbs := by
    have h1 : ((z.natAbs * z.natAbs : ℕ) : ℤ) = z * z :=
      Int.natAbs_mul_self
    rw [sq, ← h1, Int.toNat_natCast]
  rw [ite_eq_right (not_lt.mpr (sq_nonneg z)), h0, nat_sqrt_sq, ite_eq_left rfl]
  congr 1
  rw [Int.abs_eq_natAbs]

/-- Completeness of the solver: any nonnegative solution of the
system (4.16) is found and reported. -/
private theorem solveSystem_complete {n r r' s : ℕ} {a b c : ℤ}
    {x y : ℕ} (hr : 0 < r) (hrs : r < s) (hr'0 : 0 < r')
    (ha : 0 ≤ a) (hab : a = 0 → b ≠ 0)
    (hlin : (x : ℤ) * a + y * b = c)
    (hprod : (x * s + r) * (y * s + r') = n) :
    x * s + r ∈ solveSystem n r r' s a b c := by
  have hs0 : 0 < s := by omega
  have hdvd : (x * s + r) ∣ n := ⟨y * s + r', hprod.symm⟩
  have hmod : (x * s + r) % s = r := by
    rw [Nat.mul_add_mod', Nat.mod_eq_of_lt hrs]
  have hutoNat : (((x : ℤ) * s + r)).toNat = x * s + r := by
    rw [show (x : ℤ) * s + r = ((x * s + r : ℕ) : ℤ) by push_cast; ring,
      Int.toNat_natCast]
  rw [solveSystem]
  by_cases ha0 : a = 0
  · rw [ite_eq_left ha0, ite_eq_right (hab ha0)]
    have hyb : (y : ℤ) * b = c := by
      rw [← hlin, ha0]
      ring
    have hcb : c / b = y := by
      rw [← hyb, Int.mul_ediv_cancel _ (hab ha0)]
    rw [ite_eq_left ⟨⟨y, by rw [← hyb]; ring⟩, by rw [hcb]; positivity⟩, hcb]
    have hv : ((y : ℤ) * s + r').toNat = y * s + r' := by
      rw [show (y : ℤ) * s + r' = ((y * s + r' : ℕ) : ℤ) by push_cast; ring,
        Int.toNat_natCast]
    have hvpos : (0 : ℤ) < (y : ℤ) * s + r' := by positivity
    have hvdvd : ((y : ℤ) * s + r').toNat ∣ n := by
      rw [hv]
      exact ⟨x * s + r, by rw [← hprod]; ring⟩
    rw [ite_eq_left ⟨hvpos, hvdvd⟩, hv]
    have hquot : n / (y * s + r') = x * s + r := by
      rw [← hprod, Nat.mul_comm]
      exact Nat.mul_div_cancel_left _ (by positivity)
    rw [hquot, mem_reportIfDivisor]
    have htn : (((x * s + r : ℕ) : ℤ)).toNat = x * s + r :=
      Int.toNat_natCast _
    exact ⟨⟨by positivity, by rw [htn]; exact hdvd,
      by rw [htn]; exact hmod⟩, htn.symm⟩
  · rw [ite_eq_right ha0]
    have hapos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
    have hprodz : ((x : ℤ) * s + r) * ((y : ℤ) * s + r') = n := by
      exact_mod_cast hprod
    have hquad : a * ((x : ℤ) * s + r) ^ 2
        - (c * s + a * r + b * r') * ((x : ℤ) * s + r) + b * n = 0 := by
      linear_combination (-(b : ℤ)) * hprodz
        + ((x : ℤ) * s + r) * s * hlin
    have hD : (c * s + a * r + b * r') ^ 2 - 4 * a * b * n
        = (2 * a * ((x : ℤ) * s + r) - (c * s + a * r + b * r')) ^ 2 := by
      linear_combination (-4 * (a : ℤ)) * hquad
    rw [hD, intSqrt_sq]
    have humem : (((x : ℤ) * s + r)).toNat ∈
        reportIfDivisor n r s ((x : ℤ) * s + r) := by
      rw [mem_reportIfDivisor]
      exact ⟨⟨by positivity, by rw [hutoNat]; exact hdvd,
        by rw [hutoNat]; exact hmod⟩, rfl⟩
    by_cases hsgn : c * s + a * r + b * r' ≤ 2 * a * ((x : ℤ) * s + r)
    · have habs : |2 * a * ((x : ℤ) * s + r) - (c * s + a * r + b * r')|
          = 2 * a * ((x : ℤ) * s + r) - (c * s + a * r + b * r') :=
        abs_of_nonneg (by omega)
      rw [habs]
      refine List.mem_append.mpr (Or.inl ?_)
      have hRw : c * s + a * r + b * r'
          + (2 * a * ((x : ℤ) * s + r) - (c * s + a * r + b * r'))
          = 2 * a * ((x : ℤ) * s + r) := by ring
      rw [ite_eq_left (by rw [hRw]; exact ⟨(x : ℤ) * s + r, by ring⟩)]
      rw [hRw, Int.mul_ediv_cancel_left _ (by omega : (2 : ℤ) * a ≠ 0)]
      rw [hutoNat] at humem
      exact humem
    · have habs : |2 * a * ((x : ℤ) * s + r) - (c * s + a * r + b * r')|
          = c * s + a * r + b * r' - 2 * a * ((x : ℤ) * s + r) := by
        rw [abs_of_neg (by omega)]
        ring
      rw [habs]
      refine List.mem_append.mpr (Or.inr ?_)
      have hRw : c * s + a * r + b * r'
          - (c * s + a * r + b * r' - 2 * a * ((x : ℤ) * s + r))
          = 2 * a * ((x : ℤ) * s + r) := by ring
      rw [ite_eq_left (by rw [hRw]; exact ⟨(x : ℤ) * s + r, by ring⟩)]
      rw [hRw, Int.mul_ediv_cancel_left _ (by omega : (2 : ℤ) * a ≠ 0)]
      rw [hutoNat] at humem
      exact humem

/-- Completeness of the even-window enumeration. -/
private theorem mem_evenWindow {s : ℕ} (hs : 0 < s) {cᵢ S : ℤ}
    (hcong : (s : ℤ) ∣ S - cᵢ) (habs : |S| < s) :
    S ∈ evenWindow s cᵢ := by
  have hsz : (0 : ℤ) < s := by exact_mod_cast hs
  have h0 : (0 : ℤ) ≤ cᵢ % s := Int.emod_nonneg cᵢ (by omega)
  have h1 : cᵢ % s < s := Int.emod_lt_of_pos cᵢ hsz
  have hcong2 : (s : ℤ) ∣ S - cᵢ % s := by
    have hdd : (s : ℤ) ∣ cᵢ - cᵢ % s := ⟨cᵢ / s, by
      rw [Int.emod_def]
      ring⟩
    have := dvd_add hcong hdd
    rwa [show S - cᵢ + (cᵢ - cᵢ % s) = S - cᵢ % s by ring] at this
  obtain ⟨k, hk⟩ := hcong2
  have habs' : -(s : ℤ) < S ∧ S < s := abs_lt.mp habs
  have hk01 : k = 0 ∨ k = -1 := by
    rcases lt_trichotomy k (-1) with h | h | h
    · exfalso
      have hk2 : k ≤ -2 := by omega
      have : (s : ℤ) * k ≤ s * (-2) :=
        mul_le_mul_of_nonneg_left hk2 (by omega)
      omega
    · right
      exact h
    · rcases lt_trichotomy k 0 with h' | h' | h'
      · omega
      · left
        exact h'
      · exfalso
        have hk1 : 1 ≤ k := by omega
        have : (s : ℤ) * 1 ≤ s * k :=
          mul_le_mul_of_nonneg_left hk1 (by omega)
        omega
  rw [evenWindow]
  rcases hk01 with rfl | rfl
  · have hS : S = cᵢ % s := by omega
    split_ifs with hr₀
    · simp [hS, hr₀]
    · simp [hS]
  · have hS : S = cᵢ % s - s := by omega
    have hr₀ : cᵢ % s ≠ 0 := by
      intro h
      rw [h] at hS
      omega
    rw [ite_eq_right hr₀]
    simp [hS]

/-- Completeness of the odd-window enumeration. -/
private theorem mem_oddWindow {n s : ℕ} (hs : 0 < s) {a b cᵢ S : ℤ}
    (hab : 0 ≤ a * b) (hcong : (s : ℤ) ∣ S - cᵢ)
    (hlow : 2 * (a * b) ≤ S)
    (hup : (s : ℤ) ^ 2 * (S - a * b) < n) : S ∈ oddWindow n s a b cᵢ := by
  have hsz : (0 : ℤ) < s := by exact_mod_cast hs
  have h0 : (0 : ℤ) ≤ (cᵢ - 2 * (a * b)) % s :=
    Int.emod_nonneg _ (by omega)
  have h1 : (cᵢ - 2 * (a * b)) % s < s := Int.emod_lt_of_pos _ hsz
  -- `S ≡ c₀ := 2ab + (cᵢ − 2ab) % s (mod s)` and `S ≥ c₀`
  have hcong2 : (s : ℤ) ∣ S - (2 * (a * b) + (cᵢ - 2 * (a * b)) % s) := by
    have hdd : (s : ℤ) ∣ (cᵢ - 2 * (a * b)) - (cᵢ - 2 * (a * b)) % s :=
      ⟨(cᵢ - 2 * (a * b)) / s, by
        rw [Int.emod_def]
        ring⟩
    have := dvd_add hcong hdd
    rwa [show S - cᵢ + ((cᵢ - 2 * (a * b)) - (cᵢ - 2 * (a * b)) % s)
        = S - (2 * (a * b) + (cᵢ - 2 * (a * b)) % s) by ring] at this
  obtain ⟨k, hk⟩ := hcong2
  have hcomm : (s : ℤ) * k = k * s := mul_comm _ _
  have hk0 : 0 ≤ k := by
    by_contra h
    push Not at h
    have hk1 : k ≤ -1 := by omega
    have : (s : ℤ) * k ≤ s * (-1) :=
      mul_le_mul_of_nonneg_left hk1 (by omega)
    omega
  -- the index and its bound
  have hSk : S = 2 * (a * b) + (cᵢ - 2 * (a * b)) % s + k * s := by omega
  have hkbound : k.toNat < n / s ^ 3 + 1 := by
    have hks : k * s ≤ S - 2 * (a * b) := by omega
    have hSab : S - 2 * (a * b) ≤ S - a * b := by omega
    have hs2 : (0 : ℤ) ≤ (s : ℤ) ^ 2 := by positivity
    have hchain : (s : ℤ) ^ 2 * (k * s) ≤ (s : ℤ) ^ 2 * (S - a * b) :=
      mul_le_mul_of_nonneg_left (by omega) hs2
    have hlt : k * (s : ℤ) ^ 3 < n := by nlinarith
    have hltN : k.toNat * s ^ 3 < n := by
      have hcast : ((k.toNat * s ^ 3 : ℕ) : ℤ) < ((n : ℕ) : ℤ) := by
        push_cast
        rw [Int.toNat_of_nonneg hk0]
        linarith [hlt]
      exact_mod_cast hcast
    have : k.toNat ≤ n / s ^ 3 :=
      Nat.le_div_iff_mul_le (by positivity) |>.mpr hltN.le
    omega
  rw [oddWindow]
  refine List.mem_filterMap.mpr ⟨k.toNat, List.mem_range.mpr hkbound, ?_⟩
  have hkc : (k.toNat : ℤ) = k := Int.toNat_of_nonneg hk0
  rw [show 2 * (a * b) + (cᵢ - 2 * (a * b)) % s + (k.toNat : ℤ) * s = S by
    rw [hkc]; omega]
  rw [ite_eq_left hup]

/-- **Correctness of the computable Algorithm 4.2.11**: under the
hypotheses of Theorem 4.2.12, the list `lenstraDivisors n r s rs`
contains exactly the divisors of `n` congruent to `r (mod s)`. -/
theorem mem_lenstraDivisors {n r s rs : ℕ} (hr : 0 < r) (hrs : r < s)
    (hsn : s < n) (hinv : r * rs % s = 1) (hns : ¬s ∣ n) {d : ℕ} :
    d ∈ lenstraDivisors n r s rs ↔ d ∣ n ∧ d % s = r := by
  have hs0 : 0 < s := by omega
  have hs1 : 1 < s := by omega
  constructor
  · intro hd
    rw [lenstraDivisors] at hd
    obtain ⟨i, -, hd⟩ := List.mem_flatMap.mp hd
    obtain ⟨c, -, hd⟩ := List.mem_flatMap.mp hd
    exact solveSystem_sound hd
  · intro hdd
    -- the chain parameters and their bounds
    have hrs_cop : Nat.Coprime rs s := by
      have h3' : r * rs = s * (r * rs / s) + 1 := by
        conv_lhs => rw [← Nat.div_add_mod (r * rs) s]
        rw [hinv]
      have h1' : Nat.gcd rs s ∣ r * rs :=
        Dvd.dvd.mul_left (Nat.gcd_dvd_left rs s) r
      have h2' : Nat.gcd rs s ∣ s * (r * rs / s) :=
        Dvd.dvd.mul_right (Nat.gcd_dvd_right rs s) _
      have hg : Nat.gcd rs s ∣ 1 := by
        have := Nat.dvd_sub h1' h2'
        rwa [show r * rs - s * (r * rs / s) = 1 by omega] at this
      exact Nat.dvd_one.mp hg
    have hr'lt : n * rs % s < s := Nat.mod_lt _ hs0
    have hr'pos : 0 < n * rs % s := by
      rcases Nat.eq_zero_or_pos (n * rs % s) with h0 | h
      · exact absurd (hrs_cop.symm.dvd_of_dvd_mul_right
          (Nat.dvd_of_mod_eq_zero h0)) hns
      · exact h
    have ha₁lt : n * rs % s * rs % s < s := Nat.mod_lt _ hs0
    have ha₁pos : 0 < n * rs % s * rs % s := by
      rcases Nat.eq_zero_or_pos (n * rs % s * rs % s) with h0 | h
      · exfalso
        have hsr' : s ∣ n * rs % s := hrs_cop.symm.dvd_of_dvd_mul_right
          (Nat.dvd_of_mod_eq_zero h0)
        have := Nat.le_of_dvd hr'pos hsr'
        omega
      · exact h
    -- the theorem gives the witness triple; the congruence localizes it
    obtain ⟨x, y, hd, hprod, i, hi, hwin⟩ :=
      (theorem_4_2_12 (rs := rs) hr hrs hsn hinv hns rfl rfl rfl d).mp hdd
    have hcong := lenstra_congruence (rs := rs) hs1 hinv rfl rfl rfl
      ha₁pos ha₁lt.le hprod i hi
    have hsign := sign_pattern (t := lT s (n * rs % s * rs % s)
        ((rs : ℤ) * (((n : ℤ) - r * ((n * rs % s : ℕ) : ℤ)) / s)))
      lB_zero lB_one (fun j hj => by
        obtain ⟨q, hq, hA, hB, -⟩ := l_rec ha₁pos ha₁lt.le j hj
        exact ⟨q, hq, hA, hB⟩)
    rw [lenstraDivisors, List.mem_flatMap]
    have hargs : (lenstraChainArgs n r s rs).1 = n * rs % s * rs % s := rfl
    have hargs2 : (lenstraChainArgs n r s rs).2
        = (rs : ℤ) * (((n : ℤ) - r * ((n * rs % s : ℕ) : ℤ)) / s) := rfl
    rw [hargs, hargs2]
    refine ⟨i, List.mem_range.mpr (by omega), ?_⟩
    rw [List.mem_flatMap]
    refine ⟨(x : ℤ) * lA s (n * rs % s * rs % s)
        ((rs : ℤ) * (((n : ℤ) - r * ((n * rs % s : ℕ) : ℤ)) / s)) i
      + y * lB s (n * rs % s * rs % s)
        ((rs : ℤ) * (((n : ℤ) - r * ((n * rs % s : ℕ) : ℤ)) / s)) i, ?_, ?_⟩
    · rcases hwin with ⟨hev, habs⟩ | ⟨hodd, hlow, hup⟩
      · rw [ite_eq_left hev]
        exact mem_evenWindow hs0 hcong habs
      · rw [ite_eq_right (by omega)]
        have hApos : 0 < lA s (n * rs % s * rs % s)
            ((rs : ℤ) * (((n : ℤ) - r * ((n * rs % s : ℕ) : ℤ)) / s)) i := by
          refine lA_pos ha₁pos ha₁lt.le i ?_
          have hT := lT_even (s := s) (a₁ := n * rs % s * rs % s)
            (c₁ := (rs : ℤ) * (((n : ℤ) - r * ((n * rs % s : ℕ) : ℤ)) / s))
          omega
        have hBpos : 1 ≤ lB s (n * rs % s * rs % s)
            ((rs : ℤ) * (((n : ℤ) - r * ((n * rs % s : ℕ) : ℤ)) / s)) i :=
          (hsign i hi).2.2 hodd
        exact mem_oddWindow hs0 (by positivity) hcong hlow hup
    · have hd' : d = x * s + r := hd
      rw [hd']
      refine solveSystem_complete hr hrs hr'pos ?_ ?_ rfl hprod
      · -- `0 ≤ aᵢ`
        rcases eq_or_lt_of_le hi with rfl | hlt
        · rw [lA_T ha₁pos ha₁lt.le]
        · exact (lA_pos ha₁pos ha₁lt.le i hlt).le
      · -- `aᵢ = 0 → bᵢ ≠ 0`
        intro hA0
        have hit : i = lT s (n * rs % s * rs % s)
            ((rs : ℤ) * (((n : ℤ) - r * ((n * rs % s : ℕ) : ℤ)) / s)) := by
          by_contra hne
          have hlt : i < _ := lt_of_le_of_ne hi hne
          have := lA_pos ha₁pos ha₁lt.le i hlt
          omega
        have ht0 := lT_pos (c₁ := (rs : ℤ)
          * (((n : ℤ) - r * ((n * rs % s : ℕ) : ℤ)) / s)) hs0 ha₁pos ha₁lt.le
        have hTev := lT_even (s := s) (a₁ := n * rs % s * rs % s)
          (c₁ := (rs : ℤ) * (((n : ℤ) - r * ((n * rs % s : ℕ) : ℤ)) / s))
        have hBt := (hsign i hi).2.1 (by omega) (by omega)
        omega

section AlgorithmExample

-- the divisors of `91` congruent to `2 (mod 5)`: exactly `7`
#guard 7 ∈ lenstraDivisors 91 2 5 3
#guard 13 ∉ lenstraDivisors 91 2 5 3
#guard 1 ∉ lenstraDivisors 91 2 5 3

-- the `(n, r, s) = (50, 1, 4)` instance on which the book's PRINTED
-- algorithm loses the divisor `5` to its strict window: the corrected
-- algorithm finds all three divisors `≡ 1 (mod 4)`
#guard 1 ∈ lenstraDivisors 50 1 4 1
#guard 5 ∈ lenstraDivisors 50 1 4 1
#guard 25 ∈ lenstraDivisors 50 1 4 1
#guard 2 ∉ lenstraDivisors 50 1 4 1
#guard 10 ∉ lenstraDivisors 50 1 4 1

-- a bigger instance: `1001 = 7·11·13`, divisors `≡ 1 (mod 10)`
-- (`rs = 1`): exactly `1, 11, 91, 1001`
#guard 1 ∈ lenstraDivisors 1001 1 10 1
#guard 11 ∈ lenstraDivisors 1001 1 10 1
#guard 91 ∈ lenstraDivisors 1001 1 10 1
#guard 1001 ∈ lenstraDivisors 1001 1 10 1
#guard 7 ∉ lenstraDivisors 1001 1 10 1
#guard 13 ∉ lenstraDivisors 1001 1 10 1

end AlgorithmExample

end AlgorithmSpec

end CP

end Azurite