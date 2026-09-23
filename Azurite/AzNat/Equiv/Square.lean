/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzNat.Square
import Azurite.AzNat.Equiv.Mul.Basic
import Azurite.UInt64.Equiv.AddWithCarry
import Azurite.UInt64.Equiv.WideMul

/-!
# Correctness of `schoolbookSquareLimbs`

For a slice `s := (a.toList.drop lo).take len`,

  `toNatLimbsList (schoolbookSquareLimbs a lo len hA).toList = (toNatLimbsList s)^2`.

The proof factors through three phase lemmas matching the three phases
of the algorithm:

* `offDiag` accumulates `Σ_{0 ≤ p < q < len} a_p · a_q · 2^{64·(p+q)}`.
* `doubleLimbs` multiplies the result by `2`.
* `addDiagonalLimbs` adds `Σ_p a_p² · 2^{128·p}`.

The algebraic identity `(Σ a_p · 2^{64p})² = Σ a_p² · 2^{128p} +
2 · Σ_{p < q} a_p · a_q · 2^{64·(p+q)}` then closes the proof.

-/

namespace Azurite.AzNat

/-! ### Algebraic identity: split `(toNat s)^2` into diagonal + 2·off-diagonal -/

/-- Diagonal sum `Σ_{p < n} s[p]² · 2^{128·p}` over the prefix `s.take n`. -/
def diagSumAux (s : List UInt64) (n : Nat) : Nat :=
  match n with
  | 0 => 0
  | n + 1 =>
    diagSumAux s n +
      (if h : n < s.length then (s[n]'h).toNat ^ 2 * 2 ^ (128 * n) else 0)

/-- Off-diagonal sum `Σ_{p < q < n} s[p] · s[q] · 2^{64·(p+q)}` over the
    prefix `s.take n`. -/
def offDiagSumAux (s : List UInt64) (n : Nat) : Nat :=
  match n with
  | 0 => 0
  | n + 1 =>
    offDiagSumAux s n +
      (if h : n < s.length then
        (s[n]'h).toNat * toNatLimbsList (s.take n) * 2 ^ (64 * n)
      else 0)

/-- The key algebraic identity:
    `(toNat s)² = diag + 2 · offDiag` for any list `s`. -/
lemma toNatLimbsList_sq_eq (s : List UInt64) :
    (toNatLimbsList s) ^ 2 = diagSumAux s s.length + 2 * offDiagSumAux s s.length := by
  induction s using List.reverseRecOn with
  | nil => simp [diagSumAux, offDiagSumAux, toNatLimbsList]
  | append_singleton xs x ih =>
    -- toNatLimbsList (xs ++ [x]) = toNatLimbsList xs + x.toNat * 2^(64 * xs.length).
    have h_len : (xs ++ [x]).length = xs.length + 1 := by simp
    have h_take_xs : (xs ++ [x]).take xs.length = xs := by
      rw [List.take_append_of_le_length (Nat.le_refl _), List.take_length]
    have h_idx : xs.length < (xs ++ [x]).length := by simp
    have h_get : (xs ++ [x])[xs.length]'h_idx = x := by simp
    have h_toNat_append :
        toNatLimbsList (xs ++ [x]) = toNatLimbsList xs + x.toNat * 2 ^ (64 * xs.length) := by
      rw [toNatLimbsList_append]
      rw [show toNatLimbsList [x] = x.toNat from by simp [toNatLimbsList]]
      ring
    -- Expand diag (xs ++ [x]) = diag xs + x^2 * 2^(128 * xs.length).
    have h_diag :
        diagSumAux (xs ++ [x]) (xs.length + 1) =
          diagSumAux (xs ++ [x]) xs.length + x.toNat ^ 2 * 2 ^ (128 * xs.length) := by
      rw [diagSumAux, dite_eq_left h_idx, h_get]
    -- diag xs is the same when computed over (xs ++ [x]).
    have h_diag_pref :
        ∀ n ≤ xs.length, diagSumAux (xs ++ [x]) n = diagSumAux xs n := by
      intro n hn
      induction n with
      | zero => rfl
      | succ k ihk =>
        rw [diagSumAux, ihk (by omega), diagSumAux]
        congr 1
        have h_k_lt_xs : k < xs.length := by omega
        have h_k_lt_xx : k < (xs ++ [x]).length := by simp; omega
        rw [dite_eq_left h_k_lt_xs, dite_eq_left h_k_lt_xx]
        have h_get' : (xs ++ [x])[k]'h_k_lt_xx = xs[k]'h_k_lt_xs := by
          rw [List.getElem_append_left h_k_lt_xs]
        rw [h_get']
    -- Similarly off-diag.
    have h_offdiag :
        offDiagSumAux (xs ++ [x]) (xs.length + 1) =
          offDiagSumAux (xs ++ [x]) xs.length
            + x.toNat * toNatLimbsList xs * 2 ^ (64 * xs.length) := by
      rw [offDiagSumAux, dite_eq_left h_idx, h_get, h_take_xs]
    have h_offdiag_pref :
        ∀ n ≤ xs.length, offDiagSumAux (xs ++ [x]) n = offDiagSumAux xs n := by
      intro n hn
      induction n with
      | zero => rfl
      | succ k ihk =>
        rw [offDiagSumAux, ihk (by omega), offDiagSumAux]
        congr 1
        have h_k_lt_xs : k < xs.length := by omega
        have h_k_lt_xx : k < (xs ++ [x]).length := by simp; omega
        rw [dite_eq_left h_k_lt_xs, dite_eq_left h_k_lt_xx]
        have h_get' : (xs ++ [x])[k]'h_k_lt_xx = xs[k]'h_k_lt_xs := by
          rw [List.getElem_append_left h_k_lt_xs]
        have h_take_pref : (xs ++ [x]).take k = xs.take k :=
          List.take_append_of_le_length (by omega)
        rw [h_get', h_take_pref]
    rw [h_len, h_diag, h_diag_pref _ (le_refl _),
        h_offdiag, h_offdiag_pref _ (le_refl _)]
    rw [h_toNat_append]
    have h_ih : (toNatLimbsList xs) ^ 2 = diagSumAux xs xs.length + 2 * offDiagSumAux xs xs.length := ih
    have h_pow2 : (2 : Nat) ^ (128 * xs.length) = (2 ^ (64 * xs.length)) ^ 2 := by
      rw [← pow_mul]; congr 1; ring
    rw [h_pow2]
    nlinarith [h_ih, sq_nonneg (toNatLimbsList xs), sq_nonneg (x.toNat * 2 ^ (64 * xs.length))]

/-- A `Nat` form of `Pow` used in `nlinarith` proofs. -/
private lemma sq_def (n : Nat) : n^2 = n * n := by ring

/-! ### Helper: `toNatLimbsList` of `Array.set` -/

/-- Setting position `i` in an array shifts the `toNatLimbsList` by
    the difference at position `i`. Stated additively to avoid Nat
    subtraction issues. -/
lemma toNatLimbsList_set (a : Array UInt64) (i : Nat) (v : UInt64)
    (hi : i < a.size) :
    toNatLimbsList (a.set i v).toList + a[i].toNat * 2 ^ (64 * i)
      = toNatLimbsList a.toList + v.toNat * 2 ^ (64 * i) := by
  have hi_list : i < a.toList.length := by rw [Array.length_toList]; exact hi
  -- Split a.toList around position i.
  have h_split_a :
      a.toList = (a.toList.take i) ++ a[i] :: (a.toList.drop (i + 1)) := by
    conv_lhs => rw [← List.take_append_drop i a.toList]
    rw [List.drop_eq_getElem_cons hi_list, Array.getElem_toList]
  have h_set_list :
      (a.set i v).toList
        = (a.toList.take i) ++ v :: (a.toList.drop (i + 1)) := by
    rw [Array.toList_set]
    conv_lhs => rw [← List.take_append_drop i (a.toList.set i v)]
    rw [List.take_set_of_le (Nat.le_refl _)]
    rw [List.drop_set, ite_eq_right (by omega)]
    rw [show i - i = 0 from Nat.sub_self _]
    rw [List.drop_eq_getElem_cons hi_list, List.set_cons_zero]
  rw [h_set_list]
  conv_rhs => rw [h_split_a]
  -- Both sides: toNatLimbsList of (take i ++ x :: drop (i+1)) form.
  rw [toNatLimbsList_append, toNatLimbsList_cons]
  rw [toNatLimbsList_append, toNatLimbsList_cons]
  rw [List.length_take, Nat.min_eq_left (Nat.le_of_lt hi_list)]
  ring

/-! ### Correctness of `propagateCarry` -/

/-- Positions `< pos` are unchanged by `propagateCarry`. -/
theorem propagateCarry_toList_take (acc : Array UInt64) (pos : Nat) (carry : Bool)
    (k : Nat) (hk : k ≤ pos) :
    (propagateCarry acc pos carry).toList.take k = acc.toList.take k := by
  induction h_sub : acc.size - pos generalizing acc pos carry with
  | zero =>
    have h_ge : acc.size ≤ pos := by omega
    cases carry with
    | false => rw [propagateCarry]
    | true =>
      rw [propagateCarry]; simp [Nat.not_lt.mpr h_ge]
  | succ n ih =>
    cases carry with
    | false => rw [propagateCarry]
    | true =>
      rw [propagateCarry]
      have h_lt : pos < acc.size := by omega
      simp only [h_lt, ↓reduceDIte]
      rw [ih _ _ _ (by omega : k ≤ pos + 1) (by rw [Array.size_set]; omega)]
      rw [Array.toList_set, List.take_set_of_le hk]

/-- `propagateCarry` preserves the `toList.drop acc.size` (i.e., nothing
    past the end changes — trivially true since `drop acc.size` is empty,
    but useful for size-preservation reasoning). -/
theorem propagateCarry_size' (acc : Array UInt64) (pos : Nat) (carry : Bool) :
    (propagateCarry acc pos carry).toList.length = acc.toList.length := by
  rw [Array.length_toList, Array.length_toList, propagateCarry_size]

/-- Decomposition of `toNatLimbsList acc.toList` at position `pos`. -/
private lemma toNatLimbsList_split_at (acc : Array UInt64) (pos : Nat)
    (h_lt : pos < acc.size) :
    toNatLimbsList acc.toList
      = toNatLimbsList (acc.toList.take pos)
        + acc[pos].toNat * 2 ^ (64 * pos)
        + toNatLimbsList (acc.toList.drop (pos + 1)) * 2 ^ (64 * (pos + 1)) := by
  have h_pos_list : pos < acc.toList.length := by
    rw [Array.length_toList]; exact h_lt
  conv_lhs => rw [← List.take_append_drop pos acc.toList]
  rw [toNatLimbsList_append, List.length_take,
      Nat.min_eq_left (Nat.le_of_lt h_pos_list)]
  rw [List.drop_eq_getElem_cons h_pos_list, toNatLimbsList_cons]
  rw [Array.getElem_toList]
  rw [show 64 * (pos + 1) = 64 * pos + 64 from by ring, Nat.pow_add]
  ring

/-- **Carry-propagation correctness** (no-leak form): adding `carry` at
    position `pos` propagates correctly through `acc`, assuming the result
    fits in `acc.size` limbs (no leak past the end). -/
theorem propagateCarry_toNat (acc : Array UInt64) (pos : Nat) (carry : Bool)
    (h_pos : pos ≤ acc.size)
    (h_bound : toNatLimbsList acc.toList + (if carry then 2 ^ (64 * pos) else 0)
                < 2 ^ (64 * acc.size)) :
    toNatLimbsList (propagateCarry acc pos carry).toList
      = toNatLimbsList acc.toList + (if carry then 2 ^ (64 * pos) else 0) := by
  induction h_sub : acc.size - pos generalizing acc pos carry with
  | zero =>
    cases carry with
    | false => rw [propagateCarry]; simp
    | true =>
      exfalso
      have h_eq : acc.size = pos := by omega
      rw [h_eq] at h_bound
      simp at h_bound
  | succ n ih =>
    cases carry with
    | false => rw [propagateCarry]; simp
    | true =>
      rw [propagateCarry]
      have h_lt : pos < acc.size := by omega
      simp only [h_lt, ↓reduceDIte]
      set r := UInt64.addWithCarry acc[pos] 0 true with hr_def
      have h_aw := UInt64.addWithCarry_eq acc[pos] 0 true
      rw [← hr_def] at h_aw
      have h_zero : (0 : UInt64).toNat = 0 := rfl
      have h_true_eq : (if (true : Bool) = true then (1 : Nat) else 0) = 1 := rfl
      rw [h_zero, h_true_eq] at h_aw
      set acc' := acc.set pos r.1 with hacc'_def
      have h_set_size : acc'.size = acc.size := by rw [hacc'_def, Array.size_set]
      have h_pos' : pos + 1 ≤ acc'.size := by rw [h_set_size]; omega
      have h_sub' : acc'.size - (pos + 1) = n := by rw [h_set_size]; omega
      have h_toNat_acc' :
          toNatLimbsList acc'.toList + acc[pos].toNat * 2 ^ (64 * pos)
            = toNatLimbsList acc.toList + r.1.toNat * 2 ^ (64 * pos) := by
        rw [hacc'_def]; exact toNatLimbsList_set acc pos r.1 h_lt
      have h_pow_succ : (2 : Nat) ^ (64 * (pos + 1)) = 2 ^ (64 * pos) * 2 ^ 64 := by
        rw [show 64 * (pos + 1) = 64 * pos + 64 from by ring, Nat.pow_add]
      have h_acc_pos_lt : acc[pos].toNat < 2 ^ 64 := UInt64.toNat_lt _
      have h_r1_lt : r.1.toNat < 2 ^ 64 := UInt64.toNat_lt _
      have h_bound_acc :
          toNatLimbsList acc.toList + 2 ^ (64 * pos) < 2 ^ (64 * acc.size) := by
        have := h_bound; simp at this; exact this
      -- Lower bound on toNat acc when acc[pos] = 2^64 - 1 (used in r.2 = true case).
      have h_acc_dec := toNatLimbsList_split_at acc pos h_lt
      -- The main invariant.
      have h_main :
          toNatLimbsList acc'.toList + (if r.2 then 2 ^ (64 * (pos + 1)) else 0)
            = toNatLimbsList acc.toList + 2 ^ (64 * pos) := by
        rcases hb : r.2 with _ | _
        · -- false case.
          rw [hb] at h_aw
          have h_aw' : r.1.toNat = acc[pos].toNat + 1 := by
            simp at h_aw; omega
          show toNatLimbsList acc'.toList + 0 = _
          rw [Nat.add_zero]
          have h_g_eq : r.1.toNat * 2 ^ (64 * pos)
              = acc[pos].toNat * 2 ^ (64 * pos) + 2 ^ (64 * pos) := by
            rw [h_aw']; ring
          have := h_toNat_acc'
          omega
        · -- true case: acc[pos] = 2^64 - 1.
          rw [hb] at h_aw
          have h_aw' : acc[pos].toNat + 1 = 2 ^ 64 + r.1.toNat := by
            simp at h_aw; omega
          have h_acc_pos_eq : acc[pos].toNat = 2 ^ 64 - 1 := by omega
          have h_r1_zero : r.1.toNat = 0 := by omega
          show toNatLimbsList acc'.toList + 2 ^ (64 * (pos + 1))
            = toNatLimbsList acc.toList + 2 ^ (64 * pos)
          rw [h_pow_succ]
          have h_pow_pos : 0 < (2 : Nat) ^ (64 * pos) := Nat.pow_pos (by norm_num)
          have h_pow64_pos : 0 < (2 : Nat) ^ 64 := Nat.pow_pos (by norm_num)
          have h_acc_ge :
              acc[pos].toNat * 2 ^ (64 * pos) ≤ toNatLimbsList acc.toList := by
            rw [h_acc_dec]
            have := Nat.zero_le (toNatLimbsList (acc.toList.take pos))
            have := Nat.zero_le (toNatLimbsList (acc.toList.drop (pos + 1))
              * 2 ^ (64 * (pos + 1)))
            omega
          have h_toNat_acc'_explicit :
              toNatLimbsList acc'.toList
                = toNatLimbsList acc.toList + r.1.toNat * 2 ^ (64 * pos)
                  - acc[pos].toNat * 2 ^ (64 * pos) := by
            omega
          rw [h_toNat_acc'_explicit, h_r1_zero, h_acc_pos_eq]
          have h_mul_id : (2 ^ 64 - 1) * 2 ^ (64 * pos) + 2 ^ (64 * pos)
                  = 2 ^ (64 * pos) * 2 ^ 64 := by
            have : (2 ^ 64 : Nat) - 1 + 1 = 2 ^ 64 := by omega
            calc (2 ^ 64 - 1) * 2 ^ (64 * pos) + 2 ^ (64 * pos)
                = ((2 ^ 64 - 1) + 1) * 2 ^ (64 * pos) := by ring
              _ = 2 ^ 64 * 2 ^ (64 * pos) := by rw [this]
              _ = 2 ^ (64 * pos) * 2 ^ 64 := by ring
          have h_sub_ge : (2 ^ 64 - 1) * 2 ^ (64 * pos) ≤ 2 ^ (64 * pos) * 2 ^ 64 := by
            omega
          have h_acc_ge_explicit :
              (2 ^ 64 - 1) * 2 ^ (64 * pos) ≤ toNatLimbsList acc.toList := by
            rw [h_acc_pos_eq] at h_acc_ge
            exact h_acc_ge
          omega
      have h_bound' :
          toNatLimbsList acc'.toList + (if r.2 then 2 ^ (64 * (pos + 1)) else 0)
            < 2 ^ (64 * acc'.size) := by
        rw [h_set_size, h_main]; exact h_bound_acc
      rw [ih acc' (pos + 1) r.2 h_pos' h_bound' h_sub']
      rw [h_main]
      simp

/-! ### Correctness of `doubleLimbs` -/

/-- Invariant for `doubleLimbs.go`: positions `< k` are unchanged, positions
    `≥ k` get doubled with the incoming `carry`. Bounded by the no-leak
    assumption on the total. -/
theorem doubleLimbs.go_toNat (acc : Array UInt64) (k : Nat) (carry : Bool)
    (h_k : k ≤ acc.size)
    (h_bound : toNatLimbsList (acc.toList.take k)
                + (2 * toNatLimbsList (acc.toList.drop k)
                    + (if carry then 1 else 0)) * 2 ^ (64 * k)
                < 2 ^ (64 * acc.size)) :
    toNatLimbsList (doubleLimbs.go acc k carry).toList
      = toNatLimbsList (acc.toList.take k)
        + (2 * toNatLimbsList (acc.toList.drop k)
            + (if carry then 1 else 0)) * 2 ^ (64 * k) := by
  induction h_sub : acc.size - k generalizing acc k carry with
  | zero =>
    have h_eq : acc.size = k := by omega
    rw [doubleLimbs.go]
    have h_neg : ¬ k < acc.size := by omega
    simp only [h_neg, ↓reduceDIte]
    have h_drop_empty : acc.toList.drop k = [] := by
      apply List.drop_eq_nil_of_le
      rw [Array.length_toList]; omega
    have h_take_all : acc.toList.take k = acc.toList := by
      apply List.take_of_length_le
      rw [Array.length_toList]; omega
    rw [h_drop_empty, h_take_all]
    simp [toNatLimbsList]
    -- Need carry = false (from h_bound).
    rw [h_drop_empty, h_take_all] at h_bound
    simp [toNatLimbsList] at h_bound
    rcases hb : carry with _ | _
    · simp
    · -- carry = true: h_bound gives toNat acc + 2^(64*k) < 2^(64*acc.size) = 2^(64*k).
      -- So toNat acc < 0, impossible.
      exfalso
      rw [hb] at h_bound
      simp at h_bound
      rw [h_eq] at h_bound
      omega
  | succ n ih =>
    have h_lt : k < acc.size := by omega
    rw [doubleLimbs.go]
    simp only [h_lt, ↓reduceDIte]
    set r := UInt64.addWithCarry acc[k] acc[k] carry with hr_def
    have h_aw := UInt64.addWithCarry_eq acc[k] acc[k] carry
    rw [← hr_def] at h_aw
    -- h_aw: acc[k].toNat + acc[k].toNat + (if carry then 1 else 0)
    --     = (if r.2 then 1 else 0) * 2^64 + r.1.toNat
    set acc' := acc.set k r.1 with hacc'_def
    have h_set_size : acc'.size = acc.size := by rw [hacc'_def, Array.size_set]
    have h_k' : k + 1 ≤ acc'.size := by rw [h_set_size]; omega
    have h_sub' : acc'.size - (k + 1) = n := by rw [h_set_size]; omega
    -- Compute relations.
    -- acc'.toList.drop (k+1) = acc.toList.drop (k+1) (set is at k, not k+1).
    have h_drop_acc' : acc'.toList.drop (k + 1) = acc.toList.drop (k + 1) := by
      rw [hacc'_def, Array.toList_set, List.drop_set]
      simp
    have h_k_list : k < acc.toList.length := by rw [Array.length_toList]; exact h_lt
    have h_take_acc' :
        acc'.toList.take (k + 1) = acc.toList.take k ++ [r.1] := by
      rw [hacc'_def, Array.toList_set]
      rw [List.take_add_one]
      have h_get : (acc.toList.set k r.1)[k]? = some r.1 :=
        List.getElem?_set_self h_k_list
      rw [h_get]
      simp
      rw [List.take_set_of_le (Nat.le_refl _)]
    have h_drop_acc_split :
        toNatLimbsList (acc.toList.drop k)
          = acc[k].toNat + toNatLimbsList (acc.toList.drop (k + 1)) * 2 ^ 64 := by
      rw [List.drop_eq_getElem_cons h_k_list, toNatLimbsList_cons]
      rw [Array.getElem_toList]
      ring
    have h_take_acc'_split :
        toNatLimbsList (acc'.toList.take (k + 1))
          = toNatLimbsList (acc.toList.take k) + r.1.toNat * 2 ^ (64 * k) := by
      rw [h_take_acc', toNatLimbsList_append, List.length_take]
      rw [Nat.min_eq_left (Nat.le_of_lt h_k_list)]
      rw [show toNatLimbsList [r.1] = r.1.toNat from by simp [toNatLimbsList]]
      ring
    -- Apply IH.
    have h_pow_succ : (2 : Nat) ^ (64 * (k + 1)) = 2 ^ (64 * k) * 2 ^ 64 := by
      rw [show 64 * (k + 1) = 64 * k + 64 from by ring, Nat.pow_add]
    -- Key algebraic identity used in both the bound and the final equation.
    have h_aw_rewrite :
        r.1.toNat + (if r.2 then 1 else 0) * 2 ^ 64
          = 2 * acc[k].toNat + (if carry then 1 else 0) := by omega
    have h_alg_eq :
        toNatLimbsList (acc.toList.take k) + r.1.toNat * 2 ^ (64 * k)
          + (2 * toNatLimbsList (acc.toList.drop (k + 1))
              + (if r.2 then 1 else 0)) * 2 ^ (64 * (k + 1))
          = toNatLimbsList (acc.toList.take k)
            + (2 * toNatLimbsList (acc.toList.drop k) + (if carry then 1 else 0))
              * 2 ^ (64 * k) := by
      rw [h_drop_acc_split, h_pow_succ]
      -- Strategy: scale h_aw_rewrite by 2^(64*k) and combine.
      have h_scaled :
          (r.1.toNat + (if r.2 then 1 else 0) * 2 ^ 64) * 2 ^ (64 * k)
            = (2 * acc[k].toNat + (if carry then 1 else 0)) * 2 ^ (64 * k) := by
        rw [h_aw_rewrite]
      linarith [h_scaled]
    have h_bound' :
        toNatLimbsList (acc'.toList.take (k + 1))
          + (2 * toNatLimbsList (acc'.toList.drop (k + 1)) + (if r.2 then 1 else 0))
              * 2 ^ (64 * (k + 1))
          < 2 ^ (64 * acc'.size) := by
      rw [h_set_size, h_take_acc'_split, h_drop_acc', h_alg_eq]
      exact h_bound
    rw [ih acc' (k + 1) r.2 h_k' h_bound' h_sub']
    rw [h_take_acc'_split, h_drop_acc']
    exact h_alg_eq

/-- **Doubling correctness** (no-leak form): `doubleLimbs` returns `2 ×
    acc` when the doubled value fits in `acc.size` limbs. -/
theorem doubleLimbs_toNat (acc : Array UInt64)
    (h_bound : 2 * toNatLimbsList acc.toList < 2 ^ (64 * acc.size)) :
    toNatLimbsList (doubleLimbs acc).toList = 2 * toNatLimbsList acc.toList := by
  unfold doubleLimbs
  have h_take_zero : (acc.toList.take 0 : List UInt64) = [] := List.take_zero
  have h_drop_zero : acc.toList.drop 0 = acc.toList := List.drop_zero
  have h_nil_toNat : toNatLimbsList ([] : List UInt64) = 0 := rfl
  have h_bound_go :
      toNatLimbsList (acc.toList.take 0)
        + (2 * toNatLimbsList (acc.toList.drop 0) + (if (false : Bool) then 1 else 0))
            * 2 ^ (64 * 0)
        < 2 ^ (64 * acc.size) := by
    rw [h_take_zero, h_drop_zero, h_nil_toNat]
    show 0 + (2 * toNatLimbsList acc.toList + 0) * 1 < _
    omega
  rw [doubleLimbs.go_toNat acc 0 false (Nat.zero_le _) h_bound_go]
  rw [h_take_zero, h_drop_zero, h_nil_toNat]
  show 0 + (2 * toNatLimbsList acc.toList + 0) * 1 = _
  ring

/-! ### Monotonicity and stabilisation of `diagSumAux` / `offDiagSumAux` -/

/-- For `n ≤ m`, `diagSumAux s n ≤ diagSumAux s m`. -/
private lemma diagSumAux_mono (s : List UInt64) :
    ∀ n m, n ≤ m → diagSumAux s n ≤ diagSumAux s m := by
  intro n m
  induction m with
  | zero =>
    intro hnm
    have : n = 0 := Nat.le_zero.mp hnm
    rw [this]
  | succ k ih =>
    intro hnm
    by_cases hnk : n ≤ k
    · rw [diagSumAux]
      split_ifs
      · have := ih hnk; omega
      · exact ih hnk
    · have : n = k + 1 := by omega
      rw [this]

/-- For `n ≤ m`, `offDiagSumAux s n ≤ offDiagSumAux s m`. -/
private lemma offDiagSumAux_mono (s : List UInt64) :
    ∀ n m, n ≤ m → offDiagSumAux s n ≤ offDiagSumAux s m := by
  intro n m
  induction m with
  | zero =>
    intro hnm
    have : n = 0 := Nat.le_zero.mp hnm
    rw [this]
  | succ k ih =>
    intro hnm
    by_cases hnk : n ≤ k
    · rw [offDiagSumAux]
      split_ifs
      · have := ih hnk; omega
      · exact ih hnk
    · have : n = k + 1 := by omega
      rw [this]

/-! ### Correctness of `addDiagonalLimbs` -/

private lemma diagSumAux_stabilizes (s : List UInt64) (k : Nat) :
    diagSumAux s (s.length + k) = diagSumAux s s.length := by
  induction k with
  | zero => rfl
  | succ j ih =>
    rw [show s.length + (j + 1) = (s.length + j) + 1 from by ring, diagSumAux]
    rw [dite_eq_right (by omega : ¬ s.length + j < s.length), Nat.add_zero, ih]

private lemma diagSumAux_slice_succ (a : Array UInt64) (lo len i : Nat)
    (hA : lo + len ≤ a.size) (hi : i < len) :
    diagSumAux ((a.toList.drop lo).take len) (i + 1)
      = diagSumAux ((a.toList.drop lo).take len) i
        + (a[lo + i]'(by omega)).toNat ^ 2 * 2 ^ (128 * i) := by
  have h_slice_len : ((a.toList.drop lo).take len).length = len := by
    rw [List.length_take, List.length_drop, Array.length_toList]; omega
  have h_i_lt_slice : i < ((a.toList.drop lo).take len).length := by
    rw [h_slice_len]; exact hi
  have h_get : ((a.toList.drop lo).take len)[i]'h_i_lt_slice = a[lo + i]'(by omega) := by
    rw [List.getElem_take, List.getElem_drop, Array.getElem_toList]
  rw [diagSumAux, dite_eq_left h_i_lt_slice, h_get]

/-- Inductive invariant for `addDiagonalLimbs.go`. -/
theorem addDiagonalLimbs.go_toNat (a : Array UInt64) (lo len : Nat)
    (acc : Array UInt64) (i : Nat)
    (hA : lo + len ≤ a.size) (hAcc : 2 * len ≤ acc.size)
    (h_bound : toNatLimbsList acc.toList
                + diagSumAux ((a.toList.drop lo).take len) len
                < diagSumAux ((a.toList.drop lo).take len) i
                  + 2 ^ (64 * acc.size)) :
    toNatLimbsList (addDiagonalLimbs.go a lo len acc i hA hAcc).toList
      + diagSumAux ((a.toList.drop lo).take len) i
      = toNatLimbsList acc.toList
        + diagSumAux ((a.toList.drop lo).take len) len := by
  induction h_sub : len - i generalizing acc i with
  | zero =>
    have h_ge : len ≤ i := by omega
    rw [addDiagonalLimbs.go]
    have h_neg : ¬ i < len := by omega
    simp only [h_neg, ↓reduceDIte]
    -- For i ≥ len, diagSumAux ... i = diagSumAux ... len.
    set s := (a.toList.drop lo).take len with hs_def
    have h_slice_len : s.length = len := by
      rw [hs_def, List.length_take, List.length_drop, Array.length_toList]; omega
    have h_i_eq : diagSumAux s i = diagSumAux s len := by
      obtain ⟨k, rfl⟩ : ∃ k, i = len + k := ⟨i - len, by omega⟩
      rw [← h_slice_len]
      exact diagSumAux_stabilizes s k
    rw [h_i_eq]
  | succ n ih =>
    have h_lt : i < len := by omega
    have h_idx : lo + i < a.size := by omega
    have h_acc_lo : 2 * i < acc.size := by omega
    -- Set up the intermediates BEFORE unfolding `addDiagonalLimbs.go`.
    set x : UInt64 := a[lo + i] with hx_def
    set p : UInt64 × UInt64 := UInt64.wideMul x x with hp_def
    set r0 : UInt64 × Bool := UInt64.addWithCarry acc[2 * i] p.2 false with hr0_def
    set acc1 : Array UInt64 := acc.set (2 * i) r0.1 with hacc1_def
    have h_acc1_size : acc1.size = acc.size := by rw [hacc1_def, Array.size_set]
    have hAcc1 : 2 * len ≤ acc1.size := by rw [h_acc1_size]; exact hAcc
    have h_acc_hi : 2 * i + 1 < acc1.size := by rw [h_acc1_size]; omega
    set r1 : UInt64 × Bool :=
      UInt64.addWithCarry acc1[2 * i + 1] p.1 r0.2 with hr1_def
    set acc2 : Array UInt64 := acc1.set (2 * i + 1) r1.1 with hacc2_def
    have h_acc2_size : acc2.size = acc.size := by
      rw [hacc2_def, Array.size_set, h_acc1_size]
    have hAcc2 : 2 * len ≤ acc2.size := by rw [h_acc2_size]; exact hAcc
    set acc3 : Array UInt64 := propagateCarry acc2 (2 * i + 2) r1.2 with hacc3_def
    have h_acc3_size : acc3.size = acc.size := by
      rw [hacc3_def, propagateCarry_size, h_acc2_size]
    have hAcc3 : 2 * len ≤ acc3.size := by rw [h_acc3_size]; exact hAcc
    -- Step equation: one iteration of go.
    have h_eq : addDiagonalLimbs.go a lo len acc i hA hAcc
              = addDiagonalLimbs.go a lo len acc3 (i + 1) hA hAcc3 := by
      conv_lhs => rw [addDiagonalLimbs.go]
      simp [h_lt, hx_def, hp_def, hr0_def, hacc1_def, hr1_def, hacc2_def, hacc3_def]
    rw [h_eq]
    -- Now build the helper facts.
    set s := (a.toList.drop lo).take len with hs_def
    have h_slice_len : s.length = len := by
      rw [hs_def, List.length_take, List.length_drop, Array.length_toList]; omega
    have h_wm : p.1.toNat * 2 ^ 64 + p.2.toNat = x.toNat * x.toNat :=
      UInt64.toNat_wideMul x x
    have h_aw0 :
        acc[2 * i].toNat + p.2.toNat
          = (if r0.2 then 1 else 0) * 2 ^ 64 + r0.1.toNat := by
      have h := UInt64.addWithCarry_eq acc[2 * i] p.2 false
      rw [← hr0_def] at h
      have h_iff : (if false = true then 1 else 0 : Nat) = 0 := rfl
      rw [h_iff] at h
      omega
    have h_acc1_get : acc1[2 * i + 1] = acc[2 * i + 1] := by
      show (acc.set (2 * i) r0.1)[2 * i + 1] = acc[2 * i + 1]
      exact Array.getElem_set_ne _ _ (by omega : 2 * i ≠ 2 * i + 1)
    have h_aw1 :
        acc[2 * i + 1].toNat + p.1.toNat + (if r0.2 then 1 else 0)
          = (if r1.2 then 1 else 0) * 2 ^ 64 + r1.1.toNat := by
      have h := UInt64.addWithCarry_eq acc1[2 * i + 1] p.1 r0.2
      rw [← hr1_def] at h
      rw [h_acc1_get] at h
      exact h
    -- toNat acc1, acc2 relations.
    have h_toNat_acc1 :
        toNatLimbsList acc1.toList + (acc[2 * i]'h_acc_lo).toNat * 2 ^ (64 * (2 * i))
          = toNatLimbsList acc.toList + r0.1.toNat * 2 ^ (64 * (2 * i)) := by
      rw [hacc1_def]
      exact toNatLimbsList_set acc (2 * i) r0.1 h_acc_lo
    have h_toNat_acc2 :
        toNatLimbsList acc2.toList
            + (acc[2 * i + 1]'(by omega)).toNat * 2 ^ (64 * (2 * i + 1))
          = toNatLimbsList acc1.toList + r1.1.toNat * 2 ^ (64 * (2 * i + 1)) := by
      rw [hacc2_def]
      have h := toNatLimbsList_set acc1 (2 * i + 1) r1.1 h_acc_hi
      rw [h_acc1_get] at h
      exact h
    have h_pow_128i : (2 : Nat) ^ (128 * i) = 2 ^ (64 * (2 * i)) := by
      rw [show 128 * i = 64 * (2 * i) from by ring]
    have h_pow_64_2i_1 :
        (2 : Nat) ^ (64 * (2 * i + 1)) = 2 ^ (64 * (2 * i)) * 2 ^ 64 := by
      rw [show 64 * (2 * i + 1) = 64 * (2 * i) + 64 from by ring, Nat.pow_add]
    have h_pow_64_2i_2 :
        (2 : Nat) ^ (64 * (2 * i + 2)) = 2 ^ (64 * (2 * i)) * 2 ^ 64 * 2 ^ 64 := by
      rw [show 64 * (2 * i + 2) = 64 * (2 * i) + 64 + 64 from by ring,
          Nat.pow_add, Nat.pow_add]
    -- Bounds on UInt64.
    have h_acc_lt : (acc[2 * i]'h_acc_lo).toNat < 2 ^ 64 := UInt64.toNat_lt _
    have h_acc1_lt : (acc[2 * i + 1]'(by omega)).toNat < 2 ^ 64 := UInt64.toNat_lt _
    have h_p1_lt : p.1.toNat < 2 ^ 64 := UInt64.toNat_lt _
    have h_p2_lt : p.2.toNat < 2 ^ 64 := UInt64.toNat_lt _
    have h_r01_lt : r0.1.toNat < 2 ^ 64 := UInt64.toNat_lt _
    have h_r11_lt : r1.1.toNat < 2 ^ 64 := UInt64.toNat_lt _
    -- Key algebraic identity:
    --   toNat acc2 + r1.2_nat * 2^(64*(2i+2)) = toNat acc + x.toNat^2 * 2^(128*i)
    have h_x_sq : x.toNat ^ 2 = x.toNat * x.toNat := by ring
    have h_step_eq :
        toNatLimbsList acc2.toList
          + (if r1.2 then 2 ^ (64 * (2 * i + 2)) else 0)
          = toNatLimbsList acc.toList + x.toNat ^ 2 * 2 ^ (128 * i) := by
      -- Strategy: scale `h_aw0` by `2^(64*2i)` and `h_aw1` by `2^(64*(2i+1))`,
      -- then combine with `h_toNat_acc1`, `h_toNat_acc2`, and `h_wm` via
      -- `linarith` (treating products as atoms).
      have e0 : (acc[2 * i].toNat + p.2.toNat) * 2 ^ (64 * (2 * i))
          = ((if r0.2 then 1 else 0) * 2 ^ 64 + r0.1.toNat) * 2 ^ (64 * (2 * i)) := by
        rw [h_aw0]
      have e1 : (acc[2 * i + 1].toNat + p.1.toNat + (if r0.2 then 1 else 0))
          * 2 ^ (64 * (2 * i + 1))
          = ((if r1.2 then 1 else 0) * 2 ^ 64 + r1.1.toNat) * 2 ^ (64 * (2 * i + 1)) := by
        rw [h_aw1]
      have h_wm_scaled :
          x.toNat ^ 2 * 2 ^ (128 * i)
          = (p.1.toNat * 2 ^ 64 + p.2.toNat) * 2 ^ (64 * (2 * i)) := by
        rw [h_x_sq, ← h_wm, h_pow_128i]
      have h_r12_eq : (if r1.2 then 2 ^ (64 * (2 * i + 2)) else 0 : Nat)
          = (if r1.2 then 1 else 0) * 2 ^ (64 * (2 * i + 2)) := by
        rcases r1.2 with _ | _ <;> simp
      -- Convert e0, e1 to product form by ring_nf in the multiplied forms.
      have e0' :
          acc[2 * i].toNat * 2 ^ (64 * (2 * i)) + p.2.toNat * 2 ^ (64 * (2 * i))
          = (if r0.2 then 1 else 0) * 2 ^ 64 * 2 ^ (64 * (2 * i))
              + r0.1.toNat * 2 ^ (64 * (2 * i)) := by linarith [e0]
      have e1' :
          acc[2 * i + 1].toNat * 2 ^ (64 * (2 * i + 1))
            + p.1.toNat * 2 ^ (64 * (2 * i + 1))
            + (if r0.2 then 1 else 0) * 2 ^ (64 * (2 * i + 1))
          = (if r1.2 then 1 else 0) * 2 ^ 64 * 2 ^ (64 * (2 * i + 1))
              + r1.1.toNat * 2 ^ (64 * (2 * i + 1)) := by linarith [e1]
      have h_wm_scaled' :
          x.toNat ^ 2 * 2 ^ (128 * i)
          = p.1.toNat * 2 ^ 64 * 2 ^ (64 * (2 * i)) + p.2.toNat * 2 ^ (64 * (2 * i)) := by
        linarith [h_wm_scaled]
      -- Connect powers: 2^64 * 2^(64*2i) = 2^(64*(2i+1)).
      have h_pow_step1 :
          (2 : Nat) ^ 64 * 2 ^ (64 * (2 * i)) = 2 ^ (64 * (2 * i + 1)) := by
        rw [show 64 * (2 * i + 1) = 64 * (2 * i) + 64 from by ring, Nat.pow_add]; ring
      have h_pow_step2 :
          (2 : Nat) ^ 64 * 2 ^ (64 * (2 * i + 1)) = 2 ^ (64 * (2 * i + 2)) := by
        rw [show 64 * (2 * i + 2) = 64 * (2 * i + 1) + 64 from by ring, Nat.pow_add]; ring
      rw [h_r12_eq]
      -- Bridge atoms via the power identities (linarith treats `r₀ * 2^64 * P`
      -- and `r₀ * Q` as distinct, so we expose the equality explicitly).
      have b1 :
          (if r0.2 then 1 else 0) * 2 ^ 64 * 2 ^ (64 * (2 * i))
            = (if r0.2 then 1 else 0) * 2 ^ (64 * (2 * i + 1)) := by
        rw [show (if r0.2 then 1 else 0) * 2 ^ 64 * 2 ^ (64 * (2 * i))
              = (if r0.2 then 1 else 0) * (2 ^ 64 * 2 ^ (64 * (2 * i))) from by ring,
            h_pow_step1]
      have b2 :
          (if r1.2 then 1 else 0) * 2 ^ 64 * 2 ^ (64 * (2 * i + 1))
            = (if r1.2 then 1 else 0) * 2 ^ (64 * (2 * i + 2)) := by
        rw [show (if r1.2 then 1 else 0) * 2 ^ 64 * 2 ^ (64 * (2 * i + 1))
              = (if r1.2 then 1 else 0) * (2 ^ 64 * 2 ^ (64 * (2 * i + 1))) from by ring,
            h_pow_step2]
      have b3 :
          p.1.toNat * 2 ^ 64 * 2 ^ (64 * (2 * i))
            = p.1.toNat * 2 ^ (64 * (2 * i + 1)) := by
        rw [show p.1.toNat * 2 ^ 64 * 2 ^ (64 * (2 * i))
              = p.1.toNat * (2 ^ 64 * 2 ^ (64 * (2 * i))) from by ring,
            h_pow_step1]
      linarith [h_toNat_acc1, h_toNat_acc2, e0', e1', h_wm_scaled', b1, b2, b3]
    -- The diagonal-step identity in `x.toNat` form (matches h_step_eq's RHS).
    have h_diag_succ : diagSumAux s (i + 1)
        = diagSumAux s i + x.toNat ^ 2 * 2 ^ (128 * i) := by
      have h := diagSumAux_slice_succ a lo len i hA h_lt
      rw [← hs_def] at h
      show _ = _ + (x.toNat) ^ 2 * 2 ^ (128 * i)
      exact h
    have h_mono := diagSumAux_mono s (i + 1) len (by omega)
    -- Apply propagateCarry_toNat to acc2.
    have h_pos_acc2 : 2 * i + 2 ≤ acc2.size := by rw [h_acc2_size]; omega
    have h_propagate_bound :
        toNatLimbsList acc2.toList + (if r1.2 then 2 ^ (64 * (2 * i + 2)) else 0)
          < 2 ^ (64 * acc2.size) := by
      rw [h_acc2_size, h_step_eq]
      omega
    have h_propagate :=
      propagateCarry_toNat acc2 (2 * i + 2) r1.2 h_pos_acc2 h_propagate_bound
    have h_acc3_toNat : toNatLimbsList acc3.toList
        = toNatLimbsList acc.toList + x.toNat ^ 2 * 2 ^ (128 * i) := by
      rw [hacc3_def, h_propagate]
      omega
    have h_sub' : len - (i + 1) = n := by omega
    have h_ih_bound : toNatLimbsList acc3.toList
        + diagSumAux s len < diagSumAux s (i + 1) + 2 ^ (64 * acc3.size) := by
      rw [h_acc3_size, h_acc3_toNat, h_diag_succ]
      omega
    have h_ih := ih acc3 (i + 1) hAcc3 h_ih_bound h_sub'
    -- h_ih : toNat result + diagSumAux s (i + 1) = toNat acc3 + diagSumAux s len.
    linarith [h_ih, h_acc3_toNat, h_diag_succ]

/-- **Diagonal-addition correctness.** Adding all the `a_i²` contributions
    yields a final accumulator whose `toNat` is the initial value plus
    `diagSumAux` over the slice. -/
theorem addDiagonalLimbs_toNat (a : Array UInt64) (lo len : Nat) (acc : Array UInt64)
    (hA : lo + len ≤ a.size) (hAcc : 2 * len ≤ acc.size)
    (h_bound : toNatLimbsList acc.toList + diagSumAux ((a.toList.drop lo).take len) len
                < 2 ^ (64 * acc.size)) :
    toNatLimbsList (addDiagonalLimbs a lo len acc hA hAcc).toList
      = toNatLimbsList acc.toList + diagSumAux ((a.toList.drop lo).take len) len := by
  unfold addDiagonalLimbs
  have h_go_bound :
      toNatLimbsList acc.toList + diagSumAux ((a.toList.drop lo).take len) len
        < diagSumAux ((a.toList.drop lo).take len) 0 + 2 ^ (64 * acc.size) := by
    rw [diagSumAux]; omega
  have h_go := addDiagonalLimbs.go_toNat a lo len acc 0 hA hAcc h_go_bound
  rw [diagSumAux] at h_go
  omega

/-! ### Correctness of off-diagonal accumulation -/

/-- The off-diagonal "row sum" starting from iter `i`: a recursive sum
    matching the structure of `schoolbookSquareLimbs.offDiag.go`. -/
private def partialOffDiagSum (a : Array UInt64) (lo len : Nat) (i : Nat) : Nat :=
  if i + 1 < len then
    ((a.toList.drop (lo + i)).headD 0).toNat
      * toNatLimbsList ((a.toList.drop (lo + i + 1)).take (len - i - 1))
      * 2 ^ (64 * (2 * i + 1))
    + partialOffDiagSum a lo len (i + 1)
  else 0
  termination_by len - i

private lemma partialOffDiagSum_step (a : Array UInt64) (lo len i : Nat)
    (h : i + 1 < len) :
    partialOffDiagSum a lo len i
      = ((a.toList.drop (lo + i)).headD 0).toNat
        * toNatLimbsList ((a.toList.drop (lo + i + 1)).take (len - i - 1))
        * 2 ^ (64 * (2 * i + 1))
        + partialOffDiagSum a lo len (i + 1) := by
  rw [partialOffDiagSum]
  simp [h]

private lemma partialOffDiagSum_terminal (a : Array UInt64) (lo len i : Nat)
    (h : ¬ i + 1 < len) :
    partialOffDiagSum a lo len i = 0 := by
  rw [partialOffDiagSum]
  simp [h]

private lemma drop_headD_eq (a : Array UInt64) (lo i : Nat) (hi : lo + i < a.size) :
    (a.toList.drop (lo + i)).headD 0 = a[lo + i] := by
  have h_len : lo + i < a.toList.length := by rw [Array.length_toList]; exact hi
  rw [List.drop_eq_getElem_cons h_len, List.headD_cons, Array.getElem_toList]

/-- `offDiagSumAux` only depends on the first `n` elements of `s`. -/
private lemma offDiagSumAux_take_eq (s : List UInt64) :
    ∀ n m, n ≤ m → offDiagSumAux (s.take m) n = offDiagSumAux s n := by
  intro n m hnm
  induction n generalizing m with
  | zero => simp [offDiagSumAux]
  | succ k ih =>
    rw [offDiagSumAux, offDiagSumAux]
    congr 1
    · exact ih m (by omega)
    · by_cases hk_lt : k < s.length
      · have hk_lt_tm : k < (s.take m).length := by rw [List.length_take]; omega
        rw [dite_eq_left hk_lt, dite_eq_left hk_lt_tm]
        have h_get_eq : (s.take m)[k]'hk_lt_tm = s[k]'hk_lt := List.getElem_take
        have h_take_eq : (s.take m).take k = s.take k := by
          rw [List.take_take]; congr 1; omega
        rw [h_get_eq, h_take_eq]
      · push Not at hk_lt
        have hk_ge_tm : ¬ k < (s.take m).length := by
          rw [List.length_take]; omega
        rw [dite_eq_right hk_ge_tm, dite_eq_right (Nat.not_lt.mpr hk_lt)]

/-- Helper: snoc-decompose `(a.drop X).take (Y+1)` at the boundary. -/
private lemma drop_take_succ_snoc (a : Array UInt64) (X Y : Nat)
    (h : X + Y < a.size) :
    (a.toList.drop X).take (Y + 1)
      = (a.toList.drop X).take Y ++ [a[X + Y]] := by
  have h_idx : X + Y < a.toList.length := by rw [Array.length_toList]; exact h
  rw [← List.take_concat_get' (a.toList.drop X) Y (by
    rw [List.length_drop, Array.length_toList]; omega)]
  congr 1
  rw [List.getElem_drop, Array.getElem_toList]

/-- Variant of `drop_take_succ_snoc` accepting an index equation. -/
private lemma drop_take_succ_snoc_eq (a : Array UInt64) (X Y N : Nat)
    (h_eq : X + Y = N) (h : N < a.size) :
    (a.toList.drop X).take (Y + 1)
      = (a.toList.drop X).take Y ++ [a[N]] := by
  subst h_eq
  exact drop_take_succ_snoc a X Y h

/-- Helper: cons-decompose `(a.drop X).take (Y+1)`. -/
private lemma drop_take_succ_cons (a : Array UInt64) (X Y : Nat)
    (h : X < a.size) :
    (a.toList.drop X).take (Y + 1)
      = a[X] :: (a.toList.drop (X + 1)).take Y := by
  have h_len : X < a.toList.length := by rw [Array.length_toList]; exact h
  rw [List.drop_eq_getElem_cons h_len, List.take_succ_cons]
  rw [Array.getElem_toList]

/-- Auxiliary: `partialOffDiagSum` at `len = n+1` decomposes as the value
    at `len = n` plus an extra "new column n" contribution. -/
private lemma partialOffDiagSum_aux (a : Array UInt64) (lo n : Nat)
    (hA : lo + n + 1 ≤ a.size) :
    ∀ i, i ≤ n →
      partialOffDiagSum a lo (n + 1) i
        = partialOffDiagSum a lo n i
          + a[lo + n].toNat
            * toNatLimbsList ((a.toList.drop (lo + i)).take (n - i))
            * 2 ^ (64 * (i + n)) := by
  intro i hi
  induction h_diff : n - i generalizing i with
  | zero =>
    rw [partialOffDiagSum_terminal a lo (n + 1) i (by omega)]
    rw [partialOffDiagSum_terminal a lo n i (by omega)]
    simp [toNatLimbsList]
  | succ k ihk =>
    have h_lt : i < n := by omega
    have h_pn : i + 1 < n + 1 := by omega
    have h_i_lt_size : lo + i < a.size := by omega
    have h_sub' : n - (i + 1) = k := by omega
    rw [partialOffDiagSum_step a lo (n + 1) i h_pn]
    rw [ihk (i + 1) (by omega) h_sub']
    rw [drop_headD_eq a lo i h_i_lt_size]
    rw [show n + 1 - i - 1 = k + 1 from by omega]
    rw [show lo + (i + 1) = lo + i + 1 from by ring]
    rw [drop_take_succ_snoc_eq a (lo + i + 1) k (lo + n) (by omega) (by omega)]
    rw [drop_take_succ_cons a (lo + i) k h_i_lt_size]
    rw [toNatLimbsList_append]
    have h_len_eq : ((a.toList.drop (lo + i + 1)).take k).length = k := by
      rw [List.length_take, List.length_drop, Array.length_toList]
      apply min_eq_left; omega
    rw [h_len_eq]
    have h_single : ∀ x : UInt64, toNatLimbsList [x] = x.toNat := by
      intro x; simp [toNatLimbsList]
    rw [h_single]
    rw [toNatLimbsList_cons]
    have h_pow_C : (2 : Nat) ^ (64 * (i + 1 + n))
                      = 2 ^ (64 * (i + n)) * 2 ^ 64 := by
      rw [show 64 * (i + 1 + n) = 64 * (i + n) + 64 from by ring, Nat.pow_add]
    have h_pow_D : (2 : Nat) ^ (64 * k) * 2 ^ (64 * (2 * i + 1))
                      = 2 ^ (64 * (i + n)) := by
      rw [← Nat.pow_add]; congr 1; omega
    by_cases h_lt' : i + 1 < n
    · rw [partialOffDiagSum_step a lo n i h_lt']
      rw [drop_headD_eq a lo i h_i_lt_size]
      rw [show n - i - 1 = k from h_sub']
      rw [h_pow_C, ← h_pow_D]
      -- Goal is a pure-Nat algebraic identity.
      generalize a[lo + i].toNat = X
      generalize a[lo + n].toNat = Y
      generalize toNatLimbsList ((a.toList.drop (lo + i + 1)).take k) = T
      generalize partialOffDiagSum a lo n (i + 1) = P1
      ring
    · have h_k_zero : k = 0 := by omega
      have h_term_i : partialOffDiagSum a lo n i = 0 :=
        partialOffDiagSum_terminal a lo n i (by omega)
      have h_term_i1 : partialOffDiagSum a lo n (i + 1) = 0 :=
        partialOffDiagSum_terminal a lo n (i + 1) (by omega)
      have h_exp_eq : 64 * (2 * i + 1) = 64 * (i + n) := by omega
      have h_pow_E : (2 : Nat) ^ (64 * (2 * i + 1)) = 2 ^ (64 * (i + n)) := by
        rw [h_exp_eq]
      rw [h_term_i, h_term_i1, h_k_zero, h_pow_E]
      generalize a[lo + i].toNat = X
      generalize a[lo + n].toNat = Y
      simp only [List.take_zero, toNatLimbsList, List.foldr_nil]
      ring

/-- The total `partialOffDiagSum a lo len 0` equals `offDiagSumAux` of the
    slice. The two sides represent the same double sum
    `Σ_{p < q < len} s[p] · s[q] · 2^(64·(p+q))` traversed by `p`
    (LHS) vs. by `q` (RHS). -/
private lemma partialOffDiagSum_eq_offDiagSumAux (a : Array UInt64) (lo len : Nat)
    (hA : lo + len ≤ a.size) :
    partialOffDiagSum a lo len 0
      = offDiagSumAux ((a.toList.drop lo).take len) len := by
  induction len with
  | zero => rw [partialOffDiagSum]; simp [offDiagSumAux]
  | succ n ih =>
    have hA' : lo + n ≤ a.size := by omega
    have hAn1 : lo + n + 1 ≤ a.size := by omega
    have h_step := partialOffDiagSum_aux a lo n hAn1 0 (by omega)
    rw [show n - 0 = n from rfl, show (0 : Nat) + n = n from by omega,
        show lo + 0 = lo from by omega] at h_step
    rw [h_step, ih hA']
    -- Now combine with offDiagSumAux's step.
    have h_take_take :
        ((a.toList.drop lo).take (n + 1)).take n = (a.toList.drop lo).take n := by
      rw [List.take_take]; congr 1; omega
    have h_n_lt : n < ((a.toList.drop lo).take (n + 1)).length := by
      rw [List.length_take, List.length_drop, Array.length_toList]; omega
    have h_get : ((a.toList.drop lo).take (n + 1))[n]'h_n_lt = a[lo + n] := by
      rw [List.getElem_take, List.getElem_drop, Array.getElem_toList]
    rw [offDiagSumAux, dite_eq_left h_n_lt, h_get, h_take_take]
    have h_inner :
        offDiagSumAux ((a.toList.drop lo).take (n + 1)) n
          = offDiagSumAux ((a.toList.drop lo).take n) n := by
      have h1 := offDiagSumAux_take_eq (a.toList.drop lo) n (n + 1) (by omega)
      have h2 := offDiagSumAux_take_eq (a.toList.drop lo) n n (le_refl _)
      linarith
    rw [h_inner]

/-- `offDiag.go` preserves positions `≥ 2*len`: it only writes to
    `acc[2i+1 .. i+len]` at iter `i`, which is contained in `[0, 2*len)`. -/
private lemma schoolbookSquareLimbs.offDiag.go_toList_drop
    (a : Array UInt64) (lo len : Nat) (acc : Array UInt64) (i : Nat)
    (hA : lo + len ≤ a.size) (hAcc : 2 * len ≤ acc.size) :
    (schoolbookSquareLimbs.offDiag.go a lo len acc i hA hAcc).toList.drop (2 * len)
      = acc.toList.drop (2 * len) := by
  induction h_sub : len - i generalizing acc i with
  | zero =>
    rw [schoolbookSquareLimbs.offDiag.go]
    simp [show ¬ i + 1 < len from by omega]
  | succ n ih =>
    rw [schoolbookSquareLimbs.offDiag.go]
    by_cases h_lt : i + 1 < len
    · simp only [h_lt, ↓reduceDIte]
      have h_inner_len : (lo + i + 1) + (len - i - 1) ≤ a.size := by omega
      have h_acc_row : (2 * i + 1) + (len - i - 1) ≤ acc.size := by omega
      have h_rec : len - (i + 1) = n := by omega
      set r := mulAddLimbs a (lo + i + 1) (len - i - 1) (2 * i + 1) a[lo + i]
                acc h_inner_len h_acc_row with hr_def
      have h_r_size : r.1.size = acc.size := mulAddLimbs_size _ _ _ _ _ _ _ _
      set acc' := r.1.set ((2 * i + 1) + (len - i - 1)) r.2 with hacc'_def
      have hAcc' : 2 * len ≤ acc'.size := by
        rw [hacc'_def, Array.size_set, h_r_size]; exact hAcc
      rw [ih acc' (i + 1) hAcc' h_rec]
      rw [hacc'_def, Array.toList_set, List.drop_set]
      simp only [show 2 * i + 1 + (len - i - 1) < 2 * len from by omega, ↓reduceIte]
      have h_drop_r : r.1.toList.drop ((2 * i + 1) + (len - i - 1)) =
                      acc.toList.drop ((2 * i + 1) + (len - i - 1)) := by
        rw [hr_def]
        exact mulAddLimbs.go_toList_drop a (lo + i + 1) (len - i - 1) (2 * i + 1)
          a[lo + i] acc 0 0 h_inner_len h_acc_row
      calc r.1.toList.drop (2 * len)
          = (r.1.toList.drop ((2 * i + 1) + (len - i - 1))).drop
                (2 * len - ((2 * i + 1) + (len - i - 1))) := by
            rw [List.drop_drop]; congr 1; omega
        _ = (acc.toList.drop ((2 * i + 1) + (len - i - 1))).drop
                (2 * len - ((2 * i + 1) + (len - i - 1))) := by rw [h_drop_r]
        _ = acc.toList.drop (2 * len) := by
            rw [List.drop_drop]; congr 1; omega
    · simp [h_lt]

/-- Splits `toNatLimbsList (l.take (m + k))` into prefix and middle pieces. -/
private lemma toNatLimbsList_take_add (l : List UInt64) (m k : Nat) (hm : m ≤ l.length) :
    toNatLimbsList (l.take (m + k))
      = toNatLimbsList (l.take m)
        + toNatLimbsList ((l.drop m).take k) * 2 ^ (64 * m) := by
  rw [List.take_add, toNatLimbsList_append, List.length_take, Nat.min_eq_left hm]
  ring

/-- Indexing `mulAddLimbs` past its written region yields the original `acc`. -/
private lemma mulAddLimbs_getElem_ge (a : Array UInt64) (offA lenA offAcc : Nat) (b : UInt64)
    (acc : Array UInt64)
    (hA : offA + lenA ≤ a.size) (hAcc : offAcc + lenA ≤ acc.size)
    (i : Nat) (hge : offAcc + lenA ≤ i)
    (hi : i < (mulAddLimbs a offA lenA offAcc b acc hA hAcc).1.size) :
    (mulAddLimbs a offA lenA offAcc b acc hA hAcc).1[i]'hi = acc[i]'(by
      have := mulAddLimbs_size a offA lenA offAcc b acc hA hAcc
      omega) := by
  have h_drop := mulAddLimbs.go_toList_drop a offA lenA offAcc b acc 0 0 hA hAcc
  change (mulAddLimbs a offA lenA offAcc b acc hA hAcc).1.toList.drop (offAcc + lenA)
    = acc.toList.drop (offAcc + lenA) at h_drop
  have h_sizeR := mulAddLimbs_size a offA lenA offAcc b acc hA hAcc
  have h_acc_size : i < acc.size := by omega
  have h_lenL : (mulAddLimbs a offA lenA offAcc b acc hA hAcc).1.toList.length = acc.size := by
    rw [Array.length_toList]; exact h_sizeR
  have h_get := congrArg (fun l => l[i - (offAcc + lenA)]?) h_drop
  simp only [List.getElem?_drop] at h_get
  rw [show offAcc + lenA + (i - (offAcc + lenA)) = i from by omega] at h_get
  have hi_L : i < (mulAddLimbs a offA lenA offAcc b acc hA hAcc).1.toList.length := by
    rw [h_lenL]; exact by omega
  have hi_R : i < acc.toList.length := by rw [Array.length_toList]; exact h_acc_size
  rw [List.getElem?_eq_getElem hi_L, List.getElem?_eq_getElem hi_R,
    Array.getElem_toList, Array.getElem_toList] at h_get
  exact Option.some.inj h_get

/-- Invariant of `schoolbookSquareLimbs.offDiag.go`: with the zero-tail
    invariant on `acc` (positions `[i + len, 2*len)` of `acc` are zero),
    the low `2*len` limbs of the result equal `acc` plus the partial
    off-diagonal sum from iter `i`.

    At each iter, the fuse-add `mulAddLimbs` writes
    `a[lo+i] · a[lo+i+1..lo+len) · 2^(64·(2i+1))` into `acc[2i+1 .. i+len)`,
    with the final carry placed at `acc[i+len]`. The zero-tail invariant
    advances from `[i+len, 2*len)` to `[i+1+len, 2*len)` after each iter. -/
private lemma schoolbookSquareLimbs.offDiag.go_correct
    (a : Array UInt64) (lo len : Nat) (acc : Array UInt64) (i : Nat)
    (hA : lo + len ≤ a.size) (hAcc : 2 * len ≤ acc.size)
    (h_zero : ∀ (k : Nat) (hk : k < acc.size), i + len ≤ k → k < 2 * len →
        acc[k]'hk = (0 : UInt64)) :
    toNatLimbsList
        ((schoolbookSquareLimbs.offDiag.go a lo len acc i hA hAcc).toList.take (2 * len))
      = toNatLimbsList (acc.toList.take (2 * len))
        + partialOffDiagSum a lo len i := by
  induction h_sub : len - i generalizing acc i with
  | zero =>
    have h_ge : len ≤ i := by omega
    rw [schoolbookSquareLimbs.offDiag.go]
    simp only [show ¬ i + 1 < len from by omega, ↓reduceDIte]
    rw [partialOffDiagSum_terminal a lo len i (by omega)]
    ring
  | succ n ih =>
    rw [schoolbookSquareLimbs.offDiag.go]
    by_cases h_lt : i + 1 < len
    · simp only [h_lt, ↓reduceDIte]
      have h_inner_len : (lo + i + 1) + (len - i - 1) ≤ a.size := by omega
      have h_acc_row : (2 * i + 1) + (len - i - 1) ≤ acc.size := by omega
      have h_rec : len - (i + 1) = n := by omega
      set r := mulAddLimbs a (lo + i + 1) (len - i - 1) (2 * i + 1) a[lo + i]
                acc h_inner_len h_acc_row with hr_def
      have h_r_size : r.1.size = acc.size := mulAddLimbs_size _ _ _ _ _ _ _ _
      set acc' := r.1.set ((2 * i + 1) + (len - i - 1)) r.2 with hacc'_def
      have h_acc'_size : acc'.size = acc.size := by
        rw [hacc'_def, Array.size_set, h_r_size]
      have hAcc' : 2 * len ≤ acc'.size := by rw [h_acc'_size]; exact hAcc
      -- Zero-tail invariant advances: positions [(i+1) + len, 2*len) are zero.
      have h_zero' : ∀ (k : Nat) (hk : k < acc'.size), (i + 1) + len ≤ k → k < 2 * len →
          acc'[k]'hk = (0 : UInt64) := by
        intro k hk hlo hhi
        have h_ne : k ≠ (2 * i + 1) + (len - i - 1) := by omega
        have hk_r : k < r.1.size := by rw [h_r_size]; rw [h_acc'_size] at hk; exact hk
        have h_acc'_eq : acc'[k]'hk = r.1[k]'hk_r :=
          Array.getElem_set_ne _ _ h_ne.symm
        rw [h_acc'_eq]
        have h_acc_size_k : k < acc.size := by rw [← h_r_size]; exact hk_r
        rw [show r.1[k]'hk_r = acc[k]'h_acc_size_k from
          mulAddLimbs_getElem_ge a (lo + i + 1) (len - i - 1) (2 * i + 1) a[lo + i]
            acc h_inner_len h_acc_row k (by omega) hk_r]
        exact h_zero k h_acc_size_k (by omega) hhi
      rw [ih acc' (i + 1) hAcc' h_zero' h_rec]
      -- Now prove: toNat(acc'.take(2*len)) + partialOffDiagSum a lo len (i+1)
      --          = toNat(acc.take(2*len)) + partialOffDiagSum a lo len i.
      rw [partialOffDiagSum_step a lo len i h_lt]
      rw [drop_headD_eq a lo i (by omega)]
      -- The step contribution is `a[lo+i].toNat * toNat((a.drop (lo+i+1)).take (len-i-1)) * 2^(64*(2*i+1))`.
      -- We need: toNat(acc'.take(2*len)) = toNat(acc.take(2*len)) + (step contribution).
      -- Split toNat(acc.take(2*len)) and toNat(acc'.take(2*len)) at indices 2*i+1 and i+len.
      set AS := toNatLimbsList ((a.toList.drop (lo + i + 1)).take (len - i - 1)) with hAS_def
      have h_len_acc : acc.toList.length = acc.size := Array.length_toList
      have h_len_acc' : acc'.toList.length = acc.size := by
        rw [Array.length_toList, h_acc'_size]
      have h_len_r : r.1.toList.length = acc.size := by rw [Array.length_toList, h_r_size]
      have h_2i1_le : 2 * i + 1 ≤ acc.toList.length := by rw [h_len_acc]; omega
      have h_2i1_le' : 2 * i + 1 ≤ acc'.toList.length := by rw [h_len_acc']; omega
      have h_ilen_le : i + len ≤ acc.toList.length := by rw [h_len_acc]; omega
      have h_ilen_le' : i + len ≤ acc'.toList.length := by rw [h_len_acc']; omega
      -- Split toNat(acc.take(2*len)) at i+len, then at 2*i+1.
      have h_2len_eq : 2 * len = (i + len) + (len - i) := by omega
      have h_split_acc :
          toNatLimbsList (acc.toList.take (2 * len))
            = toNatLimbsList (acc.toList.take (i + len))
              + toNatLimbsList ((acc.toList.drop (i + len)).take (len - i))
                * 2 ^ (64 * (i + len)) := by
        rw [h_2len_eq]
        exact toNatLimbsList_take_add acc.toList (i + len) (len - i) h_ilen_le
      have h_ilen_eq : i + len = (2 * i + 1) + (len - i - 1) := by omega
      have h_split_acc_inner :
          toNatLimbsList (acc.toList.take (i + len))
            = toNatLimbsList (acc.toList.take (2 * i + 1))
              + toNatLimbsList ((acc.toList.drop (2 * i + 1)).take (len - i - 1))
                * 2 ^ (64 * (2 * i + 1)) := by
        rw [h_ilen_eq]
        exact toNatLimbsList_take_add acc.toList (2 * i + 1) (len - i - 1) h_2i1_le
      have h_split_acc' :
          toNatLimbsList (acc'.toList.take (2 * len))
            = toNatLimbsList (acc'.toList.take (i + len))
              + toNatLimbsList ((acc'.toList.drop (i + len)).take (len - i))
                * 2 ^ (64 * (i + len)) := by
        rw [h_2len_eq]
        exact toNatLimbsList_take_add acc'.toList (i + len) (len - i) h_ilen_le'
      have h_split_acc'_inner :
          toNatLimbsList (acc'.toList.take (i + len))
            = toNatLimbsList (acc'.toList.take (2 * i + 1))
              + toNatLimbsList ((acc'.toList.drop (2 * i + 1)).take (len - i - 1))
                * 2 ^ (64 * (2 * i + 1)) := by
        rw [h_ilen_eq]
        exact toNatLimbsList_take_add acc'.toList (2 * i + 1) (len - i - 1) h_2i1_le'
      -- Prefix equality: acc'.take(2*i+1) = acc.take(2*i+1).
      have h_acc'_take_pref :
          toNatLimbsList (acc'.toList.take (2 * i + 1)) = toNatLimbsList (acc.toList.take (2 * i + 1)) := by
        have h_list_eq : acc'.toList.take (2 * i + 1) = acc.toList.take (2 * i + 1) := by
          rw [hacc'_def, Array.toList_set, List.take_set_of_le (by omega)]
          rw [hr_def]
          exact mulAddLimbs.go_toList_take_le a (lo + i + 1) (len - i - 1) (2 * i + 1)
            a[lo + i] acc 0 0 h_inner_len h_acc_row (2 * i + 1) (by omega)
        rw [h_list_eq]
      -- Middle slice for acc': matches r.1's middle slice.
      have h_acc'_mid :
          (acc'.toList.drop (2 * i + 1)).take (len - i - 1)
            = (r.1.toList.drop (2 * i + 1)).take (len - i - 1) := by
        rw [hacc'_def, Array.toList_set, List.drop_set]
        simp only [show ¬ (2 * i + 1) + (len - i - 1) < 2 * i + 1 from by omega, ↓reduceIte]
        rw [List.take_set_of_le (by omega)]
      -- mulAddLimbs_toNat for the middle slice.
      have h_mac := mulAddLimbs_toNat a (lo + i + 1) (len - i - 1) (2 * i + 1) a[lo + i]
                     acc h_inner_len h_acc_row
      rw [show mulAddLimbs a (lo + i + 1) (len - i - 1) (2 * i + 1) a[lo + i]
            acc h_inner_len h_acc_row = r from hr_def.symm] at h_mac
      change AS * a[lo + i].toNat
          + toNatLimbsList ((acc.toList.drop (2 * i + 1)).take (len - i - 1))
        = toNatLimbsList ((r.1.toList.drop (2 * i + 1)).take (len - i - 1))
          + r.2.toNat * 2 ^ (64 * (len - i - 1)) at h_mac
      -- Tail slice of acc (after i+len): all zero by h_zero.
      have h_tail_acc :
          toNatLimbsList ((acc.toList.drop (i + len)).take (len - i)) = 0 := by
        have h_aux : ∀ (l : List UInt64), (∀ x ∈ l, x = 0) → toNatLimbsList l = 0 := by
          intro l h
          induction l with
          | nil => simp [toNatLimbsList]
          | cons x xs ih_aux =>
            rw [toNatLimbsList_cons]
            have hx : x = 0 := h x (List.mem_cons.mpr (Or.inl rfl))
            have hxs : ∀ y ∈ xs, y = 0 := fun y hy => h y (List.mem_cons.mpr (Or.inr hy))
            rw [ih_aux hxs, hx]; simp
        apply h_aux
        intro x hx
        obtain ⟨j, h_j_lt, hj_eq⟩ := List.mem_iff_getElem.mp hx
        rw [List.length_take, List.length_drop, Array.length_toList] at h_j_lt
        have h_idx_lt : i + len + j < acc.size := by omega
        have h_at : ((acc.toList.drop (i + len)).take (len - i))[j]'(by
            rw [List.length_take, List.length_drop, Array.length_toList]; omega)
                  = acc.toList[i + len + j]'(by rw [Array.length_toList]; omega) := by
          rw [List.getElem_take, List.getElem_drop]
        rw [← hj_eq, h_at, Array.getElem_toList]
        exact h_zero (i + len + j) h_idx_lt (by omega) (by omega)
      -- Tail slice of acc' (after i+len): r.2 at position 0, then zeros.
      have h_drop_r : r.1.toList.drop (i + len) = acc.toList.drop (i + len) := by
        rw [h_ilen_eq, hr_def]
        exact mulAddLimbs.go_toList_drop a (lo + i + 1) (len - i - 1) (2 * i + 1)
          a[lo + i] acc 0 0 h_inner_len h_acc_row
      have h_ilen_lt_r : i + len < r.1.toList.length := by rw [h_len_r]; omega
      have h_tail_acc' :
          toNatLimbsList ((acc'.toList.drop (i + len)).take (len - i)) = r.2.toNat := by
        have h_drop_succ : r.1.toList.drop (i + len + 1) = acc.toList.drop (i + len + 1) := by
          have h := congrArg (List.drop 1) h_drop_r
          simpa [List.drop_drop, Nat.add_comm 1] using h
        have h_form : (acc'.toList.drop (i + len)).take (len - i)
            = r.2 :: (acc.toList.drop (i + len + 1)).take (len - i - 1) := by
          rw [hacc'_def, Array.toList_set, List.drop_set]
          simp only [show ¬ (2 * i + 1) + (len - i - 1) < i + len from by omega, ↓reduceIte]
          rw [show (2 * i + 1) + (len - i - 1) - (i + len) = 0 from by omega]
          rw [List.drop_eq_getElem_cons h_ilen_lt_r, List.set_cons_zero]
          rw [show len - i = (len - i - 1) + 1 from by omega, List.take_succ_cons]
          rw [show (len - i - 1) + 1 - 1 = len - i - 1 from by omega]
          rw [h_drop_succ]
        rw [h_form, toNatLimbsList_cons]
        have h_zero_tail :
            toNatLimbsList ((acc.toList.drop (i + len + 1)).take (len - i - 1)) = 0 := by
          have h_aux : ∀ (l : List UInt64), (∀ x ∈ l, x = 0) → toNatLimbsList l = 0 := by
            intro l h
            induction l with
            | nil => simp [toNatLimbsList]
            | cons x xs ih_aux =>
              rw [toNatLimbsList_cons]
              have hx : x = 0 := h x (List.mem_cons.mpr (Or.inl rfl))
              have hxs : ∀ y ∈ xs, y = 0 := fun y hy => h y (List.mem_cons.mpr (Or.inr hy))
              rw [ih_aux hxs, hx]; simp
          apply h_aux
          intro x hx
          obtain ⟨j, h_j_lt, hj_eq⟩ := List.mem_iff_getElem.mp hx
          rw [List.length_take, List.length_drop, Array.length_toList] at h_j_lt
          have h_idx_lt : i + len + 1 + j < acc.size := by omega
          have h_at : ((acc.toList.drop (i + len + 1)).take (len - i - 1))[j]'(by
              rw [List.length_take, List.length_drop, Array.length_toList]; omega)
                    = acc.toList[i + len + 1 + j]'(by rw [Array.length_toList]; omega) := by
            rw [List.getElem_take, List.getElem_drop]
          rw [← hj_eq, h_at, Array.getElem_toList]
          exact h_zero (i + len + 1 + j) h_idx_lt (by omega) (by omega)
        rw [h_zero_tail]; simp
      -- Assemble.
      rw [h_split_acc, h_split_acc_inner, h_split_acc', h_split_acc'_inner]
      rw [h_acc'_take_pref, h_acc'_mid, h_tail_acc, h_tail_acc']
      have h_pow_ilen : (2 : Nat) ^ (64 * (i + len))
                          = 2 ^ (64 * (2 * i + 1)) * 2 ^ (64 * (len - i - 1)) := by
        rw [← Nat.pow_add]; congr 1; omega
      rw [h_pow_ilen]
      -- Scale h_mac by E1 to bridge the algebraic identity.
      have h_mac_scaled : (AS * a[lo + i].toNat
            + toNatLimbsList ((acc.toList.drop (2 * i + 1)).take (len - i - 1)))
            * 2 ^ (64 * (2 * i + 1))
          = (toNatLimbsList ((r.1.toList.drop (2 * i + 1)).take (len - i - 1))
            + r.2.toNat * 2 ^ (64 * (len - i - 1)))
            * 2 ^ (64 * (2 * i + 1)) := by rw [h_mac]
      -- The remaining identity is purely algebraic.
      generalize toNatLimbsList (acc.toList.take (2 * i + 1)) = P
      generalize toNatLimbsList ((acc.toList.drop (2 * i + 1)).take (len - i - 1)) = M at *
      generalize toNatLimbsList ((r.1.toList.drop (2 * i + 1)).take (len - i - 1)) = M' at *
      generalize a[lo + i].toNat = X at *
      generalize r.2.toNat = R at *
      generalize (2 : Nat) ^ (64 * (2 * i + 1)) = E1 at *
      generalize (2 : Nat) ^ (64 * (len - i - 1)) = E2 at *
      generalize partialOffDiagSum a lo len (i + 1) = Q
      linarith [h_mac_scaled]
    · -- Iter doesn't run; this implies i + 1 = len (since n + 1 ≥ 1 means len - i ≥ 1).
      simp only [h_lt, ↓reduceDIte]
      rw [partialOffDiagSum_terminal a lo len i (by omega)]
      ring

theorem schoolbookSquareLimbs_offDiag_toNat (a : Array UInt64) (lo len : Nat)
    (acc : Array UInt64) (hA : lo + len ≤ a.size) (hAcc : 2 * len ≤ acc.size)
    (h_zero : ∀ k (hk : k < acc.size), acc[k]'hk = (0 : UInt64)) :
    toNatLimbsList (schoolbookSquareLimbs.offDiag a lo len acc hA hAcc).toList
      = offDiagSumAux ((a.toList.drop lo).take len) len := by
  unfold schoolbookSquareLimbs.offDiag
  have h_zero' : ∀ (k : Nat) (hk : k < acc.size), 0 + len ≤ k → k < 2 * len →
      acc[k]'hk = (0 : UInt64) := fun k hk _ _ => h_zero k hk
  have h_go := schoolbookSquareLimbs.offDiag.go_correct a lo len acc 0 hA hAcc h_zero'
  -- Connect the take(2*len) result to the full result via the size invariant.
  have h_go_size : (schoolbookSquareLimbs.offDiag.go a lo len acc 0 hA hAcc).size = acc.size :=
    schoolbookSquareLimbs.offDiag.go_size a lo len acc 0 hA hAcc
  -- The result's toNat over all positions ≥ toNat over first 2*len positions;
  -- but positions beyond 2*len in the result are the unchanged trailing tail of `acc`.
  -- Since the algorithm only touches [0, 2*len), the toNat of the full list
  -- factors as toNat(take 2*len) + toNat(drop 2*len) · 2^(64·2·len).
  -- For the toNat of `acc.toList.take (2*len)`, all positions are zero (by h_zero),
  -- so toNat = 0.
  have h_acc_zero :
      toNatLimbsList (acc.toList.take (2 * len)) = 0 := by
    have h_aux : ∀ (l : List UInt64), (∀ x ∈ l, x = 0) → toNatLimbsList l = 0 := by
      intro l h
      induction l with
      | nil => simp [toNatLimbsList]
      | cons x xs ih =>
        rw [toNatLimbsList_cons]
        have hx : x = 0 := h x (List.mem_cons.mpr (Or.inl rfl))
        have hxs : ∀ y ∈ xs, y = 0 := fun y hy => h y (List.mem_cons.mpr (Or.inr hy))
        rw [ih hxs, hx]; simp
    apply h_aux
    intro x hx
    obtain ⟨i, h_i_lt, hi_eq⟩ := List.mem_iff_getElem.mp hx
    rw [List.length_take, Array.length_toList] at h_i_lt
    have h_i_lt_size : i < acc.size := by omega
    have h_at : (acc.toList.take (2 * len))[i]'(by
        rw [List.length_take, Array.length_toList]; omega)
              = acc.toList[i]'(by rw [Array.length_toList]; omega) := by
      rw [List.getElem_take]
    rw [← hi_eq, h_at, Array.getElem_toList]
    exact h_zero i h_i_lt_size
  -- The result has the same size as acc, and positions ≥ 2*len of `acc` were
  -- zero by `h_zero` and untouched by the algorithm.
  -- Show the algorithm only modifies positions in [0, 2*len).
  -- For now, we use the take(2*len) form of h_go and convert.
  have h_result_eq_take :
      (schoolbookSquareLimbs.offDiag.go a lo len acc 0 hA hAcc).toList
        = ((schoolbookSquareLimbs.offDiag.go a lo len acc 0 hA hAcc).toList.take (2 * len))
          ++ ((schoolbookSquareLimbs.offDiag.go a lo len acc 0 hA hAcc).toList.drop (2 * len)) := by
    rw [List.take_append_drop]
  -- toNatLimbsList of full = toNatLimbsList of take(2*len) + toNatLimbsList of drop(2*len) * 2^(64*2*len),
  -- and the drop(2*len) part is all zero (since acc was zero there and the algorithm doesn't touch it).
  -- TODO: prove this `result.drop (2*len) = acc.drop (2*len)` invariant and that those positions are zero.
  -- For now, we still need the .go_correct, so this is gated on that proof.
  rw [h_result_eq_take, toNatLimbsList_append]
  rw [h_go, h_acc_zero, Nat.zero_add]
  -- partialOffDiagSum a lo len 0 = offDiagSumAux of slice (by partialOffDiagSum_eq_offDiagSumAux).
  rw [partialOffDiagSum_eq_offDiagSumAux a lo len hA]
  -- Trailing zeros from the drop(2*len) tail.
  have h_drop_zero :
      toNatLimbsList ((schoolbookSquareLimbs.offDiag.go a lo len acc 0 hA hAcc).toList.drop (2 * len))
        = 0 := by
    rw [schoolbookSquareLimbs.offDiag.go_toList_drop a lo len acc 0 hA hAcc]
    have h_aux : ∀ (l : List UInt64), (∀ x ∈ l, x = 0) → toNatLimbsList l = 0 := by
      intro l h
      induction l with
      | nil => simp [toNatLimbsList]
      | cons x xs ih =>
        rw [toNatLimbsList_cons]
        have hx : x = 0 := h x (List.mem_cons.mpr (Or.inl rfl))
        have hxs : ∀ y ∈ xs, y = 0 := fun y hy => h y (List.mem_cons.mpr (Or.inr hy))
        rw [ih hxs, hx]; simp
    apply h_aux
    intro x hx
    obtain ⟨i, h_i_lt, hi_eq⟩ := List.mem_iff_getElem.mp hx
    rw [List.length_drop, Array.length_toList] at h_i_lt
    have h_idx_lt : 2 * len + i < acc.size := by omega
    rw [← hi_eq, List.getElem_drop, Array.getElem_toList]
    exact h_zero (2 * len + i) h_idx_lt
  rw [h_drop_zero]; ring

/-! ### Main correctness theorem -/

private lemma toNatLimbsList_replicate_zero (n : Nat) :
    toNatLimbsList (List.replicate n (0 : UInt64)) = 0 := by
  induction n with
  | zero => rfl
  | succ k ih => rw [List.replicate_succ, toNatLimbsList_cons, ih]; simp

private lemma diagSumAux_le (s : List UInt64) (n : Nat) :
    diagSumAux s n ≤ (toNatLimbsList s) ^ 2 := by
  have h_sq := toNatLimbsList_sq_eq s
  by_cases hn : n ≤ s.length
  · have h_mono := diagSumAux_mono s n s.length hn
    omega
  · push Not at hn
    have h_mono := diagSumAux_mono s s.length n (Nat.le_of_lt hn)
    -- For n > s.length: diagSumAux s n stabilizes at diagSumAux s s.length.
    have h_stab : ∀ k, diagSumAux s (s.length + k) = diagSumAux s s.length := by
      intro k
      induction k with
      | zero => rfl
      | succ j ih =>
        rw [show s.length + (j + 1) = (s.length + j) + 1 from by ring, diagSumAux]
        rw [dite_eq_right (by omega : ¬ s.length + j < s.length)]
        rw [Nat.add_zero, ih]
    obtain ⟨k, rfl⟩ : ∃ k, n = s.length + k := ⟨n - s.length, by omega⟩
    rw [h_stab]
    omega

private lemma offDiagSumAux_le (s : List UInt64) (n : Nat) :
    2 * offDiagSumAux s n ≤ (toNatLimbsList s) ^ 2 := by
  have h_sq := toNatLimbsList_sq_eq s
  by_cases hn : n ≤ s.length
  · have h_mono := offDiagSumAux_mono s n s.length hn
    omega
  · push Not at hn
    have h_stab : ∀ k, offDiagSumAux s (s.length + k) = offDiagSumAux s s.length := by
      intro k
      induction k with
      | zero => rfl
      | succ j ih =>
        rw [show s.length + (j + 1) = (s.length + j) + 1 from by ring, offDiagSumAux]
        rw [dite_eq_right (by omega : ¬ s.length + j < s.length)]
        rw [Nat.add_zero, ih]
    obtain ⟨k, rfl⟩ : ∃ k, n = s.length + k := ⟨n - s.length, by omega⟩
    rw [h_stab]
    omega

/-- **Correctness of `schoolbookSquareLimbs`** at the slice level. -/
theorem schoolbookSquareLimbs_toNat (a : Array UInt64) (lo len : Nat)
    (hA : lo + len ≤ a.size) :
    toNatLimbsList (schoolbookSquareLimbs a lo len hA).toList
      = (toNatLimbsList ((a.toList.drop lo).take len)) ^ 2 := by
  unfold schoolbookSquareLimbs
  set s := (a.toList.drop lo).take len with hs_def
  -- Slice length is exactly `len`.
  have h_slice_len : s.length = len := by
    rw [hs_def, List.length_take, List.length_drop, Array.length_toList]
    omega
  -- (toNat s) < 2^(64*len), hence (toNat s)² < 2^(128*len) = 2^(64*(2*len)).
  have h_N_lt : toNatLimbsList s < 2 ^ (64 * len) := by
    have := toNatLimbsList_lt_pow s
    rw [h_slice_len] at this
    exact this
  have h_N_sq_lt : (toNatLimbsList s) ^ 2 < 2 ^ (64 * (2 * len)) := by
    have h_pow_split : (2 : Nat) ^ (64 * (2 * len)) = 2 ^ (64 * len) * 2 ^ (64 * len) := by
      rw [show 64 * (2 * len) = 64 * len + 64 * len from by ring, Nat.pow_add]
    rw [h_pow_split, sq]
    exact Nat.mul_lt_mul_of_lt_of_le h_N_lt (Nat.le_of_lt h_N_lt) (Nat.pow_pos (by norm_num))
  set acc0 : Array UInt64 := Array.replicate (2 * len) 0 with hacc0_def
  have h_acc0_size : acc0.size = 2 * len := by rw [hacc0_def, Array.size_replicate]
  have hAcc0 : 2 * len ≤ acc0.size := by rw [h_acc0_size]
  have h_acc0_toNat : toNatLimbsList acc0.toList = 0 := by
    rw [hacc0_def, Array.toList_replicate]
    exact toNatLimbsList_replicate_zero _
  have h_acc0_zero : ∀ k (hk : k < acc0.size), acc0[k]'hk = (0 : UInt64) := by
    intro k hk
    show (Array.replicate (2 * len) 0)[k]'(by rw [Array.size_replicate]; rw [hacc0_def, Array.size_replicate] at hk; exact hk) = 0
    exact Array.getElem_replicate _
  -- Off-diagonal phase.
  have h_offdiag_bound : offDiagSumAux s len < 2 ^ (64 * acc0.size) := by
    rw [h_acc0_size]
    have h_2od := offDiagSumAux_le s len
    have h_od_le : offDiagSumAux s len ≤ (toNatLimbsList s) ^ 2 := by omega
    omega
  have h_offdiag :=
    schoolbookSquareLimbs_offDiag_toNat a lo len acc0 hA hAcc0 h_acc0_zero
  set acc1 := schoolbookSquareLimbs.offDiag a lo len acc0 hA hAcc0 with hacc1_def
  have hAcc1 : 2 * len ≤ acc1.size := by
    rw [hacc1_def, schoolbookSquareLimbs.offDiag_size]; exact hAcc0
  have h_acc1_size_eq : acc1.size = acc0.size := by
    rw [hacc1_def, schoolbookSquareLimbs.offDiag_size]
  -- Doubling phase.
  have h_acc1_toNat : toNatLimbsList acc1.toList = offDiagSumAux s len := h_offdiag
  have h_double_bound : 2 * toNatLimbsList acc1.toList < 2 ^ (64 * acc1.size) := by
    rw [h_acc1_toNat, h_acc1_size_eq, h_acc0_size]
    have h_2od := offDiagSumAux_le s len
    omega
  have h_double := doubleLimbs_toNat acc1 h_double_bound
  set acc2 := doubleLimbs acc1 with hacc2_def
  have hAcc2 : 2 * len ≤ acc2.size := by
    rw [hacc2_def, doubleLimbs_size]; exact hAcc1
  have h_acc2_size_eq : acc2.size = acc0.size := by
    rw [hacc2_def, doubleLimbs_size]; exact h_acc1_size_eq
  -- Diagonal phase.
  have h_acc2_toNat : toNatLimbsList acc2.toList = 2 * offDiagSumAux s len := by
    rw [h_double, h_acc1_toNat]
  have h_diag_bound :
      toNatLimbsList acc2.toList + diagSumAux s len < 2 ^ (64 * acc2.size) := by
    rw [h_acc2_size_eq, h_acc0_size, h_acc2_toNat]
    have h_sq := toNatLimbsList_sq_eq s
    rw [h_slice_len] at h_sq
    have : 2 * offDiagSumAux s len + diagSumAux s len = (toNatLimbsList s) ^ 2 := by omega
    rw [this]
    exact h_N_sq_lt
  -- Slice equality: s.length = len handled by `h_slice_len`.
  have h_diag := addDiagonalLimbs_toNat a lo len acc2 hA hAcc2 h_diag_bound
  -- Assemble.
  rw [h_diag, h_acc2_toNat]
  -- Goal: 2 * offDiagSumAux s len + diagSumAux s len = (toNat s)²
  show 2 * offDiagSumAux s len + diagSumAux s len = (toNatLimbsList s) ^ 2
  have h_sq := toNatLimbsList_sq_eq s
  rw [h_slice_len] at h_sq
  omega

end Azurite.AzNat
