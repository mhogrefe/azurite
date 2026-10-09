/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzNat.MultiFactorial
import Azurite.AzNat.Equiv.DoubleFactorial
import Azurite.AzNat.Equiv.Pow
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Nat.Factorial.BigOperators

/-!
## The multifactorial and its correctness

`Nat.multiFactorial` satisfies the recurrence `(n + m)!⁽ᵐ⁾ = (n + m) · n!⁽ᵐ⁾`
(`Nat.multiFactorial_add`), from which the factorial and double factorial cases, the closed
forms `(q m)!⁽ᵐ⁾ = m^q q!` and `(q m + r)!⁽ᵐ⁾ = ∏_{i ≤ q} (i m + r)` follow by induction;
`toNat_multiFactorial` then checks each branch of `AzNat.multiFactorial`.
-/

namespace Nat

open scoped Nat

theorem multiFactorial_zero (m : ℕ) : multiFactorial m 0 = 1 := by
  unfold multiFactorial
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm; rfl
  · rw [show (0 + m - 1) / m = 0 from Nat.div_eq_of_lt (by omega)]; rfl

/-- The recurrence `(n + m)!⁽ᵐ⁾ = (n + m) · n!⁽ᵐ⁾`. -/
theorem multiFactorial_add (m n : ℕ) (hm : 1 ≤ m) :
    multiFactorial m (n + m) = (n + m) * multiFactorial m n := by
  unfold multiFactorial
  rw [show n + m + m - 1 = (n + m - 1) + m by omega, Nat.add_div_right _ hm,
    Finset.prod_range_succ', Nat.zero_mul, Nat.sub_zero, mul_comm]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  rw [add_mul, one_mul, Nat.add_sub_add_right]

theorem multiFactorial_of_le (m n : ℕ) (h1 : 1 ≤ n) (hnm : n ≤ m) : multiFactorial m n = n := by
  unfold multiFactorial
  rw [show (n + m - 1) / m = 1 from Nat.div_eq_of_lt_le (by omega) (by omega),
    Finset.prod_range_one, Nat.zero_mul, Nat.sub_zero]

theorem multiFactorial_one (n : ℕ) : multiFactorial 1 n = n ! := by
  induction n with
  | zero => rw [multiFactorial_zero]; rfl
  | succ n ih => rw [multiFactorial_add 1 n le_rfl, ih, Nat.factorial_succ]

theorem multiFactorial_two (n : ℕ) : multiFactorial 2 n = n‼ := by
  induction n using Nat.twoStepInduction with
  | zero => rw [multiFactorial_zero]; rfl
  | one => rw [multiFactorial_of_le 2 1 le_rfl (by norm_num)]; rfl
  | more n ih _ => rw [multiFactorial_add 2 n (by norm_num), ih, Nat.doubleFactorial_add_two]

/-- `(q m)!⁽ᵐ⁾ = m^q · q!`. -/
theorem multiFactorial_mul (m : ℕ) (hm : 1 ≤ m) : ∀ q, multiFactorial m (q * m) = m ^ q * q ! := by
  intro q
  induction q with
  | zero => rw [Nat.zero_mul, multiFactorial_zero]; rfl
  | succ q ih =>
    rw [add_mul, one_mul, multiFactorial_add m _ hm, ih, pow_succ, Nat.factorial_succ]
    ring

/-- `(q m + r)!⁽ᵐ⁾ = ∏_{i ≤ q} (i m + r)` for `1 ≤ r ≤ m`. -/
theorem multiFactorial_mul_add (m r : ℕ) (hr1 : 1 ≤ r) (hrm : r ≤ m) :
    ∀ q, multiFactorial m (q * m + r) = ∏ i ∈ Finset.range (q + 1), (i * m + r) := by
  intro q
  induction q with
  | zero => rw [Nat.zero_mul, zero_add, multiFactorial_of_le m r hr1 hrm]; simp
  | succ q ih =>
    rw [show (q + 1) * m + r = (q * m + r) + m by ring, multiFactorial_add m _ (by omega), ih,
      Finset.prod_range_succ (fun i => i * m + r) (q + 1)]
    ring

end Nat

namespace Azurite.AzNat

theorem prod_map_range (g : ℕ → ℕ) :
    ∀ n, ((List.range n).map g).prod = ∏ i ∈ Finset.range n, g i := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih => rw [List.prod_range_succ, ih, Finset.prod_range_succ]

/-- **Correctness of `multiFactorial`.** -/
theorem toNat_multiFactorial (m n : ℕ) : (multiFactorial m n).toNat = Nat.multiFactorial m n := by
  unfold multiFactorial
  split_ifs with h0 h1 h2 hr
  · subst h0
    unfold Nat.multiFactorial
    rw [Nat.div_zero, Finset.prod_range_zero]
    exact toNat_one
  · subst h1
    rw [toNat_factorial, Nat.multiFactorial_one]
  · subst h2
    rw [toNat_doubleFactorial, Nat.multiFactorial_two]
  · have hn : n = (n / m) * m := by
      rw [Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero hr)]
    rw [toNat_mul, toNat_pow, toNat_ofNat, toNat_factorial]
    conv_rhs => rw [hn]
    rw [Nat.multiFactorial_mul m (by omega)]
  · have hn : n = (n / m) * m + n % m := by rw [mul_comm, Nat.div_add_mod]
    rw [toNat_prodList, List.map_map]
    conv_rhs => rw [hn]
    rw [Nat.multiFactorial_mul_add m (n % m) (by omega) (Nat.mod_lt _ (by omega)).le]
    rw [show (toNat ∘ fun i => ofNat (i * m + n % m)) = fun i => i * m + n % m from
      funext fun i => by simp [toNat_ofNat]]
    exact prod_map_range _ _

end Azurite.AzNat
