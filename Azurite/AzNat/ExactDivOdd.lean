/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzNat.OfLimbs
import Azurite.UInt64.WideMul
import Azurite.UInt64.SubWithBorrow

/-!
# Exact division by an odd limb

Jebelean's exact division (Brent–Zimmermann, *Modern Computer Arithmetic*, Algorithm 1.10,
specialized to a single-limb divisor): when `d` is odd and `d ∣ N`, the quotient `Q = N / d` is
produced limb by limb from the *low* end using the inverse `dinv = d⁻¹ mod 2^64`.

Write `β = 2^64` and let `T_i` be the value of the limbs of `N` from position `i` up.  Before step
`i` the state `(hi, borrow)` satisfies `T_i = hi + borrow + d · (Q / β^i)`.  Step `i` computes
`r := n_i − hi − borrow` (with a new borrow), which is congruent to `d · (Q / β^i)` modulo `β`, so
`q_i := r · dinv mod β` is the `i`-th limb of `Q`; then `q_i · d = hi' · β + r` exactly, and the
invariant is restored with `(hi', borrow')`.  No trial division, no normalization, one multiply
and one wide multiply per limb.

The inverse is passed in as a constant (for the divisors used in Toom–Cook interpolation it is a
literal, checked by `decide`); `exactDivOdd_toNat` in `Equiv/ExactDivOdd.lean` proves the result
equals `N / d` whenever `d · dinv = 1` and `d ∣ N`.
-/

namespace Azurite.AzNat

/-- The limb loop: `acc` holds the quotient limbs below `i`; `(hi, borrow)` is the carry state. -/
def exactDivOddLimbs.go (d dinv : UInt64) (a : Array UInt64) (lo len : Nat)
    (hA : lo + len ≤ a.size) (acc : Array UInt64) (i : Nat) (hi : UInt64) (borrow : Bool) :
    Array UInt64 :=
  if h : i < len then
    have h_idx : lo + i < a.size := by omega
    let sb := UInt64.subWithBorrow (a[lo + i]'h_idx) hi borrow
    let q := sb.1 * dinv
    let hi' := (UInt64.wideMul q d).1
    exactDivOddLimbs.go d dinv a lo len hA (acc.push q) (i + 1) hi' sb.2
  else acc
  termination_by len - i

/-- Exact quotient of the `len`-limb slice `a[lo, lo + len)` by the odd limb `d` with inverse
`dinv`, as a fresh `len`-limb array.  Only meaningful when `d ∣` the slice's value. -/
def exactDivOddLimbs (d dinv : UInt64) (a : Array UInt64) (lo len : Nat)
    (hA : lo + len ≤ a.size) : Array UInt64 :=
  exactDivOddLimbs.go d dinv a lo len hA #[] 0 0 false

theorem exactDivOddLimbs.go_size (d dinv : UInt64) (a : Array UInt64) (lo len : Nat)
    (hA : lo + len ≤ a.size) :
    ∀ (n : Nat) (acc : Array UInt64) (i : Nat) (hi : UInt64) (borrow : Bool), len - i = n →
      (exactDivOddLimbs.go d dinv a lo len hA acc i hi borrow).size = acc.size + (len - i) := by
  intro n
  induction n with
  | zero =>
    intro acc i hi borrow hn
    rw [exactDivOddLimbs.go, dite_eq_right (by omega)]
    omega
  | succ n ih =>
    intro acc i hi borrow hn
    have h : i < len := by omega
    rw [exactDivOddLimbs.go, dite_eq_left h]
    simp only []
    rw [ih _ (i + 1) _ _ (by omega), Array.size_push]
    omega

theorem exactDivOddLimbs_size (d dinv : UInt64) (a : Array UInt64) (lo len : Nat)
    (hA : lo + len ≤ a.size) : (exactDivOddLimbs d dinv a lo len hA).size = len := by
  unfold exactDivOddLimbs
  rw [exactDivOddLimbs.go_size d dinv a lo len hA (len - 0) #[] 0 0 false rfl]
  simp

/-- `n / d` for an odd limb `d` with `d · dinv = 1` (as `UInt64`s), assuming `d ∣ n`. -/
def exactDivOdd (d dinv : UInt64) (n : AzNat) : AzNat :=
  ofLimbs (exactDivOddLimbs d dinv n.limbs 0 n.limbs.size (by simp))

/-- `3⁻¹ mod 2^64`. -/
def inv3 : UInt64 := 12297829382473034411
/-- `5⁻¹ mod 2^64`. -/
def inv5 : UInt64 := 14757395258967641293
/-- `9⁻¹ mod 2^64`. -/
def inv9 : UInt64 := 10248191152060862009
/-- `45⁻¹ mod 2^64`. -/
def inv45 : UInt64 := 5738987045154082725

theorem mul_inv3 : (3 : UInt64) * inv3 = 1 := by decide
theorem mul_inv5 : (5 : UInt64) * inv5 = 1 := by decide
theorem mul_inv9 : (9 : UInt64) * inv9 = 1 := by decide
theorem mul_inv45 : (45 : UInt64) * inv45 = 1 := by decide

end Azurite.AzNat
