/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzNat.Gcd
import Azurite.AzNat.Montgomery
import Azurite.AzNat.OfLimbs
import Azurite.AzNat.Size
import Azurite.UInt64.MulAddWithCarry
import Azurite.UInt64.MulWithCarry

/-!
# Pollard's rho method for numbers of two machine words

Brent's algorithm (`Azurite/AzNat/PollardRho.lean` has the description) for an odd `n` of
64 to 126 bits (below that `Word.factorWord` does the work), with every residue held in two `UInt64` words and the loops written as
recursions on words, so that a term of the sequence costs no allocation.  A search: nothing
is proven, and `AzNat.factor` checks what it returns.

Montgomery arithmetic with `R = 2^128`: `mulMont a b = a b R⁻¹ mod n` from the four-word
product and two rounds that each clear the lowest word by adding a multiple of `n`.  Since
`n < 2^126`, nothing overflows the four words and the result before the final subtraction
is below `2n`.  The conditional subtractions are written without a branch on a pair (the
subtrahend is `n` or `0`, chosen word by word), which keeps the words in registers.
-/

namespace Azurite.AzNat.TwoWord

/-- `(a₁, a₀) − (s₁, s₀)` when `(a₁, a₀) ≥ (n₁, n₀)` with `s = n`, and `a` itself otherwise:
reduction of a number below `2n` modulo `n`. -/
@[inline] def reduce (n₁ n₀ a₁ a₀ : UInt64) : UInt64 × UInt64 :=
  let ge := n₁ < a₁ || (a₁ == n₁ && n₀ ≤ a₀)
  let s₀ := if ge then n₀ else 0
  let s₁ := if ge then n₁ else 0
  (a₁ - s₁ - (if a₀ < s₀ then 1 else 0), a₀ - s₀)

/-- `a b R⁻¹ mod n` for `a, b < n < 2^126`, `n` odd, `ninv = −n⁻¹ mod 2^64`. -/
@[inline] def mulMont (n₁ n₀ ninv a₁ a₀ b₁ b₀ : UInt64) : UInt64 × UInt64 :=
  -- the product `t₃ t₂ t₁ t₀`
  let p₀₀ := UInt64.mulWithCarry a₀ b₀ 0
  let p₀₁ := UInt64.mulWithCarry a₀ b₁ p₀₀.1
  let p₁₀ := UInt64.mulWithCarry a₁ b₀ p₀₁.2
  let p₁₁ := UInt64.mulAddWithCarry a₁ b₁ p₀₁.1 p₁₀.1
  let t₀ := p₀₀.2
  let t₁ := p₁₀.2
  let t₂ := p₁₁.2
  let t₃ := p₁₁.1
  -- clear `t₀`
  let m := t₀ * ninv
  let c₀ := UInt64.mulAddWithCarry m n₀ t₀ 0
  let c₁ := UInt64.mulAddWithCarry m n₁ t₁ c₀.1
  let u₁ := c₁.2
  let u₂ := t₂ + c₁.1
  let u₃ := t₃ + (if u₂ < t₂ then 1 else 0)
  -- clear `u₁`
  let m' := u₁ * ninv
  let d₀ := UInt64.mulAddWithCarry m' n₀ u₁ 0
  let d₁ := UInt64.mulAddWithCarry m' n₁ u₂ d₀.1
  reduce n₁ n₀ (u₃ + d₁.1) d₁.2

/-- `a + b mod n` for `a, b < n < 2^126`. -/
@[inline] def addMod (n₁ n₀ a₁ a₀ b₁ b₀ : UInt64) : UInt64 × UInt64 :=
  let s₀ := a₀ + b₀
  reduce n₁ n₀ (a₁ + b₁ + (if s₀ < a₀ then 1 else 0)) s₀

/-- `|a − b|`. -/
@[inline] def absDiff (a₁ a₀ b₁ b₀ : UInt64) : UInt64 × UInt64 :=
  let lt := a₁ < b₁ || (a₁ == b₁ && a₀ < b₀)
  let x₁ := if lt then b₁ else a₁
  let x₀ := if lt then b₀ else a₀
  let y₁ := if lt then a₁ else b₁
  let y₀ := if lt then a₀ else b₀
  (x₁ - y₁ - (if x₀ < y₀ then 1 else 0), x₀ - y₀)

/-- One term of the sequence: `y² R⁻¹ + c mod n`. -/
@[inline] def next (n₁ n₀ ninv c₁ c₀ y₁ y₀ : UInt64) : UInt64 × UInt64 :=
  let s := mulMont n₁ n₀ ninv y₁ y₀ y₁ y₀
  addMod n₁ n₀ s.1 s.2 c₁ c₀

/-- `k` terms from `y`. -/
def advance (n₁ n₀ ninv c₁ c₀ : UInt64) : Nat → UInt64 → UInt64 → UInt64 × UInt64
  | 0, y₁, y₀ => (y₁, y₀)
  | k + 1, y₁, y₀ =>
    let s := next n₁ n₀ ninv c₁ c₀ y₁ y₀
    advance n₁ n₀ ninv c₁ c₀ k s.1 s.2

/-- `k` terms from `y`, multiplying the differences `|x − y|` into `q`: the new `y` and
`q`. -/
def batch (n₁ n₀ ninv c₁ c₀ x₁ x₀ : UInt64) :
    Nat → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 × UInt64 × UInt64 × UInt64
  | 0, y₁, y₀, q₁, q₀ => (y₁, y₀, q₁, q₀)
  | k + 1, y₁, y₀, q₁, q₀ =>
    let s := next n₁ n₀ ninv c₁ c₀ y₁ y₀
    let d := absDiff x₁ x₀ s.1 s.2
    let q := mulMont n₁ n₀ ninv q₁ q₀ d.1 d.2
    batch n₁ n₀ ninv c₁ c₀ x₁ x₀ k s.1 s.2 q.1 q.2

/-- The two words as a number. -/
def toAzNat (a₁ a₀ : UInt64) : AzNat := ofLimbs #[a₀, a₁]

/-- **Brent's rho algorithm in two machine words**: a divisor of the odd composite
`n < 2^126` strictly between `1` and `n`, with the constant `c` (a machine word below `n`),
`batchSize` differences per gcd and at most about `budget` terms; with the number of terms
computed. -/
def rhoBrent (n : AzNat) (c : UInt64) (batchSize budget : Nat) : Option AzNat × Nat :=
  Id.run do
    if n.size > 126 || n.size ≤ 63 then return (none, 0)
    let n₀ := n.limbs.getD 0 0
    let n₁ := n.limbs.getD 1 0
    let ninv := montNegInv n₀
    let mut y₁ : UInt64 := 0
    let mut y₀ : UInt64 := 2
    let mut q₁ : UInt64 := 0
    let mut q₀ : UInt64 := 1
    let mut r := 1
    let mut used := 0
    for _ in [0:126] do
      if used ≥ budget then return (none, used)
      let x₁ := y₁
      let x₀ := y₀
      let a := advance n₁ n₀ ninv 0 c r y₁ y₀
      y₁ := a.1
      y₀ := a.2
      used := used + r
      let mut k := 0
      let mut g : AzNat := 1
      let mut ys₁ := y₁
      let mut ys₀ := y₀
      for _ in [0:r] do
        if k ≥ r || g ≠ 1 then break
        ys₁ := y₁
        ys₀ := y₀
        let lim := min batchSize (r - k)
        let b := batch n₁ n₀ ninv 0 c x₁ x₀ lim y₁ y₀ q₁ q₀
        y₁ := b.1
        y₀ := b.2.1
        q₁ := b.2.2.1
        q₀ := b.2.2.2
        g := gcd (toAzNat q₁ q₀) n
        k := k + lim
        used := used + lim
      if g ≠ 1 then
        if g = n then
          g := 1
          for _ in [0:batchSize + 1] do
            if g ≠ 1 then break
            let s := next n₁ n₀ ninv 0 c ys₁ ys₀
            ys₁ := s.1
            ys₀ := s.2
            let d := absDiff x₁ x₀ ys₁ ys₀
            g := gcd (toAzNat d.1 d.2) n
        return (if g = n || g = 1 then none else some g, used)
      r := 2 * r
    return (none, used)

end Azurite.AzNat.TwoWord

section Tests

open Azurite Azurite.AzNat

private def N (k : Nat) : AzNat := ofNat k

/-- The Montgomery product of two words against its definition: `mulMont a b · 2^128 ≡ a b`
and `mulMont a b < n`. -/
private def mulOk (n a b : Nat) : Bool :=
  let w (x : Nat) : UInt64 × UInt64 := ((x / 2 ^ 64).toUInt64, (x % 2 ^ 64).toUInt64)
  let r := TwoWord.mulMont (w n).1 (w n).2 (montNegInv (w n).2) (w a).1 (w a).2 (w b).1 (w b).2
  let v := r.1.toNat * 2 ^ 64 + r.2.toNat
  v < n && (v * 2 ^ 128) % n == (a * b) % n

#guard mulOk (2 ^ 100 + 277) 3 5 && mulOk (2 ^ 100 + 277) (2 ^ 100 + 276) (2 ^ 100 + 276)
#guard mulOk (2 ^ 126 - 137) (2 ^ 126 - 138) (2 ^ 126 - 138) && mulOk (2 ^ 126 - 137) 0 7
#guard (List.range 300).all fun i =>
  let n := 2 ^ 125 + 2 ^ 70 * (i * i + 1) + 2 * i + 1
  mulOk n ((3 ^ (60 + i)) % n) ((7 ^ (40 + i)) % n)
#guard (List.range 100).all fun i =>
  let n := 2 ^ 64 + 2 * i + 1
  mulOk n ((3 ^ (60 + i)) % n) ((7 ^ (40 + i)) % n)
#guard TwoWord.addMod 1 5 1 3 0 4 == (0, 2) && TwoWord.addMod 1 5 0 3 0 4 == (0, 7)
#guard TwoWord.absDiff 1 0 0 1 == (0, 18446744073709551615) && TwoWord.absDiff 0 1 1 0 ==
  (0, 18446744073709551615)

private def splits (n : Nat) : Bool :=
  match (TwoWord.rhoBrent (N n) 1 64 4000000).1 with
  | some d => 1 < d.toNat && d.toNat < n && n % d.toNat == 0
  | none => false

#guard splits (1000003 * (2 ^ 61 - 1))
#guard splits (1000003 * (10 ^ 30 + 57))
#guard splits ((2 ^ 31 - 1) * (2 ^ 61 - 1))
#guard splits (4294967311 * 4294967357 * 4294967371)
#guard splits ((2 ^ 61 - 1) * (2 ^ 61 - 1) * 5)
-- exactly 64 bits
#guard splits (2000000011 * 7000000001)
-- outside its range: less than 64 bits, or more than 126
#guard (TwoWord.rhoBrent (N (10007 * 10009)) 1 64 1000).1 == none
#guard (TwoWord.rhoBrent (N (1000003 * (10 ^ 50 + 151))) 1 64 1000).1 == none

end Tests
