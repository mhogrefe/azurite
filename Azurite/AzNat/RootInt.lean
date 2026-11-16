/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzNat.Add
import Azurite.AzNat.Basic
import Azurite.AzNat.Compare
import Azurite.AzNat.Conversion
import Azurite.AzNat.Div
import Azurite.AzNat.Mul
import Azurite.AzNat.Pow
import Azurite.AzNat.ShiftLeft
import Azurite.AzNat.ShiftRight
import Azurite.AzNat.Size
import Mathlib.Data.Nat.Size

namespace Azurite.AzNat

/-!
Integer `k`-th root for `AzNat`: MCA Algorithm 1.14 (`RootInt`,
Brent–Zimmermann, *Modern Computer Arithmetic* §1.5.2).

  ```
  u ← m                      (any u ≥ ⌊m^(1/k)⌋ works)
  repeat
    s ← u
    t ← (k−1)·s + ⌊m / s^(k−1)⌋
    u ← ⌊t / k⌋
  until u ≥ s
  return s
  ```

MCA Theorem 1.7: the loop terminates and returns `⌊m^(1/k)⌋`.  The
`s`-values strictly decrease until the exit test fires; the exit test
`u ≥ s` forces `s^k ≤ m`; and every iterate stays `≥ ⌊m^(1/k)⌋`
because the Newton map `f(s) = ((k−1)s + m/s^(k−1))/k` is `≥ m^(1/k)`
(weighted AM–GM).  The proof in `Equiv/RootInt.lean` renders the AM–GM
step as the integer tangent-line inequality
`k·r·s^(k−1) ≤ r^k + (k−1)·s^k` (Bernoulli), and carries the invariant
"`s` bounds every `y` with `y^k ≤ m`" rather than talking about a
real root.

Design, as for `basecaseSqrt` (the `k = 2` case):

  - Initial guess `u₀ = 2^⌈b/k⌉` with `b = AzNat.size m` the bit
    length: `m < 2^b ≤ (2^⌈b/k⌉)^k`, so `u₀ > ⌊m^(1/k)⌋`, and `u₀` is
    within a factor `2` of the root — the iteration starts in its
    fast-convergence regime instead of at `u = m`.
  - Fuel `u₀ + 1` (as a `Nat`, never approached: each step strictly
    decreases `s`), so the recursion is structural.
  - Body in `AzNat` arithmetic: `pow`, `div`, `mul` by the small
    constant `k − 1`, `add`, `div` by `k`, and one comparison.

A ℕ reference `rootIntNat` with the same loop is the specification;
`toNat_rootInt` identifies the two, and `rootIntNat_spec` gives the
characterizing bounds `s^k ≤ m < (s+1)^k`.  Conventions: `k = 1`
returns `m`; `k = 0` is out of scope (returns `m`); `m = 0` returns `0`.
-/

/-- **MCA Algorithm 1.14, ℕ reference — the loop.**  `fuel` bounds the
iteration count; from `s`, compute `u = ⌊((k−1)s + ⌊m/s^(k−1)⌋)/k⌋` and
recurse on `u` while `u < s`. -/
def rootIntNat.loop (m k : ℕ) : ℕ → ℕ → ℕ
  | 0, s => s
  | fuel + 1, s =>
    if ((k - 1) * s + m / s ^ (k - 1)) / k < s
    then rootIntNat.loop m k fuel (((k - 1) * s + m / s ^ (k - 1)) / k)
    else s

/-- **MCA Algorithm 1.14, ℕ reference**: `⌊m^(1/k)⌋`, from the initial
guess `2^⌈b/k⌉` (`b` the bit length of `m`) with fuel `2^⌈b/k⌉ + 1`. -/
def rootIntNat (m k : ℕ) : ℕ :=
  if k ≤ 1 then m
  else rootIntNat.loop m k (2 ^ ((m.size + k - 1) / k) + 1) (2 ^ ((m.size + k - 1) / k))

/-- Initial guess `2^⌈b/k⌉` with `b = AzNat.size m`. -/
def rootInt.initialGuess (m : AzNat) (k : ℕ) : AzNat :=
  (1 : AzNat) <<< ((m.size + k - 1) / k)

/-- **The Newton loop on `AzNat`**: `t ← (k−1)·s + m / s^(k−1)`,
`u ← t / k`; recurse on `u` while `u < s`. -/
def rootInt.loop (m : AzNat) (k : ℕ) : ℕ → AzNat → AzNat
  | 0, s => s
  | fuel + 1, s =>
    let t := ofNat (k - 1) * s + m / s.pow (k - 1)
    let u := t / ofNat k
    if u < s then rootInt.loop m k fuel u else s

/-- **Bisection refinement of the initial guess.**  `hi` bounds the root from above
throughout; each step tests the midpoint of `[lo, hi]` and keeps `hi` an upper bound.  Starting
from `hi = 2^⌈b/k⌉` (within a factor `2` of the root) Newton's iteration contracts only by
`1 − 1/k` per step until the relative error drops below about `1/k`, that is for about
`k ln 2` steps; `log₂ k + 1` bisection steps bring it there directly. -/
def rootInt.refine (m : AzNat) (k : ℕ) : ℕ → AzNat → AzNat → AzNat
  | 0, _, hi => hi
  | n + 1, lo, hi =>
    let mid := (lo + hi) >>> 1
    if m < mid.pow k then rootInt.refine m k n lo mid else rootInt.refine m k n mid hi

/-- The starting point of Newton's iteration: `2^⌈b/k⌉`, refined when `k ≥ 8` by `size k`
bisection steps (at most `⌈b/k⌉`, the bit length of the guess: a tiny root needs none).  When
`k` divides the bit length `b` the guess `2^(b/k)` is already within a factor `2^(1/k)` of the
root and is kept. -/
def rootInt.start (m : AzNat) (k : ℕ) : AzNat :=
  let hi := rootInt.initialGuess m k
  if k < 8 ∨ m.size % k = 0 then hi
  else rootInt.refine m k (min k.size ((m.size + k - 1) / k)) (hi >>> 1) hi

/-- **Integer `k`-th root** `⌊m^(1/k)⌋` (MCA Algorithm 1.14) on `AzNat`;
`k = 1` returns `m`.  When `k` is at least the bit length of `m` the root is `1` (or `0` for
`m = 0`) since `m < 2^k`, and it is returned without iterating: the Newton step would start
by computing `2^(k − 1)`, a number of `k` bits, however small `m` is. -/
def rootInt (m : AzNat) (k : ℕ) : AzNat :=
  if k ≤ 1 then m
  else if m.size ≤ k then ofNat (if m.size = 0 then 0 else 1)
  else rootInt.loop m k ((1 : ℕ) <<< ((m.size + k - 1) / k) + 1) (rootInt.start m k)

/-- **Perfect-`k`-th-power test**: `m = y^k` for some `y` iff
`(⌊m^(1/k)⌋)^k = m`. -/
def isPow (m : AzNat) (k : ℕ) : Bool :=
  decide ((rootInt m k).pow k = m)

-- ℕ reference sanity
#guard rootIntNat 1000000 3 = 100
#guard rootIntNat 999999 3 = 99
#guard rootIntNat 1000001 3 = 100
#guard rootIntNat (2 ^ 200) 5 = 2 ^ 40
#guard rootIntNat (2 ^ 200 - 1) 5 = 2 ^ 40 - 1
#guard rootIntNat 0 7 = 0
#guard rootIntNat 1 7 = 1
#guard rootIntNat 127 7 = 1
#guard rootIntNat 128 7 = 2
#guard rootIntNat 12345 1 = 12345

end Azurite.AzNat
