/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.Algorithm.PrimeSieve
import Azurite.AzNat.IsSquare
import Azurite.AzNat.ModPow2
import Azurite.AzNat.MulModPow2.Dispatch
import Azurite.AzNat.Pow
import Azurite.AzNat.RootInt
import Azurite.AzNat.ShiftLeft
import Azurite.AzNat.ShiftRight
import Azurite.AzNat.Size
import Azurite.AzNat.SqrtRem
import Azurite.AzNat.SquareModPow2.Dispatch
import Azurite.AzNat.TrailingZeros

/-!
# Perfect powers by 2-adic roots

`isPerfectPower n` decides whether `n = x ^ k` for some `k > 1`, and `expressAsPower n` gives
such `x` and `k` with `x` not itself a perfect power.  The method is the 2-adic variant of
D. J. Bernstein, *Detecting perfect powers in essentially linear time*, Math. Comp. 67 (1998),
§21–§22; the theory is in `Azurite/Bernstein/PerfectPower.lean`, the proofs in
`Azurite/AzNat/Equiv/PerfectPower.lean`.

Write `n = 2 ^ e m` with `m` odd.  A `p`-th root of `n` (`p` prime) is `2 ^ (e/p)` times one
of `m`, and `p` divides `e`; so the exponents to try are the primes dividing `e`, or, for odd
`n`, the primes below its bit length `f`.  For an odd `p` and an odd `m` of `f` bits a root
has at most `b = ⌈f/p⌉` bits, and is determined modulo `2 ^ b` by `r ^ p ≡ m`: such an `r` is
found by Newton's iteration `z ← z + z (1 − zᵖ y)/p` for the inverse `p`-th root of
`y = m⁻¹`, doubling the number of bits (`rootHint`; `y` is computed once for all `p`).  Then
`r ^ p` is computed modulo `2 ^ (2b)`: if it differs from `m` there, `m` is not a `p`-th
power — the usual case, at the cost of a few products of `2f/p` bits — and only otherwise is
`r ^ p` computed in full.  Squares go through `isSquare` and `sqrt`.

What is proven does not depend on the Newton iterations (`invModPow2Hint`, `rootHint`), which
only supply the candidate `r`: `oddRoot?` checks `r ^ p ≡ m (mod 2 ^ b)` itself, and falls
back on `rootInt` (`kthRoot?`) should it ever fail.
-/

namespace Azurite.AzNat

/-- `r ^ k mod 2 ^ b` by the left-to-right binary method, every product truncated. -/
def powModPow2 (r : AzNat) (b : Nat) : Nat → AzNat
  | 0 => (1 : AzNat).modPow2 b
  | k + 1 =>
    let s := squareDispatchModPow2 (powModPow2 r b ((k + 1) / 2)) b
    if (k + 1) % 2 = 1 then mulDispatchModPow2 s r b else s
decreasing_by omega

/-- `2 ^ b + x − y mod 2 ^ b`, for `y < 2 ^ b`. -/
def subLow (x y : AzNat) (b : Nat) : AzNat := (((1 : AzNat) <<< b) + x - y).modPow2 b

/-- Newton's iteration `y ← y (2 − a y)` for the inverse of an odd `a` modulo `2 ^ b`, from
`prec` correct bits (not verified: a hint). -/
def invModPow2Hint.go (a : AzNat) (b : Nat) : Nat → Nat → AzNat → AzNat
  | 0, _, y => y
  | fuel + 1, prec, y =>
    if b ≤ prec then y
    else
      let q := min (2 * prec) b
      let t := mulDispatchModPow2 (a.modPow2 q) y q
      invModPow2Hint.go a b fuel q (mulDispatchModPow2 y (subLow (ofNat 2) t q) q)

/-- The inverse of an odd `a` modulo `2 ^ b` (not verified: a hint for `rootHint`). -/
def invModPow2Hint (a : AzNat) (b : Nat) : AzNat :=
  invModPow2Hint.go a b (b + 1) 1 ((1 : AzNat).modPow2 b)

/-- Newton's iteration for a `k`-th root modulo `2 ^ b` of the inverse of `y` (`k` and `y`
odd, `kinv` the inverse of `k`): from `z` at `⌈b/2⌉` bits, `(z (k + 1) − y z^(k+1)) / k`
(Bernstein's Algorithm N2; not verified: a hint for `oddRoot?`). -/
def rootHint (y kinv : AzNat) (k : Nat) : Nat → AzNat
  | 0 => 0
  | 1 => 1
  | b + 2 =>
    let B := b + 2
    let z := rootHint y kinv k ((b + 3) / 2)
    let r2 := mulDispatchModPow2 z (ofNat (k + 1)) B
    let r3 := mulDispatchModPow2 (y.modPow2 B) (powModPow2 z B (k + 1)) B
    mulDispatchModPow2 (subLow r2 r3 B) (kinv.modPow2 B) B
decreasing_by omega

/-- **A `k`-th root by `rootInt`**: `some x` with `x ^ k = m` if there is one. -/
def kthRoot? (m : AzNat) (k : Nat) : Option AzNat :=
  if isPow m k then some (rootInt m k) else none

/-- **A `k`-th root of an odd `m` for odd `k`** (`y` a hint: the inverse of `m` modulo
`2 ^ ⌈f/k⌉`, `f` the bit length of `m`): `some x` with `x ^ k = m` if there is one. -/
def oddRoot? (m y : AzNat) (k : Nat) : Option AzNat :=
  let b := (m.size + k - 1) / k
  let r := (rootHint y (invModPow2Hint (ofNat k) b) k b).modPow2 b
  let p := powModPow2 r (2 * b) k
  if p.modPow2 b ≠ m.modPow2 b then kthRoot? m k
  else if p ≠ m.modPow2 (2 * b) then none
  else if r.pow k = m then some r else none

/-- **A `p`-th root of an odd `m`** (`y` as in `oddRoot?`): squares by `isSquare`, odd `p` by
`oddRoot?`. -/
def primeRoot? (m y : AzNat) (p : Nat) : Option AzNat :=
  if p = 2 then (if isSquare m then some (sqrt m) else none)
  else if p % 2 = 1 then oddRoot? m y p
  else kthRoot? m p

/-- **One perfect-power step**: a prime `p` and `x` with `x ^ p = n`, if `n ≥ 2` is a perfect
power (the least such `p`); `none` otherwise, and for `n ≤ 1`. -/
def perfectPowerStep (n : AzNat) : Option (AzNat × Nat) :=
  match n.trailingZeros with
  | none => none
  | some e =>
    let m := n >>> e
    let f := m.size
    let cands := if e = 0 then primesUpTo f else (primesUpTo e).filter (e % · = 0)
    let y := invModPow2Hint m ((f + 2) / 3)
    cands.toList.findSome? fun p =>
      (primeRoot? m y p).map fun (r : AzNat) => ((r <<< (e / p) : AzNat), p)

/-- Repeat `perfectPowerStep` on the root, multiplying the exponents. -/
def expressAsPower.go : Nat → AzNat → Nat → AzNat × Nat
  | 0, x, k => (x, k)
  | fuel + 1, x, k =>
    match perfectPowerStep x with
    | none => (x, k)
    | some (r, p) => expressAsPower.go fuel r (k * p)

/-- **Perfect-power decomposition**: `some (x, k)` with `x ^ k = n` and `k > 1` if `n` is a
perfect power, where `x` is not a perfect power when `n ≥ 2` (so `k` is the largest possible
exponent); `some (n, 2)` for `n ≤ 1`; `none` if `n` is not a perfect power. -/
def expressAsPower (n : AzNat) : Option (AzNat × Nat) :=
  if n.size ≤ 1 then some (n, 2)
  else
    match perfectPowerStep n with
    | none => none
    | some (r, p) => some (expressAsPower.go n.size r p)

/-- **Perfect-power test**: is `n = x ^ k` for some `x` and some `k > 1`?  (`0` and `1`
are.) -/
def isPerfectPower (n : AzNat) : Bool :=
  decide (n.size ≤ 1) || (perfectPowerStep n).isSome

end Azurite.AzNat

-- ── Tests ────────────────────────────────────────────────────────────────────

section Tests

open Azurite Azurite.AzNat

private def N (k : Nat) : AzNat := ofNat k

private def E (k : Nat) : Option (Nat × Nat) :=
  (expressAsPower (N k)).map fun (x, e) => (x.toNat, e)

#guard (List.range 40).filter (fun k => isPerfectPower (N k)) ==
  [0, 1, 4, 8, 9, 16, 25, 27, 32, 36]
#guard E 0 == some (0, 2) && E 1 == some (1, 2) && E 2 == none && E 3 == none
#guard E 4 == some (2, 2) && E 8 == some (2, 3) && E 16 == some (2, 4)
#guard E 64 == some (2, 6) && E 729 == some (3, 6) && E 46656 == some (6, 6)
#guard E (3 ^ 5) == some (3, 5) && E (3 ^ 5 + 2) == none
#guard E (10 ^ 30) == some (10, 30) && E (10 ^ 30 + 1) == none
#guard E (12 ^ 77) == some (12, 77) && E (12 ^ 77 * 5) == none
#guard E ((10 ^ 20 + 39) ^ 7) == some (10 ^ 20 + 39, 7)
#guard E ((10 ^ 20 + 39) ^ 7 + 2) == none
#guard E ((2 ^ 100 + 277) ^ 2) == some (2 ^ 100 + 277, 2)
#guard E ((2 ^ 64 * 3) ^ 15) == some (2 ^ 64 * 3, 15)
#guard E (2 ^ 97) == some (2, 97) && E (2 ^ 97 * 3) == none
#guard E (7 ^ 210) == some (7, 210) && E (15 ^ 64) == some (15, 64)
-- agreement with the root-by-root test on a range
#guard (List.range 3000).all fun k =>
  isPerfectPower (N k) == (k ≤ 1 || (List.range 12).any fun j => isPow (N k) (j + 2))
-- the hints: inverses and roots modulo powers of two
#guard (invModPow2Hint (N 12345) 100 * N 12345).modPow2 100 == N 1
#guard powModPow2 (N 3) 10 7 == N (3 ^ 7 % 1024)
#guard powModPow2 (N 3) 0 7 == N 0 && powModPow2 (N 3) 5 0 == N 1
-- the candidate of `oddRoot?` is right, so the fallback is not taken
#guard (List.range 200).all fun i =>
  let m := N (2 * i + 1)
  let k := 3 + 2 * (i % 4)
  let b := (m.size + k - 1) / k
  let r := (rootHint (invModPow2Hint m b) (invModPow2Hint (N k) b) k b).modPow2 b
  (powModPow2 r b k) == m.modPow2 b

end Tests
