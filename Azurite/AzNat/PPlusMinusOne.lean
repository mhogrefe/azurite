/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.Algorithm.PrimeSieve
import Azurite.AzNat.Gcd
import Azurite.AzNat.InvMod
import Azurite.AzNat.Montgomery
import Azurite.AzNat.Parity

/-!
# The `p − 1` and `p + 1` methods

Divisor finders for `AzNat.factor`: J. M. Pollard, *Theorems on factorization and primality
testing*, Proc. Cambridge Philos. Soc. 76 (1974); H. C. Williams, *A `p + 1` method of
factoring*, Math. Comp. 39 (1982); the second stage after P. L. Montgomery, *Speeding the
Pollard and elliptic curve methods of factorization*, Math. Comp. 48 (1987), §4.  They are
searches: nothing is proven, and what they return is checked by the caller.

**`p − 1`.**  If `p − 1` divides `M = ∏_{q ≤ B₁} q^⌊log_q B₁⌋` then `a^M ≡ 1 (mod p)`, and
`gcd(a^M − 1, n)` shows `p`.

**`p + 1`.**  With `V₀ = 2`, `V₁ = P`, `V_{k+1} = P V_k − V_{k−1}` (so `V_k = α^k + α^(−k)` for
`α + α⁻¹ = P`): if `P² − 4` is not a square modulo `p`, `α` lies in the subgroup of order
`p + 1` of the quadratic extension, and `p + 1 ∣ M` gives `V_M ≡ 2 (mod p)`.  When `P² − 4`
is a square the same computation is a `p − 1` method, so a few values of `P` are tried.

**Second stage**, for one more prime `q ≤ B₂` in the order: both methods end with an element
`V₁ = α + α⁻¹` (for `p − 1`, `α = a^M`) and need a `q` with `α^q ≡ 1`.  With `w = 210`,
`V_{kw} − V_j = α^(−kw) (α^(kw+j) − 1)(α^(kw−j) − 1)`, so the product of `V_{kw} − V_j` over
the pairs `(k, j)`, `0 < j < w/2` prime to `w`, for which `kw − j` or `kw + j` is a prime in
`(B₁, B₂]`, is divisible by `p`.  `V_{kw}` advances by `V_{(k+1)w} = V_w V_{kw} − V_{(k−1)w}`:
about one multiplication per prime.

All residues are in Montgomery form (`MontCtx`).
-/

namespace Azurite.AzNat.PM1

/-- `a − b mod n` for `a, b < n`. -/
def subMod (n a b : AzNat) : AzNat := if b ≤ a then a - b else a + n - b

/-- `a ^ e` for a small exponent, in Montgomery form. -/
def powSmall (ctx : MontCtx) (a : AzNat) (e : Nat) : AzNat := Id.run do
  if e = 0 then return ctx.one
  let mut r := a
  let bits := Nat.log2 e
  for i in [0:bits] do
    r := ctx.sqr r
    if e.testBit (bits - 1 - i) then r := ctx.mul r a
  return r

/-- `(V_k, V_{k+1})` of the sequence with `V₁ = P`, in Montgomery form (`two` is the form of
`2`), by the binary ladder; `k ≥ 1`. -/
def lucasPair (ctx : MontCtx) (n two P : AzNat) (k : Nat) : AzNat × AzNat := Id.run do
  let mut x := P
  let mut y := subMod n (ctx.sqr P) two
  let bits := Nat.log2 k
  for i in [0:bits] do
    if k.testBit (bits - 1 - i) then
      x := subMod n (ctx.mul x y) P
      y := subMod n (ctx.sqr y) two
    else
      y := subMod n (ctx.mul x y) P
      x := subMod n (ctx.sqr x) two
  return (x, y)

/-- The largest power of `q` not exceeding `B`. -/
def primePower (q B : Nat) : Nat := Id.run do
  let mut e := q
  for _ in [0:64] do
    if e * q > B then break
    e := e * q
  return e

/-- A divisor strictly between `1` and `n` from a gcd, if it is one. -/
def proper (n g : AzNat) : Option AzNat := if g = 1 || g = n then none else some g

/-- **The second stage** from `V₁` (see the file header): the gcd with `n` of the product of
`V_{kw} − V_j` for the primes in `(B₁, B₂]`. -/
def stage2 (ctx : MontCtx) (n two V₁ : AzNat) (B₁ B₂ : Nat) : AzNat := Id.run do
  let w := 210
  if B₂ ≤ B₁ || B₁ < w then return 1
  -- the primes up to `B₂ + w`, as flags
  let mut isP : ByteArray := ByteArray.emptyWithCapacity (B₂ + w + 1)
  for _ in [0:B₂ + w + 1] do
    isP := isP.push 0
  for p in primesUpTo (B₂ + w) do
    if p > B₁ && p ≤ B₂ then isP := isP.set! p 1
  -- `V_j` for `0 < j < w/2` prime to `w`
  let mut vs : Array (Nat × AzNat) := #[(1, V₁)]
  let mut prev := two
  let mut cur := V₁
  for j in [2:w / 2] do
    let next := subMod n (ctx.mul V₁ cur) prev
    prev := cur
    cur := next
    if Nat.gcd j w = 1 then vs := vs.push (j, cur)
  -- `V_{kw}` from `k₀ = ⌊B₁/w⌋`
  let Vw := (lucasPair ctx n two V₁ w).1
  let k₀ := B₁ / w
  let start := lucasPair ctx n two Vw k₀
  let mut tPrev := if k₀ = 1 then two else (lucasPair ctx n two Vw (k₀ - 1)).1
  let mut t := start.1
  let mut acc := ctx.one
  for k in [k₀:B₂ / w + 2] do
    let c := k * w
    for (j, vj) in vs do
      if isP.get! (c - j) != 0 || (c + j < isP.size && isP.get! (c + j) != 0) then
        acc := ctx.mul acc (subMod n t vj)
    let tNext := subMod n (ctx.mul Vw t) tPrev
    tPrev := t
    t := tNext
  return gcd acc n

/-- **Pollard's `p − 1` method** for an odd `n`, base `a`, bounds `B₁ < B₂`: a divisor
strictly between `1` and `n`, if one is found.  When the first stage ends with `a^M ≡ 1`
modulo all of `n` the base is unsuitable (as `2` is for `2^k − 1`, where it has order `k`),
and the next of `a, a + 1, a + 2` is taken. -/
def pMinusOne (n : AzNat) (a B₁ B₂ : Nat) : Option AzNat := Id.run do
  if n.isEven || n.size ≤ 2 then return none
  let ctx := MontCtx.make n
  let primes := primesUpTo B₁
  for i in [0:3] do
    let mut x := ctx.toMont (ofNat (a + i) % n)
    for q in primes do
      x := powSmall ctx x (primePower q B₁)
    let g := gcd (subMod n x ctx.one) n
    if g = n then continue
    if g ≠ 1 then return some g
    -- `V₁ = x + x⁻¹`
    let xi := invMod (ctx.fromMont x) n
    let s := ctx.toMont xi + x
    let V₁ := if n ≤ s then s - n else s
    let two := ctx.toMont (ofNat 2)
    return proper n (stage2 ctx n two V₁ B₁ B₂)
  return none

/-- **Williams's `p + 1` method** for an odd `n`, starting value `P`, bounds `B₁ < B₂`: a
divisor strictly between `1` and `n`, if one is found. -/
def pPlusOne (n : AzNat) (P B₁ B₂ : Nat) : Option AzNat := Id.run do
  if n.isEven || n.size ≤ 2 then return none
  let ctx := MontCtx.make n
  let two := ctx.toMont (ofNat 2)
  let mut v := ctx.toMont (ofNat P % n)
  for q in primesUpTo B₁ do
    v := (lucasPair ctx n two v (primePower q B₁)).1
  let g := gcd (subMod n v two) n
  if g ≠ 1 then return proper n g
  proper n (stage2 ctx n two v B₁ B₂)

end Azurite.AzNat.PM1

section Tests

open Azurite Azurite.AzNat

private def N (k : Nat) : AzNat := ofNat k

private def big : Nat := 10 ^ 50 + 151

-- `p − 1 = 2 ⋯ 659 · 677 · 683`: first stage
#guard (PM1.pMinusOne (N (249257417243 * big)) 2 1000 20000).map toNat == some 249257417243
-- `p − 1 = ⋯ 727 · 773 · 11783`: second stage; not found without it
#guard (PM1.pMinusOne (N (1091614439518223 * big)) 2 1000 20000).map toNat ==
  some 1091614439518223
#guard PM1.pMinusOne (N (1091614439518223 * big)) 2 1000 1000 == none
#guard PM1.pMinusOne (N (1091614439518223 * big)) 2 1000 11000 == none
-- `2` has order `101` modulo `2^101 − 1`: the base `3` finds `7432339208719`
-- (`p − 1 = 2 · 3 · 101 · 44029 · 278557`, second stage)
#guard (PM1.pMinusOne (N (2 ^ 101 - 1)) 2 50000 300000).map toNat == some 7432339208719
-- `p + 1 = ⋯ 449 · 587 · 821`: first stage of `p + 1` (for a `P` with `P² − 4` a non-residue)
-- (the first `P` for which it is one is 15: for a square `P² − 4` this is a `p − 1` method)
#guard (PM1.pPlusOne (N (150171344761 * big)) 15 1000 20000).map toNat == some 150171344761
#guard PM1.pPlusOne (N (150171344761 * big)) 3 1000 20000 == none
#guard PM1.pMinusOne (N (150171344761 * big)) 2 1000 20000 == none
-- `p + 1 = ⋯ 499 · 839 · 15643`: second stage of `p + 1`
#guard ([3, 5, 7, 11].filterMap fun P =>
  (PM1.pPlusOne (N (1270305450585217 * big)) P 1000 20000).map toNat).contains 1270305450585217
#guard ([3, 5, 7, 11].filterMap fun P =>
  (PM1.pPlusOne (N (1270305450585217 * big)) P 1000 1000).map toNat) == []
-- the Lucas sequence: `V_k(3)` modulo `1009`, against the recurrence
#guard (List.range 40).all fun i =>
  let n := N 1009
  let ctx := MontCtx.make n
  let two := ctx.toMont (N 2)
  let ref := (List.range i).foldl (fun (a, b) _ => (b, (3 * b + 1009 - a) % 1009)) (3, 7)
  ctx.fromMont (PM1.lucasPair ctx n two (ctx.toMont (N 3)) (i + 1)).1 == N ref.1
#guard PM1.primePower 2 1000 == 512 && PM1.primePower 31 1000 == 961 && PM1.primePower 997 1000
  == 997

end Tests
