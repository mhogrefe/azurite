/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.Algorithm.PrimeSieve
import Azurite.AzNat.Gcd.Binary
import Azurite.AzNat.Montgomery
import Azurite.UInt64.MulWithCarry

/-!
# Factoring a number below `2^63` in machine words

`factorWord n` proposes the prime factors of `n < 2^63` with multiplicity, computed entirely
in `UInt64` arithmetic: trial division by the primes up to 1024, a Miller–Rabin test in
Montgomery form to recognise primes, and Pollard's rho method with Brent's cycle finding
(`Azurite/AzNat/PollardRho.lean` has the description) to split composites.

Nothing here is proven and nothing needs to be: `AzNat.factor` accepts the proposal only
after checking that the product is `n` and that every factor passes the proven `isPrime`
(`Azurite/AzNat/Factor.lean`, `checkFactors`).  `none` means no proposal (`n ≥ 2^63`, or the
rho method did not split some cofactor: a power of a prime above 1024 higher than the
second, typically), and the general path takes over.

Montgomery arithmetic modulo an odd `n < 2^63` with `R = 2^64`: `mulMont a b = a b R⁻¹ mod n`
from the two halves of `a b` and one more high product; since `n < 2^63` the intermediate
sum stays below `2^64`.
-/

namespace Azurite.AzNat.Word

/-- The high word of `a b`. -/
@[inline] def mulHi (a b : UInt64) : UInt64 := (UInt64.mulWithCarry a b 0).1

/-- `a b R⁻¹ mod n` for `a, b < n < 2^63`, `n` odd, `ninv = −n⁻¹ mod 2^64`. -/
@[inline] def mulMont (n ninv a b : UInt64) : UInt64 :=
  let p := UInt64.mulWithCarry a b 0
  let m := p.2 * ninv
  let t := p.1 + mulHi m n + (if p.2 = 0 then 0 else 1)
  if n ≤ t then t - n else t

/-- `a + b mod n` for `a, b < n < 2^63`. -/
@[inline] def addMod (n a b : UInt64) : UInt64 :=
  let s := a + b
  if n ≤ s then s - n else s

/-- `R mod n`: the Montgomery form of `1`. -/
def montOne (n : UInt64) : UInt64 := (0 - n) % n

/-- `R² mod n` (by 64 doublings of `R mod n`): the factor that converts into Montgomery
form. -/
def montR2 (n : UInt64) : UInt64 := Id.run do
  let mut x := montOne n
  for _ in [0:64] do
    x := addMod n x x
  return x

/-- `a ^ e` in Montgomery form (`a` and the result in Montgomery form, `one = R mod n`). -/
def powMont (n ninv one a e : UInt64) : UInt64 := Id.run do
  let mut result := one
  let mut base := a
  let mut k := e
  for _ in [0:64] do
    if k = 0 then break
    if k &&& 1 = 1 then result := mulMont n ninv result base
    base := mulMont n ninv base base
    k := k >>> 1
  return result

/-- One Miller–Rabin round for an odd `n > 2` to the base `a` (`n − 1 = 2^s d`, `d` odd). -/
def millerRabinRound (n ninv one r2 d : UInt64) (s : Nat) (a : UInt64) : Bool := Id.run do
  let am := mulMont n ninv (a % n) r2
  if am = 0 then return true
  let mut x := powMont n ninv one am d
  let minusOne := n - one
  if x = one || x = minusOne then return true
  for _ in [1:s] do
    x := mulMont n ninv x x
    if x = minusOne then return true
    if x = one then return false
  return false

/-- **Probable primality of `n < 2^63`** by Miller–Rabin to the first twelve prime bases
(which leaves no composite below `2^64`, a fact not used by any proof). -/
def isProbablePrime (n : UInt64) : Bool :=
  if n < 2 then false
  else if n < 4 then true
  else if n % 2 = 0 then false
  else Id.run do
    let ninv := montNegInv n
    let one := montOne n
    let r2 := montR2 n
    let mut d := n - 1
    let mut s := 0
    for _ in [0:64] do
      if d % 2 = 1 then break
      d := d >>> 1
      s := s + 1
    for a in [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37] do
      if !millerRabinRound n ninv one r2 d s a then return false
    return true

/-- `|a − b|`. -/
@[inline] def absDiff (a b : UInt64) : UInt64 := if b ≤ a then a - b else b - a

/-- **Brent's rho algorithm in machine words** (see `rhoBrent`): a divisor of the odd
composite `n < 2^63` strictly between `1` and `n`, with the constant `c` (below `n`), `batch`
differences per gcd and at most about `budget` terms. -/
def rhoBrent (n c : UInt64) (batch budget : Nat) : Option UInt64 := Id.run do
  let ninv := montNegInv n
  let next (y : UInt64) : UInt64 := addMod n (mulMont n ninv y y) c
  let mut y : UInt64 := 2 % n
  let mut q : UInt64 := 1
  let mut r := 1
  let mut used := 0
  for _ in [0:64] do
    if used ≥ budget then return none
    let x := y
    for _ in [0:r] do
      y := next y
    used := used + r
    let mut k := 0
    let mut g : UInt64 := 1
    let mut ys := y
    for _ in [0:r] do
      if k ≥ r || g ≠ 1 then break
      ys := y
      let lim := min batch (r - k)
      for _ in [0:lim] do
        y := next y
        q := mulMont n ninv q (absDiff x y)
      g := gcdUInt64 q n
      k := k + lim
      used := used + lim
    if g ≠ 1 then
      if g = n then
        g := 1
        for _ in [0:batch + 1] do
          if g ≠ 1 then break
          ys := next ys
          g := gcdUInt64 (absDiff x ys) n
      return if g = n || g = 1 then none else some g
    r := 2 * r
  return none

/-- The integer square root of `n < 2^63`, from the floating-point one. -/
def sqrtWord (n : UInt64) : UInt64 := Id.run do
  let mut s := (Float.sqrt n.toFloat).toUInt64
  for _ in [0:4] do
    if s * s > n then s := s - 1
  for _ in [0:4] do
    if (s + 1) * (s + 1) ≤ n then s := s + 1
  return s

/-- The primes up to 1024, as machine words. -/
def smallPrimes : Thunk (Array UInt64) :=
  Thunk.mk fun _ => (primesUpTo 1024).map Nat.toUInt64

/-- The prime factors of a cofactor `c > 1` without prime factor up to 1024, added to
`acc`; `none` if some composite is not split. -/
def splitWord : Nat → UInt64 → List UInt64 → Option (List UInt64)
  | 0, _, _ => none
  | fuel + 1, c, acc =>
    if c < 1048576 then some (c :: acc)
    else if isProbablePrime c then some (c :: acc)
    else
      let s := sqrtWord c
      if s * s = c then
        (splitWord fuel s acc).bind fun acc' => splitWord fuel s acc'
      else
        match [1, 2, 3, 5, 7, 11].findSome? fun k => rhoBrent c k 64 4194304 with
        | none => none
        | some d => (splitWord fuel d acc).bind fun acc' => splitWord fuel (c / d) acc'

/-- **A proposal for the prime factors of `n`** with multiplicity (in no particular order),
for `2 ≤ n < 2^63`; `none` if there is none. -/
def factorWord (n : UInt64) : Option (List UInt64) := Id.run do
  if n < 2 || n ≥ 9223372036854775808 then return none
  let mut c := n
  let mut acc : List UInt64 := []
  for p in smallPrimes.get do
    if p * p > c then break
    for _ in [0:64] do
      if c % p ≠ 0 then break
      c := c / p
      acc := p :: acc
  if c = 1 then return some acc
  splitWord 64 c acc

end Azurite.AzNat.Word

section Tests

open Azurite.AzNat.Word

private def W (n : UInt64) : Option (List Nat) :=
  (factorWord n).map fun l => (l.map UInt64.toNat).mergeSort

#guard W 0 == none && W 1 == none && W 2 == some [2] && W 3 == some [3]
#guard W 360 == some [2, 2, 2, 3, 3, 5] && W 97 == some [97]
#guard W 1048573 == some [1048573] && W 1022117 == some [1009, 1013]
#guard W 600851475143 == some [71, 839, 1471, 6857]
#guard W 4294967297 == some [641, 6700417]
#guard W (1000003 * 1000033) == some [1000003, 1000033]
#guard W (1000003 * 1000003) == some [1000003, 1000003]
#guard W (2147483647 * 4294967291) == some [2147483647, 4294967291]
#guard W 9223372036854775783 == some [9223372036854775783]   -- the largest prime below 2^63
#guard W 9223372036854775807 == some [7, 7, 73, 127, 337, 92737, 649657]   -- 2^63 − 1
#guard W (3037000493 * 3037000493) == some [3037000493, 3037000493]
#guard W 9223372036854775808 == none
-- every number of a range multiplies back into probable primes
#guard (List.range 3000).all fun k =>
  match factorWord (k + 2).toUInt64 with
  | some l => (l.foldl (· * ·) 1).toNat == k + 2 && l.all isProbablePrime
  | none => false
#guard isProbablePrime 2305843009213693951 && !isProbablePrime 2305843009213693953
#guard !isProbablePrime 3215031751   -- a strong pseudoprime to the bases 2, 3, 5, 7
#guard sqrtWord 9223372036854775807 == 3037000499 && sqrtWord 15 == 3 && sqrtWord 16 == 4

end Tests
