/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzNat.Conversion
import Azurite.AzNat.Div
import Azurite.AzNat.FactorWord
import Azurite.AzNat.IsPrimeWord
import Azurite.AzNat.Size
import Azurite.AzNat.Sub
import Azurite.AzZMod.Instances
import Mathlib.Data.List.Dedup

/-!
# Primality of a number of one machine word by the factorization of `n − 1`

Lucas's test: `n` is prime if some `a` has `a^(n−1) ≡ 1` and `a^((n−1)/q) ≢ 1 (mod n)` for
every prime `q` dividing `n − 1`.  For `n < 2^63` the factorization of `n − 1` is at hand
(`Word.factorWord`), so primes of 33 to 63 bits are proven in a few modular powers instead
of by the general tests.

* `lucasHint n` (machine words, not verified): the prime factors of `n − 1` with
  multiplicity and a witness `a`, found by trying small primes.
* `lucasCheck n a l` (on `AzZMod n`, the arithmetic that is proven): `l` multiplies to
  `n − 1`, and `a` passes the conditions for every `q` in `l`.
* `lucasCertified fuel n`: the check, with every `q` of `l` certified in turn — by
  `isPrimeWord` up to 32 bits, by this test above.  `true` proves that `n` is prime
  (`lucasCertified_prime`, `Azurite/AzNat/Equiv/IsPrimeLucas.lean`); `false` says nothing.
-/

namespace Azurite.AzNat

/-- The product of a list. -/
def listProd (l : List AzNat) : AzNat := l.foldl (· * ·) 1

/-- **A proposal for Lucas's test** for an odd `n` with `4 < n < 2^63`: a witness `a` and the
prime factors of `n − 1` with multiplicity.  Not verified: `lucasCheck` checks it. -/
def lucasHint (n : UInt64) : Option (UInt64 × List UInt64) := Id.run do
  if n ≥ 9223372036854775808 || n < 5 || n % 2 = 0 then return none
  match Word.factorWord ((n - 1) / 2) with
  | none => return none
  | some l =>
    let fs := 2 :: l
    let qs := fs.eraseDups
    let ninv := montNegInv n
    let one := Word.montOne n
    let r2 := Word.montR2 n
    for a in [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71] do
      let am := Word.mulMont n ninv a r2
      if qs.all fun q => Word.powMont n ninv one am ((n - 1) / q) != one then
        return some (a, fs)
    return none

/-- **The conditions of Lucas's test**: `l` has product `n − 1`, `a^(n−1) = 1` in `ℤ/n`, and
`a^((n−1)/q) ≠ 1` for every `q` of `l`. -/
def lucasCheck (n : AzNat) [NeZero n.toNat] (a : AzNat) (l : List AzNat) : Bool :=
  let x := AzZMod.ofAzNat n a
  decide (listProd l = n - 1) && decide (x.powAzNat (n - 1) = 1)
    && l.dedup.all fun q => decide (x.powAzNat ((n - 1) / q) ≠ 1)

/-- **Primality by Lucas's test**, for `n` of at most 63 bits: `true` proves that `n` is
prime; `false` means only that no certificate was produced. -/
def lucasCertified : Nat → AzNat → Bool
  | 0, _ => false
  | fuel + 1, n =>
    if n.size ≤ 32 then isPrimeWord n.toUInt64 == some true
    else if n.size ≤ 63 then
      if h : n.toNat = 0 then false
      else
        haveI : NeZero n.toNat := ⟨h⟩
        match lucasHint n.toUInt64 with
        | none => false
        | some (a, l) =>
          let l' := l.map UInt64.toAzNat
          lucasCheck n a.toAzNat l' && l'.dedup.all (lucasCertified fuel)
    else false

end Azurite.AzNat

section Tests

open Azurite Azurite.AzNat

private def N (k : Nat) : AzNat := ofNat k

private def chk (n a : AzNat) (l : List AzNat) : Bool :=
  if h : n.toNat = 0 then false
  else
    haveI : NeZero n.toNat := ⟨h⟩
    lucasCheck n a l

#guard lucasCertified 40 (N 97) && lucasCertified 40 (N 4294967311)
#guard lucasCertified 40 (N (2 ^ 61 - 1)) && lucasCertified 40 (N 9223372036854775783)
#guard lucasCertified 40 (N 67280421310721) && lucasCertified 40 (N 1000000007)
-- a chain: 2 q + 1 with q = 2 r + 1, all above 2^32
#guard lucasCertified 40 (N 8589935801) && lucasCertified 40 (N 17179871603)
#guard lucasCertified 40 (N 34359743207) && !lucasCertified 1 (N 34359743207)
-- composites, and numbers out of range, are not certified
#guard !lucasCertified 40 (N (4294967311 * 4294967357 / 4294967311 * 3))
#guard !lucasCertified 40 (N 4294967297) && !lucasCertified 40 (N (2 ^ 61 + 1))
#guard !lucasCertified 40 (N (2 ^ 64 + 13)) && !lucasCertified 0 (N 97)
#guard (lucasHint 1000000007).map (·.2.map UInt64.toNat) == some [2, 500000003]
#guard lucasHint 1000000008 == none && lucasHint 4 == none
-- the check itself: 5 is a primitive root modulo 1000000007, 4 is a square
#guard chk (N 1000000007) (N 5) [N 2, N 500000003]
#guard !chk (N 1000000007) (N 4) [N 2, N 500000003]
#guard !chk (N 1000000007) (N 5) [N 2, N 2, N 250000001]

end Tests
