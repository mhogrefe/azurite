/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.Algorithm.PrimeSieve
import Azurite.AzNat.Compare
import Azurite.AzNat.Conversion
import Azurite.AzNat.Div
import Azurite.AzNat.FactorWord
import Azurite.AzNat.IsPrime
import Azurite.AzNat.PerfectPower
import Azurite.AzNat.PollardRho

/-!
# Integer factorization

`factor n` is the prime factorization of `n`: the list of pairs `(p, e)` with `p` prime and
`e > 0` its exponent, by increasing `p`; `[]` for `n ≤ 1`.  Proven
(`Azurite/AzNat/Equiv/Factor.lean`): the list written out with multiplicities is Mathlib's
`Nat.primeFactorsList n.toNat`, so the `p` are the primes dividing `n`, strictly increasing,
and `e = n.toNat.factorization p.toNat`.

The structure:

* `trialDivide`: the primes up to `trialBound` are divided out;
* `splitFactors`: what is left is prime (`isPrime`), or a perfect power (`expressAsPower`: the
  factors of the root, repeated), or is split by a divisor `d` from `findDivisor` into `d`
  and `n / d`, each treated the same way;
* `trialFactor`: complete trial division, for when `findDivisor` has nothing to offer.

Before any of this, a number below `2^63` (the input, or any cofactor) is given to
`Word.factorWord` (`Azurite/AzNat/FactorWord.lean`), which works in machine words and is not
verified: its proposal is accepted if it multiplies back to the number and consists of
primes (`checkFactors`, by the proven `isPrime`), and otherwise the steps above run
(`hinted`).

Only `findDivisor` and `factorHint` are a matter of speed, and they are not part of what is
proven: whatever it
returns is used only if it is a divisor strictly between `1` and `n` (three comparisons), and
the proofs hold for any function in its place.  Primality is decided by the proven `isPrime`.
For now `findDivisor` is Pollard's rho method with Brent's cycle finding
(`Azurite/AzNat/PollardRho.lean`), which finds a prime factor `p` in about `3 √p`
multiplications modulo `n`.
-/

namespace Azurite.AzNat

/-- **Complete trial division from `d`**, for `n ≥ 2` with no prime factor below `d`: the prime
factors of `n` with multiplicity, in increasing order. -/
def trialFactor.go (n d : AzNat) : List AzNat :=
  if h1 : n < d * d then [n]
  else if h2 : d < ofNat 2 then [n]
  else if n % d = 0 then
    if n / d = 1 then [d] else d :: trialFactor.go (n / d) d
  else trialFactor.go n (d + 1)
termination_by n.toNat + (n.toNat - d.toNat)
decreasing_by
  all_goals
    rw [lt_iff_toNat_lt, toNat_mul] at h1
    rw [lt_iff_toNat_lt, toNat_ofNat] at h2
    push Not at h1 h2
    have hdn : d.toNat < n.toNat := by nlinarith
  · have hq : (n / d).toNat < n.toNat := by
      rw [toNat_div]
      exact Nat.div_lt_self (by omega) (by omega)
    omega
  · rw [toNat_add]
    have : (1 : AzNat).toNat = 1 := by decide
    omega

/-- **Factorization by trial division alone**: the prime factors of `n ≥ 2` with multiplicity.
Slow (about `√p` divisions for the second largest prime factor `p`); the fallback of
`splitFactors`. -/
def trialFactor (n : AzNat) : List AzNat := trialFactor.go n (ofNat 2)

/-- Divide `n` by `p` as often as it goes (at most `fuel` times): what is left, and `acc` with
one `p` for every division. -/
def pullOut (p : AzNat) : Nat → AzNat → List AzNat → AzNat × List AzNat
  | 0, n, acc => (n, acc)
  | fuel + 1, n, acc => if n % p = 0 then pullOut p fuel (n / p) (p :: acc) else (n, acc)

/-- Divide out the primes of the list, stopping when nothing is left: the cofactor and the
primes found (with multiplicity, in no particular order). -/
def trialDivideBy : List Nat → AzNat → List AzNat → AzNat × List AzNat
  | [], n, acc => (n, acc)
  | p :: ps, n, acc =>
    if n = 1 then (n, acc)
    else
      let r := pullOut (ofNat p) n.size n acc
      trialDivideBy ps r.1 r.2

/-- The primes up to this bound are divided out first. -/
def trialBound : Nat := 4096

/-- **Trial division by the primes up to `trialBound`**: the cofactor and the primes found. -/
def trialDivide (n : AzNat) : AzNat × List AzNat :=
  trialDivideBy (primesUpTo trialBound).toList n []

/-- The terms of the rho sequence computed for one constant before the next is tried.  Until
there are methods for larger factors there is nothing better to hand over to, so this is
generous. -/
def rhoBudget : Nat := 1 <<< 36

/-- **A divisor of a composite `n`** that has no small prime factor and is not a perfect power,
if one is found: Pollard's rho method.  Not verified, and need not be: `splitFactors` checks
what it returns. -/
def findDivisor (n : AzNat) : Option AzNat := pollardRho n 16 rhoBudget

/-- The product of a list. -/
def listProd (l : List AzNat) : AzNat := l.foldl (· * ·) 1

/-- **Is `l` a list of primes with product `n`?**  Primality by the proven `isPrime`. -/
def checkFactors (n : AzNat) (l : List AzNat) : Bool :=
  decide (listProd l = n) && l.all isPrime

/-- **A proposal for the prime factors of `n`** (`[]` when there is none): for `n < 2^63`,
from the machine-word factorization.  Not verified: `hinted` checks it. -/
def factorHint (n : AzNat) : List AzNat :=
  if n.size ≤ 63 then
    match Word.factorWord n.toUInt64 with
    | some l => l.map UInt64.toAzNat
    | none => []
  else []

/-- The proposal of `factorHint` if it passes `checkFactors`, and `slow ()` otherwise. -/
def hinted (n : AzNat) (slow : Unit → List AzNat) : List AzNat :=
  let h := factorHint n
  if checkFactors n h then h else slow ()

/-- **The prime factors of `n ≥ 2`** with multiplicity: the checked proposal of `factorHint`
if there is one; otherwise `n` itself if it is prime, the factors
of the root if it is a perfect power, those of `d` and `n / d` for a divisor `d` given by
`find`, and trial division if there is none (or when `fuel` runs out, which the bit length of
`n` does not). -/
def splitFactors (find : AzNat → Option AzNat) : Nat → AzNat → List AzNat
  | 0, n => trialFactor n
  | fuel + 1, n =>
    hinted n fun _ =>
      if isPrime n then [n]
      else
        match expressAsPower n with
        | some (x, k) => (splitFactors find fuel x).flatMap (List.replicate k)
        | none =>
          match find n with
          | some d =>
            if ofNat 1 < d ∧ d < n ∧ n % d = 0 then
              splitFactors find fuel d ++ splitFactors find fuel (n / d)
            else trialFactor n
          | none => trialFactor n

/-- **The prime factors of `n`** with multiplicity, in no particular order (`[]` for
`n ≤ 1`). -/
def primeFactorList (n : AzNat) : List AzNat :=
  if n.size ≤ 1 then []
  else
    hinted n fun _ =>
      let r := trialDivide n
      if r.1 = 1 then r.2 else r.2 ++ splitFactors findDivisor r.1.size r.1

/-- Runs of equal elements, each with its length. -/
def groupRuns : List AzNat → List (AzNat × Nat)
  | [] => []
  | p :: ps =>
    match groupRuns ps with
    | [] => [(p, 1)]
    | (q, e) :: rest => if p = q then (q, e + 1) :: rest else (p, 1) :: (q, e) :: rest

/-- **Prime factorization**: the pairs `(p, e)`, `p` prime and `e > 0`, with `n = ∏ p ^ e`, by
increasing `p`; `[]` for `n ≤ 1`. -/
def factor (n : AzNat) : List (AzNat × Nat) :=
  groupRuns ((primeFactorList n).mergeSort (· ≤ ·))

end Azurite.AzNat

-- ── Tests ────────────────────────────────────────────────────────────────────

section Tests

open Azurite Azurite.AzNat

private def F (k : Nat) : List (Nat × Nat) := (factor (ofNat k)).map fun (p, e) => (p.toNat, e)

#guard F 0 == [] && F 1 == [] && F 2 == [(2, 1)] && F 3 == [(3, 1)] && F 4 == [(2, 2)]
#guard F 12 == [(2, 2), (3, 1)] && F 360 == [(2, 3), (3, 2), (5, 1)]
#guard F 97 == [(97, 1)] && F 1024 == [(2, 10)] && F (2 ^ 64) == [(2, 64)]
#guard F 600851475143 == [(71, 1), (839, 1), (1471, 1), (6857, 1)]
#guard F (2 ^ 32 + 1) == [(641, 1), (6700417, 1)]
-- a prime above the trial bound, and powers of one
#guard F 1000003 == [(1000003, 1)] && F (1000003 ^ 3) == [(1000003, 3)]
#guard F (2 ^ 5 * 3 ^ 4 * 1000003 ^ 2) == [(2, 5), (3, 4), (1000003, 2)]
-- cofactors with two primes above the trial bound: complete trial division
#guard F (10007 * 10009) == [(10007, 1), (10009, 1)]
#guard F (7 * 10007 ^ 2 * 10009) == [(7, 1), (10007, 2), (10009, 1)]
#guard F (2 ^ 61 - 1) == [(2 ^ 61 - 1, 1)]
#guard F (10 ^ 30) == [(2, 30), (5, 30)]
#guard F (2 ^ 127 - 1) == [(2 ^ 127 - 1, 1)]
#guard F (Nat.factorial 30) ==
  [(2, 26), (3, 14), (5, 7), (7, 4), (11, 2), (13, 2), (17, 1), (19, 1), (23, 1), (29, 1)]
-- every number of a range multiplies back, with increasing primes
#guard (List.range 2000).all fun k =>
  let f := F (k + 1)
  f.foldl (fun acc pe => acc * pe.1 ^ pe.2) 1 == k + 1 &&
    (f.zip f.tail).all fun (a, b) => a.1 < b.1
-- cofactors that Pollard's rho method splits
#guard F ((2 ^ 31 - 1) * (2 ^ 61 - 1)) == [(2 ^ 31 - 1, 1), (2 ^ 61 - 1, 1)]
#guard F (1000003 * 1000033 * 1000037) == [(1000003, 1), (1000033, 1), (1000037, 1)]
#guard F (1000003 ^ 2 * 1000033) == [(1000003, 2), (1000033, 1)]
#guard F (2 ^ 64 + 1) == [(274177, 1), (67280421310721, 1)]
#guard F (10 ^ 30 + 1) ==
  [(61, 1), (101, 1), (3541, 1), (9901, 1), (27961, 1), (4188901, 1), (39526741, 1)]
-- above 2^63: the general path, with cofactors that go back to machine words
#guard F (2 ^ 64 - 1) == [(3, 1), (5, 1), (17, 1), (257, 1), (641, 1), (65537, 1), (6700417, 1)]
#guard F (2 ^ 63) == [(2, 63)] && F (2 ^ 63 - 1) ==
  [(7, 2), (73, 1), (127, 1), (337, 1), (92737, 1), (649657, 1)]
#guard F ((2 ^ 61 - 1) * 1000003 * 1000033) == [(1000003, 1), (1000033, 1), (2 ^ 61 - 1, 1)]
-- the check of a proposal
#guard checkFactors (ofNat 15) [ofNat 3, ofNat 5] && !checkFactors (ofNat 15) [ofNat 15]
#guard !checkFactors (ofNat 16) [ofNat 3, ofNat 5] && !checkFactors (ofNat 15) []
#guard checkFactors (ofNat 1) [] && !checkFactors (ofNat 12) [ofNat 2, ofNat 6]
-- the pieces
#guard (trialFactor (ofNat 360)).map toNat == [2, 2, 2, 3, 3, 5]
#guard (splitFactors (fun _ => some (ofNat 10007)) 40 (ofNat (10007 * 10009))).map toNat
  == [10007, 10009]
#guard (splitFactors (fun _ => some (ofNat 5)) 40 (ofNat (10007 * 10009))).map toNat
  == [10007, 10009]
#guard groupRuns [ofNat 2, ofNat 2, ofNat 3, ofNat 7, ofNat 7] ==
  [(ofNat 2, 2), (ofNat 3, 1), (ofNat 7, 2)]

end Tests
