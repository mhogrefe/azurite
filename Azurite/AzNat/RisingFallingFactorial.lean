/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzNat.Factorial
import Azurite.AzNat.Conversion
import Azurite.AzNat.Compare
import Azurite.AzNat.Sub

/-!
## Rising and falling factorials

`risingFactorial x k = x (x + 1) ⋯ (x + k − 1)` (Mathlib's `Nat.ascFactorial`) and
`fallingFactorial x k = x (x − 1) ⋯ (x − k + 1)` (`Nat.descFactorial`, zero when `k > x`).

Two regimes.  When the base is small — `x ≤ k`, so the factors fill most of `[1, x + k)` — the
product is the quotient of factorials `(x + k − 1)! / (x − 1)!`, assembled from its prime
factorization like the factorial itself (`factorialQuotient`: `v_p = v_p((x+k−1)!) − v_p((x−1)!)`
by Legendre's formula over the primes up to `x + k − 1`, Horner's rule on the exponent bits,
the power of two as a shift; no division is performed).  Otherwise the `k` factors are a thin
slice of a long range, the sieve would be wasted, and the factors themselves are multiplied by a
balanced product tree (`product`).  The falling factorial is the rising factorial of
`x + 1 − k` (with the truncated subtraction giving base `0`, hence product `0`, when `k > x`).
-/

namespace Azurite.AzNat

/-! ### Quotients of factorials -/

/-- The odd primes up to `a` with their exponents in `a! / b!`, `v_p(a!) − v_p(b!)`. -/
def factorialQuotientExps (a b : Nat) : List (Nat × Nat) :=
  ((primesUpTo a).toList.filter (· ≠ 2)).map fun p => (p, legendreExp p a a - legendreExp p b b)

/-- `a! / b!` for `b ≤ a`, from its prime factorization. -/
def factorialQuotient (a b : Nat) : AzNat :=
  prodPrimePowers (factorialQuotientExps a b) (Nat.log 2 a + 1)
    <<< (legendreExp 2 a a - legendreExp 2 b b)

/-! ### Rising and falling factorials -/

/-- **Rising factorial** `x (x + 1) ⋯ (x + k − 1)`. -/
def risingFactorial (x : AzNat) (k : Nat) : AzNat :=
  if k = 0 then 1
  else if x = 0 then 0
  else if x.limbs.size ≤ 1 ∧ x.toUInt64.toNat ≤ k then
    let n := x.toUInt64.toNat
    factorialQuotient (n + k - 1) (n - 1)
  else product ((List.range k).map fun i => x + ofNat i)

/-- **Falling factorial** `x (x − 1) ⋯ (x − k + 1)`, zero when `k > x`. -/
def fallingFactorial (x : AzNat) (k : Nat) : AzNat := risingFactorial (x + 1 - ofNat k) k

end Azurite.AzNat

/-! ### Tests -/

section Tests

open Azurite Azurite.AzNat

private def N (s : String) : AzNat := (AzNat.parse s).get!
private def R (x k : Nat) : String := AzNat.toString (risingFactorial (ofNat x) k)
private def Fa (x k : Nat) : String := AzNat.toString (fallingFactorial (ofNat x) k)

#guard R 0 0 == "1"
#guard R 0 5 == "0"
#guard R 1 5 == "120"
#guard R 5 0 == "1"
#guard R 5 1 == "5"
#guard R 5 3 == "210"                       -- 5 · 6 · 7
#guard R 3 4 == "360"                       -- 3 · 4 · 5 · 6, the quotient regime
#guard R 10 2 == "110"
#guard R 2 10 == "39916800"                 -- 11!
#guard Fa 0 0 == "1"
#guard Fa 0 1 == "0"
#guard Fa 5 0 == "1"
#guard Fa 5 1 == "5"
#guard Fa 5 3 == "60"                       -- 5 · 4 · 3
#guard Fa 5 5 == "120"
#guard Fa 5 6 == "0"
#guard Fa 10 3 == "720"
#guard Fa 100 2 == "9900"
-- a large base with few factors
#guard AzNat.toString (risingFactorial (N "1000000000000000000000") 3)
  == "1000000000000000000003000000000000000000002000000000000000000000"
#guard AzNat.toString (fallingFactorial (N "1000000000000000000000") 3)
  == "999999999999999999997000000000000000000002000000000000000000000"
-- agreement with the plain products, across both regimes
private def naiveRising (x k : Nat) : AzNat :=
  (List.range k).foldl (fun acc i => acc * ofNat (x + i)) 1
private def naiveFalling (x k : Nat) : AzNat :=
  (List.range k).foldl (fun acc i => acc * ofNat (x - i)) 1
#guard (List.range 40).all fun x => (List.range 45).all fun k =>
  risingFactorial (ofNat x) k == naiveRising x k
#guard (List.range 40).all fun x => (List.range 45).all fun k =>
  fallingFactorial (ofNat x) k == naiveFalling x k
#guard risingFactorial (ofNat 300) 700 == naiveRising 300 700
#guard fallingFactorial (ofNat 1000) 600 == naiveFalling 1000 600
#guard (List.range 30).all fun n => fallingFactorial (ofNat n) n == factorial n
#guard (List.range 30).all fun n => risingFactorial 1 n == factorial n

end Tests
