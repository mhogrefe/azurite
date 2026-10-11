/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzNat.RisingFallingFactorial
import Azurite.AzNat.Div

/-!
## Binomial coefficients

`binomial n k = C(n, k) = n! / (k! (n − k)!)`, zero when `k > n`.  After the symmetry
`C(n, k) = C(n, n − k)` reduces `k` to at most `n / 2`, two regimes:

* **Dense** (`n ≤ 64 k`, the factors `n − k + 1, …, n` fill a good part of the range): the
  prime factorization.  By Legendre's formula `v_p(C(n, k)) = v_p(n!) − v_p(k!) − v_p((n−k)!)`
  for every prime `p ≤ n` (equivalently, by Kummer's theorem, the number of carries when
  adding `k` and `n − k` in base `p`); the primes come from the sieve, the exponents from three
  Legendre sums each, and the prime powers are assembled by Horner's rule on the exponent bits
  (`prodPrimePowers`) with the power of two as a shift.  No division is performed.  This is
  Goetgheluck's method; his refinement for the primes above `√n`, whose exponent is `0` or `1`
  and given by one comparison of residues, is not needed separately, since the Legendre sums for
  such primes are one or two divisions anyway.
* **Thin** (`k` small against `n`, or `n` beyond one limb): `C(n, k) = n_(k) / k!` — the
  falling factorial by its balanced product tree, the factorial from its prime factorization,
  and one exact division.  The sieve up to `n` would cost far more than the `k` factors.

The ratio `64` between the regimes (`binomialDenseRatio`) is a placeholder, not tuned.

### References

* P. Goetgheluck, *Computing binomial coefficients*, American Mathematical Monthly 94 (1987),
  360–365, <https://doi.org/10.2307/2323099> — `C(n, k)` from its prime factorization, with the
  exponent of each prime from the base-`p` digits of `n` and `k`.
* *Kummer's theorem*, Wikipedia, <https://en.wikipedia.org/wiki/Kummer%27s_theorem> — the
  exponent of `p` in `C(n, k)` is the number of carries when adding `k` and `n − k` in base `p`.
* *Binomial coefficient*, Wikipedia, §Computing the value of binomial coefficients,
  <https://en.wikipedia.org/wiki/Binomial_coefficient> — the multiplicative formula, the
  symmetry, and the prime-factorization method.
* P. Luschny, *Fast Binomial Function*,
  <http://www.luschny.de/math/factorial/FastBinomialFunction.html> — the survey of the
  prime-based variants.  No library code was consulted.
-/

namespace Azurite.AzNat

/-! ### The dense regime: prime factorization -/

/-- The odd primes up to `n` with their exponents in `C(n, k)`,
`v_p(n!) − v_p(k!) − v_p((n − k)!)`. -/
def binomialExps (n k : Nat) : List (Nat × Nat) :=
  ((primesUpTo n).toList.filter (· ≠ 2)).map fun p =>
    (p, legendreExp p n n - legendreExp p k k - legendreExp p (n - k) (n - k))

/-- `C(n, k)` for `k ≤ n` from its prime factorization. -/
def binomialPrime (n k : Nat) : AzNat :=
  prodPrimePowers (binomialExps n k) (Nat.log 2 n + 1)
    <<< (legendreExp 2 n n - legendreExp 2 k k - legendreExp 2 (n - k) (n - k))

/-! ### The thin regime: a falling factorial and one division -/

/-- `C(n, k) = n_(k) / k!`. -/
def binomialProduct (n : AzNat) (k : Nat) : AzNat := fallingFactorial n k / factorial k

/-- The prime factorization is used when `n ≤ binomialDenseRatio · k` (after the symmetry);
not tuned. -/
def binomialDenseRatio : Nat := 64

/-- **Binomial coefficient** `C(n, k)`, zero when `k > n`. -/
def binomial (n : AzNat) (k : Nat) : AzNat :=
  if n.limbs.size ≤ 1 then
    let m := n.toUInt64.toNat
    if m < k then 0
    else
      let j := min k (m - k)
      if j = 0 then 1
      else if m ≤ binomialDenseRatio * j then binomialPrime m j
      else binomialProduct n j
  else binomialProduct n k

end Azurite.AzNat

/-! ### Tests -/

section Tests

open Azurite Azurite.AzNat

private def N (s : String) : AzNat := (AzNat.parse s).get!
private def B (n k : Nat) : String := AzNat.toString (binomial (ofNat n) k)

#guard B 0 0 == "1"
#guard B 0 1 == "0"
#guard B 1 0 == "1"
#guard B 1 1 == "1"
#guard B 5 0 == "1"
#guard B 5 1 == "5"
#guard B 5 2 == "10"
#guard B 5 3 == "10"
#guard B 5 5 == "1"
#guard B 5 6 == "0"
#guard B 10 3 == "120"
#guard B 10 7 == "120"
#guard B 20 10 == "184756"
#guard B 50 25 == "126410606437752"
#guard B 64 32 == "1832624140942590534"
#guard B 100 50 == "100891344545564193334812497256"
#guard B 100 2 == "4950"
#guard B 1000 3 == "166167000"
#guard B 200 100 == "90548514656103281165404177077484163874504589675413336841320"
-- `C(1000, 500)` has 300 digits
#guard (B 1000 500).length == 300
#guard (B 1000 500).take 20 == "27028824094543656951"
-- a base beyond one limb
#guard AzNat.toString (binomial (N "100000000000000000000") 2)
  == "4999999999999999999950000000000000000000"
#guard AzNat.toString (binomial (N "100000000000000000000") 3)
  == "166666666666666666661666666666666666666700000000000000000000"
#guard AzNat.toString (binomial (N "18446744073709551621") 2)
  == "170141183460469231814697652047577088010"
#guard binomial (N "100000000000000000000") 0 == 1
#guard binomial (N "100000000000000000000") 1 == N "100000000000000000000"
-- the two regimes agree
#guard binomialPrime 1000 500 == binomialProduct (ofNat 1000) 500
#guard binomialPrime 3000 700 == binomialProduct (ofNat 3000) 700
#guard binomialPrime 777 1 == binomialProduct (ofNat 777) 1
#guard binomialPrime 2 1 == binomialProduct (ofNat 2) 1
-- Pascal's triangle
private def pascalRows (n : Nat) : Array (Array AzNat) :=
  (List.range n).foldl (fun rows _ =>
    let prev := rows.back!
    let next := (List.range (prev.size + 1)).toArray.map fun i =>
      (if i = 0 then (0 : AzNat) else prev[i - 1]!)
        + (if i = prev.size then (0 : AzNat) else prev[i]!)
    rows.push next) #[#[1]]
#guard
  let rows := pascalRows 80
  (List.range 80).all fun n => (List.range (n + 3)).all fun k =>
    binomial (ofNat n) k == (rows[n]!)[k]?.getD 0

end Tests
