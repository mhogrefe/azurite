/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.Algorithm.PrimeSieve
import Azurite.AzNat.Mul
import Azurite.AzNat.Square
import Azurite.AzNat.ShiftLeft
import Azurite.AzNat.Conversion
import Azurite.AzNat.ToStringBase
import Mathlib.Data.Nat.Log

/-!
## Factorial

`factorial n = n!` from the prime factorization of `n!`:

`n! = 2^{e₂} · ∏_{p odd prime ≤ n} p^{e_p}`, `e_p = Σ_{i ≥ 1} ⌊n / p^i⌋` (Legendre's formula).

The odd part is assembled from the binary digits of the exponents.  With `P_j` the product of the
odd primes whose exponent has bit `j` set and `B` a bit length bounding every exponent,
`∏ p^{e_p} = (((P_{B−1})² · P_{B−2})² ⋯)² · P_0` — Horner's rule on the binary digits, one
squaring and one multiplication per bit (`hornerPow`).  Each `P_j` is a product of small
numbers of similar size, computed by pairing adjacent factors until one remains (`prodList`, a
balanced product tree).  The factor `2^{e₂}` is a shift.  Since the primes come from a sieve and
the exponents from `O(log n)` divisions each, the cost is dominated by the big multiplications:
`O(M(n log n))` for the Horner squarings (the sizes halve going up the bits) plus the product
trees, against `O(M(n log n) log n)` for a plain product tree over `1, …, n`.

The method is Borwein's (grouping prime factors by the binary digits of their exponents),
refined by Schönhage et al. (multiply before exponentiating); see the references below.  No
library code was consulted.

### References

* P. B. Borwein, *On the complexity of calculating factorials*, Journal of Algorithms 6 (1985),
  376–380, <https://doi.org/10.1016/0196-6774(85)90006-9> — `n!` from its prime factorization
  with the exponents' binary digits, `O(M(n log n) log log n)` given the prime table.
* A. Schönhage, A. F. W. Grotefeld and E. Vetter, *Fast Algorithms: A Multitape Turing Machine
  Implementation*, BI Wissenschaftsverlag (1994), §3.3 — the nested products-then-powers form
  reaching `O(M(n log n))`.
* *Factorial*, Wikipedia, §Computation, <https://en.wikipedia.org/wiki/Factorial> — the
  complexity comparison (`O(n log³ n)` for binary splitting against `O(n log² n)` for the
  prime-factorization method with fast multiplication).
* P. Luschny, *Fast Factorial Functions*, <http://www.luschny.de/math/factorial/description.html>
  — the survey and benchmark of the prime-based variants (Borwein, Schönhage, prime swing).
-/

namespace Azurite.AzNat

/-! ### Legendre's exponent -/

/-- `Σ_{i ≥ 1} ⌊m / p^i⌋` by repeated division, stopping at the first zero quotient (`fuel`
bounds the number of divisions; `m` itself is enough for `p ≥ 2`). -/
def legendreExp (p : Nat) : Nat → Nat → Nat
  | 0, _ => 0
  | fuel + 1, m =>
    let q := m / p
    if q = 0 then 0 else q + legendreExp p fuel q

/-! ### Balanced products -/

/-- Multiply adjacent pairs. -/
def mulPairs : List AzNat → List AzNat
  | x :: y :: rest => (x * y) :: mulPairs rest
  | l => l

/-- The product of a list by `fuel` rounds of pairing (a balanced tree); a left fold finishes if
the fuel runs out. -/
def prodTree : Nat → List AzNat → AzNat
  | 0, l => l.foldl (· * ·) 1
  | fuel + 1, l =>
    match l with
    | [] => 1
    | [x] => x
    | _ => prodTree fuel (mulPairs l)

/-- The product of a list of `AzNat`s by a balanced tree. -/
def prodList (l : List AzNat) : AzNat := prodTree l.length l

/-! ### Horner's rule on the exponent bits -/

/-- The primes (given with their exponents) whose exponent has bit `j` set. -/
def primesWithBit (pes : List (Nat × Nat)) (j : Nat) : List AzNat :=
  pes.filterMap fun pe => if pe.2.testBit j then some (ofNat pe.1) else none

/-- `acc ↦ acc² · P j` for `j = B − 1, …, 0`. -/
def hornerPow (P : Nat → AzNat) : Nat → AzNat → AzNat
  | 0, acc => acc
  | j + 1, acc => hornerPow P j (square acc * P j)

/-! ### Factorial -/

/-- The odd primes up to `n` with their exponents in `n!`. -/
def oddPrimeExps (n : Nat) : List (Nat × Nat) :=
  ((primesUpTo n).toList.filter (· ≠ 2)).map fun p => (p, legendreExp p n n)

/-- The odd part of `n!`: `∏_{p odd prime ≤ n} p^{e_p}` by Horner's rule on the exponent bits. -/
def factorialOdd (n : Nat) : AzNat :=
  let pes := oddPrimeExps n
  hornerPow (fun j => prodList (primesWithBit pes j)) (Nat.log 2 n + 1) 1

/-- **Factorial** `n!`, from its prime factorization (Borwein / Schönhage). -/
def factorial (n : Nat) : AzNat := factorialOdd n <<< legendreExp 2 n n

end Azurite.AzNat

/-! ### Tests -/

section Tests

open Azurite Azurite.AzNat

private def F (n : Nat) : String := AzNat.toString (factorial n)

#guard F 0 == "1"
#guard F 1 == "1"
#guard F 2 == "2"
#guard F 3 == "6"
#guard F 4 == "24"
#guard F 5 == "120"
#guard F 6 == "720"
#guard F 7 == "5040"
#guard F 10 == "3628800"
#guard F 20 == "2432902008176640000"
#guard F 25 == "15511210043330985984000000"
#guard F 30 == "265252859812191058636308480000000"
#guard F 50 == "30414093201713378043612608166064768844377641568960512000000000000"
#guard F 100 == "9332621544394415268169923885626670049071596826438162146859296389521759999322991"
  ++ "5608941463976156518286253697920827223758251185210916864000000000000000000000000"
-- `1000!` has 2568 digits and ends in 249 zeros; its leading digits
#guard (F 1000).length == 2568
#guard (F 1000).take 20 == "40238726007709377354"
#guard (F 1000).drop (2568 - 30) == "000000000000000000000000000000"
-- agreement with the plain product `1 · 2 ⋯ n`
private def naive (n : Nat) : AzNat := (List.range n).foldl (fun acc i => acc * ofNat (i + 1)) 1
#guard (List.range 400).all fun n => factorial n == naive n
#guard factorial 2500 == naive 2500
-- the pieces
#guard legendreExp 2 10 10 == 8                    -- `v₂(10!) = 5 + 2 + 1`
#guard legendreExp 5 100 100 == 24                 -- `v₅(100!) = 20 + 4`
#guard legendreExp 7 6 6 == 0
#guard AzNat.toString (prodList [ofNat 2, ofNat 3, ofNat 5, ofNat 7, ofNat 11]) == "2310"
#guard AzNat.toString (prodList []) == "1"

end Tests
