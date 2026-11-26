/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Mathlib.Data.Nat.Sqrt

/-!
# Reduced binary quadratic forms and fundamental discriminants (generator side)

Small-number bookkeeping for the certificate generator (`docs/ecpp_plan.md`, layer 3; nothing
here is proven, the certificates are checked by `ECPP.check`).  A discriminant is `−D` with
`D : ℕ` positive.

* `reducedForms D`: the reduced primitive forms `(A, B, C)` of discriminant `−D` with `B ≥ 0`,
  each with a flag telling whether `(A, −B, C)` is a different reduced form.
* `classNumber D`.
* `isFundamental D`, `primeDiscriminants D` (the factorization of `−D` into prime
  discriminants `−4`, `±8`, `(−1)^((p−1)/2) p`).
* `discriminantTable Dmax hmax`: the fundamental `D ≤ Dmax` with class number at most `hmax`,
  by increasing class number.
* `smoothDiscriminantTable`: the discriminants the search uses, built from small primes.
-/

namespace Azurite.ECPP

/-- A reduced form `(A, B, C)` with `B ≥ 0`; `paired` when `(A, −B, C)` is another reduced
form. -/
structure RedForm where
  a : Nat
  b : Nat
  c : Nat
  paired : Bool
  deriving Repr, DecidableEq

/-- The reduced primitive forms of discriminant `−D` with `B ≥ 0`. -/
def reducedForms (D : Nat) : List RedForm := Id.run do
  let mut out : List RedForm := []
  let bmax := Nat.sqrt (D / 3)
  for b in [0:bmax + 1] do
    if b % 2 == D % 2 then
      let n := (b * b + D) / 4
      if (b * b + D) % 4 == 0 then
        for a in [max b 1:Nat.sqrt n + 1] do
          if n % a == 0 then
            let c := n / a
            if Nat.gcd (Nat.gcd a b) c == 1 then
              out := ⟨a, b, c, decide (0 < b ∧ b < a ∧ a < c)⟩ :: out
  return out.reverse

/-- The class number of the discriminant `−D`. -/
def classNumber (D : Nat) : Nat :=
  (reducedForms D).foldl (fun s f => s + if f.paired then 2 else 1) 0

/-- Is `n` squarefree? (small `n`) -/
def isSquarefreeNat (n : Nat) : Bool :=
  n != 0 && (List.range (Nat.sqrt n + 1)).all fun d => d < 2 || n % (d * d) != 0

/-- Is `−D` a fundamental discriminant? -/
def isFundamental (D : Nat) : Bool :=
  (D % 4 == 3 && isSquarefreeNat D) ||
    (D % 4 == 0 && ((D / 4) % 4 == 1 || (D / 4) % 4 == 2) && isSquarefreeNat (D / 4))

/-- The odd prime factors of `n`, increasing (trial division). -/
def oddPrimeFactors (n : Nat) : List Nat := Id.run do
  let mut m := n
  for _ in [0:Nat.log2 n + 1] do
    if m % 2 != 0 then break
    m := m / 2
  let mut out : List Nat := []
  let mut p := 3
  for _ in [0:Nat.sqrt n + 2] do
    if p * p > m then break
    if m % p == 0 then
      out := p :: out
      for _ in [0:Nat.log2 n + 1] do
        if m % p != 0 then break
        m := m / p
    p := p + 2
  if m > 1 then out := m :: out
  return out.reverse

/-- The prime discriminants whose product is the fundamental discriminant `−D`: the odd ones
`(−1)^((p−1)/2) p` and, for even `D`, one of `−4`, `8`, `−8`. -/
def primeDiscriminants (D : Nat) : List Int :=
  let odd : List Int := (oddPrimeFactors D).map fun (p : Nat) =>
    if p % 4 == 1 then (p : Int) else -(p : Int)
  let prod := odd.foldl (· * ·) 1
  let e := -(D : Int) / prod
  if e == 1 then odd else e :: odd

/-- The fundamental `D ≤ Dmax` with class number at most `hmax`, as `(D, h)`, by increasing
class number and then increasing `D`. -/
def discriminantTable (Dmax hmax : Nat) : List (Nat × Nat) :=
  let all := ((List.range (Dmax + 1)).filter fun D => D ≥ 3 && isFundamental D).map
    fun D => (D, classNumber D)
  let kept := all.filter fun x => x.2 ≤ hmax
  (kept.toArray.qsort fun x y => x.2 < y.2 || (x.2 == y.2 && x.1 < y.1)).toList

/-- The fundamental `D ≤ Dmax` all of whose odd prime factors are at most `pMax`: the
products of distinct odd primes `m`, as `m`, `4m` or `8m`. -/
def smoothFundamental (Dmax pMax : Nat) : List Nat :=
  let ps := (List.range (pMax + 1)).filter fun p => p ≥ 3 && oddPrimeFactors p == [p]
  let ms := ps.foldl (fun acc p =>
    acc ++ acc.filterMap fun m => if m * p ≤ Dmax then some (m * p) else none) [1]
  (ms.flatMap fun m => [m, 4 * m, 8 * m]).filter fun D => D ≥ 3 && D ≤ Dmax && isFundamental D

/-- **The discriminants of the search**, as `(D, h)`: the fundamental `D ≤ Dmax` built from
the primes up to `pMax`, with class number `h` at most `hMax` (`hMaxWeber` for
`D ≡ 7 (mod 8)`, where the class polynomial is cheap) and at most `gMax` classes per genus,
`g = h / 2^(t−1)` for `t` prime discriminants (the degree of the polynomial of which a root
is needed, and the inverse of the chance that `4n = x² + D y²` has a solution once `−D` is a
square).

The order is the order of use, chosen greedily by estimated cost in microseconds: the class
polynomial (`1100 h` for Weber's, `50 h²` for `H_{−D}`, nothing for `h = 1`), its root
(`rootCost · g` for `g > 1`), and `sqrtCost` for every prime discriminant of `D` that no
earlier `D` of the table has used (its square root modulo `n` is computed once).  The first
cost does not depend on `n`, the other two grow like the cube of its length. -/
def smoothDiscriminantTable (Dmax pMax gMax hMax hMaxWeber sqrtCost rootCost : Nat) :
    List (Nat × Nat) := Id.run do
  let rows : Array (Nat × Nat × Nat × List Int) :=
    ((smoothFundamental Dmax pMax).filterMap fun D =>
      let h := classNumber D
      let ds := primeDiscriminants D
      let g := h / 2 ^ (ds.length - 1)
      if g ≤ gMax && h ≤ (if D % 8 == 7 then hMaxWeber else hMax) then
        let poly := if h ≤ 1 then 0 else if D % 8 == 7 then 1100 * h else 50 * h * h
        some (D, h, poly + (if g ≤ 1 then 0 else rootCost * g), ds)
      else none).toArray
  -- the prime discriminants, numbered; the rows that contain each
  let all : Array Int := (rows.foldl (fun acc r =>
    r.2.2.2.foldl (fun acc d => if acc.contains d then acc else d :: acc) acc) []).toArray
  let ids : Array (Array Nat) := rows.map fun r =>
    (r.2.2.2.map fun d => (all.idxOf? d).getD 0).toArray
  let mut rowsOf : Array (Array Nat) := Array.replicate all.size #[]
  for i in [0:rows.size] do
    for k in ids[i]! do
      rowsOf := rowsOf.modify k (·.push i)
  -- the present cost of every row (`none`: already placed)
  let mut cost : Array (Option Nat) := (Array.range rows.size).map fun i =>
    some ((rows[i]!).2.2.1 + sqrtCost * (ids[i]!).size)
  let mut opened : Array Bool := Array.replicate all.size false
  let mut out : Array (Nat × Nat) := Array.mkEmpty rows.size
  for _ in [0:rows.size] do
    let mut best := rows.size
    let mut bestCost := 0
    for i in [0:rows.size] do
      match cost[i]! with
      | none => continue
      | some c =>
        if best == rows.size || c < bestCost ||
            (c == bestCost && (rows[i]!).1 < (rows[best]!).1) then
          best := i
          bestCost := c
    if best == rows.size then break
    out := out.push ((rows[best]!).1, (rows[best]!).2.1)
    cost := cost.set! best none
    for k in ids[best]! do
      if !opened[k]! then
        opened := opened.set! k true
        for i in rowsOf[k]! do
          cost := cost.modify i fun c => c.map (· - sqrtCost)
  return out.toList

#guard oddPrimeFactors 1 = []
#guard oddPrimeFactors 840 = [3, 5, 7]
#guard oddPrimeFactors 1999 = [1999]
#guard oddPrimeFactors 4 = []
#guard smoothFundamental 30 5 = [4, 8, 3, 24, 20, 15]
#guard (smoothDiscriminantTable 60 7 8 8 8 2000 10000).map (·.1) =
  [3, 4, 7, 8, 20, 35, 40, 15, 24, 56]
#guard classNumber 3 = 1
#guard classNumber 23 = 3
#guard classNumber 47 = 5
#guard classNumber 71 = 7
#guard classNumber 163 = 1
#guard classNumber 84 = 4
#guard primeDiscriminants 3 = [-3]
#guard primeDiscriminants 4 = [-4]
#guard primeDiscriminants 15 = [-3, 5]
#guard primeDiscriminants 24 = [8, -3]
#guard primeDiscriminants 40 = [-8, 5]
#guard primeDiscriminants 84 = [-4, -3, -7]
#guard (discriminantTable 30 2).map (·.1) = [3, 4, 7, 8, 11, 19, 15, 20, 24]

end Azurite.ECPP
