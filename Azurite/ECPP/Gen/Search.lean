/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.ECPP.Check
import Azurite.ECPP.Gen.ClassPoly
import Azurite.ECPP.Gen.Modular
import Azurite.AzNat.MillerRabin

/-!
# The generator of elliptic curve primality certificates

Unproven (`docs/ecpp_plan.md`, layer 3): whatever it returns is a list of `StepCert`s that
`ECPP.check` accepts or rejects.  One step for a probable prime `n` (Atkin–Morain, in the
arrangement of Morain's fastECPP, *Math. Comp.* 76 (2007), §3):

1. **Square roots of prime discriminants** (Step 1′).  A fundamental discriminant `−D` is a
   product of prime discriminants `q*` (`−4`, `±8`, `±q`); `−D` is a square modulo `n` for the
   `D` all of whose `q*` are squares, and then `√−D = ∏ √q*`.  The roots `√q*` are computed
   once per `n` and shared by all `D` (`SqrtCache`).
2. **Cornacchia**: `4n = x² + D y²`, giving the candidate orders `m = n + 1 ± x` (and the four
   or six orders for `D = 4`, `3`).
3. **Factor** `m = c · q` by trial division, with `c > 1` and `q` a probable prime above the
   bound of the criterion.
4. **Curve**: `y² = x³ + b` (`D = 3`), `y² = x³ + ax` (`D = 4`), otherwise from a root `j`
   of the class polynomial `H_{−D}` modulo `n`: `k = j/(1728 − j)`, `(a, b) = (3k, 2k)`, and
   its quadratic twist.
5. **Point**: `(u, v) = c · P` for a point `P` of the curve; the step is kept when
   `checkStep` accepts it.

`ecppCertificate n` chains the steps down to `baseBits` bits, where `AzNat.isPrime` takes
over, backtracking to the next step when a `q` leads nowhere and enlarging the set of
discriminants and the trial division bound (`GenParams.tiers`) when no step is found.  Not
yet done from fastECPP:
the simultaneous smoothness test of all the `m` and the asymptotically fast subroutines.
-/

namespace Azurite.ECPP

open AzZMod

/-- The parameters of the search. -/
structure GenParams where
  /-- Largest `D`. -/
  dMax : Nat := 2000
  /-- Largest class number. -/
  hMax : Nat := 24
  /-- Trial division bound for the cofactor. -/
  trialBound : Nat := 16384
  /-- Below this many bits the chain stops (`AzNat.isPrime` finishes). -/
  baseBits : Nat := 64
  /-- Points (and twists for `D = 3, 4`) tried per curve family. -/
  tries : Nat := 24
  /-- How many alternative steps are tried at one level when the continuation fails. -/
  backtrack : Nat := 4
  /-- How many times the discriminant set and the trial division bound are enlarged when no
  step is found. -/
  tiers : Nat := 2

/-- The tables that do not depend on `n`. -/
structure GenTables where
  discs : List (Nat × Nat)
  primes : List Nat

/-- Build the tables for the parameters. -/
def GenParams.tables (P : GenParams) : GenTables :=
  ⟨discriminantTable P.dMax P.hMax, smallPrimes P.trialBound⟩

/-- The tables of the successive tiers of the search: the parameters as given, then `tiers`
enlargements (four times the discriminants and the trial division bound, twice the class
number), each built only when the tiers before it found no step. -/
def GenParams.tierTables (P : GenParams) : List (Thunk GenTables) :=
  (List.range (P.tiers + 1)).map fun i =>
    Thunk.mk fun _ =>
      ({ P with dMax := P.dMax * 4 ^ i, hMax := P.hMax * 2 ^ i,
                trialBound := P.trialBound * 4 ^ i } : GenParams).tables

variable {n : AzNat} [NeZero n.toNat]

/-- The square roots of prime discriminants found so far (`none`: not a square). -/
abbrev SqrtCache (n : AzNat) : Type := List (Int × Option (AzZMod n))

/-- Look up or compute `√d` modulo `n`. -/
def SqrtCache.get (c : SqrtCache n) (d : Int) : Option (AzZMod n) × SqrtCache n :=
  match c.lookup d with
  | some r => (r, c)
  | none =>
    let r := sqrtSmall? n d
    (r, (d, r) :: c)

/-- `√−D` modulo `n` as the product of the roots of the prime discriminants of `−D`. -/
def sqrtDisc (c : SqrtCache n) (D : Nat) : Option (AzZMod n) × SqrtCache n := Id.run do
  let mut cache := c
  let mut acc : AzZMod n := 1
  for d in primeDiscriminants D do
    let (r, cache') := cache.get d
    cache := cache'
    match r with
    | none => return (none, cache)
    | some s => acc := acc * s
  return (some acc, cache)

/-- The candidate curve orders from `4n = x² + D y²`. -/
def candidateOrders (n : AzNat) (D : Nat) (x y : AzNat) : List AzNat :=
  let n1 := n + 1
  let base := [n1 + x, n1 - x]
  if D = 4 then
    let y2 := y.shiftLeft 1
    base ++ [n1 + y2, n1 - y2]
  else if D = 3 then
    let y3 := y + y + y
    let s := (x + y3).shiftRight 1
    let d := (if y3 ≤ x then x - y3 else y3 - x).shiftRight 1
    base ++ [n1 + s, n1 - s, n1 + d, n1 - d]
  else base

/-- Is `q` above the bound of the criterion for `n`? -/
def aboveBound (n q : AzNat) : Bool :=
  let s := AzNat.sqrt n
  let t := q - s - 1
  decide (s + 1 < q) && decide (AzNat.ofNat 4 * s < t * t)

/-- A quick probable-prime test: one Miller–Rabin round (a composite that passes only costs
the search a failed step). -/
def probablePrime (q : AzNat) : Bool := AzNat.millerRabinBase q (AzNat.ofNat 2)

/-- Try to finish a step on the curve `y² = x³ + ax + b`: a point `P`, `(u, v) = c · P`, and
the check.  Gives up at the first point that fails the check (the curve has another order). -/
def tryCurve (a b : AzZMod n) (c q : AzNat) (tries : Nat) : Option StepCert := Id.run do
  let mut failures := 0
  for i in [1:tries + 1] do
    if failures ≥ 1 then break
    let x : AzZMod n := ofAzNat n (AzNat.ofNat i)
    let rhs := x * Square.square x + a * x + b
    if rhs = 0 then continue
    if AzNat.jacobi rhs.val n ≠ 1 then continue
    match AzZMod.sqrt? rhs with
    | none => continue
    | some y =>
      match jacMul a x y (c.size + 1) c with
      | none => continue
      | some V =>
        match V.2.2.inv? with
        | none => continue
        | some zi =>
          let zi2 := Square.square zi
          let cert : StepCert := ⟨a.val, b.val, (V.1 * zi2).val, (V.2.1 * (zi2 * zi)).val, q⟩
          if checkStep n cert then return some cert
          failures := failures + 1
  return none

/-- A quadratic non-residue modulo `n` among the small numbers. -/
def smallNonResidue (n : AzNat) : Option Nat :=
  (List.range 200).find? fun g => g ≥ 2 && AzNat.jacobi (AzNat.ofNat g) n == -1

/-- A generator of `(ℤ/n)ˣ` modulo sixth powers, for `n ≡ 1 (mod 3)`: a small number that is
neither a square nor a cube. -/
def smallSexticNonResidue (n : AzNat) [NeZero n.toNat] : Option Nat :=
  let e := (n - 1) / AzNat.ofNat 3
  (List.range 200).find? fun g =>
    g ≥ 2 && AzNat.jacobi (AzNat.ofNat g) n == -1 &&
      decide ((ofAzNat n (AzNat.ofNat g)).powAzNat e ≠ 1)

/-- The powers `g⁰, …, g^(k−1)`. -/
def powersOf (g : AzZMod n) (k : Nat) : List (AzZMod n) :=
  ((List.range k).foldl (fun (acc : List (AzZMod n) × AzZMod n) _ =>
    (acc.2 :: acc.1, acc.2 * g)) ([], 1)).1.reverse

/-- The curves with complex multiplication by the order of discriminant `−D` to try.  For
`D = 3` the six twists `y² = x³ + gᵏ` (`g` neither a square nor a cube), for `D = 4` the four
twists `y² = x³ + gᵏ x` (`g` not a square); when no such small `g` is found, the first
`tries` coefficients. -/
def cmCurves (n : AzNat) [NeZero n.toNat] (D tries : Nat) : List (AzZMod n × AzZMod n) :=
  if D = 3 then
    match smallSexticNonResidue n with
    | some g => (powersOf (ofAzNat n (AzNat.ofNat g)) 6).map fun b => (0, b)
    | none => (List.range tries).map fun i => (0, ofAzNat n (AzNat.ofNat (i + 1)))
  else if D = 4 then
    match smallNonResidue n with
    | some g => (powersOf (ofAzNat n (AzNat.ofNat g)) 4).map fun a => (a, 0)
    | none => (List.range tries).map fun i => (ofAzNat n (AzNat.ofNat (i + 1)), 0)
  else
    match (hilbertClassPoly D).bind fun h => rootOfSplitPoly n (polyOfInts n h) with
    | none => []
    | some j =>
      match (ofAzNat n (AzNat.ofNat 1728) - j).inv? with
      | none => []
      | some i =>
        let k := j * i
        let a := k + k + k
        let b := k + k
        match smallNonResidue n with
        | none => [(a, b)]
        | some g =>
          let g' : AzZMod n := ofAzNat n (AzNat.ofNat g)
          let g2 := g' * g'
          [(a, b), (a * g2, b * (g2 * g'))]

/-- `findStep` with the cache of square roots given and returned. -/
def findStepWith (P : GenParams) (T : GenTables) (n : AzNat) [NeZero n.toNat] (skip : Nat)
    (cache : SqrtCache n) : Option StepCert × SqrtCache n := Id.run do
  let mut cache := cache
  let mut toSkip := skip
  for (D, _) in T.discs do
    let (r, cache') := sqrtDisc cache D
    cache := cache'
    match r with
    | none => continue
    | some r =>
      match cornacchia4 n D r.val with
      | none => continue
      | some (x, y) =>
        let mut curves : Option (List (AzZMod n × AzZMod n)) := none
        for m in candidateOrders n D x y do
          let (q, c) := trialDivide m T.primes
          if c = 1 then continue
          if !aboveBound n q then continue
          if !probablePrime q then continue
          let cs := match curves with
            | some cs => cs
            | none => cmCurves n D P.tries
          curves := some cs
          for (a, b) in cs do
            match tryCurve a b c q P.tries with
            | none => continue
            | some cert =>
              if toSkip = 0 then return (some cert, cache)
              toSkip := toSkip - 1
              break
  return (none, cache)

/-- **One step for `n`**: the `(skip + 1)`-th step the search finds, if any. -/
def findStep (P : GenParams) (T : GenTables) (n : AzNat) (skip : Nat) : Option StepCert :=
  if h : 1 < n.toNat then
    haveI : NeZero n.toNat := ⟨by omega⟩
    (findStepWith P T n skip []).1
  else none

/-- The first tier that gives a `(skip + 1)`-th step; the square roots found are kept from
one tier to the next. -/
def findStepTiers (P : GenParams) (T : List (Thunk GenTables)) (n : AzNat) (skip : Nat) :
    Option StepCert :=
  if h : 1 < n.toNat then
    haveI : NeZero n.toNat := ⟨by omega⟩
    Id.run do
      let mut cache : SqrtCache n := []
      for t in T do
        let (r, cache') := findStepWith P t.get n skip cache
        cache := cache'
        if r.isSome then return r
      return none
  else none

/-- The chain of steps from `n` down to `baseBits` bits. -/
def genChain (P : GenParams) (T : List (Thunk GenTables)) (fuel : Nat) (n : AzNat)
    (skip budget : Nat) :
    Option (List StepCert) :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
    if n.size ≤ P.baseBits then some []
    else
      match findStepTiers P T n skip with
      | none => none
      | some c =>
        match genChain P T fuel c.q 0 P.backtrack with
        | some rest => some (c :: rest)
        | none =>
          match budget with
          | 0 => none
          | budget + 1 => genChain P T (fuel + 1) n (skip + 1) budget
termination_by (fuel, budget)

/-- **A primality certificate for `n`** by elliptic curves, if the search finds one.  The
result is to be given to `ECPP.check`. -/
def ecppCertificate (n : AzNat) (P : GenParams := {}) : Option (List StepCert) :=
  genChain P P.tierTables (n.size + 1) n 0 P.backtrack

/-- **Primality proving by elliptic curves**: search for a certificate and check it.
`true` proves that `n` is prime (`provePrime_sound`); `false` says nothing. -/
def provePrime (n : AzNat) (P : GenParams := {}) : Bool :=
  match ecppCertificate n P with
  | some cert => check n cert
  | none => false

end Azurite.ECPP
