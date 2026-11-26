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
   bound of the criterion.  The orders are collected in batches (`GenParams.batch`) and each
   batch is divided at once by all the primes below the bound (`smoothParts`: one remainder
   of their product modulo the product of the batch), which makes a bound of `2^20`
   affordable at 300 digits; the bound grows with `n` (`GenTables.primorialFor`).  Within a
   batch the candidates are tried by increasing `q`, the largest reduction first.
4. **Curve**: `y² = x³ + b` (`D = 3`), `y² = x³ + ax` (`D = 4`), otherwise from a root `j`
   of the class polynomial `H_{−D}` modulo `n`: `k = j/(1728 − j)`, `(a, b) = (3k, 2k)`, and
   its quadratic twist.
5. **Point**: `(u, v) = c · P` for a point `P` of the curve; the step is kept when
   `checkStep` accepts it.

`ecppCertificate n` chains the steps down to `baseBits` bits, where `AzNat.isPrimeAprcl` takes
over, backtracking to the next step when a `q` leads nowhere and enlarging the set of
discriminants and the trial division bound (`GenParams.tiers`) when no step is found.  The
search for a step gives up at a sign that `n` is composite (a small number of Jacobi symbol
`1` without a square root, or `GenParams.maxFailures` probable-prime cofactors for which no
curve gives a step), so that a composite that passes Miller–Rabin costs little.

**The discriminants** (`smoothDiscriminantTable`) are built from small primes, so that few
square roots serve many `D`, and are tried in an order of estimated cost (class polynomial,
its root, new square roots).  The tables of the default parameters are built once and kept
(`defaultTierTables`; `smallTierTables` for `n` of at most 256 bits).  Not yet done from
fastECPP: the asymptotically fast subroutines.
-/

namespace Azurite.ECPP

open AzZMod

/-- The parameters of the search. -/
structure GenParams where
  /-- Largest `D`. -/
  dMax : Nat := 20000
  /-- Largest odd prime factor of `D`. -/
  pMax : Nat := 1000
  /-- Largest number of classes per genus. -/
  gMax : Nat := 8
  /-- Largest class number. -/
  hMax : Nat := 24
  /-- Largest class number for `D ≡ 7 (mod 8)` (Weber class polynomials). -/
  hMaxWeber : Nat := 64
  /-- The estimated cost of a square root modulo `n`, in microseconds, for the order of the
  discriminants (`smoothDiscriminantTable`); the default is for 1000 bits. -/
  sqrtCost : Nat := 2000
  /-- The estimated cost per degree of a root of a class polynomial modulo `n`. -/
  rootCost : Nat := 10000
  /-- Largest trial division bound for the cofactor (rounded down to a power of two); the
  bound used for an `n` of `b` bits is about `b^2.7 / 64` (`GenTables.primorialFor`), at
  most this. -/
  trialBound : Nat := 16777216
  /-- Added to the exponent of the trial division bound used for `n`. -/
  trialExtra : Nat := 0
  /-- Candidate orders divided together. -/
  batch : Nat := 16
  /-- Below this many bits the chain stops (`AzNat.isPrimeAprcl` finishes). -/
  baseBits : Nat := 64
  /-- Points (and twists for `D = 3, 4`) tried per curve family. -/
  tries : Nat := 24
  /-- How many alternative steps are tried at one level when the continuation fails. -/
  backtrack : Nat := 4
  /-- How many times the discriminant set and the trial division bound are enlarged when no
  step is found. -/
  tiers : Nat := 2
  /-- The search for a step for `n` is given up (`n` is taken to be composite) after this
  many probable-prime cofactors for which no curve gave a step.  For a prime `n` every such
  cofactor gives a step, up to accidents. -/
  maxFailures : Nat := 3
  deriving DecidableEq

/-- The tables that do not depend on `n`: the discriminants, and the products of the primes
below `2^j` for each `j` (computed when first used), of which those up to `2^levelCap` are
used. -/
structure GenTables where
  discs : List (Nat × Nat)
  primorials : Array (Thunk AzNat)
  levelCap : Nat
  levelExtra : Nat := 0

/-- The product of the primes for the trial division of the candidate orders of `n`: those
below `2^j`, `j = ⌊2.7 log₂(bits of n)⌋ − 6 + levelExtra` between 10 and the cap of the table
(`2^16`, `2^19`, `2^20` at 100, 200, 300 digits).  Measured 2026-11-25 on ten primes each:
the best of `2^16, 2^18, 2^20` was `2^16` at 100 digits, `2^18` at 200, `2^20` at 300 (and
`2^22` worse there). -/
def GenTables.primorialFor (T : GenTables) (n : AzNat) : AzNat :=
  let j := min T.levelCap (max 10 (Nat.log2 (n.size ^ 27) / 10 - 6 + T.levelExtra))
  match T.primorials[j]? with
  | some t => t.get
  | none => 1

/-- The products of the primes below `2^j`, `j ≤ top`, each computed when first used, from
the one before it and the primes between `2^(j−1)` and `2^j`. -/
def primorialLadder (top : Nat) : Array (Thunk AzNat) :=
  (List.range (top + 1)).foldl (fun acc j =>
    acc.push <| Thunk.mk fun _ =>
      match acc.back? with
      | none => 1
      | some t =>
        t.get * AzNat.product
          (((AzNat.primesUpTo (2 ^ j)).toList.filter (2 ^ (j - 1) < ·)).map AzNat.ofNat)) #[]

/-- The products of primes of the process: computed when first used, and then kept. -/
def sharedPrimorials : Array (Thunk AzNat) := primorialLadder 32

/-- The ladder up to `2^top`: that of the process when it reaches that far. -/
def primorialsUpTo (top : Nat) : Array (Thunk AzNat) :=
  if top < sharedPrimorials.size then sharedPrimorials else primorialLadder top

/-- Build the tables for the parameters. -/
def GenParams.tables (P : GenParams) : GenTables :=
  let top := Nat.log2 P.trialBound
  ⟨smoothDiscriminantTable P.dMax P.pMax P.gMax P.hMax P.hMaxWeber P.sqrtCost P.rootCost,
    primorialsUpTo top, top, P.trialExtra⟩

/-- The tables of the successive tiers of the search: the parameters as given, then `tiers`
enlargements (four times the trial division bound, twice the bounds of the discriminants, of
their primes and of the class numbers), each built only when the tiers before it
found no step.  The products of primes
are shared by the tiers (and by all the searches of the process, `sharedPrimorials`). -/
def GenParams.tierTables (P : GenParams) : List (Thunk GenTables) :=
  let top := Nat.log2 P.trialBound
  let ladder := primorialsUpTo (top + 2 * P.tiers)
  (List.range (P.tiers + 1)).map fun i =>
    Thunk.mk fun _ =>
      ⟨smoothDiscriminantTable (P.dMax * 2 ^ i) (P.pMax * 2 ^ i) (P.gMax * 2 ^ i)
        (P.hMax * 2 ^ i) (P.hMaxWeber * 2 ^ i) P.sqrtCost P.rootCost, ladder, top + 2 * i,
        P.trialExtra⟩

/-- The tables of the default parameters: built when first used, and then kept. -/
def defaultTierTables : List (Thunk GenTables) := ({} : GenParams).tierTables

/-- The default parameters for an `n` of at most 256 bits: a set of discriminants that is
built in a few milliseconds. -/
def smallParams : GenParams := { dMax := 2000, pMax := 2000, sqrtCost := 5, rootCost := 30 }

/-- The tables of `smallParams`: built when first used, and then kept. -/
def smallTierTables : List (Thunk GenTables) := smallParams.tierTables

variable {n : AzNat} [NeZero n.toNat]

/-- The square roots of prime discriminants found so far (`none`: not a square), and whether
the search has met a sign that `n` is composite: a `d` of Jacobi symbol `1` without a square
root, or `maxFailures` cofactors without a step. -/
structure SqrtCache (n : AzNat) : Type where
  roots : List (Int × Option (AzZMod n)) := []
  composite : Bool := false

/-- Look up or compute `√d` modulo `n`. -/
def SqrtCache.get (c : SqrtCache n) (d : Int) : Option (AzZMod n) × SqrtCache n :=
  match c.roots.lookup d with
  | some r => (r, c)
  | none =>
    let v := resOfInt n d
    if AzNat.jacobi v.val n = 1 then
      let r := AzZMod.sqrt? v
      (r, ⟨(d, r) :: c.roots, c.composite || r.isNone⟩)
    else (none, { c with roots := (d, none) :: c.roots })

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

/-- **A genus factor modulo `n`**: the square roots of the prime discriminants modulo `n`
turn `2^(−t) ∑_S A_S ∏_{i ∈ S} √dᵢ` into residues.  `none` if a square root or the inverse
of `2^t` is missing. -/
def genusPolyMod (n : AzNat) [NeZero n.toNat] (G : GenusPoly) :
    Option (AzPolynomial (AzZMod n)) := do
  let roots ← G.ds.mapM (sqrtSmall? n)
  let inv ← (ofAzNat n (AzNat.ofNat (2 ^ G.ds.length))).inv?
  let len := (G.terms.headD ([], [])).2.length
  let coeffs := (Array.range len).map fun k =>
    inv * G.terms.foldl (fun acc term =>
      let s := (roots.zip term.1).foldl (fun s y => if y.2 then s * y.1 else s) (1 : AzZMod n)
      acc + ofAzInt n (term.2.getD k 0) * s) 0
  pure (AzPolynomial.normalize coeffs)

/-- A root modulo `n` of a class polynomial given by its factor over the genus field (if it
has one) and by itself: through the factor, and through the polynomial when that fails. -/
def rootVia (n : AzNat) [NeZero n.toNat] (G : Option GenusPoly)
    (H : Unit → Option (List AzInt)) : Option (AzZMod n) :=
  let viaGenus : Option (AzZMod n) := do
    let G ← G
    let g ← genusPolyMod n G
    if g.natDegree = 0 then none
    rootOfSplitPoly n g
  viaGenus.orElse fun _ => (H ()).bind fun h => rootOfSplitPoly n (polyOfInts n h)

/-- A root of `H_{−D}` modulo `n` through `H_{−D}` (and its factor over the genus field). -/
def hilbertRoot (n : AzNat) [NeZero n.toNat] (D : Nat) : Option (AzZMod n) :=
  let C := classPolys D
  rootVia n C.genusHilbert.get fun _ => C.hilbert.get

/-- A root of `H_{−D}` modulo `n` through the Weber class polynomial, `D ≡ 7 (mod 8)`: from
a root `u` of it, `(x − 16)³ / x` with `x = u^24`, or `x = u^8` when `3 ∣ D`. -/
def weberRoot (n : AzNat) [NeZero n.toNat] (D : Nat) : Option (AzZMod n) := do
  let k ← weberKind D
  let C := classPolys D
  let u ← rootVia n C.genusWeber.get fun _ => C.weber.get
  let u2 := Square.square u
  let u8 := Square.square (Square.square u2)
  let x := if k = 3 then u8 else u8 * Square.square u8
  let xi ← x.inv?
  let t := x - ofAzNat n (AzNat.ofNat 16)
  pure (t * Square.square t * xi)

/-- **A root of `H_{−D}` modulo `n`** (`n` a probable prime that splits in the class field):
through Weber's class invariants for `D ≡ 7 (mod 8)`, and through `H_{−D}` otherwise or when
that fails; in both cases through the factor over the genus field when `−D` is not a prime
discriminant.  The polynomials are those of the process (`classPolys`): each is computed
once. -/
def classPolyRoot (n : AzNat) [NeZero n.toNat] (D : Nat) : Option (AzZMod n) :=
  (weberRoot n D).orElse fun _ => hilbertRoot n D

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
    match classPolyRoot n D with
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

/-- **A batch of candidate orders** `(D, m)`: trial division of all of them at once by the
primes of `prim`, then, by increasing cofactor `q`, the probable-prime test, the curves of
`D` and the point.  Returns the `(toSkip + 1)`-th step found, or what is left of `toSkip`,
and the number of probable-prime cofactors for which no curve gave a step. -/
def processBatch (P : GenParams) (prim : AzNat) (n : AzNat) [NeZero n.toNat]
    (batch : Array (Nat × AzNat)) (toSkip : Nat) : Option StepCert × Nat × Nat := Id.run do
  let parts := smoothParts prim (batch.map (·.2))
  let mut cands : Array (Nat × AzNat × AzNat) := #[]
  for i in [0:batch.size] do
    let (q, c) := parts[i]!
    if c = 1 then continue
    if !aboveBound n q then continue
    cands := cands.push (batch[i]!.1, q, c)
  let sorted := cands.qsort fun x y => decide (x.2.1 < y.2.1)
  let mut toSkip := toSkip
  let mut failures := 0
  let mut curves : List (Nat × List (AzZMod n × AzZMod n)) := []
  for (D, q, c) in sorted do
    if failures ≥ P.maxFailures then break
    if !probablePrime q then continue
    let cs ← match curves.lookup D with
      | some cs => pure cs
      | none => pure (cmCurves n D P.tries)
    curves := (D, cs) :: curves
    let mut found := false
    for (a, b) in cs do
      match tryCurve a b c q P.tries with
      | none => continue
      | some cert =>
        if toSkip = 0 then return (some cert, 0, failures)
        toSkip := toSkip - 1
        found := true
        break
    if !found then failures := failures + 1
  return (none, toSkip, failures)

/-- `findStep` with the cache of square roots given and returned. -/
def findStepWith (P : GenParams) (T : GenTables) (n : AzNat) [NeZero n.toNat] (skip : Nat)
    (cache : SqrtCache n) : Option StepCert × SqrtCache n := Id.run do
  let prim := T.primorialFor n
  let mut cache := cache
  let mut toSkip := skip
  let mut failures := 0
  let mut pending : Array (Nat × AzNat) := #[]
  for (D, _) in T.discs do
    let (r, cache') := sqrtDisc cache D
    cache := cache'
    if cache.composite then return (none, cache)
    match r with
    | none => continue
    | some r =>
      match cornacchia4 n D r.val with
      | none => continue
      | some (x, y) =>
        for m in candidateOrders n D x y do
          pending := pending.push (D, m)
        if pending.size ≥ P.batch then
          let (res, left, failed) := processBatch P prim n pending toSkip
          if res.isSome then return (res, cache)
          failures := failures + failed
          if failures ≥ P.maxFailures then return (none, { cache with composite := true })
          toSkip := left
          pending := #[]
  let (res, _, failed) := processBatch P prim n pending toSkip
  if res.isNone && failures + failed ≥ P.maxFailures then
    return (none, { cache with composite := true })
  return (res, cache)

/-- **One step for `n`**: the `(skip + 1)`-th step the search finds, if any. -/
def findStep (P : GenParams) (T : GenTables) (n : AzNat) (skip : Nat) : Option StepCert :=
  if h : 1 < n.toNat then
    haveI : NeZero n.toNat := ⟨by omega⟩
    (findStepWith P T n skip {}).1
  else none

/-- The first tier that gives a `(skip + 1)`-th step; the square roots found are kept from
one tier to the next.  Stops at a sign that `n` is composite (`SqrtCache.composite`). -/
def findStepTiers (P : GenParams) (T : List (Thunk GenTables)) (n : AzNat) (skip : Nat) :
    Option StepCert :=
  if h : 1 < n.toNat then
    haveI : NeZero n.toNat := ⟨by omega⟩
    Id.run do
      let mut cache : SqrtCache n := {}
      for t in T do
        let (r, cache') := findStepWith P t.get n skip cache
        cache := cache'
        if r.isSome then return r
        if cache.composite then return none
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
  let T :=
    if P = {} then (if n.size ≤ 256 then smallTierTables else defaultTierTables)
    else P.tierTables
  genChain P T (n.size + 1) n 0 P.backtrack

/-- **Primality proving by elliptic curves**: search for a certificate and check it.
`true` proves that `n` is prime (`provePrime_sound`); `false` says nothing. -/
def provePrime (n : AzNat) (P : GenParams := {}) : Bool :=
  match ecppCertificate n P with
  | some cert => check n cert
  | none => false

end Azurite.ECPP
