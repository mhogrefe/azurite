/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzNat.Montgomery
import Azurite.ECPP.Gen.Search
import Azurite.AzNat.IsPrime
import Azurite.Benchmark.Common

open Azurite Azurite.ECPP Azurite.Benchmark

/-!
# Elliptic curve primality proving: timing

`benchmark ecpp <limit> "digits:D"` takes the first `limit` probable primes above `10^D`
and, for each, times the certificate generator (`ecppCertificate`), the checker (`check`)
and, unless `noaprcl:1` is given, `AzNat.isPrimeAprcl` (Miller–Rabin and APR-CL) on the same
number.  The search parameters can be set with `dmax`, `hmax`, `trial`, `extra`, `batch`, `base`.
`"digits:D,parts:1"` times the pieces of the first step instead, `"…,trace:1"` follows the
chain, `"…,profile:1"` follows it with a clock on every stage of the search.  Times in milliseconds.
-/

namespace Azurite.Benchmark.Ecpp

def ms (ns : UInt64) : String :=
  let m := ns / 1000000
  let f := (ns / 10000) % 100
  s!"{m}.{if f < 10 then "0" else ""}{f}"

def timeOnce {α : Type} (f : Unit → α) : IO (α × UInt64) := timeNsIter 1 f

/-- The first `k` probable primes from `m` on. -/
def nextProbablePrimes (m : AzNat) (k : Nat) : List AzNat := Id.run do
  let mut out : List AzNat := []
  let mut c := if m.isOdd then m else m + 1
  for _ in [0:100000] do
    if out.length ≥ k then break
    if probablePrime c then out := c :: out
    c := c + AzNat.ofNat 2
  return out.reverse

def params (cfg : Std.HashMap String String) : GenParams :=
  let d : GenParams := {}
  { dMax := configGetNat cfg "dmax" d.dMax, hMax := configGetNat cfg "hmax" d.hMax,
    pMax := configGetNat cfg "pmax" d.pMax, gMax := configGetNat cfg "gmax" d.gMax,
    hMaxWeber := configGetNat cfg "hweber" d.hMaxWeber,
    sqrtCost := configGetNat cfg "sqrtcost" d.sqrtCost,
    rootCost := configGetNat cfg "rootcost" d.rootCost,
    trialBound := configGetNat cfg "trial" d.trialBound,
    batch := configGetNat cfg "batch" d.batch,
    trialExtra := configGetNat cfg "extra" d.trialExtra,
    baseBits := configGetNat cfg "base" d.baseBits,
    tiers := configGetNat cfg "tiers" d.tiers }

/-- Time the pieces of one step for `n`. -/
def parts (P : GenParams) (n : AzNat) : IO Unit := do
  if h : 1 < n.toNat then
    have : NeZero n.toNat := ⟨by omega⟩
    let (tabs, tT) ← timeOnce fun _ => P.tables
    IO.println s!"   tables: {tabs.discs.length} discriminants  {ms tT}ms"
    let (prim, tP) ← timeOnce fun _ => tabs.primorialFor n
    IO.println s!"   product of the primes for this n: {prim.size} bits  {ms tP}ms"
    let (r, tS) ← timeOnce fun _ => sqrtSmall? n (-3)
    IO.println s!"   one square root (−3): {ms tS}ms ({r.isSome})"
    let (j, tJ) ← timeOnce fun _ => AzNat.jacobi (n / AzNat.ofNat 3) n
    IO.println s!"   one Jacobi symbol: {ms tJ}ms ({j})"
    let ms16 : Array AzNat := (Array.range P.batch).map fun i => n + AzNat.ofNat (2 * i + 1)
    let (q, tD) ← timeOnce fun _ => (smoothParts prim ms16).foldl (fun s x => s + x.1.size) 0
    IO.println s!"   trial division of a batch of {P.batch}: {ms tD}ms ({q} bits left)"
    let (pp, tM) ← timeOnce fun _ => probablePrime n
    IO.println s!"   probablePrime: {ms tM}ms ({pp})"
    for D in [23, 47, 71, 191, 311, 431] do
      let (hp, tH) ← timeOnce fun _ => (hilbertClassPoly D).map (·.length)
      IO.println s!"   H_(-{D}): {ms tH}ms (length {hp})"
    let (step, tF) ← timeOnce fun _ => findStep P tabs n 0
    IO.println s!"   findStep: {ms tF}ms"
    match step with
    | none => IO.println "   no step"
    | some c =>
      let (ok, tC) ← timeOnce fun _ => checkStep n c
      IO.println s!"   checkStep: {ms tC}ms ({ok}), q has {c.q.size} bits"

/-- Count, for one `n`: discriminants with a square root, Cornacchia solutions, orders with a
nontrivial smooth part, and those with a probable prime cofactor above the bound. -/
def stats (T : GenTables) (n : AzNat) : Nat × Nat × Nat × Nat :=
  if h : 1 < n.toNat then
    haveI : NeZero n.toNat := ⟨by omega⟩
    Id.run do
      let mut cache : SqrtCache n := {}
      let mut s := (0, 0, 0, 0)
      let prim := T.primorialFor n
      for (D, _) in T.discs do
        let (r, cache') := sqrtDisc cache D
        cache := cache'
        match r with
        | none => continue
        | some r =>
          s := (s.1 + 1, s.2)
          match cornacchia4 n D r.val with
          | none => continue
          | some (x, y) =>
            s := (s.1, s.2.1 + 1, s.2.2)
            for (q, c) in smoothParts prim (candidateOrders n D x y).toArray do
              if c = 1 then continue
              if !aboveBound n q then continue
              s := (s.1, s.2.1, s.2.2.1 + 1, s.2.2.2)
              if probablePrime q then s := (s.1, s.2.1, s.2.2.1, s.2.2.2 + 1)
      return s
  else (0, 0, 0, 0)

/-- Follow the first step at every level, printing the sizes, and the counts where it stops. -/
def trace (P : GenParams) (n : AzNat) : IO Unit := do
  let tabs := P.tables
  let tiers := P.tierTables
  let mut m := n
  for _ in [0:n.size] do
    if m.size ≤ P.baseBits then break
    let (st, t) ← timeOnce fun _ => findStepTiers P tiers m 0
    match st with
    | some c =>
      IO.println s!"   {m.size} bits -> {c.q.size} bits  {ms t}ms"
      m := c.q
    | none =>
      IO.println s!"   {m.size} bits: no step  {ms t}ms  (roots, cornacchia, smooth, prime) = {stats tabs m}"
      break

/-- `processBatch` with a clock on every stage (see `findStepTimed`). -/
def processBatchTimed (P : GenParams) (prim : AzNat) (n : AzNat) [NeZero n.toNat]
    (batch : Array (Nat × AzNat)) (acc : Array UInt64) (cnt : Array Nat) :
    IO (Option (StepCert × Nat) × Array UInt64 × Array Nat) := do
  let mut acc := acc
  let mut cnt := cnt
  let (parts, t) ← timeOnce fun _ => smoothParts prim (batch.map (·.2))
  acc := acc.modify 2 (· + t)
  cnt := cnt.modify 2 (· + batch.size)
  let mut cands : Array (Nat × AzNat × AzNat) := #[]
  for i in [0:batch.size] do
    let (q, c) := parts[i]!
    if c = 1 then continue
    let (ab, t) ← timeOnce fun _ => aboveBound n q
    acc := acc.modify 3 (· + t)
    cnt := cnt.modify 3 (· + 1)
    if !ab then continue
    cands := cands.push (batch[i]!.1, q, c)
  let sorted := cands.qsort fun x y => decide (x.2.1 < y.2.1)
  let mut curves : List (Nat × List (AzZMod n × AzZMod n)) := []
  for (D, q, c) in sorted do
    let (pp, t) ← timeOnce fun _ => probablePrime q
    acc := acc.modify 4 (· + t)
    cnt := cnt.modify 4 (· + 1)
    if !pp then continue
    let cs ← match curves.lookup D with
      | some cs => pure cs
      | none => do
        let mut tH : UInt64 := 0
        if D ≠ 3 ∧ D ≠ 4 then
          let (_, t) ← timeOnce fun _ =>
            if (weberKind D).isSome then
              match genusWeberPoly D with
              | some G => G.terms.length
              | none => ((weberClassPoly D).map List.length).getD 0
            else
              match genusClassPoly D with
              | some G => G.terms.length
              | none => ((hilbertClassPoly D).map List.length).getD 0
          tH := t
          acc := acc.modify 5 (· + t)
          cnt := cnt.modify 5 (· + 1)
        let (cs, t) ← timeOnce fun _ => cmCurves n D P.tries
        acc := acc.modify 6 (· + (if tH < t then t - tH else 0))
        cnt := cnt.modify 6 (· + 1)
        pure cs
    curves := (D, cs) :: curves
    for (a, b) in cs do
      let (res, t) ← timeOnce fun _ => tryCurve a b c q P.tries
      acc := acc.modify 7 (· + t)
      cnt := cnt.modify 7 (· + 1)
      match res with
      | none => continue
      | some cert => return (some (cert, D), acc, cnt)
  return (none, acc, cnt)

/-- `findStep` with a clock on every stage.  The times (nanoseconds) and counts are added to
`acc`: square roots, Cornacchia, trial division (per candidate order), the size test,
probable primes, class polynomials, their roots, curves. -/
def findStepTimed (P : GenParams) (T : GenTables) (n : AzNat) [NeZero n.toNat]
    (cache : SqrtCache n) (acc : Array UInt64) (cnt : Array Nat) :
    IO (Option (StepCert × Nat) × SqrtCache n × Array UInt64 × Array Nat) := do
  if 1 < n.toNat then
    let mut acc := acc
    let mut cnt := cnt
    let mut cache := cache
    let (prim, t) ← timeOnce fun _ => T.primorialFor n
    acc := acc.modify 2 (· + t)
    let mut pending : Array (Nat × AzNat) := #[]
    for (D, _) in T.discs do
      let ((r, cache'), t) ← timeOnce fun _ => sqrtDisc cache D
      cache := cache'
      acc := acc.modify 0 (· + t)
      cnt := cnt.modify 0 (· + 1)
      match r with
      | none => continue
      | some r =>
        let (xy, t) ← timeOnce fun _ => cornacchia4 n D r.val
        acc := acc.modify 1 (· + t)
        cnt := cnt.modify 1 (· + 1)
        match xy with
        | none => continue
        | some (x, y) =>
          for m in candidateOrders n D x y do
            pending := pending.push (D, m)
          if pending.size ≥ P.batch then
            let (res, a, c) ← processBatchTimed P prim n pending acc cnt
            acc := a
            cnt := c
            if res.isSome then return (res, cache, acc, cnt)
            pending := #[]
    let (res, a, c) ← processBatchTimed P prim n pending acc cnt
    return (res, cache, a, c)
  else return (none, cache, acc, cnt)

def stageNames : List String :=
  ["sqrt", "cornacchia", "trial", "bound", "prp", "classpoly", "root", "curve"]

def showStages (acc : Array UInt64) (cnt : Array Nat) : String :=
  " ".intercalate <| (List.range 8).map fun i =>
    s!"{stageNames[i]!}={ms acc[i]!}/{cnt[i]!}"

/-- Follow the first step at every level with the stage clocks; one line per step (the
discriminant used, the tier, time/count per stage) and the totals. -/
def profile (P : GenParams) (n : AzNat) : IO Unit := do
  let tiers := P.tierTables
  let zeroT : Array UInt64 := Array.replicate 8 0
  let zeroC : Array Nat := Array.replicate 8 0
  let mut totT := zeroT
  let mut totC := zeroC
  let mut m := n
  for _ in [0:n.size] do
    if m.size ≤ P.baseBits then break
    let mut accT := zeroT
    let mut accC := zeroC
    let mut found : Option (StepCert × Nat) := none
    let mut tier := 0
    if h : 1 < m.toNat then
      have : NeZero m.toNat := ⟨by omega⟩
      let mut cache : SqrtCache m := {}
      for t in tiers do
        let (r, cache', a, c) ← findStepTimed P t.get m cache accT accC
        cache := cache'
        accT := a
        accC := c
        if r.isSome then
          found := r
          break
        tier := tier + 1
    totT := (totT.zip accT).map fun (a, b) => a + b
    totC := (totC.zip accC).map fun (a, b) => a + b
    match found with
    | some (c, D) =>
      let tot := accT.foldl (· + ·) 0
      IO.println
        s!"   {m.size} -> {c.q.size} D={D} tier={tier} {ms tot}ms: {showStages accT accC}"
      m := c.q
    | none =>
      IO.println s!"   {m.size} bits: no step: {showStages accT accC}"
      break
  IO.println s!"   total {ms (totT.foldl (· + ·) 0)}ms: {showStages totT totC}"

/-- `benchmark ecpp 1 "modmul:1"`: the cost of one multiplication modulo `m` and of its two
halves, for moduli of several sizes.  Nanoseconds per operation, over 2000 operand pairs. -/
def modmulParts : IO Unit := do
  for bits in [64, 128, 256, 500, 512, 1000, 1024, 2048] do
    let m := AzNat.pow (AzNat.ofNat 2) bits - AzNat.ofNat 159
    if h : m.toNat ≠ 0 then
      have : NeZero m.toNat := ⟨h⟩
      let big := AzNat.pow (AzNat.ofNat 1000003) (bits / 10 + 3)
      let xs : Array AzNat := (Array.range 2000).map fun i =>
        (big * AzNat.ofNat (i * i + 7 * i + 11) + AzNat.ofNat i) % m
      let ys : Array AzNat := (Array.range 2000).map fun i =>
        (big * AzNat.ofNat (3 * i * i + i + 5) + AzNat.ofNat (2 * i + 1)) % m
      let ps : Array AzNat := (Array.range 2000).map fun i => xs[i]! * ys[i]!
      let zx : Array (AzZMod m) := xs.map (AzZMod.ofAzNat m)
      let zy : Array (AzZMod m) := ys.map (AzZMod.ofAzNat m)
      let loop (f : Nat → Nat) : IO UInt64 := do
        let t0 ← IO.monoNanosNow
        let mut s := 0
        for i in [0:2000] do
          s := s + f i
        let t1 ← IO.monoNanosNow
        if s == 0 then IO.println "?"
        return ((t1 - t0) / 2000).toUInt64
      let tMul ← loop fun i => (xs[i]! * ys[i]!).limbs.size
      let tSqr ← loop fun i => (AzNat.square xs[i]!).limbs.size
      let tMod ← loop fun i => (ps[i]! % m).limbs.size + 1
      let tBoth ← loop fun i => ((xs[i]! * ys[i]!) % m).limbs.size + 1
      let tZ ← loop fun i => (zx[i]! * zy[i]!).val.limbs.size + 1
      let tZs ← loop fun i => (Square.square zx[i]!).val.limbs.size + 1
      let tAdd ← loop fun i => (zx[i]! + zy[i]!).val.limbs.size + 1
      -- Barrett's step with a precomputed reciprocal of the normalized modulus
      let n := m.limbs.size
      let k := 64 * n - m.size
      let V := m <<< k
      let X := AzNat.approxReciprocal AzNat.reciprocalBaseThreshold AzNat.newtonFFTThreshold V n
      let pre (t : AzNat) : AzNat :=
        (AzNat.barrettStep AzNat.shortProductBase V X n (t <<< k)).2 >>> k
      let tPre ← loop fun i => (pre ps[i]!).limbs.size + 1
      let ok := (List.range 2000).all fun i => pre ps[i]! == ps[i]! % m
      -- Montgomery reduction (`AzNat/Montgomery.lean`)
      let c := AzNat.MontCtx.make m
      let tRedc ← loop fun i => (c.redc ps[i]!).limbs.size + 1
      let tMont ← loop fun i => (c.mul xs[i]! ys[i]!).limbs.size + 1
      let tMontS ← loop fun i => (c.sqr xs[i]!).limbs.size + 1
      let okM := (List.range 2000).all fun i =>
        c.fromMont (c.mul (c.toMont xs[i]!) (c.toMont ys[i]!)) == ps[i]! % m
      IO.println s!"{bits} bits (ns): mul {tMul}, square {tSqr}, mod {tMod}, mul+mod {tBoth}, AzZMod mul {tZ}, AzZMod square {tZs}, AzZMod add {tAdd}, Barrett mod {tPre} ({ok}), Montgomery: redc {tRedc}, mul {tMont}, square {tMontS} ({okM})"

/-- `benchmark ecpp 1 "digits:D,root:1"`: the pieces of one squaring in `PackedMod` (the power
`(X + r)^((n−1)/2)` modulo a monic `g` of the root finding), for a `D`-digit modulus and
several degrees.  Microseconds per operation over 100 different residues. -/
def rootParts (digits : Nat) : IO Unit := do
  let n := AzNat.pow (AzNat.ofNat 10) digits + AzNat.ofNat 331
  if h : n.toNat ≠ 0 then
    have : NeZero n.toNat := ⟨h⟩
    for d in [2, 4, 8, 16, 24, 48] do
      let big := AzNat.pow (AzNat.ofNat 1000003) (digits / 5 + 3)
      let g : Array AzNat := (Array.range d).map fun i =>
        (big * AzNat.ofNat (i * i + 3 * i + 7) + AzNat.ofNat i) % n
      let M := PackedMod.make n g
      -- 100 residues: successive squares
      let mut accs : Array (Array AzNat) := #[]
      let mut acc := M.mulLinear (M.c.toMont (AzNat.ofNat 5)) (g.map M.c.toMont)
      for _ in [0:100] do
        acc := M.sqr acc
        accs := accs.push acc
      let loop (f : Nat → Nat) : IO Float := do
        let t0 ← IO.monoNanosNow
        let mut s := 0
        for i in [0:100] do
          s := s + f i
        let t1 ← IO.monoNanosNow
        if s == 0 then IO.println "?"
        return (t1 - t0).toFloat / 100000.0
      let ev := accs.map (evalPM M.hw)
      let sq := ev.map (·.sqr M.hw)
      let ps := sq.map (unpackCoeffs M.c M.hw (2 * d - 1))
      let his := ps.map fun p => (Array.range (d - 1)).map fun i => p[2 * d - 2 - i]!
      let hp := his.map (evalPM M.hw)
      let qi := hp.map (·.mul M.hw M.invEval)
      let qrs := qi.map (unpackCoeffs M.c M.hw (d - 1))
      let qp := qrs.map fun q => evalPM M.hw q.reverse
      let qg := qp.map (·.mul M.hw M.gEval)
      let tAll ← loop fun i => (M.sqr accs[i]!).size
      let tPack ← loop fun i => (evalPM M.hw accs[i]!).plus.limbs.size + 1
      let tSq ← loop fun i => (ev[i]!.sqr M.hw).1.limbs.size + 1
      let tSqP ← loop fun i => (AzNat.square ev[i]!.plus).limbs.size + 1
      let tUnp ← loop fun i => (unpackCoeffs M.c M.hw (2 * d - 1) sq[i]!).size
      let tQi ← loop fun i => (hp[i]!.mul M.hw M.invEval).1.limbs.size + 1
      let tUnq ← loop fun i => (unpackCoeffs M.c M.hw (d - 1) qi[i]!).size
      let tQg ← loop fun i => (qp[i]!.mul M.hw M.gEval).1.limbs.size + 1
      let tUng ← loop fun i => (unpackCoeffs M.c M.hw d qg[i]!).size
      let tLin ← loop fun i => (M.mulLinear (AzNat.ofNat 12345) accs[i]!).size
      let r (x : Float) : String := toString ((x * 10).round / 10)
      IO.println s!"degree {d}, hw = {M.hw} limbs (µs): sqr {r tAll} = eval {r tPack} + square {r tSq} (one of the two squarings {r tSqP}) + unpack {r tUnp} + q: product {r tQi}, unpack {r tUnq} + q·g: product {r tQg}, unpack {r tUng}; mulLinear {r tLin}"
      -- the gcd at the end of a round
      let f : AzPolynomial (AzZMod n) :=
        AzPolynomial.normalize ((g.push 1).map (AzZMod.ofAzNat n))
      let t : AzPolynomial (AzZMod n) :=
        AzPolynomial.normalize ((accs[99]!.map M.c.fromMont).map (AzZMod.ofAzNat n)) - 1
      let t0 ← IO.monoNanosNow
      let res := AzPolynomial.gcdOrFactor n t f
      let deg := match res with | .inl _ => 0 | .inr x => x.natDegree + 1
      let t1 ← IO.monoNanosNow
      let t2 ← IO.monoNanosNow
      let M2 := PackedMod.make n g
      let t3 ← IO.monoNanosNow
      IO.println s!"   gcdOrFactor {ms (t1 - t0).toUInt64}ms ({deg}), PackedMod.make {ms (t3 - t2).toUInt64}ms ({M2.hw})"

/-- `benchmark ecpp 1 "classpoly:1"`: the class polynomial of `−D` by `j` and by Weber's
invariants, for some `D ≡ 7 (mod 8)` of growing class number. -/
def classPolyParts : IO Unit := do
  for D in [1319, 4079, 9239, 20639, 49871, 1295, 5015] do
    let (h, tH) ← timeOnce fun _ => (hilbertClassPoly D).map (·.length)
    let (w, tW) ← timeOnce fun _ => (weberClassPoly D).map (·.length)
    let (g, tG) ← timeOnce fun _ => (genusClassPoly D).map (·.terms.length)
    let (gw, tGW) ← timeOnce fun _ => (genusWeberPoly D).map (·.terms.length)
    IO.println s!"D={D} h={classNumber D}: H {ms tH}ms ({h}), W {ms tW}ms ({w}), \
      genus H {ms tG}ms ({g}), genus W {ms tGW}ms ({gw})"

def run (limit : Nat) (cfg : Std.HashMap String String) : IO Unit := do
  let d := configGetNat cfg "digits" 30
  if cfg.contains "classpoly" then
    classPolyParts
    return
  let P := params cfg
  let ps := nextProbablePrimes (AzNat.ofNat (10 ^ d) + 1) limit
  if cfg.contains "modmul" then
    modmulParts
    return
  if cfg.contains "root" then
    rootParts d
    return
  for n in ps do
    if cfg.contains "profile" then
      IO.println s!"n ≈ 10^{d} ({n.size} bits)"
      profile P n
    else if cfg.contains "trace" then
      IO.println s!"n ≈ 10^{d} ({n.size} bits)"
      trace P n
    else if cfg.contains "parts" then
      IO.println s!"n ≈ 10^{d} ({n.size} bits)"
      parts P n
    else
      let (cert, tGen) ← timeOnce fun _ => ecppCertificate n P
      match cert with
      | none => IO.println s!"n ≈ 10^{d} ({n.size} bits): no certificate, gen={ms tGen}ms"
      | some c =>
        let (ok, tCheck) ← timeOnce fun _ => check n c
        IO.println
          s!"n ≈ 10^{d} ({n.size} bits): steps={c.length} gen={ms tGen}ms check={ms tCheck}ms ({ok})"
      if !cfg.contains "noaprcl" then
        let (r, tA) ← timeOnce fun _ => n.isPrimeAprcl
        IO.println s!"   isPrimeAprcl: {ms tA}ms ({r})"

end Azurite.Benchmark.Ecpp
