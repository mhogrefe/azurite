/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.ECPP.Gen.Search
import Azurite.AzNat.IsPrime
import Azurite.Benchmark.Common

open Azurite Azurite.ECPP Azurite.Benchmark

/-!
# Elliptic curve primality proving: timing

`benchmark ecpp <limit> "digits:D"` takes the first `limit` probable primes above `10^D`
and, for each, times the certificate generator (`ecppCertificate`), the checker (`check`)
and, unless `noaprcl:1` is given, `AzNat.isPrime` (Miller–Rabin and APR-CL) on the same
number.  The search parameters can be set with `dmax`, `hmax`, `trial`, `base`.
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
    trialBound := configGetNat cfg "trial" d.trialBound,
    baseBits := configGetNat cfg "base" d.baseBits,
    tiers := configGetNat cfg "tiers" d.tiers }

/-- Time the pieces of one step for `n`. -/
def parts (P : GenParams) (n : AzNat) : IO Unit := do
  if h : 1 < n.toNat then
    have : NeZero n.toNat := ⟨by omega⟩
    let (tabs, tT) ← timeOnce fun _ => P.tables
    IO.println s!"   tables: {tabs.discs.length} discriminants, {tabs.primes.length} primes  {ms tT}ms"
    let (r, tS) ← timeOnce fun _ => sqrtSmall? n (-3)
    IO.println s!"   one square root (−3): {ms tS}ms ({r.isSome})"
    let (j, tJ) ← timeOnce fun _ => AzNat.jacobi (n / AzNat.ofNat 3) n
    IO.println s!"   one Jacobi symbol: {ms tJ}ms ({j})"
    let (q, tD) ← timeOnce fun _ => (trialDivide (n + 1) tabs.primes).1.size
    IO.println s!"   trial division of one m: {ms tD}ms ({q} bits left)"
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
      let mut cache : SqrtCache n := []
      let mut s := (0, 0, 0, 0)
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
            for m in candidateOrders n D x y do
              let (q, c) := trialDivide m T.primes
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

/-- `findStep` with a clock on every stage.  The times (nanoseconds) and counts are added to
`acc`: square roots, Cornacchia, trial division, the size test, probable primes, class
polynomials, their roots, curves. -/
def findStepTimed (P : GenParams) (T : GenTables) (n : AzNat) [NeZero n.toNat]
    (cache : SqrtCache n) (acc : Array UInt64) (cnt : Array Nat) :
    IO (Option (StepCert × Nat) × SqrtCache n × Array UInt64 × Array Nat) := do
  if 1 < n.toNat then
    let mut acc := acc
    let mut cnt := cnt
    let mut cache := cache
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
          let mut curves : Option (List (AzZMod n × AzZMod n)) := none
          for m in candidateOrders n D x y do
            let ((q, c), t) ← timeOnce fun _ => trialDivide m T.primes
            acc := acc.modify 2 (· + t)
            cnt := cnt.modify 2 (· + 1)
            if c = 1 then continue
            let (ab, t) ← timeOnce fun _ => aboveBound n q
            acc := acc.modify 3 (· + t)
            cnt := cnt.modify 3 (· + 1)
            if !ab then continue
            let (pp, t) ← timeOnce fun _ => probablePrime q
            acc := acc.modify 4 (· + t)
            cnt := cnt.modify 4 (· + 1)
            if !pp then continue
            let cs ← match curves with
              | some cs => pure cs
              | none => do
                let mut tH : UInt64 := 0
                if D ≠ 3 ∧ D ≠ 4 then
                  let (_, t) ← timeOnce fun _ => (hilbertClassPoly D).map (·.length)
                  tH := t
                  acc := acc.modify 5 (· + t)
                  cnt := cnt.modify 5 (· + 1)
                let (cs, t) ← timeOnce fun _ => cmCurves n D P.tries
                acc := acc.modify 6 (· + (if tH < t then t - tH else 0))
                cnt := cnt.modify 6 (· + 1)
                pure cs
            curves := some cs
            for (a, b) in cs do
              let (res, t) ← timeOnce fun _ => tryCurve a b c q P.tries
              acc := acc.modify 7 (· + t)
              cnt := cnt.modify 7 (· + 1)
              match res with
              | none => continue
              | some cert => return (some (cert, D), cache, acc, cnt)
    return (none, cache, acc, cnt)
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
      let mut cache : SqrtCache m := []
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

def run (limit : Nat) (cfg : Std.HashMap String String) : IO Unit := do
  let d := configGetNat cfg "digits" 30
  let P := params cfg
  let ps := nextProbablePrimes (AzNat.ofNat (10 ^ d) + 1) limit
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
        let (r, tA) ← timeOnce fun _ => n.isPrime
        IO.println s!"   isPrime (APR-CL): {ms tA}ms ({r})"

end Azurite.Benchmark.Ecpp
