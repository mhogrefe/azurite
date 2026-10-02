/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/
import Azurite.AzNat.Div
import Azurite.Benchmark.Common
import Azurite.Benchmark.LimbWidth

/-!
# Division crossover: schoolbook vs divide-and-conquer at fixed sizes

`az_nat_div_cross`: for each divisor size `n` (limbs) and a dividend of `ratio · n` limbs, times
`divModWith` at threshold `999999` (pure schoolbook) and at each threshold in `thresholds`, in µs
per division, with the ratio to schoolbook.  Sizes are exact (top limb has its high bit set), so
the table is a clean crossover picture rather than a mean-size cloud.
-/

open Azurite Azurite.Random Azurite.Benchmark

namespace Azurite.Benchmark

/-- A `/`-separated list of naturals from the config (`,` separates config entries). -/
def configGetNatSlashList (cfg : Std.HashMap String String) (key : String)
    (default : Array Nat) : Array Nat :=
  match cfg[key]? with
  | none => default
  | some s =>
    let xs := (s.splitOn "/").filterMap (·.trimAscii.toString.toNat?)
    if xs.isEmpty then default else xs.toArray

/-- A random `AzNat` of exactly `n` limbs (the top limb has its high bit set). -/
def randomAzNatOfLimbs (n : Nat) (g : SplitMix64) : AzNat × SplitMix64 :=
  let (xs, g') := Azurite.Benchmark.LimbWidth.randomLimbs64 n g
  let xs := if h : 0 < xs.size then
    xs.set (xs.size - 1) (xs[xs.size - 1] ||| ((1 : UInt64) <<< 63)) else xs
  (AzNat.ofLimbs xs, g')

/-- Time `divModWith threshold` over all pairs, `iters` passes; returns total ns. -/
@[noinline] def benchDivModWith (threshold iters : Nat) (pairs : Array (AzNat × AzNat)) :
    IO UInt64 := do
  let t0 ← monoNanos
  let mut checksum : Nat := 0
  for _ in List.range iters do
    for (u, v) in pairs do
      let r := AzNat.divModWith threshold u v
      checksum := checksum + r.1.limbs.size + r.2.limbs.size
  let t1 ← monoNanos
  if checksum = 0 then IO.eprintln "unreachable"
  return t1 - t0

/-- Median-of-three total ns. -/
def benchDivModWithMedian (threshold iters : Nat) (pairs : Array (AzNat × AzNat)) :
    IO UInt64 := do
  let a ← benchDivModWith threshold iters pairs
  let b ← benchDivModWith threshold iters pairs
  let c ← benchDivModWith threshold iters pairs
  return median3 a b c

private def padLeft (s : String) (w : Nat) : String :=
  "".pushn ' ' (w - s.length) ++ s

/-- Run the `az_nat_div_cross` benchmark; `limit` is the number of random pairs per size.
Config keys: `limbs` (divisor sizes, `/`-separated, default `32/64/128/256/512/1024/2048`),
`thresholds` (default `4/8/16/32/64/128/256`), `ratio` (dividend limbs / divisor limbs, default
`2`), `iters` (passes per timing, default `3`). -/
def runAzNatDivCross (limit : Nat) (cfg : Std.HashMap String String) (seed : UInt64) :
    IO Unit := do
  let sizes := configGetNatSlashList cfg "limbs" #[32, 64, 128, 256, 512, 1024, 2048]
  let thresholds := configGetNatSlashList cfg "thresholds" #[4, 8, 16, 32, 64, 128, 256]
  let ratio := configGetNat cfg "ratio" 2
  let iters := configGetNat cfg "iters" 3
  IO.println s!"[AzNat-DivCross] divModWith; dividend = {ratio}× divisor limbs; {limit} pairs \
    per size; µs per division (schoolbook = threshold 999999; % = vs schoolbook)"
  let mut header := padLeft "limbs" 6 ++ padLeft "school" 9
  for t in thresholds do
    header := header ++ padLeft s!"t={t}" 9 ++ padLeft "%" 5
  IO.println header
  let mut g := mkSplitMix64 seed
  for n in sizes do
    let mut pairs : Array (AzNat × AzNat) := #[]
    for _ in List.range limit do
      let (u, g₁) := randomAzNatOfLimbs (ratio * n) g
      let (v, g₂) := randomAzNatOfLimbs n g₁
      g := g₂
      pairs := pairs.push (u, v)
    let divisions := iters * limit
    let nsSchool ← benchDivModWithMedian 999999 iters pairs
    let usSchool := nsSchool.toNat / divisions / 1000
    let mut row := padLeft s!"{n}" 6 ++ padLeft s!"{usSchool}" 9
    for t in thresholds do
      let ns ← benchDivModWithMedian t iters pairs
      let us := ns.toNat / divisions / 1000
      let pct := if nsSchool = 0 then 0 else ns.toNat * 100 / nsSchool.toNat
      row := row ++ padLeft s!"{us}" 9 ++ padLeft s!"{pct}" 5
    IO.println row

end Azurite.Benchmark
