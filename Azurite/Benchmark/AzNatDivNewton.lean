/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzNat.Div
import Azurite.Benchmark.Common
import Azurite.Benchmark.AzNatDivCross

/-!
# Division crossover: classical vs Newton–Barrett at fixed sizes

`az_nat_div_newton`: for each divisor size `n` (limbs) and a dividend of `ratio · n` limbs, times
`divModClassic divDispatchThreshold` and `divModNewton base fftFrom sp` for each base threshold
in `bases`, FFT threshold in `ffts` and short-product base case in `sps`, in µs per division, with the ratio to the classical path.  Sizes are exact (top limb has
its high bit set).
-/

open Azurite Azurite.Random Azurite.Benchmark

namespace Azurite.Benchmark

@[noinline] def benchDivModClassic (iters : Nat) (pairs : Array (AzNat × AzNat)) :
    IO UInt64 := do
  let t0 ← monoNanos
  let mut checksum : Nat := 0
  for _ in List.range iters do
    for (u, v) in pairs do
      let r := AzNat.divModClassic AzNat.divDispatchThreshold u v
      checksum := checksum + r.1.limbs.size + r.2.limbs.size
  let t1 ← monoNanos
  if checksum = 0 then IO.eprintln "unreachable"
  return t1 - t0

@[noinline] def benchDivModNewton (base fftFrom sp iters : Nat) (pairs : Array (AzNat × AzNat)) :
    IO UInt64 := do
  let t0 ← monoNanos
  let mut checksum : Nat := 0
  for _ in List.range iters do
    for (u, v) in pairs do
      let r := AzNat.divModNewton base fftFrom sp u v
      checksum := checksum + r.1.limbs.size + r.2.limbs.size
  let t1 ← monoNanos
  if checksum = 0 then IO.eprintln "unreachable"
  return t1 - t0

private def padLeft (s : String) (w : Nat) : String :=
  "".pushn ' ' (w - s.length) ++ s

/-- Config keys: `limbs` (divisor sizes, `/`-separated, default `2048/4096/8192/16384`), `bases`
(reciprocal base thresholds, default `512`), `ffts` (`fftFrom` thresholds for the FFT-range
tricks, default `999999/0`: plain, then the tricks forced on), `sps` (short-product base-case
sizes, default `32`), `ratio` (dividend limbs / divisor limbs, default `2`), `iters` (passes per
timing, default `1`).  One column per `(base, fft, sp)` triple. -/
def runAzNatDivNewton (limit : Nat) (cfg : Std.HashMap String String) (seed : UInt64) :
    IO Unit := do
  let sizes := configGetNatSlashList cfg "limbs" #[2048, 4096, 8192, 16384]
  let bases := configGetNatSlashList cfg "bases" #[512]
  let ffts := configGetNatSlashList cfg "ffts" #[999999, 0]
  let sps := configGetNatSlashList cfg "sps" #[32]
  let ratio := configGetNat cfg "ratio" 2
  let iters := configGetNat cfg "iters" 1
  IO.println s!"[AzNat-DivNewton] classical vs Newton–Barrett; dividend = {ratio}× divisor \
    limbs; {limit} pairs per size; µs per division (% = vs classical)"
  let mut header := padLeft "limbs" 6 ++ padLeft "classic" 10
  for b in bases do
    for f in ffts do
      for sp in sps do
        header := header ++ padLeft s!"b{b}/f{f}/s{sp}" 15 ++ padLeft "%" 5
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
    let nsClassic ← do
      let a ← benchDivModClassic iters pairs
      let b ← benchDivModClassic iters pairs
      let c ← benchDivModClassic iters pairs
      pure (median3 a b c)
    let usClassic := nsClassic.toNat / divisions / 1000
    let mut row := padLeft s!"{n}" 6 ++ padLeft s!"{usClassic}" 10
    for b in bases do
      for f in ffts do
        for sp in sps do
          let a ← benchDivModNewton b f sp iters pairs
          let b' ← benchDivModNewton b f sp iters pairs
          let c ← benchDivModNewton b f sp iters pairs
          let ns := median3 a b' c
          let us := ns.toNat / divisions / 1000
          let pct := if nsClassic = 0 then 0 else ns.toNat * 100 / nsClassic.toNat
          row := row ++ padLeft s!"{us}" 15 ++ padLeft s!"{pct}" 5
    IO.println row

end Azurite.Benchmark
