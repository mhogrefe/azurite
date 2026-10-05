/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzNat.Gcd
import Azurite.Benchmark.AzNatDivCross
import Azurite.Benchmark.Common

/-!
# Benchmark: AzNat GCD algorithms

`az_nat_gcd`: for each operand size (bits), the time of the binary GCD (`gcdBinary`), of the
half-binary GCD (`gcdHalfBinary`), and of the size-dispatching `gcd`, on random operands with a
planted common factor of about a third of the size.  Microseconds per call.
-/

open Azurite Azurite.Random Azurite.Benchmark

namespace Azurite.Benchmark

private def padLeft (s : String) (w : Nat) : String :=
  "".pushn ' ' (w - s.length) ++ s

/-- Total ns of `f` over all `xs`, median of three passes (see `AzRatProfile`). -/
@[noinline] private def timeOver {β α : Type} (xs : Array β) (f : β → α) (size : α → Nat) :
    IO UInt64 := do
  let pass : IO UInt64 := do
    let t0 ← monoNanos
    let mut acc : Nat := 0
    for x in xs do
      acc := acc + size (f x)
    let t1 ← monoNanos
    if acc = 0 then IO.eprintln "(zero checksum)"
    return t1 - t0
  let a ← pass
  let b ← pass
  let c ← pass
  return median3 a b c

private def us (ns : UInt64) (count : Nat) : String :=
  let v := ns.toNat * 10 / count / 1000
  s!"{v / 10}.{v % 10}"

/-- Run the `az_nat_gcd` benchmark.  Config: `bits` (`/`-separated, default
`128/256/512/1024/2048/4096/16384/65536`), `inputs` (random operand pairs per size, default `4`),
`skipBinary` (bits above which `gcdBinary` is not timed, default `1000000`), `thresholds`
(`/`-separated fallback thresholds for extra `gcdHalfBinaryWith` columns, default none). -/
def runAzNatGcd (_limit : Nat) (cfg : Std.HashMap String String) (seed : UInt64) : IO Unit := do
  let bitsList := match cfg["bits"]? with
    | some s => ((s.splitOn "/").filterMap (fun t : String => t.trimAscii.toString.toNat?)).toArray
    | none => #[128, 256, 512, 1024, 2048, 4096, 16384, 65536]
  let count := configGetNat cfg "inputs" 4
  let skipBinary := configGetNat cfg "skipBinary" 1000000
  let thresholds : Array Nat := match cfg["thresholds"]? with
    | some s => ((s.splitOn "/").filterMap (fun t : String => t.trimAscii.toString.toNat?)).toArray
    | none => #[]
  IO.println s!"[AzNat-GCD] µs per call (median of 3 passes over {count} random pairs per size, \
    common factor ≈ bits/3)"
  IO.println (padLeft "bits" 7 ++ padLeft "gcdBinary" 12 ++ padLeft "gcdHalfBin" 12
    ++ padLeft "gcd" 12 ++ String.join (thresholds.toList.map fun t => padLeft s!"t={t}" 10))
  let mut g := mkSplitMix64 seed
  for bits in bitsList do
    let limbs := (bits + 63) / 64
    let mut pairs : Array (AzNat × AzNat) := #[]
    for _ in List.range count do
      let (a, g₁) := randomAzNatOfLimbs limbs g
      let (b, g₂) := randomAzNatOfLimbs limbs g₁
      let (f, g₃) := randomAzNatOfLimbs (limbs / 3 + 1) g₂
      g := g₃
      pairs := pairs.push (a * f, b * f)
    let nsBin ← if bits ≤ skipBinary then
        timeOver pairs (fun (a, b) => AzNat.gcdBinary a b) (·.limbs.size)
      else pure 0
    let nsHalf ← timeOver pairs (fun (a, b) => AzNat.gcdHalfBinary a b) (·.limbs.size)
    let nsGcd ← timeOver pairs (fun (a, b) => AzNat.gcd a b) (·.limbs.size)
    let mut extra := ""
    for t in thresholds do
      let ns ← timeOver pairs (fun (a, b) => AzNat.gcdHalfBinaryWith t a b) (·.limbs.size)
      extra := extra ++ padLeft (us ns count) 10
    IO.println (padLeft s!"{bits}" 7
      ++ padLeft (if bits ≤ skipBinary then us nsBin count else "-") 12
      ++ padLeft (us nsHalf count) 12 ++ padLeft (us nsGcd count) 12 ++ extra)

end Azurite.Benchmark
