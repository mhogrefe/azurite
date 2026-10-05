/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzNat.Gcd
import Azurite.AzRat.Add
import Azurite.AzRat.Compare
import Azurite.AzRat.Div
import Azurite.AzRat.Mul
import Azurite.Benchmark.AzNatDivCross
import Azurite.Benchmark.Common

/-!
# Where `AzRat` spends its time

`az_rat_profile`: for each operand size (bits of numerator and denominator), the time of the
`AzNat` gcd of two such numbers, of the `AzNat` multiplication and division, of the normalized
construction `ofSignAzNats`, and of `AzRat` addition, multiplication, division and comparison on
random reduced rationals.  Microseconds per call.
-/

open Azurite Azurite.Random Azurite.Benchmark

namespace Azurite.Benchmark

private def padLeft (s : String) (w : Nat) : String :=
  "".pushn ' ' (w - s.length) ++ s

/-- Total ns of `f` over all `xs` (each input computed once per pass, results kept alive by a
checksum so nothing is hoisted), median of three passes. -/
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

/-- Run the `az_rat_profile` benchmark.  Config: `bits` (`/`-separated, default
`64/256/1024/4096/16384`), `inputs` (random operand sets per size, default `4`). -/
def runAzRatProfile (_limit : Nat) (cfg : Std.HashMap String String) (seed : UInt64) :
    IO Unit := do
  let bitsList := match cfg["bits"]? with
    | some s => ((s.splitOn "/").filterMap (fun t : String => t.trimAscii.toString.toNat?)).toArray
    | none => #[64, 256, 1024, 4096, 16384]
  let count := configGetNat cfg "inputs" 4
  IO.println s!"[AzRat-Profile] µs per call (median of 3 passes over {count} random inputs per \
    size); operands of the given bit size"
  IO.println (padLeft "bits" 7 ++ padLeft "gcd" 10 ++ padLeft "natMul" 10 ++ padLeft "natDiv" 10
    ++ padLeft "construct" 11 ++ padLeft "ratAdd" 10 ++ padLeft "ratMul" 10 ++ padLeft "ratDiv" 10
    ++ padLeft "ratCmp" 10)
  let mut g := mkSplitMix64 seed
  for bits in bitsList do
    let limbs := (bits + 63) / 64
    let mut nats : Array (AzNat × AzNat) := #[]
    let mut rats : Array (AzRat × AzRat) := #[]
    for _ in List.range count do
      let (a, g₁) := randomAzNatOfLimbs limbs g
      let (b, g₂) := randomAzNatOfLimbs limbs g₁
      let (c, g₃) := randomAzNatOfLimbs limbs g₂
      let (d, g₄) := randomAzNatOfLimbs limbs g₃
      g := g₄
      nats := nats.push (a, b)
      rats := rats.push (AzRat.ofSignAzNats true a b, AzRat.ofSignAzNats true c d)
    let nsGcd ← timeOver nats (fun (a, b) => AzNat.gcd a b) (·.limbs.size)
    let nsMul ← timeOver nats (fun (a, b) => a * b) (·.limbs.size)
    let nsDiv ← timeOver nats (fun (a, b) => a / b) (·.limbs.size)
    let nsCon ← timeOver nats (fun (a, b) => AzRat.ofSignAzNats true a b) (·.num.limbs.size)
    let nsAdd ← timeOver rats (fun (x, y) => x + y) (·.num.limbs.size)
    let nsRMul ← timeOver rats (fun (x, y) => x * y) (·.num.limbs.size)
    let nsRDiv ← timeOver rats (fun (x, y) => x / y) (·.num.limbs.size)
    let nsCmp ← timeOver rats (fun (x, y) => compare x y) (fun o => if o = .lt then 1 else 2)
    IO.println (padLeft s!"{bits}" 7 ++ padLeft (us nsGcd count) 10 ++ padLeft (us nsMul count) 10
      ++ padLeft (us nsDiv count) 10 ++ padLeft (us nsCon count) 11 ++ padLeft (us nsAdd count) 10
      ++ padLeft (us nsRMul count) 10 ++ padLeft (us nsRDiv count) 10
      ++ padLeft (us nsCmp count) 10)

end Azurite.Benchmark
