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
(`/`-separated `t-q` pairs — binary fallback `t`, quadratic-layer bound `q` — for extra
`gcdHalfBinaryWith` columns, default none). -/
def runAzNatGcd (_limit : Nat) (cfg : Std.HashMap String String) (seed : UInt64) : IO Unit := do
  let bitsList := match cfg["bits"]? with
    | some s => ((s.splitOn "/").filterMap (fun t : String => t.trimAscii.toString.toNat?)).toArray
    | none => #[128, 256, 512, 1024, 2048, 4096, 16384, 65536]
  let count := configGetNat cfg "inputs" 4
  let skipBinary := configGetNat cfg "skipBinary" 1000000
  let thresholds : Array (Nat × Nat) := match cfg["thresholds"]? with
    | some s => ((s.splitOn "/").filterMap fun t : String =>
        match (t.trimAscii.toString.splitOn "-").map String.toNat? with
        | [some x, some y] => some (x, y)
        | _ => none).toArray
    | none => #[]
  IO.println s!"[AzNat-GCD] µs per call (median of 3 passes over {count} random pairs per size, \
    common factor ≈ bits/3)"
  IO.println (padLeft "bits" 7 ++ padLeft "gcdBinary" 12 ++ padLeft "gcdHalfBin" 12
    ++ padLeft "gcd" 12 ++ String.join (thresholds.toList.map fun t => padLeft s!"{t.1}-{t.2}" 12))
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
      let ns ← timeOver pairs (fun (a, b) => AzNat.gcdHalfBinaryWith t.1 t.2 a b) (·.limbs.size)
      extra := extra ++ padLeft (us ns count) 12
    IO.println (padLeft s!"{bits}" 7
      ++ padLeft (if bits ≤ skipBinary then us nsBin count else "-") 12
      ++ padLeft (us nsHalf count) 12 ++ padLeft (us nsGcd count) 12 ++ extra)


/-- Time `f x`; `f` and `x` arrive as arguments of a non-inlined function so the compiler cannot
float the computation out of the timed region. -/
@[noinline] private def timeIt {β α : Type} (f : β → α) (x : β) (size : α → Nat) :
    IO (α × Float) := do
  let t0 ← monoNanos
  let v := f x
  if size v = 424242424242 then IO.eprintln "(unlikely checksum)"
  let t1 ← monoNanos
  return (v, (t1 - t0).toNat.toFloat / 1000.0)

/-- Run the `az_nat_gcd_breakdown` benchmark: one top-level step of `halfBinaryGcdDriver` at each
size (config `limbs`, `/`-separated, default `1024/2048/4096`), split into truncation, half-gcd,
matrix application, exact shifts and binary division, next to the balanced product, the
unbalanced product of a matrix entry by an operand, and the full `gcd`.  Microseconds. -/
def runAzNatGcdBreakdown (_limit : Nat) (cfg : Std.HashMap String String) (seed : UInt64) :
    IO Unit := do
  let limbsList := match cfg["limbs"]? with
    | some s => ((s.splitOn "/").filterMap (fun t : String => t.trimAscii.toString.toNat?)).toArray
    | none => #[1024, 2048, 4096]
  for limbs in limbsList do
    let g := mkSplitMix64 seed
    let (a0, g₁) := randomAzNatOfLimbs limbs g
    let (b0, _) := randomAzNatOfLimbs limbs g₁
    let a := if a0.isOdd then a0 else a0 + 1
    let b := if b0.isOdd then b0 + a else b0
    let x := a.toAzInt
    let y := b.toAzInt
    let n := max x.size y.size
    let k₁ := n / 2
    let m₁ := 2 * k₁ + 1
    let (lb, tLow) ← timeIt
      (fun p : AzInt × AzInt × Nat => (p.1.lowBits p.2.2, p.2.1.lowBits p.2.2)) (x, y, m₁)
      (fun p => p.1.size + p.2.size)
    let (jR, tHalf) ← timeIt
      (fun p : AzInt × AzInt × Nat => AzNat.halfBinaryGcd (p.2.2 + 1) p.1 p.2.1 p.2.2)
      (lb.1, lb.2, k₁) (fun p => p.1 + p.2.a.size)
    let (ab, tApply) ← timeIt (fun p : AzNat.Mat2 × AzInt × AzInt => p.1.apply p.2.1 p.2.2)
      (jR.2, x, y) (fun p => p.1.size + p.2.size)
    let (sh, tShift) ← timeIt (fun p : AzInt × AzInt × Nat =>
      (p.1.exactShiftRight p.2.2, p.2.1.exactShiftRight p.2.2)) (ab.1, ab.2, 2 * jR.1)
      (fun p => (p.1.map AzInt.size).getD 0 + (p.2.map AzInt.size).getD 0)
    match sh.1, sh.2 with
    | some a', some b' =>
      let j₀ := b'.trailingZeros.getD 0
      let b'' := AzInt.mkNorm b'.sign (b'.abs >>> j₀)
      let (qr, tDiv) ← timeIt (fun p : AzInt × AzInt × Nat => AzNat.binaryDivide p.1 p.2.1 p.2.2)
        (a', b'', j₀) (fun p => p.1.size + p.2.size)
      let (_, tMul) ← timeIt (fun p : AzNat × AzNat => p.1 * p.2) (a0, b0) (·.limbs.size)
      let (_, tMulUnbal) ← timeIt (fun p : AzNat × AzNat => p.1 * p.2) (jR.2.a.abs, a0)
        (·.limbs.size)
      let (_, tGcd) ← timeIt (fun p : AzNat × AzNat => AzNat.gcd p.1 p.2) (a0, b0)
        (·.limbs.size)
      IO.println s!"limbs={limbs}: R entry bits={jR.2.a.size} j={jR.1} j0={j₀} \
        a' bits={a'.size} r bits={qr.2.size}"
      IO.println s!"  lowBits {tLow} | halfGcd {tHalf} | apply {tApply} | shift {tShift} | \
        binDiv {tDiv} µs"
      IO.println s!"  balanced mul {tMul} | unbalanced mul (R entry × a) {tMulUnbal} | \
        full gcd {tGcd} µs"
    | _, _ => IO.println s!"limbs={limbs}: inexact shift (unexpected)"


/-- Run the `az_nat_gcd_word` benchmark: the cost of the pieces of one quadratic round at `limbs`
limbs (config `limbs`, default `4/8/16`), each as ns per call over `inputs` random inputs: the word
base case `halfBinaryGcdWord` alone, `lowWord2`, the two fused combinations of a round, one
`linCombLimbs` pass, and `Mat2.ofWord`. -/
def runAzNatGcdWord (_limit : Nat) (cfg : Std.HashMap String String) (seed : UInt64) : IO Unit := do
  let limbsList := match cfg["limbs"]? with
    | some s => ((s.splitOn "/").filterMap (fun t : String => t.trimAscii.toString.toNat?)).toArray
    | none => #[4, 8, 16]
  let count := configGetNat cfg "inputs" 64
  IO.println s!"[AzNat-GCD-word] ns per call (median of 3 passes over {count} random inputs)"
  IO.println (padLeft "limbs" 7 ++ padLeft "baseCase" 12 ++ padLeft "lowWord2" 12
    ++ padLeft "fused×2" 12 ++ padLeft "linComb" 12 ++ padLeft "ofWord" 12)
  for limbs in limbsList do
    let mut g := mkSplitMix64 seed
    let mut pairs : Array (AzInt × AzInt) := #[]
    for _ in List.range count do
      let (a0, g₁) := randomAzNatOfLimbs limbs g
      let (b0, g₂) := randomAzNatOfLimbs limbs g₁
      g := g₂
      let a := if a0.isOdd then a0 else a0 + 1
      let b := if b0.isOdd then b0 + a else b0
      pairs := pairs.push (a.toAzInt, b.toAzInt)
    let words := pairs.map fun (a, b) => (a.lowWord2 127, b.lowWord2 127)
    let nsBase ← timeOver words (fun (A, B) => AzNat.halfBinaryGcdWord A B 63) (·.1)
    let nsLow ← timeOver pairs (fun (a, b) => (a.lowWord2 127, b.lowWord2 127))
      (fun p => p.1.lo.toNat)
    let jMs := words.map fun (A, B) => AzNat.halfBinaryGcdWord A B 63
    let mut jsum := 0
    for jM in jMs do
      jsum := jsum + jM.1
    IO.println s!"  (limbs={limbs}: mean j per base-case call {jsum / count})"
    let inputs := (pairs.zip jMs)
    let nsApply ← timeOver inputs (fun ((a, b), jM) =>
        (AzNat.fusedCombine? jM.2.m₁₁ jM.2.m₁₂ a b (2 * jM.1),
          AzNat.fusedCombine? jM.2.m₂₁ jM.2.m₂₂ a b (2 * jM.1)))
      (fun q => match q.1 with | some z => z.size | none => 0)
    let nsShift ← timeOver inputs (fun ((a, b), jM) =>
        AzNat.linCombLimbs a.abs.limbs b.abs.limbs jM.2.m₁₁.toUInt64 jM.2.m₁₂.toUInt64 true)
      (·.1.size)
    let nsOfInts ← timeOver jMs (fun jM => AzNat.Mat2.ofWord jM.2) (·.a.size)
    IO.println (padLeft s!"{limbs}" 7 ++ padLeft s!"{nsBase.toNat / count}" 12
      ++ padLeft s!"{nsLow.toNat / count}" 12 ++ padLeft s!"{nsApply.toNat / count}" 12
      ++ padLeft s!"{nsShift.toNat / count}" 12 ++ padLeft s!"{nsOfInts.toNat / count}" 12)



end Azurite.Benchmark
