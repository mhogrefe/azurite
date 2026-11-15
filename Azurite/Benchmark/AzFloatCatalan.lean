/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Catalan
import Azurite.AzFloat.EulerGamma
import Azurite.AzFloat.Pi
import Azurite.Benchmark.Common

/-!
# Catalan's constant: where the time goes

`az_float_catalan`: for each precision `P` (bits), the time of `catalanConstant P` (nearest, Ziv
loop from `w = P + 64`) and the pieces of one bracket at `w = P + 64`: the binary splitting of
`S = ∑ 1/((2k+1)² C(2k,k))` (`AzNat.catalanNumDen`, column `splitS`) and of
`A = ∑ 1/((2k+1) 3^(k+1))` (`AzNat.atanhSqrtThreeNumDen`, column `splitA`), the float brackets
of the two exact fractions (`seriesBracket`, column `serBr`), the two roundings of `√3` (column
`sqrt3`), `piBracket` (column `piBr`), and for reference `pi P` and `eulerGamma P`.
Milliseconds.  Config: `bits` (default `53/200/1000/5000/20000`).
-/

open Azurite Azurite.AzFloat Azurite.Benchmark

namespace Azurite.Benchmark

private def padLeft (s : String) (w : Nat) : String :=
  "".pushn ' ' (w - s.length) ++ s

/-- Total ns of `f ()`, median of three passes (checksum keeps the result alive). -/
@[noinline] private def timeOne {α : Type} (f : Unit → α) (size : α → Nat) : IO UInt64 := do
  let pass : IO UInt64 := do
    let t0 ← monoNanos
    let acc := size (f ())
    let t1 ← monoNanos
    if acc = 0 then IO.eprintln "(zero checksum)"
    return t1 - t0
  let a ← pass
  let b ← pass
  let c ← pass
  return median3 a b c

private def ms (ns : UInt64) : String :=
  let us := ns.toNat / 1000
  s!"{us / 1000}.{padLeft s!"{us % 1000}" 3 |>.replace " " "0"}"

private def fsize (x : AzFloat) : Nat := x.precision?.getD 0

/-- Run the `az_float_catalan` benchmark. -/
def runAzFloatCatalan (_limit : Nat) (cfg : Std.HashMap String String) (_seed : UInt64) :
    IO Unit := do
  let bitsList : Array Nat := match cfg["bits"]? with
    | some s =>
      ((s.splitOn "/").filterMap (fun t : String => t.trimAscii.toString.toNat?)).toArray
    | none => #[53, 200, 1000, 5000, 20000]
  IO.println "[AzFloat-Catalan] ms per call (median of 3 passes); pieces at w = P + 64"
  IO.println (padLeft "bits" 7 ++ padLeft "N_S" 7 ++ padLeft "N_A" 7 ++ padLeft "G" 10
    ++ padLeft "splitS" 10 ++ padLeft "splitA" 10 ++ padLeft "serBr" 10 ++ padLeft "sqrt3" 10
    ++ padLeft "piBr" 10 ++ padLeft "pi" 10 ++ padLeft "gamma" 10)
  for P in bitsList do
    let w := P + zivGuardBits
    let k := catalanBits w
    let nS := catalanTerms w
    let nA := atanhSqrtThreeTerms w
    let nsG ← timeOne (fun _ => AzFloat.catalanConstant P) fsize
    let nsS ← timeOne (fun _ => AzNat.catalanNumDen nS) (fun s => s.2.size)
    let nsA ← timeOne (fun _ => AzNat.atanhSqrtThreeNumDen nA) (fun s => s.2.size)
    let s := AzNat.catalanNumDen nS
    let a := AzNat.atanhSqrtThreeNumDen nA
    let nsB ← timeOne (fun _ => (seriesBracket s k, seriesBracket a k))
      (fun b => fsize b.1.1 + fsize b.2.1)
    let three := ofAzNat (AzNat.ofNat 3)
    let nsR ← timeOne (fun _ => ((sqrtPrecRound three k .Floor).1,
      (sqrtPrecRound three k .Ceiling).1)) (fun b => fsize b.1 + fsize b.2)
    let nsPB ← timeOne (fun _ => piBracket k) (fun b => fsize b.1)
    let nsP ← timeOne (fun _ => pi P) fsize
    let nsE ← timeOne (fun _ => eulerGamma P) fsize
    IO.println (padLeft s!"{P}" 7 ++ padLeft s!"{nS}" 7 ++ padLeft s!"{nA}" 7
      ++ padLeft (ms nsG) 10 ++ padLeft (ms nsS) 10 ++ padLeft (ms nsA) 10 ++ padLeft (ms nsB) 10
      ++ padLeft (ms nsR) 10 ++ padLeft (ms nsPB) 10 ++ padLeft (ms nsP) 10
      ++ padLeft (ms nsE) 10)

end Azurite.Benchmark
