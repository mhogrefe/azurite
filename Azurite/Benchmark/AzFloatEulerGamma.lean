/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.EulerGamma
import Azurite.AzFloat.Ln
import Azurite.AzFloat.Pi
import Azurite.Benchmark.Common

/-!
# Euler's constant: where the time goes

`az_float_euler_gamma`: for each precision `P` (bits), the time of `eulerGamma P` (nearest, Ziv
loop from `w = P + 64`) and the pieces of one bracket at `w = P + 64`: the signed binary
splitting of Sweeney's series (`AzInt.sweeneyNumDen`, column `split`), the float bracket of the
exact fraction (`seriesBracket`, column `serBr`), the bracket of `ln n` (`lnBracketOf`, column
`lnBr`), and for reference `pi P` and `ln` of a float at `P` bits.  Milliseconds.  Config: `bits`
(default `53/200/1000/5000`).
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

/-- Run the `az_float_euler_gamma` benchmark. -/
def runAzFloatEulerGamma (_limit : Nat) (cfg : Std.HashMap String String) (_seed : UInt64) :
    IO Unit := do
  let bitsList : Array Nat := match cfg["bits"]? with
    | some s =>
      ((s.splitOn "/").filterMap (fun t : String => t.trimAscii.toString.toNat?)).toArray
    | none => #[53, 200, 1000, 5000]
  IO.println "[AzFloat-EulerGamma] ms per call (median of 3 passes); pieces at w = P + 64"
  IO.println (padLeft "bits" 7 ++ padLeft "n" 7 ++ padLeft "N" 8 ++ padLeft "gamma" 10
    ++ padLeft "split" 10 ++ padLeft "serBr" 10 ++ padLeft "lnBr" 10 ++ padLeft "pi" 10
    ++ padLeft "ln 3/2" 10)
  for P in bitsList do
    let w := P + zivGuardBits
    let n := eulerGammaN w
    let N := eulerGammaTerms w
    let k := eulerGammaBits w
    let nsG ← timeOne (fun _ => eulerGamma P) fsize
    let nsS ← timeOne (fun _ => AzInt.sweeneyNumDen n N) (fun s => s.2.size)
    let s := AzInt.sweeneyNumDen n N
    let nsB ← timeOne (fun _ => seriesBracket (s.1.natAbs, s.2) k) (fun b => fsize b.1)
    let nsL ← timeOne (fun _ => lnBracketOf (ofAzNat (AzNat.ofNat n)) k) (fun b => fsize b.1)
    let nsP ← timeOne (fun _ => pi P) fsize
    let y := ofAzRat ((AzRat.parse "3/2").get!) P
    let nsLn ← timeOne (fun _ => ln y) fsize
    IO.println (padLeft s!"{P}" 7 ++ padLeft s!"{n}" 7 ++ padLeft s!"{N}" 8 ++ padLeft (ms nsG) 10
      ++ padLeft (ms nsS) 10 ++ padLeft (ms nsB) 10 ++ padLeft (ms nsL) 10 ++ padLeft (ms nsP) 10
      ++ padLeft (ms nsLn) 10)

end Azurite.Benchmark
