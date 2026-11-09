/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Exp
import Azurite.AzFloat.Ln
import Azurite.AzFloat.LambertW
import Azurite.AzRat.Parse
import Azurite.Benchmark.Common

/-!
# The Lambert `W` function: timings

`az_float_lambert`: for each precision `P` (bits), the time (ms) of `W₀` at `1/2`, `1`, `10¹⁰`,
`−1/10` and one ulp above the 53-bit float nearest `−e⁻¹` (the branch point), of `W₋₁` at
`−1/10`, `−2^(−100)` and the same branch-point float, and for reference `exp` and `ln` of a float
at `P` bits.  Config: `bits` (default `53/200/1000/5000`).
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

private def psize (x : AzFloat × Ordering) : Nat := x.1.precision?.getD 0

/-- Run the `az_float_lambert` benchmark. -/
def runAzFloatLambert (_limit : Nat) (cfg : Std.HashMap String String) (_seed : UInt64) :
    IO Unit := do
  let bitsList : Array Nat := match cfg["bits"]? with
    | some s =>
      ((s.splitOn "/").filterMap (fun t : String => t.trimAscii.toString.toNat?)).toArray
    | none => #[53, 200, 1000, 5000]
  let q := fun (s : String) => (AzRat.parse s).get!
  IO.println "[AzFloat-Lambert] ms per call (median of 3 passes)"
  IO.println (padLeft "bits" 6 ++ padLeft "W0 1/2" 9 ++ padLeft "W0 1" 9 ++ padLeft "W0 1e10" 9
    ++ padLeft "W0 -.1" 9 ++ padLeft "W0 bp" 9 ++ padLeft "Wm -.1" 9 ++ padLeft "Wm 2^-100" 10
    ++ padLeft "Wm bp" 9 ++ padLeft "exp" 9 ++ padLeft "ln" 9)
  for P in bitsList do
    let x12 := ofAzRat (q "1/2") P
    let x1 := ofAzRat (q "1") P
    let x10 := ofAzRat (q "10000000000") P
    let xm := ofAzRat (q "-1/10") P
    let xbp := ofAzRat (q "-6627126856707895/18014398509481984") P
    let xsm := ofAzRat (q "-1/1267650600228229401496703205376") P
    let t1 ← timeOne (fun _ => lambertW0PrecRound x12 P .Nearest) psize
    let t2 ← timeOne (fun _ => lambertW0PrecRound x1 P .Nearest) psize
    let t3 ← timeOne (fun _ => lambertW0PrecRound x10 P .Nearest) psize
    let t4 ← timeOne (fun _ => lambertW0PrecRound xm P .Nearest) psize
    let t5 ← timeOne (fun _ => lambertW0PrecRound xbp P .Nearest) psize
    let t6 ← timeOne (fun _ => lambertWm1PrecRound xm P .Nearest) psize
    let t7 ← timeOne (fun _ => lambertWm1PrecRound xsm P .Nearest) psize
    let t8 ← timeOne (fun _ => lambertWm1PrecRound xbp P .Nearest) psize
    let t9 ← timeOne (fun _ => expPrecRound x12 P .Nearest) psize
    let t10 ← timeOne (fun _ => lnPrecRound x12 P .Nearest) psize
    IO.println (padLeft s!"{P}" 6 ++ padLeft (ms t1) 9 ++ padLeft (ms t2) 9 ++ padLeft (ms t3) 9
      ++ padLeft (ms t4) 9 ++ padLeft (ms t5) 9 ++ padLeft (ms t6) 9 ++ padLeft (ms t7) 10
      ++ padLeft (ms t8) 9 ++ padLeft (ms t9) 9 ++ padLeft (ms t10) 9)

end Azurite.Benchmark
