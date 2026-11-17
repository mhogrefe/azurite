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

`az_float_lambert_extreme`: arguments in the subnormal range of `Float` (`|x| < 2^(−1022)`),
arguments with exponents up to `±2^200`, and `W₀ (1/3)` at a few precisions.
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

/-- Run the `az_float_lambert_extreme` benchmark: arguments in the subnormal range of `Float`
and arguments with huge exponents, where the candidate used to miss (ms per call). -/
def runAzFloatLambertExtreme (_limit : Nat) (_cfg : Std.HashMap String String) (_seed : UInt64) :
    IO Unit := do
  let nat := fun (n : Nat) => ofAzNat (AzNat.ofNat n)
  let sh := fun (x : AzFloat) (k : Int) => x <<< AzInt.ofInt k
  IO.println "[AzFloat-Lambert-extreme] ms per call (median of 3 passes)"
  let row := fun (name : String) (f : Unit → AzFloat × Ordering) => do
    let t ← timeOne f psize
    IO.println (padLeft name 44 ++ padLeft (ms t) 10)
  -- `−0x6.2dc507e392e14E−268`: the reported subnormal argument
  let xsub := -(sh (nat 0x62dc507e392e14) (-1124))
  row "Wm1 -0x6.2dc507e392e14E-268 @93" fun _ => lambertWm1PrecRound xsub 93 .Nearest
  row "Wm1 same @53" fun _ => lambertWm1PrecRound xsub 53 .Nearest
  row "Wm1 same @200" fun _ => lambertWm1PrecRound xsub 200 .Nearest
  row "W0 same @93" fun _ => lambertW0PrecRound xsub 93 .Nearest
  row "Wm1 -2^-1030 @93" fun _ => lambertWm1PrecRound (-(sh one (-1030))) 93 .Nearest
  row "Wm1 -3*2^-1074 @53" fun _ => lambertWm1PrecRound (-(sh (nat 3) (-1074))) 53 .Nearest
  row "Wm1 -2^-1000 @93 (normal range)" fun _ => lambertWm1PrecRound (-(sh one (-1000))) 93 .Nearest
  row "Wm1 -2^-1100 @93 (below Float)" fun _ => lambertWm1PrecRound (-(sh one (-1100))) 93 .Nearest
  row "W0 3*2^-1050 @93" fun _ => lambertW0PrecRound (sh (nat 3) (-1050)) 93 .Nearest
  -- huge exponents: `|W|` has more integer bits than the working precision
  for k in [60, 70, 78, 100, 200] do
    let xh := one <<< AzInt.ofInt (2 ^ k)
    row s!"W0 2^(2^{k}) @3" fun _ => lambertW0PrecRound xh 3 .Nearest
    row s!"W0 2^(2^{k}) @53" fun _ => lambertW0PrecRound xh 53 .Nearest
    let xs := -(one <<< AzInt.ofInt (-(2 ^ k)))
    row s!"Wm1 -2^(-2^{k}) @3" fun _ => lambertWm1PrecRound xs 3 .Nearest
    row s!"Wm1 -2^(-2^{k}) @53" fun _ => lambertWm1PrecRound xs 53 .Nearest
  -- the top of the `Float` range: the `Float` seed used to stall from about `2^1022` on
  for k in [990, 1010, 1021, 1022, 1023, 1030] do
    let xt := sh (nat 3) k
    for P in [53, 200, 1000] do
      row s!"W0 3*2^{k} @{P}" fun _ => lambertW0PrecRound xt P .Nearest
  -- precisions where the Halley schedule used to end short
  let third := ofAzRat ((AzRat.parse "1/3").get!) 53
  for P in [53, 99, 100, 120, 150, 310] do
    row s!"W0 1/3 @{P}" fun _ => lambertW0PrecRound third P .Nearest

end Azurite.Benchmark
