/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Atan
import Azurite.AzFloat.Ln
import Azurite.AzFloat.Sin
import Azurite.AzRat.Parse
import Azurite.Benchmark.Common

/-!
# `atan`: timings

`az_float_atan`: for each precision `P` (bits) and each base argument (`1/1000`, `5/7`, `3`,
`1000`), the time (ms per call) of `sinPrecRound`, `lnPrecRound` and `atanPrecRound`, and two
pieces of the arctangent: one bracket `atanBracket` at the first Ziv level `w = P + 64` (column
`brkt`) and, for `|x| < 1` and a top level `K > 256` (below that the top step starts from the
machine-word seed), the levels of `atanLoop` below the top one (column `low`: the loop at level
`⌈K/5⌉`), so that `brkt − low` is the top step.  Each pass runs over `reps` distinct
arguments near the base argument; the passes alternate and the median of three is reported.
Config: `bits` (default `53/113/200/500/1000/2000/5000/20000`).
-/

open Azurite Azurite.AzFloat Azurite.Benchmark

namespace Azurite.Benchmark

private def padLeft (s : String) (w : Nat) : String :=
  "".pushn ' ' (w - s.length) ++ s

/-- Total ns of `f` over the arguments (the checksum keeps the results alive). -/
@[noinline] private def passOver (xs : Array AzFloat) (f : AzFloat → Nat) : IO UInt64 := do
  let t0 ← monoNanos
  let mut acc := 0
  for x in xs do
    acc := acc + f x
  if acc = 0 then IO.eprintln "(zero checksum)"
  let t1 ← monoNanos
  return (t1 - t0) / xs.size.toUInt64

private def ms (ns : UInt64) : String :=
  let us := ns.toNat / 1000
  s!"{us / 1000}.{padLeft s!"{us % 1000}" 3 |>.replace " " "0"}"

private def psize (x : AzFloat × Ordering) : Nat := x.1.precision?.getD 0 + 1

private def esize (b : AzFloat × AzFloat) : Nat := b.1.precision?.getD 0 + 1

private def ratio (a b : UInt64) : String :=
  if b = 0 then "-" else
    let r := (a.toNat * 100) / b.toNat
    s!"{r / 100}.{padLeft s!"{r % 100}" 2 |>.replace " " "0"}"

/-- Run the `az_float_atan` benchmark. -/
def runAzFloatAtan (_limit : Nat) (cfg : Std.HashMap String String) (_seed : UInt64) :
    IO Unit := do
  let bitsList : Array Nat := match cfg["bits"]? with
    | some s =>
      ((s.splitOn "/").filterMap (fun t : String => t.trimAscii.toString.toNat?)).toArray
    | none => #[53, 113, 200, 500, 1000, 2000, 5000, 20000]
  IO.println "[AzFloat-Atan] ms per call (median of 3 alternating passes)"
  IO.println (padLeft "bits" 6 ++ padLeft "x" 7 ++ padLeft "reps" 6 ++ padLeft "sin" 11
    ++ padLeft "ln" 11 ++ padLeft "atan" 11 ++ padLeft "brkt" 11 ++ padLeft "low" 11
    ++ padLeft "atan/sin" 10 ++ padLeft "atan/ln" 9)
  for P in bitsList do
    for (base, num, den) in
        #[("1/1000", 1, 1000), ("5/7", 5, 7), ("3", 3, 1), ("1000", 1000, 1)] do
      let reps := max 2 (4000 / P)
      let xs : Array AzFloat := (Array.range reps).filterMap fun i =>
        (AzRat.parse s!"{num * 1000003 + i * den}/{den * 1000003}").map fun q => ofAzRat q P
      let w := P + zivGuardBits
      let fS := fun x => psize (sinPrecRound x P .Nearest)
      let fL := fun x => psize (lnPrecRound x P .Nearest)
      let fA := fun x => psize (atanPrecRound x P .Nearest)
      let fB := fun (x : AzFloat) => esize (atanBracket x (x.exponent?.getD 0) w)
      let fW := fun (x : AzFloat) =>
        let ex := x.exponent?.getD 0
        if ex.sign = false ∨ ex.abs.toNat = 0 then
          let K := atanWork ex w
          if K ≤ 256 then 1 else esize (atanLoop x.abs K ((K + 4) / 5))
        else 1
      let s1 ← passOver xs fS
      let l1 ← passOver xs fL
      let a1 ← passOver xs fA
      let b1 ← passOver xs fB
      let w1 ← passOver xs fW
      let s2 ← passOver xs fS
      let l2 ← passOver xs fL
      let a2 ← passOver xs fA
      let b2 ← passOver xs fB
      let w2 ← passOver xs fW
      let s3 ← passOver xs fS
      let l3 ← passOver xs fL
      let a3 ← passOver xs fA
      let b3 ← passOver xs fB
      let w3 ← passOver xs fW
      let s := median3 s1 s2 s3
      let l := median3 l1 l2 l3
      let a := median3 a1 a2 a3
      let b := median3 b1 b2 b3
      let lw := median3 w1 w2 w3
      IO.println (padLeft s!"{P}" 6 ++ padLeft base 7 ++ padLeft s!"{reps}" 6 ++ padLeft (ms s) 11
        ++ padLeft (ms l) 11 ++ padLeft (ms a) 11 ++ padLeft (ms b) 11 ++ padLeft (ms lw) 11
        ++ padLeft (ratio a s) 10 ++ padLeft (ratio a l) 9)

end Azurite.Benchmark
