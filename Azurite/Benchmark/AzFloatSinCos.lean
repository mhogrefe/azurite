/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.SinCos
import Azurite.AzRat.Parse
import Azurite.Benchmark.Common

/-!
# `sinCos` against `sin` and `cos`: timings

`az_float_sin_cos`: for each precision `P` (bits) and each base argument (`5/7`, `3`, `1000`),
the time (ms per call) of `sinPrecRound`, `cosPrecRound`, the two together, and
`sinCosPrecRound`, with the ratio `(sin + cos) / sinCos`.  Each pass runs over `reps` distinct
arguments near the base argument (so that nothing is hoisted out of the loop); the passes of the
three functions alternate and the median of three is reported.  Config: `bits` (default
`53/113/200/500/1000/2000/5000/20000`).
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

/-- Run the `az_float_sin_cos` benchmark. -/
def runAzFloatSinCos (_limit : Nat) (cfg : Std.HashMap String String) (_seed : UInt64) :
    IO Unit := do
  let bitsList : Array Nat := match cfg["bits"]? with
    | some s =>
      ((s.splitOn "/").filterMap (fun t : String => t.trimAscii.toString.toNat?)).toArray
    | none => #[53, 113, 200, 500, 1000, 2000, 5000, 20000]
  IO.println "[AzFloat-SinCos] ms per call (median of 3 alternating passes)"
  IO.println (padLeft "bits" 6 ++ padLeft "x" 6 ++ padLeft "reps" 6 ++ padLeft "sin" 11
    ++ padLeft "cos" 11 ++ padLeft "sin+cos" 11 ++ padLeft "sinCos" 11 ++ padLeft "ratio" 8)
  for P in bitsList do
    for (base, num, den) in #[("5/7", 5, 7), ("3", 3, 1), ("1000", 1000, 1)] do
      let reps := max 2 (4000 / P)
      let xs : Array AzFloat := (Array.range reps).filterMap fun i =>
        (AzRat.parse s!"{num * 1000003 + i * den}/{den * 1000003}").map fun q => ofAzRat q P
      let fS := fun x => psize (sinPrecRound x P .Nearest)
      let fC := fun x => psize (cosPrecRound x P .Nearest)
      let fSC := fun x =>
        let r := sinCosPrecRound x P .Nearest
        psize r.1 + psize r.2
      let s1 ← passOver xs fS
      let c1 ← passOver xs fC
      let j1 ← passOver xs fSC
      let s2 ← passOver xs fS
      let c2 ← passOver xs fC
      let j2 ← passOver xs fSC
      let s3 ← passOver xs fS
      let c3 ← passOver xs fC
      let j3 ← passOver xs fSC
      let s := median3 s1 s2 s3
      let c := median3 c1 c2 c3
      let j := median3 j1 j2 j3
      let ratio100 := if j = 0 then 0 else ((s + c).toNat * 100) / j.toNat
      IO.println (padLeft s!"{P}" 6 ++ padLeft base 6 ++ padLeft s!"{reps}" 6 ++ padLeft (ms s) 11
        ++ padLeft (ms c) 11 ++ padLeft (ms (s + c)) 11 ++ padLeft (ms j) 11
        ++ padLeft s!"{ratio100 / 100}.{padLeft s!"{ratio100 % 100}" 2 |>.replace " " "0"}" 8)

end Azurite.Benchmark
