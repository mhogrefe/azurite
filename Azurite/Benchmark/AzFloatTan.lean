/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Sin
import Azurite.AzFloat.Tan
import Azurite.AzRat.Parse
import Azurite.Benchmark.Common

/-!
# `tan`: timings, and four divisions against two

`az_float_tan`: for each precision `P` (bits) and each base argument (`5/7`, `3`, `1000`), the
time (ms per call) of `sinPrecRound`, of `tanPrecRound`, and of two fuel-driven replicas of the
tangent loop that differ only in the quotient of the sine bracket by the `|cos|` bracket:
`tan4` with `enclDivSignedPos4` (four directed divisions, no sign analysis: the first version)
and `tan2` with the library's `enclDivSignedPos` (two divisions, chosen by the signs of the ends
of the sine bracket; adopted on 2026-11-14).  The replicas are experiments local to this file (no
proofs).  Each pass runs over
`reps` distinct arguments near the base argument; the passes alternate and the median of three is
reported.  Config: `bits` (default `53/113/200/500/1000/2000/5000/20000`).
-/

open Azurite Azurite.AzFloat Azurite.Benchmark

namespace Azurite.Benchmark

/-- `[s] / [b]` for a positive `[b]` with four divisions and no sign test (the first version of
the library's `enclDivSignedPos`, kept here for the comparison). -/
def enclDivSignedPos4 (w : Nat) (s b : Encl) : Encl :=
  (minOf (divPrecRound s.1 b.1 w .Floor).1 (divPrecRound s.1 b.2 w .Floor).1,
    maxOf (divPrecRound s.2 b.1 w .Ceiling).1 (divPrecRound s.2 b.2 w .Ceiling).1)

/-- `tanBracket` with the quotient `div`. -/
def tanBracketWith (div : Nat → Encl → Encl → Encl) (x : AzFloat) (ex : AzInt) (w : Nat) :
    AzFloat × AzFloat :=
  let b := sinCosBracket x ex w
  let B := enclAbs b.2
  match B.1 with
  | zero => (-one, one)
  | _ =>
    let T := div (w + 12) b.1 B
    if b.2.2.isNegative then Encl.neg T else T

/-- The tangent of a positive float by the fuel-driven loop on `tanBracketWith div`. -/
def tanWith (div : Nat → Encl → Encl → Encl) (x : AzFloat) (p : Nat) : AzFloat × Ordering :=
  let ex := x.exponent?.getD 0
  zivLoop (fun w =>
    let b := tanBracketWith div x ex w
    (fun P M => setPrecRound b.1 P M, fun P M => setPrecRound b.2 P M)) p .Nearest 20
    (p + zivGuardBits)

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

private def pct (a b : UInt64) : String :=
  if b = 0 then "-" else
    let r := (a.toNat * 1000) / b.toNat
    s!"{r / 10}.{r % 10}%"

/-- Run the `az_float_tan` benchmark. -/
def runAzFloatTan (_limit : Nat) (cfg : Std.HashMap String String) (_seed : UInt64) :
    IO Unit := do
  let bitsList : Array Nat := match cfg["bits"]? with
    | some s =>
      ((s.splitOn "/").filterMap (fun t : String => t.trimAscii.toString.toNat?)).toArray
    | none => #[53, 113, 200, 500, 1000, 2000, 5000, 20000]
  IO.println "[AzFloat-Tan] ms per call (median of 3 alternating passes)"
  IO.println (padLeft "bits" 6 ++ padLeft "x" 6 ++ padLeft "reps" 6 ++ padLeft "sin" 11
    ++ padLeft "tan" 11 ++ padLeft "tan4" 11 ++ padLeft "tan2" 11 ++ padLeft "tan2/tan4" 11
    ++ padLeft "same" 6)
  for P in bitsList do
    for (base, num, den) in #[("5/7", 5, 7), ("3", 3, 1), ("1000", 1000, 1)] do
      let reps := max 2 (4000 / P)
      let xs : Array AzFloat := (Array.range reps).filterMap fun i =>
        (AzRat.parse s!"{num * 1000003 + i * den}/{den * 1000003}").map fun q => ofAzRat q P
      let fS := fun x => psize (sinPrecRound x P .Nearest)
      let fT := fun x => psize (tanPrecRound x P .Nearest)
      let f4 := fun x => psize (tanWith enclDivSignedPos4 x P)
      let f2 := fun x => psize (tanWith enclDivSignedPos x P)
      let same := xs.all fun x =>
        tanWith enclDivSignedPos x P == tanPrecRound x P .Nearest
          && tanWith enclDivSignedPos4 x P == tanPrecRound x P .Nearest
      let s1 ← passOver xs fS
      let t1 ← passOver xs fT
      let a1 ← passOver xs f4
      let b1 ← passOver xs f2
      let s2 ← passOver xs fS
      let t2 ← passOver xs fT
      let a2 ← passOver xs f4
      let b2 ← passOver xs f2
      let s3 ← passOver xs fS
      let t3 ← passOver xs fT
      let a3 ← passOver xs f4
      let b3 ← passOver xs f2
      let s := median3 s1 s2 s3
      let t := median3 t1 t2 t3
      let a := median3 a1 a2 a3
      let b := median3 b1 b2 b3
      IO.println (padLeft s!"{P}" 6 ++ padLeft base 6 ++ padLeft s!"{reps}" 6 ++ padLeft (ms s) 11
        ++ padLeft (ms t) 11 ++ padLeft (ms a) 11 ++ padLeft (ms b) 11 ++ padLeft (pct b a) 11
        ++ padLeft s!"{same}" 6)

end Azurite.Benchmark
