/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Exp
import Azurite.AzFloat.Ln
import Azurite.AzFloat.Pow
import Azurite.AzFloat.PowBase
import Azurite.AzFloat.PowBaseBracket
import Azurite.AzFloat.PowRat
import Azurite.AzFloat.RatPow
import Azurite.AzFloat.RatPowRat
import Azurite.AzRat.Parse
import Azurite.Benchmark.Common

/-!
# The `pow` family: where the time goes

`az_float_pow`: for each precision `P` (bits), the time (ms) of the four rational/float power
drivers and the natural-base power on irrational inputs — `pow (3/2)^(1/3)` (floats),
`ratPow (1/3)^(1/2)`, `powRat (3/2)^(1/3)`, `ratPowRat (1/3)^(1/3)`, `powBase 3^(1/3)` — and
the pieces of one `pow` bracket at its start precision `w = powStart`: the bracket of `ln` at
`W = expWork ey w` (`lnBr`), `ln2Bracket W` (`ln2`), `expBracketAt` at `w` (`expBr`); for
reference `exp` and `ln` of a float at `P` bits.  Config: `bits` (default `53/200/1000/5000`).
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
private def psize (x : AzFloat × Ordering) : Nat := fsize x.1
private def bsize (x : AzFloat × AzFloat) : Nat := fsize x.1 + fsize x.2

/-- Run the `az_float_pow` benchmark. -/
def runAzFloatPow (_limit : Nat) (cfg : Std.HashMap String String) (_seed : UInt64) :
    IO Unit := do
  let bitsList : Array Nat := match cfg["bits"]? with
    | some s =>
      ((s.splitOn "/").filterMap (fun t : String => t.trimAscii.toString.toNat?)).toArray
    | none => #[53, 200, 1000, 5000]
  let q32 := (AzRat.parse "3/2").get!
  let q13 := (AzRat.parse "1/3").get!
  let q12 := (AzRat.parse "1/2").get!
  IO.println "[AzFloat-Pow] ms per call (median of 3 passes); pieces at w = powStart"
  IO.println (padLeft "bits" 6 ++ padLeft "w" 6 ++ padLeft "pow" 9 ++ padLeft "ratPow" 9
    ++ padLeft "powRat" 9 ++ padLeft "ratPRat" 9 ++ padLeft "powBase" 9 ++ padLeft "lnBr" 9
    ++ padLeft "ln2" 9 ++ padLeft "expBr" 9 ++ padLeft "exp" 9 ++ padLeft "ln" 9)
  for P in bitsList do
    let x := ofAzRat q32 P
    let y := ofAzRat q13 P
    let h := ofAzRat q12 P
    let ex := x.exponent?.getD 0
    let ey := y.exponent?.getD 0
    let w := powStart ey ex P
    let W := expWork ey w
    let ns1 ← timeOne (fun _ => powPrecRound x y P .Nearest) psize
    let ns2 ← timeOne (fun _ => ratPowPrecRound q13 h P .Nearest) psize
    let ns3 ← timeOne (fun _ => powRatPrecRound x q13 P .Nearest) psize
    let ns4 ← timeOne (fun _ => ratPowRatPrecRound q13 q13 P .Nearest) psize
    let ns5 ← timeOne (fun _ => powBasePrecRound 3 y P .Nearest) psize
    let nsL ← timeOne (fun _ => lnBracket x ex W) bsize
    let ns2b ← timeOne (fun _ => ln2Bracket W) bsize
    let L := lnMulBracket x ex y ey w
    let nsE ← timeOne (fun _ => expBracketAt L.1 w) bsize
    let nsExp ← timeOne (fun _ => expPrecRound y P .Nearest) psize
    let nsLn ← timeOne (fun _ => lnPrecRound x P .Nearest) psize
    IO.println (padLeft s!"{P}" 6 ++ padLeft s!"{w}" 6 ++ padLeft (ms ns1) 9 ++ padLeft (ms ns2) 9
      ++ padLeft (ms ns3) 9 ++ padLeft (ms ns4) 9 ++ padLeft (ms ns5) 9 ++ padLeft (ms nsL) 9
      ++ padLeft (ms ns2b) 9 ++ padLeft (ms nsE) 9 ++ padLeft (ms nsExp) 9 ++ padLeft (ms nsLn) 9)

/-- `lg` of a finite float (the exponent `e` with `2^(e−1) ≤ |x| < 2^e`), as a string. -/
private def lg (x : AzFloat) : String :=
  match x.exponent? with
  | some e => toString e.toInt
  | none => "?"

/-- The bits lost by a bracket at working precision `w`: `w + lg (hi − lo)` (absolute) and
`w + lg ((hi − lo) / |hi|)` (relative). -/
private def lost (b : AzFloat × AzFloat) (w : Nat) : String :=
  let d := (subPrecRound b.2 b.1 53 .Nearest).1
  let r := (divPrecRound d b.2.abs 53 .Nearest).1
  match d.exponent?, r.exponent? with
  | some e, some f => s!"{(w : Int) + e.toInt}/{(w : Int) + f.toInt}"
  | _, _ => "?"

/-- Run the `az_float_pow_width` benchmark: the bits lost by the pieces of the `pow` bracket
(`abs/rel`), at `w = powStart` and at `w = P + 64`, for several bases and exponents. -/
def runAzFloatPowWidth (_limit : Nat) (cfg : Std.HashMap String String) (_seed : UInt64) :
    IO Unit := do
  let bitsList : Array Nat := match cfg["bits"]? with
    | some s =>
      ((s.splitOn "/").filterMap (fun t : String => t.trimAscii.toString.toNat?)).toArray
    | none => #[53, 200, 1000]
  let pairs : List (String × String) :=
    [("3/2", "1/3"), ("10", "1/7"), ("1000000", "1/3"), ("1/3", "-100"), ("7/5", "1000"),
     ("2", "-1/1000000"), ("1234567/1000", "-12345/100")]
  IO.println "[AzFloat-Pow-Width] bits lost (abs/rel) by lnMul at W, exp at w, pow at w"
  IO.println (padLeft "bits" 6 ++ padLeft "x" 14 ++ padLeft "y" 12 ++ padLeft "w" 6
    ++ padLeft "lnMul@W" 10 ++ padLeft "exp@w" 10 ++ padLeft "pow@w" 10 ++ padLeft "w'" 6
    ++ padLeft "lnMul@W'" 10 ++ padLeft "pow@w'" 10 ++ padLeft "pB@w'" 10)
  for P in bitsList do
    for (xs, ys) in pairs do
      let x := ofAzRat ((AzRat.parse xs).get!) P
      let y := ofAzRat ((AzRat.parse ys).get!) P
      let ex := x.exponent?.getD 0
      let ey := y.exponent?.getD 0
      for (w, tag) in [(powStart ey ex P, "w"), (P + zivGuardBits, "w'")] do
        let W := expWork ey w
        let L := lnMulBracket x ex y ey w
        let E := expBracketAt L.1 w
        let B := powBracket x ex y ey w
        let BB := powBaseBracket y ey 3 w
        if tag == "w" then
          IO.print (padLeft s!"{P}" 6 ++ padLeft xs 14 ++ padLeft ys 12 ++ padLeft s!"{w}" 6
            ++ padLeft (lost L W) 10 ++ padLeft (lost E w) 10 ++ padLeft (lost B w) 10)
        else
          IO.println (padLeft s!"{w}" 6 ++ padLeft (lost L W) 10 ++ padLeft (lost B w) 10
            ++ padLeft (lost BB w) 10)
  -- the natural-base pieces at 53 bits
  let y := ofAzRat ((AzRat.parse "1/3").get!) 53
  let ey := y.exponent?.getD 0
  let w := powBaseStart ey 3 53
  let W := expWork ey w
  let nsX ← timeOne (fun _ => powBaseExact? y (AzNat.ofNat 3)) (fun r => if r.isSome then 1 else 2)
  let nsL ← timeOne (fun _ => lnBaseBracket 3 W) bsize
  let nsM ← timeOne (fun _ => lnBaseMulBracket y ey 3 w) bsize
  let nsB ← timeOne (fun _ => powBaseBracket y ey 3 w) bsize
  let nsP ← timeOne (fun _ => powBasePrecRound 3 y 53 .Nearest) psize
  IO.println (s!"powBase 3^(1/3) @53, w = {w}: exact? {ms nsX}  lnBase {ms nsL}  "
    ++ s!"lnBaseMul {ms nsM}  bracket {ms nsB}  full {ms nsP}")

/-- Whether the first Ziv attempt (at the start precision) already rounds. -/
private def firstOk (a : Roundable × Roundable) (P : Nat) : String :=
  if (roundingPossible a.1 a.2 P .Nearest).isSome then "ok" else "FAIL"

/-- Run the `az_float_pow_first` benchmark: for several inputs and precisions, the start
precisions of the eight pow-family Ziv loops and whether their first attempt succeeds. -/
def runAzFloatPowFirst (_limit : Nat) (cfg : Std.HashMap String String) (_seed : UInt64) :
    IO Unit := do
  let bitsList : Array Nat := match cfg["bits"]? with
    | some s =>
      ((s.splitOn "/").filterMap (fun t : String => t.trimAscii.toString.toNat?)).toArray
    | none => #[1, 2, 10, 53, 200, 1000]
  let pairs : List (String × String) :=
    [("3/2", "1/3"), ("10", "1/7"), ("1000000", "1/3"), ("1/3", "-100"), ("7/5", "1000"),
     ("2", "-1/1000000"), ("1234567/1000", "-12345/100"), ("5", "1/1000000000000"),
     ("3", "-3/1000000000")]
  IO.println "[AzFloat-Pow-First] start precision / first attempt of the eight Ziv loops"
  IO.println (padLeft "bits" 5 ++ padLeft "x" 14 ++ padLeft "y" 16 ++ padLeft "pow" 10
    ++ padLeft "ratPow" 10 ++ padLeft "powRat" 10 ++ padLeft "ratPRat" 10 ++ padLeft "pBase" 10
    ++ padLeft "pBRat" 10 ++ padLeft "pBM1" 10 ++ padLeft "pBM1Rat" 10)
  for P in bitsList do
    for (xs, ys) in pairs do
      let qx := (AzRat.parse xs).get!
      let qy := (AzRat.parse ys).get!
      let x := ofAzRat qx P
      let y := ofAzRat qy P
      let ex := x.exponent?.getD 0
      let ey := y.exponent?.getD 0
      let w1 := powStart ey ex P
      let w2 := ratPowStart ey qx P
      let w3 := powRatStart qy ex P
      let w4 := ratPowRatStart qy qx P
      let w5 := powBaseStart ey 3 P
      let w6 := powBaseRatStart qy 3 P
      let w7 := powBaseM1Start ey 3 P
      let w8 := powBaseM1RatStart qy 3 P
      IO.println (padLeft s!"{P}" 5 ++ padLeft xs 14 ++ padLeft ys 16
        ++ padLeft s!"{w1}/{firstOk (powApprox false x ex y ey w1) P}" 10
        ++ padLeft s!"{w2}/{firstOk (ratPowApprox false qx y ey w2) P}" 10
        ++ padLeft s!"{w3}/{firstOk (powRatApprox false x ex qy w3) P}" 10
        ++ padLeft s!"{w4}/{firstOk (ratPowRatApprox false qx qy w4) P}" 10
        ++ padLeft s!"{w5}/{firstOk (powBaseApprox y ey 3 w5) P}" 10
        ++ padLeft s!"{w6}/{firstOk (powBaseRatApprox qy 3 w6) P}" 10
        ++ padLeft s!"{w7}/{firstOk (powBaseM1Approx y ey 3 w7) P}" 10
        ++ padLeft s!"{w8}/{firstOk (powBaseM1RatApprox qy 3 w8) P}" 10)

end Azurite.Benchmark
