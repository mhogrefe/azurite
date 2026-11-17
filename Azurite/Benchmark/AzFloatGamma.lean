/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Gamma
import Azurite.AzFloat.GammaRat
import Azurite.AzFloat.LnGamma
import Azurite.AzFloat.LnGammaRat
import Azurite.AzFloat.Exp
import Azurite.AzFloat.Conversion
import Azurite.AzRat.Parse
import Azurite.Benchmark.Common

/-!
# `Γ`, `1/Γ` and `ln Γ` at a rational

`az_float_gamma`: for each precision `P` (bits) and each argument `x` (a rational rounded to
`max P 64` bits), the time of `gammaPrecRound x P` and `reciprocalGammaPrecRound x P` (nearest),
of `gammaRatPrecRound` at the rational itself, and for reference `lnGammaPrecRound x P` and
`lnGammaRatPrecRound` at the rational itself (both only for `x > 0`) and `expPrecRound x P`.
Milliseconds.  Config: `bits` (default `53/200/1000`), `xs` (`;`-separated rationals).
-/

open Azurite Azurite.AzFloat Azurite.Benchmark

namespace Azurite.Benchmark

private def padL (s : String) (w : Nat) : String := "".pushn ' ' (w - s.length) ++ s

@[noinline] private def timeMed {α : Type} (f : Unit → α) (size : α → Nat) : IO UInt64 := do
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

private def msStr (ns : UInt64) : String :=
  let us := ns.toNat / 1000
  s!"{us / 1000}.{padL s!"{us % 1000}" 3 |>.replace " " "0"}"

private def fsz (x : AzFloat) : Nat := x.precision?.getD 0 + 1

/-- Run the `az_float_gamma` benchmark. -/
def runAzFloatGamma (_limit : Nat) (cfg : Std.HashMap String String) (_seed : UInt64) :
    IO Unit := do
  let bitsList : Array Nat := match cfg["bits"]? with
    | some s =>
      ((s.splitOn "/").filterMap (fun t : String => t.trimAscii.toString.toNat?)).toArray
    | none => #[53, 200, 1000]
  let xs : List String := match cfg["xs"]? with
    | some s => (s.splitOn ";").map fun t => t.trimAscii.toString
    | none => ["1/3", "3/2", "21/2", "150", "2001/2", "3000001/3",
      "1/1000000000000000000000000000000", "1099511627777/1099511627776",
      "-1/3", "-201/2", "-3000001/3", "-1099511627777/1099511627776"]
  IO.println "[AzFloat-Gamma] ms per call (median of 3 passes)"
  IO.println (padL "bits" 6 ++ padL "x" 12 ++ padL "Gamma" 10 ++ padL "1/Gamma" 10
    ++ padL "GammaRat" 10 ++ padL "lnGamma" 10 ++ padL "lnGammaRat" 11 ++ padL "exp" 10)
  for P in bitsList do
    for xs' in xs do
      let q := (AzRat.parse xs').get!
      let x := ofAzRat q (max P 64)
      let nsG ← timeMed (fun _ => gammaPrecRound x P .Nearest) (fun r => fsz r.1)
      let nsR ← timeMed (fun _ => reciprocalGammaPrecRound x P .Nearest) (fun r => fsz r.1)
      let nsQG ← timeMed (fun _ => gammaRatPrecRound q P .Nearest) (fun r => fsz r.1)
      let nsE ← timeMed (fun _ => expPrecRound x P .Nearest) (fun r => fsz r.1)
      let (sL, sQ) ← if q.sign && q.num != 0 then do
          let nsL ← timeMed (fun _ => lnGammaPrecRound x P .Nearest) (fun r => fsz r.1)
          let nsQ ← timeMed (fun _ => lnGammaRatPrecRound q P .Nearest) (fun r => fsz r.1)
          pure (msStr nsL, msStr nsQ)
        else pure ("-", "-")
      IO.println (padL s!"{P}" 6 ++ padL (xs'.take 11).toString 12 ++ padL (msStr nsG) 10
        ++ padL (msStr nsR) 10 ++ padL (msStr nsQG) 10 ++ padL sL 10 ++ padL sQ 11
        ++ padL (msStr nsE) 10)

end Azurite.Benchmark
