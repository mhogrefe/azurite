/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.LnGamma
import Azurite.AzFloat.Ln
import Azurite.AzFloat.Conversion
import Azurite.AzRat.Parse
import Azurite.Benchmark.Common

/-!
# `ln Γ`: where the time goes

`az_float_ln_gamma`: for each precision `P` (bits) and each argument, the time of
`lnGammaPrecRound x P` (nearest) and the pieces of one bracket at the first working precision
`w`: the table of tangent numbers (`tang`), the rising product (`prod`), with the shift `δ`,
the number of tangent numbers `M`, the width of the bracket in bits below `2^(−w)` relative to
the value (`slack`), and `ln x` at `P` bits for reference.  Milliseconds.  Config: `bits`
(default `53/200/1000`), `xs` (default `1/3;3/2;10;1000;10^30`, `;`-separated rationals).
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

/-- Run the `az_float_ln_gamma` benchmark. -/
def runAzFloatLnGamma (_limit : Nat) (cfg : Std.HashMap String String) (_seed : UInt64) :
    IO Unit := do
  let bitsList : Array Nat := match cfg["bits"]? with
    | some s =>
      ((s.splitOn "/").filterMap (fun t : String => t.trimAscii.toString.toNat?)).toArray
    | none => #[53, 200, 1000]
  let xs : List String := match cfg["xs"]? with
    | some s => (s.splitOn ";").map fun t => t.trimAscii.toString
    | none => ["1/3", "3/2", "10", "1000", "1000000000000000000000000000000"]
  IO.println "[AzFloat-LnGamma] ms per call (median of 3 passes); pieces at the first w"
  IO.println (padL "bits" 6 ++ padL "x" 10 ++ padL "w" 7 ++ padL "shift" 7 ++ padL "M" 6
    ++ padL "lnGamma" 10 ++ padL "tang" 10 ++ padL "prod" 10 ++ padL "slack" 7 ++ padL "ln x" 10)
  for P in bitsList do
    for xs' in xs do
      let x := ofAzRat ((AzRat.parse xs').get!) (max P 64)
      match x with
      | .finite _ e q _ _ =>
        let w := max 64 (P + 32 + lnGammaCancelBits x q)
        let L := lnGammaShiftExp w
        let V := w + 2 * L + 8 + 2 * w.log2
        let sh := lnGammaShift x e L
        let E := max (L + 1) (if e.sign then e.abs.toNat else 0)
        let M := lnGammaTerms w E
        let nsG ← timeMed (fun _ => lnGammaPrecRound x P .Nearest) (fun r => fsz r.1)
        let nsT ← timeMed (fun _ => AzNat.tangentNumbers M) (fun t => t.size + 1)
        let nsP ← timeMed (fun _ => risingEncl V (Encl.exact x) sh) (fun b => fsz b.1)
        let nsL ← timeMed (fun _ => lnPrecRound x P .Nearest) (fun r => fsz r.1)
        let b := lnGammaBracket x e w
        let wd := (subPrecRound b.2 b.1 32 .Ceiling).1
        let slack : Int := match wd.exponent?, b.2.exponent? with
          | some a, some c => (c - a).toInt64.toInt - (w : Int)
          | _, _ => 0
        IO.println (padL s!"{P}" 6 ++ padL (xs'.take 9).toString 10 ++ padL s!"{w}" 7
          ++ padL s!"{sh}" 7 ++ padL s!"{M}" 6 ++ padL (msStr nsG) 10 ++ padL (msStr nsT) 10
          ++ padL (msStr nsP) 10 ++ padL s!"{slack}" 7 ++ padL (msStr nsL) 10)
      | _ => pure ()

end Azurite.Benchmark
