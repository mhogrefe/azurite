/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Ln
import Azurite.AzFloat.Ln2
import Azurite.AzFloat.Pi
import Azurite.AzFloat.Sqrt
import Azurite.AzNat.Gcd
import Azurite.AzRat.Parse
import Azurite.Benchmark.Common

/-!
# `ln` of an `AzFloat`: where the time goes

`az_float_ln`: for each precision `P` (bits), the time of `ln x` (nearest, Ziv loop from
`w = P + 64`), and the pieces of one bracket at `w = P + 64`: the whole `lnBracket`, the
interval AGM alone (`agmIterN` from the bracket of `k`), `piBracket w`, `ln2Bracket w`
(rational), and for reference `sqrt`, `pi P` and `ln2 P`.  Milliseconds.

`az_float_ln2_breakdown`: the pieces of `ln2Bracket w` — the three binary splittings, the three
series brackets (`seriesBracket`: truncations and two directed divisions each), the whole bracket
(the float combination more), and, for the record, the GCD of the first fraction that the former
`AzRat` bracket had to reduce, with the operand sizes in bits.
-/

open Azurite Azurite.AzFloat Azurite.Benchmark

namespace Azurite.Benchmark

private def padLeft (s : String) (w : Nat) : String :=
  "".pushn ' ' (w - s.length) ++ s

/-- Total ns of `f` over all `xs`, median of three passes (checksum keeps the results alive). -/
@[noinline] private def timeOver {β α : Type} (xs : Array β) (f : β → α) (size : α → Nat) :
    IO UInt64 := do
  let pass : IO UInt64 := do
    let t0 ← monoNanos
    let mut acc : Nat := 0
    for x in xs do
      acc := acc + size (f x)
    let t1 ← monoNanos
    if acc = 0 then IO.eprintln "(zero checksum)"
    return t1 - t0
  let a ← pass
  let b ← pass
  let c ← pass
  return median3 a b c

private def ms (ns : UInt64) (count : Nat) : String :=
  let us := ns.toNat / count / 1000
  s!"{us / 1000}.{padLeft (toString (us % 1000)) 3 |>.replace " " "0"}"

/-- The interval AGM of `lnBracket` alone, from the bracket of `k = 4/y`. -/
private def agmOnly (x : AzFloat) (w : Nat) : AgmBounds :=
  let h := lnH w
  let e := x.exponent?.getD 0
  let l : AzInt := (AzNat.ofNat (2 * h + 2)).toAzInt - e
  let y := x <<< l
  let kLo := (divPrecRound (one <<< (2 : Nat)) y w .Floor).1
  let kHi := (divPrecRound (one <<< (2 : Nat)) y w .Ceiling).1
  agmIterN w (lnSteps w) ⟨one, one, kLo, kHi⟩

private def fsize (x : AzFloat) : Nat := x.precision?.getD 0

/-- Run the `az_float_ln` benchmark.  Config: `bits` (`/`-separated precisions, default
`53/1000/10000/100000`), `inputs` (the first `inputs` of `10, 3, 1/2, 3/2, 10^12, 7`, default
`4`). -/
def runAzFloatLn (_limit : Nat) (cfg : Std.HashMap String String) (_seed : UInt64) :
    IO Unit := do
  let bitsList := match cfg["bits"]? with
    | some s =>
      ((s.splitOn "/").filterMap (fun t : String => t.trimAscii.toString.toNat?)).toArray
    | none => #[53, 1000, 10000, 100000]
  let count := configGetNat cfg "inputs" 4
  let srcs : Array String := #["10", "3", "1/2", "3/2", "1000000000000", "7"]
  IO.println s!"[AzFloat-Ln] ms per call (median of 3 passes over {count} inputs: \
    ln 10, ln 3, ln ½, …); bracket pieces at w = P + 64"
  IO.println (padLeft "bits" 7 ++ padLeft "ln" 10 ++ padLeft "lnBracket" 10 ++ padLeft "agm" 10
    ++ padLeft "piBracket" 10 ++ padLeft "ln2Bracket" 11 ++ padLeft "sqrt" 10 ++ padLeft "pi" 10
    ++ padLeft "ln2" 10)
  for P in bitsList do
    let w := P + zivGuardBits
    let xs : Array AzFloat := (srcs.extract 0 (min count srcs.size)).map fun s =>
      ofAzRat ((AzRat.parse s).get!) P
    let nsLn ← timeOver xs ln fsize
    let nsBr ← timeOver xs (fun x => lnBracket x (x.exponent?.getD 0) w) (fun p => fsize p.1)
    let nsAgm ← timeOver xs (fun x => agmOnly x w) (fun s => fsize s.aHi)
    let ws : Array Nat := xs.map fun _ => w
    let nsPi ← timeOver ws piBracket (fun p => fsize p.1)
    let nsLn2 ← timeOver ws ln2Bracket (fun p => fsize p.1)
    let nsSqrt ← timeOver xs sqrt fsize
    let ps : Array Nat := xs.map fun _ => P
    let nsPiC ← timeOver ps pi fsize
    let nsLn2C ← timeOver ps ln2 fsize
    IO.println (padLeft s!"{P}" 7 ++ padLeft (ms nsLn count) 10 ++ padLeft (ms nsBr count) 10
      ++ padLeft (ms nsAgm count) 10 ++ padLeft (ms nsPi count) 10 ++ padLeft (ms nsLn2 count) 11
      ++ padLeft (ms nsSqrt count) 10 ++ padLeft (ms nsPiC count) 10
      ++ padLeft (ms nsLn2C count) 10)

/-- Run the `az_float_ln2_breakdown` benchmark: the pieces of `ln2Bracket w` at `w = P + 64`.
Config: `bits` (default `1000/5000/20000`). -/
def runAzFloatLn2Breakdown (_limit : Nat) (cfg : Std.HashMap String String) (_seed : UInt64) :
    IO Unit := do
  let bitsList := match cfg["bits"]? with
    | some s =>
      ((s.splitOn "/").filterMap (fun t : String => t.trimAscii.toString.toNat?)).toArray
    | none => #[1000, 5000, 20000]
  IO.println "[AzFloat-Ln2-breakdown] ms per call (median of 3); w = P + 64"
  IO.println (padLeft "bits" 7 ++ padLeft "split26" 10 ++ padLeft "split4801" 10
    ++ padLeft "split8749" 10 ++ padLeft "series3" 10 ++ padLeft "bracket" 10
    ++ padLeft "gcd26" 10 ++ padLeft "numBits" 10 ++ padLeft "denBits" 10)
  for P in bitsList do
    let w := P + zivGuardBits
    let ws : Array Nat := #[w]
    let ns1 ← timeOver ws (fun w => AzNat.atanhNumDen 26 (ln2N₁ w)) (fun r => r.1.limbs.size)
    let ns2 ← timeOver ws (fun w => AzNat.atanhNumDen 4801 (ln2N₂ w)) (fun r => r.1.limbs.size)
    let ns3 ← timeOver ws (fun w => AzNat.atanhNumDen 8749 (ln2N₃ w)) (fun r => r.1.limbs.size)
    let nsF ← timeOver ws (fun w =>
      (seriesBracket (AzNat.atanhNumDen 26 (ln2N₁ w)) (w + 8),
        seriesBracket (AzNat.atanhNumDen 4801 (ln2N₂ w)) (w + 8),
        seriesBracket (AzNat.atanhNumDen 8749 (ln2N₃ w)) (w + 8))) (fun b => fsize b.1.1)
    let nsB ← timeOver ws ln2Bracket (fun b => fsize b.1)
    let r1 := AzNat.atanhNumDen 26 (ln2N₁ w)
    let nsG ← timeOver #[r1] (fun r => AzNat.gcd r.1 r.2) (fun g => g.limbs.size)
    IO.println (padLeft s!"{P}" 7 ++ padLeft (ms ns1 1) 10 ++ padLeft (ms ns2 1) 10
      ++ padLeft (ms ns3 1) 10 ++ padLeft (ms nsF 1) 10 ++ padLeft (ms nsB 1) 10
      ++ padLeft (ms nsG 1) 10 ++ padLeft s!"{r1.1.limbs.size * 64}" 10
      ++ padLeft s!"{r1.2.limbs.size * 64}" 10)

end Azurite.Benchmark
