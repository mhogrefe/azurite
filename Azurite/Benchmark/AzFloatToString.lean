/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzFloat.Arith
import Azurite.AzFloat.ToString
import Azurite.AzRat.Parse
import Azurite.Benchmark.Common

/-!
# Decimal output of an `AzFloat`: where the time goes

`az_float_to_string`: for each precision `P` (bits), the time of `sqrt (F "2" P)`, of its
shortest-decimal rendering with the galloping search (`toString`), of the same rendering with a
plain bisection of `[1, hi]` (the previous search), and of the three steps of one round-trip
probe at the digit estimate: `toSciNumber`, `SciNumber.toAzRat` and `ofAzRat`.  Milliseconds.
-/

open Azurite Azurite.AzFloat Azurite.Benchmark

namespace Azurite.Benchmark

private def padLeft (s : String) (w : Nat) : String :=
  "".pushn ' ' (w - s.length) ++ s

/-- The previous search: bisection of `[1, hi]`. -/
private def oldShortestDecimalPrecision (x : AzFloat) : Nat :=
  match x.toAzRat?, x.precision? with
  | some q, some P =>
    let pred := decimalRoundTrips x q P
    let hi := expandUntil pred (P * 30103 / 100000 + 2) 64
    searchLeast pred 1 hi
  | _, _ => 0

private def oldToString (x : AzFloat) : String :=
  (toDecimalAt x (oldShortestDecimalPrecision x)).getD ""

/-- Total ns of `f` over all `xs` (each computed once per pass, kept alive by a checksum so nothing
is hoisted), median of three passes. -/
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

/-- Run the `az_float_to_string` benchmark.  Config: `bits` (`/`-separated precisions, default
`53/1000/10000/100000`), `inputs` (square roots of the first `inputs` primes, default `4`). -/
def runAzFloatToString (_limit : Nat) (cfg : Std.HashMap String String) (_seed : UInt64) :
    IO Unit := do
  let bitsList := match cfg["bits"]? with
    | some s => ((s.splitOn "/").filterMap (fun t : String => t.trimAscii.toString.toNat?)).toArray
    | none => #[53, 1000, 10000, 100000]
  let count := configGetNat cfg "inputs" 4
  let primes : Array Nat := #[2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37]
  IO.println s!"[AzFloat-ToString] ms per call (median of 3 passes over {count} inputs: √2, √3, \
    …); \
    probe = one round-trip test at the digit estimate"
  IO.println (padLeft "bits" 7 ++ padLeft "digits" 7 ++ padLeft "sqrt" 10 ++ padLeft "toString" 10
    ++ padLeft "old search" 11 ++ padLeft "toSci" 10 ++ padLeft "toAzRat" 10
    ++ padLeft "ofAzRat" 10)
  for P in bitsList do
    let ns : Array AzFloat := (primes.extract 0 (min count primes.size)).map fun n =>
      ofAzRat ((AzRat.parse (toString n)).get!) P
    let nsSqrt ← timeOver ns sqrt (·.precision?.getD 0)
    let xs := ns.map sqrt
    let nsNew ← timeOver xs toString (·.length)
    let nsOld ← timeOver xs oldToString (·.length)
    let digits := shortestDecimalPrecision xs[0]!
    let qs := xs.map fun x => x.toAzRat?.get!
    let est := P * 30103 / 100000 + 2
    let nsSci ← timeOver qs (fun q => q.toSciNumber (decimalOptions est))
      (fun o => if o.isSome then 1 else 2)
    let sns := qs.filterMap fun q => q.toSciNumber (decimalOptions est)
    let nsRat ← timeOver sns (fun sn => sn.toAzRat) (·.num.limbs.size)
    let rs := sns.map fun sn => sn.toAzRat
    let nsOf ← timeOver rs (fun r => ofAzRat r P) (·.precision?.getD 0)
    IO.println (padLeft s!"{P}" 7 ++ padLeft s!"{digits}" 7 ++ padLeft (ms nsSqrt count) 10
      ++ padLeft (ms nsNew count) 10 ++ padLeft (ms nsOld count) 11 ++ padLeft (ms nsSci count) 10
      ++ padLeft (ms nsRat count) 10 ++ padLeft (ms nsOf count) 10)

end Azurite.Benchmark
