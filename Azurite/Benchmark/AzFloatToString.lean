/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

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

/-- Median-of-three timing of `f`, in ns, `iters` passes each. -/
private def med3 {α : Type} (iters : Nat) (f : Unit → α) : IO UInt64 := do
  let (_, a) ← timeNsIter iters f
  let (_, b) ← timeNsIter iters f
  let (_, c) ← timeNsIter iters f
  return median3 a b c

private def ms (ns : UInt64) (iters : Nat) : String :=
  let us := ns.toNat / iters / 1000
  s!"{us / 1000}.{padLeft (toString (us % 1000)) 3 |>.replace " " "0"}"

/-- Run the `az_float_to_string` benchmark.  Config: `bits` (`/`-separated precisions, default
`53/1000/10000/100000`), `iters` (default `3`). -/
def runAzFloatToString (_limit : Nat) (cfg : Std.HashMap String String) (_seed : UInt64) :
    IO Unit := do
  let bitsList := match cfg["bits"]? with
    | some s => ((s.splitOn "/").filterMap (fun t : String => t.trimAscii.toString.toNat?)).toArray
    | none => #[53, 1000, 10000, 100000]
  let iters := configGetNat cfg "iters" 3
  IO.println "[AzFloat-ToString] ms per call (median of 3); probe = one round-trip test at the \
    digit estimate"
  IO.println (padLeft "bits" 7 ++ padLeft "digits" 7 ++ padLeft "sqrt" 10 ++ padLeft "toString" 10
    ++ padLeft "old search" 11 ++ padLeft "toSci" 10 ++ padLeft "toAzRat" 10 ++ padLeft "ofAzRat" 10
    ++ padLeft "probes" 8)
  for P in bitsList do
    let two := ofAzRat ((AzRat.parse "2").get!) P
    let nsSqrt ← med3 iters (fun _ => sqrt two)
    let x := sqrt two
    let nsNew ← med3 iters (fun _ => toString x)
    let nsOld ← med3 iters (fun _ => oldToString x)
    let digits := shortestDecimalPrecision x
    let q := x.toAzRat?.get!
    let est := P * 30103 / 100000 + 2
    let nsSci ← med3 iters (fun _ => q.toSciNumber (decimalOptions est))
    match q.toSciNumber (decimalOptions est) with
    | none => IO.println s!"{P}: no SciNumber at {est} digits"
    | some sn =>
    let nsRat ← med3 iters (fun _ => sn.toAzRat)
    let r := sn.toAzRat
    let nsOf ← med3 iters (fun _ => ofAzRat r P)
    -- number of probes of the new search: count predicate evaluations
    let counter ← IO.mkRef 0
    let pred := fun p => decimalRoundTrips x q P p
    let _ ← pure (searchLeastFromTop pred 0 (expandUntil pred est 64))
    let probes := (est - digits) -- distance from the estimate, a proxy for the gallop length
    counter.set probes
    IO.println (padLeft s!"{P}" 7 ++ padLeft s!"{digits}" 7 ++ padLeft (ms nsSqrt iters) 10
      ++ padLeft (ms nsNew iters) 10 ++ padLeft (ms nsOld iters) 11 ++ padLeft (ms nsSci iters) 10
      ++ padLeft (ms nsRat iters) 10 ++ padLeft (ms nsOf iters) 10
      ++ padLeft s!"est-{probes}" 8)

end Azurite.Benchmark
