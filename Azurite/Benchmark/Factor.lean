/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzNat.Factor
import Azurite.Benchmark.Common

open Azurite Azurite.Benchmark

/-!
# Integer factorization: timing

`benchmark factor <limit>`: `AzNat.factor` on products of two primes of `d` digits each, for
`d = 4, …, limit` (default 12 when `0`), three products per size; then on a few numbers of
other shapes.  One line per number: the time, and of it the time of the primality proofs of
the two factors.
-/

namespace Azurite.Benchmark.Factor

private def ms (ns : UInt64) : String :=
  let m := ns / 1000000
  let f := (ns / 1000) % 1000
  s!"{m}.{if f < 100 then "0" else ""}{if f < 10 then "0" else ""}{f}"

/-- The first prime from `m` on. -/
def nextPrime (m : AzNat) : AzNat := Id.run do
  let mut c := if m.isOdd then m else m + 1
  for _ in [0:100000] do
    if AzNat.isPrime c then return c
    c := c + AzNat.ofNat 2
  return c

def showFactors (l : List (AzNat × Nat)) : String :=
  " · ".intercalate (l.map fun (p, e) => if e = 1 then s!"{p}" else s!"{p}^{e}")

def line (name : String) (n : AzNat) : IO Unit := do
  let (f, t) ← timeNsIter 1 fun _ => AzNat.factor n
  let (_, tp) ← timeNsIter 1 fun _ => f.all fun pe => AzNat.isPrime pe.1
  IO.println s!"{name} ({n.size} bits): {ms t}ms (primality {ms tp}ms)  {showFactors f}"

def run (limit : Nat) : IO Unit := do
  let top := if limit = 0 then 12 else limit
  for d in [4:top + 1] do
    for j in [0:3] do
      let p := nextPrime (AzNat.pow (AzNat.ofNat 10) (d - 1) * AzNat.ofNat (2 + 3 * j) + 1)
      let q := nextPrime (AzNat.pow (AzNat.ofNat 10) (d - 1) * AzNat.ofNat (7 - 2 * j) + 1)
      line s!"{d}+{d} digits" (p * q)
  line "30!" ((List.range 30).foldl (fun acc i => acc * AzNat.ofNat (i + 1)) 1)
  line "10^40 + 1" (AzNat.pow (AzNat.ofNat 10) 40 + 1)
  line "2^101 - 1" (AzNat.pow (AzNat.ofNat 2) 101 - 1)
  line "2^64 + 1" (AzNat.pow (AzNat.ofNat 2) 64 + 1)
  line "(10^9 + 7)^5" (AzNat.pow (AzNat.ofNat 1000000007) 5)

end Azurite.Benchmark.Factor
