/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzNat.PerfectPower
import Azurite.Benchmark.Common

open Azurite Azurite.Benchmark

/-!
# Perfect-power detection: timing

`benchmark perfect_power <limit>` compares `AzNat.isPerfectPower` (2-adic roots) with the
test by `isPow` for every prime exponent below the bit length (`byRoots`), on odd numbers of
several sizes that are not perfect powers (the usual input), on numbers `2^e m`, and on
perfect powers.  `limit` is the largest bit length tried (default 100000 when `0`);
`limit = 10^9 + b` instead prints where the time goes for an odd non-power of `b` bits.
-/

namespace Azurite.Benchmark.PerfectPower

private def ms (ns : UInt64) : String :=
  let m := ns / 1000000
  let f := (ns / 1000) % 1000
  s!"{m}.{if f < 100 then "0" else ""}{if f < 10 then "0" else ""}{f}"

/-- The perfect-power test with one integer root per prime exponent. -/
def byRoots (n : AzNat) : Bool :=
  decide (n.size ≤ 1) || (AzNat.primesUpTo n.size).any fun p => AzNat.isPow n p

/-- An odd number of `bits` bits with no pattern. -/
def sample (bits seed : Nat) : AzNat :=
  let big := AzNat.pow (AzNat.ofNat (1000003 + 2 * seed)) (bits / 20 + 1)
  (big.modPow2 (bits - 1) + (AzNat.ofNat 1 <<< (bits - 1))) + AzNat.ofNat (1 - big.toNat % 2)

def line (name : String) (n : AzNat) (slow : Bool) : IO Unit := do
  let (a, tA) ← timeNsIter 1 fun _ => AzNat.isPerfectPower n
  if slow then
    let (b, tB) ← timeNsIter 1 fun _ => byRoots n
    IO.println s!"{name} ({n.size} bits): 2-adic {ms tA}ms ({a}), by roots {ms tB}ms ({b})"
  else
    IO.println s!"{name} ({n.size} bits): 2-adic {ms tA}ms ({a})"

/-- Where the time of an odd non-power goes: the hint `y`, and the root tests by ranges of
the exponent (with the number of candidates that failed their check). -/
def parts (bits : Nat) : IO Unit := do
  let m := sample bits 0
  let f := m.size
  let (y, tY) ← timeNsIter 1 fun _ => AzNat.invModPow2Hint m ((f + 2) / 3)
  IO.println s!"{bits} bits: inverse hint {ms tY}ms"
  let primes := (AzNat.primesUpTo f).toList
  for (lo, hi) in [(2, 3), (3, 4), (4, 8), (8, 32), (32, f / 32), (f / 32, f + 1)] do
    let ps := primes.filter fun p => lo ≤ p && p < hi
    let (c, t) ← timeNsIter 1 fun _ =>
      (ps.filter fun p => (AzNat.primeRoot? m y p).isSome).length
    let bad := (ps.filter fun p =>
      let b := (f + p - 1) / p
      p % 2 = 1 && 2 * b > 64 &&
        (AzNat.powModPow2 ((AzNat.rootHint y (AzNat.invModPow2Hint (AzNat.ofNat p) b) p
          b).modPow2 b) b p) != m.modPow2 b).length
    IO.println s!"   exponents in [{lo}, {hi}): {ps.length} primes, {ms t}ms ({c} roots, \
      {bad} wrong candidates)"

def run (limit : Nat) : IO Unit := do
  if limit ≥ 1000000000 then
    parts (limit - 1000000000)
    return
  let top := if limit = 0 then 100000 else limit
  for bits in [64, 128, 256, 512, 1024, 2048, 4096, 10000, 30000, 100000, 300000, 1000000] do
    if bits > top then break
    let slow := bits ≤ 30000
    let n := sample bits 0
    line "odd, not a power" n slow
    line "times 2^30, not a power" (n <<< 30) slow
    let r := sample (bits / 7 + 2) 1
    line "a 7th power" (r.pow 7) slow
    let s := sample (bits / 2 + 2) 2
    line "a square" (s.pow 2) slow

end Azurite.Benchmark.PerfectPower
