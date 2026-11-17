/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzRat.Bernoulli
import Azurite.Benchmark.Common

/-!
# Bernoulli numbers: the cost of the table

`az_rat_bernoulli`: for each `m`, the time of the tangent numbers `T_1, …, T_m`
(`AzNat.tangentNumbers m`) and of the whole table `B_2, …, B_{2m}` (`AzRat.bernoulliEvens m`,
which includes them), in milliseconds, with the bit length of `T_m`.  Config: `m` (default
`50/100/200/400/800`).
-/

open Azurite Azurite.Benchmark

namespace Azurite.Benchmark

/-- Run the `az_rat_bernoulli` benchmark. -/
def runAzRatBernoulli (_limit : Nat) (cfg : Std.HashMap String String) (_seed : UInt64) :
    IO Unit := do
  let ms : Array Nat := match cfg["m"]? with
    | some s =>
      ((s.splitOn "/").filterMap (fun t : String => t.trimAscii.toString.toNat?)).toArray
    | none => #[50, 100, 200, 400, 800]
  IO.println "[AzRat-Bernoulli] ms per call"
  for m in ms do
    let t0 ← monoNanos
    let T := AzNat.tangentNumbers m
    let bits := (T.getD (m - 1) 0).size
    let t1 ← monoNanos
    let Bs := AzRat.bernoulliEvens m
    let chk := (Bs.getD (m - 1) 0).den.size
    let t2 ← monoNanos
    IO.println (s!"  m = {m}: tangent numbers {(t1 - t0).toNat / 1000} µs (T_m: {bits} bits), "
      ++ s!"table {(t2 - t1).toNat / 1000} µs (denominator of B_2m: {chk} bits)")

end Azurite.Benchmark
