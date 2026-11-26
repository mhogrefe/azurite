/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzPolynomial.Factorization
import Azurite.Benchmark.Common
import Mathlib.Tactic.NormNum.Prime

open Azurite Azurite.AzPolynomial Azurite.Benchmark

/-!
# Factorization over a prime field: timing

`benchmark poly_factor <limit>` factors monic polynomials of degree 8, 16, 32, 64 (up to
`"maxdeg:D"`) over `𝔽_p` for `p = 1000003` and `p = 1000000007` with
`AzPolynomial.factorization`, and times next to it the pieces of one round of its loop: the
power `h^p mod f`, the gcd `gcd(h − X, f)` and the exact division by the gcd.  `limit` is
the number of polynomials per degree.  Milliseconds.
-/

namespace Azurite.Benchmark.PolyFactor

def ms (ns : UInt64) : String :=
  let m := ns / 1000000
  let f := (ns / 10000) % 100
  s!"{m}.{if f < 10 then "0" else ""}{f}"

def timeOne {α : Type} (f : Unit → α) : IO (α × UInt64) := timeNsIter 1 f

instance fact1000003 : Fact (Nat.Prime (AzNat.ofNat 1000003).toNat) :=
  ⟨by rw [AzNat.toNat_ofNat]; norm_num⟩

set_option maxRecDepth 100000 in
instance fact1000000007 : Fact (Nat.Prime (AzNat.ofNat 1000000007).toNat) :=
  ⟨by rw [AzNat.toNat_ofNat]; norm_num⟩

/-- A deterministic monic polynomial of degree `d` over `𝔽_p`. -/
def testMonic (p : AzNat) [Fact (Nat.Prime p.toNat)] (d seed : Nat) : AzPolynomial (AzZMod p) :=
  monomial d 1 + normalize ((Array.range d).map fun i =>
    AzZMod.ofAzNat p (AzNat.ofNat ((1000003 + seed) ^ (i % 5 + 2) + i * i * 7919 + seed)))

def runOne (p : AzNat) [Fact (Nat.Prime p.toNat)]
    [LinearOrder (AzZMod p)] [ExhaustiveGenerator (AzZMod p)] [FiniteGenerator (AzZMod p)]
    [ExhaustiveGenerator {t : AzZMod p // t ≠ 0}]
    [∀ m : ℕ, ExhaustiveGenerator (List.Vector (AzZMod p) (m + 1) × {t : AzZMod p // t ≠ 0})]
    (limit maxDeg : Nat) : IO Unit := do
  IO.println s!"p = {p.toNat} (ms: factorization | one power h^p mod f, one gcd(h - X, f), one division)"
  for d in [8, 16, 32, 64, 128] do
    if d > maxDeg then continue
    for seed in [1:limit + 1] do
      let f := testMonic p d seed
      let (fs, tF) ← timeOne fun _ => factorization p f 0
      let (h, tP) ← timeOne fun _ => powModByMonic (X : AzPolynomial (AzZMod p)) p f
      let (g, tG) ← timeOne fun _ => gcdMonic (h - X) f
      let (_, tD) ← timeOne fun _ => divByMonic f g
      let degs := fs.map fun x => (x.1.natDegree, x.2)
      IO.println s!"   deg {d}: {ms tF} | {ms tP}, {ms tG}, {ms tD}   factors (degree, multiplicity): {degs}"

def run (limit : Nat) (cfg : Std.HashMap String String) : IO Unit := do
  let maxDeg := configGetNat cfg "maxdeg" 64
  runOne (AzNat.ofNat 1000003) (max limit 1) maxDeg
  runOne (AzNat.ofNat 1000000007) (max limit 1) maxDeg

end Azurite.Benchmark.PolyFactor
