/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.Random.AzPolynomial
import Azurite.AzPolynomial.Karatsuba
import Azurite.AzPolynomial.ToString
import Azurite.AzInt.Size
import Azurite.Benchmark.Common -- reuse timeNsIter, median3, configGetRat, configGetNat

open Azurite Azurite.Random Azurite.Benchmark Azurite.AzPolynomial

-- ── Input-size metric ───────────────────────────────────────────────────────

/-- Sum of bit-lengths over all coefficients — significant bits for `AzInt`. -/
def azPolynomialIntSignificantBits (p : AzPolynomial AzInt) : Nat :=
  p.coeffs.foldl (fun acc c => acc + c.size) 0

-- ── Benchmark ───────────────────────────────────────────────────────────────

/--
Run the `az_polynomial_karatsuba` benchmark.
For each of `limit` pairs `(a, b)` of random `AzPolynomial AzInt`, time:
  - `mulBasecaseFold a b`  (O(n^2) Fin.foldl)
  - `mulKaratsuba a b`     (O(n^1.585) Karatsuba)

Asserts equality of outputs for empirical correctness testing.

Output format:
  `<sb>;mulBasecaseFold,<ns>;mulKaratsuba,<ns>`
-/
def runAzPolynomialKaratsuba (limit : Nat) (cfg : Std.HashMap String String) (seed : UInt64) : IO Unit := do
  let meanDegree := configGetRat cfg "meanDegree" 8
  let meanCoeffBitLength := configGetRat cfg "meanCoeffBitLength" 32
  let iters := configGetNat cfg "iters" 100
  let mut g := mkAzPolynomialAzIntRandomGen meanDegree meanCoeffBitLength seed
  for _ in List.range limit do
    let (a, g') := AzPolynomialRandomGen.next g
    let (b, g'') := AzPolynomialRandomGen.next g'
    let sb := azPolynomialIntSignificantBits a + azPolynomialIntSignificantBits b
    -- mulBasecaseFold
    let (r1, ns1a) ← timeNsIter iters (fun _ => mulBasecaseFold a b)
    let (_, ns1b) ← timeNsIter iters (fun _ => mulBasecaseFold a b)
    let (_, ns1c) ← timeNsIter iters (fun _ => mulBasecaseFold a b)
    let ns1 := median3 ns1a ns1b ns1c
    -- mulKaratsuba
    let (r2, ns2a) ← timeNsIter iters (fun _ => mulKaratsuba a b)
    let (_, ns2b) ← timeNsIter iters (fun _ => mulKaratsuba a b)
    let (_, ns2c) ← timeNsIter iters (fun _ => mulKaratsuba a b)
    let ns2 := median3 ns2a ns2b ns2c
    -- Equality assertion
    if r1 ≠ r2 then
      IO.eprintln s!"BUG: mulBasecaseFold ≠ mulKaratsuba for inputs:"
      IO.eprintln s!"  a = {a}"
      IO.eprintln s!"  b = {b}"
      IO.eprintln s!"  mulBasecaseFold = {r1}"
      IO.eprintln s!"  mulKaratsuba    = {r2}"
    IO.println s!"{sb};mulBasecaseFold,{ns1};mulKaratsuba,{ns2}"
    g := g''
