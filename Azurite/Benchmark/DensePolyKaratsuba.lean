import Azurite.Random
import Azurite.DensePoly.Karatsuba
import Azurite.DensePoly.ToString
import Azurite.Benchmark.RatCmp  -- reuse timeNsIter, median3, configGetRat, configGetNat

open Azurite Azurite.Random Azurite.Benchmark Azurite.DensePoly

-- ── Input-size metric ───────────────────────────────────────────────────────

/-- Sum of (log2(|c|) + 1) over all coefficients — significant bits for ℤ. -/
def densePolyIntSignificantBits (p : DensePoly ℤ) : Nat :=
  p.coeffs.foldl (fun acc c =>
    acc + if c = 0 then 0 else c.natAbs.log2 + 1) 0

-- ── Benchmark ───────────────────────────────────────────────────────────────

/--
Run the `dense_poly_karatsuba` benchmark.
For each of `limit` pairs `(a, b)` of random `DensePoly ℤ`, time:
  - `mulBasecaseFold a b`  (O(n^2) Fin.foldl)
  - `mulKaratsuba a b`     (O(n^1.585) Karatsuba)

Asserts equality of outputs for empirical correctness testing.

Output format:
  `<sb>;mulBasecaseFold,<ns>;mulKaratsuba,<ns>`
-/
def runDensePolyKaratsuba (limit : Nat) (cfg : Std.HashMap String String) (seed : UInt64) : IO Unit := do
  let meanDegree := configGetRat cfg "meanDegree" 8
  let meanCoeffBitLength := configGetRat cfg "meanCoeffBitLength" 32
  let iters := configGetNat cfg "iters" 100
  let mut g := mkDensePolyIntRandomGen meanDegree meanCoeffBitLength seed
  for _ in List.range limit do
    let (a, g') := DensePolyRandomGen.next g
    let (b, g'') := DensePolyRandomGen.next g'
    let sb := densePolyIntSignificantBits a + densePolyIntSignificantBits b
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
