import Azurite.Random.AzPolynomial
import Azurite.AzPolynomial.Mul
import Azurite.AzPolynomial.ToString
import Azurite.Benchmark.RatCmp -- reuse timeNsIter, median3, configGetRat, configGetNat

open Azurite Azurite.Random Azurite.Benchmark Azurite.AzPolynomial

-- ── Input-size metric ───────────────────────────────────────────────────────

/-- Sum of (log2 + 1) over all coefficients — matches the Rust AzPolynomial::significant_bits. -/
def azPolynomialNatSignificantBits (p : AzPolynomial ℕ) : Nat :=
  p.coeffs.foldl (fun acc c => acc + if c = 0 then 0 else c.log2 + 1) 0

-- ── Benchmark ───────────────────────────────────────────────────────────────

/--
Run the `az_polynomial_mul` benchmark.
For each of `limit` pairs `(a, b)` of random `AzPolynomial ℕ`, time:
  - `mulBasecaseList a b`  (List.range.map.sum)
  - `mulBasecase a b`      (Finset.sum)
  - `mulBasecaseFold a b`  (Fin.foldl)

Output format (one line per pair, semicolon-separated key:value pairs after the bucket):
  `<sb>;mulBasecaseList,<ns>;mulBasecase,<ns>;mulBasecaseFold,<ns>`
-/
def runAzPolynomialMul (limit : Nat) (cfg : Std.HashMap String String) (seed : UInt64) : IO Unit := do
  let meanDegree := configGetRat cfg "meanDegree" 8
  let meanCoeffBitLength := configGetRat cfg "meanCoeffBitLength" 32
  let iters := configGetNat cfg "iters" 100
  let mut g := mkAzPolynomialNatRandomGen meanDegree meanCoeffBitLength seed
  for _ in List.range limit do
    let (a, g') := AzPolynomialRandomGen.next g
    let (b, g'') := AzPolynomialRandomGen.next g'
    let sb := azPolynomialNatSignificantBits a + azPolynomialNatSignificantBits b
    -- mulBasecaseList
    let (r1, ns1a) ← timeNsIter iters (fun _ => mulBasecaseList a b)
    let (_, ns1b) ← timeNsIter iters (fun _ => mulBasecaseList a b)
    let (_, ns1c) ← timeNsIter iters (fun _ => mulBasecaseList a b)
    let ns1 := median3 ns1a ns1b ns1c
    -- mulBasecase (Finset.sum)
    let (r2, ns2a) ← timeNsIter iters (fun _ => mulBasecase a b)
    let (_, ns2b) ← timeNsIter iters (fun _ => mulBasecase a b)
    let (_, ns2c) ← timeNsIter iters (fun _ => mulBasecase a b)
    let ns2 := median3 ns2a ns2b ns2c
    -- mulBasecaseFold (Fin.foldl)
    let (r3, ns3a) ← timeNsIter iters (fun _ => mulBasecaseFold a b)
    let (_, ns3b) ← timeNsIter iters (fun _ => mulBasecaseFold a b)
    let (_, ns3c) ← timeNsIter iters (fun _ => mulBasecaseFold a b)
    let ns3 := median3 ns3a ns3b ns3c
    -- Sanity check
    if r1 ≠ r2 then
      IO.eprintln s!"BUG: mulBasecaseList ≠ mulBasecase"
    if r1 ≠ r3 then
      IO.eprintln s!"BUG: mulBasecaseList ≠ mulBasecaseFold"
    IO.println s!"{sb};mulBasecaseList,{ns1};mulBasecase,{ns2};mulBasecaseFold,{ns3}"
    g := g''
