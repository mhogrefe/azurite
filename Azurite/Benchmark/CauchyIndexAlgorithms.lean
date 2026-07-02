import Azurite.Random.AzPolynomial
import Azurite.AzPolynomial.CauchyIndex
import Azurite.AzInt.Size
import Azurite.Benchmark.Common -- timeNsIter, median3, configGetRat, configGetNat
import Azurite.Benchmark.AzPolynomialKaratsuba -- azPolynomialIntSignificantBits

open Azurite Azurite.Random Azurite.Benchmark Azurite.AzPolynomial

-- ── Benchmark ───────────────────────────────────────────────────────────────

/--
Run the `cauchy_index_algorithms` benchmark.

For each of `limit` random pairs `(Q, P)` of `AzPolynomial AzInt` with a
nonconstant denominator (`deg P ≥ 1`), compute the whole-line Cauchy index
`Ind(Q/P) : ℤ` two ways and time each:

  - `Subresultant`    — `cauchyIndex Q P` (BPR Algorithm 9.4): signed
    subresultant sequence + `PmV`, fraction-free, all arithmetic in `AzInt`.
  - `SignedRemainder` — `cauchyIndexOnIntSRem Q P (-∞) (+∞)`: signed remainder
    sequence, which lifts the coefficients to `AzRat` (rational arithmetic).

Both compute the same integer; a mismatch prints a `BUG:` line to stderr.

The signed remainder sequence over `AzRat` suffers the classic intermediate
coefficient swell — its cost grows super-exponentially in the degree — so we cap
each input degree at `maxDegree` (skipping larger draws). Without the cap a single
high-degree pair can take minutes, dwarfing the rest of the sweep.

Output (one line per pair, semicolon-separated):
  `<sb>;Subresultant,<ns>;SignedRemainder,<ns>`
where `<sb> = significantBits(P) + significantBits(Q)`.
-/
def runCauchyIndexAlgorithms (limit : Nat) (cfg : Std.HashMap String String)
    (seed : UInt64) : IO Unit := do
  let meanDegree := configGetRat cfg "meanDegree" 5
  let meanCoeffBitLength := configGetRat cfg "meanCoeffBitLength" 12
  let maxDegree := configGetNat cfg "maxDegree" 8
  let iters := configGetNat cfg "iters" 1
  let mut g := mkAzPolynomialAzIntRandomGen meanDegree meanCoeffBitLength seed
  for _ in List.range limit do
    let (q, g') := AzPolynomialRandomGen.next g
    let (p, g'') := AzPolynomialRandomGen.next g'
    g := g''
    -- Need a nonconstant denominator `P ≠ 0`; cap degrees so the signed
    -- remainder sequence over `AzRat` stays tractable.
    if p.natDegree < 1 || p.natDegree > maxDegree || q.natDegree > maxDegree then
      continue
    let sb := azPolynomialIntSignificantBits p + azPolynomialIntSignificantBits q
    -- Subresultant (BPR Algorithm 9.4), fraction-free over `AzInt`.
    let (r1, ns1a) ← timeNsIter iters (fun _ => cauchyIndex q p)
    let (_, ns1b) ← timeNsIter iters (fun _ => cauchyIndex q p)
    let (_, ns1c) ← timeNsIter iters (fun _ => cauchyIndex q p)
    let ns1 := median3 ns1a ns1b ns1c
    -- Signed remainder sequence over `AzRat`.
    let (r2, ns2a) ← timeNsIter iters (fun _ => cauchyIndexOnIntSRem q p .negInf .posInf)
    let (_, ns2b) ← timeNsIter iters (fun _ => cauchyIndexOnIntSRem q p .negInf .posInf)
    let (_, ns2c) ← timeNsIter iters (fun _ => cauchyIndexOnIntSRem q p .negInf .posInf)
    let ns2 := median3 ns2a ns2b ns2c
    -- Sanity check: the two implementations must agree.
    if r1 ≠ r2 then
      IO.eprintln s!"BUG: cauchyIndex ≠ cauchyIndexOnIntSRem at sb={sb}: {r1} vs {r2}"
    IO.println s!"{sb};Subresultant,{ns1};SignedRemainder,{ns2}"
