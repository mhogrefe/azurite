import Azurite.Random.NatGen
import Azurite.Random.Pair
import Azurite.AzNat.Add
import Azurite.AzNat.Equiv.Basic
import Azurite.Benchmark.Common -- reuse timeNsIter, median3, configGetRat, configGetNat

open Azurite Azurite.Random Azurite.Benchmark

-- ── Input-size metric ───────────────────────────────────────────────────────

/-- Significant bits of a `Nat` (`log2 n + 1`, with `0 ↦ 0`). -/
def natSignificantBits (n : Nat) : Nat :=
  if n = 0 then 0 else n.log2 + 1

-- ── Benchmark ───────────────────────────────────────────────────────────────

/--
Run the `az_nat_add` benchmark.
For each of `limit` pairs `(a, b)` of random `Nat`s (sampled with geometric
bit-length distribution of mean `meanBitLength`), time:
  - `a + b` on Lean's native `Nat`
  - `a' + b'` on `AzNat` (precomputed via `AzNat.ofNat`)

Output format (one line per pair):
  `<sb>;Nat,<ns>;AzNat,<ns>`
where `<sb>` is the sum of significant bits of the two operands.
-/
def runAzNatAdd (limit : Nat) (cfg : Std.HashMap String String) (seed : UInt64) : IO Unit := do
  let meanBitLength := configGetRat cfg "meanBitLength" 256
  let iters := configGetNat cfg "iters" 1000
  let gen := mkPairRandomGenFromSingle (α := Nat) (mkNatRandomGen meanBitLength seed)
  let mut g := gen
  for _ in List.range limit do
    let ((a, b), g') := PairRandomGenFromSingle.next g
    let azA := Azurite.AzNat.ofNat a
    let azB := Azurite.AzNat.ofNat b
    let sb := natSignificantBits a + natSignificantBits b
    -- Nat addition
    let (rNat, ns1a) ← timeNsIter iters (fun _ => a + b)
    let (_,    ns1b) ← timeNsIter iters (fun _ => a + b)
    let (_,    ns1c) ← timeNsIter iters (fun _ => a + b)
    let ns1 := median3 ns1a ns1b ns1c
    -- AzNat addition
    let (rAz, ns2a) ← timeNsIter iters (fun _ => azA + azB)
    let (_,   ns2b) ← timeNsIter iters (fun _ => azA + azB)
    let (_,   ns2c) ← timeNsIter iters (fun _ => azA + azB)
    let ns2 := median3 ns2a ns2b ns2c
    -- Sanity check: AzNat result must round-trip to the Nat result
    if Azurite.AzNat.toNat rAz ≠ rNat then
      IO.eprintln s!"BUG: AzNat add disagrees with Nat add for a={a}, b={b}"
    IO.println s!"{sb};Nat,{ns1};AzNat,{ns2}"
    g := g'
