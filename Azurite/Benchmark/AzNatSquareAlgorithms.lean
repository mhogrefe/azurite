import Azurite.Random.NatGen
import Azurite.AzNat.Square
import Azurite.AzNat.Equiv.Basic
import Azurite.Benchmark.AzNatAdd -- reuse natSignificantBits
import Azurite.Benchmark.Common   -- reuse timeNsIter, median3, configGetRat, configGetNat

open Azurite Azurite.Random Azurite.Benchmark

/--
Run the `az_nat_square_algorithms` benchmark.
For each of `limit` random `Nat`s (sampled with geometric bit-length
distribution of mean `meanBitLength`), time `a²` two ways:
  - `squareSchoolbook a`        — uses `schoolbookSquareLimbs` (O(n²) wideMuls)
  - `squareKaratsuba threshold a` — uses `karatsubaSquareLimbs` (O(n^log₂3))

Both are checked against each other at runtime; any disagreement is
reported to stderr.

Output format (one line per input):
  `<bits>;Schoolbook,<ns>;Karatsuba,<ns>`
where `<bits>` is the significant-bit count of `a`.

Config keys:
  - `meanBitLength` (Rat, default 65536) — geometric mean of bit length.
  - `iters` (Nat, default 100) — inner-loop iterations per timing sample.
  - `threshold` (Nat, default 32) — Karatsuba schoolbook-fallback threshold
    (in 64-bit limbs).
-/
def runAzNatSquareAlgorithms (limit : Nat) (cfg : Std.HashMap String String)
    (seed : UInt64) : IO Unit := do
  let meanBitLength := configGetRat cfg "meanBitLength" 65536
  let iters := configGetNat cfg "iters" 100
  let threshold := configGetNat cfg "threshold" 32
  let mut g := mkNatRandomGen meanBitLength seed
  for _ in List.range limit do
    let (a, g') := NatRandomGen.next g
    let azA := Azurite.AzNat.ofNat a
    let bits := natSignificantBits a
    -- Schoolbook square
    let (rSch, ns1a) ← timeNsIter iters (fun _ => Azurite.AzNat.squareSchoolbook azA)
    let (_,    ns1b) ← timeNsIter iters (fun _ => Azurite.AzNat.squareSchoolbook azA)
    let (_,    ns1c) ← timeNsIter iters (fun _ => Azurite.AzNat.squareSchoolbook azA)
    let ns1 := median3 ns1a ns1b ns1c
    -- Karatsuba square
    let (rKar, ns2a) ← timeNsIter iters (fun _ => Azurite.AzNat.squareKaratsuba threshold azA)
    let (_,    ns2b) ← timeNsIter iters (fun _ => Azurite.AzNat.squareKaratsuba threshold azA)
    let (_,    ns2c) ← timeNsIter iters (fun _ => Azurite.AzNat.squareKaratsuba threshold azA)
    let ns2 := median3 ns2a ns2b ns2c
    if Azurite.AzNat.toNat rSch ≠ Azurite.AzNat.toNat rKar then
      IO.eprintln s!"BUG: schoolbook ≠ karatsuba squaring for a={a}"
    IO.println s!"{bits};Schoolbook,{ns1};Karatsuba,{ns2}"
    g := g'
