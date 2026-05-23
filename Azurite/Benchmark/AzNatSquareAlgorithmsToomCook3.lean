import Azurite.Random.NatGen
import Azurite.AzNat.Square
import Azurite.AzNat.Equiv.Basic
import Azurite.Benchmark.AzNatAdd -- reuse natSignificantBits
import Azurite.Benchmark.RatCmp   -- reuse timeNsIter, median3, configGetRat, configGetNat

open Azurite Azurite.Random Azurite.Benchmark

/--
Run the `az_nat_square_algorithms_toomcook3` benchmark.
For each of `limit` random `Nat`s (sampled with geometric bit-length
distribution of mean `meanBitLength`), time `a²` two ways:
  - `squareKaratsuba karatsubaThreshold a` — Karatsuba squaring
    (O(n^log₂3), three recursive squarings per level)
  - `squareToomCook3 toomCook3Threshold karatsubaThreshold a` — Toom-Cook 3
    squaring (O(n^log₃5 ≈ 1.46), five recursive squarings per level),
    falling back to Karatsuba at sub-products below `toomCook3Threshold`.

Both are checked against each other at runtime.

Output format (one line per input):
  `<bits>;Karatsuba,<ns>;ToomCook3,<ns>`
where `<bits>` is the significant-bit count of `a`.

Config keys:
  - `meanBitLength` (Rat, default 262144) — geometric mean of bit length.
    Higher than `az_nat_square_algorithms` since the Karatsuba ↔ Toom-Cook 3
    cross-over for squaring (like for mul) sits at much larger sizes.
  - `iters` (Nat, default 10) — inner-loop iterations per timing sample
    (lower than schoolbook-comparison defaults since each call is far
    more expensive).
  - `karatsubaThreshold` (Nat, default 32) — Karatsuba schoolbook fallback.
  - `toomCook3Threshold` (Nat, default 256) — Toom-Cook 3 → Karatsuba fallback.
-/
def runAzNatSquareAlgorithmsToomCook3 (limit : Nat) (cfg : Std.HashMap String String)
    (seed : UInt64) : IO Unit := do
  let meanBitLength := configGetRat cfg "meanBitLength" 262144
  let iters := configGetNat cfg "iters" 10
  let karatsubaThreshold := configGetNat cfg "karatsubaThreshold" 32
  let toomCook3Threshold := configGetNat cfg "toomCook3Threshold" 256
  let mut g := mkNatRandomGen meanBitLength seed
  for _ in List.range limit do
    let (a, g') := NatRandomGen.next g
    let azA := Azurite.AzNat.ofNat a
    let bits := natSignificantBits a
    -- Karatsuba square
    let (rKar, ns1a) ← timeNsIter iters (fun _ => Azurite.AzNat.squareKaratsuba karatsubaThreshold azA)
    let (_,    ns1b) ← timeNsIter iters (fun _ => Azurite.AzNat.squareKaratsuba karatsubaThreshold azA)
    let (_,    ns1c) ← timeNsIter iters (fun _ => Azurite.AzNat.squareKaratsuba karatsubaThreshold azA)
    let ns1 := median3 ns1a ns1b ns1c
    -- Toom-Cook 3 square
    let (rToom, ns2a) ← timeNsIter iters (fun _ =>
      Azurite.AzNat.squareToomCook3 toomCook3Threshold karatsubaThreshold azA)
    let (_,    ns2b) ← timeNsIter iters (fun _ =>
      Azurite.AzNat.squareToomCook3 toomCook3Threshold karatsubaThreshold azA)
    let (_,    ns2c) ← timeNsIter iters (fun _ =>
      Azurite.AzNat.squareToomCook3 toomCook3Threshold karatsubaThreshold azA)
    let ns2 := median3 ns2a ns2b ns2c
    if Azurite.AzNat.toNat rKar ≠ Azurite.AzNat.toNat rToom then
      IO.eprintln s!"BUG: karatsuba ≠ toomCook3 squaring for a={a}"
    IO.println s!"{bits};Karatsuba,{ns1};ToomCook3,{ns2}"
    g := g'
