import Azurite.Random.NatGen
import Azurite.Random.Pair
import Azurite.AzNat.Mul
import Azurite.AzNat.Equiv.Basic
import Azurite.Benchmark.AzNatAdd -- reuse natSignificantBits
import Azurite.Benchmark.RatCmp -- reuse timeNsIter, median3, configGetRat, configGetNat

open Azurite Azurite.Random Azurite.Benchmark

/--
Run the `az_nat_mul` benchmark.
For each of `limit` pairs `(a, b)` of random `Nat`s (sampled with geometric
bit-length distribution of mean `meanBitLength`), time `a * b` on `Nat` (which
delegates to GMP `mpn_mul`) and on `AzNat` (schoolbook).

Output format:
  `<sb>;Nat,<ns>;AzNat,<ns>`
-/
def runAzNatMul (limit : Nat) (cfg : Std.HashMap String String) (seed : UInt64) : IO Unit := do
  let meanBitLength := configGetRat cfg "meanBitLength" 256
  let iters := configGetNat cfg "iters" 100
  let gen := mkPairRandomGenFromSingle (α := Nat) (mkNatRandomGen meanBitLength seed)
  let mut g := gen
  for _ in List.range limit do
    let ((a, b), g') := PairRandomGenFromSingle.next g
    let azA := Azurite.AzNat.ofNat a
    let azB := Azurite.AzNat.ofNat b
    let sb := natSignificantBits a + natSignificantBits b
    let (rNat, ns1a) ← timeNsIter iters (fun _ => a * b)
    let (_,    ns1b) ← timeNsIter iters (fun _ => a * b)
    let (_,    ns1c) ← timeNsIter iters (fun _ => a * b)
    let ns1 := median3 ns1a ns1b ns1c
    let (rAz, ns2a) ← timeNsIter iters (fun _ => azA * azB)
    let (_,   ns2b) ← timeNsIter iters (fun _ => azA * azB)
    let (_,   ns2c) ← timeNsIter iters (fun _ => azA * azB)
    let ns2 := median3 ns2a ns2b ns2c
    if Azurite.AzNat.toNat rAz ≠ rNat then
      IO.eprintln s!"BUG: AzNat mul disagrees with Nat mul for a={a}, b={b}"
    IO.println s!"{sb};Nat,{ns1};AzNat,{ns2}"
    g := g'
