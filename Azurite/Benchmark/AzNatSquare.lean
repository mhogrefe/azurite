import Azurite.Random.NatGen
import Azurite.AzNat.Karatsuba
import Azurite.AzNat.Square
import Azurite.AzNat.Equiv.Basic
import Azurite.Benchmark.AzNatAdd -- reuse natSignificantBits
import Azurite.Benchmark.RatCmp   -- reuse timeNsIter, median3, configGetRat, configGetNat

open Azurite Azurite.Random Azurite.Benchmark

/--
Run the `az_nat_square` benchmark.
For each of `limit` random `Nat`s (sampled with geometric bit-length
distribution of mean `meanBitLength`), time `a * a` two ways:
  - `mulSchoolbook a a`  — uses `schoolbookMulLimbs` (n² wideMuls)
  - `squareSchoolbook a` — uses `schoolbookSquareLimbs` (n(n+1)/2 wideMuls)

Output format:
  `<sb>;mulSchoolbook,<ns>;squareSchoolbook,<ns>`
where `<sb>` is the significant-bit count of the input `a`.
-/
def runAzNatSquare (limit : Nat) (cfg : Std.HashMap String String) (seed : UInt64) : IO Unit := do
  let meanBitLength := configGetRat cfg "meanBitLength" 256
  let iters := configGetNat cfg "iters" 100
  let mut g := mkNatRandomGen meanBitLength seed
  for _ in List.range limit do
    let (a, g') := NatRandomGen.next g
    let azA := Azurite.AzNat.ofNat a
    let sb := natSignificantBits a
    let (rMul, ns1a) ← timeNsIter iters (fun _ => Azurite.AzNat.mulSchoolbook azA azA)
    let (_,    ns1b) ← timeNsIter iters (fun _ => Azurite.AzNat.mulSchoolbook azA azA)
    let (_,    ns1c) ← timeNsIter iters (fun _ => Azurite.AzNat.mulSchoolbook azA azA)
    let ns1 := median3 ns1a ns1b ns1c
    let (rSq, ns2a) ← timeNsIter iters (fun _ => Azurite.AzNat.squareSchoolbook azA)
    let (_,   ns2b) ← timeNsIter iters (fun _ => Azurite.AzNat.squareSchoolbook azA)
    let (_,   ns2c) ← timeNsIter iters (fun _ => Azurite.AzNat.squareSchoolbook azA)
    let ns2 := median3 ns2a ns2b ns2c
    if Azurite.AzNat.toNat rSq ≠ Azurite.AzNat.toNat rMul then
      IO.eprintln s!"BUG: squareSchoolbook disagrees with mulSchoolbook for a={a}"
    IO.println s!"{sb};mulSchoolbook,{ns1};squareSchoolbook,{ns2}"
    g := g'
