import Azurite.Random.NatGen
import Azurite.Random.Pair
import Azurite.AzNat.DivRecursiveLimbs
import Azurite.AzNat.Equiv.Basic
import Azurite.Benchmark.AzNatAdd -- reuse natSignificantBits
import Azurite.Benchmark.RatCmp -- reuse timeNsIter, median3, configGetRat, configGetNat

open Azurite Azurite.Random Azurite.Benchmark

/--
Run the `az_nat_div_mod` benchmark.
For each of `limit` pairs `(U, V)` of random `Nat`s, time `U / V` (or
`U.divMod V`) on `Nat` and on `AzNat`. The dividend `U` is sampled from a
geometric bit-length distribution with mean `meanBitLength`; the divisor `V`
is sampled positive (≥ 1) from a geometric distribution with mean
`meanDivisorBitLength` (defaults to `meanBitLength`). Pairs are independently
seeded so dividend and divisor are uncorrelated.

Output format:
  `<sb>;Nat,<ns>;AzNat,<ns>`
where `<sb> = sigBits U + sigBits V`.
-/
def runAzNatDivMod (limit : Nat) (cfg : Std.HashMap String String) (seed : UInt64) : IO Unit := do
  let meanBitLength := configGetRat cfg "meanBitLength" 256
  let meanDivisorBitLength := configGetRat cfg "meanDivisorBitLength" meanBitLength
  let iters := configGetNat cfg "iters" 100
  let gen := mkPairRandomGen
    (α := Nat) (β := Nat)
    (mkNatRandomGen meanBitLength)
    (mkPositiveNatRandomGen meanDivisorBitLength)
    seed
  let mut g := gen
  for _ in List.range limit do
    let ((u, v), g') := PairRandomGen.next g
    let azU := Azurite.AzNat.ofNat u
    let azV := Azurite.AzNat.ofNat v
    let sb := natSignificantBits u + natSignificantBits v
    let (rNat, ns1a) ← timeNsIter iters (fun _ => u / v)
    let (_,    ns1b) ← timeNsIter iters (fun _ => u / v)
    let (_,    ns1c) ← timeNsIter iters (fun _ => u / v)
    let ns1 := median3 ns1a ns1b ns1c
    let (rAz, ns2a) ← timeNsIter iters (fun _ => azU / azV)
    let (_,   ns2b) ← timeNsIter iters (fun _ => azU / azV)
    let (_,   ns2c) ← timeNsIter iters (fun _ => azU / azV)
    let ns2 := median3 ns2a ns2b ns2c
    if Azurite.AzNat.toNat rAz ≠ rNat then
      IO.eprintln s!"BUG: AzNat div disagrees with Nat div for u={u}, v={v}"
    IO.println s!"{sb};Nat,{ns1};AzNat,{ns2}"
    g := g'
