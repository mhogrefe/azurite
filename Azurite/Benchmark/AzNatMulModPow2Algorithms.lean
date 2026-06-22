import Azurite.Random.Nat
import Azurite.Random.Geometric
import Azurite.Random.Gen
import Azurite.AzNat.MulModPow2.Schoolbook
import Azurite.AzNat.MulModPow2.Karatsuba
import Azurite.AzNat.MulModPow2.ToomCook3
import Azurite.AzNat.Equiv.Basic
import Azurite.Benchmark.Common

open Azurite Azurite.Random Azurite.Benchmark

/-!
# `az_nat_mul_mod_pow2_algorithms`

Times the three low-multiplication algorithms against each other on full-width
`b`-bit residue operands (`k = b`), to locate the dispatch cross-overs:
where Karatsuba-low overtakes schoolbook-low, and where Toom-3-low overtakes
Karatsuba-low.  Output: `<k>;Schoolbook,<ns>;Karatsuba,<ns>;Toom,<ns>`.
-/

def runAzNatMulModPow2Algorithms (limit : Nat) (cfg : Std.HashMap String String)
    (seed : UInt64) : IO Unit := do
  let meanBitLength := configGetRat cfg "meanBitLength" 4096
  let iters := configGetNat cfg "iters" 50
  let karaThreshold := configGetNat cfg "karaThreshold" 2
  let toomThreshold := configGetNat cfg "toomThreshold" 2
  let mut geo := mkNatGeometricRandomGen meanBitLength (deriveSeed seed "bitlen")
  let mut sm := mkSplitMix64 (deriveSeed seed "operands")
  for _ in List.range limit do
    let (b0, geo') := NatGeometricRandomGen.next geo
    geo := geo'
    let b := max b0 1
    let bg : NatWithBitsRandomGen SplitMix64 := { gen := sm, b := b }
    let (a, bg1) := NatWithBitsRandomGen.next bg
    let (c, bg2) := NatWithBitsRandomGen.next bg1
    sm := bg2.gen
    let azA := Azurite.AzNat.ofNat a
    let azC := Azurite.AzNat.ofNat c
    let k := b
    let (rS, ns1a) ← timeNsIter iters (fun _ => Azurite.AzNat.mulSchoolbookModPow2 azA azC k)
    let (_,  ns1b) ← timeNsIter iters (fun _ => Azurite.AzNat.mulSchoolbookModPow2 azA azC k)
    let (_,  ns1c) ← timeNsIter iters (fun _ => Azurite.AzNat.mulSchoolbookModPow2 azA azC k)
    let ns1 := median3 ns1a ns1b ns1c
    let (rK, ns2a) ← timeNsIter iters (fun _ => Azurite.AzNat.mulKaratsubaModPow2 karaThreshold azA azC k)
    let (_,  ns2b) ← timeNsIter iters (fun _ => Azurite.AzNat.mulKaratsubaModPow2 karaThreshold azA azC k)
    let (_,  ns2c) ← timeNsIter iters (fun _ => Azurite.AzNat.mulKaratsubaModPow2 karaThreshold azA azC k)
    let ns2 := median3 ns2a ns2b ns2c
    let (rT, ns3a) ← timeNsIter iters
      (fun _ => Azurite.AzNat.mulToomCook3ModPow2 toomThreshold karaThreshold azA azC k)
    let (_,  ns3b) ← timeNsIter iters
      (fun _ => Azurite.AzNat.mulToomCook3ModPow2 toomThreshold karaThreshold azA azC k)
    let (_,  ns3c) ← timeNsIter iters
      (fun _ => Azurite.AzNat.mulToomCook3ModPow2 toomThreshold karaThreshold azA azC k)
    let ns3 := median3 ns3a ns3b ns3c
    if Azurite.AzNat.toNat rS ≠ Azurite.AzNat.toNat rK
        || Azurite.AzNat.toNat rS ≠ Azurite.AzNat.toNat rT then
      IO.eprintln s!"BUG: low-mul algorithms disagree for a={a}, c={c}, k={k}"
    IO.println s!"{k};Schoolbook,{ns1};Karatsuba,{ns2};Toom,{ns3}"
