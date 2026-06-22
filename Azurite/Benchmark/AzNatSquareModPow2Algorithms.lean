import Azurite.Random.Nat
import Azurite.Random.Geometric
import Azurite.Random.Gen
import Azurite.AzNat.SquareModPow2.Schoolbook
import Azurite.AzNat.SquareModPow2.Karatsuba
import Azurite.AzNat.SquareModPow2.ToomCook3
import Azurite.AzNat.Equiv.Basic
import Azurite.Benchmark.Common

open Azurite Azurite.Random Azurite.Benchmark

/-!
# `az_nat_square_mod_pow2_algorithms`

Times the three low-squaring algorithms against each other on full-width `b`-bit
residues (`k = b`), to locate the dispatch cross-overs for squaring.
Output: `<k>;Schoolbook,<ns>;Karatsuba,<ns>;Toom,<ns>`.
-/

def runAzNatSquareModPow2Algorithms (limit : Nat) (cfg : Std.HashMap String String)
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
    sm := bg1.gen
    let azA := Azurite.AzNat.ofNat a
    let k := b
    let (rS, ns1a) ← timeNsIter iters (fun _ => Azurite.AzNat.squareSchoolbookModPow2 azA k)
    let (_,  ns1b) ← timeNsIter iters (fun _ => Azurite.AzNat.squareSchoolbookModPow2 azA k)
    let (_,  ns1c) ← timeNsIter iters (fun _ => Azurite.AzNat.squareSchoolbookModPow2 azA k)
    let ns1 := median3 ns1a ns1b ns1c
    let (rK, ns2a) ← timeNsIter iters (fun _ => Azurite.AzNat.squareKaratsubaModPow2 karaThreshold azA k)
    let (_,  ns2b) ← timeNsIter iters (fun _ => Azurite.AzNat.squareKaratsubaModPow2 karaThreshold azA k)
    let (_,  ns2c) ← timeNsIter iters (fun _ => Azurite.AzNat.squareKaratsubaModPow2 karaThreshold azA k)
    let ns2 := median3 ns2a ns2b ns2c
    let (rT, ns3a) ← timeNsIter iters
      (fun _ => Azurite.AzNat.squareToomCook3ModPow2 toomThreshold karaThreshold azA k)
    let (_,  ns3b) ← timeNsIter iters
      (fun _ => Azurite.AzNat.squareToomCook3ModPow2 toomThreshold karaThreshold azA k)
    let (_,  ns3c) ← timeNsIter iters
      (fun _ => Azurite.AzNat.squareToomCook3ModPow2 toomThreshold karaThreshold azA k)
    let ns3 := median3 ns3a ns3b ns3c
    if Azurite.AzNat.toNat rS ≠ Azurite.AzNat.toNat rK
        || Azurite.AzNat.toNat rS ≠ Azurite.AzNat.toNat rT then
      IO.eprintln s!"BUG: low-square algorithms disagree for a={a}, k={k}"
    IO.println s!"{k};Schoolbook,{ns1};Karatsuba,{ns2};Toom,{ns3}"
