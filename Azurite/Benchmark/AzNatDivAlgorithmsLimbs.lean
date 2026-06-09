import Azurite.Random.NatGen
import Azurite.Random.Pair
import Azurite.AzNat.Div
import Azurite.AzNat.Equiv.Basic
import Azurite.Benchmark.AzNatAdd
import Azurite.Benchmark.Common

open Azurite Azurite.Random Azurite.Benchmark

/--
Run the `az_nat_div_algorithms_limbs` benchmark.

Compares `AzNat.recursiveDivMod` (proven AzNat-level D&C) against
`AzNat.recursiveDivModFast` (slice-style D&C with in-place body).

Output: `<bitsU>,<bitsV>;AzNat,<ns>;Limbs,<ns>`
-/
def runAzNatDivAlgorithmsLimbs (limit : Nat) (cfg : Std.HashMap String String)
    (seed : UInt64) : IO Unit := do
  let meanDividendBitLength := configGetRat cfg "meanDividendBitLength" 32768
  let meanDivisorBitLength := configGetRat cfg "meanDivisorBitLength" 16384
  let iters := configGetNat cfg "iters" 10
  let threshold := configGetNat cfg "threshold" 32
  let gen := mkPairRandomGen
    (α := Nat) (β := Nat)
    (mkNatRandomGen meanDividendBitLength)
    (mkPositiveNatRandomGen meanDivisorBitLength)
    seed
  let mut g := gen
  for _ in List.range limit do
    let ((u, v), g') := PairRandomGen.next g
    let azU := Azurite.AzNat.ofNat u
    let azV := Azurite.AzNat.ofNat v
    let bitsU := natSignificantBits u
    let bitsV := natSignificantBits v
    let (rAz, ns1a) ← timeNsIter iters
      (fun _ => Azurite.AzNat.divMod azU azV)
    let (_,   ns1b) ← timeNsIter iters
      (fun _ => Azurite.AzNat.divMod azU azV)
    let (_,   ns1c) ← timeNsIter iters
      (fun _ => Azurite.AzNat.divMod azU azV)
    let ns1 := median3 ns1a ns1b ns1c
    let (rLb, ns2a) ← timeNsIter iters
      (fun _ => Azurite.AzNat.recursiveDivModFast threshold azU azV)
    let (_,   ns2b) ← timeNsIter iters
      (fun _ => Azurite.AzNat.recursiveDivModFast threshold azU azV)
    let (_,   ns2c) ← timeNsIter iters
      (fun _ => Azurite.AzNat.recursiveDivModFast threshold azU azV)
    let ns2 := median3 ns2a ns2b ns2c
    if Azurite.AzNat.toNat rAz.1 ≠ Azurite.AzNat.toNat rLb.1
       ∨ Azurite.AzNat.toNat rAz.2 ≠ Azurite.AzNat.toNat rLb.2 then
      IO.eprintln s!"BUG: AzNat ≠ Limbs for u={u}, v={v}"
    IO.println s!"{bitsU},{bitsV};AzNat,{ns1};Limbs,{ns2}"
    g := g'
