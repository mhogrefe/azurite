import Azurite.Random.Nat
import Azurite.Random.Geometric
import Azurite.Random.Gen
import Azurite.AzNat.SubModPow2
import Azurite.AzNat.ModPow2
import Azurite.AzNat.Add
import Azurite.AzNat.Equiv.Basic
import Azurite.Benchmark.Common

open Azurite Azurite.Random Azurite.Benchmark

/-!
# `az_nat_sub_mod_pow2_residue`

Fused borrow-and-mask `AzNat.subModPow2 a c k` vs. the naive add-of-complement
`modPow2 (a + (2^k - c)) k`, on full-width `k`-bit residues.

Since `AzNat` subtraction truncates at `0`, the honest non-fused way to get
`(a - c) mod 2^k` is to add the precomputed additive inverse `cb = 2^k - c` and
mask — the same add-then-mask shape compared in the addition benchmark.
-/

/-- Run the `az_nat_sub_mod_pow2_residue` benchmark.  Both operands are exactly
`b`-bit (`k = b`); times fused `subModPow2 a c k` vs `modPow2 (a + cb) k` where
`cb = 2^k - c` is precomputed (not timed).  Output: `<k>;Fused,<ns>;Naive,<ns>`. -/
def runAzNatSubModPow2Residue (limit : Nat) (cfg : Std.HashMap String String)
    (seed : UInt64) : IO Unit := do
  let meanBitLength := configGetRat cfg "meanBitLength" 4096
  let iters := configGetNat cfg "iters" 200
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
    -- Additive inverse of `c` mod `2^k`, precomputed (not timed).
    let cb := Azurite.AzNat.ofNat (2 ^ k - c)
    -- Fused borrow-and-mask
    let (rFused, ns1a) ← timeNsIter iters (fun _ => Azurite.AzNat.subModPow2 azA azC k)
    let (_,      ns1b) ← timeNsIter iters (fun _ => Azurite.AzNat.subModPow2 azA azC k)
    let (_,      ns1c) ← timeNsIter iters (fun _ => Azurite.AzNat.subModPow2 azA azC k)
    let ns1 := median3 ns1a ns1b ns1c
    -- Naive add-of-complement then mask
    let (rNaive, ns2a) ← timeNsIter iters (fun _ => Azurite.AzNat.modPow2 (azA + cb) k)
    let (_,      ns2b) ← timeNsIter iters (fun _ => Azurite.AzNat.modPow2 (azA + cb) k)
    let (_,      ns2c) ← timeNsIter iters (fun _ => Azurite.AzNat.modPow2 (azA + cb) k)
    let ns2 := median3 ns2a ns2b ns2c
    -- Sanity check: both must equal `(a - c) mod 2^k = (a + 2^k - c) % 2^k`.
    let spec := (a + (2 ^ k - c)) % 2 ^ k
    if Azurite.AzNat.toNat rFused ≠ spec then
      IO.eprintln s!"BUG: subModPow2 disagrees with spec for a={a}, c={c}, k={k}"
    if Azurite.AzNat.toNat rNaive ≠ spec then
      IO.eprintln s!"BUG: modPow2 (a+cb) disagrees with spec for a={a}, c={c}, k={k}"
    IO.println s!"{k};Fused,{ns1};Naive,{ns2}"
