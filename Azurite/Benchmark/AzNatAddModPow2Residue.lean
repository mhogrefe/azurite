import Azurite.Random.Nat
import Azurite.Random.Geometric
import Azurite.Random.Gen
import Azurite.AzNat.AddModPow2
import Azurite.AzNat.Equiv.AddModPow2
import Azurite.AzNat.ModPow2
import Azurite.AzNat.Add
import Azurite.AzNat.Equiv.Basic
import Azurite.Benchmark.Common

open Azurite Azurite.Random Azurite.Benchmark

/-!
# `az_nat_add_mod_pow2_residue`

Residue-style variant of `az_nat_add_mod_pow2`: both operands are full-width
`b`-bit values and the modulus is `2^b`, matching the actual `AzZModPow2` use
case (uniform `k`-bit residues, roughly equal width) rather than the lopsided
geometric pairs of the original benchmark.
-/

/--
Run the `az_nat_add_mod_pow2_residue` benchmark.

For each of `limit` samples, draw a bit-length `b` (geometric, mean
`meanBitLength`) and generate **both** operands as exactly-`b`-bit values; set
`k = b` so they are full-width `k`-bit residues.  Time on `AzNat`:
  - `addModPow2 a c k`        (fused single-pass low-`L` add-and-mask)
  - `modPow2 (a + c) k`       (full `AzNat.add` then a separate masking pass)

Output (one line per sample): `<k>;Fused,<ns>;Naive,<ns>`.
-/
def runAzNatAddModPow2Residue (limit : Nat) (cfg : Std.HashMap String String)
    (seed : UInt64) : IO Unit := do
  let meanBitLength := configGetRat cfg "meanBitLength" 4096
  let iters := configGetNat cfg "iters" 200
  let mut geo := mkNatGeometricRandomGen meanBitLength (deriveSeed seed "bitlen")
  let mut sm := mkSplitMix64 (deriveSeed seed "operands")
  for _ in List.range limit do
    let (b0, geo') := NatGeometricRandomGen.next geo
    geo := geo'
    let b := max b0 1
    -- Two exactly-`b`-bit operands from a single threaded stream.
    let bg : NatWithBitsRandomGen SplitMix64 := { gen := sm, b := b }
    let (a, bg1) := NatWithBitsRandomGen.next bg
    let (c, bg2) := NatWithBitsRandomGen.next bg1
    sm := bg2.gen
    let azA := Azurite.AzNat.ofNat a
    let azC := Azurite.AzNat.ofNat c
    let k := b
    -- Fused add-and-mask
    let (rFused, ns1a) ← timeNsIter iters (fun _ => Azurite.AzNat.addModPow2 azA azC k)
    let (_,      ns1b) ← timeNsIter iters (fun _ => Azurite.AzNat.addModPow2 azA azC k)
    let (_,      ns1c) ← timeNsIter iters (fun _ => Azurite.AzNat.addModPow2 azA azC k)
    let ns1 := median3 ns1a ns1b ns1c
    -- Naive add then mask
    let (rNaive, ns2a) ← timeNsIter iters (fun _ => Azurite.AzNat.modPow2 (azA + azC) k)
    let (_,      ns2b) ← timeNsIter iters (fun _ => Azurite.AzNat.modPow2 (azA + azC) k)
    let (_,      ns2c) ← timeNsIter iters (fun _ => Azurite.AzNat.modPow2 (azA + azC) k)
    let ns2 := median3 ns2a ns2b ns2c
    -- Sanity check: both must equal `(a + c) % 2^k`.
    let spec := (a + c) % 2 ^ k
    if Azurite.AzNat.toNat rFused ≠ spec then
      IO.eprintln s!"BUG: addModPow2 disagrees with spec for a={a}, c={c}, k={k}"
    if Azurite.AzNat.toNat rNaive ≠ spec then
      IO.eprintln s!"BUG: modPow2 (a+c) disagrees with spec for a={a}, c={c}, k={k}"
    IO.println s!"{k};Fused,{ns1};Naive,{ns2}"
