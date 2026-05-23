import Azurite.Random.NatGen
import Azurite.AzNat.Square
import Azurite.AzNat.Equiv.Basic
import Azurite.Benchmark.AzNatAdd -- reuse natSignificantBits
import Azurite.Benchmark.RatCmp   -- reuse timeNsIter, median3, configGetRat, configGetNat

open Azurite Azurite.Random Azurite.Benchmark

/--
Run the `az_nat_square_vs_nat` benchmark.
For each of `limit` random `Nat`s `a` (sampled with geometric bit-length
distribution of mean `meanBitLength`), time `a²` two ways:
  - `a * a`              — Lean's `Nat` mul (GMP-backed)
  - `AzNat.square a`     — dispatched `AzNat` squaring

Runtime correctness is checked per input; any disagreement is reported
to stderr.

Output format (one line per input):
  `<bits>;Nat,<ns>;AzNat,<ns>`
where `<bits>` is the significant-bit count of `a`. The output sum-of-input-
bits convention of `az_nat_mul_vs_nat` doesn't apply here (squaring takes one
operand), so we report `bits(a)` directly.

Config keys:
  - `meanBitLength` (Rat, default 256) — geometric mean of bit length.
  - `iters` (Nat, default 100) — inner-loop iterations per timing sample.
-/
def runAzNatSquareVsNat (limit : Nat) (cfg : Std.HashMap String String)
    (seed : UInt64) : IO Unit := do
  let meanBitLength := configGetRat cfg "meanBitLength" 256
  let iters := configGetNat cfg "iters" 100
  let mut g := mkNatRandomGen meanBitLength seed
  for _ in List.range limit do
    let (a, g') := NatRandomGen.next g
    let azA := Azurite.AzNat.ofNat a
    let bits := natSignificantBits a
    let (rNat, ns1a) ← timeNsIter iters (fun _ => a * a)
    let (_,    ns1b) ← timeNsIter iters (fun _ => a * a)
    let (_,    ns1c) ← timeNsIter iters (fun _ => a * a)
    let ns1 := median3 ns1a ns1b ns1c
    let (rAz, ns2a) ← timeNsIter iters (fun _ => Azurite.AzNat.square azA)
    let (_,   ns2b) ← timeNsIter iters (fun _ => Azurite.AzNat.square azA)
    let (_,   ns2c) ← timeNsIter iters (fun _ => Azurite.AzNat.square azA)
    let ns2 := median3 ns2a ns2b ns2c
    if Azurite.AzNat.toNat rAz ≠ rNat then
      IO.eprintln s!"BUG: AzNat.square disagrees with Nat mul for a={a}"
    IO.println s!"{bits};Nat,{ns1};AzNat,{ns2}"
    g := g'
