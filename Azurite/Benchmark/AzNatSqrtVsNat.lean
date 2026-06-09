import Azurite.Random.NatGen
import Azurite.AzNat.SqrtRem
import Azurite.AzNat.Equiv.Basic
import Azurite.Benchmark.AzNatAdd -- reuse natSignificantBits
import Azurite.Benchmark.Common   -- reuse timeNsIter, median3, configGetRat, configGetNat

open Azurite Azurite.Random Azurite.Benchmark

/--
Run the `az_nat_sqrt_vs_nat` benchmark.

For each of `limit` random `Nat`s `n` (sampled with geometric bit-length
distribution of mean `meanBitLength`), time `⌊√n⌋` two ways:
  - `Nat.sqrt n`     — Lean's built-in Newton iteration on `Nat` (the
    arithmetic inside each step is GMP-backed, but the iteration loop
    is pure Lean).
  - `AzNat.sqrt`     — the divide-and-conquer wrapper (MCA 1.12) over
    the limb-level basecase.

Runtime correctness is checked per input; any disagreement is reported
to stderr.

Output format (one line per input):
  `<bits>;Nat,<ns>;AzNat,<ns>`
where `<bits>` is the significant-bit count of `n`. Sqrt is single-input,
so we report `bits(n)` directly (mirrors `az_nat_square_vs_nat`).

Config keys:
  - `meanBitLength` (Rat, default 4096) — geometric mean of input bit
    length.
  - `iters` (Nat, default 10) — inner-loop iterations per timing
    sample.
-/
def runAzNatSqrtVsNat (limit : Nat) (cfg : Std.HashMap String String)
    (seed : UInt64) : IO Unit := do
  let meanBitLength := configGetRat cfg "meanBitLength" 4096
  let iters := configGetNat cfg "iters" 10
  let mut g := mkNatRandomGen meanBitLength seed
  for _ in List.range limit do
    let (n, g') := NatRandomGen.next g
    let azN := Azurite.AzNat.ofNat n
    let bits := natSignificantBits n
    let (rNat, ns1a) ← timeNsIter iters (fun _ => Nat.sqrt n)
    let (_,    ns1b) ← timeNsIter iters (fun _ => Nat.sqrt n)
    let (_,    ns1c) ← timeNsIter iters (fun _ => Nat.sqrt n)
    let ns1 := median3 ns1a ns1b ns1c
    let (rAz, ns2a) ← timeNsIter iters (fun _ => Azurite.AzNat.sqrt azN)
    let (_,   ns2b) ← timeNsIter iters (fun _ => Azurite.AzNat.sqrt azN)
    let (_,   ns2c) ← timeNsIter iters (fun _ => Azurite.AzNat.sqrt azN)
    let ns2 := median3 ns2a ns2b ns2c
    if Azurite.AzNat.toNat rAz ≠ rNat then
      IO.eprintln s!"BUG: AzNat.sqrt disagrees with Nat.sqrt for n={n}"
    IO.println s!"{bits};Nat,{ns1};AzNat,{ns2}"
    g := g'
