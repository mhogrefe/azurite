import Azurite.Random.NatGen
import Azurite.AzNat.SqrtRem
import Azurite.AzNat.Equiv.Basic
import Azurite.Benchmark.AzNatAdd -- reuse natSignificantBits
import Azurite.Benchmark.Common -- reuse timeNsIter, median3, configGetRat, configGetNat

open Azurite Azurite.Random Azurite.Benchmark

/--
Run the `az_nat_sqrt_rem_algorithms` benchmark.

For each of `limit` random `Nat`s `n` (sampled with geometric bit-length
distribution of mean `meanBitLength`), time:
  - `basecaseSqrtRem` — MCA Algorithm 1.13 (Newton iteration) applied to
    the whole input.
  - `sqrtRem` — MCA Algorithm 1.12 (divide-and-conquer) that recurses on
    the top half once `(len − 1) / 4 ≥ 1`, delegating to
    `basecaseSqrtRem` for the leaves.

Output uses the duplicated-bucket form `<sb>,<sb>;Basecase,<ns>;DnC,<ns>`
so the same data can drive both a line chart (x = `2 · sb`) and a
heatmap (cells along the diagonal `y = x` showing which algorithm wins
at each input bit length).

Config keys:
  - `meanBitLength` (Rat, default 8192) — geometric mean of input bit
    length. D&C only kicks in for `m.limbs.size ≥ 5` (i.e., ≳ 320
    bits), so we want a distribution centred well above that.
  - `iters` (Nat, default 10) — inner-loop iterations per timing
    sample.  Low because each call is expensive at our scale.
-/
def runAzNatSqrtRemAlgorithms (limit : Nat) (cfg : Std.HashMap String String)
    (seed : UInt64) : IO Unit := do
  let meanBitLength := configGetRat cfg "meanBitLength" 8192
  let iters := configGetNat cfg "iters" 10
  let mut g := mkNatRandomGen meanBitLength seed
  for _ in List.range limit do
    let (n, g') := NatRandomGen.next g
    let azN := Azurite.AzNat.ofNat n
    let sb := natSignificantBits n
    -- basecaseSqrtRem
    let (rBase, ns1a) ← timeNsIter iters (fun _ => Azurite.AzNat.basecaseSqrtRem azN)
    let (_,     ns1b) ← timeNsIter iters (fun _ => Azurite.AzNat.basecaseSqrtRem azN)
    let (_,     ns1c) ← timeNsIter iters (fun _ => Azurite.AzNat.basecaseSqrtRem azN)
    let ns1 := median3 ns1a ns1b ns1c
    -- D&C sqrtRem
    let (rDnC, ns2a) ← timeNsIter iters (fun _ => Azurite.AzNat.sqrtRem azN)
    let (_,    ns2b) ← timeNsIter iters (fun _ => Azurite.AzNat.sqrtRem azN)
    let (_,    ns2c) ← timeNsIter iters (fun _ => Azurite.AzNat.sqrtRem azN)
    let ns2 := median3 ns2a ns2b ns2c
    -- Sanity: both algorithms must agree.
    if Azurite.AzNat.toNat rBase.1 ≠ Azurite.AzNat.toNat rDnC.1
       ∨ Azurite.AzNat.toNat rBase.2 ≠ Azurite.AzNat.toNat rDnC.2 then
      IO.eprintln s!"BUG: basecase ≠ D&C for n={n}"
    IO.println s!"{sb},{sb};Basecase,{ns1};DnC,{ns2}"
    g := g'
