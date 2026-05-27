import Azurite.Random.NatGen
import Azurite.Random.Pair
import Azurite.AzNat.DivRecursiveLimbs
import Azurite.AzNat.Equiv.Basic
import Azurite.Benchmark.AzNatAdd -- reuse natSignificantBits
import Azurite.Benchmark.RatCmp -- reuse timeNsIter, median3, configGetRat, configGetNat

open Azurite Azurite.Random Azurite.Benchmark

/--
Run the `az_nat_div_vs_div_mod` benchmark.
For each of `limit` pairs `(U, V)` of random `Nat`s (independently seeded so
the dividend and divisor are uncorrelated, both at mean bit length
`meanBitLength`), time:
  - `U / V`        — the specialised `div` (skips remainder post-processing).
  - `U.divMod V`   — the full divMod that produces both quotient and remainder.

The expected gap is the remainder post-processing the specialised div skips:
extracting the n-limb remainder, normalising it, and the `>>> k`
denormalisation shift.  For multi-limb divisors with similarly-sized
operands this is O(n) work on top of the O((n_U − n) · n) algorithm.

Output format (one line per pair):
  `<sb>;Div,<ns>;DivMod,<ns>`
where `<sb> = sigBits U + sigBits V`.

Config keys:
  - `meanBitLength` (Rat, default 8192) — geometric mean of dividend and
    divisor bit length.  Larger than `az_nat_div_mod`'s 256 so the
    post-processing savings are measurable.
  - `iters` (Nat, default 100) — inner-loop iterations per timing sample.
-/
def runAzNatDivVsDivMod (limit : Nat) (cfg : Std.HashMap String String)
    (seed : UInt64) : IO Unit := do
  let meanBitLength := configGetRat cfg "meanBitLength" 8192
  let iters := configGetNat cfg "iters" 100
  let gen := mkPairRandomGen
    (α := Nat) (β := Nat)
    (mkNatRandomGen meanBitLength)
    (mkPositiveNatRandomGen meanBitLength)
    seed
  let mut g := gen
  for _ in List.range limit do
    let ((u, v), g') := PairRandomGen.next g
    let azU := Azurite.AzNat.ofNat u
    let azV := Azurite.AzNat.ofNat v
    let sb := natSignificantBits u + natSignificantBits v
    -- Specialised div
    let (rDiv, ns1a) ← timeNsIter iters (fun _ => azU / azV)
    let (_,    ns1b) ← timeNsIter iters (fun _ => azU / azV)
    let (_,    ns1c) ← timeNsIter iters (fun _ => azU / azV)
    let ns1 := median3 ns1a ns1b ns1c
    -- Full divMod
    let (rDivMod, ns2a) ← timeNsIter iters (fun _ => azU.divMod azV)
    let (_,       ns2b) ← timeNsIter iters (fun _ => azU.divMod azV)
    let (_,       ns2c) ← timeNsIter iters (fun _ => azU.divMod azV)
    let ns2 := median3 ns2a ns2b ns2c
    -- Sanity: the specialised div should agree with the projected divMod.
    if Azurite.AzNat.toNat rDiv ≠ Azurite.AzNat.toNat rDivMod.1 then
      IO.eprintln s!"BUG: div disagrees with divMod.1 for u={u}, v={v}"
    IO.println s!"{sb};Div,{ns1};DivMod,{ns2}"
    g := g'
