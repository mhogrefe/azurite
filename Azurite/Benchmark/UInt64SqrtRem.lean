import Azurite.Random.NatGen
import Azurite.UInt64.SqrtRem
import Azurite.Benchmark.AzNatAdd -- reuse natSignificantBits
import Azurite.Benchmark.RatCmp -- reuse timeNsIter, median3, configGetRat, configGetNat

open Azurite Azurite.Random Azurite.Benchmark

/--
Run the `uint64_sqrt_rem` benchmark.

Times `Azurite.UInt64.sqrtRem n` on random `UInt64` values whose
underlying `Nat` is drawn from a geometric bit-length distribution.
The single series isolates the cost of a Float-based initial guess
plus the ±1 correction loops; expected runtime is essentially the
hardware sqrt latency, which we expect to be on the order of tens
of nanoseconds — close to or below `timeNsIter`'s resolution, so we
need a high inner-iter count.

We also accumulate the low 64 bits of the result so the compiler
cannot dead-code-eliminate the call.

Output format (one line per input):
  `<sb>;SqrtRem,<ns>`
where `<sb> = sigBits n.toNat`.

Config keys:
  - `meanBitLength` (Rat, default 32) — geometric mean of the input
    bit length.  Cap at 64.
  - `iters` (Nat, default 10000) — inner-loop iterations per timing
    sample.  Larger than other benchmarks because each call is so
    cheap.
-/
def runUInt64SqrtRem (limit : Nat) (cfg : Std.HashMap String String)
    (seed : UInt64) : IO Unit := do
  let meanBitLength := configGetRat cfg "meanBitLength" 32
  let iters := configGetNat cfg "iters" 10000
  let mut g := mkNatRandomGen meanBitLength seed
  let mut acc : UInt64 := 0
  for _ in List.range limit do
    let (uNat, g') := NatRandomGen.next g
    -- Geometric distribution can exceed 64 bits; mask down to UInt64.
    let n : UInt64 := uNat.toUInt64
    let sb := natSignificantBits n.toNat
    let (r1, ns1a) ← timeNsIter iters (fun _ => Azurite.UInt64.sqrtRem n)
    let (_,  ns1b) ← timeNsIter iters (fun _ => Azurite.UInt64.sqrtRem n)
    let (_,  ns1c) ← timeNsIter iters (fun _ => Azurite.UInt64.sqrtRem n)
    let ns1 := median3 ns1a ns1b ns1c
    -- Sanity: s² + r = n (no overflow on the s² side since s ≤ 2^32 − 1).
    if r1.1 * r1.1 + r1.2 ≠ n then
      IO.eprintln s!"BUG: sqrtRem invariant violated for n={n.toNat}"
    -- Use the result so the compiler can't elide it.
    acc := acc ^^^ r1.1 ^^^ r1.2
    IO.println s!"{sb};SqrtRem,{ns1}"
    g := g'
  IO.eprintln s!"# accumulator: {acc.toNat}"
