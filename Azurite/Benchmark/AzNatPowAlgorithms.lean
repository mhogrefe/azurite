import Azurite.Random.NatGen
import Azurite.AzNat.Pow
import Azurite.AzNat.Equiv.Basic
import Azurite.Benchmark.AzNatAdd -- reuse natSignificantBits
import Azurite.Benchmark.RatCmp   -- reuse timeNsIter, median3, configGetRat, configGetNat

open Azurite Azurite.Random Azurite.Benchmark

/--
Run the `az_nat_pow_algorithms` benchmark.

Times `a ^ n` two ways for random base/exponent pairs:
  - `AzNat.pow a n`        — sliding-window exponentiation
  - `AzNat.powBinary a n`  — right-to-left binary exponentiation (the old algorithm)

Both share the same fast three-way `square` (via the `Square AzNat` instance), so the only
difference is the number of *multiplications* the exponent recurrence performs — that is exactly
what this benchmark isolates.

The base `a` is sampled with a fixed mean bit-length (`baseBits`); the exponent `n` is sampled with
a small mean bit-length (`meanExpBits`) and hard-capped at `maxExp`, since `a ^ n` has
`n · bits(a)` bits and full (non-modular) exponentiation is only practical for modest `n`. The
x-axis bucket is the exponent's significant-bit count, which determines how many squarings and
window multiplications each algorithm performs.

Both results are checked against each other; any disagreement is reported to stderr.

Output format (one line per input):
  `<expBits>;SlidingWindow,<ns>;Binary,<ns>`

Config keys:
  - `baseBits` (Rat, default 512) — geometric mean bit length of the base `a`.
  - `meanExpBits` (Rat, default 9) — geometric mean bit length of the exponent `n`.
  - `maxExp` (Nat, default 4096) — hard cap on the exponent (keeps `a ^ n` bounded).
  - `iters` (Nat, default 5) — inner-loop iterations per timing sample.
-/
def runAzNatPowAlgorithms (limit : Nat) (cfg : Std.HashMap String String)
    (seed : UInt64) : IO Unit := do
  let baseBits := configGetRat cfg "baseBits" 512
  let meanExpBits := configGetRat cfg "meanExpBits" 9
  let maxExp := configGetNat cfg "maxExp" 4096
  let iters := configGetNat cfg "iters" 5
  let mut gBase := mkNatRandomGen baseBits seed
  let mut gExp := mkNatRandomGen meanExpBits (seed + 0x9e3779b9)
  for _ in List.range limit do
    let (a, gBase') := NatRandomGen.next gBase
    let (eRaw, gExp') := NatRandomGen.next gExp
    let n := Nat.max 2 (Nat.min eRaw maxExp)
    let azA := Azurite.AzNat.ofNat a
    let bits := natSignificantBits n
    -- Sliding-window exponentiation
    let (rSW, ns1a) ← timeNsIter iters (fun _ => azA.pow n)
    let (_,   ns1b) ← timeNsIter iters (fun _ => azA.pow n)
    let (_,   ns1c) ← timeNsIter iters (fun _ => azA.pow n)
    let ns1 := median3 ns1a ns1b ns1c
    -- Binary exponentiation
    let (rB, ns2a) ← timeNsIter iters (fun _ => azA.powBinary n)
    let (_,  ns2b) ← timeNsIter iters (fun _ => azA.powBinary n)
    let (_,  ns2c) ← timeNsIter iters (fun _ => azA.powBinary n)
    let ns2 := median3 ns2a ns2b ns2c
    if rSW ≠ rB then
      IO.eprintln s!"BUG: sliding-window ≠ binary pow for a={a}, n={n}"
    IO.println s!"{bits};SlidingWindow,{ns1};Binary,{ns2}"
    gBase := gBase'
    gExp := gExp'
