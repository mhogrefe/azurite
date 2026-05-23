import Azurite.Random.NatGen
import Azurite.Random.Pair
import Azurite.AzNat.Mul
import Azurite.AzNat.Equiv.Basic
import Azurite.Benchmark.AzNatAdd -- reuse natSignificantBits
import Azurite.Benchmark.RatCmp -- reuse timeNsIter, median3, configGetRat, configGetNat

open Azurite Azurite.Random Azurite.Benchmark

/--
Run the `az_nat_mul_algorithms` benchmark.
For each of `limit` pairs `(a, b)` of random `Nat`s (sampled with geometric
bit-length distribution of mean `meanBitLength`), time:
  - `mulSchoolbook` (current default mul, O(p·q))
  - `mulKaratsuba threshold` (O(n^1.585) once `len ≥ threshold`)

Both operate on the same `AzNat` values; `mulKaratsuba` pads the shorter
limb array with high zero limbs so the slices have equal length.

Output format (one line per pair):
  `<bitsA>,<bitsB>;Schoolbook,<ns>;Karatsuba,<ns>`
where `<bitsA>`, `<bitsB>` are the significant bits of `a` and `b`. The
chart driver can derive the sum as needed for line plots, or use the pair
as coordinates for a 2-D heatmap.

Config keys:
  - `meanBitLength` (Rat, default 256) — geometric mean of operand bit length.
  - `iters` (Nat, default 100) — inner-loop iterations per timing sample.
  - `threshold` (Nat, default 32) — Karatsuba schoolbook fallback threshold
    (in 64-bit limbs).
-/
def runAzNatMulAlgorithms (limit : Nat) (cfg : Std.HashMap String String)
    (seed : UInt64) : IO Unit := do
  let meanBitLength := configGetRat cfg "meanBitLength" 256
  let iters := configGetNat cfg "iters" 100
  let threshold := configGetNat cfg "threshold" 32
  let gen := mkPairRandomGenFromSingle (α := Nat) (mkNatRandomGen meanBitLength seed)
  let mut g := gen
  for _ in List.range limit do
    let ((a, b), g') := PairRandomGenFromSingle.next g
    let azA := Azurite.AzNat.ofNat a
    let azB := Azurite.AzNat.ofNat b
    let bitsA := natSignificantBits a
    let bitsB := natSignificantBits b
    -- Schoolbook
    let (rSch, ns1a) ← timeNsIter iters (fun _ => Azurite.AzNat.mulSchoolbook azA azB)
    let (_,    ns1b) ← timeNsIter iters (fun _ => Azurite.AzNat.mulSchoolbook azA azB)
    let (_,    ns1c) ← timeNsIter iters (fun _ => Azurite.AzNat.mulSchoolbook azA azB)
    let ns1 := median3 ns1a ns1b ns1c
    -- Karatsuba
    let (rKar, ns2a) ← timeNsIter iters (fun _ => Azurite.AzNat.mulKaratsuba threshold azA azB)
    let (_,   ns2b) ← timeNsIter iters (fun _ => Azurite.AzNat.mulKaratsuba threshold azA azB)
    let (_,   ns2c) ← timeNsIter iters (fun _ => Azurite.AzNat.mulKaratsuba threshold azA azB)
    let ns2 := median3 ns2a ns2b ns2c
    if Azurite.AzNat.toNat rSch ≠ Azurite.AzNat.toNat rKar then
      IO.eprintln s!"BUG: schoolbook ≠ karatsuba for a={a}, b={b}"
    IO.println s!"{bitsA},{bitsB};Schoolbook,{ns1};Karatsuba,{ns2}"
    g := g'
