import Azurite.Random
import Azurite.Rat.Compare
import Azurite.Benchmark.Timer

open Azurite.Random Azurite.Benchmark

-- ── Config helpers ──────────────────────────────────────────────────────────

def configGetRat (cfg : Std.HashMap String String) (key : String) (default : Rat) : Rat :=
  match cfg[key]? with
  | none   => default
  | some s =>
    match s.toNat? with
    | some n => (n : Rat)
    | none   => default

def configGetNat (cfg : Std.HashMap String String) (key : String) (default : Nat) : Nat :=
  match cfg[key]? with
  | none   => default
  | some s => s.toNat?.getD default

-- ── Rat formatting ──────────────────────────────────────────────────────────

def formatRat (r : Rat) : String :=
  if r.den == 1 then toString r.num
  else s!"{r.num}/{r.den}"

-- ── Timing ──────────────────────────────────────────────────────────────────

/-- Time `iters` calls to `f ()`. Returns `(lastResult, avgNsPerCall)`. -/
@[noinline]
def timeNsIter {α : Type} (iters : Nat) (f : Unit → α) : IO (α × UInt64) := do
  let t0 ← monoNanos
  let mut v := f ()
  for _ in List.range (iters - 1) do
    v := f ()
  let t1 ← monoNanos
  return (v, (t1 - t0) / iters.toUInt64)

/-- Return the median of three values. -/
def median3 (a b c : UInt64) : UInt64 :=
  if a ≤ b then
    if b ≤ c then b        -- a ≤ b ≤ c
    else if a ≤ c then c   -- a ≤ c < b
    else a                 -- c < a ≤ b
  else -- b < a
    if a ≤ c then a        -- b < a ≤ c
    else if b ≤ c then c   -- b ≤ c < a
    else b                 -- c < b < a

-- ── Benchmark ───────────────────────────────────────────────────────────────

/--
Run the `rat_cmp` benchmark.
For each of `limit` pairs `(a, b)` of random `Rat`s, time both:
  - `compare a b`          (Lean default)
  - `Azurite.Rat.cmp a b`  (Azurite implementation)

Output format (one line per pair):
  `a,b,default,<ns>,azurite,<ns>`
-/
def runRatCmp (limit : Nat) (cfg : Std.HashMap String String) (seed : UInt64) : IO Unit := do
  let meanBitLength := configGetRat cfg "meanBitLength" 64
  let iters := configGetNat cfg "iters" 1000
  let gen := mkPairRandomGenFromSingle (α := Rat) (mkRatRandomGen meanBitLength seed)
  let mut g := gen
  for _ in List.range limit do
    let ((a, b), g') := PairRandomGenFromSingle.next g
    let (r1, ns1a) ← timeNsIter iters (fun _ => compare a b)
    let (_, ns1b) ← timeNsIter iters (fun _ => compare a b)
    let (_, ns1c) ← timeNsIter iters (fun _ => compare a b)
    let ns1 := median3 ns1a ns1b ns1c
    let (r2, ns2a) ← timeNsIter iters (fun _ => Azurite.Rat.cmp a b)
    let (_, ns2b) ← timeNsIter iters (fun _ => Azurite.Rat.cmp a b)
    let (_, ns2c) ← timeNsIter iters (fun _ => Azurite.Rat.cmp a b)
    let ns2 := median3 ns2a ns2b ns2c
    if r1 ≠ r2 then
      let fmt : Ordering → String | .lt => "lt" | .eq => "eq" | .gt => "gt"
      IO.eprintln s!"BUG: compare={fmt r1} cmp={fmt r2} for {formatRat a},{formatRat b}"
    IO.println s!"{formatRat a},{formatRat b},default,{ns1},azurite,{ns2}"
    g := g'
