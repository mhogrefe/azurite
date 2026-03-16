import Azurite.Random
import Azurite.Rat.Compare
import Azurite.Benchmark.Timer

open Azurite.Random Azurite.Benchmark

-- ── Config parsing ──────────────────────────────────────────────────────────

def parseConfig (s : String) : Std.HashMap String String :=
  s.splitOn "," |>.foldl (init := {}) fun m entry =>
    match entry.splitOn ":" with
    | [k, v] => m.insert k.trimAscii.toString v.trimAscii.toString
    | _      => m

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

/-- Time `f ()` over `iters` iterations and return the average nanoseconds per call.
    Running multiple iterations amortizes clock overhead and gives measurable results
    even for sub-nanosecond operations. `iters` should be large enough that the total
    time is well above the clock resolution (~10–50 ns on CLOCK_MONOTONIC). -/
@[noinline]
def timeNsIter {α : Type} (iters : Nat) (f : Unit → α) : IO (α × UInt64) := do
  let t0 ← monoNanos
  let mut v := f ()
  for _ in List.range (iters - 1) do
    v := f ()
  let t1 ← monoNanos
  return (v, (t1 - t0) / iters.toUInt64)

-- ── Benchmarks ──────────────────────────────────────────────────────────────

def validBenchmarks : List String := ["rat_cmp"]

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
  -- iters: number of repetitions per pair for timing; default 1000
  let iters := configGetNat cfg "iters" 100
  let gen := mkPairRandomGenFromSingle (α := Rat) (mkRatRandomGen meanBitLength seed)
  let mut g := gen
  for _ in List.range limit do
    let ((a, b), g') := PairRandomGenFromSingle.next g
    -- Run each implementation `iters` times; report average ns/op
    let (r1, ns1) ← timeNsIter iters (fun _ => compare a b)
    let (r2, ns2) ← timeNsIter iters (fun _ => Azurite.Rat.cmp a b)
    -- Assert correctness
    if r1 ≠ r2 then
      let fmt : Ordering → String | .lt => "lt" | .eq => "eq" | .gt => "gt"
      IO.eprintln s!"BUG: compare={fmt r1} cmp={fmt r2} for {formatRat a},{formatRat b}"
    IO.println s!"{formatRat a},{formatRat b},default,{ns1},azurite,{ns2}"
    g := g'

-- ── Main ────────────────────────────────────────────────────────────────────

def main (args : List String) : IO Unit := do
  -- Usage: benchmark <name> <limit> [config]
  -- config example: "meanBitLength:64"
  match args with
  | name :: limitStr :: rest =>
    let seed : UInt64 := 1337
    let cfg  := parseConfig (rest.headD "")
    match limitStr.toNat? with
    | none =>
      IO.eprintln s!"Error: limit must be a natural number, got '{limitStr}'"
    | some limit =>
      match name with
      | "rat_cmp" => runRatCmp limit cfg seed
      | _ =>
        IO.eprintln s!"Unknown benchmark: '{name}'"
        IO.eprintln s!"Valid benchmarks: {validBenchmarks}"
  | _ =>
    IO.eprintln "Usage: benchmark <name> <limit> [config]"
    IO.eprintln s!"Valid benchmarks: {validBenchmarks}"
    IO.eprintln "Config example:   meanBitLength:64"
