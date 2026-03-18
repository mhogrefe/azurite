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

/-- Encode an Ordering as a byte for XOR accumulation. -/
@[inline] def orderingByte : Ordering → UInt8
  | .lt => 1
  | .eq => 2
  | .gt => 4

/-- Time `iters` calls to `f ()`, XOR-folding results into a checksum to prevent
    dead-code elimination. The compiler cannot eliminate calls when each result
    contributes to the checksum (which is printed in the output). Returns
    `(lastResult, checksum, avgNsPerCall)`. -/
@[noinline]
def timeNsIterOrdering (iters : Nat) (f : Unit → Ordering) : IO (Ordering × UInt8 × UInt64) := do
  let t0 ← monoNanos
  let mut v := f ()
  let mut chk : UInt8 := orderingByte v
  for _ in List.range (iters - 1) do
    v := f ()
    chk := chk ^^^ orderingByte v
  let t1 ← monoNanos
  return (v, chk, (t1 - t0) / iters.toUInt64)

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

-- ── Benchmarks ──────────────────────────────────────────────────────────────

def validBenchmarks : List String := ["rat_cmp"]

/--
Run the `rat_cmp` benchmark.
For each of `limit` pairs `(a, b)` of random `Rat`s, time both:
  - `compare a b`          (Lean default)
  - `Azurite.Rat.cmp a b`  (Azurite implementation)

Output format (one line per pair):
  `a,b,default,<ns>,<chk>,azurite,<ns>,<chk>`
where `<chk>` is an XOR checksum of all Ordering results (prevents DCE).
-/
def runRatCmp (limit : Nat) (cfg : Std.HashMap String String) (seed : UInt64) : IO Unit := do
  let meanBitLength := configGetRat cfg "meanBitLength" 64
  let iters := configGetNat cfg "iters" 1000
  let gen := mkPairRandomGenFromSingle (α := Rat) (mkRatRandomGen meanBitLength seed)
  let mut g := gen
  for _ in List.range limit do
    let ((a, b), g') := PairRandomGenFromSingle.next g
    let (r1, chk1, ns1a) ← timeNsIterOrdering iters (fun _ => compare a b)
    let (_, _, ns1b) ← timeNsIterOrdering iters (fun _ => compare a b)
    let (_, _, ns1c) ← timeNsIterOrdering iters (fun _ => compare a b)
    let ns1 := median3 ns1a ns1b ns1c
    let (r2, chk2, ns2a) ← timeNsIterOrdering iters (fun _ => Azurite.Rat.cmp a b)
    let (_, _, ns2b) ← timeNsIterOrdering iters (fun _ => Azurite.Rat.cmp a b)
    let (_, _, ns2c) ← timeNsIterOrdering iters (fun _ => Azurite.Rat.cmp a b)
    let ns2 := median3 ns2a ns2b ns2c
    if r1 ≠ r2 then
      let fmt : Ordering → String | .lt => "lt" | .eq => "eq" | .gt => "gt"
      IO.eprintln s!"BUG: compare={fmt r1} cmp={fmt r2} for {formatRat a},{formatRat b}"
    IO.println s!"{formatRat a},{formatRat b},default,{ns1},{chk1},azurite,{ns2},{chk2}"
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
