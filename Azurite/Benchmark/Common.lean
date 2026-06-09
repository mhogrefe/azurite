import Azurite.Random.Rat
import Azurite.Benchmark.Timer

open Azurite.Random Azurite.Benchmark

/-!
# Shared benchmark utilities

Config parsing, timing, and small helpers reused across the benchmark drivers.
-/

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
