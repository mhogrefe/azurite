import Azurite.AzPolynomial.Karatsuba
import Azurite.Random.AzPolynomial
import Azurite.Benchmark.Timer
import Mathlib.Data.ZMod.Basic

/-!
# Karatsuba Threshold Auto-Tuner

Uses golden-section search to find the optimal Karatsuba cutoff threshold
for the current machine. The search minimises total wall-clock time over a
deterministic set of pseudorandom polynomial multiplications.

Provides tuners for `AzPolynomial ℤ`, `AzPolynomial ℚ`, and `AzPolynomial (ZMod n)`.
-/

open Azurite Azurite.AzPolynomial Azurite.Random Azurite.Benchmark

-- ── Test input generation ───────────────────────────────────────────────────

/-- Generate `n` pairs of random `AzPolynomial ℤ`. -/
def generateTestPairsInt (n : Nat) (meanDegree : Rat) (seed : UInt64) :
    Array (AzPolynomial ℤ × AzPolynomial ℤ) := Id.run do
  let mut g := mkAzPolynomialIntRandomGen meanDegree 8 seed
  let mut pairs : Array (AzPolynomial ℤ × AzPolynomial ℤ) := #[]
  for _ in List.range n do
    let (a, g') := AzPolynomialRandomGen.next g
    let (b, g'') := AzPolynomialRandomGen.next g'
    pairs := pairs.push (a, b)
    g := g''
  return pairs

/-- Generate `n` pairs of random `AzPolynomial ℚ`. -/
def generateTestPairsRat (n : Nat) (meanDegree : Rat) (seed : UInt64) :
    Array (AzPolynomial ℚ × AzPolynomial ℚ) := Id.run do
  let mut g := mkAzPolynomialRatRandomGen meanDegree 8 seed
  let mut pairs : Array (AzPolynomial ℚ × AzPolynomial ℚ) := #[]
  for _ in List.range n do
    let (a, g') := AzPolynomialRandomGen.next g
    let (b, g'') := AzPolynomialRandomGen.next g'
    pairs := pairs.push (a, b)
    g := g''
  return pairs

/-- Generate `n` pairs of random `AzPolynomial (ZMod p)`.
    Uses `p = 65537` (a Fermat prime) for realistic modular arithmetic. -/
def generateTestPairsZMod (n : Nat) (meanDegree : Rat) (seed : UInt64) :
    Array (AzPolynomial (ZMod 65537) × AzPolynomial (ZMod 65537)) := Id.run do
  let mut g := mkAzPolynomialZModRandomGen 65537 meanDegree seed
  let mut pairs : Array (AzPolynomial (ZMod 65537) × AzPolynomial (ZMod 65537)) := #[]
  for _ in List.range n do
    let (a, g') := AzPolynomialRandomGen.next g
    let (b, g'') := AzPolynomialRandomGen.next g'
    pairs := pairs.push (a, b)
    g := g''
  return pairs

-- ── Generic benchmarking ────────────────────────────────────────────────────

/-- Time `mulKaratsubaWithThreshold` over all pairs of a given type.
    Accumulates result array sizes to prevent dead-code-elimination. -/
@[noinline]
def benchThresholdGeneric [Ring R] [DecidableEq R]
    (threshold : Nat) (pairs : Array (AzPolynomial R × AzPolynomial R)) : IO (UInt64 × Nat) := do
  let t0 ← monoNanos
  let mut checksum : Nat := 0
  for (a, b) in pairs do
    let r := mulKaratsubaWithThreshold threshold a b
    checksum := checksum + r.coeffs.size
  let t1 ← monoNanos
  return (t1 - t0, checksum)

/-- Median-of-3 benchmark for a given threshold. -/
def benchThresholdMedianGeneric [Ring R] [DecidableEq R]
    (threshold : Nat) (pairs : Array (AzPolynomial R × AzPolynomial R)) : IO UInt64 := do
  let (t1, _) ← benchThresholdGeneric threshold pairs
  let (t2, _) ← benchThresholdGeneric threshold pairs
  let (t3, _) ← benchThresholdGeneric threshold pairs
  -- Median of 3
  if t1 ≤ t2 then
    if t2 ≤ t3 then return t2
    else if t1 ≤ t3 then return t3
    else return t1
  else
    if t1 ≤ t3 then return t1
    else if t2 ≤ t3 then return t3
    else return t2

-- ── Golden-section search ───────────────────────────────────────────────────

/-- Golden-section search over `[lo, hi]` to minimise runtime. -/
partial def goldenSectionSearchGeneric [Ring R] [DecidableEq R]
    (lo hi : Nat)
    (tolerance : Nat)
    (pairs : Array (AzPolynomial R × AzPolynomial R))
    (verbose : Bool := true)
    : IO Nat := do
  if hi - lo ≤ tolerance then
    let mut bestThreshold := lo
    let mut bestTime ← benchThresholdMedianGeneric lo pairs
    if verbose then
      IO.eprintln s!"  threshold={lo}  time={bestTime}ns"
    for k in List.range (hi - lo) do
      let t := lo + k + 1
      let time ← benchThresholdMedianGeneric t pairs
      if verbose then
        IO.eprintln s!"  threshold={t}  time={time}ns"
      if time < bestTime then
        bestTime := time
        bestThreshold := t
    return bestThreshold
  else
    let x1 := lo + (hi - lo) * 382 / 1000
    let x2 := lo + (hi - lo) * 618 / 1000
    let x1 := max (lo + 1) (min x1 (hi - 2))
    let x2 := max (x1 + 1) (min x2 (hi - 1))
    let f1 ← benchThresholdMedianGeneric x1 pairs
    let f2 ← benchThresholdMedianGeneric x2 pairs
    if verbose then
      IO.eprintln s!"  [{lo}, {hi}]  x1={x1} ({f1}ns)  x2={x2} ({f2}ns)"
    if f1 < f2 then
      goldenSectionSearchGeneric lo x2 tolerance pairs verbose
    else
      goldenSectionSearchGeneric x1 hi tolerance pairs verbose

-- ── Shared reporting helper ─────────────────────────────────────────────────

private def reportResult [Ring R] [DecidableEq R]
    (label : String) (best : Nat)
    (pairs : Array (AzPolynomial R × AzPolynomial R)) : IO Unit := do
  IO.eprintln ""
  IO.eprintln s!"[{label}] Optimal threshold: {best}"
  let timeBest ← benchThresholdMedianGeneric best pairs
  let timeDefault ← benchThresholdMedianGeneric karatsubaThreshold pairs
  IO.eprintln s!"  threshold={best}: {timeBest}ns"
  IO.eprintln s!"  threshold={karatsubaThreshold} (default): {timeDefault}ns"
  if timeBest < timeDefault then
    let pct := (timeDefault - timeBest).toNat * 100 / timeDefault.toNat
    IO.eprintln s!"  → {pct}% faster than default"
  else
    IO.eprintln s!"  → default is already optimal (or within noise)"

-- ── Top-level tuners ────────────────────────────────────────────────────────

/-- Tune Karatsuba threshold for `AzPolynomial ℤ`. -/
def tuneKaratsuba
    (lo : Nat := 4) (hi : Nat := 256)
    (nPairs : Nat := 200) (meanDegree : Rat := 256)
    (tolerance : Nat := 4)
    (seed : UInt64 := 42) : IO Nat := do
  IO.eprintln s!"[ℤ] Generating {nPairs} test pairs (mean degree {meanDegree})..."
  let pairs := generateTestPairsInt nPairs meanDegree seed
  IO.eprintln s!"[ℤ] Searching for optimal threshold in [{lo}, {hi}]..."
  IO.eprintln ""
  let best ← goldenSectionSearchGeneric lo hi tolerance pairs
  reportResult "ℤ" best pairs
  return best

/-- Tune Karatsuba threshold for `AzPolynomial ℚ`. -/
def tuneKaratsubaRat
    (lo : Nat := 4) (hi : Nat := 256)
    (nPairs : Nat := 200) (meanDegree : Rat := 256)
    (tolerance : Nat := 4)
    (seed : UInt64 := 42) : IO Nat := do
  IO.eprintln s!"[ℚ] Generating {nPairs} test pairs (mean degree {meanDegree})..."
  let pairs := generateTestPairsRat nPairs meanDegree seed
  IO.eprintln s!"[ℚ] Searching for optimal threshold in [{lo}, {hi}]..."
  IO.eprintln ""
  let best ← goldenSectionSearchGeneric lo hi tolerance pairs
  reportResult "ℚ" best pairs
  return best

/-- Tune Karatsuba threshold for `AzPolynomial (ZMod 65537)`. -/
def tuneKaratsubaZMod
    (lo : Nat := 4) (hi : Nat := 256)
    (nPairs : Nat := 200) (meanDegree : Rat := 256)
    (tolerance : Nat := 4)
    (seed : UInt64 := 42) : IO Nat := do
  IO.eprintln s!"[ZMod] Generating {nPairs} test pairs (mean degree {meanDegree})..."
  let pairs := generateTestPairsZMod nPairs meanDegree seed
  IO.eprintln s!"[ZMod] Searching for optimal threshold in [{lo}, {hi}]..."
  IO.eprintln ""
  let best ← goldenSectionSearchGeneric lo hi tolerance pairs
  reportResult "ZMod 65537" best pairs
  return best

/-- Run all three tuners and compare results. -/
def tuneKaratsubaAll
    (lo : Nat := 4) (hi : Nat := 256)
    (nPairs : Nat := 200) (meanDegree : Rat := 256)
    (tolerance : Nat := 4)
    (seed : UInt64 := 42) : IO Unit := do
  let bestZ ← tuneKaratsuba lo hi nPairs meanDegree tolerance seed
  IO.eprintln ""
  let bestQ ← tuneKaratsubaRat lo hi nPairs meanDegree tolerance seed
  IO.eprintln ""
  let bestZM ← tuneKaratsubaZMod lo hi nPairs meanDegree tolerance seed
  IO.eprintln ""
  IO.eprintln "══════════════════════════════════════════"
  IO.eprintln s!"Summary:"
  IO.eprintln s!"  AzPolynomial ℤ:          optimal threshold = {bestZ}"
  IO.eprintln s!"  AzPolynomial ℚ:          optimal threshold = {bestQ}"
  IO.eprintln s!"  AzPolynomial (ZMod 65537): optimal threshold = {bestZM}"
  IO.eprintln "══════════════════════════════════════════"
