import Azurite.AzNat.Karatsuba
import Azurite.AzNat.Equiv.Basic
import Azurite.Random.NatGen
import Azurite.Benchmark.Timer

/-!
# Karatsuba Threshold Auto-Tuner for `AzNat`

Mirrors `AzPolynomial/Tune.lean`: golden-section search to find the optimal
Karatsuba cutoff threshold (in 64-bit limbs) for the current machine.

Two notable differences from the polynomial tuner:
* Inputs are `AzNat`s; "size" is `limbs.size`.
* Pairs that are very unbalanced (e.g. 100 limbs × 5 limbs) are filtered out,
  since `mulKaratsuba` pads the shorter operand to match the longer.  Tuning
  on those would mostly measure padding overhead, not the cross-over between
  schoolbook and Karatsuba on real-sized inputs.  The filter keeps pairs
  where `min/max ≥ balanceRatio/100`.
-/

open Azurite Azurite.AzNat Azurite.Random Azurite.Benchmark

-- ── Test input generation ───────────────────────────────────────────────────

/-- Generate `n` pairs of random `AzNat`, each at approximately `meanBitLength`
    bits, filtered to those with limb-size ratio ≥ `balanceRatio / 100`.
    Caps generation at `nPairs * 20` attempts to avoid infinite loops on
    overly aggressive filters. -/
def generateBalancedAzNatPairs (n : Nat) (meanBitLength : Rat)
    (balanceRatio : Nat) (seed : UInt64) :
    Array (AzNat × AzNat) := Id.run do
  let mut g := mkNatRandomGen meanBitLength seed
  let mut pairs : Array (AzNat × AzNat) := #[]
  let mut attempts := 0
  let maxAttempts := n * 20
  while pairs.size < n && attempts < maxAttempts do
    attempts := attempts + 1
    let (a, g₁) := NatRandomGen.next g
    let (b, g₂) := NatRandomGen.next g₁
    g := g₂
    let azA := AzNat.ofNat a
    let azB := AzNat.ofNat b
    let sa := azA.limbs.size
    let sb := azB.limbs.size
    let mn := min sa sb
    let mx := max sa sb
    if 1 ≤ mx && mn * 100 ≥ balanceRatio * mx then
      pairs := pairs.push (azA, azB)
  return pairs

-- ── Generic benchmarking ────────────────────────────────────────────────────

/-- Time `mulKaratsuba` over all pairs at the given threshold.  Accumulates
    result limb counts to prevent dead-code elimination. -/
@[noinline]
def benchAzNatThreshold (threshold : Nat) (pairs : Array (AzNat × AzNat)) :
    IO (UInt64 × Nat) := do
  let t0 ← monoNanos
  let mut checksum : Nat := 0
  for (a, b) in pairs do
    let r := AzNat.mulKaratsuba threshold a b
    checksum := checksum + r.limbs.size
  let t1 ← monoNanos
  return (t1 - t0, checksum)

/-- Median-of-3 timing for a given threshold. -/
def benchAzNatThresholdMedian (threshold : Nat) (pairs : Array (AzNat × AzNat)) :
    IO UInt64 := do
  let (t1, _) ← benchAzNatThreshold threshold pairs
  let (t2, _) ← benchAzNatThreshold threshold pairs
  let (t3, _) ← benchAzNatThreshold threshold pairs
  if t1 ≤ t2 then
    if t2 ≤ t3 then return t2
    else if t1 ≤ t3 then return t3
    else return t1
  else
    if t1 ≤ t3 then return t1
    else if t2 ≤ t3 then return t3
    else return t2

-- ── Golden-section search ───────────────────────────────────────────────────

/-- Golden-section search over `[lo, hi]` to minimise total runtime.  Below
    the tolerance window, falls back to exhaustive scan. -/
partial def goldenSectionSearchAzNat (lo hi : Nat) (tolerance : Nat)
    (pairs : Array (AzNat × AzNat)) (verbose : Bool := true) : IO Nat := do
  if hi - lo ≤ tolerance then
    let mut bestThreshold := lo
    let mut bestTime ← benchAzNatThresholdMedian lo pairs
    if verbose then
      IO.eprintln s!"  threshold={lo}  time={bestTime}ns"
    for k in List.range (hi - lo) do
      let t := lo + k + 1
      let time ← benchAzNatThresholdMedian t pairs
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
    let f1 ← benchAzNatThresholdMedian x1 pairs
    let f2 ← benchAzNatThresholdMedian x2 pairs
    if verbose then
      IO.eprintln s!"  [{lo}, {hi}]  x1={x1} ({f1}ns)  x2={x2} ({f2}ns)"
    if f1 < f2 then
      goldenSectionSearchAzNat lo x2 tolerance pairs verbose
    else
      goldenSectionSearchAzNat x1 hi tolerance pairs verbose

-- ── Top-level tuner ─────────────────────────────────────────────────────────

/-- Tune Karatsuba threshold for `AzNat`.

    `lo`/`hi` bound the search window (limbs).  `nPairs` is the number of
    test pairs to generate at `meanBitLength` bits each, filtered to those
    whose limb-size ratio (min/max) is at least `balanceRatio / 100`.
    `tolerance` is the exhaustive-scan window once the golden-section search
    narrows down. -/
def tuneAzNatKaratsuba
    (lo : Nat := 2) (hi : Nat := 128)
    (nPairs : Nat := 200) (meanBitLength : Rat := 100000)
    (balanceRatio : Nat := 50) (tolerance : Nat := 4)
    (seed : UInt64 := 42) : IO Nat := do
  IO.eprintln s!"[AzNat] Generating up to {nPairs} balanced test pairs"
  IO.eprintln s!"        (mean bit length {meanBitLength}, balance ≥ {balanceRatio}%)..."
  let pairs := generateBalancedAzNatPairs nPairs meanBitLength balanceRatio seed
  IO.eprintln s!"[AzNat] Got {pairs.size} pairs after filtering."
  if pairs.size = 0 then
    IO.eprintln "[AzNat] No pairs survived filtering — try a smaller balanceRatio."
    return lo
  IO.eprintln s!"[AzNat] Searching for optimal threshold in [{lo}, {hi}]..."
  IO.eprintln ""
  let best ← goldenSectionSearchAzNat lo hi tolerance pairs
  IO.eprintln ""
  IO.eprintln s!"[AzNat] Optimal threshold: {best}"
  let timeBest ← benchAzNatThresholdMedian best pairs
  let timeDefault ← benchAzNatThresholdMedian 32 pairs  -- match the default in mulKaratsuba caller
  IO.eprintln s!"  threshold={best}: {timeBest}ns"
  IO.eprintln s!"  threshold=32 (typical default): {timeDefault}ns"
  if timeBest < timeDefault then
    let pct := (timeDefault - timeBest).toNat * 100 / timeDefault.toNat
    IO.eprintln s!"  → {pct}% faster than default"
  else
    IO.eprintln "  → default is already optimal (or within noise)"
  return best
