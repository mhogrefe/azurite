import Azurite.AzNat.Mul
import Azurite.AzNat.Square
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

-- ── 2-D tuner over (minThreshold, k) ────────────────────────────────────────

/-- Generate `n` pairs of random `AzNat` with the full bivariate (lenA, lenB)
    distribution — no balance filter. The 2-D tuner *wants* to see lopsided
    pairs since the ratio dimension is what it's tuning. -/
def generateAzNatPairsUnfiltered (n : Nat) (meanBitLength : Rat) (seed : UInt64) :
    Array (AzNat × AzNat) := Id.run do
  let mut g := mkNatRandomGen meanBitLength seed
  let mut pairs : Array (AzNat × AzNat) := #[]
  for _ in List.range n do
    let (a, g₁) := NatRandomGen.next g
    let (b, g₂) := NatRandomGen.next g₁
    g := g₂
    pairs := pairs.push (AzNat.ofNat a, AzNat.ofNat b)
  return pairs

/-- Time `mulDispatchParam` over all pairs at the given (minThreshold, kPercent),
    where `k = kPercent / 100`. Returns total ns. -/
@[noinline]
def benchAzNatDispatchParam (minThreshold kPercent : Nat)
    (pairs : Array (AzNat × AzNat)) : IO (UInt64 × Nat) := do
  let t0 ← monoNanos
  let mut checksum : Nat := 0
  for (a, b) in pairs do
    let r := AzNat.mulDispatchParam minThreshold kPercent 100 a b
    checksum := checksum + r.limbs.size
  let t1 ← monoNanos
  return (t1 - t0, checksum)

/-- Median-of-3 timing for a given (minThreshold, kPercent). -/
def benchAzNatDispatchParamMedian (minThreshold kPercent : Nat)
    (pairs : Array (AzNat × AzNat)) : IO UInt64 := do
  let (t1, _) ← benchAzNatDispatchParam minThreshold kPercent pairs
  let (t2, _) ← benchAzNatDispatchParam minThreshold kPercent pairs
  let (t3, _) ← benchAzNatDispatchParam minThreshold kPercent pairs
  if t1 ≤ t2 then
    if t2 ≤ t3 then return t2
    else if t1 ≤ t3 then return t3
    else return t1
  else
    if t1 ≤ t3 then return t1
    else if t2 ≤ t3 then return t3
    else return t2

/-- Pad a string with spaces on the left up to `width`. -/
private def padLeft (width : Nat) (s : String) : String :=
  let n := s.length
  if n ≥ width then s else String.ofList (List.replicate (width - n) ' ') ++ s

/-- 2-D grid sweep over `(minThreshold, kPercent)`.

    Karatsuba is picked at the top-level dispatch when
    `lenMin ≥ minThreshold ∧ 100 · lenMin ≥ kPercent · lenMax`.
    Setting `kPercent = 0` recovers the "min-threshold only" criterion.

    Prints a landscape table of total times and returns the best
    `(minThreshold, kPercent)`. -/
def tuneAzNatDispatch2D
    (thresholds : Array Nat := #[16, 24, 32, 48, 64, 96, 128])
    (kPercents  : Array Nat := #[0, 6, 12, 18, 25, 37, 50, 75])
    (nPairs : Nat := 400) (meanBitLength : Rat := 100000)
    (seed : UInt64 := 42) : IO (Nat × Nat) := do
  IO.eprintln s!"[AzNat-2D] Generating {nPairs} test pairs (mean bit length {meanBitLength}, no filter)..."
  let pairs := generateAzNatPairsUnfiltered nPairs meanBitLength seed
  IO.eprintln s!"[AzNat-2D] {pairs.size} pairs."
  IO.eprintln ""
  -- Collect timings: timings[i][j] = ns at thresholds[i], kPercents[j].
  let mut timings : Array (Array UInt64) := #[]
  let mut bestThreshold : Nat := 0
  let mut bestKPercent  : Nat := 0
  let mut bestTime : UInt64 := UInt64.ofNat (Nat.pow 2 63)
  for i in List.range thresholds.size do
    let t := thresholds[i]!
    let mut row : Array UInt64 := #[]
    for j in List.range kPercents.size do
      let k := kPercents[j]!
      let time ← benchAzNatDispatchParamMedian t k pairs
      row := row.push time
      if time < bestTime then
        bestThreshold := t
        bestKPercent := k
        bestTime := time
    timings := timings.push row
  -- Render landscape: rows = minThreshold, columns = kPercent.
  let colWidth := 9
  let header := "  thr \\ k%  " ++ String.join (kPercents.toList.map fun k =>
    padLeft colWidth s!"{k}")
  IO.eprintln header
  IO.eprintln (String.ofList (List.replicate header.length '-'))
  for i in List.range thresholds.size do
    let t := thresholds[i]!
    let mut line := padLeft 10 s!"{t}" ++ "  "
    for j in List.range kPercents.size do
      let ns := timings[i]![j]!
      -- Show in microseconds (rounded) to keep the table narrow.
      let us := ns.toNat / 1000
      let marker := if t == bestThreshold && kPercents[j]! == bestKPercent then "*" else " "
      line := line ++ padLeft colWidth (s!"{us}" ++ marker)
    IO.eprintln line
  IO.eprintln ""
  IO.eprintln s!"[AzNat-2D] Best: minThreshold = {bestThreshold}, kPercent = {bestKPercent} ({bestTime}ns)"
  return (bestThreshold, bestKPercent)

-- ── 1-D tuner for square dispatch threshold ─────────────────────────────────

/-- Generate `n` random `AzNat`s for the single-input squaring tune. -/
def generateAzNatSingles (n : Nat) (meanBitLength : Rat) (seed : UInt64) :
    Array AzNat := Id.run do
  let mut g := mkNatRandomGen meanBitLength seed
  let mut nats : Array AzNat := #[]
  for _ in List.range n do
    let (a, g') := NatRandomGen.next g
    g := g'
    nats := nats.push (AzNat.ofNat a)
  return nats

/-- Time `squareDispatchParam minThreshold` over all inputs.  Accumulates
    result limb counts to prevent dead-code elimination. -/
@[noinline]
def benchAzNatSquareDispatch (minThreshold : Nat) (inputs : Array AzNat) :
    IO (UInt64 × Nat) := do
  let t0 ← monoNanos
  let mut checksum : Nat := 0
  for a in inputs do
    let r := AzNat.squareDispatchParam minThreshold a
    checksum := checksum + r.limbs.size
  let t1 ← monoNanos
  return (t1 - t0, checksum)

/-- Median-of-3 timing for a given threshold. -/
def benchAzNatSquareDispatchMedian (minThreshold : Nat) (inputs : Array AzNat) :
    IO UInt64 := do
  let (t1, _) ← benchAzNatSquareDispatch minThreshold inputs
  let (t2, _) ← benchAzNatSquareDispatch minThreshold inputs
  let (t3, _) ← benchAzNatSquareDispatch minThreshold inputs
  if t1 ≤ t2 then
    if t2 ≤ t3 then return t2
    else if t1 ≤ t3 then return t3
    else return t1
  else
    if t1 ≤ t3 then return t1
    else if t2 ≤ t3 then return t3
    else return t2

/-- 1-D grid sweep over `minThreshold` for the squaring dispatcher.

    Squaring has no balance dimension (single operand → split into nearly
    equal halves), so this is a straightforward 1-D search.  Setting
    `minThreshold = ∞` recovers schoolbook-only behavior; very small values
    push Karatsuba down to trivially short inputs.

    Returns the best `minThreshold`. -/
def tuneAzNatSquareDispatch
    (thresholds : Array Nat :=
       #[2, 4, 8, 12, 16, 20, 24, 32, 48, 64, 96, 128, 256])
    (nInputs : Nat := 400) (meanBitLength : Rat := 100000)
    (seed : UInt64 := 42) : IO Nat := do
  IO.eprintln s!"[AzNat-Square] Generating {nInputs} test inputs (mean bit length {meanBitLength})..."
  let inputs := generateAzNatSingles nInputs meanBitLength seed
  IO.eprintln s!"[AzNat-Square] {inputs.size} inputs."
  IO.eprintln ""
  let mut bestThreshold : Nat := 0
  let mut bestTime : UInt64 := UInt64.ofNat (Nat.pow 2 63)
  let mut times : Array UInt64 := #[]
  for i in List.range thresholds.size do
    let t := thresholds[i]!
    let time ← benchAzNatSquareDispatchMedian t inputs
    times := times.push time
    if time < bestTime then
      bestThreshold := t
      bestTime := time
  -- Render a single-row landscape.
  let colWidth := 12
  let header := "  threshold  " ++ String.join (thresholds.toList.map fun t =>
    padLeft colWidth s!"{t}")
  IO.eprintln header
  IO.eprintln (String.ofList (List.replicate header.length '-'))
  let mut line := padLeft 11 "µs/run" ++ "  "
  for i in List.range thresholds.size do
    let ns := times[i]!
    let us := ns.toNat / 1000
    let marker := if thresholds[i]! == bestThreshold then "*" else " "
    line := line ++ padLeft colWidth (s!"{us}" ++ marker)
  IO.eprintln line
  IO.eprintln ""
  IO.eprintln s!"[AzNat-Square] Best: minThreshold = {bestThreshold} ({bestTime}ns)"
  return bestThreshold
