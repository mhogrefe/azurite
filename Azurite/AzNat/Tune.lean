/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

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
    let r := AzNat.mulDispatchParam minThreshold kPercent 100
      AzNat.mulDispatchToomCook3Cutoff a b
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
      let ns := (timings[i]!)[j]!
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
    let r := AzNat.squareDispatchParam minThreshold AzNat.squareDispatchToomCook3Cutoff
      AzNat.squareDispatchToomCook4Cutoff AzNat.squareDispatchFFTCutoff a
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

-- ── 1-D tuner for the Karatsuba ↔ Toom-Cook 3 dispatch threshold ──────────

/-- Dispatch between Karatsuba and Toom-Cook 3 based on `max(lenA, lenB)`.
    Below `toomCook3Cutoff`, use `mulKaratsuba`; at-or-above, use
    `mulToomCook3`.  The internal fallback thresholds (Karatsuba's schoolbook
    cutoff and Toom-Cook 3's Karatsuba cutoff) stay at their tuned defaults
    so this is a single-knob sweep. -/
def mulToomCook3DispatchParam (toomCook3Cutoff : Nat) (a b : AzNat) : AzNat :=
  let lenMax := max a.limbs.size b.limbs.size
  if toomCook3Cutoff ≤ lenMax then
    AzNat.mulToomCook3 32 16 a b
  else
    AzNat.mulKaratsuba 16 a b

/-- Time `mulToomCook3DispatchParam` over all pairs at the given cutoff. -/
@[noinline]
def benchAzNatMulToomCook3Dispatch (cutoff : Nat) (pairs : Array (AzNat × AzNat)) :
    IO (UInt64 × Nat) := do
  let t0 ← monoNanos
  let mut checksum : Nat := 0
  for (a, b) in pairs do
    let r := mulToomCook3DispatchParam cutoff a b
    checksum := checksum + r.limbs.size
  let t1 ← monoNanos
  return (t1 - t0, checksum)

/-- Median-of-3 timing for a given cutoff. -/
def benchAzNatMulToomCook3DispatchMedian (cutoff : Nat)
    (pairs : Array (AzNat × AzNat)) : IO UInt64 := do
  let (t1, _) ← benchAzNatMulToomCook3Dispatch cutoff pairs
  let (t2, _) ← benchAzNatMulToomCook3Dispatch cutoff pairs
  let (t3, _) ← benchAzNatMulToomCook3Dispatch cutoff pairs
  if t1 ≤ t2 then
    if t2 ≤ t3 then return t2
    else if t1 ≤ t3 then return t3
    else return t1
  else
    if t1 ≤ t3 then return t1
    else if t2 ≤ t3 then return t3
    else return t2

/-- 1-D grid sweep over the Karatsuba ↔ Toom-Cook 3 dispatch cutoff.

    The heatmap from `az_nat_mul_algorithms_toomcook3` shows Toom-Cook 3 winning
    whenever *either* operand is above ~2200 bits (~35 limbs).  This sweep
    confirms the precise cross-over by timing the dispatched multiplication
    over an unfiltered random distribution.

    Returns the best `cutoff` (in limbs). -/
def tuneAzNatMulToomCook3
    (cutoffs : Array Nat :=
       #[32, 64, 128, 192, 256, 320, 384, 512, 768, 1024])
    (nPairs : Nat := 200) (meanBitLength : Rat := 32768)
    (seed : UInt64 := 42) : IO Nat := do
  IO.eprintln s!"[AzNat-MulToom3] Generating {nPairs} test pairs (mean bit length {meanBitLength})..."
  let pairs := generateAzNatPairsUnfiltered nPairs meanBitLength seed
  IO.eprintln s!"[AzNat-MulToom3] {pairs.size} pairs."
  IO.eprintln ""
  let mut bestCutoff : Nat := 0
  let mut bestTime : UInt64 := UInt64.ofNat (Nat.pow 2 63)
  let mut times : Array UInt64 := #[]
  for i in List.range cutoffs.size do
    let c := cutoffs[i]!
    let time ← benchAzNatMulToomCook3DispatchMedian c pairs
    times := times.push time
    if time < bestTime then
      bestCutoff := c
      bestTime := time
  -- Render a single-row landscape.
  let colWidth := 12
  let header := "  cutoff    " ++ String.join (cutoffs.toList.map fun c =>
    padLeft colWidth s!"{c}")
  IO.eprintln header
  IO.eprintln (String.ofList (List.replicate header.length '-'))
  let mut line := padLeft 11 "µs/run" ++ "  "
  for i in List.range cutoffs.size do
    let ns := times[i]!
    let us := ns.toNat / 1000
    let marker := if cutoffs[i]! == bestCutoff then "*" else " "
    line := line ++ padLeft colWidth (s!"{us}" ++ marker)
  IO.eprintln line
  IO.eprintln ""
  IO.eprintln s!"[AzNat-MulToom3] Best: toomCook3Cutoff = {bestCutoff} ({bestTime}ns)"
  return bestCutoff

-- ── 1-D tuner for the Karatsuba ↔ Toom-Cook 3 squaring dispatch threshold ──

/-- Dispatch between Karatsuba squaring and Toom-Cook 3 squaring based on
    the input length.  Below `toomCook3Cutoff`, use `squareKaratsuba`;
    at-or-above, use `squareToomCook3` with the tuned Karatsuba threshold
    as its fallback. -/
def squareToomCook3DispatchParam (toomCook3Cutoff : Nat) (a : AzNat) : AzNat :=
  if toomCook3Cutoff ≤ a.limbs.size then
    AzNat.squareToomCook3 toomCook3Cutoff AzNat.squareDispatchThreshold a
  else
    AzNat.squareKaratsuba AzNat.squareDispatchThreshold a

/-- Time `squareToomCook3DispatchParam` over all inputs at the given cutoff. -/
@[noinline]
def benchAzNatSquareToomCook3Dispatch (cutoff : Nat) (inputs : Array AzNat) :
    IO (UInt64 × Nat) := do
  let t0 ← monoNanos
  let mut checksum : Nat := 0
  for a in inputs do
    let r := squareToomCook3DispatchParam cutoff a
    checksum := checksum + r.limbs.size
  let t1 ← monoNanos
  return (t1 - t0, checksum)

/-- Median-of-3 timing for a given cutoff. -/
def benchAzNatSquareToomCook3DispatchMedian (cutoff : Nat) (inputs : Array AzNat) :
    IO UInt64 := do
  let (t1, _) ← benchAzNatSquareToomCook3Dispatch cutoff inputs
  let (t2, _) ← benchAzNatSquareToomCook3Dispatch cutoff inputs
  let (t3, _) ← benchAzNatSquareToomCook3Dispatch cutoff inputs
  if t1 ≤ t2 then
    if t2 ≤ t3 then return t2
    else if t1 ≤ t3 then return t3
    else return t1
  else
    if t1 ≤ t3 then return t1
    else if t2 ≤ t3 then return t3
    else return t2

/-- 1-D grid sweep over the Karatsuba ↔ Toom-Cook 3 squaring cutoff.

    Squaring has no balance dimension (single operand → halves differ by
    at most one limb), so this is a clean 1-D search.  Returns the best
    `cutoff` (in limbs). -/
def tuneAzNatSquareToomCook3
    (cutoffs : Array Nat :=
       #[32, 64, 128, 192, 256, 320, 384, 512, 768, 1024])
    (nInputs : Nat := 400) (meanBitLength : Rat := 32768)
    (seed : UInt64 := 42) : IO Nat := do
  IO.eprintln s!"[AzNat-SquareToom3] Generating {nInputs} test inputs (mean bit length {meanBitLength})..."
  let inputs := generateAzNatSingles nInputs meanBitLength seed
  IO.eprintln s!"[AzNat-SquareToom3] {inputs.size} inputs."
  IO.eprintln ""
  let mut bestCutoff : Nat := 0
  let mut bestTime : UInt64 := UInt64.ofNat (Nat.pow 2 63)
  let mut times : Array UInt64 := #[]
  for i in List.range cutoffs.size do
    let c := cutoffs[i]!
    let time ← benchAzNatSquareToomCook3DispatchMedian c inputs
    times := times.push time
    if time < bestTime then
      bestCutoff := c
      bestTime := time
  -- Render a single-row landscape.
  let colWidth := 12
  let header := "  cutoff    " ++ String.join (cutoffs.toList.map fun c =>
    padLeft colWidth s!"{c}")
  IO.eprintln header
  IO.eprintln (String.ofList (List.replicate header.length '-'))
  let mut line := padLeft 11 "µs/run" ++ "  "
  for i in List.range cutoffs.size do
    let ns := times[i]!
    let us := ns.toNat / 1000
    let marker := if cutoffs[i]! == bestCutoff then "*" else " "
    line := line ++ padLeft colWidth (s!"{us}" ++ marker)
  IO.eprintln line
  IO.eprintln ""
  IO.eprintln s!"[AzNat-SquareToom3] Best: toomCook3Cutoff = {bestCutoff} ({bestTime}ns)"
  return bestCutoff

-- ── Milestone 5 (`docs/toom_cook_plan.md`): Toom-4 crossovers and the unbalanced bands ──

/-- An `AzNat` of exactly `n` random limbs (the top limb has its high bit set). -/
def randomAzNatLimbs (n : Nat) (g : SplitMix64) : AzNat × SplitMix64 := Id.run do
  let mut g := g
  let mut limbs : Array UInt64 := #[]
  for _ in List.range n do
    let (x, g') := SplitMix64.next g
    g := g'
    limbs := limbs.push x
  if 0 < n then
    limbs := limbs.set! (n - 1) (limbs[n - 1]! ||| ((1 : UInt64) <<< 63))
  return (AzNat.ofLimbs limbs, g)

/-- `reps` random pairs of exactly `lenA` and `lenB` limbs. -/
def randomLimbPairs (reps lenA lenB : Nat) (g : SplitMix64) :
    Array (AzNat × AzNat) × SplitMix64 := Id.run do
  let mut g := g
  let mut pairs : Array (AzNat × AzNat) := #[]
  for _ in List.range reps do
    let (a, g1) := randomAzNatLimbs lenA g
    let (b, g2) := randomAzNatLimbs lenB g1
    g := g2
    pairs := pairs.push (a, b)
  return (pairs, g)

/-- Time `f` over all inputs once (the checksum keeps the results live). -/
@[noinline]
def timeAzNatOnce {α : Type} (f : α → AzNat) (inputs : Array α) : IO (UInt64 × Nat) := do
  let t0 ← monoNanos
  let mut checksum : Nat := 0
  for x in inputs do
    let r := f x
    checksum := checksum + r.limbs.size
  let t1 ← monoNanos
  return (t1 - t0, checksum)

/-- Median-of-three timing of `f` over all inputs, in nanoseconds. -/
def timeAzNatMedian3 {α : Type} (f : α → AzNat) (inputs : Array α) : IO UInt64 := do
  let (t1, _) ← timeAzNatOnce f inputs
  let (t2, _) ← timeAzNatOnce f inputs
  let (t3, _) ← timeAzNatOnce f inputs
  return max (min t1 t2) (min (max t1 t2) t3)

/-- Microseconds per input from a total in nanoseconds. -/
private def usPer (ns : UInt64) (count : Nat) : Nat := ns.toNat / (1000 * max count 1)

/-- Multiplication with explicit thresholds (the production `mul` with `th` in place of the
defaults). -/
def mulWithThresholds (th : MulThresholds) (a b : AzNat) : AzNat :=
  AzNat.ofLimbs (mulLimbsWith th a.limbs b.limbs 0 a.limbs.size 0 b.limbs.size
    (Nat.zero_add _ ▸ Nat.le_refl _) (Nat.zero_add _ ▸ Nat.le_refl _))

/-- **Toom-4 multiplication crossover.**  For each size `n`, on pairs of exactly `n` limbs,
Toom-3 all the way down against Toom-4 at the top level only (its recursive calls on
`⌈n/4⌉ + 1` limbs fall back to Toom-3).  The crossover is the first size at which Toom-4
wins; that is the value for `MulThresholds.toomCook4`. -/
def tuneAzNatMulToomCook4 (th : MulThresholds := defaultMulThresholds)
    (sizes : Array Nat := #[256, 320, 384, 448, 512, 640, 768, 896, 1024, 1280, 1536, 2048, 3072,
      4096])
    (workLimbs : Nat := 16384) (seed : UInt64 := 42) : IO Unit := do
  IO.eprintln s!"[AzNat-MulToom4] Toom-3 (cutoff {th.toomCook3}, Karatsuba below {th.schoolbook}) vs Toom-4 at the top level; µs per product"
  IO.eprintln (padLeft 6 "limbs" ++ padLeft 7 "pairs" ++ padLeft 12 "toom3" ++ padLeft 12 "toom4"
    ++ padLeft 10 "t4/t3 %")
  let mut g := mkSplitMix64 seed
  for n in sizes do
    let reps := max 4 (workLimbs / n)
    let (pairs, g') := randomLimbPairs reps n n g
    g := g'
    let t3 ← timeAzNatMedian3 (fun p : AzNat × AzNat => mulToomCook3 th.toomCook3 th.schoolbook p.1 p.2)
      pairs
    let t4 ← timeAzNatMedian3 (fun p : AzNat × AzNat => mulToomCook4 n th.toomCook3 th.schoolbook p.1 p.2)
      pairs
    let pct := (100 * t4.toNat) / max t3.toNat 1
    let marker := if t4 < t3 then "  <- toom4 wins" else ""
    IO.eprintln (padLeft 6 s!"{n}" ++ padLeft 7 s!"{reps}" ++ padLeft 12 s!"{usPer t3 reps}"
      ++ padLeft 12 s!"{usPer t4 reps}" ++ padLeft 10 s!"{pct}" ++ marker)

/-- **Toom-4 squaring crossover**, as `tuneAzNatMulToomCook4` for squaring. -/
def tuneAzNatSquareToomCook4 (toomCook3Cutoff : Nat := squareDispatchToomCook3Cutoff)
    (karatsubaCutoff : Nat := squareDispatchThreshold)
    (sizes : Array Nat := #[128, 192, 256, 320, 384, 448, 512, 640, 768, 1024, 1280, 1536, 2048,
      3072, 4096])
    (workLimbs : Nat := 16384) (seed : UInt64 := 42) : IO Unit := do
  IO.eprintln s!"[AzNat-SquareToom4] Toom-3 squaring (cutoff {toomCook3Cutoff}, Karatsuba below {karatsubaCutoff}) vs Toom-4 at the top level; µs per square"
  IO.eprintln (padLeft 6 "limbs" ++ padLeft 7 "inputs" ++ padLeft 12 "toom3" ++ padLeft 12 "toom4"
    ++ padLeft 10 "t4/t3 %")
  let mut g := mkSplitMix64 seed
  for n in sizes do
    let reps := max 4 (workLimbs / n)
    let mut inputs : Array AzNat := #[]
    for _ in List.range reps do
      let (a, g') := randomAzNatLimbs n g
      g := g'
      inputs := inputs.push a
    let t3 ← timeAzNatMedian3 (fun a => squareToomCook3 toomCook3Cutoff karatsubaCutoff a) inputs
    let t4 ← timeAzNatMedian3 (fun a => squareToomCook4 n toomCook3Cutoff karatsubaCutoff a) inputs
    let pct := (100 * t4.toNat) / max t3.toNat 1
    let marker := if t4 < t3 then "  <- toom4 wins" else ""
    IO.eprintln (padLeft 6 s!"{n}" ++ padLeft 7 s!"{reps}" ++ padLeft 12 s!"{usPer t3 reps}"
      ++ padLeft 12 s!"{usPer t4 reps}" ++ padLeft 10 s!"{pct}" ++ marker)

/-- The five strategies `mulLimbsOrdered` chooses between, on `AzNat`s with
`b.limbs.size ≤ a.limbs.size`: schoolbook, the balanced ladder on `b` padded to `a`'s length,
Toom-(3,2), Toom-(4,2), and the chunk loop. -/
def unbalancedStrategy (th : MulThresholds) (which : Nat) (a b : AzNat) : AzNat :=
  match which with
  | 0 => AzNat.ofLimbs (schoolbookMulLimbs a.limbs b.limbs 0 a.limbs.size 0 b.limbs.size
      (Nat.zero_add _ ▸ Nat.le_refl _) (Nat.zero_add _ ▸ Nat.le_refl _))
  | 1 => AzNat.ofLimbs (balancedMulLimbs th a.limbs (truncatePad b.limbs a.limbs.size) 0 0
      a.limbs.size (Nat.zero_add _ ▸ Nat.le_refl _) (by rw [truncatePad_size]; omega))
  | 2 => AzNat.ofLimbs (toom32MulLimbs (balancedMul th) a.limbs b.limbs 0 a.limbs.size 0
      b.limbs.size (Nat.zero_add _ ▸ Nat.le_refl _) (Nat.zero_add _ ▸ Nat.le_refl _))
  | 3 => AzNat.ofLimbs (toom42MulLimbs (balancedMul th) a.limbs b.limbs 0 a.limbs.size 0
      b.limbs.size (Nat.zero_add _ ▸ Nat.le_refl _) (Nat.zero_add _ ▸ Nat.le_refl _))
  | _ => AzNat.ofLimbs (mulChunksLimbs (balancedMul th) a.limbs b.limbs 0 a.limbs.size 0
      b.limbs.size (Nat.zero_add _ ▸ Nat.le_refl _) (Nat.zero_add _ ▸ Nat.le_refl _))

/-- **The unbalanced bands.**  For each shorter length `lenB` and ratio `r/8`, pairs of exactly
`lenA = lenB·r/8` and `lenB` limbs, timed under each of the five strategies.  The winners
determine the ratio bands of `mulLimbsOrdered` and `MulThresholds.unbalanced`. -/
def tuneAzNatUnbalanced (th : MulThresholds := defaultMulThresholds)
    (lenBs : Array Nat := #[32, 48, 64, 96, 128, 192, 256, 512])
    (ratios8 : Array Nat := #[8, 9, 10, 11, 12, 13, 14, 15, 16, 18, 20, 22, 24, 32])
    (workLimbs : Nat := 8192) (seed : UInt64 := 42) : IO Unit := do
  IO.eprintln s!"[AzNat-Unbalanced] thresholds schoolbook {th.schoolbook}, toom3 {th.toomCook3}, toom4 {th.toomCook4}; µs per product"
  let names := #["school", "padded", "toom32", "toom42", "chunks"]
  IO.eprintln (padLeft 6 "lenB" ++ padLeft 6 "lenA" ++ padLeft 7 "ratio" ++ padLeft 6 "pairs"
    ++ String.join (names.toList.map (padLeft 10 ·)) ++ "  winner")
  let mut g := mkSplitMix64 seed
  for lenB in lenBs do
    for r in ratios8 do
      let lenA := lenB * r / 8
      let reps := max 4 (workLimbs / lenA)
      let (pairs, g') := randomLimbPairs reps lenA lenB g
      g := g'
      let mut times : Array UInt64 := #[]
      for which in List.range names.size do
        let t ← timeAzNatMedian3 (fun p : AzNat × AzNat => unbalancedStrategy th which p.1 p.2)
          pairs
        times := times.push t
      let mut best := 0
      for i in List.range names.size do
        if times[i]! < times[best]! then best := i
      let ratioStr := s!"{r / 8}.{(r % 8) * 125}"
      IO.eprintln (padLeft 6 s!"{lenB}" ++ padLeft 6 s!"{lenA}" ++ padLeft 7 ratioStr
        ++ padLeft 6 s!"{reps}"
        ++ String.join (times.toList.map fun t => padLeft 10 s!"{usPer t reps}")
        ++ "  " ++ names[best]!)

/-- **Old against new dispatcher** on the geometric random distribution: the pre-milestone-4
`mulDispatchParam 16 1 4 256` (pad to the longer length, schoolbook below ratio 1/4) against
`mulWithThresholds th`. -/
def tuneAzNatMulDispatchCompare (th : MulThresholds := defaultMulThresholds)
    (meanBitLengths : Array Rat := #[4096, 16384, 65536, 262144]) (nPairs : Nat := 100)
    (seed : UInt64 := 42) : IO Unit := do
  IO.eprintln s!"[AzNat-Dispatch] old `mulDispatchParam 16 1 4 256` vs new dispatcher (schoolbook {th.schoolbook}, toom3 {th.toomCook3}, toom4 {th.toomCook4}, unbalanced {th.unbalanced}); µs per product"
  IO.eprintln (padLeft 10 "mean bits" ++ padLeft 7 "pairs" ++ padLeft 12 "old" ++ padLeft 12 "new"
    ++ padLeft 10 "new/old %")
  for m in meanBitLengths do
    let pairs := generateAzNatPairsUnfiltered nPairs m seed
    let tOld ← timeAzNatMedian3 (fun p : AzNat × AzNat => mulDispatchParam 16 1 4 256 p.1 p.2) pairs
    let tNew ← timeAzNatMedian3 (fun p : AzNat × AzNat => mulWithThresholds th p.1 p.2) pairs
    let pct := (100 * tNew.toNat) / max tOld.toNat 1
    IO.eprintln (padLeft 10 s!"{m.floor}" ++ padLeft 7 s!"{pairs.size}"
      ++ padLeft 12 s!"{usPer tOld pairs.size}" ++ padLeft 12 s!"{usPer tNew pairs.size}"
      ++ padLeft 10 s!"{pct}")

/-- **Toom-4 cutoff sweep on the production multiplication dispatcher**, over the geometric
random distribution of balanced pairs (limb ratio at least `balanceRatio/100`).  The last
cutoff should be larger than any input, so it measures the ladder without Toom-4. -/
def tuneAzNatMulToomCook4Dispatch (th : MulThresholds := defaultMulThresholds)
    (cutoffs : Array Nat := #[256, 320, 384, 448, 512, 640, 768, 1024, 1536, 2048, 1000000])
    (nPairs : Nat := 200) (meanBitLength : Rat := 65536) (balanceRatio : Nat := 75)
    (seed : UInt64 := 42) : IO Unit := do
  IO.eprintln s!"[AzNat-MulToom4Dispatch] {nPairs} balanced pairs, mean bit length {meanBitLength}; total ms per cutoff"
  let pairs := generateBalancedAzNatPairs nPairs meanBitLength balanceRatio seed
  let mut line := ""
  let mut best := 0
  let mut bestTime : UInt64 := UInt64.ofNat (Nat.pow 2 63)
  let mut times : Array UInt64 := #[]
  for c in cutoffs do
    let t ← timeAzNatMedian3 (fun p : AzNat × AzNat =>
      mulWithThresholds { th with toomCook4 := c } p.1 p.2) pairs
    times := times.push t
    if t < bestTime then
      bestTime := t
      best := c
  IO.eprintln ("  cutoff  " ++ String.join (cutoffs.toList.map fun c => padLeft 10 s!"{c}"))
  for i in List.range cutoffs.size do
    let marker := if cutoffs[i]! == best then "*" else " "
    line := line ++ padLeft 10 (s!"{times[i]!.toNat / 1000000}" ++ marker)
  IO.eprintln ("  ms      " ++ line)
  IO.eprintln s!"[AzNat-MulToom4Dispatch] Best: toomCook4 = {best}"

/-- **Toom-4 cutoff sweep on the production squaring dispatcher**, over the geometric random
distribution. -/
def tuneAzNatSquareToomCook4Dispatch (schoolbook : Nat := squareDispatchThreshold)
    (toomCook3 : Nat := squareDispatchToomCook3Cutoff)
    (cutoffs : Array Nat := #[128, 192, 256, 320, 384, 448, 512, 640, 768, 1024, 1536, 2048,
      1000000])
    (nInputs : Nat := 400) (meanBitLength : Rat := 65536) (seed : UInt64 := 42) : IO Unit := do
  IO.eprintln s!"[AzNat-SquareToom4Dispatch] {nInputs} inputs, mean bit length {meanBitLength}, schoolbook {schoolbook}, toomCook3 {toomCook3}; total ms per cutoff"
  let inputs := generateAzNatSingles nInputs meanBitLength seed
  let mut line := ""
  let mut best := 0
  let mut bestTime : UInt64 := UInt64.ofNat (Nat.pow 2 63)
  let mut times : Array UInt64 := #[]
  for c in cutoffs do
    let t ← timeAzNatMedian3 (fun a => squareDispatchParam schoolbook toomCook3 c squareDispatchFFTCutoff a) inputs
    times := times.push t
    if t < bestTime then
      bestTime := t
      best := c
  IO.eprintln ("  cutoff  " ++ String.join (cutoffs.toList.map fun c => padLeft 10 s!"{c}"))
  for i in List.range cutoffs.size do
    let marker := if cutoffs[i]! == best then "*" else " "
    line := line ++ padLeft 10 (s!"{times[i]!.toNat / 1000000}" ++ marker)
  IO.eprintln ("  ms      " ++ line)
  IO.eprintln s!"[AzNat-SquareToom4Dispatch] Best: toomCook4 = {best}"

/-- Per-size A/B table for two multiplication strategies, each given the size `n` (so a
strategy can be "the variant at the top level only": pass `n` as its cutoff). -/
def crossoverTableMul (tag nameA nameB : String) (fA fB : Nat → AzNat → AzNat → AzNat)
    (sizes : Array Nat) (workLimbs : Nat) (seed : UInt64) : IO Unit := do
  IO.eprintln s!"[{tag}] {nameA} vs {nameB}; µs per product"
  IO.eprintln (padLeft 6 "limbs" ++ padLeft 7 "pairs" ++ padLeft 12 nameA ++ padLeft 12 nameB
    ++ padLeft 10 "B/A %")
  let mut g := mkSplitMix64 seed
  for n in sizes do
    let reps := max 4 (workLimbs / n)
    let (pairs, g') := randomLimbPairs reps n n g
    g := g'
    let tA ← timeAzNatMedian3 (fun p : AzNat × AzNat => fA n p.1 p.2) pairs
    let tB ← timeAzNatMedian3 (fun p : AzNat × AzNat => fB n p.1 p.2) pairs
    let pct := (100 * tB.toNat) / max tA.toNat 1
    let marker := if tB < tA then s!"  <- {nameB} wins" else ""
    IO.eprintln (padLeft 6 s!"{n}" ++ padLeft 7 s!"{reps}" ++ padLeft 12 s!"{usPer tA reps}"
      ++ padLeft 12 s!"{usPer tB reps}" ++ padLeft 10 s!"{pct}" ++ marker)

/-- Per-size A/B table for two squaring strategies. -/
def crossoverTableSquare (tag nameA nameB : String) (fA fB : Nat → AzNat → AzNat)
    (sizes : Array Nat) (workLimbs : Nat) (seed : UInt64) : IO Unit := do
  IO.eprintln s!"[{tag}] {nameA} vs {nameB}; µs per square"
  IO.eprintln (padLeft 6 "limbs" ++ padLeft 7 "inputs" ++ padLeft 12 nameA ++ padLeft 12 nameB
    ++ padLeft 10 "B/A %")
  let mut g := mkSplitMix64 seed
  for n in sizes do
    let reps := max 4 (workLimbs / n)
    let mut inputs : Array AzNat := #[]
    for _ in List.range reps do
      let (a, g') := randomAzNatLimbs n g
      g := g'
      inputs := inputs.push a
    let tA ← timeAzNatMedian3 (fA n) inputs
    let tB ← timeAzNatMedian3 (fB n) inputs
    let pct := (100 * tB.toNat) / max tA.toNat 1
    let marker := if tB < tA then s!"  <- {nameB} wins" else ""
    IO.eprintln (padLeft 6 s!"{n}" ++ padLeft 7 s!"{reps}" ++ padLeft 12 s!"{usPer tA reps}"
      ++ padLeft 12 s!"{usPer tB reps}" ++ padLeft 10 s!"{pct}" ++ marker)

/-- **Karatsuba crossover**: schoolbook against Karatsuba at the top level only (its halves
schoolbook). -/
def tuneAzNatKaratsubaCrossover (th : MulThresholds := defaultMulThresholds)
    (sizes : Array Nat := #[8, 12, 16, 24, 32, 48, 64, 80, 96, 112, 128, 160, 192, 256])
    (workLimbs : Nat := 65536) (seed : UInt64 := 42) : IO Unit :=
  crossoverTableMul "AzNat-KaraCross" "school" "kara-top"
    (fun _ a b => unbalancedStrategy th 0 a b) (fun n a b => mulKaratsuba n a b)
    sizes workLimbs seed

/-- **Toom-3 crossover**: recursive Karatsuba (schoolbook below `th.schoolbook`) against Toom-3
at the top level only (its five products by that Karatsuba). -/
def tuneAzNatToomCook3Crossover (th : MulThresholds := defaultMulThresholds)
    (sizes : Array Nat := #[48, 64, 96, 128, 160, 192, 256, 320, 384, 512, 768, 1024])
    (workLimbs : Nat := 65536) (seed : UInt64 := 42) : IO Unit :=
  crossoverTableMul "AzNat-Toom3Cross" "kara" "toom3-top"
    (fun _ a b => mulKaratsuba th.schoolbook a b) (fun n a b => mulToomCook3 n th.schoolbook a b)
    sizes workLimbs seed

/-- **Karatsuba squaring crossover**: schoolbook squaring against Karatsuba squaring at the top
level only. -/
def tuneAzNatSquareKaratsubaCrossover
    (sizes : Array Nat := #[8, 12, 16, 24, 32, 48, 64, 80, 96, 112, 128, 160, 192, 256])
    (workLimbs : Nat := 65536) (seed : UInt64 := 42) : IO Unit :=
  crossoverTableSquare "AzNat-SqKaraCross" "school" "kara-top"
    (fun n a => squareKaratsuba (n + 1) a) (fun n a => squareKaratsuba n a) sizes workLimbs seed

/-- **Toom-3 squaring crossover**: recursive Karatsuba squaring (schoolbook below
`karatsubaCutoff`) against Toom-3 squaring at the top level only. -/
def tuneAzNatSquareToomCook3Crossover (karatsubaCutoff : Nat := squareDispatchThreshold)
    (sizes : Array Nat := #[48, 64, 96, 128, 160, 192, 256, 320, 384, 512, 768, 1024])
    (workLimbs : Nat := 65536) (seed : UInt64 := 42) : IO Unit :=
  crossoverTableSquare "AzNat-SqToom3Cross" "kara" "toom3-top"
    (fun _ a => squareKaratsuba karatsubaCutoff a)
    (fun n a => squareToomCook3 n karatsubaCutoff a) sizes workLimbs seed

/-- Render a 2-D grid of total milliseconds with the minimum starred. -/
private def printGrid (rowLabel colLabel : String) (rows cols : Array Nat)
    (times : Array (Array UInt64)) : IO Unit := do
  let mut best : UInt64 := UInt64.ofNat (Nat.pow 2 63)
  for r in times do
    for t in r do
      if t < best then best := t
  IO.eprintln (padLeft 10 s!"{rowLabel}\\{colLabel}"
    ++ String.join (cols.toList.map fun c => padLeft 9 s!"{c}"))
  for i in List.range rows.size do
    let mut line := padLeft 10 s!"{rows[i]!}"
    for j in List.range cols.size do
      let t := (times[i]!)[j]!
      let marker := if t == best then "*" else " "
      line := line ++ padLeft 9 (s!"{t.toNat / 1000000}" ++ marker)
    IO.eprintln line

/-- **The balanced ladder's lower cutoffs**: a 2-D sweep of `(schoolbook, toomCook3)` on the
production multiplication dispatcher over balanced random pairs. -/
def tuneAzNatMulLadder2D (th : MulThresholds := defaultMulThresholds)
    (schoolbooks : Array Nat := #[16, 32, 48, 64, 80, 96, 128])
    (toomCook3s : Array Nat := #[128, 192, 256, 320, 384, 512])
    (nPairs : Nat := 200) (meanBitLength : Rat := 16384) (balanceRatio : Nat := 75)
    (seed : UInt64 := 42) : IO Unit := do
  IO.eprintln s!"[AzNat-MulLadder2D] {nPairs} balanced pairs, mean bit length {meanBitLength}, toomCook4 {th.toomCook4}; total ms"
  let pairs := generateBalancedAzNatPairs nPairs meanBitLength balanceRatio seed
  let mut times : Array (Array UInt64) := #[]
  for s in schoolbooks do
    let mut row : Array UInt64 := #[]
    for t3 in toomCook3s do
      let t ← timeAzNatMedian3 (fun p : AzNat × AzNat =>
        mulWithThresholds { th with schoolbook := s, toomCook3 := t3 } p.1 p.2) pairs
      row := row.push t
    times := times.push row
  printGrid "school" "toom3" schoolbooks toomCook3s times

/-- **The squaring ladder's lower cutoffs**: a 2-D sweep of `(schoolbook, toomCook3)` on the
production squaring dispatcher. -/
def tuneAzNatSquareLadder2D (toomCook4Cutoff : Nat := squareDispatchToomCook4Cutoff)
    (schoolbooks : Array Nat := #[16, 32, 48, 64, 80, 96, 128])
    (toomCook3s : Array Nat := #[64, 96, 128, 192, 256, 320, 384])
    (nInputs : Nat := 400) (meanBitLength : Rat := 16384) (seed : UInt64 := 42) : IO Unit := do
  IO.eprintln s!"[AzNat-SquareLadder2D] {nInputs} inputs, mean bit length {meanBitLength}, toomCook4 {toomCook4Cutoff}; total ms"
  let inputs := generateAzNatSingles nInputs meanBitLength seed
  let mut times : Array (Array UInt64) := #[]
  for s in schoolbooks do
    let mut row : Array UInt64 := #[]
    for t3 in toomCook3s do
      let t ← timeAzNatMedian3 (fun a => squareDispatchParam s t3 toomCook4Cutoff squareDispatchFFTCutoff a) inputs
      row := row.push t
    times := times.push row
  printGrid "school" "toom3" schoolbooks toomCook3s times

-- ── The FFT stage (`docs/fft_plan.md`, item 4): crossover against the Toom ladder ──

/-- **FFT multiplication crossover**: the Toom ladder against `fftMul` (with that ladder for the
pointwise products) on pairs of exactly `n` limbs. -/
def tuneAzNatFFTCrossover (th : MulThresholds := defaultMulThresholds) (kAdj : Nat := ssKAdjust)
    (sizes : Array Nat := #[1024, 1536, 2048, 3072, 4096, 6144, 8192, 12288, 16384, 32768])
    (workLimbs : Nat := 65536) (seed : UInt64 := 42) : IO Unit :=
  crossoverTableMul "AzNat-FFTCross" "toom" s!"fft(k+{kAdj})"
    (fun _ a b => toomLadderMul th a b) (fun _ a b => fftMulWith kAdj (toomLadderMul th) a b)
    sizes workLimbs seed

/-- **FFT squaring crossover**: the Toom squaring ladder against `fftSquare`. -/
def tuneAzNatSquareFFTCrossover (schoolbook : Nat := squareDispatchThreshold)
    (toomCook3 : Nat := squareDispatchToomCook3Cutoff)
    (toomCook4 : Nat := squareDispatchToomCook4Cutoff) (kAdj : Nat := ssKAdjust)
    (sizes : Array Nat := #[1024, 1536, 2048, 3072, 4096, 6144, 8192, 12288, 16384, 32768])
    (workLimbs : Nat := 65536) (seed : UInt64 := 42) : IO Unit :=
  crossoverTableSquare "AzNat-SqFFTCross" "toom" s!"fft(k+{kAdj})"
    (fun _ a => toomSquareLadder schoolbook toomCook3 toomCook4 a)
    (fun _ a => fftSquareWith kAdj (toomSquareLadder schoolbook toomCook3 toomCook4) a)
    sizes workLimbs seed

/-- **FFT cutoff sweep on the production multiplication dispatcher** over balanced random
pairs; the last cutoff disables the FFT. -/
def tuneAzNatFFTDispatch (th : MulThresholds := defaultMulThresholds)
    (cutoffs : Array Nat := #[1024, 2048, 3072, 4096, 6144, 8192, 12288, 16384, 1000000])
    (nPairs : Nat := 40) (meanBitLength : Rat := 524288) (balanceRatio : Nat := 75)
    (seed : UInt64 := 42) : IO Unit := do
  IO.eprintln s!"[AzNat-FFTDispatch] {nPairs} balanced pairs, mean bit length {meanBitLength}; total ms per cutoff"
  let pairs := generateBalancedAzNatPairs nPairs meanBitLength balanceRatio seed
  let mut line := ""
  let mut best := 0
  let mut bestTime : UInt64 := UInt64.ofNat (Nat.pow 2 63)
  let mut times : Array UInt64 := #[]
  for c in cutoffs do
    let t ← timeAzNatMedian3 (fun p : AzNat × AzNat =>
      mulWithThresholds { th with fft := c } p.1 p.2) pairs
    times := times.push t
    if t < bestTime then
      bestTime := t
      best := c
  IO.eprintln ("  cutoff  " ++ String.join (cutoffs.toList.map fun c => padLeft 10 s!"{c}"))
  for i in List.range cutoffs.size do
    let marker := if cutoffs[i]! == best then "*" else " "
    line := line ++ padLeft 10 (s!"{(times[i]!).toNat / 1000000}" ++ marker)
  IO.eprintln ("  ms      " ++ line)
  IO.eprintln s!"[AzNat-FFTDispatch] Best: fft = {best}"

/-- Time one stage over all pairs (median of three), in microseconds per pair. -/
private def stageUs {α β : Type} (f : α → β) (touch : β → Nat) (inputs : Array α) : IO Nat := do
  let once : IO UInt64 := do
    let t0 ← monoNanos
    let mut acc : Nat := 0
    for x in inputs do
      acc := acc + touch (f x)
    let t1 ← monoNanos
    if acc == 0 then IO.eprintln "" else pure ()
    return t1 - t0
  let t1 ← once
  let t2 ← once
  let t3 ← once
  let med := max (min t1 t2) (min (max t1 t2) t3)
  return med.toNat / (1000 * max inputs.size 1)

open Azurite.AzFermat in
/-- **Stage profile of `fftMul`** on pairs of exactly `n` limbs with the digit-count
adjustment `kAdj`: weighting, the two forward transforms, the pointwise products, the backward
transform, and coefficient recovery plus assembly, each in µs per product, next to the whole
`fftMulWith` and the Toom ladder. -/
def profileAzNatFFT (n : Nat) (kAdj : Nat) (th : MulThresholds := defaultMulThresholds)
    (reps : Nat := 4) (seed : UInt64 := 42) : IO Unit := do
  let p := ssParamsWith kAdj (2 * n)
  let k := p.1
  let w := p.2
  have hw0 : 0 < w := ssParamsWith_pos kAdj (2 * n)
  let N := ssFermatExponent k w
  have hN : 2 * (64 * w) + (k + 1) ≤ N := ssFermatExponent_ge k w
  have : NeZero N := ⟨by omega⟩
  have : NeZero (64 * w * 2 ^ (k + 1)) := ⟨Nat.pos_iff_ne_zero.mp (by positivity)⟩
  let eθ := N / 2 ^ (k + 1)
  IO.eprintln s!"[AzNat-FFTProfile] n = {n} limbs, kAdj = {kAdj}: K = 2^{k + 1} = {2 ^ (k + 1)} digits of w = {w} limbs (M = {64 * w} bits), N = {N} bits ({N / 64 + 1} limbs), {reps} pairs"
  let (pairs, _) := randomLimbPairs reps n n (mkSplitMix64 seed)
  let mulFn := toomLadderMul th
  -- the stages, on arrays that carry their size
  let V := { a : Array (AzFermat N) // a.size = 2 ^ (k + 1) }
  let weightV : AzNat → V := fun a => ⟨ssWeighted k w N eθ a, ssWeighted_size k w N eθ a⟩
  let fwdV : V → V := fun v => ⟨forwardFFT (2 * eθ) (k + 1) v.1 v.2, forwardFFT_size _ _ _ _⟩
  let prodV : V → V → V := fun fa fb =>
    ⟨Array.ofFn fun r : Fin (2 ^ (k + 1)) =>
      mulWith mulFn (fa.1[r.val]'(by rw [fa.2]; exact r.isLt)) (fb.1[r.val]'(by rw [fb.2]; exact r.isLt)),
     Array.size_ofFn⟩
  let bwdV : V → V := fun v => ⟨backwardFFT (2 * eθ) (k + 1) v.1 v.2, backwardFFT_size _ _ _ _⟩
  let finishV : V → AzNat := fun v =>
    (ssAssemble (64 * w) (64 * w * 2 ^ (k + 1)) (Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _))
      (ssCoefficients k w N (64 * w * 2 ^ (k + 1)) eθ v.1 v.2)).val
  let touchV : V → Nat := fun v => v.1.size + (v.1[0]?.map fun x => x.val.limbs.size).getD 0
  -- stage inputs
  let weighted : Array (V × V) := pairs.map fun q => (weightV q.1, weightV q.2)
  let transformed : Array (V × V) := weighted.map fun q => (fwdV q.1, fwdV q.2)
  let products : Array V := transformed.map fun q => prodV q.1 q.2
  let back : Array V := products.map bwdV
  let tWeight ← stageUs (fun q : AzNat × AzNat => (weightV q.1, weightV q.2))
    (fun q => touchV q.1 + touchV q.2) pairs
  let tForward ← stageUs (fun q : V × V => (fwdV q.1, fwdV q.2))
    (fun q => touchV q.1 + touchV q.2) weighted
  let tProducts ← stageUs (fun q : V × V => prodV q.1 q.2) touchV transformed
  let tBackward ← stageUs bwdV touchV products
  let tFinish ← stageUs finishV (fun x => x.limbs.size) back
  let tAll ← stageUs (fun q : AzNat × AzNat => fftMulWith kAdj mulFn q.1 q.2)
    (fun x => x.limbs.size) pairs
  let tToom ← stageUs (fun q : AzNat × AzNat => toomLadderMul th q.1 q.2)
    (fun x => x.limbs.size) pairs
  let sum := tWeight + tForward + tProducts + tBackward + tFinish
  IO.eprintln (padLeft 22 "stage" ++ padLeft 12 "µs" ++ padLeft 8 "%")
  let row := fun (name : String) (t : Nat) =>
    IO.eprintln (padLeft 22 name ++ padLeft 12 s!"{t}" ++ padLeft 8 s!"{100 * t / max sum 1}")
  row "weighting" tWeight
  row "forward FFTs (2)" tForward
  row "pointwise products" tProducts
  row "backward FFT" tBackward
  row "coefficients+assembly" tFinish
  row "(sum of stages)" sum
  IO.eprintln (padLeft 22 "fftMulWith total" ++ padLeft 12 s!"{tAll}")
  IO.eprintln (padLeft 22 "Toom ladder" ++ padLeft 12 s!"{tToom}")
