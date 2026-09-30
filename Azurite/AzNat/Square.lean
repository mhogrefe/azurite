/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzNat.Square.Schoolbook
import Azurite.AzNat.Square.Karatsuba
import Azurite.AzNat.Square.ToomCook3
import Azurite.AzNat.Square.ToomCook4
import Azurite.AzNat.Mul.SchonhageStrassen

namespace Azurite.AzNat

-- ── Limb-level dispatcher and AzNat wrapper ─────────────────────────────────

/-- Default minimum-length threshold for Karatsuba squaring (in 64-bit limbs).
    Below this size the `squareLimbs` dispatcher picks `schoolbookSquareLimbs`;
    above it, `karatsubaSquareLimbs`. Unlike `mulDispatchThreshold` there is
    no balance ratio because squaring takes a single operand — the recursive
    split's two halves always differ in length by at most one.  Retuned in the
    milestone 5 sweep (`tune_aznat_square_karatsuba_crossover`,
    `tune_aznat_square_ladder_2d`): schoolbook squaring and top-level Karatsuba
    squaring tie at 96 limbs, and the 2-D ladder sweep is best at 96. -/
def squareDispatchThreshold : Nat := 96

/-- Default cutoff (in limbs) for switching Karatsuba squaring → Toom-Cook 3
    squaring.  Retuned in the milestone 5 sweep
    (`tune_aznat_square_toomcook3_crossover`, `tune_aznat_square_ladder_2d`):
    top-level Toom-3 squaring ties with Karatsuba squaring at 192–256 limbs and
    wins from 320; the 2-D ladder sweep is best at 320. -/
def squareDispatchToomCook3Cutoff : Nat := 320

/-- Default cutoff (in limbs) for Toom-4 squaring over Toom-3 squaring
    (`tune_aznat_square_toomcook4_dispatch`): the dispatcher sweep is flat from
    448 to 1024 limbs with its minimum at 512–768. -/
def squareDispatchToomCook4Cutoff : Nat := 512

/-- Default cutoff (in limbs) for the Schönhage–Strassen squaring over Toom-4
    squaring.  Measured (`tune_aznat_square_fft_crossover`, `docs/fft_plan.md`):
    the FFT ties Toom-4 squaring at 32768 limbs and wins by 10 % at 49152 and
    14 % at 65536. -/
def squareDispatchFFTCutoff : Nat := 32768

/-- The Toom squaring ladder: schoolbook, Karatsuba, Toom-3 or Toom-4 by size. -/
def toomSquareLadderLimbs (minThreshold toomCook3Cutoff toomCook4Cutoff : Nat)
    (a : Array UInt64) (lo len : Nat) (hA : lo + len ≤ a.size) : Array UInt64 :=
  if toomCook4Cutoff ≤ len then
    toomCook4SquareLimbs toomCook4Cutoff toomCook3Cutoff minThreshold a lo len hA
  else if toomCook3Cutoff ≤ len then
    toomCook3SquareLimbs toomCook3Cutoff minThreshold a lo len hA
  else if minThreshold ≤ len then
    karatsubaSquareLimbs minThreshold a lo len hA
  else
    schoolbookSquareLimbs a lo len hA

/-- The Toom squaring ladder on an `AzNat`: the squarer handed to the FFT stage for its
    pointwise squares. -/
def toomSquareLadder (minThreshold toomCook3Cutoff toomCook4Cutoff : Nat) (x : AzNat) : AzNat :=
  ofLimbs (toomSquareLadderLimbs minThreshold toomCook3Cutoff toomCook4Cutoff x.limbs 0
    x.limbs.size (Nat.zero_add _ ▸ Nat.le_refl _))

/-- Parametrized limb-level square dispatcher (used directly by `Tune`).
    Five-way dispatch:

    * `len < minThreshold` → `schoolbookSquareLimbs`;
    * `minThreshold ≤ len < toomCook3Cutoff` → `karatsubaSquareLimbs`;
    * `toomCook3Cutoff ≤ len < toomCook4Cutoff` → `toomCook3SquareLimbs`;
    * `toomCook4Cutoff ≤ len < fftCutoff` → `toomCook4SquareLimbs`;
    * `fftCutoff ≤ len` → `fftSquareLimbs` with the Toom ladder for the pointwise squares. -/
def squareLimbsParam (minThreshold toomCook3Cutoff toomCook4Cutoff fftCutoff : Nat)
    (a : Array UInt64) (lo len : Nat) (hA : lo + len ≤ a.size) : Array UInt64 :=
  if fftCutoff ≤ len then
    fftSquareLimbs (toomSquareLadder minThreshold toomCook3Cutoff toomCook4Cutoff) a lo len hA
  else
    toomSquareLadderLimbs minThreshold toomCook3Cutoff toomCook4Cutoff a lo len hA

/-- Limb-level squaring using the default dispatch parameters. -/
def squareLimbs (a : Array UInt64) (lo len : Nat)
    (hA : lo + len ≤ a.size) : Array UInt64 :=
  squareLimbsParam squareDispatchThreshold squareDispatchToomCook3Cutoff
    squareDispatchToomCook4Cutoff squareDispatchFFTCutoff a lo len hA

/-- AzNat wrapper for `squareLimbsParam`; lets the tuner sweep the
    dispatch parameters. -/
def squareDispatchParam (minThreshold toomCook3Cutoff toomCook4Cutoff fftCutoff : Nat)
    (a : AzNat) : AzNat :=
  ofLimbs (squareLimbsParam minThreshold toomCook3Cutoff toomCook4Cutoff fftCutoff a.limbs 0
    a.limbs.size (Nat.zero_add _ ▸ Nat.le_refl _))

/-- Square an `AzNat`.  Dispatches five-way between schoolbook, Karatsuba,
    Toom-Cook 3, Toom-Cook 4 and the FFT via `squareLimbs`. -/
def square (a : AzNat) : AzNat :=
  ofLimbs (squareLimbs a.limbs 0 a.limbs.size (Nat.zero_add _ ▸ Nat.le_refl _))

-- ── Always-one-algorithm wrappers (for benchmarking) ────────────────────────

/-- Square an `AzNat` forced to use `schoolbookSquareLimbs`. For benchmarking;
    callers should normally use `square`. -/
def squareSchoolbook (a : AzNat) : AzNat :=
  ofLimbs (schoolbookSquareLimbs a.limbs 0 a.limbs.size
    (Nat.zero_add _ ▸ Nat.le_refl _))

/-- Square an `AzNat` forced to use `karatsubaSquareLimbs`. For benchmarking;
    parallels `mulKaratsuba`. -/
def squareKaratsuba (threshold : Nat) (a : AzNat) : AzNat :=
  ofLimbs (karatsubaSquareLimbs threshold a.limbs 0 a.limbs.size
    (Nat.zero_add _ ▸ Nat.le_refl _))

/-- Square an `AzNat` forced to use `toomCook3SquareLimbs`.  For benchmarking;
    parallels `mulToomCook3`.  Takes the two thresholds explicitly so the
    benchmark can use the same fallback as the mul-side. -/
def squareToomCook3 (toomThreshold karaThreshold : Nat) (a : AzNat) : AzNat :=
  ofLimbs (toomCook3SquareLimbs toomThreshold karaThreshold a.limbs 0 a.limbs.size
    (Nat.zero_add _ ▸ Nat.le_refl _))

end Azurite.AzNat
