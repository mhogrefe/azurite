/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.Random.Gen
import Azurite.Random.Geometric
import Azurite.Random.Nat
import Azurite.Random.NatGen
import Azurite.Random.Int
import Azurite.Random.Rat
import Azurite.Random.Pair
import Azurite.AzPolynomial.Basic
import Azurite.AzNat.Instances
import Azurite.AzNat.Equiv.Basic
import Azurite.AzInt.Instances
import Azurite.AzInt.Equiv.Basic
import Mathlib.Data.ZMod.Basic

namespace Azurite.Random

/--
A generator that produces random `AzPolynomial R` values. Each call:
1. Samples a degree `d` from a geometric distribution with mean `meanDegree`.
2. Generates `d` coefficients (for positions 0 through d-1) using `coeffGen`.
3. Generates one nonzero coefficient for the leading position using `nonzeroCoeffGen`.
4. Constructs the polynomial via `AzPolynomial.normalize`.

If `d = 0`, the result is the zero polynomial.

The generator is generic over `R`, but construction functions are provided for
`ℕ`, `ℤ`, `ℚ`, and `ZMod n`.
-/
structure AzPolynomialRandomGen (R : Type) [Semiring R] [DecidableEq R]
    (CG : Type) (NCG : Type) where
  degreeGen        : NatGeometricRandomGen SplitMix64
  coeffGen         : CG
  nonzeroCoeffGen : NCG
  /-- Generate one coefficient (may be zero). -/
  nextCoeff        : CG → R × CG
  /-- Generate one nonzero coefficient. -/
  nextNonzeroCoeff : NCG → R × NCG

/-- Internal helper: generate `n` coefficients into an accumulator list. -/
def genCoeffsLoop {R CG : Type} (next : CG → R × CG) : Nat → CG → List R → List R × CG
  | 0, g, acc => (acc.reverse, g)
  | n + 1, g, acc =>
    let (c, g') := next g
    genCoeffsLoop next n g' (c :: acc)

variable {R : Type} [Semiring R] [DecidableEq R] {CG NCG : Type}

def AzPolynomialRandomGen.next (pg : AzPolynomialRandomGen R CG NCG) :
    AzPolynomial R × AzPolynomialRandomGen R CG NCG :=
  let (d, degreeGen') := RandomGen.next pg.degreeGen
  if d = 0 then
    (AzPolynomial.zero, { pg with degreeGen := degreeGen' })
  else
    -- Generate d-1 arbitrary coefficients for positions 0 .. d-2
    let (coeffs, coeffGen') := genCoeffsLoop pg.nextCoeff (d - 1) pg.coeffGen []
    -- Generate 1 nonzero leading coefficient
    let (lc, nonzeroCoeffGen') := pg.nextNonzeroCoeff pg.nonzeroCoeffGen
    let arr := (coeffs ++ [lc]).toArray
    (AzPolynomial.normalize arr,
     { pg with degreeGen := degreeGen',
               coeffGen := coeffGen',
               nonzeroCoeffGen := nonzeroCoeffGen' })

-- ── Constructors ────────────────────────────────────────────────────────────

/-- Create a `AzPolynomialRandomGen` for `AzPolynomial ℕ`.
- Coefficients are drawn from a geometric bit-length distribution with mean `meanCoeffBitLength`.
- The leading coefficient is always ≥ 1 (positive nat). -/
def mkAzPolynomialNatRandomGen (meanDegree : Rat) (meanCoeffBitLength : Rat) (seed : UInt64) :
    AzPolynomialRandomGen ℕ (NatRandomGen SplitMix64) (PositiveNatRandomGen SplitMix64) :=
  { degreeGen        := mkNatGeometricRandomGen meanDegree (deriveSeed seed "degree"),
    coeffGen         := mkNatRandomGen meanCoeffBitLength (deriveSeed seed "coeff"),
    nonzeroCoeffGen := mkPositiveNatRandomGen meanCoeffBitLength (deriveSeed seed "nzcoeff"),
    nextCoeff        := NatRandomGen.next,
    nextNonzeroCoeff := PositiveNatRandomGen.next}

/-- Create a `AzPolynomialRandomGen` for `AzPolynomial ℤ`.
- Coefficients are drawn from a signed distribution with geometric bit-length.
- The leading coefficient is always nonzero. -/
def mkAzPolynomialIntRandomGen (meanDegree : Rat) (meanCoeffBitLength : Rat) (seed : UInt64) :
    AzPolynomialRandomGen ℤ IntRandomGen NonzeroIntRandomGen :=
  { degreeGen        := mkNatGeometricRandomGen meanDegree (deriveSeed seed "degree"),
    coeffGen         := mkIntRandomGen meanCoeffBitLength (deriveSeed seed "coeff"),
    nonzeroCoeffGen := mkNonzeroIntRandomGen meanCoeffBitLength (deriveSeed seed "nzcoeff"),
    nextCoeff        := IntRandomGen.next,
    nextNonzeroCoeff := NonzeroIntRandomGen.next}

/-- Create a `AzPolynomialRandomGen` for `AzPolynomial AzNat`, reusing the `ℕ`
generator and mapping each drawn coefficient through `AzNat.ofNat`. -/
def mkAzPolynomialAzNatRandomGen (meanDegree : Rat) (meanCoeffBitLength : Rat) (seed : UInt64) :
    AzPolynomialRandomGen AzNat (NatRandomGen SplitMix64) (PositiveNatRandomGen SplitMix64) :=
  { degreeGen        := mkNatGeometricRandomGen meanDegree (deriveSeed seed "degree"),
    coeffGen         := mkNatRandomGen meanCoeffBitLength (deriveSeed seed "coeff"),
    nonzeroCoeffGen := mkPositiveNatRandomGen meanCoeffBitLength (deriveSeed seed "nzcoeff"),
    nextCoeff        := fun g => let (n, g') := NatRandomGen.next g; (AzNat.ofNat n, g'),
    nextNonzeroCoeff := fun g => let (n, g') := PositiveNatRandomGen.next g; (AzNat.ofNat n, g') }

/-- Create a `AzPolynomialRandomGen` for `AzPolynomial AzInt`, reusing the `ℤ`
generator and mapping each drawn coefficient through `AzInt.ofInt`. -/
def mkAzPolynomialAzIntRandomGen (meanDegree : Rat) (meanCoeffBitLength : Rat) (seed : UInt64) :
    AzPolynomialRandomGen AzInt IntRandomGen NonzeroIntRandomGen :=
  { degreeGen        := mkNatGeometricRandomGen meanDegree (deriveSeed seed "degree"),
    coeffGen         := mkIntRandomGen meanCoeffBitLength (deriveSeed seed "coeff"),
    nonzeroCoeffGen := mkNonzeroIntRandomGen meanCoeffBitLength (deriveSeed seed "nzcoeff"),
    nextCoeff        := fun g => let (z, g') := IntRandomGen.next g; (AzInt.ofInt z, g'),
    nextNonzeroCoeff := fun g => let (z, g') := NonzeroIntRandomGen.next g; (AzInt.ofInt z, g') }

/-- Create a `AzPolynomialRandomGen` for `AzPolynomial ℚ`.
- Coefficients are random rationals with geometric bit-length for numerator and denominator.
- The leading coefficient is always nonzero. -/
def mkAzPolynomialRatRandomGen (meanDegree : Rat) (meanCoeffBitLength : Rat) (seed : UInt64) :
    AzPolynomialRandomGen ℚ RatRandomGen NonzeroRatRandomGen :=
  { degreeGen        := mkNatGeometricRandomGen meanDegree (deriveSeed seed "degree"),
    coeffGen         := mkRatRandomGen meanCoeffBitLength (deriveSeed seed "coeff"),
    nonzeroCoeffGen := mkNonzeroRatRandomGen meanCoeffBitLength (deriveSeed seed "nzcoeff"),
    nextCoeff        := RatRandomGen.next,
    nextNonzeroCoeff := NonzeroRatRandomGen.next}

/-- Create a `AzPolynomialRandomGen` for `AzPolynomial (ZMod n)`.
- Coefficients are uniform in `{0, ..., n-1}`.
- The leading coefficient is uniform in `{1, ..., n-1}` (always nonzero).
- Requires `n ≥ 2` (so that nonzero elements exist). -/
def mkAzPolynomialZModRandomGen (n : ℕ) [NeZero n] (meanDegree : Rat) (seed : UInt64) :
    AzPolynomialRandomGen (ZMod n)
      (NatLessThanRandomGen SplitMix64)
      (NatLessThanRandomGen SplitMix64) :=
  { degreeGen        := mkNatGeometricRandomGen meanDegree (deriveSeed seed "degree"),
    coeffGen         := mkNatLessThanRandomGen n (deriveSeed seed "coeff"),
    nonzeroCoeffGen := mkNatLessThanRandomGen (n - 1) (deriveSeed seed "nzcoeff"),
    nextCoeff        := fun g =>
      let (v, g') := NatLessThanRandomGen.next g
      ((v : ZMod n), g'),
    nextNonzeroCoeff := fun g =>
      let (v, g') := NatLessThanRandomGen.next g
      -- v ∈ {0, ..., n-2}, so v+1 ∈ {1, ..., n-1}
      ((v + 1 : ZMod n), g') }

end Azurite.Random
