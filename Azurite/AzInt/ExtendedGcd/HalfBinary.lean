/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzInt.ExtendedGcd.Binary
import Azurite.AzNat.Gcd.HalfBinary

/-!
## Extended half-binary GCD (Bézout coefficients, subquadratic)

The extended analogue of `AzNat.gcdHalfBinary` (MCA §1.6.3): `gcd(a, b)` together with `s, t`
such that `s·a + t·b = gcd(a, b)`, in `O(M(n) log n)`.

**Pulling a Bézout row back through the reduction.**  Every round of the plain driver
(`AzNat.halfBinaryGcdDriver`) replaces the operands `(x, y)` by `(x', y')` with
`2^{2j} (x', y')ᵀ = R (x, y)ᵀ` for an integer matrix `R` — the matrix of a half-binary GCD,
the `Int64` matrix of the word base case, or the matrix `[0, 2^j; 2^j, q]` of one binary
division.  If `(s', t')` is a Bézout row for the new operands, `s' x' + t' y' = 2^e g`, then
`(s' R₁₁ + t' R₂₁) x + (s' R₁₂ + t' R₂₂) y = 2^{e + 2j} g` is one for the old ones.  So
the extended driver runs the same rounds, computes a Bézout row for the final small operands
with the quadratic `egcdBinary`, and pulls it back through the rounds on return (`pullBack`,
`pullBackWord`, `pullBackStep`) — a row vector, never the full matrix.  The result is
`s x + t y = 2^e g` with `g` the odd part of the GCD and `e` the total valuation shed.

**Stripping the power of two.**  The driver's first operand `x` is odd.  For `k ≡ −t · x⁻¹
(mod 2^e)` (the inverse from `AzZModPow2.invOdd`), both `t + k x` and `s − k y` are divisible by
`2^e`, and `(s − k y) x + (t + k x) y = s x + t y`, so dividing both by `2^e` gives a Bézout row
for `g` itself (`fixUp`).  This costs one inverse modulo `2^e`, two products and two shifts —
`O(M(n))` — instead of the `e` single-bit corrections of the binary extended GCD.

Correctness (`Equiv/ExtendedGcd/HalfBinary.lean`) needs only the identities above for the Bézout
part; the gcd value follows from the odd-part invariant of the plain driver.  As there, every
division by a power of two is checked at runtime and the quadratic algorithm is the fallback, so
the result is exact for all inputs.
-/

namespace Azurite.AzInt

/-- A Bézout row with a power-of-two scale: `s · x + t · y = 2^e · g` for the operands `(x, y)`
it was computed for, with `g` the odd part of their GCD. -/
structure ScaledBezout where
  /-- The power of two shed by the reduction. -/
  e : Nat
  /-- The odd part of the GCD. -/
  g : AzNat
  /-- The coefficient of the first operand. -/
  s : AzInt
  /-- The coefficient of the second operand. -/
  t : AzInt

/-- The terminal case: the quadratic extended binary GCD on the magnitudes, with the signs folded
into the coefficients and the power of two split off the GCD. -/
def egcdBase (x y : AzInt) : ScaledBezout :=
  let r := egcdBinary x.abs y.abs
  let s := if x.sign then r.2.1 else -r.2.1
  let t := if y.sign then r.2.2 else -r.2.2
  match r.1.trailingZeros with
  | none => ⟨0, 0, s, t⟩
  | some e => ⟨e, r.1 >>> e, s, t⟩

/-- Pull a Bézout row for `(x', y')` back through a matrix `R` with
`2^sh (x', y')ᵀ = R (x, y)ᵀ`: the row `(s R₁₁ + t R₂₁, s R₁₂ + t R₂₂)` for `(x, y)`, scaled
by `2^sh` more. -/
def pullBack (R : AzNat.Mat2) (sh : Nat) (r : ScaledBezout) : ScaledBezout :=
  ⟨r.e + sh, r.g, r.s * R.a + r.t * R.c, r.s * R.b + r.t * R.d⟩

/-- `pullBack` for the `Int64` matrix of the word base case, each new coefficient in one fused
limb pass (`fusedCombine?` with no shift; the generic product is the never-taken default). -/
def pullBackWord (M : AzNat.WordMat) (sh : Nat) (r : ScaledBezout) : ScaledBezout :=
  ⟨r.e + sh, r.g,
    (AzNat.fusedCombine? M.m₁₁ M.m₂₁ r.s r.t 0).getD
      (M.m₁₁.toAzInt * r.s + M.m₂₁.toAzInt * r.t),
    (AzNat.fusedCombine? M.m₁₂ M.m₂₂ r.s r.t 0).getD
      (M.m₁₂.toAzInt * r.s + M.m₂₂.toAzInt * r.t)⟩

/-- `pullBack` for the matrix `[0, 2^j; 2^j, q]` of one binary-division step
`(x, 2^j y'') ↦ (y'', (x + q y'') / 2^j)`: the row `(2^j t, 2^j s + q t)`, scaled by `2^{2j}`. -/
def pullBackStep (j : Nat) (q : AzInt) (r : ScaledBezout) : ScaledBezout :=
  ⟨r.e + 2 * j, r.g, r.t <<< j, (r.s <<< j) + r.t * q⟩

/-- The extended driver: the rounds of `AzNat.halfBinaryGcdDriver` (quadratic word rounds up to
`quadThreshold` bits, the `k = n / 2` recursion above), ending in `egcdBase` at or below
`threshold` bits or on any failed exactness check, with the Bézout row pulled back on return. -/
def egcdDriver (threshold quadThreshold : Nat) : Nat → AzInt → AzInt → ScaledBezout
  | 0, x, y => egcdBase x y
  | fuel + 1, x, y =>
    let n := max x.size y.size
    if n ≤ threshold then egcdBase x y
    else if n ≤ quadThreshold then
      let jM := AzNat.halfBinaryGcdWord (x.lowWord2 (2 * AzNat.halfBinaryWordThreshold + 1))
        (y.lowWord2 (2 * AzNat.halfBinaryWordThreshold + 1)) AzNat.halfBinaryWordThreshold
      if jM.1 = 0 then egcdBase x y
      else
        match AzNat.fusedCombine? jM.2.m₁₁ jM.2.m₁₂ x y (2 * jM.1),
            AzNat.fusedCombine? jM.2.m₂₁ jM.2.m₂₂ x y (2 * jM.1) with
        | some x', some y' =>
          pullBackWord jM.2 (2 * jM.1) (egcdDriver threshold quadThreshold fuel x' y')
        | _, _ => egcdBase x y
    else
      let k₁ := n / 2
      let m₁ := 2 * k₁ + 1
      let jR := AzNat.halfBinaryGcd (k₁ + 1) (x.lowBits m₁) (y.lowBits m₁) k₁
      let xy := jR.2.apply x y
      match xy.1.exactShiftRight (2 * jR.1), xy.2.exactShiftRight (2 * jR.1) with
      | some x', some y' =>
        match y'.trailingZeros with
        | none => pullBack jR.2 (2 * jR.1) (egcdBase x' y')
        | some j₀ =>
          let y'' := AzInt.mkNorm y'.sign (y'.abs >>> j₀)
          let qr := AzNat.binaryDivide x' y'' j₀
          match qr.2.exactShiftRight j₀ with
          | some r' =>
            pullBack jR.2 (2 * jR.1)
              (pullBackStep j₀ qr.1 (egcdDriver threshold quadThreshold fuel y'' r'))
          | none => pullBack jR.2 (2 * jR.1) (egcdBase x' y')
      | _, _ => egcdBase x y

/-- From `s x + t y = 2^e g` with `x` odd, a Bézout row for `g` itself: with
`k ≡ −t · x⁻¹ (mod 2^e)`, both `t + k x` and `s − k y` are divisible by `2^e` and
`(s − k y) x + (t + k x) y = 2^e g`.  (For `e = 0` the residue ring is trivial and nothing is
to be done.) -/
def fixUp (x y : AzNat) (r : ScaledBezout) : AzInt × AzInt :=
  let xz := AzZModPow2.ofAzNat r.e x
  if h : xz.isOdd then
    let k := (AzZModPow2.ofAzInt r.e (-r.t) * xz.invOdd h).val.toAzInt
    ((r.s - k * y.toAzInt) >>> r.e, (r.t + k * x.toAzInt) >>> r.e)
  else (r.s, r.t)

/-- The extended GCD of an odd `x` and an arbitrary `y`: the second operand is made even by adding
`x` when necessary, the driver is run, the power of two is stripped (`fixUp`) and the addition is
undone (`(s + t) x + t y = s x + t (x + y)`).  Returns `(gcd(x, y), s, t)`. -/
def egcdOddWith (threshold quadThreshold : Nat) (x y : AzNat) : AzNat × AzInt × AzInt :=
  let addX := y.isOdd
  let y' := if addX then x + y else y
  let r := egcdDriver threshold quadThreshold (max x.size y'.size + 1) x.toAzInt y'.toAzInt
  let st := fixUp x y' r
  (r.g, if addX then st.1 + st.2 else st.1, st.2)

/-- **Extended half-binary GCD** with explicit thresholds (bits) for the quadratic base case and
for the quadratic middle layer (see `AzNat.gcdHalfBinaryWith`).  Strips the common power of two
`2^m`, puts the operand of smaller valuation (now odd) first, runs `egcdOddWith` and restores
the factor on the GCD; the coefficients of `a / 2^m`, `b / 2^m` for `gcd / 2^m` are those of
`a`, `b` for the GCD. -/
def egcdHalfBinaryWith (threshold quadThreshold : Nat) (a b : AzNat) : AzNat × AzInt × AzInt :=
  match a.trailingZeros, b.trailingZeros with
  | none, _ => (b, 0, 1)
  | _, none => (a, 1, 0)
  | some ta, some tb =>
    let m := min ta tb
    let a₁ := a >>> m
    let b₁ := b >>> m
    if ta ≤ tb then
      let r := egcdOddWith threshold quadThreshold a₁ b₁
      (r.1 <<< m, r.2.1, r.2.2)
    else
      let r := egcdOddWith threshold quadThreshold b₁ a₁
      (r.1 <<< m, r.2.2, r.2.1)

/-- Operands of at most this many bits use the quadratic `egcdBinary` inside the extended
half-binary GCD.  Set to `AzNat.halfBinaryGcdThreshold`; not tuned separately. -/
def egcdHalfBinaryThreshold : Nat := AzNat.halfBinaryGcdThreshold

/-- **Extended half-binary GCD** at the default thresholds. -/
def egcdHalfBinary (a b : AzNat) : AzNat × AzInt × AzInt :=
  egcdHalfBinaryWith egcdHalfBinaryThreshold AzNat.halfBinaryGcdQuadraticThreshold a b

end Azurite.AzInt
