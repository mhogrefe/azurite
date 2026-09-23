/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzNat.Div.Schoolbook
import Azurite.AzNat.DivMod10p19
import Azurite.AzNat.LimbDigitsPow2
import Azurite.AzNat.OfLimbs
import Azurite.UInt64.Digits
import Azurite.UInt64.MaxPow

namespace Azurite

/-- Recursive helper for `AzNat.limbDigits`: repeatedly divide `U` by a
    nonzero `UInt64` base `d`, pushing each remainder LSB-first. Fuel
    bounds the iteration; `64 * U.limbs.size` suffices for any `d ≥ 2`. -/
def AzNat.toBaseUInt64DigitsAux (d : UInt64) (hd : d ≠ 0) :
    Nat → AzNat → Array UInt64 → Array UInt64
  | 0, _, acc => acc
  | f + 1, U, acc =>
    if U.limbs.size = 0 then acc
    else
      let qr := U.divModUInt64 d hd
      AzNat.toBaseUInt64DigitsAux d hd f qr.1 (acc.push qr.2)

/-- Base-`10^19` specialization of `toBaseUInt64DigitsAux`: the per-limb
    division routes through the constant-folded `divMod10p19`, avoiding
    the `leadingZeros` / `reciprocal` / shift bookkeeping that the
    generic `divModUInt64` does at every call. Functionally equivalent
    to `toBaseUInt64DigitsAux UInt64.maxPow10 (by decide)`. -/
def AzNat.toBase10p19DigitsAux :
    Nat → AzNat → Array UInt64 → Array UInt64
  | 0, _, acc => acc
  | f + 1, U, acc =>
    if U.limbs.size = 0 then acc
    else
      let qr := U.divMod10p19
      AzNat.toBase10p19DigitsAux f qr.1 (acc.push qr.2)

/-- Right-pad `UInt64.digits b u` with zeros to length `e`. Used when
    expanding a single base-`(maxPow b).1` "super-digit" into exactly
    `(maxPow b).2` base-`b` digits, so the concatenation aligns. -/
def UInt64.digitsPaddedTo (b u : UInt64) (e : Nat) : Array UInt64 :=
  let d := UInt64.digits b u
  if d.size < e then d ++ Array.replicate (e - d.size) (0 : UInt64)
  else d

/-- `n.limbDigits b` returns the base-`b` digits of `n`, LSB-first,
    trimmed of trailing zeros. Intended for `b ∈ [2, 2^64 - 1]`.

    Dispatches:
    * `b < 2`: degenerate, returns `#[]`.
    * `n.limbs.size ≤ 1` (so `n.toNat < 2^64` — the common case for
      typical inputs): short-circuit through `UInt64.digits`,
      avoiding the AzNat division loop entirely.
    * `b` is a power of two: delegates to `limbDigitsPow2 (ctz b)`,
      which avoids any general-base division.
    * `b = 10`: routes the per-super-digit division through the
      constant-folded `divMod10p19` (via `toBase10p19DigitsAux`),
      saving the `leadingZeros` / `reciprocal` / shift bookkeeping
      that the generic path repeats on every call. Since `19` is prime,
      `(maxPow b).1 = maxPow10` only for `b ∈ {10, 10^19}` — we
      disregard the `b = 10^19` case as rare.
    * otherwise: with `(P, E) := maxPow b` (so `P = b^E < 2^64`),
      repeatedly divide `n` by `P` via `divModUInt64`, collecting `E`
      base-`P` "super-digits" per division step. Each super-digit is
      then expanded to exactly `E` base-`b` digits (zero-padded via
      `digitsPaddedTo`), the contributions concatenated, and trailing
      zeros trimmed.

    The defensive `P = 0` branch is unreachable when `b ≥ 2`. -/
def AzNat.limbDigits (b : UInt64) (n : AzNat) : Array UInt64 :=
  if b < 2 then #[]
  else
    match h : n.limbs.size with
    | 0 => #[]
    | 1 => UInt64.digits b (n.limbs[0]'(by simp [h]))
    | _ + 2 =>
      if b.isPowerOfTwo then
        n.limbDigitsPow2 b.toBitVec.ctz.toNat
      else if b = 10 then
        let bigDigits := AzNat.toBase10p19DigitsAux (64 * n.limbs.size) n #[]
        let flat := bigDigits.foldl (init := (#[] : Array UInt64))
          fun acc d => acc ++ UInt64.digitsPaddedTo 10 d UInt64.maxPow10Exp
        AzNat.trimTrailingZeros flat
      else
        let P := (UInt64.maxPow b).1
        let E := (UInt64.maxPow b).2
        if hP : P = 0 then #[]
        else
          let bigDigits := AzNat.toBaseUInt64DigitsAux P hP
            (64 * n.limbs.size) n #[]
          let flat := bigDigits.foldl (init := (#[] : Array UInt64))
            fun acc d => acc ++ UInt64.digitsPaddedTo b d E
          AzNat.trimTrailingZeros flat

-- Sanity checks.
-- Single limb, non-power-of-2 base.
#guard ((AzNat.ofLimbs #[100]).limbDigits 10) = #[0, 0, 1]
#guard ((AzNat.ofLimbs #[12345]).limbDigits 10) = #[5, 4, 3, 2, 1]
#guard ((0 : AzNat).limbDigits 10) = #[]
#guard ((1 : AzNat).limbDigits 10) = #[1]

-- Power-of-2 base routes through `limbDigitsPow2`.
#guard ((AzNat.ofLimbs #[0xDEADBEEF]).limbDigits 16) =
       #[0xF, 0xE, 0xE, 0xB, 0xD, 0xA, 0xE, 0xD]
#guard ((AzNat.ofLimbs #[0xDEADBEEF]).limbDigits 2) =
       (AzNat.ofLimbs #[0xDEADBEEF]).limbDigitsPow2 1

-- Multi-limb, non-power-of-2 base: 2^64 = 18446744073709551616 in decimal.
#guard ((AzNat.ofLimbs #[0, 1]).limbDigits 10) =
       #[6, 1, 6, 1, 5, 5, 9, 0, 7, 3, 7, 0, 4, 4, 7, 6, 4, 4, 8, 1]

-- Degenerate (b < 2).
#guard ((AzNat.ofLimbs #[42]).limbDigits 0) = #[]
#guard ((AzNat.ofLimbs #[42]).limbDigits 1) = #[]

end Azurite
