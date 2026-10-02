/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzInt.Add
import Azurite.AzNat.Equiv.IsMultipleOfPow2
import Azurite.AzNat.Equiv.ShiftLeft
import Azurite.AzNat.Equiv.Size
import Mathlib.Data.Nat.Size

/-!
# `AzFloat`: arbitrary-precision binary floating-point numbers

A computable floating-point type whose *representation* follows the author's Malachite `Float`
(`docs/azfloat_plan.md`; the algorithms do not — see the plan for the provenance rule): a sign,
an **unbounded** exponent (`AzInt`, so there is no overflow or underflow and no minimum or
maximum exponent), a precision, and a limb-aligned significand.  The special values `NaN`,
`±∞` and `0` are separate constructors.  There is no negative zero: its purpose in IEEE 754
arithmetic is to remember the sign of a value that underflowed to zero, and with an unbounded
exponent nothing underflows (a nonzero value rounded to any positive precision stays nonzero).

A finite nonzero value `finite s e p m _` denotes `(−1)^(¬s) · m · 2^(e − m.size)`, where the
significand `m` is **left-aligned**: its bit length is `alignedBits p`, the least multiple of
`64` that is at least the precision `p`, and its low `alignedBits p − p` bits are zero.  So
`m.size = 64 · ⌈p / 64⌉`, the top bit of the top limb is set, and `2^(e−1) ≤ |x| < 2^e`: the
exponent is `⌊log₂ |x|⌋ + 1`.  Keeping the significand left-aligned at a limb boundary lets
comparisons and same-exponent additions work limb by limb from the top and keeps the rounding
position inside the lowest limb; the price is the invariant `FiniteValid`, established once in
the smart constructor `mkFinite`.  `1.0` at precision `53` is
`finite true 1 53 (2^63)`.

This file holds the type, its classification predicates, the accessors and the sign-only
operations.  Conversions live in `AzFloat/Conversion.lean`; the value model `toVal :
AzFloat → Option EReal` (`none` for `NaN`) and all correctness proofs live under
`AzFloat/Equiv/`.
-/

namespace Azurite

namespace AzFloat

/-- The bit length of a significand of precision `p`: the least multiple of `64` that is at
least `p` (and at least `64` when `0 < p`). -/
def alignedBits (p : Nat) : Nat := (p + 63) / 64 * 64

/-- The representation invariant of a finite nonzero value of precision `p` with significand
`m`: the precision is positive, `m` has exactly `alignedBits p` bits (so its top bit is the top
bit of its top limb), and its low `alignedBits p − p` bits are zero. -/
structure FiniteValid (p : Nat) (m : AzNat) : Prop where
  /-- The precision is positive. -/
  pos : 0 < p
  /-- The significand is left-aligned at a limb boundary. -/
  size_eq : m.size = alignedBits p
  /-- Only the top `p` bits of the significand may be nonzero. -/
  dvd : 2 ^ (alignedBits p - p) ∣ m.toNat

end AzFloat

/-- An arbitrary-precision binary floating-point number: `NaN`, a signed infinity, zero, or
a finite nonzero value `(−1)^(¬sign) · significand · 2^(exponent − significand.size)`
of the given precision.  The sign is `true` for positive. -/
inductive AzFloat where
  /-- Not a number. -/
  | nan
  /-- `+∞` (`sign = true`) or `−∞`. -/
  | infinity (sign : Bool)
  /-- Zero (unsigned). -/
  | zero
  /-- A finite nonzero value with a left-aligned significand (`AzFloat.FiniteValid`). -/
  | finite (sign : Bool) (exponent : AzInt) (precision : Nat) (significand : AzNat)
      (valid : AzFloat.FiniteValid precision significand)
  deriving DecidableEq

namespace AzFloat

instance : Inhabited AzFloat := ⟨nan⟩

theorem le_alignedBits (p : Nat) : p ≤ alignedBits p := by
  unfold alignedBits; omega

theorem alignedBits_lt (p : Nat) : alignedBits p < p + 64 := by
  unfold alignedBits; omega

theorem alignedBits_mod (p : Nat) : alignedBits p % 64 = 0 := by
  unfold alignedBits; omega

/-- Build a finite value from a sign, an exponent, a requested precision and a significand `m`
with at most that many bits: the significand is left-aligned and the value is
`(−1)^(¬sign) · m · 2^(exponent − m.size)`.  A zero significand gives `zero`.  The
precision of the result is `max p m.size`, which is `p` whenever `m.size ≤ p`. -/
def mkFinite (sign : Bool) (exponent : AzInt) (p : Nat) (m : AzNat) : AzFloat :=
  if hm : m = 0 then zero
  else
    let p' := max p m.size
    have hm0 : m.toNat ≠ 0 := fun h => hm (AzNat.toNat_injective (h.trans AzNat.toNat_zero.symm))
    have hsize : 0 < m.size := by
      rw [← AzNat.size_toNat]; exact Nat.size_pos.mpr (Nat.pos_of_ne_zero hm0)
    have hle : m.size ≤ alignedBits p' := le_trans (le_max_right _ _) (le_alignedBits _)
    finite sign exponent p' (m.shiftLeft (alignedBits p' - m.size))
      { pos := lt_of_lt_of_le hsize (le_max_right _ _)
        size_eq := by
          rw [← AzNat.size_toNat, AzNat.toNat_shiftLeft, ← Nat.shiftLeft_eq,
            Nat.size_shiftLeft hm0, AzNat.size_toNat]
          omega
        dvd := by
          rw [AzNat.toNat_shiftLeft]
          exact Dvd.dvd.mul_left (pow_dvd_pow 2 (by omega)) _ }

/-! ### Classification -/

/-- `NaN`? -/
def isNaN : AzFloat → Bool
  | nan => true
  | _ => false

/-- `±∞`? -/
def isInfinite : AzFloat → Bool
  | infinity _ => true
  | _ => false

/-- Zero? -/
def isZero : AzFloat → Bool
  | zero => true
  | _ => false

/-- Finite (zero or not)? -/
def isFinite : AzFloat → Bool
  | zero => true
  | finite _ _ _ _ _ => true
  | _ => false

/-- Finite and nonzero?  (With an unbounded exponent every finite nonzero value is normal.) -/
def isNormal : AzFloat → Bool
  | finite _ _ _ _ _ => true
  | _ => false

/-- Strictly positive (`+∞` or a positive finite value)? -/
def isPositive : AzFloat → Bool
  | infinity s => s
  | finite s _ _ _ _ => s
  | _ => false

/-- Strictly negative (`−∞` or a negative finite value)? -/
def isNegative : AzFloat → Bool
  | infinity s => !s
  | finite s _ _ _ _ => !s
  | _ => false

/-! ### Accessors -/

/-- The sign (`true` = positive) of a nonzero non-`NaN` value, `none` for `NaN` and zero. -/
def sign? : AzFloat → Option Bool
  | infinity s => some s
  | finite s _ _ _ _ => some s
  | _ => none

/-- The exponent `⌊log₂ |x|⌋ + 1` of a finite nonzero value, `none` otherwise. -/
def exponent? : AzFloat → Option AzInt
  | finite _ e _ _ _ => some e
  | _ => none

/-- The precision of a finite nonzero value, `none` otherwise. -/
def precision? : AzFloat → Option Nat
  | finite _ _ p _ _ => some p
  | _ => none

/-- The (left-aligned) significand of a finite nonzero value, `none` otherwise. -/
def significand? : AzFloat → Option AzNat
  | finite _ _ _ m _ => some m
  | _ => none

/-! ### Sign operations -/

/-- Negation: flips the sign; `NaN` stays `NaN`. -/
def neg : AzFloat → AzFloat
  | nan => nan
  | infinity s => infinity (!s)
  | zero => zero
  | finite s e p m h => finite (!s) e p m h

instance : Neg AzFloat := ⟨neg⟩

/-- Absolute value: sets the sign positive; `NaN` stays `NaN`. -/
def abs : AzFloat → AzFloat
  | nan => nan
  | infinity _ => infinity true
  | zero => zero
  | finite _ e p m h => finite true e p m h

/-! ### Constants -/

/-- `+∞`. -/
def posInfinity : AzFloat := infinity true

/-- `−∞`. -/
def negInfinity : AzFloat := infinity false

instance : Zero AzFloat := ⟨zero⟩

/-- `2^e` at precision `1`. -/
def powerOf2 (e : AzInt) : AzFloat := mkFinite true (e + 1) 1 1

/-- `1` at precision `1`. -/
def one : AzFloat := powerOf2 0

instance : One AzFloat := ⟨one⟩

/-- `−1` at precision `1`. -/
def negOne : AzFloat := -one

/-- `2` at precision `1`. -/
def two : AzFloat := powerOf2 1

/-- `1/2` at precision `1`. -/
def oneHalf : AzFloat := powerOf2 (-1)

end AzFloat

end Azurite
