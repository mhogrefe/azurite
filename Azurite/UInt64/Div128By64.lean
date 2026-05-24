import Azurite.UInt64.Div2By1
import Azurite.UInt64.Equiv.LeadingZeros
import Azurite.UInt64.LeadingZeros
import Azurite.UInt64.Reciprocal

namespace Azurite.UInt64

/-!
128-bit by 64-bit division with on-the-fly divisor normalization.

Wraps `UInt64.div2By1` (which assumes a normalized divisor) to handle
an arbitrary nonzero `UInt64` divisor.  Specialization of the
`divModLimb` algorithm from `Azurite.AzNat.Div` for the case of a
2-limb dividend; structured as a direct UInt64 primitive so callers
(e.g. the two-limb `sqrtRem`) avoid Array allocation.
-/

/-- Divide a 128-bit dividend `hi * 2^64 + lo` by a nonzero 64-bit
    divisor `d`.  Returns `(q, r)` with `q * d + r = hi * 2^64 + lo`
    and `0 ≤ r < d`.

    Implicit precondition: `hi < d`, so the quotient fits in `UInt64`.
    If violated, the call still returns *some* `UInt64`, but it has
    no useful meaning.

    Algorithm:
      `k := leadingZeros d`; `d' := d << k`; the shifted dividend's
      top 64 bits land in `m_hi`, the bottom in `m_lo`.  Apply
      `div2By1` to `(m_hi, m_lo)` by `d'`; the quotient is exact,
      the remainder gets right-shifted by `k` to undo the
      normalisation. -/
def div128by64 (hi lo d : UInt64) (hd : d ≠ 0) : UInt64 × UInt64 :=
  let k := _root_.UInt64.leadingZeros d
  let kU : UInt64 := UInt64.ofNat k
  let d' := d <<< kU
  have hd'_norm : 2 ^ 63 ≤ d'.toNat :=
    _root_.UInt64.two_pow_63_le_toNat_shiftLeft_leadingZeros d hd
  let inv := _root_.UInt64.reciprocal d' hd'_norm
  let m_hi : UInt64 :=
    if k = 0 then hi
    else (hi <<< kU) ||| (lo >>> UInt64.ofNat (64 - k))
  let m_lo : UInt64 := lo <<< kU
  let qr := _root_.UInt64.div2By1 m_hi m_lo d' inv
  (qr.1, qr.2 >>> kU)

end Azurite.UInt64

section Examples

open Azurite.UInt64

-- 64/64 cases: hi = 0.
#guard div128by64 0 100 7 (by decide) = (14, 2)
#guard div128by64 0 0 1 (by decide) = (0, 0)
#guard div128by64 0 ((1 : UInt64) <<< 63) 1 (by decide) = ((1 : UInt64) <<< 63, 0)

-- True 128-bit dividend, small divisor.
#guard div128by64 1 0 2 (by decide) = ((1 : UInt64) <<< 63, 0)
#guard div128by64 1 1 2 (by decide) = ((1 : UInt64) <<< 63, 1)

-- Normalized divisor (k = 0): top bit of d is 1.
#guard div128by64 0 ((1 : UInt64) <<< 63) ((1 : UInt64) <<< 63) (by decide) = (1, 0)
#guard div128by64 1 0 ((1 : UInt64) <<< 63) (by decide) = (2, 0)

-- Largest dividend the precondition admits, divisor = UInt64.maxValue.
#guard div128by64 ((0 : UInt64) - 2) ((0 : UInt64) - 1) ((0 : UInt64) - 1) (by decide)
        = ((0 : UInt64) - 1, (0 : UInt64) - 2)

end Examples
