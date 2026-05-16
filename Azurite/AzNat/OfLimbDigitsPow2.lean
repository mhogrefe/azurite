import Azurite.AzNat.OfLimbs
import Azurite.AzNat.Parse
import Azurite.AzNat.ToString
import Azurite.AzNat.LimbDigitsPow2

namespace Azurite

/-- `ofLimbDigitsPow2 k digits` reconstructs an `AzNat` from its base-`2^k`
    digit array (LSB-first), the left inverse of `AzNat.limbDigitsPow2 k`.
    Intended for `k ∈ [1, 64]`.

    The build is **limb-driven**, mirroring how `limbDigitsPow2` is
    **digit-driven**: for each output limb `q`, we OR in the contribution
    of every digit whose bit range `[i*k, (i+1)*k)` overlaps the limb's
    bit range `[q*64, q*64+64)`. The accumulator starts at zero per limb
    and is never read back, so we avoid any "clear-then-set" bookkeeping.

    Dispatches symmetric to `limbDigitsPow2`:

    * `k = 64`: each digit is a limb. Wrap with `AzNat.ofLimbs` (which
      trims any trailing zeros, restoring the AzNat invariant when the
      input digit array is unnormalized).
    * `k | 64` with `k < 64` (i.e., `k ∈ {1, 2, 4, 8, 16, 32}`): every
      output limb collects `perLimb = 64 / k` consecutive digits, each
      left-shifted into its slot inside the limb. Digits never span
      limb boundaries in this case.
    * `k ∤ 64` with `k ∈ [1, 63]`: a single digit can straddle a limb
      boundary, so each output limb may receive bits from the tail of
      one digit (right-shifted) plus zero or more whole digits (left-
      shifted). The contributing digit range is
      `[q*64 / k, (q*64 + 63) / k]`.
    * Other `k` (zero or above 64): returns `0`. -/
def AzNat.ofLimbDigitsPow2 (k : Nat) (digits : Array UInt64) : AzNat :=
  if k = 64 then
    AzNat.ofLimbs digits
  else if _h1 : 1 ≤ k ∧ k < 64 ∧ 64 % k = 0 then
    let perLimb := 64 / k
    let numLimbs := (digits.size + perLimb - 1) / perLimb
    let limbs := Array.ofFn (n := numLimbs) fun q =>
      (Array.range perLimb).foldl (init := (0 : UInt64)) fun acc j =>
        let i := q.val * perLimb + j
        if h : i < digits.size then
          acc ||| (digits[i] <<< UInt64.ofNat (j * k))
        else acc
    AzNat.ofLimbs limbs
  else if _h2 : 1 ≤ k ∧ k < 64 then
    let totalBits := digits.size * k
    let numLimbs := (totalBits + 63) / 64
    let limbs := Array.ofFn (n := numLimbs) fun q =>
      let qBits := q.val * 64
      let iLo := qBits / k
      let iHi := (qBits + 63) / k
      (Array.range (iHi + 1 - iLo)).foldl (init := (0 : UInt64)) fun acc j =>
        let i := iLo + j
        if h : i < digits.size then
          let d := digits[i]
          if i * k ≥ qBits then
            acc ||| (d <<< UInt64.ofNat (i * k - qBits))
          else
            acc ||| (d >>> UInt64.ofNat (qBits - i * k))
        else acc
    AzNat.ofLimbs limbs
  else
    0

-- Sanity checks.

-- k = 64 short-circuit: digits ARE the limbs.
-- 2^64 has limbs [0, 1].
#guard (AzNat.ofLimbDigitsPow2 64 #[0, 1]) = AzNat.ofLimbs #[0, 1]
#guard (AzNat.ofLimbDigitsPow2 64 #[100]) = AzNat.ofLimbs #[100]
#guard (AzNat.ofLimbDigitsPow2 64 #[]) = (0 : AzNat)
-- Trailing-zero digits get trimmed (input was unnormalized).
#guard (AzNat.ofLimbDigitsPow2 64 #[7, 0, 0]) = AzNat.ofLimbs #[7]

-- k | 64 with k < 64 (digits never span limb boundaries).
-- 100 = 0x64 in base 16 has LSB-first digits [4, 6]. Round-trip.
#guard (AzNat.ofLimbDigitsPow2 4 #[4, 6]) = AzNat.ofLimbs #[100]
-- Sixteen Fs in base 16 reconstruct 0xFFFF_FFFF_FFFF_FFFF.
#guard (AzNat.ofLimbDigitsPow2 4
         #[0xF, 0xF, 0xF, 0xF, 0xF, 0xF, 0xF, 0xF,
           0xF, 0xF, 0xF, 0xF, 0xF, 0xF, 0xF, 0xF])
       = AzNat.ofLimbs #[0xFFFF_FFFF_FFFF_FFFF]
-- Cross-limb base-2^32: digits [1, 0, 1] → 1 + 1·2^64, limbs [1, 1].
#guard (AzNat.ofLimbDigitsPow2 32 #[1, 0, 1]) = AzNat.ofLimbs #[1, 1]
-- Empty input → zero.
#guard (AzNat.ofLimbDigitsPow2 4 #[]) = (0 : AzNat)

-- k ∤ 64 (digits span limb boundaries).
-- 100 = 0o144 in base 8 has LSB-first digits [4, 4, 1]. Round-trip.
#guard (AzNat.ofLimbDigitsPow2 3 #[4, 4, 1]) = AzNat.ofLimbs #[100]
-- 2^65 in base 32: digit 13 = 1, others 0. Reconstructs limbs [0, 2].
#guard (AzNat.ofLimbDigitsPow2 5 #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1])
       = AzNat.ofLimbs #[0, 2]
-- Zero digits → zero.
#guard (AzNat.ofLimbDigitsPow2 3 #[]) = (0 : AzNat)

-- Degenerate (k out of range).
#guard (AzNat.ofLimbDigitsPow2 0 #[42]) = (0 : AzNat)
#guard (AzNat.ofLimbDigitsPow2 65 #[42]) = (0 : AzNat)

-- Round-trip with `limbDigitsPow2`: `ofLimbDigitsPow2 k (limbDigitsPow2 k n) = n`.
#guard AzNat.ofLimbDigitsPow2 64 ((AzNat.ofLimbs #[0, 1]).limbDigitsPow2 64)
       = AzNat.ofLimbs #[0, 1]
#guard AzNat.ofLimbDigitsPow2 4 ((AzNat.ofLimbs #[100]).limbDigitsPow2 4)
       = AzNat.ofLimbs #[100]
#guard AzNat.ofLimbDigitsPow2 3 ((AzNat.ofLimbs #[100]).limbDigitsPow2 3)
       = AzNat.ofLimbs #[100]
#guard AzNat.ofLimbDigitsPow2 5 ((AzNat.ofLimbs #[0, 2]).limbDigitsPow2 5)
       = AzNat.ofLimbs #[0, 2]
-- Larger cross-limb round-trip.
#guard AzNat.ofLimbDigitsPow2 7
         ((Azurite.AzNat.parse "36893488147419103233".toList).get!.limbDigitsPow2 7)
       = (Azurite.AzNat.parse "36893488147419103233".toList).get!

end Azurite
