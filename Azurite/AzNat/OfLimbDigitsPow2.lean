import Azurite.AzNat.OfLimbs
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

end Azurite
