import Azurite.AzNat.GetBits
import Azurite.AzNat.OfLimbs
import Azurite.UInt64.Digits

namespace Azurite

/-- `n.limbDigitsPow2 k` returns the base-`2^k` digits of `n`, LSB-first,
    with trailing zeros trimmed (matching `Nat.digits (2^k) n.toNat`).
    Intended for `k ∈ [1, 64]`.

    Dispatches on the relationship between `k` and the limb width `64`:

    * `k = 64`: each limb is one digit. The `AzNat` invariant
      `back? ≠ some 0` ensures the limb array already has no trailing
      zeros, so we return it unchanged.
    * `k | 64` with `k < 64` (i.e., `k ∈ {1, 2, 4, 8, 16, 32}`): digits
      fit inside limbs, so each limb produces exactly `64 / k` digits via
      `UInt64.digitsPow2` (zero-padded to that width, since `digitsPow2`
      trims trailing zeros within a single limb). The concatenated result
      is then trimmed once at the end.
    * `k ∤ 64` with `k ∈ [1, 63]`: digits span limb boundaries; each digit
      is read via `AzNat.getBitsAsLimb`, then trimmed at the end.
    * Other `k` (zero or above 64): returns `#[]`. -/
def AzNat.limbDigitsPow2 (k : Nat) (n : AzNat) : Array UInt64 :=
  if k = 64 then
    n.limbs
  else if _h1 : 1 ≤ k ∧ k < 64 ∧ 64 % k = 0 then
    let perLimb := 64 / k
    let raw := n.limbs.foldl (init := (#[] : Array UInt64)) fun acc l =>
      let d := UInt64.digitsPow2 k l
      let padded :=
        if d.size < perLimb then d ++ Array.replicate (perLimb - d.size) (0 : UInt64)
        else d
      acc ++ padded
    AzNat.trimTrailingZeros raw
  else if h2 : 1 ≤ k ∧ k < 64 then
    let totalBits := n.limbs.size * 64
    let numDigits := (totalBits + k - 1) / k
    let raw := Array.ofFn (n := numDigits) fun i =>
      n.getBitsAsLimb (i.val * k) (i.val * k + k) (by have := h2.2; omega)
    AzNat.trimTrailingZeros raw
  else
    #[]

-- Sanity checks.

-- k = 64 short-circuit: limbs ARE the digits.
-- 2^64 = 1 + 1*2^64, limbs = [0, 1]
#guard ((AzNat.ofLimbs #[0, 1]).limbDigitsPow2 64) = #[0, 1]
-- AzNat 100 fits in one limb.
#guard ((AzNat.ofLimbs #[100]).limbDigitsPow2 64) = #[100]
-- Zero: empty digit array.
#guard ((0 : AzNat).limbDigitsPow2 64) = #[]

-- k | 64 with k < 64 (digitsPow2 path).
-- 100 in base 16 = 0x64, LSB-first hex digits [4, 6].
#guard ((AzNat.ofLimbs #[100]).limbDigitsPow2 4) = #[4, 6]
-- 0xFFFF_FFFF_FFFF_FFFF in base 16 = 16 hex Fs.
#guard ((AzNat.ofLimbs #[0xFFFF_FFFF_FFFF_FFFF]).limbDigitsPow2 4) =
       #[0xF, 0xF, 0xF, 0xF, 0xF, 0xF, 0xF, 0xF, 0xF, 0xF, 0xF, 0xF, 0xF, 0xF, 0xF, 0xF]
-- Cross-limb in base 2^32: limbs [a, b] split as [a-low, a-high, b-low, b-high].
-- 1 + 1*2^64 has limbs [1, 1], in base 2^32 digits [1, 0, 1] (trailing zero from b-high trimmed).
#guard ((AzNat.ofLimbs #[1, 1]).limbDigitsPow2 32) = #[1, 0, 1]

-- k ∤ 64 (getBits path).
-- 100 in base 8 (k=3): 100 = 4 + 4*8 + 1*64 = 0o144, LSB-first [4, 4, 1].
#guard ((AzNat.ofLimbs #[100]).limbDigitsPow2 3) = #[4, 4, 1]
-- Cross-limb base 2^5: 2^64 = ... base 32. 2^64 / 32^12 = 32^... let's just check digit 12.
-- 2^64 has limbs [0, 1]. In base 32: 2^64 = 32^(64/5) ... not clean.
-- Instead, check a simpler cross-limb pattern via 2^65 = 36893488147419103232.
-- Limbs of 2^65 = [0, 2]. In base 32 (k=5): 2^65 = 2 * 2^64 = 2 * 32^12.8 — fractional.
-- Just check round-trip property: bit 65 should appear at base-32 position 13.
-- digit 13 = bits [65, 70) of n. Bit 65 = 1, rest 0. So digit 13 = 1. All others below are 0.
#guard ((AzNat.ofLimbs #[0, 2]).limbDigitsPow2 5) =
       #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
-- Zero gives empty.
#guard ((0 : AzNat).limbDigitsPow2 3) = #[]

-- Degenerate (k out of range).
#guard ((AzNat.ofLimbs #[42]).limbDigitsPow2 0) = #[]
#guard ((AzNat.ofLimbs #[42]).limbDigitsPow2 65) = #[]

end Azurite
