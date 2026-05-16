import Azurite.AzNat.Karatsuba
import Azurite.AzNat.LimbDigits
import Azurite.AzNat.OfLimbDigitsPow2
import Azurite.UInt64.MaxPow
import Azurite.UInt64.OfDigits

namespace Azurite

/-- Constant-folded base-10 specialisation: reconstructs an `AzNat` from
    its base-10 digit array using the precomputed `UInt64.maxPow10` and
    `UInt64.maxPow10Exp`, skipping the runtime `UInt64.maxPow 10` call.
    Functionally equivalent to `AzNat.ofLimbDigits 10`. -/
def AzNat.ofBase10Digits (digits : Array UInt64) : AzNat :=
  let E := UInt64.maxPow10Exp
  let P := UInt64.maxPow10
  let numSuperDigits := (digits.size + E - 1) / E
  let superDigits : Array UInt64 := Array.ofFn (n := numSuperDigits) fun i =>
    let chunkStart := i.val * E
    let chunkEnd := min (chunkStart + E) digits.size
    UInt64.ofDigits 10 (digits.extract chunkStart chunkEnd)
  let PNat : AzNat := AzNat.ofLimbs #[P]
  superDigits.foldr (init := (0 : AzNat)) fun d acc =>
    acc * PNat + AzNat.ofLimbs #[d]

/-- `ofLimbDigits b digits` reconstructs an `AzNat` from its base-`b`
    digit array (LSB-first), the left inverse of `AzNat.limbDigits b`.
    Intended for `b ∈ [2, 2^64 - 1]` with every digit `< b.toNat`.

    Dispatches symmetric to `limbDigits`:

    * `b < 2`: degenerate; returns `0`.
    * `b` is a power of two: delegates to
      `ofLimbDigitsPow2 (ctz b) digits`, which avoids any general-base
      multiplication.
    * `b = 10`: delegates to `ofBase10Digits digits`, which uses the
      precomputed `UInt64.maxPow10` / `UInt64.maxPow10Exp` instead of
      recomputing `UInt64.maxPow 10` at every call.
    * otherwise: with `(P, E) := UInt64.maxPow b` (so `P = b^E` is the
      largest power of `b` in `[2, 2^64)`), regroup `digits` into
      `⌈|digits| / E⌉` super-digits via `UInt64.ofDigits b` on each
      `E`-digit chunk (each super-digit fits in a `UInt64` because
      every base-`b` digit is `< b` and `b^E < 2^64`), then run
      Horner's scheme over the super-digits to build the `AzNat`:
      `acc := acc * P + d`, walked MSB-first via `Array.foldr`. -/
def AzNat.ofLimbDigits (b : UInt64) (digits : Array UInt64) : AzNat :=
  if b < 2 then 0
  else if b.isPowerOfTwo then
    AzNat.ofLimbDigitsPow2 b.toBitVec.ctz.toNat digits
  else if b = 10 then
    AzNat.ofBase10Digits digits
  else
    let P := (UInt64.maxPow b).1
    let E := (UInt64.maxPow b).2
    let numSuperDigits := (digits.size + E - 1) / E
    let superDigits : Array UInt64 := Array.ofFn (n := numSuperDigits) fun i =>
      let chunkStart := i.val * E
      let chunkEnd := min (chunkStart + E) digits.size
      UInt64.ofDigits b (digits.extract chunkStart chunkEnd)
    let PNat : AzNat := AzNat.ofLimbs #[P]
    superDigits.foldr (init := (0 : AzNat)) fun d acc =>
      acc * PNat + AzNat.ofLimbs #[d]

-- Sanity checks.

-- Direct reconstruction in various bases.
#guard AzNat.ofLimbDigits 10 #[5, 4, 3, 2, 1] = AzNat.ofLimbs #[12345]
#guard AzNat.ofLimbDigits 10 #[] = (0 : AzNat)

-- Base-10 specialisation agrees with the general path.
#guard AzNat.ofBase10Digits #[5, 4, 3, 2, 1] = AzNat.ofLimbs #[12345]
#guard AzNat.ofBase10Digits #[] = (0 : AzNat)
-- Cross-`10^19` super-digit boundary: 2^65 + 1 = 36893488147419103233 has 20
-- decimal digits, so it spans two super-digits.
#guard AzNat.ofBase10Digits ((Azurite.AzNat.parse "36893488147419103233".toList).get!.limbDigits 10)
       = (Azurite.AzNat.parse "36893488147419103233".toList).get!
#guard AzNat.ofLimbDigits 16 #[0xF, 0xE, 0xE, 0xB, 0xD, 0xA, 0xE, 0xD] =
       AzNat.ofLimbs #[0xDEADBEEF]
#guard AzNat.ofLimbDigits 2 #[0, 1, 1, 0, 1] = AzNat.ofLimbs #[0b10110]
#guard AzNat.ofLimbDigits 8 #[5, 5, 7] = AzNat.ofLimbs #[0o755]

-- Degenerate bases.
#guard AzNat.ofLimbDigits 0 #[1, 2, 3] = (0 : AzNat)
#guard AzNat.ofLimbDigits 1 #[0, 0] = (0 : AzNat)

-- Round-trip with limbDigits across multiple bases.
#guard AzNat.ofLimbDigits 10 ((AzNat.ofLimbs #[12345]).limbDigits 10)
       = AzNat.ofLimbs #[12345]
#guard AzNat.ofLimbDigits 16 ((AzNat.ofLimbs #[0xDEADBEEF]).limbDigits 16)
       = AzNat.ofLimbs #[0xDEADBEEF]
#guard AzNat.ofLimbDigits 2 ((AzNat.ofLimbs #[0xDEADBEEF]).limbDigits 2)
       = AzNat.ofLimbs #[0xDEADBEEF]
-- Multi-limb round-trip (2^65 + 1).
#guard AzNat.ofLimbDigits 10
         ((Azurite.AzNat.parse "36893488147419103233".toList).get!.limbDigits 10)
       = (Azurite.AzNat.parse "36893488147419103233".toList).get!
-- Large base, multi-limb.
#guard AzNat.ofLimbDigits 7
         ((Azurite.AzNat.parse "36893488147419103233".toList).get!.limbDigits 7)
       = (Azurite.AzNat.parse "36893488147419103233".toList).get!
-- Power-of-two base (delegates to ofLimbDigitsPow2).
#guard AzNat.ofLimbDigits 16
         ((Azurite.AzNat.parse "36893488147419103233".toList).get!.limbDigits 16)
       = (Azurite.AzNat.parse "36893488147419103233".toList).get!

end Azurite
