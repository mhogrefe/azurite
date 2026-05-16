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

end Azurite
