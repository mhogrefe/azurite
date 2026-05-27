import Azurite.AzNat.Compare
import Azurite.AzNat.ShiftLeft
import Azurite.AzNat.ShiftRight
import Azurite.AzNat.Sub
import Azurite.AzNat.TrailingZeros

namespace Azurite.AzNat

/-!
## Binary GCD (Stein's algorithm) — limb-level

Implements Algorithm 1.18 (BinaryGcd) from "Modern Computer Arithmetic" (Brent
& Zimmermann), with the optimisation that each "shift out trailing zeros" step
uses hardware `ctz` per limb + a single bulk right-shift, rather than repeated
shift-by-one.
-/

/-- Right-shift a limb array by its trailing zeros count, then trim.
    The input must represent a positive number (nonempty, at least one
    nonzero limb).  The result is odd. -/
def makeOddLimbs (a : Array UInt64) : Array UInt64 :=
  trimTrailingZeros (shrLimbs a (trailingZerosLimbs a))

/-! ### Limb-level GCD loop -/

/-- Core binary GCD loop on two trimmed, odd, positive limb arrays.
    Returns the limb array of their GCD (without the common power-of-two
    factor, which the caller must shift back in).

    `fuel` bounds the number of iterations; `64 * (a.size + b.size)` is a
    safe upper bound since each step strictly reduces the bit length of
    one operand. -/
def gcdOddLimbs (a b : Array UInt64) (fuel : Nat)
    (ha : 0 < a.size) (hb : 0 < b.size) : Array UInt64 :=
  match fuel with
  | 0 => a
  | fuel' + 1 =>
    if h_eqsz : a.size = b.size then
      match compareLimbs a b 0 0 a.size (by omega) (by omega) with
      | Ordering.eq => a
      | Ordering.gt =>
        let sub := subSameLengthLimbs a b 0 0 a.size (by omega) (by omega)
        let diff := makeOddLimbs sub.1
        if hd : 0 < diff.size then gcdOddLimbs diff b fuel' hd hb
        else b
      | Ordering.lt =>
        let sub := subSameLengthLimbs b a 0 0 b.size (by omega) (by omega)
        let diff := makeOddLimbs sub.1
        if hd : 0 < diff.size then gcdOddLimbs a diff fuel' ha hd
        else a
    else if h_gt : a.size > b.size then
      let sub := subGeqLimbs a b 0 a.size 0 b.size
        (by omega) (by omega) (Nat.le_of_lt h_gt) ha hb
      let diff := makeOddLimbs (trimTrailingZeros sub.1)
      if hd : 0 < diff.size then gcdOddLimbs diff b fuel' hd hb
      else b
    else
      have h_lt : b.size > a.size := by omega
      let sub := subGeqLimbs b a 0 b.size 0 a.size
        (by omega) (by omega) (Nat.le_of_lt h_lt) hb ha
      let diff := makeOddLimbs (trimTrailingZeros sub.1)
      if hd : 0 < diff.size then gcdOddLimbs a diff fuel' ha hd
      else a

/-! ### Limb-level entry point -/

/-- Limb-level binary GCD.  Takes two limb arrays (sub-arrays of a shared
    buffer, specified by `(lo, len)` pairs) and returns the GCD as a
    fresh limb array.

    Handles the shared power-of-two factor: extracts the common trailing
    zeros, makes both operands odd, runs the GCD loop, and shifts the
    result back.  Returns an empty array if both inputs are zero-length. -/
def gcdLimbs (buf : Array UInt64) (loA lenA loB lenB : Nat)
    (_hA : loA + lenA ≤ buf.size) (_hB : loB + lenB ≤ buf.size) :
    Array UInt64 :=
  let a := trimTrailingZeros (buf.extract loA (loA + lenA))
  let b := trimTrailingZeros (buf.extract loB (loB + lenB))
  if _ha : a.size = 0 then b
  else if _hb : b.size = 0 then a
  else
    let tzA := trailingZerosLimbs a
    let tzB := trailingZerosLimbs b
    let commonTz := min tzA tzB
    let aOdd := makeOddLimbs (shrLimbs a commonTz)
    let bOdd := makeOddLimbs (shrLimbs b commonTz)
    let fuel := 64 * (a.size + b.size)
    if haO : 0 < aOdd.size then
      if hbO : 0 < bOdd.size then
        let result := gcdOddLimbs aOdd bOdd fuel haO hbO
        if commonTz = 0 then result
        else (shiftLeft (ofLimbs result) commonTz).limbs
      else a
    else b

/-! ### AzNat-level entry point -/

/-- Binary GCD of two `AzNat`s.  Returns `gcd(a, b)`.

    Special cases: `gcd(0, b) = b`, `gcd(a, 0) = a`.  Otherwise extracts
    the common power-of-two factor, makes both operands odd, runs the
    limb-level binary GCD loop, and shifts the result back. -/
def gcd (a b : AzNat) : AzNat :=
  if a.limbs.size = 0 then b
  else if b.limbs.size = 0 then a
  else
    let tzA := trailingZerosLimbs a.limbs
    let tzB := trailingZerosLimbs b.limbs
    let commonTz := min tzA tzB
    let aOdd := makeOddLimbs (shrLimbs a.limbs commonTz)
    let bOdd := makeOddLimbs (shrLimbs b.limbs commonTz)
    let fuel := 64 * (a.limbs.size + b.limbs.size)
    if haO : 0 < aOdd.size then
      if hbO : 0 < bOdd.size then
        let result := gcdOddLimbs aOdd bOdd fuel haO hbO
        ofLimbs result <<< commonTz
      else a
    else b

end Azurite.AzNat

/-! ### Tests -/

section Tests

open Azurite Azurite.AzNat

private def n (k : Nat) : AzNat := ofLimbs (go k #[])
where go (k : Nat) (acc : Array UInt64) : Array UInt64 :=
  if k = 0 then acc
  else go (k / 2 ^ 64) (acc.push (UInt64.ofNat k))
  termination_by k

#guard gcd (n 0) (n 0) = n 0
#guard gcd (n 0) (n 7) = n 7
#guard gcd (n 7) (n 0) = n 7
#guard gcd (n 1) (n 1) = n 1
#guard gcd (n 6) (n 4) = n 2
#guard gcd (n 12) (n 8) = n 4
#guard gcd (n 54) (n 24) = n 6
#guard gcd (n 48) (n 18) = n 6
#guard gcd (n 100) (n 75) = n 25
#guard gcd (n 17) (n 13) = n 1
#guard gcd (n 1024) (n 512) = n 512
#guard gcd (n 7) (n 7) = n 7
#guard gcd (n 255) (n 85) = n 85
#guard gcd (n 10000) (n 2500) = n 2500
-- Powers of two
#guard gcd (n (2^128)) (n (2^64)) = n (2^64)
-- Multi-limb: (2^128 - 1) = 3 * 5 * 17 * 257 * 641 * 65537 * 6700417 * ...
-- gcd with (2^64 - 1) = 3 * 5 * 17 * 257 * 641 * 65537 * 6700417
#guard gcd (n (2^128 - 1)) (n (2^64 - 1)) = n (2^64 - 1)
-- Large with shared factor
#guard gcd (n (2^256 * 3 * 7)) (n (2^256 * 5 * 7)) = n (2^256 * 7)
-- Coprime multi-limb
#guard gcd (n (2^128 + 1)) (n (2^128 - 1)) = n 1

end Tests
