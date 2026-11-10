/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzNat.Gcd.Binary
import Azurite.AzNat.Gcd.HalfBinary
import Azurite.AzNat.Div

/-!
## Greatest common divisor

`AzNat.gcd` first balances operands of very different sizes by remainder steps
(`gcdUnbalanced`), then dispatches on the operand size: Euclid's algorithm on `UInt64` for
single limbs and the binary GCD (`Gcd/Binary.lean`) up to `halfBinaryGcdThreshold` bits, the
subquadratic half-binary GCD (`Gcd/HalfBinary.lean`, MCA §1.6.3) above.  `coprime` is the coprimality test.
-/

namespace Azurite.AzNat

/-- The size difference (bits) above which `gcd` first takes a remainder. -/
def unbalancedGcdGap : Nat := 64

/-- The number of balancing remainder steps `gcd` may take (each needs a size gap of more than
`unbalancedGcdGap` bits, so more than a few in a row is rare; any value is correct). -/
def unbalancedGcdSteps : Nat := 8


/-- GCD of two `AzNat`s of comparable sizes: binary GCD below `halfBinaryGcdThreshold` bits,
half-binary GCD above. -/
def gcdBalanced (a b : AzNat) : AzNat :=
  if max a.size b.size ≤ halfBinaryGcdThreshold then gcdBinary a b else gcdHalfBinary a b

/-- Euclidean steps while the operands are unbalanced: when one operand is more than
`unbalancedGcdGap` bits longer than the other (nonzero) one, it is replaced by its remainder
(one division, linear in the longer operand for a short divisor); at most `fuel` such steps,
then `gcdBalanced`.  Both the binary and the half-binary GCD gain only a bounded number of bits
per step, so on operands of very different sizes they are quadratic in the *longer* one. -/
def gcdUnbalanced : Nat → AzNat → AzNat → AzNat
  | 0, a, b => gcdBalanced a b
  | fuel + 1, a, b =>
    if b.size ≠ 0 ∧ b.size + unbalancedGcdGap < a.size then gcdUnbalanced fuel b (a % b)
    else if a.size ≠ 0 ∧ a.size + unbalancedGcdGap < b.size then gcdUnbalanced fuel a (b % a)
    else gcdBalanced a b

/-- GCD of two `AzNat`s: `gcd 0 b = b`, `gcd a 0 = a`.  Up to `unbalancedGcdSteps` Euclidean
steps balance the operands (`gcdUnbalanced`); then the binary GCD below
`halfBinaryGcdThreshold` bits, the half-binary GCD above. -/
def gcd (a b : AzNat) : AzNat := gcdUnbalanced unbalancedGcdSteps a b

/-- Coprimality test.  Returns `true` iff `gcd(a, b) = 1`.
    Short-circuits: if both arguments are even, returns `false` without
    computing the GCD (two even numbers share the factor 2). -/
def coprime (a b : AzNat) : Bool :=
  if a.isEven && b.isEven then false
  else gcd a b == 1

end Azurite.AzNat
/-! ### Tests -/

section Tests

open Azurite Azurite.AzNat

private def n (k : Nat) : AzNat := ofLimbs (go k #[])
where go (k : Nat) (acc : Array UInt64) : Array UInt64 :=
  if k = 0 then acc
  else go (k / 2 ^ 64) (acc.push (UInt64.ofNat k))
  termination_by k

#guard AzNat.toString (gcd (n 0) (n 0)) == "0"
#guard AzNat.toString (gcd (n 0) (n 7)) == "7"
#guard AzNat.toString (gcd (n 7) (n 0)) == "7"
#guard AzNat.toString (gcd (n 1) (n 1)) == "1"
#guard AzNat.toString (gcd (n 6) (n 4)) == "2"
#guard AzNat.toString (gcd (n 12) (n 8)) == "4"
#guard AzNat.toString (gcd (n 54) (n 24)) == "6"
#guard AzNat.toString (gcd (n 48) (n 18)) == "6"
#guard AzNat.toString (gcd (n 100) (n 75)) == "25"
#guard AzNat.toString (gcd (n 17) (n 13)) == "1"
#guard AzNat.toString (gcd (n 1024) (n 512)) == "512"
#guard AzNat.toString (gcd (n 7) (n 7)) == "7"
#guard AzNat.toString (gcd (n 255) (n 85)) == "85"
#guard AzNat.toString (gcd (n 10000) (n 2500)) == "2500"
-- Powers of two
#guard AzNat.toString (gcd (n (2^128)) (n (2^64))) == "18446744073709551616"
-- Multi-limb: (2^128 - 1) = 3 * 5 * 17 * 257 * 641 * 65537 * 6700417 * ...
-- gcd with (2^64 - 1) = 3 * 5 * 17 * 257 * 641 * 65537 * 6700417
#guard AzNat.toString (gcd (n (2^128 - 1)) (n (2^64 - 1))) == "18446744073709551615"
-- Large with shared factor (huge 2^256-scale target: left as an algorithm-level
-- equality rather than a string literal, for readability)
#guard gcd (n (2^256 * 3 * 7)) (n (2^256 * 5 * 7)) = n (2^256 * 7)
-- Coprime multi-limb
#guard AzNat.toString (gcd (n (2^128 + 1)) (n (2^128 - 1))) == "1"

-- Unbalanced operands: balanced by remainder steps first (`gcdUnbalanced`)
#guard AzNat.toString (gcd (n (2^1000 * 3)) (n 7)) == "1"
#guard AzNat.toString (gcd (n 7) (n (2^1000 * 21))) == "7"
#guard AzNat.toString (gcd (n (2^1000 + 1)) (n 0)) == AzNat.toString (n (2^1000 + 1))
#guard AzNat.toString (gcd (n 0) (n (2^1000 + 1))) == AzNat.toString (n (2^1000 + 1))
#guard gcd (n (2^3000 * 15 * (2^200 + 1))) (n (9 * (2^200 + 1))) = n (3 * (2^200 + 1))
#guard gcd (n (3^5000)) (n (3^40 * 2^70)) = n (3^40)
#guard coprime (n 1) (n (2^100000 * 3)) = true

-- coprime tests
#guard coprime (n 1) (n 1) = true
#guard coprime (n 3) (n 5) = true
#guard coprime (n 6) (n 4) = false   -- both even, short-circuit
#guard coprime (n 9) (n 6) = false    -- gcd(9,6) = 3
#guard coprime (n 9) (n 4) = true     -- gcd(9,4) = 1
#guard coprime (n 7) (n 15) = true
#guard coprime (n 0) (n 1) = true
#guard coprime (n 0) (n 0) = false
#guard coprime (n 17) (n 13) = true
#guard coprime (n 100) (n 21) = true
#guard coprime (n (2^128 + 1)) (n (2^128 - 1)) = true

end Tests
