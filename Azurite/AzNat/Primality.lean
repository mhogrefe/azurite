import Azurite.AzNat.SqrtRem
import Azurite.AzNat.Div
import Azurite.AzNat.Compare
import Azurite.AzNat.Parity
import Azurite.AzNat.Add
import Azurite.AzNat.Conversion
import Azurite.AzNat.ParseBase
import Azurite.AzNat.Equiv.Basic
import Azurite.AzNat.Equiv.Add
import Azurite.AzNat.Equiv.Compare
import Azurite.AzNat.Equiv.Conversion

namespace Azurite.AzNat

/-!
## Naive primality test (trial division)

A deliberately simple `isPrime` for `AzNat`, intended as a placeholder to be
replaced by a real primality test later: handle `< 2`, `2`, and even numbers
directly, then trial-divide by every odd `d` with `3 ≤ d ≤ ⌊√n⌋` (the integer
square root `AzNat.sqrt`).  `n` is prime iff none of those `d` divides it.

Trial division performs up to `~√n` iterations (exponential in the bit length),
so there is no small fuel bound; termination is by well-founded recursion on the
`toNat`-measure `(⌊√n⌋ + 1) − d` (used only in the termination proof — the function
itself runs entirely at the limb level).
-/

/-- Trial-divide `n` by the odd numbers `d, d+2, d+4, …` up to `s = ⌊√n⌋`.
Returns `true` (no divisor found) once `d > s`, `false` as soon as some `d ∣ n`.
Intended to be called with `s = sqrt n` and `d = 3`. -/
def trialDivideOdd (n s d : AzNat) : Bool :=
  if _hgt : compare d s = Ordering.gt then
    true
  else if n % d == 0 then
    false
  else
    trialDivideOdd n s (d + (2 : UInt64).toAzNat)
  termination_by (s.toNat + 1) - d.toNat
  decreasing_by
    have hle : d.toNat ≤ s.toNat := by
      rw [compare_eq_compare_toNat] at _hgt
      exact Nat.le_of_not_lt (fun h => _hgt (Nat.compare_eq_gt.mpr h))
    have htwo : ((2 : UInt64).toAzNat).toNat = 2 := by
      rw [UInt64.toNat_toAzNat]; decide
    have h2 : (d + (2 : UInt64).toAzNat).toNat = d.toNat + 2 := by
      rw [toNat_add, htwo]
    omega

/-- **Naive primality test.**  `n` is prime iff `n ≥ 2`, and (when odd and `> 2`)
no odd `d` with `3 ≤ d ≤ ⌊√n⌋` divides `n`.  Trial division — slow; a placeholder
to be superseded by a fast test. -/
def isPrime (n : AzNat) : Bool :=
  if compare n (2 : UInt64).toAzNat = Ordering.lt then
    false                                         -- n < 2: not prime
  else if n == (2 : UInt64).toAzNat then
    true                                          -- n = 2: prime
  else if n.isEven then
    false                                         -- even and > 2: composite
  else
    trialDivideOdd n (sqrt n) (3 : UInt64).toAzNat

end Azurite.AzNat

/-! ### Tests -/

section Tests

open Azurite Azurite.AzNat

/-- Parse a decimal string into an `AzNat` (exercises the real parse path). -/
private def parse (s : String) : AzNat := (AzNat.parse s).get!

#guard isPrime (parse "0") == false
#guard isPrime (parse "1") == false
#guard isPrime (parse "2") == true
#guard isPrime (parse "3") == true
#guard isPrime (parse "4") == false
#guard isPrime (parse "5") == true
#guard isPrime (parse "7") == true
#guard isPrime (parse "9") == false       -- 3·3
#guard isPrime (parse "15") == false      -- 3·5
#guard isPrime (parse "17") == true
#guard isPrime (parse "25") == false      -- 5·5
#guard isPrime (parse "49") == false      -- 7·7
#guard isPrime (parse "97") == true
#guard isPrime (parse "100") == false
#guard isPrime (parse "221") == false     -- 13·17
#guard isPrime (parse "7919") == true     -- 1000th prime
#guard isPrime (parse "7917") == false    -- 3·7·13·29
#guard isPrime (parse "104729") == true   -- 10000th prime
#guard isPrime (parse "104730") == false

end Tests
