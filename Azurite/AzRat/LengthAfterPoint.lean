/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzRat.Basic
import Azurite.AzNat.Div
import Azurite.AzNat.Equiv.Div.DivModLimb

/-!
# Length of a terminating base-`b` expansion

`AzRat.lengthAfterPoint b q` is the number of base-`b` digits after the point in the expansion
of `q`, or `none` when the expansion does not terminate (the denominator has a prime factor
not dividing `b`).  Port of the author's `Rational::length_after_point_in_small_base`
(Malachite): with `b = ∏ pᵢ^mᵢ` (the table `basePrimeFactors`, bases `2`–`36`), strip each
`pᵢ` from the reduced denominator, counting its multiplicity `cᵢ`; the answer is
`max ⌈cᵢ / mᵢ⌉`, and the expansion terminates iff nothing but `1` is left.

Specification (`Equiv/LengthAfterPoint.lean`): `lengthAfterPoint b q = some L` iff `L` is the
least `ℓ` with `q.den ∣ b^ℓ`, i.e. the least `ℓ` with `q · b^ℓ` an integer.
-/

namespace Azurite.AzRat

/-- The prime factorization `[(p₁, m₁), …]` of each base `2 ≤ b ≤ 36` (`[]` otherwise). -/
def basePrimeFactors : Nat → List (UInt64 × Nat)
  | 2 => [(2, 1)]            | 3 => [(3, 1)]            | 4 => [(2, 2)]
  | 5 => [(5, 1)]            | 6 => [(2, 1), (3, 1)]    | 7 => [(7, 1)]
  | 8 => [(2, 3)]            | 9 => [(3, 2)]            | 10 => [(2, 1), (5, 1)]
  | 11 => [(11, 1)]          | 12 => [(2, 2), (3, 1)]   | 13 => [(13, 1)]
  | 14 => [(2, 1), (7, 1)]   | 15 => [(3, 1), (5, 1)]   | 16 => [(2, 4)]
  | 17 => [(17, 1)]          | 18 => [(2, 1), (3, 2)]   | 19 => [(19, 1)]
  | 20 => [(2, 2), (5, 1)]   | 21 => [(3, 1), (7, 1)]   | 22 => [(2, 1), (11, 1)]
  | 23 => [(23, 1)]          | 24 => [(2, 3), (3, 1)]   | 25 => [(5, 2)]
  | 26 => [(2, 1), (13, 1)]  | 27 => [(3, 3)]           | 28 => [(2, 2), (7, 1)]
  | 29 => [(29, 1)]          | 30 => [(2, 1), (3, 1), (5, 1)] | 31 => [(31, 1)]
  | 32 => [(2, 5)]           | 33 => [(3, 1), (11, 1)]  | 34 => [(2, 1), (17, 1)]
  | 35 => [(5, 1), (7, 1)]   | 36 => [(2, 2), (3, 2)]
  | _ => []

/-- Strip the factor `p` (a limb, `2 ≤ p`) from `n`: returns `(c, m)` with `n = p^c · m` and
`p ∤ m`.  For `n = 0` or `p < 2` returns `(0, n)`. -/
def countFactor (p : UInt64) (n : AzNat) : Nat × AzNat :=
  if hp : 2 ≤ p.toNat then
    if h0 : n = 0 then (0, n)
    else
      have hp0 : p ≠ 0 := by
        intro h; rw [h] at hp; exact absurd hp (by decide)
      let qr := AzNat.divModUInt64 n p hp0
      if qr.2 = 0 then
        let r := countFactor p qr.1
        (r.1 + 1, r.2)
      else (0, n)
  else (0, n)
  termination_by n.toNat
  decreasing_by
    have h := AzNat.toNat_divModUInt64 n p hp0
    simp only at h
    have hn : n.toNat ≠ 0 := by
      intro hz; exact h0 (AzNat.toNat_injective (by rw [hz]; rfl))
    have h2 : (AzNat.divModUInt64 n p hp0).1.toNat * 2
        ≤ (AzNat.divModUInt64 n p hp0).1.toNat * p.toNat := Nat.mul_le_mul_left _ hp
    omega

/-- Malachite's `length_after_point_in_small_base`: the number of base-`b` digits after the
point in the expansion of `q`, or `none` if it does not terminate.  Requires `2 ≤ b ≤ 36`
(`none` otherwise). -/
def lengthAfterPoint (b : UInt64) (q : AzRat) : Option Nat :=
  if 2 ≤ b.toNat ∧ b.toNat ≤ 36 then
    let r := (basePrimeFactors b.toNat).foldl
      (fun (acc : Nat × AzNat) (pm : UInt64 × Nat) =>
        let s := countFactor pm.1 acc.2
        (max acc.1 ((s.1 + pm.2 - 1) / pm.2), s.2))
      (0, q.den)
    if r.2 = 1 then some r.1 else none
  else none

end Azurite.AzRat
