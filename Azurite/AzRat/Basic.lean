import Azurite.AzNat.Gcd

/-!
# AzRat: computable rationals

`AzRat` is a sign-magnitude rational in lowest terms, built on `AzNat`:
- a `sign : Bool` (`true` = nonnegative),
- an `AzNat` numerator magnitude `num` and denominator `den`,
- a proof `den ≠ 0`,
- a proof that the sign is positive when the numerator is zero (so zero has a canonical form),
- a proof that `num` and `den` are coprime (`AzNat.coprime`), i.e. the fraction is reduced.

The value represented is `(if sign then 1 else -1) * num / den`.
-/

namespace Azurite

/-- A computable rational number: a sign, an `AzNat` numerator and denominator in lowest terms. -/
structure AzRat where
  /-- Sign of the rational (`true` = nonnegative). -/
  sign : Bool
  /-- Numerator magnitude (nonnegative). -/
  num : AzNat
  /-- Denominator. -/
  den : AzNat
  /-- The denominator is nonzero. -/
  den_nz : den ≠ 0
  /-- Zero is represented with a positive sign (canonical form). -/
  zero_sign : num = 0 → sign = true
  /-- The numerator and denominator are coprime (the fraction is reduced). -/
  reduced : AzNat.coprime num den = true
  deriving DecidableEq

namespace AzRat

/-- Two `AzRat`s are equal when their sign, numerator, and denominator agree (the remaining fields
are propositions, hence proof-irrelevant). -/
@[ext] theorem ext {p q : AzRat} (hs : p.sign = q.sign) (hn : p.num = q.num) (hd : p.den = q.den) :
    p = q := by
  cases p; cases q
  cases hs; cases hn; cases hd
  rfl

end AzRat

end Azurite
