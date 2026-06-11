import Azurite.AzRat.Construct
import Azurite.AzRat.Parse
import Azurite.AzRat.ToString
import Azurite.AzNat.Pow
import Azurite.AzNat.Equiv.Pow

/-!
# Exponentiation for `AzRat`

`q ^ n` for reduced fractions: numerator and denominator are powered
separately by `AzNat`'s sliding-window exponentiation (`AzNat.pow`), and
**no reduction is ever needed** — coprime numbers stay coprime under powers
(`Nat.Coprime.pow`). The sign rule is `AzInt.pow`'s: the result is
nonnegative unless the base is negative and the exponent odd.

`zpow` extends to integer exponents: a negative exponent powers with the
numerator and denominator roles swapped (the reciprocal of a reduced
fraction is the swap), with `0 ^ (-k) = 0` following the `GroupWithZero`
convention `0⁻¹ = 0`. Despite the direct implementation,
`q.zpow (-(k+1)) = (q.pow (k+1))⁻¹` holds *structurally*
(`zpow_negSucc` in `Azurite/AzRat/Equiv/Pow.lean`).

These are installed as the `npow` and `zpow` of the `Field` instance
(`Azurite/AzRat/Instances.lean`), so `q ^ (n : ℕ)` and `q ^ (z : ℤ)` run
the same fast algorithms and `q.pow n = q ^ n` definitionally.
-/

namespace Azurite.AzRat

/-- Exponentiation for `AzRat` by a natural exponent: numerator and
denominator are powered separately (sliding-window via `AzNat.pow`), with no
reduction needed — powers of coprimes are coprime. The result is nonnegative
unless `q` is negative and `n` is odd. This is the `Field`'s `npow`, so it
is definitionally equal to `q ^ n`. -/
protected def pow (q : AzRat) (n : ℕ) : AzRat where
  sign := q.sign || (n % 2 == 0)
  num := q.num.pow n
  den := q.den.pow n
  den_nz := fun h => by
    have h0 := congrArg AzNat.toNat h
    rw [AzNat.toNat_pow, AzNat.toNat_zero] at h0
    exact q.den_nz (AzNat.toNat_injective (by
      rw [(Nat.pow_eq_zero.mp h0).1, AzNat.toNat_zero]))
  zero_sign := fun h => by
    have h0 := congrArg AzNat.toNat h
    rw [AzNat.toNat_pow, AzNat.toNat_zero] at h0
    have hq : q.num = 0 := AzNat.toNat_injective (by
      rw [(Nat.pow_eq_zero.mp h0).1, AzNat.toNat_zero])
    rw [q.zero_sign hq, Bool.true_or]
  reduced := (AzNat.coprime_iff _ _).mpr (by
    rw [AzNat.toNat_pow, AzNat.toNat_pow]
    exact ((AzNat.coprime_iff _ _).mp q.reduced).pow n n)

/-- Exponentiation for `AzRat` by an integer exponent: nonnegative
exponents delegate to `AzRat.pow`; a negative exponent `-(k+1)` runs the
same powers with the numerator and denominator roles swapped (the
reciprocal of a reduced fraction is the swap, so no extra work is needed),
with `0 ^ -(k+1) = 0` (the `GroupWithZero` convention). This is the
`Field`'s `zpow`, so it is definitionally equal to `q ^ z`. -/
protected def zpow (q : AzRat) : ℤ → AzRat
  | .ofNat n => q.pow n
  | .negSucc n =>
    if h : q.num = 0 then 0
    else
      { sign := q.sign || ((n + 1) % 2 == 0)
        num := q.den.pow (n + 1)
        den := q.num.pow (n + 1)
        den_nz := fun h0 => by
          have h1 := congrArg AzNat.toNat h0
          rw [AzNat.toNat_pow, AzNat.toNat_zero] at h1
          exact h (AzNat.toNat_injective (by
            rw [(Nat.pow_eq_zero.mp h1).1, AzNat.toNat_zero]))
        zero_sign := fun h0 => by
          have h1 := congrArg AzNat.toNat h0
          rw [AzNat.toNat_pow, AzNat.toNat_zero] at h1
          exact absurd (AzNat.toNat_injective (by
            rw [(Nat.pow_eq_zero.mp h1).1, AzNat.toNat_zero]) : q.den = 0) q.den_nz
        reduced := (AzNat.coprime_iff _ _).mpr (by
          rw [AzNat.toNat_pow, AzNat.toNat_pow]
          exact ((AzNat.coprime_iff _ _).mp q.reduced).symm.pow (n + 1) (n + 1)) }

end Azurite.AzRat

namespace Azurite

-- Sanity checks (string-anchored via `AzRat.parse`/`AzRat.toString`).

#guard ((fun q => AzRat.toString (AzRat.pow q 3)) <$> AzRat.parse "-2/3") == some "-8/27"
#guard ((fun q => AzRat.toString (AzRat.pow q 2)) <$> AzRat.parse "-2/3") == some "4/9"
#guard ((fun q => AzRat.toString (AzRat.pow q 0)) <$> AzRat.parse "5/7") == some "1"
#guard ((fun q => AzRat.toString (AzRat.pow q 5)) <$> AzRat.parse "0") == some "0"
#guard ((fun q => AzRat.toString (AzRat.pow q 0)) <$> AzRat.parse "0") == some "1"
#guard ((fun q => AzRat.toString (AzRat.pow q 10)) <$> AzRat.parse "2") == some "1024"
#guard ((fun q => AzRat.toString (AzRat.zpow q (-2))) <$> AzRat.parse "2/3") == some "9/4"
#guard ((fun q => AzRat.toString (AzRat.zpow q (-3))) <$> AzRat.parse "-1/2") == some "-8"
#guard ((fun q => AzRat.toString (AzRat.zpow q (-2))) <$> AzRat.parse "-1/2") == some "4"
#guard ((fun q => AzRat.toString (AzRat.zpow q (-1))) <$> AzRat.parse "0") == some "0"
#guard ((fun q => AzRat.toString (AzRat.zpow q (-1))) <$> AzRat.parse "5") == some "1/5"
#guard ((fun q => AzRat.toString (AzRat.zpow q 2)) <$> AzRat.parse "7/3") == some "49/9"
#guard ((fun q => AzRat.toString (AzRat.zpow q 0)) <$> AzRat.parse "-3/4") == some "1"

end Azurite
