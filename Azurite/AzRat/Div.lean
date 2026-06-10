import Azurite.AzRat.Mul
import Azurite.AzRat.Unary

/-!
# Division for `AzRat`, with cross-gcd reduction

Division duplicates the multiplication algorithm with the roles of the
divisor's numerator and denominator swapped, rather than computing
`x * y⁻¹` — which would allocate an intermediate `AzRat` only to tear it
apart again. The cross-gcds are `g₁ = gcd (num x) (num y)` and
`g₂ = gcd (den x) (den y)`, and the quotient is
`((num x / g₁)·(den y / g₂)) / ((den x / g₂)·(num y / g₁))`, already in
lowest terms by `coprime_cross_mul` (applied to `y`'s coprimality
symmetrized). Division by zero returns `0`, matching the field convention
`x / 0 = 0` in `ℚ`.

Despite the separate implementation, `x / y = x * y⁻¹` holds *structurally*
(`div_eq_mul_inv` in `Azurite/AzRat/Equiv/Div.lean`): `inv` swaps the
divisor's fields, so `mul`'s cross-gcds against `y⁻¹` are syntactically
`div`'s cross-gcds against `y`.
-/

namespace Azurite.AzRat

/-- Divide two `AzRat`s with cross-gcd reduction: exactly two `AzNat.gcd`
computations, on the pairs `(num x, num y)` and `(den x, den y)`, and no
reduction of the products. `x / 0 = 0` (the field convention). -/
protected def div (x y : AzRat) : AzRat :=
  if hx : x.num = 0 then 0
  else if hy : y.num = 0 then 0
  else
    let gan := AzNat.gcd x.num y.num
    let gdd := AzNat.gcd x.den y.den
    have hganN : gan.toNat = Nat.gcd x.num.toNat y.num.toNat := AzNat.toNat_gcd _ _
    have hgddN : gdd.toNat = Nat.gcd x.den.toNat y.den.toNat := AzNat.toNat_gcd _ _
    have hxn : x.num.toNat ≠ 0 :=
      fun h => hx (AzNat.toNat_injective (h.trans AzNat.toNat_zero.symm))
    have hyn : y.num.toNat ≠ 0 :=
      fun h => hy (AzNat.toNat_injective (h.trans AzNat.toNat_zero.symm))
    have hxd : x.den.toNat ≠ 0 :=
      fun h => x.den_nz (AzNat.toNat_injective (h.trans AzNat.toNat_zero.symm))
    have hyd : y.den.toNat ≠ 0 :=
      fun h => y.den_nz (AzNat.toNat_injective (h.trans AzNat.toNat_zero.symm))
    { sign := x.sign == y.sign
      num := x.num / gan * (y.den / gdd)
      den := x.den / gdd * (y.num / gan)
      den_nz := fun h => by
        have h0 := congrArg AzNat.toNat h
        rw [AzNat.toNat_mul, AzNat.toNat_div, AzNat.toNat_div, hganN, hgddN,
            AzNat.toNat_zero] at h0
        have hb' : 0 < x.den.toNat / Nat.gcd x.den.toNat y.den.toNat :=
          Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hxd) (Nat.gcd_dvd_left _ _))
            (Nat.gcd_pos_of_pos_left _ (Nat.pos_of_ne_zero hxd))
        have hc' : 0 < y.num.toNat / Nat.gcd x.num.toNat y.num.toNat :=
          Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hyn) (Nat.gcd_dvd_right _ _))
            (Nat.gcd_pos_of_pos_right _ (Nat.pos_of_ne_zero hyn))
        exact absurd h0 (Nat.ne_of_gt (Nat.mul_pos hb' hc'))
      zero_sign := fun h => by
        have h0 := congrArg AzNat.toNat h
        rw [AzNat.toNat_mul, AzNat.toNat_div, AzNat.toNat_div, hganN, hgddN,
            AzNat.toNat_zero] at h0
        have ha' : 0 < x.num.toNat / Nat.gcd x.num.toNat y.num.toNat :=
          Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hxn) (Nat.gcd_dvd_left _ _))
            (Nat.gcd_pos_of_pos_left _ (Nat.pos_of_ne_zero hxn))
        have hd' : 0 < y.den.toNat / Nat.gcd x.den.toNat y.den.toNat :=
          Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hyd) (Nat.gcd_dvd_right _ _))
            (Nat.gcd_pos_of_pos_right _ (Nat.pos_of_ne_zero hyd))
        exact absurd h0 (Nat.ne_of_gt (Nat.mul_pos ha' hd'))
      reduced := (AzNat.coprime_iff _ _).mpr (by
        rw [AzNat.toNat_mul, AzNat.toNat_mul, AzNat.toNat_div, AzNat.toNat_div,
            AzNat.toNat_div, AzNat.toNat_div, hganN, hgddN]
        exact coprime_cross_mul ((AzNat.coprime_iff _ _).mp x.reduced)
          (Nat.Coprime.symm ((AzNat.coprime_iff _ _).mp y.reduced)) hxn hxd) }

instance : Div AzRat := ⟨AzRat.div⟩

end Azurite.AzRat

namespace Azurite

-- Sanity checks (string-anchored via `AzRat.parse`/`AzRat.toString`).

#guard ((fun a b => AzRat.toString (a / b)) <$> AzRat.parse "1/2" <*> AzRat.parse "3/4") == some "2/3"
#guard ((fun a b => AzRat.toString (a / b)) <$> AzRat.parse "-2/3" <*> AzRat.parse "-4/9") == some "3/2"
#guard ((fun a b => AzRat.toString (a / b)) <$> AzRat.parse "-2/3" <*> AzRat.parse "4/9") == some "-3/2"
#guard ((fun a b => AzRat.toString (a / b)) <$> AzRat.parse "5/7" <*> AzRat.parse "5/7") == some "1"
#guard ((fun a b => AzRat.toString (a / b)) <$> AzRat.parse "5" <*> AzRat.parse "0") == some "0"
#guard ((fun a b => AzRat.toString (a / b)) <$> AzRat.parse "0" <*> AzRat.parse "5") == some "0"
#guard ((fun a b => AzRat.toString (a / b)) <$> AzRat.parse "6/35" <*> AzRat.parse "9/55") == some "22/21"

end Azurite
