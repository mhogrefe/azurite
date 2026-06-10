import Azurite.AzRat.Construct
import Azurite.AzRat.Parse
import Azurite.AzRat.ToString
import Azurite.AzNat.Mul

/-!
# Multiplication for `AzRat`, with cross-gcd reduction

To multiply `a/b` by `c/d`, reduce *across* the two fractions before
multiplying: with `gad = gcd a d` and `gbc = gcd b c`, set `a' = a / gad`,
`d' = d / gad`, `b' = b / gbc`, `c' = c / gbc`; the product is
`(a'·c') / (b'·d')`, already in lowest terms — no gcd computation on the
products is needed. (Within each input fraction the numerator and denominator
are already coprime by the `AzRat` invariant, so the only common factors
between `a·c` and `b·d` can sit across the diagonal pairs `(a, d)` and
`(b, c)`, and those are exactly what the two gcds remove. The proof is
`coprime_cross_mul` below.) The cross-gcds are also computed on the
*smallest* available operands, rather than on the products.

The sign is positive iff the signs agree; a zero operand short-circuits to
the canonical zero.
-/

namespace Azurite.AzRat

/-- The `ℕ`-level core of cross-gcd reduction: if `a ⊥ b` and `c ⊥ d`, then
after dividing the diagonal pairs by their gcds, the product fraction
`(a'·c') / (b'·d')` is in lowest terms. -/
theorem coprime_cross_mul {a b c d : ℕ} (hab : Nat.Coprime a b) (hcd : Nat.Coprime c d)
    (ha : a ≠ 0) (hb : b ≠ 0) :
    Nat.Coprime (a / Nat.gcd a d * (c / Nat.gcd b c))
      (b / Nat.gcd b c * (d / Nat.gcd a d)) := by
  have hgad : 0 < Nat.gcd a d := Nat.gcd_pos_of_pos_left _ (Nat.pos_of_ne_zero ha)
  have hgbc : 0 < Nat.gcd b c := Nat.gcd_pos_of_pos_left _ (Nat.pos_of_ne_zero hb)
  have hA : a / Nat.gcd a d ∣ a := Nat.div_dvd_of_dvd (Nat.gcd_dvd_left _ _)
  have hD : d / Nat.gcd a d ∣ d := Nat.div_dvd_of_dvd (Nat.gcd_dvd_right _ _)
  have hB : b / Nat.gcd b c ∣ b := Nat.div_dvd_of_dvd (Nat.gcd_dvd_left _ _)
  have hC : c / Nat.gcd b c ∣ c := Nat.div_dvd_of_dvd (Nat.gcd_dvd_right _ _)
  have had : Nat.Coprime (a / Nat.gcd a d) (d / Nat.gcd a d) :=
    Nat.coprime_div_gcd_div_gcd hgad
  have hbc : Nat.Coprime (b / Nat.gcd b c) (c / Nat.gcd b c) :=
    Nat.coprime_div_gcd_div_gcd hgbc
  have hab' : Nat.Coprime (a / Nat.gcd a d) (b / Nat.gcd b c) :=
    (hab.coprime_dvd_left hA).coprime_dvd_right hB
  have hcd' : Nat.Coprime (c / Nat.gcd b c) (d / Nat.gcd a d) :=
    (hcd.coprime_dvd_left hC).coprime_dvd_right hD
  exact Nat.Coprime.mul_left (Nat.Coprime.mul_right hab' had)
    (Nat.Coprime.mul_right hbc.symm hcd')

/-- Multiply two `AzRat`s with cross-gcd reduction (see the module
docstring): exactly two `AzNat.gcd` computations, on the cross pairs
`(num x, den y)` and `(den x, num y)`, and no reduction of the products. -/
protected def mul (x y : AzRat) : AzRat :=
  if hx : x.num = 0 then 0
  else if hy : y.num = 0 then 0
  else
    let gad := AzNat.gcd x.num y.den
    let gbc := AzNat.gcd x.den y.num
    have hgadN : gad.toNat = Nat.gcd x.num.toNat y.den.toNat := AzNat.toNat_gcd _ _
    have hgbcN : gbc.toNat = Nat.gcd x.den.toNat y.num.toNat := AzNat.toNat_gcd _ _
    have hxn : x.num.toNat ≠ 0 :=
      fun h => hx (AzNat.toNat_injective (h.trans AzNat.toNat_zero.symm))
    have hyn : y.num.toNat ≠ 0 :=
      fun h => hy (AzNat.toNat_injective (h.trans AzNat.toNat_zero.symm))
    have hxd : x.den.toNat ≠ 0 :=
      fun h => x.den_nz (AzNat.toNat_injective (h.trans AzNat.toNat_zero.symm))
    have hyd : y.den.toNat ≠ 0 :=
      fun h => y.den_nz (AzNat.toNat_injective (h.trans AzNat.toNat_zero.symm))
    { sign := x.sign == y.sign
      num := x.num / gad * (y.num / gbc)
      den := x.den / gbc * (y.den / gad)
      den_nz := fun h => by
        have h0 := congrArg AzNat.toNat h
        rw [AzNat.toNat_mul, AzNat.toNat_div, AzNat.toNat_div, hgadN, hgbcN,
            AzNat.toNat_zero] at h0
        have hb' : 0 < x.den.toNat / Nat.gcd x.den.toNat y.num.toNat :=
          Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hxd) (Nat.gcd_dvd_left _ _))
            (Nat.gcd_pos_of_pos_left _ (Nat.pos_of_ne_zero hxd))
        have hd' : 0 < y.den.toNat / Nat.gcd x.num.toNat y.den.toNat :=
          Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hyd) (Nat.gcd_dvd_right _ _))
            (Nat.gcd_pos_of_pos_right _ (Nat.pos_of_ne_zero hyd))
        exact absurd h0 (Nat.ne_of_gt (Nat.mul_pos hb' hd'))
      zero_sign := fun h => by
        have h0 := congrArg AzNat.toNat h
        rw [AzNat.toNat_mul, AzNat.toNat_div, AzNat.toNat_div, hgadN, hgbcN,
            AzNat.toNat_zero] at h0
        have ha' : 0 < x.num.toNat / Nat.gcd x.num.toNat y.den.toNat :=
          Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hxn) (Nat.gcd_dvd_left _ _))
            (Nat.gcd_pos_of_pos_left _ (Nat.pos_of_ne_zero hxn))
        have hc' : 0 < y.num.toNat / Nat.gcd x.den.toNat y.num.toNat :=
          Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hyn) (Nat.gcd_dvd_right _ _))
            (Nat.gcd_pos_of_pos_right _ (Nat.pos_of_ne_zero hyn))
        exact absurd h0 (Nat.ne_of_gt (Nat.mul_pos ha' hc'))
      reduced := (AzNat.coprime_iff _ _).mpr (by
        rw [AzNat.toNat_mul, AzNat.toNat_mul, AzNat.toNat_div, AzNat.toNat_div,
            AzNat.toNat_div, AzNat.toNat_div, hgadN, hgbcN]
        exact coprime_cross_mul ((AzNat.coprime_iff _ _).mp x.reduced)
          ((AzNat.coprime_iff _ _).mp y.reduced) hxn hxd) }

instance : Mul AzRat := ⟨AzRat.mul⟩

end Azurite.AzRat

namespace Azurite

-- Sanity checks (string-anchored via `AzRat.parse`/`AzRat.toString`).

#guard ((fun a b => AzRat.toString (a * b)) <$> AzRat.parse "2/3" <*> AzRat.parse "9/4") == some "3/2"
#guard ((fun a b => AzRat.toString (a * b)) <$> AzRat.parse "-2/3" <*> AzRat.parse "3/4") == some "-1/2"
#guard ((fun a b => AzRat.toString (a * b)) <$> AzRat.parse "-2/3" <*> AzRat.parse "-3/2") == some "1"
#guard ((fun a b => AzRat.toString (a * b)) <$> AzRat.parse "0" <*> AzRat.parse "5/7") == some "0"
#guard ((fun a b => AzRat.toString (a * b)) <$> AzRat.parse "5/7" <*> AzRat.parse "0") == some "0"
#guard ((fun a b => AzRat.toString (a * b)) <$> AzRat.parse "3" <*> AzRat.parse "4") == some "12"
#guard ((fun a b => AzRat.toString (a * b)) <$> AzRat.parse "6/35" <*> AzRat.parse "55/9") == some "22/21"
#guard ((fun a b => AzRat.toString (a * b)) <$> AzRat.parse "1/3" <*> AzRat.parse "3") == some "1"

end Azurite
