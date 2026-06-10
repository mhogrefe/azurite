import Azurite.AzRat.Mul
import Azurite.AzRat.Equiv.Unary
import Mathlib.Tactic.LinearCombination

/-!
# Correctness of `AzRat` multiplication

`toRat_mul` / `ofRat_mul`: cross-gcd-reduced multiplication computes exactly the
field multiplication of `ℚ`, in both directions. The proof works in `divInt`
normal form: `Rat.divInt_mul_divInt` multiplies the right-hand side, and
`Rat.divInt_eq_divInt_iff` reduces the equality to the cross-multiplication
identity

  `(a/g₁)·(c/g₂)·(b·d) = a·c·(b/g₂)·(d/g₁)`,

which holds in `ℕ` by substituting `a = (a/g₁)·g₁`, `b = (b/g₂)·g₂`, etc.
(`Nat.div_mul_cancel` of the gcd divisibilities) and re-associating. The four
sign cases differ from it by a sign, handled by `linear_combination`.
-/

namespace Azurite.AzRat

/-- Pure-semiring core of the cross-multiplication identity: with each
unprimed value the product of its primed reduction and the shared gcd,
the two product fractions cross-multiply equally. -/
private lemma cross_assoc {A B C D G1 G2 A' B' C' D' : ℕ}
    (hA : A' * G1 = A) (hB : B' * G2 = B) (hC : C' * G2 = C) (hD : D' * G1 = D) :
    A' * C' * (B * D) = A * C * (B' * D') := by
  subst hA hB hC hD; ring

@[simp] theorem toRat_mul (x y : AzRat) : toRat (x * y) = toRat x * toRat y := by
  show toRat (AzRat.mul x y) = toRat x * toRat y
  by_cases hx : x.num = 0
  · rw [AzRat.mul, dif_pos hx, toRat_zero, toRat_of_num_zero x hx, zero_mul]
  by_cases hy : y.num = 0
  · rw [AzRat.mul, dif_neg hx, dif_pos hy, toRat_zero, toRat_of_num_zero y hy, mul_zero]
  rw [AzRat.mul, dif_neg hx, dif_neg hy,
      toRat_eq_divInt, toRat_eq_divInt x, toRat_eq_divInt y, Rat.divInt_mul_divInt]
  dsimp only
  -- Notation: A/B are x's numerator/denominator, C/D are y's, G1 = gcd A D,
  -- G2 = gcd B C (all at the toNat level).
  have hxn : x.num.toNat ≠ 0 :=
    fun h => hx (AzNat.toNat_injective (h.trans AzNat.toNat_zero.symm))
  have hyn : y.num.toNat ≠ 0 :=
    fun h => hy (AzNat.toNat_injective (h.trans AzNat.toNat_zero.symm))
  have hxd : x.den.toNat ≠ 0 :=
    fun h => x.den_nz (AzNat.toNat_injective (h.trans AzNat.toNat_zero.symm))
  have hyd : y.den.toNat ≠ 0 :=
    fun h => y.den_nz (AzNat.toNat_injective (h.trans AzNat.toNat_zero.symm))
  have hcore : x.num.toNat / Nat.gcd x.num.toNat y.den.toNat *
        (y.num.toNat / Nat.gcd x.den.toNat y.num.toNat) * (x.den.toNat * y.den.toNat)
      = x.num.toNat * y.num.toNat *
        (x.den.toNat / Nat.gcd x.den.toNat y.num.toNat *
          (y.den.toNat / Nat.gcd x.num.toNat y.den.toNat)) :=
    cross_assoc (Nat.div_mul_cancel (Nat.gcd_dvd_left _ _))
      (Nat.div_mul_cancel (Nat.gcd_dvd_left _ _))
      (Nat.div_mul_cancel (Nat.gcd_dvd_right _ _))
      (Nat.div_mul_cancel (Nat.gcd_dvd_right _ _))
  have hz : (↑(x.num.toNat / Nat.gcd x.num.toNat y.den.toNat) *
        ↑(y.num.toNat / Nat.gcd x.den.toNat y.num.toNat) *
        ((x.den.toNat : ℤ) * (y.den.toNat : ℤ)) : ℤ)
      = (x.num.toNat : ℤ) * (y.num.toNat : ℤ) *
        (↑(x.den.toNat / Nat.gcd x.den.toNat y.num.toNat) *
          ↑(y.den.toNat / Nat.gcd x.num.toNat y.den.toNat)) := by
    exact_mod_cast hcore
  have hb' : x.den.toNat / Nat.gcd x.den.toNat y.num.toNat ≠ 0 :=
    Nat.ne_of_gt (Nat.div_pos
      (Nat.le_of_dvd (Nat.pos_of_ne_zero hxd) (Nat.gcd_dvd_left _ _))
      (Nat.gcd_pos_of_pos_left _ (Nat.pos_of_ne_zero hxd)))
  have hd' : y.den.toNat / Nat.gcd x.num.toNat y.den.toNat ≠ 0 :=
    Nat.ne_of_gt (Nat.div_pos
      (Nat.le_of_dvd (Nat.pos_of_ne_zero hyd) (Nat.gcd_dvd_right _ _))
      (Nat.gcd_pos_of_pos_right _ (Nat.pos_of_ne_zero hyd)))
  have hz1 : ((x.den / AzNat.gcd x.den y.num * (y.den / AzNat.gcd x.num y.den)).toNat : ℤ) ≠ 0 := by
    rw [AzNat.toNat_mul, AzNat.toNat_div, AzNat.toNat_div, AzNat.toNat_gcd, AzNat.toNat_gcd]
    exact_mod_cast Nat.mul_ne_zero hb' hd'
  have hz2 : ((x.den.toNat : ℤ) * (y.den.toNat : ℤ)) ≠ 0 :=
    mul_ne_zero (Int.natCast_ne_zero.mpr hxd) (Int.natCast_ne_zero.mpr hyd)
  rw [Rat.divInt_eq_divInt_iff hz1 hz2]
  simp only [AzNat.toNat_mul, AzNat.toNat_div, AzNat.toNat_gcd, Nat.cast_mul]
  split_ifs with h1 h2 h3 <;>
    first
      | linear_combination hz
      | linear_combination -hz
      | (rw [beq_iff_eq] at h1; simp_all)

@[simp] theorem ofRat_mul (r s : ℚ) : ofRat (r * s) = ofRat r * ofRat s :=
  toRat_injective (by rw [toRat_ofRat, toRat_mul, toRat_ofRat, toRat_ofRat])

end Azurite.AzRat
