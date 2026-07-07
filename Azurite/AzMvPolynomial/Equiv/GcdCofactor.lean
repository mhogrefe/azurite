import Azurite.AzMvPolynomial.Equiv.IntContentMul

/-!
# Cofactors of the multivariate gcd

Facts needed to discharge the canonicity guard of `AzMvRationalFunction.ofNumDen`.
The computable multivariate `gcd` is *tower*-normalized (iterated-leading-
coefficient positive), which is **not** the same as `ord`-`leadingCoeff`
positive for `Degrevlex`. So `ofNumDen` divides the numerator/denominator
primitive parts by `signNorm (gcd …)` — the sign-normalized gcd, whose
`ord`-leading coefficient is positive — and the resulting cofactors are:

* primitive (`intContent = 1`, via `intContent_exactDiv_eq_one`);
* positive-`ord`-leading (`leadingCoeff_exactDiv_pos`); and
* **coprime** (`coprime_exactDiv_signNorm`), because the cofactors of a gcd in
  a GCD domain are coprime — proven here through the *strong* `ℤ[x⃗]`
  statement `gcd_exactDiv_signNorm_eq_one` (`gcd (a/g) (b/g) = 1`).
-/

namespace Azurite.AzMvPolynomial

variable {n : ℕ} {ord : MonomialOrder}

/-! ### `signNorm` is an associate of its argument -/

/-- `signNorm P` divides `P`. -/
theorem signNorm_dvd (P : AzMvPolynomial n AzInt ord) : signNorm P ∣ P := by
  rw [signNorm]; split
  · exact dvd_refl P
  · exact neg_dvd.mpr (dvd_refl P)

/-- `P` divides `signNorm P`. -/
theorem dvd_signNorm (P : AzMvPolynomial n AzInt ord) : P ∣ signNorm P := by
  rw [signNorm]; split
  · exact dvd_refl P
  · exact dvd_neg.mpr (dvd_refl P)

/-- `signNorm` preserves nonzeroness. -/
theorem signNorm_ne_zero {P : AzMvPolynomial n AzInt ord} (hP : P ≠ 0) :
    signNorm P ≠ 0 := by
  rw [signNorm]; split
  · exact hP
  · exact neg_ne_zero.mpr hP

/-- The leading coefficient of `-P` is `-leadingCoeff P`. -/
theorem leadingCoeff_neg (P : AzMvPolynomial n AzInt ord) :
    leadingCoeff (-P) = -leadingCoeff P := by
  by_cases hP : P = 0
  · rw [hP, neg_zero]; rfl
  · have hnP : -P ≠ 0 := neg_ne_zero.mpr hP
    rw [← leadingCoeff_toMvPoly hnP, ← leadingCoeff_toMvPoly hP,
      show toMvPoly (-P) = -(toMvPoly P) from map_neg toMvPolyHom P,
      MonomialOrder.leadingCoeff_neg]

/-- `signNorm P` has positive leading coefficient for nonzero `P`. -/
theorem leadingCoeff_signNorm_pos {P : AzMvPolynomial n AzInt ord} (hP : P ≠ 0) :
    0 < leadingCoeff (signNorm P) := by
  rw [signNorm]; split
  · assumption
  · rename_i h
    rw [leadingCoeff_neg]
    exact neg_pos.mpr (lt_of_le_of_ne (not_lt.mp h) (leadingCoeff_ne_zero hP))

/-! ### The gcd is nonzero -/

/-- `gcd a b ≠ 0` when `a ≠ 0`. -/
theorem gcd_ne_zero_left {a b : AzMvPolynomial n AzInt ord} (ha : a ≠ 0) :
    AzMvPolynomial.gcd a b ≠ 0 :=
  fun h => ha (zero_dvd_iff.mp (h ▸ gcd_dvd_left a b))

/-! ### The gcd cofactors are coprime -/

/-- **The cofactors of the (sign-normalized) gcd are coprime in `ℤ[x⃗]`**:
`gcd (a / g) (b / g) = 1` where `g = signNorm (gcd a b)`. This is the strong
(content-included) coprimality; it holds because any common divisor `e` of the
cofactors gives `e · g ∣ gcd a b ∣ g`, so `e` is a unit. -/
theorem gcd_exactDiv_signNorm_eq_one {a b : AzMvPolynomial n AzInt ord}
    (ha : a ≠ 0) (_hb : b ≠ 0) :
    AzMvPolynomial.gcd
      (Azurite.ExactDiv.exactDiv a (signNorm (AzMvPolynomial.gcd a b)))
      (Azurite.ExactDiv.exactDiv b (signNorm (AzMvPolynomial.gcd a b))) = 1 := by
  set g := signNorm (AzMvPolynomial.gcd a b) with hgdef
  have hg0 : g ≠ 0 := signNorm_ne_zero (gcd_ne_zero_left ha)
  have hga : g ∣ a := (signNorm_dvd _).trans (gcd_dvd_left a b)
  have hgb : g ∣ b := (signNorm_dvd _).trans (gcd_dvd_right a b)
  have hNa := Azurite.ExactDiv.exactDiv_mul_self a g hga hg0
  have hNb := Azurite.ExactDiv.exactDiv_mul_self b g hgb hg0
  rw [gcd_eq_one_iff]
  intro e heN heD
  have h1 : e * g ∣ a := hNa ▸ mul_dvd_mul_right heN g
  have h2 : e * g ∣ b := hNb ▸ mul_dvd_mul_right heD g
  have hthis : e * g ∣ 1 * g := by
    rw [one_mul]
    exact (dvd_gcd h1 h2).trans (dvd_signNorm _)
  exact isUnit_of_dvd_one ((mul_dvd_mul_iff_right hg0).mp hthis)

/-- **The `ofNumDen` cofactors are coprime** (fraction-field notion) — an
immediate consequence of the strong `gcd = 1` statement. -/
theorem coprime_exactDiv_signNorm {a b : AzMvPolynomial n AzInt ord}
    (ha : a ≠ 0) (hb : b ≠ 0) :
    AzMvPolynomial.coprime
      (Azurite.ExactDiv.exactDiv a (signNorm (AzMvPolynomial.gcd a b)))
      (Azurite.ExactDiv.exactDiv b (signNorm (AzMvPolynomial.gcd a b))) = true := by
  rw [AzMvPolynomial.coprime_iff, gcd_exactDiv_signNorm_eq_one ha hb,
    show (1 : AzMvPolynomial n AzInt ord).toMvPoly = 1 from map_one toMvPolyHom, map_one]
  exact isUnit_one

/-! ### Positive leading coefficient of a cofactor -/

/-- The exact quotient of `a` by a positive-leading divisor `g` (with `a`
positive-leading) again has positive leading coefficient. -/
theorem leadingCoeff_exactDiv_pos {a g : AzMvPolynomial n AzInt ord}
    (hga : g ∣ a) (hg0 : g ≠ 0) (hg_pos : 0 < leadingCoeff g)
    (ha_pos : 0 < leadingCoeff a) :
    0 < leadingCoeff (Azurite.ExactDiv.exactDiv a g) := by
  have hN := Azurite.ExactDiv.exactDiv_mul_self a g hga hg0
  have hN0 : Azurite.ExactDiv.exactDiv a g ≠ 0 := by
    intro h; rw [h, zero_mul] at hN
    rw [← hN, show leadingCoeff (0 : AzMvPolynomial n AzInt ord) = 0 from rfl] at ha_pos
    exact lt_irrefl 0 ha_pos
  have hlc : leadingCoeff a
      = leadingCoeff (Azurite.ExactDiv.exactDiv a g) * leadingCoeff g := by
    conv_lhs => rw [← hN]
    rw [leadingCoeff_mul hN0 hg0]
  rw [hlc] at ha_pos
  exact (pos_iff_pos_of_mul_pos ha_pos).mpr hg_pos

end Azurite.AzMvPolynomial
