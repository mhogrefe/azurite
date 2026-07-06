import Azurite.AzRationalFunction.Arithmetic
import Azurite.AzRationalFunction.Equiv.Basic
import Azurite.AzRationalFunction.Equiv.Compare
import Azurite.AzRationalFunction.Equiv.Eval
import Azurite.AzRat.Equiv.Mul
import Azurite.AzRat.Equiv.Pow
import Azurite.AzPolynomial.Equiv.Derivative
import Azurite.AzPolynomial.Equiv.Eval
import Azurite.AzPolynomial.Equiv.Mul
import Azurite.AzPolynomial.Equiv.Pow
import Azurite.AzPolynomial.Equiv.SMul
import Azurite.AzPolynomial.Equiv.Sub
import Azurite.AzInt.Equiv.Mul
import Mathlib.FieldTheory.RatFunc.Degree

/-!
# Correctness of the `AzRationalFunction` arithmetic

`toRatFunc` is compatible with all six operations: it maps `-r` to the
negation, `r⁻¹` to the inverse, `r * s` to the product, `r / s` to the
quotient, `r + s` to the sum, and `r - s` to the difference in `ℚ(x)`. In
particular the cross-gcd multiplication's and the Knuth addition's decidable
invariant checks always pass — the fallback `0` branches are unreachable.
-/

namespace Azurite.AzRationalFunction

open Polynomial

/-- **Negation is correct**: `toRatFunc (-r) = -(toRatFunc r)`. -/
theorem toRatFunc_neg (r : AzRationalFunction) :
    toRatFunc (-r) = -(toRatFunc r) := by
  show toRatFunc (neg r) = _
  rw [toRatFunc, toRatFunc]
  show algebraMap ℚ (RatFunc ℚ) (Azurite.AzRat.toRat (-r.factor)) * _ = _
  rw [Azurite.AzRat.toRat_neg, map_neg, neg_mul]
  rfl

/-- **Reciprocal is correct**: `toRatFunc r⁻¹ = (toRatFunc r)⁻¹`
(`0⁻¹ = 0` on both sides). -/
theorem toRatFunc_inv (r : AzRationalFunction) :
    toRatFunc r⁻¹ = (toRatFunc r)⁻¹ := by
  show toRatFunc (inv r) = _
  rw [inv]
  by_cases h : r.factor = 0
  · rw [dif_pos h]
    have hr : toRatFunc r = 0 := by
      rw [toRatFunc, h]
      have h0 : Azurite.AzRat.toRat 0 = 0 := rfl
      rw [h0, map_zero, zero_mul]
    rw [hr, inv_zero, toRatFunc_zero]
  · rw [dif_neg h, toRatFunc, toRatFunc]
    show algebraMap ℚ (RatFunc ℚ) (Azurite.AzRat.toRat r.factor⁻¹)
        * (algebraMap ℚ[X] (RatFunc ℚ) (toPolyQ r.den)
            / algebraMap ℚ[X] (RatFunc ℚ) (toPolyQ r.num)) = _
    rw [Azurite.AzRat.toRat_inv, map_inv₀, mul_inv, inv_div]

/-- `ofRatFunc` version: pulling back a negation. -/
theorem ofRatFunc_neg (f : RatFunc ℚ) : ofRatFunc (-f) = -(ofRatFunc f) :=
  toRatFunc_injective (by
    rw [toRatFunc_ofRatFunc, toRatFunc_neg, toRatFunc_ofRatFunc])

/-- `ofRatFunc` version: pulling back an inverse. -/
theorem ofRatFunc_inv (f : RatFunc ℚ) : ofRatFunc f⁻¹ = (ofRatFunc f)⁻¹ :=
  toRatFunc_injective (by
    rw [toRatFunc_ofRatFunc, toRatFunc_inv, toRatFunc_ofRatFunc])

/-! ### Bridges for multiplication

Private duplicates of the guard-discharge machinery of `Equiv/Basic.lean`
(kept `private` there), plus the product/cofactor bookkeeping lemmas
specific to the cross-gcd multiplication. -/

private theorem hιinj : Function.Injective AzInt.toIntRingHom :=
  fun a b h => Azurite.AzInt.ringEquivInt.injective (by simpa using h)

private theorem hκinj : Function.Injective (Int.castRingHom ℚ) := Int.cast_injective

/-- The fused `ℚ[X]` image factors through the `ℤ[X]` image. -/
private theorem toPolyQ_eq (p : Azurite.AzPolynomial AzInt) :
    toPolyQ p
      = ((AzPolynomial.toPoly p).map AzInt.toIntRingHom).map (Int.castRingHom ℚ) := by
  rw [toPolyQ, Polynomial.map_map]

/-- `toPolyQ` is multiplicative. -/
private theorem toPolyQ_mul (p q : Azurite.AzPolynomial AzInt) :
    toPolyQ (p * q) = toPolyQ p * toPolyQ q := by
  rw [toPolyQ, toPolyQ, toPolyQ, Azurite.AzPolynomial.toPoly_mul, Polynomial.map_mul]

private theorem intPoly_ne_zero {p : Azurite.AzPolynomial AzInt} (hp : p ≠ 0) :
    (AzPolynomial.toPoly p).map AzInt.toIntRingHom ≠ 0 := by
  rw [Ne, Polynomial.map_eq_zero_iff hιinj]
  exact AzPolynomial.toPoly_ne_zero hp

/-- Leading coefficient of the `ℤ[X]` image. -/
private theorem leadingCoeff_intPoly (p : Azurite.AzPolynomial AzInt) :
    ((AzPolynomial.toPoly p).map AzInt.toIntRingHom).leadingCoeff
      = p.leadingCoeff.toInt := by
  rw [Polynomial.leadingCoeff, Polynomial.natDegree_map_eq_of_injective hιinj,
    Polynomial.coeff_map, ← Polynomial.leadingCoeff, leadingCoeff_toPoly]
  rfl

private theorem toInt_zero : (0 : AzInt).toInt = 0 := rfl

private theorem lcPos_int {p : Azurite.AzPolynomial AzInt}
    (h : (0 : AzInt) < p.leadingCoeff) :
    0 < ((AzPolynomial.toPoly p).map AzInt.toIntRingHom).leadingCoeff := by
  rw [leadingCoeff_intPoly]
  rwa [Azurite.AzInt.lt_iff_toInt_lt, toInt_zero] at h

private theorem lcPos_az {p : Azurite.AzPolynomial AzInt}
    (h : 0 < ((AzPolynomial.toPoly p).map AzInt.toIntRingHom).leadingCoeff) :
    (0 : AzInt) < p.leadingCoeff := by
  rw [Azurite.AzInt.lt_iff_toInt_lt, toInt_zero]
  rwa [leadingCoeff_intPoly] at h

/-- A primitive part (in the computable sense) is a primitive `ℤ[X]`
polynomial. -/
private theorem isPrimitive_intPoly {p : Azurite.AzPolynomial AzInt} (h : p.content = 1) :
    ((AzPolynomial.toPoly p).map AzInt.toIntRingHom).IsPrimitive := by
  rw [Polynomial.isPrimitive_iff_content_eq_one, Azurite.AzPolynomial.content_toPoly, h]
  rfl

/-- Nonzero normalized `ℤ[X]` polynomials have positive leading coefficient. -/
private theorem lc_pos_of_normalized {p : ℤ[X]} (hp : p ≠ 0)
    (hnorm : _root_.normalize p = p) : 0 < p.leadingCoeff := by
  have h1 : p.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hp
  have h2 := Polynomial.leadingCoeff_normalize p
  rw [hnorm, ← Int.abs_eq_normalize] at h2
  have h3 : 0 ≤ p.leadingCoeff := h2 ▸ abs_nonneg _
  exact lt_of_le_of_ne h3 (Ne.symm h1)

/-- `gcdNormalizedInt` is symmetric (both sides represent the commutative
normalized `ℤ[X]` gcd). -/
private theorem gcdNormalizedInt_comm (a b : Azurite.AzPolynomial AzInt) :
    Azurite.AzPolynomial.gcdNormalizedInt b a
      = Azurite.AzPolynomial.gcdNormalizedInt a b := by
  rw [← toPoly_inj]
  apply Polynomial.map_injective _ hιinj
  rw [Azurite.AzPolynomial.map_toPoly_gcdNormalizedInt,
    Azurite.AzPolynomial.map_toPoly_gcdNormalizedInt, gcd_comm]

/-- The synthetic quotient by the gcd is an exact cofactor in `ℤ[X]`. -/
private theorem cofactor_mul (a b : Azurite.AzPolynomial AzInt)
    (hg : Azurite.AzPolynomial.gcdNormalizedInt a b ≠ 0) :
    (AzPolynomial.toPoly (Azurite.AzPolynomial.gcdNormalizedInt a b)).map
        AzInt.toIntRingHom
      * (AzPolynomial.toPoly
          (Azurite.AzPolynomial.exactDivQuoRem a
            (Azurite.AzPolynomial.gcdNormalizedInt a b)).1).map AzInt.toIntRingHom
    = (AzPolynomial.toPoly a).map AzInt.toIntRingHom := by
  have hspec := (Azurite.AzPolynomial.gcdGcdFreePart_int_spec a b).2
  have hsnd : (Azurite.AzPolynomial.gcdGcdFreePart a b).2
      = (Azurite.AzPolynomial.exactDivQuoRem a
          (Azurite.AzPolynomial.gcdNormalizedInt a b)).1 := by
    show (if Azurite.AzPolynomial.gcdNormalizedInt a b = 0 then 0
      else (Azurite.AzPolynomial.exactDivQuoRem a
        (Azurite.AzPolynomial.gcdNormalizedInt a b)).1) = _
    rw [if_neg hg]
  rw [hsnd, ← Azurite.AzPolynomial.map_toPoly_gcdNormalizedInt] at hspec
  exact hspec

/-- The `ℚ[X]` image of a nonzero `ℤ[X]` polynomial is associated to that of
its primitive part. -/
private theorem map_assoc_primPart {T : ℤ[X]} (hT : T ≠ 0) :
    Associated (T.map (Int.castRingHom ℚ)) ((T.primPart).map (Int.castRingHom ℚ)) := by
  have hcT : T.content ≠ 0 := by rwa [Ne, Polynomial.content_eq_zero_iff]
  have hu : IsUnit (Polynomial.C ((T.content : ℤ) : ℚ) : ℚ[X]) :=
    Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr (by exact_mod_cast hcT))
  have h1 : T.map (Int.castRingHom ℚ)
      = Polynomial.C ((T.content : ℤ) : ℚ) * (T.primPart).map (Int.castRingHom ℚ) := by
    conv_lhs => rw [T.eq_C_content_mul_primPart]
    rw [Polynomial.map_mul, Polynomial.map_C]
    rfl
  rw [h1]
  exact Associated.symm ⟨hu.unit, by rw [IsUnit.unit_spec, mul_comm]⟩

/-- Every nonzero `ℚ[X]` polynomial is associated to the image of a primitive
`ℤ[X]` polynomial (clear denominators, take the primitive part). -/
private theorem exists_primitive_assoc {E : ℚ[X]} (hE : E ≠ 0) :
    ∃ E' : ℤ[X], E'.IsPrimitive ∧ Associated (E'.map (Int.castRingHom ℚ)) E := by
  obtain ⟨b, hb, hspec⟩ :=
    IsLocalization.integerNormalization_spec (nonZeroDivisors ℤ) E
  set F := IsLocalization.integerNormalization (nonZeroDivisors ℤ) E with hF
  have hF0 : F ≠ 0 := by
    rw [hF, Ne, IsLocalization.integerNormalization_eq_zero_iff le_rfl]
    exact hE
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hmap : F.map (Int.castRingHom ℚ) = Polynomial.C ((b : ℚ)) * E := by
    rw [← algebraMap_int_eq, hspec, zsmul_eq_mul, ← Polynomial.C_eq_intCast]
  refine ⟨F.primPart, F.isPrimitive_primPart, ?_⟩
  have h1 := map_assoc_primPart hF0
  have hCunit : IsUnit (Polynomial.C ((b : ℚ)) : ℚ[X]) :=
    Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr (by exact_mod_cast hb0))
  have h2 : Associated (F.map (Int.castRingHom ℚ)) E := by
    rw [hmap]
    exact Associated.symm ⟨hCunit.unit, by rw [IsUnit.unit_spec, mul_comm]⟩
  exact h1.symm.trans h2

/-- **Coprimality descent**: a unit `ℤ[X]` gcd forces coprimality of the
`ℚ[X]` images (any common `ℚ[X]` divisor has a primitive `ℤ[X]` model, which
divides both integer polynomials and hence the unit gcd). -/
private theorem isCoprime_map_of_gcd_isUnit {A B : ℤ[X]} (hB : B ≠ 0)
    (h : IsUnit (GCDMonoid.gcd A B)) :
    IsCoprime (A.map (Int.castRingHom ℚ)) (B.map (Int.castRingHom ℚ)) := by
  classical
  rw [← EuclideanDomain.gcd_isUnit_iff]
  have hBq : B.map (Int.castRingHom ℚ) ≠ 0 := by
    rw [Ne, Polynomial.map_eq_zero_iff hκinj]
    exact hB
  set E := EuclideanDomain.gcd (A.map (Int.castRingHom ℚ)) (B.map (Int.castRingHom ℚ))
    with hE
  have hE0 : E ≠ 0 := fun h0 => hBq (EuclideanDomain.gcd_eq_zero_iff.mp h0).2
  obtain ⟨E', hprim, hassoc⟩ := exists_primitive_assoc hE0
  have hdvd : ∀ T : ℤ[X], E ∣ T.map (Int.castRingHom ℚ) → E' ∣ T := by
    intro T hdvdT
    by_cases hT : T = 0
    · rw [hT]
      exact dvd_zero _
    · have h1 : E'.map (Int.castRingHom ℚ) ∣ (T.primPart).map (Int.castRingHom ℚ) :=
        (hassoc.dvd.trans hdvdT).trans (map_assoc_primPart hT).dvd
      exact (hprim.dvd_of_fraction_map_dvd_fraction_map (K := ℚ)
        T.isPrimitive_primPart h1).trans T.primPart_dvd
  have hE'unit : IsUnit E' :=
    isUnit_of_dvd_unit
      (dvd_gcd (hdvd A (EuclideanDomain.gcd_dvd_left _ _))
        (hdvd B (EuclideanDomain.gcd_dvd_right _ _))) h
  have h2 : IsUnit (E'.map (Int.castRingHom ℚ)) := by
    have h3 := hE'unit.map (Polynomial.mapRingHom (Int.castRingHom ℚ))
    simpa using h3
  exact hassoc.isUnit h2

/-- Cofactors of primitive parts (by an image-level factor) are primitive. -/
private theorem content_cofactor {g c p : Azurite.AzPolynomial AzInt}
    (hid : (AzPolynomial.toPoly g).map AzInt.toIntRingHom
          * (AzPolynomial.toPoly c).map AzInt.toIntRingHom
        = (AzPolynomial.toPoly p).map AzInt.toIntRingHom)
    (hp : p.content = 1) : c.content = 1 := by
  have h1 := congrArg Polynomial.content hid
  rw [Polynomial.content_mul,
    Polynomial.isPrimitive_iff_content_eq_one.mp (isPrimitive_intPoly hp),
    Azurite.AzPolynomial.content_toPoly, Azurite.AzPolynomial.content_toPoly] at h1
  rcases Int.mul_eq_one_iff_eq_one_or_neg_one.mp h1 with ⟨_, h2⟩ | ⟨_, h2⟩
  · apply Azurite.AzNat.toNat_injective
    have h3 : c.content.toNat = 1 := by exact_mod_cast h2
    rw [h3]
    rfl
  · exfalso
    have h3 : (0 : ℤ) ≤ (c.content.toNat : ℤ) := Int.natCast_nonneg _
    omega

/-- Products of primitive parts are primitive (Gauss), computably. -/
private theorem content_mul_one {a b : Azurite.AzPolynomial AzInt}
    (ha : a.content = 1) (hb : b.content = 1) : (a * b).content = 1 := by
  apply Azurite.AzNat.toNat_injective
  have h1 : (((a * b).content.toNat : ℤ)) = 1 := by
    rw [← Azurite.AzPolynomial.content_toPoly, Azurite.AzPolynomial.toPoly_mul,
      Polynomial.map_mul, Polynomial.content_mul,
      Polynomial.isPrimitive_iff_content_eq_one.mp (isPrimitive_intPoly ha),
      Polynomial.isPrimitive_iff_content_eq_one.mp (isPrimitive_intPoly hb), mul_one]
  have h2 : (a * b).content.toNat = 1 := by exact_mod_cast h1
  rw [h2]
  rfl

/-- Cofactors by a positive-leading-coefficient image factor keep the
positive leading coefficient. -/
private theorem lc_pos_cofactor {g c p : Azurite.AzPolynomial AzInt}
    (hid : (AzPolynomial.toPoly g).map AzInt.toIntRingHom
          * (AzPolynomial.toPoly c).map AzInt.toIntRingHom
        = (AzPolynomial.toPoly p).map AzInt.toIntRingHom)
    (hg : 0 < ((AzPolynomial.toPoly g).map AzInt.toIntRingHom).leadingCoeff)
    (hp : (0 : AzInt) < p.leadingCoeff) : (0 : AzInt) < c.leadingCoeff := by
  apply lcPos_az
  have h1 := congrArg Polynomial.leadingCoeff hid
  rw [Polynomial.leadingCoeff_mul] at h1
  nlinarith [hg, lcPos_int hp, h1]

/-- Positive leading coefficients multiply. -/
private theorem lc_pos_mul {a b : Azurite.AzPolynomial AzInt}
    (ha : (0 : AzInt) < a.leadingCoeff) (hb : (0 : AzInt) < b.leadingCoeff) :
    (0 : AzInt) < (a * b).leadingCoeff := by
  apply lcPos_az
  rw [Azurite.AzPolynomial.toPoly_mul, Polynomial.map_mul, Polynomial.leadingCoeff_mul]
  exact mul_pos (lcPos_int ha) (lcPos_int hb)

/-- Resolve `mul` once the guard conjuncts are known to hold (so the
fallback `0` branch is skipped). -/
private theorem mul_eq_of_guard (r s : AzRationalFunction)
    (hrs : ¬(r.factor = 0 ∨ s.factor = 0))
    (h1 : ((Azurite.AzPolynomial.exactDivQuoRem r.num
          (Azurite.AzPolynomial.gcdNormalizedInt r.num s.den)).1
        * (Azurite.AzPolynomial.exactDivQuoRem s.num
          (Azurite.AzPolynomial.gcdNormalizedInt s.num r.den)).1).content = 1)
    (h2 : ((Azurite.AzPolynomial.exactDivQuoRem r.den
          (Azurite.AzPolynomial.gcdNormalizedInt s.num r.den)).1
        * (Azurite.AzPolynomial.exactDivQuoRem s.den
          (Azurite.AzPolynomial.gcdNormalizedInt r.num s.den)).1).content = 1)
    (h3 : (0 : AzInt) < ((Azurite.AzPolynomial.exactDivQuoRem r.num
          (Azurite.AzPolynomial.gcdNormalizedInt r.num s.den)).1
        * (Azurite.AzPolynomial.exactDivQuoRem s.num
          (Azurite.AzPolynomial.gcdNormalizedInt s.num r.den)).1).leadingCoeff)
    (h4 : (0 : AzInt) < ((Azurite.AzPolynomial.exactDivQuoRem r.den
          (Azurite.AzPolynomial.gcdNormalizedInt s.num r.den)).1
        * (Azurite.AzPolynomial.exactDivQuoRem s.den
          (Azurite.AzPolynomial.gcdNormalizedInt r.num s.den)).1).leadingCoeff)
    (h5 : Azurite.AzPolynomial.coprime
        ((Azurite.AzPolynomial.exactDivQuoRem r.num
            (Azurite.AzPolynomial.gcdNormalizedInt r.num s.den)).1
          * (Azurite.AzPolynomial.exactDivQuoRem s.num
            (Azurite.AzPolynomial.gcdNormalizedInt s.num r.den)).1)
        ((Azurite.AzPolynomial.exactDivQuoRem r.den
            (Azurite.AzPolynomial.gcdNormalizedInt s.num r.den)).1
          * (Azurite.AzPolynomial.exactDivQuoRem s.den
            (Azurite.AzPolynomial.gcdNormalizedInt r.num s.den)).1) = true)
    (h6 : r.factor * s.factor = 0
      → (Azurite.AzPolynomial.exactDivQuoRem r.num
            (Azurite.AzPolynomial.gcdNormalizedInt r.num s.den)).1
          * (Azurite.AzPolynomial.exactDivQuoRem s.num
            (Azurite.AzPolynomial.gcdNormalizedInt s.num r.den)).1 = 1
        ∧ (Azurite.AzPolynomial.exactDivQuoRem r.den
            (Azurite.AzPolynomial.gcdNormalizedInt s.num r.den)).1
          * (Azurite.AzPolynomial.exactDivQuoRem s.den
            (Azurite.AzPolynomial.gcdNormalizedInt r.num s.den)).1 = 1) :
    mul r s = ⟨r.factor * s.factor,
      (Azurite.AzPolynomial.exactDivQuoRem r.num
          (Azurite.AzPolynomial.gcdNormalizedInt r.num s.den)).1
        * (Azurite.AzPolynomial.exactDivQuoRem s.num
          (Azurite.AzPolynomial.gcdNormalizedInt s.num r.den)).1,
      (Azurite.AzPolynomial.exactDivQuoRem r.den
          (Azurite.AzPolynomial.gcdNormalizedInt s.num r.den)).1
        * (Azurite.AzPolynomial.exactDivQuoRem s.den
          (Azurite.AzPolynomial.gcdNormalizedInt r.num s.den)).1,
      h1, h2, h3, h4, h5, h6⟩ := by
  simp only [mul, if_neg hrs]
  rw [dif_pos (⟨h1, h2, h3, h4, h5, h6⟩ : _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _)]

set_option maxHeartbeats 1600000 in
/-- **Multiplication is correct**:
`toRatFunc (r * s) = toRatFunc r * toRatFunc s` — in particular the cross-gcd
constructor's invariant checks always pass (the fallback `0` branch is
unreachable). -/
theorem toRatFunc_mul (r s : AzRationalFunction) :
    toRatFunc (r * s) = toRatFunc r * toRatFunc s := by
  classical
  show toRatFunc (mul r s) = _
  by_cases hr : r.factor = 0
  · have hmz : mul r s = 0 := by rw [mul, if_pos (Or.inl hr)]
    have hr0 : toRatFunc r = 0 := by
      rw [toRatFunc, hr, Azurite.AzRat.toRat_zero, map_zero, zero_mul]
    rw [hmz, toRatFunc_zero, hr0, zero_mul]
  by_cases hs : s.factor = 0
  · have hmz : mul r s = 0 := by rw [mul, if_pos (Or.inr hs)]
    have hs0 : toRatFunc s = 0 := by
      rw [toRatFunc, hs, Azurite.AzRat.toRat_zero, map_zero, zero_mul]
    rw [hmz, toRatFunc_zero, hs0, mul_zero]
  have hnd : ¬(r.factor = 0 ∨ s.factor = 0) := fun h0 => h0.elim hr hs
  -- the scalar factor is nonzero
  have hf0 : r.factor * s.factor ≠ 0 := by
    intro h0
    have h1 := congrArg Azurite.AzRat.toRat h0
    rw [Azurite.AzRat.toRat_mul, Azurite.AzRat.toRat_zero] at h1
    rcases mul_eq_zero.mp h1 with h2 | h2
    · exact hr (Azurite.AzRat.toRat_injective (by rw [h2, Azurite.AzRat.toRat_zero]))
    · exact hs (Azurite.AzRat.toRat_injective (by rw [h2, Azurite.AzRat.toRat_zero]))
  -- the cross gcds and their cofactors
  set g₁ := Azurite.AzPolynomial.gcdNormalizedInt r.num s.den with hg₁
  set g₂ := Azurite.AzPolynomial.gcdNormalizedInt s.num r.den with hg₂
  set N₁ := (Azurite.AzPolynomial.exactDivQuoRem r.num g₁).1 with hN₁
  set N₂ := (Azurite.AzPolynomial.exactDivQuoRem s.num g₂).1 with hN₂
  set D₁ := (Azurite.AzPolynomial.exactDivQuoRem r.den g₂).1 with hD₁
  set D₂ := (Azurite.AzPolynomial.exactDivQuoRem s.den g₁).1 with hD₂
  have hG₁ : (AzPolynomial.toPoly g₁).map AzInt.toIntRingHom
      = GCDMonoid.gcd ((AzPolynomial.toPoly r.num).map AzInt.toIntRingHom)
          ((AzPolynomial.toPoly s.den).map AzInt.toIntRingHom) := by
    rw [hg₁]
    exact Azurite.AzPolynomial.map_toPoly_gcdNormalizedInt r.num s.den
  have hG₂ : (AzPolynomial.toPoly g₂).map AzInt.toIntRingHom
      = GCDMonoid.gcd ((AzPolynomial.toPoly s.num).map AzInt.toIntRingHom)
          ((AzPolynomial.toPoly r.den).map AzInt.toIntRingHom) := by
    rw [hg₂]
    exact Azurite.AzPolynomial.map_toPoly_gcdNormalizedInt s.num r.den
  have hg₁0 : g₁ ≠ 0 := by
    intro h0
    have h1 : GCDMonoid.gcd ((AzPolynomial.toPoly r.num).map AzInt.toIntRingHom)
        ((AzPolynomial.toPoly s.den).map AzInt.toIntRingHom) = 0 := by
      rw [← hG₁, h0, toPoly_zero, Polynomial.map_zero]
    exact intPoly_ne_zero s.den_ne_zero ((gcd_eq_zero_iff _ _).mp h1).2
  have hg₂0 : g₂ ≠ 0 := by
    intro h0
    have h1 : GCDMonoid.gcd ((AzPolynomial.toPoly s.num).map AzInt.toIntRingHom)
        ((AzPolynomial.toPoly r.den).map AzInt.toIntRingHom) = 0 := by
      rw [← hG₂, h0, toPoly_zero, Polynomial.map_zero]
    exact intPoly_ne_zero r.den_ne_zero ((gcd_eq_zero_iff _ _).mp h1).2
  have hg₁Z0 : (AzPolynomial.toPoly g₁).map AzInt.toIntRingHom ≠ 0 :=
    intPoly_ne_zero hg₁0
  have hg₂Z0 : (AzPolynomial.toPoly g₂).map AzInt.toIntRingHom ≠ 0 :=
    intPoly_ne_zero hg₂0
  -- cofactor identifications
  have hN₁id : (AzPolynomial.toPoly g₁).map AzInt.toIntRingHom
        * (AzPolynomial.toPoly N₁).map AzInt.toIntRingHom
      = (AzPolynomial.toPoly r.num).map AzInt.toIntRingHom := by
    rw [hN₁, hg₁]
    exact cofactor_mul r.num s.den (by rw [← hg₁]; exact hg₁0)
  have hN₂id : (AzPolynomial.toPoly g₂).map AzInt.toIntRingHom
        * (AzPolynomial.toPoly N₂).map AzInt.toIntRingHom
      = (AzPolynomial.toPoly s.num).map AzInt.toIntRingHom := by
    rw [hN₂, hg₂]
    exact cofactor_mul s.num r.den (by rw [← hg₂]; exact hg₂0)
  have hcomm₁ : Azurite.AzPolynomial.gcdNormalizedInt s.den r.num = g₁ := by
    rw [hg₁]
    exact gcdNormalizedInt_comm r.num s.den
  have hcomm₂ : Azurite.AzPolynomial.gcdNormalizedInt r.den s.num = g₂ := by
    rw [hg₂]
    exact gcdNormalizedInt_comm s.num r.den
  have hD₂id : (AzPolynomial.toPoly g₁).map AzInt.toIntRingHom
        * (AzPolynomial.toPoly D₂).map AzInt.toIntRingHom
      = (AzPolynomial.toPoly s.den).map AzInt.toIntRingHom := by
    have h1 := cofactor_mul s.den r.num (by rw [hcomm₁]; exact hg₁0)
    rw [hcomm₁] at h1
    rw [hD₂]
    exact h1
  have hD₁id : (AzPolynomial.toPoly g₂).map AzInt.toIntRingHom
        * (AzPolynomial.toPoly D₁).map AzInt.toIntRingHom
      = (AzPolynomial.toPoly r.den).map AzInt.toIntRingHom := by
    have h1 := cofactor_mul r.den s.num (by rw [hcomm₂]; exact hg₂0)
    rw [hcomm₂] at h1
    rw [hD₁]
    exact h1
  -- the cofactors are nonzero
  have hN₁0 : N₁ ≠ 0 := by
    intro h0
    rw [h0, toPoly_zero, Polynomial.map_zero, mul_zero] at hN₁id
    exact intPoly_ne_zero r.num_ne_zero hN₁id.symm
  have hN₂0 : N₂ ≠ 0 := by
    intro h0
    rw [h0, toPoly_zero, Polynomial.map_zero, mul_zero] at hN₂id
    exact intPoly_ne_zero s.num_ne_zero hN₂id.symm
  have hD₁0 : D₁ ≠ 0 := by
    intro h0
    rw [h0, toPoly_zero, Polynomial.map_zero, mul_zero] at hD₁id
    exact intPoly_ne_zero r.den_ne_zero hD₁id.symm
  have hD₂0 : D₂ ≠ 0 := by
    intro h0
    rw [h0, toPoly_zero, Polynomial.map_zero, mul_zero] at hD₂id
    exact intPoly_ne_zero s.den_ne_zero hD₂id.symm
  -- the gcds are normalized: positive leading coefficients
  have hg₁lc : 0 < ((AzPolynomial.toPoly g₁).map AzInt.toIntRingHom).leadingCoeff := by
    apply lc_pos_of_normalized hg₁Z0
    rw [hG₁]
    exact normalize_gcd _ _
  have hg₂lc : 0 < ((AzPolynomial.toPoly g₂).map AzInt.toIntRingHom).leadingCoeff := by
    apply lc_pos_of_normalized hg₂Z0
    rw [hG₂]
    exact normalize_gcd _ _
  -- guard: contents, leading coefficients
  have hncont : (N₁ * N₂).content = 1 :=
    content_mul_one (content_cofactor hN₁id r.num_content)
      (content_cofactor hN₂id s.num_content)
  have hdcont : (D₁ * D₂).content = 1 :=
    content_mul_one (content_cofactor hD₁id r.den_content)
      (content_cofactor hD₂id s.den_content)
  have hnlc : (0 : AzInt) < (N₁ * N₂).leadingCoeff :=
    lc_pos_mul (lc_pos_cofactor hN₁id hg₁lc r.num_lc_pos)
      (lc_pos_cofactor hN₂id hg₂lc s.num_lc_pos)
  have hdlc : (0 : AzInt) < (D₁ * D₂).leadingCoeff :=
    lc_pos_mul (lc_pos_cofactor hD₁id hg₂lc r.den_lc_pos)
      (lc_pos_cofactor hD₂id hg₁lc s.den_lc_pos)
  -- guard: coprimality, via the four cross pairs in `ℚ[X]`
  have hgcd₁ : GCDMonoid.gcd ((AzPolynomial.toPoly N₁).map AzInt.toIntRingHom)
      ((AzPolynomial.toPoly D₂).map AzInt.toIntRingHom) = 1 := by
    have h1 : GCDMonoid.gcd ((AzPolynomial.toPoly r.num).map AzInt.toIntRingHom)
          ((AzPolynomial.toPoly s.den).map AzInt.toIntRingHom)
        = _root_.normalize ((AzPolynomial.toPoly g₁).map AzInt.toIntRingHom)
          * GCDMonoid.gcd ((AzPolynomial.toPoly N₁).map AzInt.toIntRingHom)
              ((AzPolynomial.toPoly D₂).map AzInt.toIntRingHom) := by
      rw [← hN₁id, ← hD₂id]
      exact gcd_mul_left _ _ _
    have h2 : _root_.normalize ((AzPolynomial.toPoly g₁).map AzInt.toIntRingHom)
        = (AzPolynomial.toPoly g₁).map AzInt.toIntRingHom := by
      rw [hG₁]
      exact normalize_gcd _ _
    rw [h2, ← hG₁] at h1
    exact (mul_left_cancel₀ hg₁Z0 (by rw [mul_one]; exact h1)).symm
  have hgcd₂ : GCDMonoid.gcd ((AzPolynomial.toPoly N₂).map AzInt.toIntRingHom)
      ((AzPolynomial.toPoly D₁).map AzInt.toIntRingHom) = 1 := by
    have h1 : GCDMonoid.gcd ((AzPolynomial.toPoly s.num).map AzInt.toIntRingHom)
          ((AzPolynomial.toPoly r.den).map AzInt.toIntRingHom)
        = _root_.normalize ((AzPolynomial.toPoly g₂).map AzInt.toIntRingHom)
          * GCDMonoid.gcd ((AzPolynomial.toPoly N₂).map AzInt.toIntRingHom)
              ((AzPolynomial.toPoly D₁).map AzInt.toIntRingHom) := by
      rw [← hN₂id, ← hD₁id]
      exact gcd_mul_left _ _ _
    have h2 : _root_.normalize ((AzPolynomial.toPoly g₂).map AzInt.toIntRingHom)
        = (AzPolynomial.toPoly g₂).map AzInt.toIntRingHom := by
      rw [hG₂]
      exact normalize_gcd _ _
    rw [h2, ← hG₂] at h1
    exact (mul_left_cancel₀ hg₂Z0 (by rw [mul_one]; exact h1)).symm
  have hc₁₂ : IsCoprime
      (((AzPolynomial.toPoly N₁).map AzInt.toIntRingHom).map (Int.castRingHom ℚ))
      (((AzPolynomial.toPoly D₂).map AzInt.toIntRingHom).map (Int.castRingHom ℚ)) :=
    isCoprime_map_of_gcd_isUnit (intPoly_ne_zero hD₂0)
      (by rw [hgcd₁]; exact isUnit_one)
  have hc₂₁ : IsCoprime
      (((AzPolynomial.toPoly N₂).map AzInt.toIntRingHom).map (Int.castRingHom ℚ))
      (((AzPolynomial.toPoly D₁).map AzInt.toIntRingHom).map (Int.castRingHom ℚ)) :=
    isCoprime_map_of_gcd_isUnit (intPoly_ne_zero hD₁0)
      (by rw [hgcd₂]; exact isUnit_one)
  have hrred : IsCoprime
      (((AzPolynomial.toPoly r.num).map AzInt.toIntRingHom).map (Int.castRingHom ℚ))
      (((AzPolynomial.toPoly r.den).map AzInt.toIntRingHom).map (Int.castRingHom ℚ)) := by
    have h1 := (Azurite.AzPolynomial.coprime_int_iff r.num r.den).mp r.reduced
    rwa [← Polynomial.map_map, ← Polynomial.map_map] at h1
  have hsred : IsCoprime
      (((AzPolynomial.toPoly s.num).map AzInt.toIntRingHom).map (Int.castRingHom ℚ))
      (((AzPolynomial.toPoly s.den).map AzInt.toIntRingHom).map (Int.castRingHom ℚ)) := by
    have h1 := (Azurite.AzPolynomial.coprime_int_iff s.num s.den).mp s.reduced
    rwa [← Polynomial.map_map, ← Polynomial.map_map] at h1
  have hdvdN₁ : ((AzPolynomial.toPoly N₁).map AzInt.toIntRingHom).map (Int.castRingHom ℚ)
      ∣ ((AzPolynomial.toPoly r.num).map AzInt.toIntRingHom).map (Int.castRingHom ℚ) :=
    ⟨((AzPolynomial.toPoly g₁).map AzInt.toIntRingHom).map (Int.castRingHom ℚ), by
      rw [← hN₁id, Polynomial.map_mul, mul_comm]⟩
  have hdvdN₂ : ((AzPolynomial.toPoly N₂).map AzInt.toIntRingHom).map (Int.castRingHom ℚ)
      ∣ ((AzPolynomial.toPoly s.num).map AzInt.toIntRingHom).map (Int.castRingHom ℚ) :=
    ⟨((AzPolynomial.toPoly g₂).map AzInt.toIntRingHom).map (Int.castRingHom ℚ), by
      rw [← hN₂id, Polynomial.map_mul, mul_comm]⟩
  have hdvdD₁ : ((AzPolynomial.toPoly D₁).map AzInt.toIntRingHom).map (Int.castRingHom ℚ)
      ∣ ((AzPolynomial.toPoly r.den).map AzInt.toIntRingHom).map (Int.castRingHom ℚ) :=
    ⟨((AzPolynomial.toPoly g₂).map AzInt.toIntRingHom).map (Int.castRingHom ℚ), by
      rw [← hD₁id, Polynomial.map_mul, mul_comm]⟩
  have hdvdD₂ : ((AzPolynomial.toPoly D₂).map AzInt.toIntRingHom).map (Int.castRingHom ℚ)
      ∣ ((AzPolynomial.toPoly s.den).map AzInt.toIntRingHom).map (Int.castRingHom ℚ) :=
    ⟨((AzPolynomial.toPoly g₁).map AzInt.toIntRingHom).map (Int.castRingHom ℚ), by
      rw [← hD₂id, Polynomial.map_mul, mul_comm]⟩
  have hc₁₁ : IsCoprime
      (((AzPolynomial.toPoly N₁).map AzInt.toIntRingHom).map (Int.castRingHom ℚ))
      (((AzPolynomial.toPoly D₁).map AzInt.toIntRingHom).map (Int.castRingHom ℚ)) :=
    (hrred.of_isCoprime_of_dvd_left hdvdN₁).of_isCoprime_of_dvd_right hdvdD₁
  have hc₂₂ : IsCoprime
      (((AzPolynomial.toPoly N₂).map AzInt.toIntRingHom).map (Int.castRingHom ℚ))
      (((AzPolynomial.toPoly D₂).map AzInt.toIntRingHom).map (Int.castRingHom ℚ)) :=
    (hsred.of_isCoprime_of_dvd_left hdvdN₂).of_isCoprime_of_dvd_right hdvdD₂
  have hcop : Azurite.AzPolynomial.coprime (N₁ * N₂) (D₁ * D₂) = true := by
    rw [Azurite.AzPolynomial.coprime_int_iff]
    simp only [Azurite.AzPolynomial.toPoly_mul, Polynomial.map_mul,
      ← Polynomial.map_map]
    exact IsCoprime.mul_left (hc₁₁.mul_right hc₁₂) (hc₂₁.mul_right hc₂₂)
  -- the represented value
  have hcancel : ∀ (c : ℚ[X]), algebraMap ℚ[X] (RatFunc ℚ) c ≠ 0 → ∀ (u v : ℚ[X]),
      algebraMap ℚ[X] (RatFunc ℚ) (c * u) / algebraMap ℚ[X] (RatFunc ℚ) (c * v)
        = algebraMap ℚ[X] (RatFunc ℚ) u / algebraMap ℚ[X] (RatFunc ℚ) v := by
    intro c hc u v
    rw [map_mul, map_mul, mul_div_mul_left _ _ hc]
  have hφG0 : algebraMap ℚ[X] (RatFunc ℚ)
      (((AzPolynomial.toPoly g₁).map AzInt.toIntRingHom).map (Int.castRingHom ℚ)
        * ((AzPolynomial.toPoly g₂).map AzInt.toIntRingHom).map (Int.castRingHom ℚ))
      ≠ 0 :=
    RatFunc.algebraMap_ne_zero (mul_ne_zero
      (by rw [Ne, Polynomial.map_eq_zero_iff hκinj]; exact hg₁Z0)
      (by rw [Ne, Polynomial.map_eq_zero_iff hκinj]; exact hg₂Z0))
  have hA₁ : toPolyQ r.num
      = ((AzPolynomial.toPoly g₁).map AzInt.toIntRingHom).map (Int.castRingHom ℚ)
        * toPolyQ N₁ := by
    rw [toPolyQ_eq, toPolyQ_eq, ← Polynomial.map_mul, hN₁id]
  have hA₂ : toPolyQ s.num
      = ((AzPolynomial.toPoly g₂).map AzInt.toIntRingHom).map (Int.castRingHom ℚ)
        * toPolyQ N₂ := by
    rw [toPolyQ_eq, toPolyQ_eq, ← Polynomial.map_mul, hN₂id]
  have hB₁ : toPolyQ r.den
      = ((AzPolynomial.toPoly g₂).map AzInt.toIntRingHom).map (Int.castRingHom ℚ)
        * toPolyQ D₁ := by
    rw [toPolyQ_eq, toPolyQ_eq, ← Polynomial.map_mul, hD₁id]
  have hB₂ : toPolyQ s.den
      = ((AzPolynomial.toPoly g₁).map AzInt.toIntRingHom).map (Int.castRingHom ℚ)
        * toPolyQ D₂ := by
    rw [toPolyQ_eq, toPolyQ_eq, ← Polynomial.map_mul, hD₂id]
  have hnQ : toPolyQ r.num * toPolyQ s.num
      = ((AzPolynomial.toPoly g₁).map AzInt.toIntRingHom).map (Int.castRingHom ℚ)
          * ((AzPolynomial.toPoly g₂).map AzInt.toIntRingHom).map (Int.castRingHom ℚ)
        * toPolyQ (N₁ * N₂) := by
    rw [hA₁, hA₂, toPolyQ_mul]
    ring
  have hdQ : toPolyQ r.den * toPolyQ s.den
      = ((AzPolynomial.toPoly g₁).map AzInt.toIntRingHom).map (Int.castRingHom ℚ)
          * ((AzPolynomial.toPoly g₂).map AzInt.toIntRingHom).map (Int.castRingHom ℚ)
        * toPolyQ (D₁ * D₂) := by
    rw [hB₁, hB₂, toPolyQ_mul]
    ring
  have hfrac : algebraMap ℚ[X] (RatFunc ℚ) (toPolyQ r.num)
          / algebraMap ℚ[X] (RatFunc ℚ) (toPolyQ r.den)
        * (algebraMap ℚ[X] (RatFunc ℚ) (toPolyQ s.num)
          / algebraMap ℚ[X] (RatFunc ℚ) (toPolyQ s.den))
      = algebraMap ℚ[X] (RatFunc ℚ) (toPolyQ (N₁ * N₂))
          / algebraMap ℚ[X] (RatFunc ℚ) (toPolyQ (D₁ * D₂)) := by
    rw [div_mul_div_comm, ← map_mul, ← map_mul, hnQ, hdQ, hcancel _ hφG0]
  have hmain : algebraMap ℚ (RatFunc ℚ) (Azurite.AzRat.toRat (r.factor * s.factor))
        * (algebraMap ℚ[X] (RatFunc ℚ) (toPolyQ (N₁ * N₂))
            / algebraMap ℚ[X] (RatFunc ℚ) (toPolyQ (D₁ * D₂)))
      = toRatFunc r * toRatFunc s := by
    rw [toRatFunc, toRatFunc, Azurite.AzRat.toRat_mul, map_mul, ← hfrac]
    ring
  -- discharge the constructor's guard
  rw [mul_eq_of_guard r s hnd hncont hdcont hnlc hdlc hcop
    (fun h0 => absurd h0 hf0)]
  show algebraMap ℚ (RatFunc ℚ) (Azurite.AzRat.toRat (r.factor * s.factor))
      * (algebraMap ℚ[X] (RatFunc ℚ) (toPolyQ (N₁ * N₂))
          / algebraMap ℚ[X] (RatFunc ℚ) (toPolyQ (D₁ * D₂))) = _
  exact hmain

/-- **Division is correct**: `toRatFunc (r / s) = toRatFunc r / toRatFunc s`
(`r / 0 = 0` on both sides). -/
theorem toRatFunc_div (r s : AzRationalFunction) :
    toRatFunc (r / s) = toRatFunc r / toRatFunc s := by
  show toRatFunc (r * s⁻¹) = _
  rw [toRatFunc_mul, toRatFunc_inv, div_eq_mul_inv]

/-- `ofRatFunc` version: pulling back a product. -/
theorem ofRatFunc_mul (f g : RatFunc ℚ) :
    ofRatFunc (f * g) = ofRatFunc f * ofRatFunc g :=
  toRatFunc_injective (by
    rw [toRatFunc_ofRatFunc, toRatFunc_mul, toRatFunc_ofRatFunc, toRatFunc_ofRatFunc])

/-- `ofRatFunc` version: pulling back a quotient. -/
theorem ofRatFunc_div (f g : RatFunc ℚ) :
    ofRatFunc (f / g) = ofRatFunc f / ofRatFunc g :=
  toRatFunc_injective (by
    rw [toRatFunc_ofRatFunc, toRatFunc_div, toRatFunc_ofRatFunc, toRatFunc_ofRatFunc])

/-! ### Bridges for addition

The `add` algorithm decomposes the rational factors into `AzInt` numerator
and denominator components, cross-multiplies into a combined polynomial
numerator, and re-extracts the content. The bridges below name the
components and intermediates (so the branch resolution stays readable) and
duplicate the remaining private `primPos` machinery of `Equiv/Basic.lean`. -/

/-- The signed numerator component of an `AzRat`, as an `AzInt`
(the `a₁`/`a₂` of `add`). -/
private abbrev ratNum (q : Azurite.AzRat) : AzInt := ⟨q.sign, q.num, q.zero_sign⟩

/-- The (positive) denominator component of an `AzRat`, as an `AzInt`
(the `b₁`/`b₂` of `add`). -/
private abbrev ratDen (q : Azurite.AzRat) : AzInt := ⟨true, q.den, fun _ => rfl⟩

private theorem ratNum_def (q : Azurite.AzRat) :
    (⟨q.sign, q.num, q.zero_sign⟩ : AzInt) = ratNum q := rfl

private theorem ratDen_def (q : Azurite.AzRat) :
    (⟨true, q.den, fun _ => rfl⟩ : AzInt) = ratDen q := rfl

private theorem ratDen_toInt (q : Azurite.AzRat) :
    (ratDen q).toInt = (q.den.toNat : ℤ) := rfl

private theorem ratDen_toInt_pos (q : Azurite.AzRat) : 0 < (ratDen q).toInt := by
  rw [ratDen_toInt]
  have h : q.den.toNat ≠ 0 := fun h0 =>
    q.den_nz (Azurite.AzNat.toNat_injective (h0.trans Azurite.AzNat.toNat_zero.symm))
  omega

/-- The represented rational, through the `add` components: `±num / den`. -/
private theorem toRat_factored (q : Azurite.AzRat) :
    Azurite.AzRat.toRat q = ((ratNum q).toInt : ℚ) / ((ratDen q).toInt : ℚ) := by
  have h1 : ((ratNum q).toInt : ℚ) = ((Azurite.AzRat.toRat q).num : ℚ) := rfl
  have h2 : ((ratDen q).toInt : ℚ) = ((Azurite.AzRat.toRat q).den : ℚ) :=
    Int.cast_natCast q.den.toNat
  rw [h1, h2, Rat.num_div_den]

private theorem ratNum_toInt_ne_zero {q : Azurite.AzRat} (hq : q ≠ 0) :
    (ratNum q).toInt ≠ 0 := by
  intro h0
  apply hq
  apply Azurite.AzRat.toRat_injective
  rw [Azurite.AzRat.toRat_zero, toRat_factored, h0, Int.cast_zero, zero_div]

/-! #### `toPolyQ` bookkeeping -/

private theorem toPolyQ_zero : toPolyQ (0 : Azurite.AzPolynomial AzInt) = 0 := by
  rw [toPolyQ, toPoly_zero, Polynomial.map_zero]

private theorem toPolyQ_ne_zero {p : Azurite.AzPolynomial AzInt} (hp : p ≠ 0) :
    toPolyQ p ≠ 0 := by
  rw [toPolyQ_eq, Ne, Polynomial.map_eq_zero_iff hκinj]
  exact intPoly_ne_zero hp

private theorem toPolyQ_add (p q : Azurite.AzPolynomial AzInt) :
    toPolyQ (p + q) = toPolyQ p + toPolyQ q := by
  rw [toPolyQ, toPolyQ, toPolyQ, Azurite.AzPolynomial.toPoly_add, Polynomial.map_add]

private theorem toPolyQ_smul (z : AzInt) (p : Azurite.AzPolynomial AzInt) :
    toPolyQ (z • p) = Polynomial.C ((z.toInt : ℚ)) * toPolyQ p := by
  rw [toPolyQ, toPolyQ, Azurite.AzPolynomial.toPoly_smul, Polynomial.smul_eq_C_mul,
    Polynomial.map_mul, Polynomial.map_C]
  rfl

/-- `coprime_int_iff`, respelled through `toPolyQ` (definitionally the same
maps). -/
private theorem coprime_toPolyQ_iff (P Q : Azurite.AzPolynomial AzInt) :
    Azurite.AzPolynomial.coprime P Q = true ↔ IsCoprime (toPolyQ P) (toPolyQ Q) :=
  Azurite.AzPolynomial.coprime_int_iff P Q

/-- An image-level cofactor identity, at the `ℚ[X]` level. -/
private theorem cofactor_toPolyQ {g c p : Azurite.AzPolynomial AzInt}
    (hid : (AzPolynomial.toPoly g).map AzInt.toIntRingHom
          * (AzPolynomial.toPoly c).map AzInt.toIntRingHom
        = (AzPolynomial.toPoly p).map AzInt.toIntRingHom) :
    toPolyQ g * toPolyQ c = toPolyQ p := by
  rw [toPolyQ_eq, toPolyQ_eq, toPolyQ_eq, ← Polynomial.map_mul, hid]

/-- Ring homs out of `ℚ` are unique, so the ambient `algebraMap ℚ (RatFunc ℚ)`
agrees with `RatFunc.C` whatever `Algebra ℚ (RatFunc ℚ)` instance is in play. -/
private theorem algebraMapQ_eq_C :
    algebraMap ℚ (RatFunc ℚ) = (RatFunc.C : ℚ →+* RatFunc ℚ) :=
  RingHom.ext_rat _ _

/-- Nonzero constants are coprime with everything (left version). -/
private theorem isCoprime_C_left {c : ℚ} (hc : c ≠ 0) (p : ℚ[X]) :
    IsCoprime (Polynomial.C c) p :=
  ⟨Polynomial.C c⁻¹, 0, by
    rw [zero_mul, add_zero, ← Polynomial.C_mul, inv_mul_cancel₀ hc, Polynomial.C_1]⟩

/-! #### The `primPos` specification (duplicate of `Equiv/Basic.lean`'s) -/

private theorem toInt_ne_zero {z : AzInt} (hz : z ≠ 0) : z.toInt ≠ 0 :=
  fun h => hz (Azurite.AzInt.ringEquivInt.injective (by simpa using h))

private theorem toInt_pos_iff_sign {z : AzInt} (hz : z ≠ 0) :
    (0 < z.toInt ↔ z.sign = true) := by
  have h0 := toInt_ne_zero hz
  rw [Azurite.AzInt.toInt] at h0 ⊢
  rcases hs : z.sign with _ | _ <;> rw [hs] at h0 <;> simp at h0 ⊢
  all_goals omega

/-- `AzInt` divisibility along the ring equivalence. -/
private theorem azInt_dvd_of_toInt_dvd {a b : AzInt} (h : a.toInt ∣ b.toInt) :
    a ∣ b := by
  obtain ⟨c, hc⟩ := h
  refine ⟨Azurite.AzInt.ringEquivInt.symm c, Azurite.AzInt.ringEquivInt.injective ?_⟩
  rw [map_mul]
  simpa using hc

private theorem toInt_azNatToAzInt (n : AzNat) :
    (Azurite.AzPolynomial.azNatToAzInt n).toInt = (n.toNat : ℤ) := rfl

private theorem content_map_ne_zero {g : Azurite.AzPolynomial AzInt} (hg : g ≠ 0) :
    ((AzPolynomial.toPoly g).map AzInt.toIntRingHom).content ≠ 0 := by
  rw [Ne, Polynomial.content_eq_zero_iff]
  exact intPoly_ne_zero hg

private theorem computable_content_ne_zero {g : Azurite.AzPolynomial AzInt} (hg : g ≠ 0) :
    (g.content.toNat : ℤ) ≠ 0 := by
  rw [← Azurite.AzPolynomial.content_toPoly]
  exact content_map_ne_zero hg

private theorem lc_ne_zero_az {p : Azurite.AzPolynomial AzInt} (hp : p ≠ 0) :
    p.leadingCoeff ≠ 0 := by
  intro h0
  have h1 := leadingCoeff_intPoly p
  rw [h0, toInt_zero] at h1
  exact Polynomial.leadingCoeff_ne_zero.mpr (intPoly_ne_zero hp) h1

/-- **The `primPos` specification** (duplicate of the private lemma in
`Equiv/Basic.lean`): the signed content times the primitive positive part
recovers the polynomial, and the primitive positive part is exactly that. -/
private theorem primPos_spec {g : Azurite.AzPolynomial AzInt} (hg : g ≠ 0) :
    (if g.leadingCoeff.sign then Azurite.AzPolynomial.azNatToAzInt g.content
        else -Azurite.AzPolynomial.azNatToAzInt g.content).toInt ≠ 0
    ∧ Polynomial.C (if g.leadingCoeff.sign then Azurite.AzPolynomial.azNatToAzInt g.content
          else -Azurite.AzPolynomial.azNatToAzInt g.content).toInt
        * ((AzPolynomial.toPoly (Azurite.AzPolynomial.primPos g)).map AzInt.toIntRingHom)
      = (AzPolynomial.toPoly g).map AzInt.toIntRingHom
    ∧ ((AzPolynomial.toPoly (Azurite.AzPolynomial.primPos g)).map
        AzInt.toIntRingHom).IsPrimitive
    ∧ 0 < ((AzPolynomial.toPoly (Azurite.AzPolynomial.primPos g)).map
        AzInt.toIntRingHom).leadingCoeff := by
  classical
  set s : AzInt := if g.leadingCoeff.sign then Azurite.AzPolynomial.azNatToAzInt g.content
    else -Azurite.AzPolynomial.azNatToAzInt g.content with hs
  set gZ : ℤ[X] := (AzPolynomial.toPoly g).map AzInt.toIntRingHom with hgZ
  have hcont0 : (g.content.toNat : ℤ) ≠ 0 := computable_content_ne_zero hg
  have hsZ : s.toInt = if g.leadingCoeff.sign then (g.content.toNat : ℤ)
      else -(g.content.toNat : ℤ) := by
    rw [hs]
    split <;> simp [toInt_azNatToAzInt]
  have hs0 : s.toInt ≠ 0 := by
    rw [hsZ]
    split <;> omega
  have hsabs : |s.toInt| = (g.content.toNat : ℤ) := by
    rw [hsZ]
    split
    · exact abs_of_nonneg (Int.natCast_nonneg _)
    · rw [abs_neg]
      exact abs_of_nonneg (Int.natCast_nonneg _)
  -- `s` divides every coefficient of `g` (the content does, in `ℤ`)
  have hdvd : ∀ i, s ∣ g.coeff i := by
    intro i
    apply azInt_dvd_of_toInt_dvd
    have h1 : gZ.content ∣ gZ.coeff i := gZ.content_dvd_coeff i
    rw [hgZ, Azurite.AzPolynomial.content_toPoly] at h1
    have h2 : (g.coeff i).toInt
        = ((AzPolynomial.toPoly g).map AzInt.toIntRingHom).coeff i := by
      rw [Polynomial.coeff_map, coeff_toPoly_eq]
      rfl
    rw [h2, hsZ]
    split
    · exact h1
    · exact (neg_dvd).mpr h1
  -- the exact-division identity, mapped to `ℤ[X]`
  have hsne : s ≠ 0 := fun h => hs0 (by rw [h]; rfl)
  have hkey : Polynomial.C s * AzPolynomial.toPoly (Azurite.AzPolynomial.primPos g)
      = AzPolynomial.toPoly g := by
    rw [Azurite.AzPolynomial.primPos]
    exact Azurite.AzPolynomial.C_mul_toPoly_divByRingElt s hsne g hdvd
  have hkeyZ : Polynomial.C s.toInt
      * ((AzPolynomial.toPoly (Azurite.AzPolynomial.primPos g)).map AzInt.toIntRingHom)
      = gZ := by
    have h := congrArg (Polynomial.map (AzInt.toIntRingHom)) hkey
    rw [Polynomial.map_mul, Polynomial.map_C] at h
    exact h
  refine ⟨hs0, hkeyZ, ?_, ?_⟩
  · -- primitivity: `|s| · content(primPos) = content g = |s|`
    have h1 := congrArg Polynomial.content hkeyZ
    rw [Polynomial.content_C_mul, hgZ, Azurite.AzPolynomial.content_toPoly,
      Azurite.AzPolynomial.content_toPoly, ← Int.abs_eq_normalize, hsabs] at h1
    rw [Polynomial.isPrimitive_iff_content_eq_one, Azurite.AzPolynomial.content_toPoly]
    have h3 : (g.content.toNat : ℤ)
        * (((Azurite.AzPolynomial.primPos g).content.toNat : ℤ) - 1) = 0 := by
      rw [mul_sub, h1, mul_one, sub_self]
    rcases mul_eq_zero.mp h3 with h4 | h4
    · exact absurd h4 hcont0
    · omega
  · -- positive leading coefficient, by the sign choice
    have hlcg : g.leadingCoeff ≠ 0 := lc_ne_zero_az hg
    have hlc := congrArg Polynomial.leadingCoeff hkeyZ
    rw [Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C, hgZ,
      leadingCoeff_intPoly, leadingCoeff_intPoly] at hlc
    rw [leadingCoeff_intPoly]
    rcases hsgn : g.leadingCoeff.sign with _ | _
    · -- negative leading coefficient: `s < 0` and `lcof gZ < 0`
      have hneg : g.leadingCoeff.toInt < 0 := by
        have hiff := toInt_pos_iff_sign hlcg
        have h0 := toInt_ne_zero hlcg
        rcases lt_trichotomy g.leadingCoeff.toInt 0 with h | h | h
        · exact h
        · exact absurd h h0
        · rw [hiff.mp h] at hsgn
          exact absurd hsgn (by simp)
      have hsneg : s.toInt < 0 := by
        rw [hsZ, hsgn]
        simp only [Bool.false_eq_true, if_false]
        omega
      by_contra hcon
      push Not at hcon
      nlinarith [hlc, mul_nonneg (neg_nonneg.mpr hsneg.le) (neg_nonneg.mpr hcon)]
    · -- positive leading coefficient: `s > 0` and `lcof gZ > 0`
      have hpos : 0 < g.leadingCoeff.toInt := (toInt_pos_iff_sign hlcg).mpr hsgn
      have hspos : 0 < s.toInt := by
        rw [hsZ, hsgn]
        simp only [if_true]
        omega
      by_contra hcon
      push Not at hcon
      nlinarith [hlc, mul_nonneg hspos.le (neg_nonneg.mpr hcon)]

/-- The `add` scalar in its `primPos`-matching (Boolean-sign) form. -/
private theorem scalar_eq {p : Azurite.AzPolynomial AzInt} (hp : p ≠ 0) :
    (if (0 : AzInt) < p.leadingCoeff then p.content.toAzInt else -p.content.toAzInt)
      = (if p.leadingCoeff.sign then Azurite.AzPolynomial.azNatToAzInt p.content
          else -Azurite.AzPolynomial.azNatToAzInt p.content) := by
  have hiff : ((0 : AzInt) < p.leadingCoeff) ↔ p.leadingCoeff.sign = true := by
    rw [Azurite.AzInt.lt_iff_toInt_lt, toInt_zero]
    exact toInt_pos_iff_sign (lc_ne_zero_az hp)
  by_cases h : (0 : AzInt) < p.leadingCoeff
  · rw [if_pos h, if_pos (hiff.mp h)]
    rfl
  · rw [if_neg h, if_neg (fun hs => h (hiff.mpr hs))]
    rfl

/-- The `primPos` key identity, at the `ℚ[X]` level. -/
private theorem primPos_key_Q {g : Azurite.AzPolynomial AzInt} {a : AzInt}
    (hkey : Polynomial.C a.toInt
          * ((AzPolynomial.toPoly (Azurite.AzPolynomial.primPos g)).map AzInt.toIntRingHom)
        = (AzPolynomial.toPoly g).map AzInt.toIntRingHom) :
    Polynomial.C ((a.toInt : ℚ)) * toPolyQ (Azurite.AzPolynomial.primPos g)
      = toPolyQ g := by
  have h := congrArg (Polynomial.map (Int.castRingHom ℚ)) hkey
  rw [Polynomial.map_mul, Polynomial.map_C, Int.coe_castRingHom] at h
  rw [toPolyQ_eq, toPolyQ_eq]
  exact h

/-- A primitive image gives the computable `content = 1`. -/
private theorem content_az_one {p : Azurite.AzPolynomial AzInt}
    (h : ((AzPolynomial.toPoly p).map AzInt.toIntRingHom).IsPrimitive) :
    p.content = 1 := by
  have h1 := Polynomial.isPrimitive_iff_content_eq_one.mp h
  rw [Azurite.AzPolynomial.content_toPoly] at h1
  apply Azurite.AzNat.toNat_injective
  have h2 : p.content.toNat = 1 := by exact_mod_cast h1
  rw [h2]
  rfl

/-! #### Descent and exact-division variants -/

/-- **Coprimality descent, degree-zero-gcd version**: a constant `ℤ[X]` gcd
forces coprimality of the `ℚ[X]` images (the common primitive model divides
the constant gcd, so it is a primitive integer constant, i.e. a unit). -/
private theorem isCoprime_map_of_gcd_natDegree_eq_zero {A B : ℤ[X]} (hB : B ≠ 0)
    (hdeg : (GCDMonoid.gcd A B).natDegree = 0) :
    IsCoprime (A.map (Int.castRingHom ℚ)) (B.map (Int.castRingHom ℚ)) := by
  classical
  rw [← EuclideanDomain.gcd_isUnit_iff]
  have hBq : B.map (Int.castRingHom ℚ) ≠ 0 := by
    rw [Ne, Polynomial.map_eq_zero_iff hκinj]
    exact hB
  set E := EuclideanDomain.gcd (A.map (Int.castRingHom ℚ)) (B.map (Int.castRingHom ℚ))
    with hE
  have hE0 : E ≠ 0 := fun h0 => hBq (EuclideanDomain.gcd_eq_zero_iff.mp h0).2
  obtain ⟨E', hprim, hassoc⟩ := exists_primitive_assoc hE0
  have hdvd : ∀ T : ℤ[X], E ∣ T.map (Int.castRingHom ℚ) → E' ∣ T := by
    intro T hdvdT
    by_cases hT : T = 0
    · rw [hT]
      exact dvd_zero _
    · have h1 : E'.map (Int.castRingHom ℚ) ∣ (T.primPart).map (Int.castRingHom ℚ) :=
        (hassoc.dvd.trans hdvdT).trans (map_assoc_primPart hT).dvd
      exact (hprim.dvd_of_fraction_map_dvd_fraction_map (K := ℚ)
        T.isPrimitive_primPart h1).trans T.primPart_dvd
  have hgcd0 : GCDMonoid.gcd A B ≠ 0 := fun h0 => hB ((gcd_eq_zero_iff _ _).mp h0).2
  have hdvdgcd : E' ∣ GCDMonoid.gcd A B :=
    dvd_gcd (hdvd A (EuclideanDomain.gcd_dvd_left _ _))
      (hdvd B (EuclideanDomain.gcd_dvd_right _ _))
  have hdegE' : E'.natDegree = 0 :=
    Nat.eq_zero_of_le_zero (hdeg ▸ Polynomial.natDegree_le_of_dvd hdvdgcd hgcd0)
  have hE'C : E' = Polynomial.C (E'.coeff 0) :=
    Polynomial.eq_C_of_natDegree_eq_zero hdegE'
  have hcont : E'.content = 1 := Polynomial.isPrimitive_iff_content_eq_one.mp hprim
  rw [hE'C, Polynomial.content_C] at hcont
  have hE'unit : IsUnit E' := by
    rw [hE'C]
    exact Polynomial.isUnit_C.mpr (normalize_eq_one.mp hcont)
  have h2 : IsUnit (E'.map (Int.castRingHom ℚ)) := by
    have h3 := hE'unit.map (Polynomial.mapRingHom (Int.castRingHom ℚ))
    simpa using h3
  exact hassoc.isUnit h2

/-- Synthetic exact division is correct whenever the `ℤ[X]` images divide
(the divisor need not be a gcd). -/
private theorem toPoly_exactDiv_of_dvd {A B : Azurite.AzPolynomial AzInt} (hB : B ≠ 0)
    (h : (AzPolynomial.toPoly B).map AzInt.toIntRingHom
      ∣ (AzPolynomial.toPoly A).map AzInt.toIntRingHom) :
    (AzPolynomial.toPoly B).map AzInt.toIntRingHom
      * (AzPolynomial.toPoly (Azurite.AzPolynomial.exactDivQuoRem A B).1).map
          AzInt.toIntRingHom
    = (AzPolynomial.toPoly A).map AzInt.toIntRingHom := by
  obtain ⟨q, hq⟩ := h
  have hσι : AzInt.toIntRingHom.comp AzInt.ringEquivInt.symm.toRingHom = RingHom.id ℤ :=
    RingHom.ext fun x => Azurite.AzInt.ringEquivInt.apply_symm_apply x
  have hQι : (q.map AzInt.ringEquivInt.symm.toRingHom).map AzInt.toIntRingHom = q := by
    rw [Polynomial.map_map, hσι, Polynomial.map_id]
  have hdiv : AzPolynomial.toPoly A
      = q.map AzInt.ringEquivInt.symm.toRingHom * AzPolynomial.toPoly B + 0 := by
    rw [add_zero]
    apply Polynomial.map_injective _ hιinj
    rw [Polynomial.map_mul, hQι, hq, mul_comm]
  have hdeg0 : (0 : Polynomial AzInt).degree < (AzPolynomial.toPoly B).degree := by
    rw [Polynomial.degree_zero, bot_lt_iff_ne_bot, Ne, Polynomial.degree_eq_bot]
    exact AzPolynomial.toPoly_ne_zero hB
  have hfst := Azurite.AzPolynomial.toPoly_exactDivQuoRem_fst_of_euclidean A B
    (q.map AzInt.ringEquivInt.symm.toRingHom) 0 (AzPolynomial.toPoly_ne_zero hB)
    hdiv hdeg0
  rw [hfst, hQι, hq]

/-! #### The `add` intermediates, named -/

/-- The fast-path combined numerator of `add` (coprime denominator parts). -/
private abbrev fastT (r s : AzRationalFunction) : Azurite.AzPolynomial AzInt :=
  (ratNum r.factor * ratDen s.factor) • (r.num * s.den)
    + (ratNum s.factor * ratDen r.factor) • (s.num * r.den)

/-- The `D₁/G` cofactor of the Knuth path. -/
private abbrev slowD₁ (r s : AzRationalFunction) : Azurite.AzPolynomial AzInt :=
  (Azurite.AzPolynomial.exactDivQuoRem r.den
    (Azurite.AzPolynomial.gcdNormalizedInt r.den s.den)).1

/-- The `D₂/G` cofactor of the Knuth path. -/
private abbrev slowD₂ (r s : AzRationalFunction) : Azurite.AzPolynomial AzInt :=
  (Azurite.AzPolynomial.exactDivQuoRem s.den
    (Azurite.AzPolynomial.gcdNormalizedInt r.den s.den)).1

/-- The Knuth-path combined numerator before the `H`-reduction. -/
private abbrev slowT₀ (r s : AzRationalFunction) : Azurite.AzPolynomial AzInt :=
  (ratNum r.factor * ratDen s.factor) • (r.num * slowD₂ r s)
    + (ratNum s.factor * ratDen r.factor) • (s.num * slowD₁ r s)

/-- The second small gcd `H = gcd(T₀, G)` of the Knuth path. -/
private abbrev slowH (r s : AzRationalFunction) : Azurite.AzPolynomial AzInt :=
  Azurite.AzPolynomial.gcdNormalizedInt (slowT₀ r s)
    (Azurite.AzPolynomial.gcdNormalizedInt r.den s.den)

/-- The reduced numerator `T₀/H` of the Knuth path. -/
private abbrev slowT (r s : AzRationalFunction) : Azurite.AzPolynomial AzInt :=
  (Azurite.AzPolynomial.exactDivQuoRem (slowT₀ r s) (slowH r s)).1

/-- The `D₂/H` cofactor of the Knuth path. -/
private abbrev slowD₂H (r s : AzRationalFunction) : Azurite.AzPolynomial AzInt :=
  (Azurite.AzPolynomial.exactDivQuoRem s.den (slowH r s)).1

private theorem fastT_def (r s : AzRationalFunction) :
    (ratNum r.factor * ratDen s.factor) • (r.num * s.den)
      + (ratNum s.factor * ratDen r.factor) • (s.num * r.den) = fastT r s := rfl

private theorem slowD₁_def (r s : AzRationalFunction) :
    (Azurite.AzPolynomial.exactDivQuoRem r.den
      (Azurite.AzPolynomial.gcdNormalizedInt r.den s.den)).1 = slowD₁ r s := rfl

private theorem slowD₂_def (r s : AzRationalFunction) :
    (Azurite.AzPolynomial.exactDivQuoRem s.den
      (Azurite.AzPolynomial.gcdNormalizedInt r.den s.den)).1 = slowD₂ r s := rfl

private theorem slowT₀_def (r s : AzRationalFunction) :
    (ratNum r.factor * ratDen s.factor) • (r.num * slowD₂ r s)
      + (ratNum s.factor * ratDen r.factor) • (s.num * slowD₁ r s) = slowT₀ r s := rfl

private theorem slowH_def (r s : AzRationalFunction) :
    Azurite.AzPolynomial.gcdNormalizedInt (slowT₀ r s)
      (Azurite.AzPolynomial.gcdNormalizedInt r.den s.den) = slowH r s := rfl

private theorem slowT_def (r s : AzRationalFunction) :
    (Azurite.AzPolynomial.exactDivQuoRem (slowT₀ r s) (slowH r s)).1 = slowT r s := rfl

private theorem slowD₂H_def (r s : AzRationalFunction) :
    (Azurite.AzPolynomial.exactDivQuoRem s.den (slowH r s)).1 = slowD₂H r s := rfl

/-- The `ℚ[X]` image of the fast-path numerator. -/
private theorem toPolyQ_fastT (r s : AzRationalFunction) :
    toPolyQ (fastT r s)
      = Polynomial.C (((ratNum r.factor).toInt : ℚ) * ((ratDen s.factor).toInt : ℚ))
          * (toPolyQ r.num * toPolyQ s.den)
        + Polynomial.C (((ratNum s.factor).toInt : ℚ) * ((ratDen r.factor).toInt : ℚ))
          * (toPolyQ s.num * toPolyQ r.den) := by
  show toPolyQ ((ratNum r.factor * ratDen s.factor) • (r.num * s.den)
    + (ratNum s.factor * ratDen r.factor) • (s.num * r.den)) = _
  rw [toPolyQ_add, toPolyQ_smul, toPolyQ_smul, toPolyQ_mul, toPolyQ_mul,
    Azurite.AzInt.toInt_mul, Azurite.AzInt.toInt_mul, Int.cast_mul, Int.cast_mul]

/-- The `ℚ[X]` image of the Knuth-path numerator `T₀`. -/
private theorem toPolyQ_slowT₀ (r s : AzRationalFunction) :
    toPolyQ (slowT₀ r s)
      = Polynomial.C (((ratNum r.factor).toInt : ℚ) * ((ratDen s.factor).toInt : ℚ))
          * (toPolyQ r.num * toPolyQ (slowD₂ r s))
        + Polynomial.C (((ratNum s.factor).toInt : ℚ) * ((ratDen r.factor).toInt : ℚ))
          * (toPolyQ s.num * toPolyQ (slowD₁ r s)) := by
  show toPolyQ ((ratNum r.factor * ratDen s.factor) • (r.num * slowD₂ r s)
    + (ratNum s.factor * ratDen r.factor) • (s.num * slowD₁ r s)) = _
  rw [toPolyQ_add, toPolyQ_smul, toPolyQ_smul, toPolyQ_mul, toPolyQ_mul,
    Azurite.AzInt.toInt_mul, Azurite.AzInt.toInt_mul, Int.cast_mul, Int.cast_mul]

/-- **The sum, over a common denominator**: `toRatFunc r + toRatFunc s` as a
single `ℚ(x)` fraction of `ℚ[X]` images. -/
private theorem sum_eq (r s : AzRationalFunction) :
    toRatFunc r + toRatFunc s
      = algebraMap ℚ[X] (RatFunc ℚ)
          (Polynomial.C (((ratNum r.factor).toInt : ℚ) * ((ratDen s.factor).toInt : ℚ))
              * (toPolyQ r.num * toPolyQ s.den)
            + Polynomial.C (((ratNum s.factor).toInt : ℚ)
                * ((ratDen r.factor).toInt : ℚ))
              * (toPolyQ s.num * toPolyQ r.den))
        / algebraMap ℚ[X] (RatFunc ℚ)
          (Polynomial.C (((ratDen r.factor).toInt : ℚ) * ((ratDen s.factor).toInt : ℚ))
            * (toPolyQ r.den * toPolyQ s.den)) := by
  have hβ₁ : ((ratDen r.factor).toInt : ℚ) ≠ 0 :=
    Int.cast_ne_zero.mpr (ratDen_toInt_pos r.factor).ne'
  have hβ₂ : ((ratDen s.factor).toInt : ℚ) ≠ 0 :=
    Int.cast_ne_zero.mpr (ratDen_toInt_pos s.factor).ne'
  have h1 : toRatFunc r
      = algebraMap ℚ[X] (RatFunc ℚ)
          (Polynomial.C (((ratNum r.factor).toInt : ℚ)) * toPolyQ r.num)
        / algebraMap ℚ[X] (RatFunc ℚ)
          (Polynomial.C (((ratDen r.factor).toInt : ℚ)) * toPolyQ r.den) := by
    rw [toRatFunc, toRat_factored, map_div₀, algebraMapQ_eq_C, ← RatFunc.algebraMap_C,
      ← RatFunc.algebraMap_C, div_mul_div_comm, ← map_mul, ← map_mul]
  have h2 : toRatFunc s
      = algebraMap ℚ[X] (RatFunc ℚ)
          (Polynomial.C (((ratNum s.factor).toInt : ℚ)) * toPolyQ s.num)
        / algebraMap ℚ[X] (RatFunc ℚ)
          (Polynomial.C (((ratDen s.factor).toInt : ℚ)) * toPolyQ s.den) := by
    rw [toRatFunc, toRat_factored, map_div₀, algebraMapQ_eq_C, ← RatFunc.algebraMap_C,
      ← RatFunc.algebraMap_C, div_mul_div_comm, ← map_mul, ← map_mul]
  have hφ1 : algebraMap ℚ[X] (RatFunc ℚ)
      (Polynomial.C (((ratDen r.factor).toInt : ℚ)) * toPolyQ r.den) ≠ 0 :=
    RatFunc.algebraMap_ne_zero
      (mul_ne_zero (Polynomial.C_ne_zero.mpr hβ₁) (toPolyQ_den_ne_zero r))
  have hφ2 : algebraMap ℚ[X] (RatFunc ℚ)
      (Polynomial.C (((ratDen s.factor).toInt : ℚ)) * toPolyQ s.den) ≠ 0 :=
    RatFunc.algebraMap_ne_zero
      (mul_ne_zero (Polynomial.C_ne_zero.mpr hβ₂) (toPolyQ_den_ne_zero s))
  rw [h1, h2, div_add_div _ _ hφ1 hφ2, ← map_mul, ← map_mul, ← map_mul, ← map_add]
  have hnum : Polynomial.C (((ratNum r.factor).toInt : ℚ)) * toPolyQ r.num
        * (Polynomial.C (((ratDen s.factor).toInt : ℚ)) * toPolyQ s.den)
      + Polynomial.C (((ratDen r.factor).toInt : ℚ)) * toPolyQ r.den
        * (Polynomial.C (((ratNum s.factor).toInt : ℚ)) * toPolyQ s.num)
      = Polynomial.C (((ratNum r.factor).toInt : ℚ) * ((ratDen s.factor).toInt : ℚ))
          * (toPolyQ r.num * toPolyQ s.den)
        + Polynomial.C (((ratNum s.factor).toInt : ℚ) * ((ratDen r.factor).toInt : ℚ))
          * (toPolyQ s.num * toPolyQ r.den) := by
    rw [Polynomial.C_mul, Polynomial.C_mul]
    ring
  have hden : Polynomial.C (((ratDen r.factor).toInt : ℚ)) * toPolyQ r.den
        * (Polynomial.C (((ratDen s.factor).toInt : ℚ)) * toPolyQ s.den)
      = Polynomial.C (((ratDen r.factor).toInt : ℚ) * ((ratDen s.factor).toInt : ℚ))
          * (toPolyQ r.den * toPolyQ s.den) := by
    rw [Polynomial.C_mul]
    ring
  rw [hnum, hden]

set_option maxHeartbeats 1600000 in
/-- **Addition is correct**: `toRatFunc (r + s) = toRatFunc r + toRatFunc s`
— in particular the Knuth constructor's invariant checks always pass (the
fallback `0` branch is unreachable). -/
theorem toRatFunc_add (r s : AzRationalFunction) :
    toRatFunc (r + s) = toRatFunc r + toRatFunc s := by
  classical
  show toRatFunc (add r s) = _
  by_cases hr : r.factor = 0
  · have h0 : add r s = s := by rw [add, if_pos hr]
    have hr0 : toRatFunc r = 0 := by
      rw [toRatFunc, hr, Azurite.AzRat.toRat_zero, map_zero, zero_mul]
    rw [h0, hr0, zero_add]
  by_cases hs : s.factor = 0
  · have h0 : add r s = r := by rw [add, if_neg hr, if_pos hs]
    have hs0 : toRatFunc s = 0 := by
      rw [toRatFunc, hs, Azurite.AzRat.toRat_zero, map_zero, zero_mul]
    rw [h0, hs0, add_zero]
  -- shared scalar and coprimality facts
  have hα₁ : ((ratNum r.factor).toInt : ℚ) ≠ 0 :=
    Int.cast_ne_zero.mpr (ratNum_toInt_ne_zero hr)
  have hα₂ : ((ratNum s.factor).toInt : ℚ) ≠ 0 :=
    Int.cast_ne_zero.mpr (ratNum_toInt_ne_zero hs)
  have hβ₁ : ((ratDen r.factor).toInt : ℚ) ≠ 0 :=
    Int.cast_ne_zero.mpr (ratDen_toInt_pos r.factor).ne'
  have hβ₂ : ((ratDen s.factor).toInt : ℚ) ≠ 0 :=
    Int.cast_ne_zero.mpr (ratDen_toInt_pos s.factor).ne'
  have hc₁ : ((ratNum r.factor).toInt : ℚ) * ((ratDen s.factor).toInt : ℚ) ≠ 0 :=
    mul_ne_zero hα₁ hβ₂
  have hc₂ : ((ratNum s.factor).toInt : ℚ) * ((ratDen r.factor).toInt : ℚ) ≠ 0 :=
    mul_ne_zero hα₂ hβ₁
  have hbb0 : (ratDen r.factor * ratDen s.factor).toInt ≠ 0 := by
    rw [Azurite.AzInt.toInt_mul]
    exact mul_ne_zero (ratDen_toInt_pos r.factor).ne' (ratDen_toInt_pos s.factor).ne'
  have hND₁ : IsCoprime (toPolyQ r.num) (toPolyQ r.den) :=
    (coprime_toPolyQ_iff r.num r.den).mp r.reduced
  have hND₂ : IsCoprime (toPolyQ s.num) (toPolyQ s.den) :=
    (coprime_toPolyQ_iff s.num s.den).mp s.reduced
  have hφR : algebraMap ℚ[X] (RatFunc ℚ)
      (Polynomial.C (((ratDen r.factor).toInt : ℚ) * ((ratDen s.factor).toInt : ℚ))
        * (toPolyQ r.den * toPolyQ s.den)) ≠ 0 :=
    RatFunc.algebraMap_ne_zero (mul_ne_zero
      (Polynomial.C_ne_zero.mpr (mul_ne_zero hβ₁ hβ₂))
      (mul_ne_zero (toPolyQ_den_ne_zero r) (toPolyQ_den_ne_zero s)))
  by_cases hdeg : (Azurite.AzPolynomial.gcdNormalizedInt r.den s.den).natDegree = 0
  · -- ═══ fast path: coprime denominator parts ═══
    have hGdeg : (GCDMonoid.gcd ((AzPolynomial.toPoly r.den).map AzInt.toIntRingHom)
        ((AzPolynomial.toPoly s.den).map AzInt.toIntRingHom)).natDegree = 0 := by
      rw [← Azurite.AzPolynomial.map_toPoly_gcdNormalizedInt,
        Polynomial.natDegree_map_eq_of_injective hιinj, AzPolynomial.natDegree_toPoly]
      exact hdeg
    have hDD : IsCoprime (toPolyQ r.den) (toPolyQ s.den) := by
      rw [toPolyQ_eq, toPolyQ_eq]
      exact isCoprime_map_of_gcd_natDegree_eq_zero (intPoly_ne_zero s.den_ne_zero) hGdeg
    by_cases hT : fastT r s = 0
    · -- the combination vanishes: both sides are `0`
      have hres : add r s = 0 := by
        simp only [add, if_neg hr, if_neg hs, ratNum_def, ratDen_def, fastT_def,
          if_pos hdeg]
        rw [if_pos hT]
      rw [hres, toRatFunc_zero, sum_eq r s, ← toPolyQ_fastT r s, hT, toPolyQ_zero,
        map_zero, zero_div]
    · -- guard discharge and value
      obtain ⟨haT0, haTkey, hpTprim, hpTlc⟩ := primPos_spec hT
      rw [← scalar_eq hT] at haT0 haTkey
      have hTD₁ : IsCoprime (toPolyQ (fastT r s)) (toPolyQ r.den) := by
        have hbase : IsCoprime
            (Polynomial.C (((ratNum r.factor).toInt : ℚ) * ((ratDen s.factor).toInt : ℚ))
              * (toPolyQ r.num * toPolyQ s.den)) (toPolyQ r.den) :=
          (isCoprime_C_left hc₁ _).mul_left (hND₁.mul_left hDD.symm)
        have h1 := hbase.add_mul_right_left
          (Polynomial.C (((ratNum s.factor).toInt : ℚ) * ((ratDen r.factor).toInt : ℚ))
            * toPolyQ s.num)
        have hshape : toPolyQ (fastT r s)
            = Polynomial.C (((ratNum r.factor).toInt : ℚ)
                  * ((ratDen s.factor).toInt : ℚ))
                * (toPolyQ r.num * toPolyQ s.den)
              + (Polynomial.C (((ratNum s.factor).toInt : ℚ)
                  * ((ratDen r.factor).toInt : ℚ)) * toPolyQ s.num) * toPolyQ r.den := by
          rw [toPolyQ_fastT]
          ring
        rw [← hshape] at h1
        exact h1
      have hTD₂ : IsCoprime (toPolyQ (fastT r s)) (toPolyQ s.den) := by
        have hbase : IsCoprime
            (Polynomial.C (((ratNum s.factor).toInt : ℚ) * ((ratDen r.factor).toInt : ℚ))
              * (toPolyQ s.num * toPolyQ r.den)) (toPolyQ s.den) :=
          (isCoprime_C_left hc₂ _).mul_left (hND₂.mul_left hDD)
        have h1 := hbase.add_mul_right_left
          (Polynomial.C (((ratNum r.factor).toInt : ℚ) * ((ratDen s.factor).toInt : ℚ))
            * toPolyQ r.num)
        have hshape : toPolyQ (fastT r s)
            = Polynomial.C (((ratNum s.factor).toInt : ℚ)
                  * ((ratDen r.factor).toInt : ℚ))
                * (toPolyQ s.num * toPolyQ r.den)
              + (Polynomial.C (((ratNum r.factor).toInt : ℚ)
                  * ((ratDen s.factor).toInt : ℚ)) * toPolyQ r.num) * toPolyQ s.den := by
          rw [toPolyQ_fastT]
          ring
        rw [← hshape] at h1
        exact h1
      have hpTdvd : toPolyQ (Azurite.AzPolynomial.primPos (fastT r s))
          ∣ toPolyQ (fastT r s) :=
        ⟨Polynomial.C (((if (0 : AzInt) < (fastT r s).leadingCoeff
            then (fastT r s).content.toAzInt
            else -(fastT r s).content.toAzInt).toInt : ℚ)), by
          rw [← primPos_key_Q haTkey]
          ring⟩
      have hcop : Azurite.AzPolynomial.coprime
          (Azurite.AzPolynomial.primPos (fastT r s)) (r.den * s.den) = true := by
        rw [coprime_toPolyQ_iff, toPolyQ_mul]
        exact (hTD₁.mul_right hTD₂).of_isCoprime_of_dvd_left hpTdvd
      have h1g : (Azurite.AzPolynomial.primPos (fastT r s)).content = 1 :=
        content_az_one hpTprim
      have h2g : (r.den * s.den).content = 1 :=
        content_mul_one r.den_content s.den_content
      have h3g : (0 : AzInt) < (Azurite.AzPolynomial.primPos (fastT r s)).leadingCoeff :=
        lcPos_az hpTlc
      have h4g : (0 : AzInt) < (r.den * s.den).leadingCoeff :=
        lc_pos_mul r.den_lc_pos s.den_lc_pos
      have h6g : AzRat.ofAzInts
          (if (0 : AzInt) < (fastT r s).leadingCoeff then (fastT r s).content.toAzInt
            else -(fastT r s).content.toAzInt)
          (ratDen r.factor * ratDen s.factor) = 0
          → Azurite.AzPolynomial.primPos (fastT r s) = 1 ∧ r.den * s.den = 1 := by
        intro h0
        exfalso
        have h1 := congrArg Azurite.AzRat.toRat h0
        rw [Azurite.AzRat.toRat_ofAzInts, Azurite.AzRat.toRat_zero] at h1
        rcases div_eq_zero_iff.mp h1 with h2 | h2
        · exact haT0 (by exact_mod_cast h2)
        · exact hbb0 (by exact_mod_cast h2)
      have hres : add r s = ⟨AzRat.ofAzInts
          (if (0 : AzInt) < (fastT r s).leadingCoeff then (fastT r s).content.toAzInt
            else -(fastT r s).content.toAzInt)
          (ratDen r.factor * ratDen s.factor),
          Azurite.AzPolynomial.primPos (fastT r s), r.den * s.den,
          h1g, h2g, h3g, h4g, hcop, h6g⟩ := by
        simp only [add, if_neg hr, if_neg hs, ratNum_def, ratDen_def, fastT_def,
          if_pos hdeg]
        rw [if_neg hT, dif_pos (⟨h1g, h2g, h3g, h4g, hcop, h6g⟩
          : _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _)]
      have hφL : algebraMap ℚ[X] (RatFunc ℚ)
          (Polynomial.C (((ratDen r.factor * ratDen s.factor).toInt : ℚ))
            * toPolyQ (r.den * s.den)) ≠ 0 :=
        RatFunc.algebraMap_ne_zero (mul_ne_zero
          (Polynomial.C_ne_zero.mpr (Int.cast_ne_zero.mpr hbb0))
          (by rw [toPolyQ_mul]
              exact mul_ne_zero (toPolyQ_den_ne_zero r) (toPolyQ_den_ne_zero s)))
      have hpoly : Polynomial.C (((if (0 : AzInt) < (fastT r s).leadingCoeff
            then (fastT r s).content.toAzInt
            else -(fastT r s).content.toAzInt).toInt : ℚ))
            * toPolyQ (Azurite.AzPolynomial.primPos (fastT r s))
            * (Polynomial.C (((ratDen r.factor).toInt : ℚ)
                * ((ratDen s.factor).toInt : ℚ))
              * (toPolyQ r.den * toPolyQ s.den))
          = (Polynomial.C (((ratNum r.factor).toInt : ℚ)
                * ((ratDen s.factor).toInt : ℚ))
              * (toPolyQ r.num * toPolyQ s.den)
            + Polynomial.C (((ratNum s.factor).toInt : ℚ)
                * ((ratDen r.factor).toInt : ℚ))
              * (toPolyQ s.num * toPolyQ r.den))
            * (Polynomial.C (((ratDen r.factor * ratDen s.factor).toInt : ℚ))
              * toPolyQ (r.den * s.den)) := by
        rw [primPos_key_Q haTkey, ← toPolyQ_fastT, toPolyQ_mul,
          Azurite.AzInt.toInt_mul, Int.cast_mul]
      rw [hres]
      show algebraMap ℚ (RatFunc ℚ) (Azurite.AzRat.toRat (AzRat.ofAzInts
          (if (0 : AzInt) < (fastT r s).leadingCoeff then (fastT r s).content.toAzInt
            else -(fastT r s).content.toAzInt)
          (ratDen r.factor * ratDen s.factor)))
          * (algebraMap ℚ[X] (RatFunc ℚ)
              (toPolyQ (Azurite.AzPolynomial.primPos (fastT r s)))
            / algebraMap ℚ[X] (RatFunc ℚ) (toPolyQ (r.den * s.den))) = _
      rw [Azurite.AzRat.toRat_ofAzInts, sum_eq r s, map_div₀, algebraMapQ_eq_C,
        ← RatFunc.algebraMap_C, ← RatFunc.algebraMap_C, div_mul_div_comm,
        ← map_mul, ← map_mul, div_eq_div_iff hφL hφR, ← map_mul, ← map_mul]
      exact congrArg _ hpoly
  · -- ═══ Knuth path: reduce by `G = gcd(D₁, D₂)`, then `H = gcd(T₀, G)` ═══
    have hG : (AzPolynomial.toPoly
          (Azurite.AzPolynomial.gcdNormalizedInt r.den s.den)).map AzInt.toIntRingHom
        = GCDMonoid.gcd ((AzPolynomial.toPoly r.den).map AzInt.toIntRingHom)
            ((AzPolynomial.toPoly s.den).map AzInt.toIntRingHom) :=
      Azurite.AzPolynomial.map_toPoly_gcdNormalizedInt r.den s.den
    have hG0 : Azurite.AzPolynomial.gcdNormalizedInt r.den s.den ≠ 0 := by
      intro h0
      have h1 : GCDMonoid.gcd ((AzPolynomial.toPoly r.den).map AzInt.toIntRingHom)
          ((AzPolynomial.toPoly s.den).map AzInt.toIntRingHom) = 0 := by
        rw [← hG, h0, toPoly_zero, Polynomial.map_zero]
      exact intPoly_ne_zero s.den_ne_zero ((gcd_eq_zero_iff _ _).mp h1).2
    have hGι0 : (AzPolynomial.toPoly
          (Azurite.AzPolynomial.gcdNormalizedInt r.den s.den)).map AzInt.toIntRingHom
        ≠ 0 := intPoly_ne_zero hG0
    have hD₁id : (AzPolynomial.toPoly
          (Azurite.AzPolynomial.gcdNormalizedInt r.den s.den)).map AzInt.toIntRingHom
          * (AzPolynomial.toPoly (slowD₁ r s)).map AzInt.toIntRingHom
        = (AzPolynomial.toPoly r.den).map AzInt.toIntRingHom :=
      cofactor_mul r.den s.den hG0
    have hcomm : Azurite.AzPolynomial.gcdNormalizedInt s.den r.den
        = Azurite.AzPolynomial.gcdNormalizedInt r.den s.den :=
      gcdNormalizedInt_comm r.den s.den
    have hD₂id : (AzPolynomial.toPoly
          (Azurite.AzPolynomial.gcdNormalizedInt r.den s.den)).map AzInt.toIntRingHom
          * (AzPolynomial.toPoly (slowD₂ r s)).map AzInt.toIntRingHom
        = (AzPolynomial.toPoly s.den).map AzInt.toIntRingHom := by
      have h1 := cofactor_mul s.den r.den (by rw [hcomm]; exact hG0)
      rw [hcomm] at h1
      exact h1
    have hD₁0 : slowD₁ r s ≠ 0 := by
      intro h0
      rw [h0, toPoly_zero, Polynomial.map_zero, mul_zero] at hD₁id
      exact intPoly_ne_zero r.den_ne_zero hD₁id.symm
    have hD₂0 : slowD₂ r s ≠ 0 := by
      intro h0
      rw [h0, toPoly_zero, Polynomial.map_zero, mul_zero] at hD₂id
      exact intPoly_ne_zero s.den_ne_zero hD₂id.symm
    have hGlc : 0 < ((AzPolynomial.toPoly
        (Azurite.AzPolynomial.gcdNormalizedInt r.den s.den)).map
          AzInt.toIntRingHom).leadingCoeff := by
      apply lc_pos_of_normalized hGι0
      rw [hG]
      exact normalize_gcd _ _
    have hD₁fac : toPolyQ (Azurite.AzPolynomial.gcdNormalizedInt r.den s.den)
        * toPolyQ (slowD₁ r s) = toPolyQ r.den := cofactor_toPolyQ hD₁id
    have hD₂fac : toPolyQ (Azurite.AzPolynomial.gcdNormalizedInt r.den s.den)
        * toPolyQ (slowD₂ r s) = toPolyQ s.den := cofactor_toPolyQ hD₂id
    have hPfac : Polynomial.C (((ratNum r.factor).toInt : ℚ)
            * ((ratDen s.factor).toInt : ℚ))
          * (toPolyQ r.num * toPolyQ s.den)
        + Polynomial.C (((ratNum s.factor).toInt : ℚ) * ((ratDen r.factor).toInt : ℚ))
          * (toPolyQ s.num * toPolyQ r.den)
        = toPolyQ (Azurite.AzPolynomial.gcdNormalizedInt r.den s.den)
          * toPolyQ (slowT₀ r s) := by
      rw [← hD₁fac, ← hD₂fac, toPolyQ_slowT₀]
      ring
    by_cases hT₀ : slowT₀ r s = 0
    · -- the combination vanishes: both sides are `0`
      have hres : add r s = 0 := by
        simp only [add, if_neg hr, if_neg hs, ratNum_def, ratDen_def, slowD₁_def,
          slowD₂_def, slowT₀_def, if_neg hdeg, if_pos hT₀]
        rw [if_pos trivial]
      rw [hres, toRatFunc_zero, sum_eq r s, hPfac, hT₀, toPolyQ_zero, mul_zero,
        map_zero, zero_div]
    · -- guard discharge and value
      have hT₀ι0 : (AzPolynomial.toPoly (slowT₀ r s)).map AzInt.toIntRingHom ≠ 0 :=
        intPoly_ne_zero hT₀
      have hH : (AzPolynomial.toPoly (slowH r s)).map AzInt.toIntRingHom
          = GCDMonoid.gcd ((AzPolynomial.toPoly (slowT₀ r s)).map AzInt.toIntRingHom)
              ((AzPolynomial.toPoly
                (Azurite.AzPolynomial.gcdNormalizedInt r.den s.den)).map
                  AzInt.toIntRingHom) :=
        Azurite.AzPolynomial.map_toPoly_gcdNormalizedInt (slowT₀ r s)
          (Azurite.AzPolynomial.gcdNormalizedInt r.den s.den)
      have hH0 : slowH r s ≠ 0 := by
        intro h0
        have h1 : GCDMonoid.gcd
            ((AzPolynomial.toPoly (slowT₀ r s)).map AzInt.toIntRingHom)
            ((AzPolynomial.toPoly
              (Azurite.AzPolynomial.gcdNormalizedInt r.den s.den)).map
                AzInt.toIntRingHom) = 0 := by
          rw [← hH, h0, toPoly_zero, Polynomial.map_zero]
        exact hT₀ι0 ((gcd_eq_zero_iff _ _).mp h1).1
      have hHι0 : (AzPolynomial.toPoly (slowH r s)).map AzInt.toIntRingHom ≠ 0 :=
        intPoly_ne_zero hH0
      have hHlc : 0 < ((AzPolynomial.toPoly (slowH r s)).map
          AzInt.toIntRingHom).leadingCoeff := by
        apply lc_pos_of_normalized hHι0
        rw [hH]
        exact normalize_gcd _ _
      have hTid : (AzPolynomial.toPoly (slowH r s)).map AzInt.toIntRingHom
            * (AzPolynomial.toPoly (slowT r s)).map AzInt.toIntRingHom
          = (AzPolynomial.toPoly (slowT₀ r s)).map AzInt.toIntRingHom :=
        cofactor_mul (slowT₀ r s) (Azurite.AzPolynomial.gcdNormalizedInt r.den s.den)
          hH0
      have hT'0 : slowT r s ≠ 0 := by
        intro h0
        rw [h0, toPoly_zero, Polynomial.map_zero, mul_zero] at hTid
        exact hT₀ι0 hTid.symm
      have hHdvdG : (AzPolynomial.toPoly (slowH r s)).map AzInt.toIntRingHom
          ∣ (AzPolynomial.toPoly
              (Azurite.AzPolynomial.gcdNormalizedInt r.den s.den)).map
                AzInt.toIntRingHom := by
        rw [hH]
        exact gcd_dvd_right _ _
      have hD₂Hid : (AzPolynomial.toPoly (slowH r s)).map AzInt.toIntRingHom
            * (AzPolynomial.toPoly (slowD₂H r s)).map AzInt.toIntRingHom
          = (AzPolynomial.toPoly s.den).map AzInt.toIntRingHom :=
        toPoly_exactDiv_of_dvd hH0 (hHdvdG.trans
          ⟨(AzPolynomial.toPoly (slowD₂ r s)).map AzInt.toIntRingHom, hD₂id.symm⟩)
      have hD₂H0 : slowD₂H r s ≠ 0 := by
        intro h0
        rw [h0, toPoly_zero, Polynomial.map_zero, mul_zero] at hD₂Hid
        exact intPoly_ne_zero s.den_ne_zero hD₂Hid.symm
      -- gcd cofactors `D₁/G ⊥ D₂/G` over `ℚ[X]`
      have hgcdD : GCDMonoid.gcd
          ((AzPolynomial.toPoly (slowD₁ r s)).map AzInt.toIntRingHom)
          ((AzPolynomial.toPoly (slowD₂ r s)).map AzInt.toIntRingHom) = 1 := by
        have h1 : GCDMonoid.gcd ((AzPolynomial.toPoly r.den).map AzInt.toIntRingHom)
              ((AzPolynomial.toPoly s.den).map AzInt.toIntRingHom)
            = _root_.normalize ((AzPolynomial.toPoly
                (Azurite.AzPolynomial.gcdNormalizedInt r.den s.den)).map
                  AzInt.toIntRingHom)
              * GCDMonoid.gcd
                  ((AzPolynomial.toPoly (slowD₁ r s)).map AzInt.toIntRingHom)
                  ((AzPolynomial.toPoly (slowD₂ r s)).map AzInt.toIntRingHom) := by
          rw [← hD₁id, ← hD₂id]
          exact gcd_mul_left _ _ _
        have h2 : _root_.normalize ((AzPolynomial.toPoly
              (Azurite.AzPolynomial.gcdNormalizedInt r.den s.den)).map
                AzInt.toIntRingHom)
            = (AzPolynomial.toPoly
                (Azurite.AzPolynomial.gcdNormalizedInt r.den s.den)).map
                  AzInt.toIntRingHom := by
          rw [hG]
          exact normalize_gcd _ _
        rw [h2, ← hG] at h1
        exact (mul_left_cancel₀ hGι0 (by rw [mul_one]; exact h1)).symm
      have hDD' : IsCoprime (toPolyQ (slowD₁ r s)) (toPolyQ (slowD₂ r s)) := by
        rw [toPolyQ_eq, toPolyQ_eq]
        exact isCoprime_map_of_gcd_isUnit (intPoly_ne_zero hD₂0)
          (by rw [hgcdD]; exact isUnit_one)
      have hND₁' : IsCoprime (toPolyQ r.num) (toPolyQ (slowD₁ r s)) :=
        hND₁.of_isCoprime_of_dvd_right
          ⟨toPolyQ (Azurite.AzPolynomial.gcdNormalizedInt r.den s.den), by
            rw [← hD₁fac]; ring⟩
      have hND₂' : IsCoprime (toPolyQ s.num) (toPolyQ (slowD₂ r s)) :=
        hND₂.of_isCoprime_of_dvd_right
          ⟨toPolyQ (Azurite.AzPolynomial.gcdNormalizedInt r.den s.den), by
            rw [← hD₂fac]; ring⟩
      -- `T₀/H ⊥ G/H` over `ℚ[X]` (the confined common part is exactly `H`)
      obtain ⟨G', hG'⟩ := hHdvdG
      have hG'0 : G' ≠ 0 := by
        intro h0
        rw [h0, mul_zero] at hG'
        exact hGι0 hG'
      have hgcdT' : GCDMonoid.gcd
          ((AzPolynomial.toPoly (slowT r s)).map AzInt.toIntRingHom) G' = 1 := by
        have h1 : GCDMonoid.gcd
              ((AzPolynomial.toPoly (slowT₀ r s)).map AzInt.toIntRingHom)
              ((AzPolynomial.toPoly
                (Azurite.AzPolynomial.gcdNormalizedInt r.den s.den)).map
                  AzInt.toIntRingHom)
            = _root_.normalize ((AzPolynomial.toPoly (slowH r s)).map
                AzInt.toIntRingHom)
              * GCDMonoid.gcd
                  ((AzPolynomial.toPoly (slowT r s)).map AzInt.toIntRingHom) G' := by
          rw [← hTid, hG']
          exact gcd_mul_left _ _ _
        have h2 : _root_.normalize ((AzPolynomial.toPoly (slowH r s)).map
              AzInt.toIntRingHom)
            = (AzPolynomial.toPoly (slowH r s)).map AzInt.toIntRingHom := by
          rw [hH]
          exact normalize_gcd _ _
        rw [h2, ← hH] at h1
        exact (mul_left_cancel₀ hHι0 (by rw [mul_one]; exact h1)).symm
      have hT'G' : IsCoprime (toPolyQ (slowT r s))
          (G'.map (Int.castRingHom ℚ)) := by
        rw [toPolyQ_eq]
        exact isCoprime_map_of_gcd_isUnit hG'0 (by rw [hgcdT']; exact isUnit_one)
      -- `T₀` is coprime with each of `D₁/G`, `D₂/G`
      have hT₀D₁ : IsCoprime (toPolyQ (slowT₀ r s)) (toPolyQ (slowD₁ r s)) := by
        have hbase : IsCoprime
            (Polynomial.C (((ratNum r.factor).toInt : ℚ) * ((ratDen s.factor).toInt : ℚ))
              * (toPolyQ r.num * toPolyQ (slowD₂ r s))) (toPolyQ (slowD₁ r s)) :=
          (isCoprime_C_left hc₁ _).mul_left (hND₁'.mul_left hDD'.symm)
        have h1 := hbase.add_mul_right_left
          (Polynomial.C (((ratNum s.factor).toInt : ℚ) * ((ratDen r.factor).toInt : ℚ))
            * toPolyQ s.num)
        have hshape : toPolyQ (slowT₀ r s)
            = Polynomial.C (((ratNum r.factor).toInt : ℚ)
                  * ((ratDen s.factor).toInt : ℚ))
                * (toPolyQ r.num * toPolyQ (slowD₂ r s))
              + (Polynomial.C (((ratNum s.factor).toInt : ℚ)
                  * ((ratDen r.factor).toInt : ℚ)) * toPolyQ s.num)
                * toPolyQ (slowD₁ r s) := by
          rw [toPolyQ_slowT₀]
          ring
        rw [← hshape] at h1
        exact h1
      have hT₀D₂ : IsCoprime (toPolyQ (slowT₀ r s)) (toPolyQ (slowD₂ r s)) := by
        have hbase : IsCoprime
            (Polynomial.C (((ratNum s.factor).toInt : ℚ) * ((ratDen r.factor).toInt : ℚ))
              * (toPolyQ s.num * toPolyQ (slowD₁ r s))) (toPolyQ (slowD₂ r s)) :=
          (isCoprime_C_left hc₂ _).mul_left (hND₂'.mul_left hDD')
        have h1 := hbase.add_mul_right_left
          (Polynomial.C (((ratNum r.factor).toInt : ℚ) * ((ratDen s.factor).toInt : ℚ))
            * toPolyQ r.num)
        have hshape : toPolyQ (slowT₀ r s)
            = Polynomial.C (((ratNum s.factor).toInt : ℚ)
                  * ((ratDen r.factor).toInt : ℚ))
                * (toPolyQ s.num * toPolyQ (slowD₁ r s))
              + (Polynomial.C (((ratNum r.factor).toInt : ℚ)
                  * ((ratDen s.factor).toInt : ℚ)) * toPolyQ r.num)
                * toPolyQ (slowD₂ r s) := by
          rw [toPolyQ_slowT₀]
          ring
        rw [← hshape] at h1
        exact h1
      -- assemble the numerator/denominator coprimality
      have hT₀fac : toPolyQ (slowH r s) * toPolyQ (slowT r s)
          = toPolyQ (slowT₀ r s) := cofactor_toPolyQ hTid
      have hD₂Hfac : toPolyQ (slowH r s) * toPolyQ (slowD₂H r s) = toPolyQ s.den :=
        cofactor_toPolyQ hD₂Hid
      have hT'dvd : toPolyQ (slowT r s) ∣ toPolyQ (slowT₀ r s) :=
        ⟨toPolyQ (slowH r s), by rw [← hT₀fac]; ring⟩
      have hT'D₁ := hT₀D₁.of_isCoprime_of_dvd_left hT'dvd
      have hT'D₂ := hT₀D₂.of_isCoprime_of_dvd_left hT'dvd
      have hGQfac : toPolyQ (Azurite.AzPolynomial.gcdNormalizedInt r.den s.den)
          = toPolyQ (slowH r s) * G'.map (Int.castRingHom ℚ) := by
        rw [toPolyQ_eq, toPolyQ_eq, hG', Polynomial.map_mul]
      have hD₂Hsplit : toPolyQ (slowD₂H r s)
          = G'.map (Int.castRingHom ℚ) * toPolyQ (slowD₂ r s) := by
        apply mul_left_cancel₀ (toPolyQ_ne_zero hH0)
        rw [hD₂Hfac, ← hD₂fac, hGQfac]
        ring
      have hT'D₂H : IsCoprime (toPolyQ (slowT r s)) (toPolyQ (slowD₂H r s)) := by
        rw [hD₂Hsplit]
        exact hT'G'.mul_right hT'D₂
      obtain ⟨haT0, haTkey, hpTprim, hpTlc⟩ := primPos_spec hT'0
      rw [← scalar_eq hT'0] at haT0 haTkey
      have hpTdvd : toPolyQ (Azurite.AzPolynomial.primPos (slowT r s))
          ∣ toPolyQ (slowT r s) :=
        ⟨Polynomial.C (((if (0 : AzInt) < (slowT r s).leadingCoeff
            then (slowT r s).content.toAzInt
            else -(slowT r s).content.toAzInt).toInt : ℚ)), by
          rw [← primPos_key_Q haTkey]
          ring⟩
      have hcop : Azurite.AzPolynomial.coprime
          (Azurite.AzPolynomial.primPos (slowT r s))
          (slowD₁ r s * slowD₂H r s) = true := by
        rw [coprime_toPolyQ_iff, toPolyQ_mul]
        exact (hT'D₁.mul_right hT'D₂H).of_isCoprime_of_dvd_left hpTdvd
      have h1g : (Azurite.AzPolynomial.primPos (slowT r s)).content = 1 :=
        content_az_one hpTprim
      have h2g : (slowD₁ r s * slowD₂H r s).content = 1 :=
        content_mul_one (content_cofactor hD₁id r.den_content)
          (content_cofactor hD₂Hid s.den_content)
      have h3g : (0 : AzInt) < (Azurite.AzPolynomial.primPos (slowT r s)).leadingCoeff :=
        lcPos_az hpTlc
      have h4g : (0 : AzInt) < (slowD₁ r s * slowD₂H r s).leadingCoeff :=
        lc_pos_mul (lc_pos_cofactor hD₁id hGlc r.den_lc_pos)
          (lc_pos_cofactor hD₂Hid hHlc s.den_lc_pos)
      have h6g : AzRat.ofAzInts
          (if (0 : AzInt) < (slowT r s).leadingCoeff then (slowT r s).content.toAzInt
            else -(slowT r s).content.toAzInt)
          (ratDen r.factor * ratDen s.factor) = 0
          → Azurite.AzPolynomial.primPos (slowT r s) = 1
            ∧ slowD₁ r s * slowD₂H r s = 1 := by
        intro h0
        exfalso
        have h1 := congrArg Azurite.AzRat.toRat h0
        rw [Azurite.AzRat.toRat_ofAzInts, Azurite.AzRat.toRat_zero] at h1
        rcases div_eq_zero_iff.mp h1 with h2 | h2
        · exact haT0 (by exact_mod_cast h2)
        · exact hbb0 (by exact_mod_cast h2)
      have hres : add r s = ⟨AzRat.ofAzInts
          (if (0 : AzInt) < (slowT r s).leadingCoeff then (slowT r s).content.toAzInt
            else -(slowT r s).content.toAzInt)
          (ratDen r.factor * ratDen s.factor),
          Azurite.AzPolynomial.primPos (slowT r s), slowD₁ r s * slowD₂H r s,
          h1g, h2g, h3g, h4g, hcop, h6g⟩ := by
        simp only [add, if_neg hr, if_neg hs, ratNum_def, ratDen_def, slowD₁_def,
          slowD₂_def, slowT₀_def, slowH_def, slowT_def, slowD₂H_def, if_neg hdeg,
          if_neg hT₀]
        rw [if_neg hT'0, dif_pos (⟨h1g, h2g, h3g, h4g, hcop, h6g⟩
          : _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _)]
      have hφL : algebraMap ℚ[X] (RatFunc ℚ)
          (Polynomial.C (((ratDen r.factor * ratDen s.factor).toInt : ℚ))
            * toPolyQ (slowD₁ r s * slowD₂H r s)) ≠ 0 :=
        RatFunc.algebraMap_ne_zero (mul_ne_zero
          (Polynomial.C_ne_zero.mpr (Int.cast_ne_zero.mpr hbb0))
          (by rw [toPolyQ_mul]
              exact mul_ne_zero (toPolyQ_ne_zero hD₁0) (toPolyQ_ne_zero hD₂H0)))
      have hpoly : Polynomial.C (((if (0 : AzInt) < (slowT r s).leadingCoeff
            then (slowT r s).content.toAzInt
            else -(slowT r s).content.toAzInt).toInt : ℚ))
            * toPolyQ (Azurite.AzPolynomial.primPos (slowT r s))
            * (Polynomial.C (((ratDen r.factor).toInt : ℚ)
                * ((ratDen s.factor).toInt : ℚ))
              * (toPolyQ r.den * toPolyQ s.den))
          = (Polynomial.C (((ratNum r.factor).toInt : ℚ)
                * ((ratDen s.factor).toInt : ℚ))
              * (toPolyQ r.num * toPolyQ s.den)
            + Polynomial.C (((ratNum s.factor).toInt : ℚ)
                * ((ratDen r.factor).toInt : ℚ))
              * (toPolyQ s.num * toPolyQ r.den))
            * (Polynomial.C (((ratDen r.factor * ratDen s.factor).toInt : ℚ))
              * toPolyQ (slowD₁ r s * slowD₂H r s)) := by
        rw [primPos_key_Q haTkey, hPfac, ← hT₀fac, ← hD₁fac, ← hD₂Hfac, toPolyQ_mul,
          Azurite.AzInt.toInt_mul, Int.cast_mul]
        ring
      rw [hres]
      show algebraMap ℚ (RatFunc ℚ) (Azurite.AzRat.toRat (AzRat.ofAzInts
          (if (0 : AzInt) < (slowT r s).leadingCoeff then (slowT r s).content.toAzInt
            else -(slowT r s).content.toAzInt)
          (ratDen r.factor * ratDen s.factor)))
          * (algebraMap ℚ[X] (RatFunc ℚ)
              (toPolyQ (Azurite.AzPolynomial.primPos (slowT r s)))
            / algebraMap ℚ[X] (RatFunc ℚ) (toPolyQ (slowD₁ r s * slowD₂H r s))) = _
      rw [Azurite.AzRat.toRat_ofAzInts, sum_eq r s, map_div₀, algebraMapQ_eq_C,
        ← RatFunc.algebraMap_C, ← RatFunc.algebraMap_C, div_mul_div_comm,
        ← map_mul, ← map_mul, div_eq_div_iff hφL hφR, ← map_mul, ← map_mul]
      exact congrArg _ hpoly

/-- **Subtraction is correct**:
`toRatFunc (r - s) = toRatFunc r - toRatFunc s`. -/
theorem toRatFunc_sub (r s : AzRationalFunction) :
    toRatFunc (r - s) = toRatFunc r - toRatFunc s := by
  show toRatFunc (r + -s) = _
  rw [toRatFunc_add, toRatFunc_neg, sub_eq_add_neg]

/-- `ofRatFunc` version: pulling back a sum. -/
theorem ofRatFunc_add (f g : RatFunc ℚ) :
    ofRatFunc (f + g) = ofRatFunc f + ofRatFunc g :=
  toRatFunc_injective (by
    rw [toRatFunc_ofRatFunc, toRatFunc_add, toRatFunc_ofRatFunc, toRatFunc_ofRatFunc])

/-- `ofRatFunc` version: pulling back a difference. -/
theorem ofRatFunc_sub (f g : RatFunc ℚ) :
    ofRatFunc (f - g) = ofRatFunc f - ofRatFunc g :=
  toRatFunc_injective (by
    rw [toRatFunc_ofRatFunc, toRatFunc_sub, toRatFunc_ofRatFunc, toRatFunc_ofRatFunc])

/-! ### Bridges for exponentiation -/

/-- `toPolyQ` of a computable power. -/
private theorem toPolyQ_pow (p : Azurite.AzPolynomial AzInt) (n : ℕ) :
    toPolyQ (Azurite.AzPolynomial.pow p n) = toPolyQ p ^ n := by
  rw [toPolyQ, toPolyQ, Azurite.AzPolynomial.toPoly_pow, Polynomial.map_pow]

/-- Powers of primitive parts are primitive (Gauss, iterated). -/
private theorem content_pow_one {p : Azurite.AzPolynomial AzInt} (hp : p.content = 1)
    (n : ℕ) : (Azurite.AzPolynomial.pow p n).content = 1 := by
  apply content_az_one
  have hprim : ∀ m : ℕ,
      (((AzPolynomial.toPoly p).map AzInt.toIntRingHom) ^ m).IsPrimitive := by
    intro m
    induction m with
    | zero =>
      rw [pow_zero]
      exact Polynomial.isPrimitive_one
    | succ k ih =>
      rw [pow_succ, Polynomial.isPrimitive_iff_content_eq_one, Polynomial.content_mul,
        Polynomial.isPrimitive_iff_content_eq_one.mp ih,
        Polynomial.isPrimitive_iff_content_eq_one.mp (isPrimitive_intPoly hp), mul_one]
  rw [Azurite.AzPolynomial.toPoly_pow, Polynomial.map_pow]
  exact hprim n

/-- Powers of positive-leading-coefficient parts keep the positive leading
coefficient. -/
private theorem lc_pos_pow {p : Azurite.AzPolynomial AzInt}
    (hp : (0 : AzInt) < p.leadingCoeff) (n : ℕ) :
    (0 : AzInt) < (Azurite.AzPolynomial.pow p n).leadingCoeff := by
  apply lcPos_az
  rw [Azurite.AzPolynomial.toPoly_pow, Polynomial.map_pow, Polynomial.leadingCoeff_pow]
  exact pow_pos (lcPos_int hp) n

/-- The computable power of the polynomial one is one. -/
private theorem az_one_pow (n : ℕ) :
    Azurite.AzPolynomial.pow (1 : Azurite.AzPolynomial AzInt) n = 1 := by
  apply toPoly_inj.mp
  rw [Azurite.AzPolynomial.toPoly_pow, toPoly_one, one_pow]

/-- **Exponentiation by `ℕ` is correct**:
`toRatFunc (pow r n) = toRatFunc r ^ n` — in particular the componentwise
constructor's invariant checks always pass (the fallback `0` branch is
unreachable). -/
theorem toRatFunc_pow (r : AzRationalFunction) (n : ℕ) :
    toRatFunc (pow r n) = toRatFunc r ^ n := by
  classical
  have hND : IsCoprime (toPolyQ r.num) (toPolyQ r.den) :=
    (coprime_toPolyQ_iff r.num r.den).mp r.reduced
  have h1g : (Azurite.AzPolynomial.pow r.num n).content = 1 :=
    content_pow_one r.num_content n
  have h2g : (Azurite.AzPolynomial.pow r.den n).content = 1 :=
    content_pow_one r.den_content n
  have h3g : (0 : AzInt) < (Azurite.AzPolynomial.pow r.num n).leadingCoeff :=
    lc_pos_pow r.num_lc_pos n
  have h4g : (0 : AzInt) < (Azurite.AzPolynomial.pow r.den n).leadingCoeff :=
    lc_pos_pow r.den_lc_pos n
  have h5g : Azurite.AzPolynomial.coprime (Azurite.AzPolynomial.pow r.num n)
      (Azurite.AzPolynomial.pow r.den n) = true := by
    rw [coprime_toPolyQ_iff, toPolyQ_pow, toPolyQ_pow]
    exact hND.pow
  have h6g : r.factor.pow n = 0
      → Azurite.AzPolynomial.pow r.num n = 1
        ∧ Azurite.AzPolynomial.pow r.den n = 1 := by
    intro h0
    have h1 := congrArg Azurite.AzRat.toRat h0
    rw [Azurite.AzRat.toRat_pow, Azurite.AzRat.toRat_zero] at h1
    have hn0 : n ≠ 0 := by
      intro hn
      subst hn
      rw [pow_zero] at h1
      exact one_ne_zero h1
    have hf0 : r.factor = 0 :=
      Azurite.AzRat.toRat_injective (by
        rw [(pow_eq_zero_iff hn0).mp h1, Azurite.AzRat.toRat_zero])
    obtain ⟨hn1, hd1⟩ := r.zero_norm hf0
    rw [hn1, hd1, az_one_pow]
    exact ⟨rfl, rfl⟩
  have hres : pow r n = ⟨r.factor.pow n, Azurite.AzPolynomial.pow r.num n,
      Azurite.AzPolynomial.pow r.den n, h1g, h2g, h3g, h4g, h5g, h6g⟩ := by
    simp only [pow]
    rw [dif_pos (⟨h1g, h2g, h3g, h4g, h5g, h6g⟩ : _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _)]
  rw [hres]
  show algebraMap ℚ (RatFunc ℚ) (Azurite.AzRat.toRat (r.factor.pow n))
      * (algebraMap ℚ[X] (RatFunc ℚ) (toPolyQ (Azurite.AzPolynomial.pow r.num n))
        / algebraMap ℚ[X] (RatFunc ℚ) (toPolyQ (Azurite.AzPolynomial.pow r.den n))) = _
  rw [toRatFunc, Azurite.AzRat.toRat_pow, toPolyQ_pow, toPolyQ_pow, map_pow, map_pow,
    map_pow, ← div_pow, ← mul_pow]

/-- **Exponentiation by `ℤ` is correct**:
`toRatFunc (zpow r z) = toRatFunc r ^ z` (`zpow` of a negative exponent is
the reciprocal of the positive power, on both sides). -/
theorem toRatFunc_zpow (r : AzRationalFunction) (z : ℤ) :
    toRatFunc (zpow r z) = toRatFunc r ^ z := by
  rw [zpow]
  by_cases hz : 0 ≤ z
  · rw [if_pos hz, toRatFunc_pow, ← zpow_natCast, Int.toNat_of_nonneg hz]
  · rw [if_neg hz, toRatFunc_inv, toRatFunc_pow, ← zpow_natCast,
      Int.toNat_of_nonneg (by omega), ← zpow_neg, neg_neg]

/-- `ofRatFunc` version: pulling back a `ℕ`-power. -/
theorem ofRatFunc_pow (f : RatFunc ℚ) (n : ℕ) :
    ofRatFunc (f ^ n) = pow (ofRatFunc f) n :=
  toRatFunc_injective (by
    rw [toRatFunc_ofRatFunc, toRatFunc_pow, toRatFunc_ofRatFunc])

/-- `ofRatFunc` version: pulling back a `ℤ`-power. -/
theorem ofRatFunc_zpow (f : RatFunc ℚ) (z : ℤ) :
    ofRatFunc (f ^ z) = zpow (ofRatFunc f) z :=
  toRatFunc_injective (by
    rw [toRatFunc_ofRatFunc, toRatFunc_zpow, toRatFunc_ofRatFunc])

/-! ### Bridges for composition -/

private theorem toPolyQ_one : toPolyQ (1 : Azurite.AzPolynomial AzInt) = 1 := by
  rw [toPolyQ, toPoly_one, Polynomial.map_one]

private theorem toPolyQ_coeff (p : Azurite.AzPolynomial AzInt) (k : ℕ) :
    (toPolyQ p).coeff k = ((p.coeff k).toInt : ℚ) := by
  rw [toPolyQ, Polynomial.coeff_map, coeff_toPoly_eq]
  rfl

private theorem coeffs_size_of_ne_zero {p : Azurite.AzPolynomial AzInt} (hp : p ≠ 0) :
    p.coeffs.size = p.natDegree + 1 := by
  have hsz : p.coeffs.size ≠ 0 :=
    fun h => hp (AzPolynomial.ext (by rw [Array.size_eq_zero_iff.mp h]; rfl))
  show _ = p.coeffs.size - 1 + 1
  omega

private theorem az_zero_mul (q : Azurite.AzPolynomial AzInt) :
    (0 : Azurite.AzPolynomial AzInt) * q = 0 := by
  apply toPoly_inj.mp
  rw [Azurite.AzPolynomial.toPoly_mul, toPoly_zero, zero_mul]

private theorem az_smul_zero (z : AzInt) : z • (0 : Azurite.AzPolynomial AzInt) = 0 := by
  apply toPoly_inj.mp
  rw [Azurite.AzPolynomial.toPoly_smul, toPoly_zero, smul_zero]

/-- The `evalSpecialComp` fold, mapped componentwise to `ℚ[X]`: it becomes
the generic `evalSpecialStep` fold over the constant-embedded coefficients. -/
private theorem toPolyQ_fold_pair (l : List AzInt) (b c : Azurite.AzPolynomial AzInt) :
    toPolyQ ((l.foldr (fun a x => (a • x.2 + x.1 * b, x.2 * c)) (0, 1)).1)
      = ((l.map (fun a : AzInt => Polynomial.C ((a.toInt : ℚ)))).foldr
          (evalSpecialStep (toPolyQ b) (toPolyQ c)) (0, 1)).1
    ∧ toPolyQ ((l.foldr (fun a x => (a • x.2 + x.1 * b, x.2 * c)) (0, 1)).2)
      = ((l.map (fun a : AzInt => Polynomial.C ((a.toInt : ℚ)))).foldr
          (evalSpecialStep (toPolyQ b) (toPolyQ c)) (0, 1)).2 := by
  induction l with
  | nil => exact ⟨toPolyQ_zero, toPolyQ_one⟩
  | cons a as ih =>
    simp only [List.foldr_cons, List.map_cons, evalSpecialStep]
    constructor
    · rw [toPolyQ_add, toPolyQ_smul, toPolyQ_mul, ih.1, ih.2]
    · rw [toPolyQ_mul, ih.2]

/-- The `ℚ[X]` image of the homogenized composition kernel, as a sum. -/
private theorem toPolyQ_evalSpecialComp (p aA bB : Azurite.AzPolynomial AzInt) :
    toPolyQ (evalSpecialComp p aA bB)
      = ∑ k ∈ Finset.range p.coeffs.size,
          Polynomial.C (((p.coeff k).toInt : ℚ)) * toPolyQ aA ^ k
            * toPolyQ bB ^ (p.natDegree - k) := by
  rw [evalSpecialComp]
  rw [show p.coeffs.foldr (fun a x => (a • x.2 + x.1 * aA, x.2 * bB)) (0, 1)
      = p.coeffs.toList.foldr (fun a x => (a • x.2 + x.1 * aA, x.2 * bB)) (0, 1) from by
    rw [Array.foldr_toList]]
  rw [(toPolyQ_fold_pair p.coeffs.toList aA bB).1, evalSpecial_list_eq]
  apply Finset.sum_congr (by simp)
  intro k hk
  rw [Finset.mem_range] at hk
  have hcoeff : (p.coeffs.toList.map
        (fun a : AzInt => Polynomial.C ((a.toInt : ℚ)))).getCoeff k
      = Polynomial.C (((p.coeff k).toInt : ℚ)) := by
    simp [List.getCoeff, List.getElem?_map, Array.getElem?_toList,
      Azurite.AzPolynomial.coeff, Array.getElem?_eq_getElem hk]
  rw [hcoeff]
  simp [Azurite.AzPolynomial.natDegree]

/-- **The homogenization identity**: over `ℚ(x)`, evaluating a part at the
fraction `φA / φB` and clearing the `φB`-power denominator is exactly the
image of `evalSpecialComp`. -/
private theorem aeval_evalSpecialComp {p : Azurite.AzPolynomial AzInt} (hp : p ≠ 0)
    (aA bB : Azurite.AzPolynomial AzInt) (hB : toPolyQ bB ≠ 0) :
    Polynomial.aeval (algebraMap ℚ[X] (RatFunc ℚ) (toPolyQ aA)
        / algebraMap ℚ[X] (RatFunc ℚ) (toPolyQ bB)) (toPolyQ p)
      * algebraMap ℚ[X] (RatFunc ℚ) (toPolyQ bB) ^ p.natDegree
    = algebraMap ℚ[X] (RatFunc ℚ) (toPolyQ (evalSpecialComp p aA bB)) := by
  have hφB0 : algebraMap ℚ[X] (RatFunc ℚ) (toPolyQ bB) ≠ 0 :=
    RatFunc.algebraMap_ne_zero hB
  have hsz : p.coeffs.size = p.natDegree + 1 := coeffs_size_of_ne_zero hp
  have hdeg : (toPolyQ p).natDegree < p.coeffs.size := by
    have h1 : (toPolyQ p).natDegree ≤ p.natDegree := by
      rw [← AzPolynomial.natDegree_toPoly p, toPolyQ]
      exact Polynomial.natDegree_map_le
    omega
  rw [toPolyQ_evalSpecialComp, map_sum, Polynomial.aeval_def,
    Polynomial.eval₂_eq_sum_range' (algebraMap ℚ (RatFunc ℚ)) hdeg, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.mem_range] at hk
  have hkn : k ≤ p.natDegree := by omega
  rw [toPolyQ_coeff, map_mul, map_mul, map_pow, map_pow, RatFunc.algebraMap_C,
    ← algebraMapQ_eq_C]
  have hpow : (algebraMap ℚ[X] (RatFunc ℚ) (toPolyQ aA)
        / algebraMap ℚ[X] (RatFunc ℚ) (toPolyQ bB)) ^ k
        * algebraMap ℚ[X] (RatFunc ℚ) (toPolyQ bB) ^ p.natDegree
      = algebraMap ℚ[X] (RatFunc ℚ) (toPolyQ aA) ^ k
        * algebraMap ℚ[X] (RatFunc ℚ) (toPolyQ bB) ^ (p.natDegree - k) := by
    rw [div_pow, pow_sub₀ _ hφB0 hkn, div_mul_eq_mul_div, mul_div_assoc,
      div_eq_mul_inv]
  rw [mul_assoc, hpow, ← mul_assoc]

set_option maxHeartbeats 1600000 in
/-- **Composition is correct**: whenever the denominator part of `r` does not
vanish at `s` (as a rational function), `comp r s` represents
`factor · num(S) / den(S)` at `S := toRatFunc s`. (The vanishing case is the
junk value `0` — see `comp_eq_zero_of_aeval_den_eq_zero`.) -/
theorem toRatFunc_comp (r s : AzRationalFunction)
    (hd : Polynomial.aeval (toRatFunc s) (toPolyQ r.den) ≠ 0) :
    toRatFunc (comp r s)
      = algebraMap ℚ (RatFunc ℚ) (Azurite.AzRat.toRat r.factor)
        * (Polynomial.aeval (toRatFunc s) (toPolyQ r.num)
            / Polynomial.aeval (toRatFunc s) (toPolyQ r.den)) := by
  classical
  have hβ₁ : ((ratDen r.factor).toInt : ℚ) ≠ 0 :=
    Int.cast_ne_zero.mpr (ratDen_toInt_pos r.factor).ne'
  have hβ₂ : ((ratDen s.factor).toInt : ℚ) ≠ 0 :=
    Int.cast_ne_zero.mpr (ratDen_toInt_pos s.factor).ne'
  have hBQ0 : toPolyQ (ratDen s.factor • s.den) ≠ 0 := by
    rw [toPolyQ_smul]
    exact mul_ne_zero (Polynomial.C_ne_zero.mpr hβ₂) (toPolyQ_den_ne_zero s)
  have hφB0 : algebraMap ℚ[X] (RatFunc ℚ) (toPolyQ (ratDen s.factor • s.den)) ≠ 0 :=
    RatFunc.algebraMap_ne_zero hBQ0
  have hS : toRatFunc s
      = algebraMap ℚ[X] (RatFunc ℚ) (toPolyQ (ratNum s.factor • s.num))
        / algebraMap ℚ[X] (RatFunc ℚ) (toPolyQ (ratDen s.factor • s.den)) := by
    rw [toRatFunc, toRat_factored, map_div₀, algebraMapQ_eq_C, ← RatFunc.algebraMap_C,
      ← RatFunc.algebraMap_C, div_mul_div_comm, ← map_mul, ← map_mul, ← toPolyQ_smul,
      ← toPolyQ_smul]
  have hN := aeval_evalSpecialComp r.num_ne_zero (ratNum s.factor • s.num)
    (ratDen s.factor • s.den) hBQ0
  have hD := aeval_evalSpecialComp r.den_ne_zero (ratNum s.factor • s.num)
    (ratDen s.factor • s.den) hBQ0
  -- the composed denominator part is nonzero
  have hTD0 : evalSpecialComp r.den (ratNum s.factor • s.num) (ratDen s.factor • s.den)
      ≠ 0 := by
    intro h0
    apply hd
    rw [hS]
    have h1 := hD
    rw [h0, toPolyQ_zero, map_zero] at h1
    rcases mul_eq_zero.mp h1 with h2 | h2
    · exact h2
    · exact absurd h2 (pow_ne_zero _ hφB0)
  have hd0 : ratDen r.factor
      • (evalSpecialComp r.den (ratNum s.factor • s.num) (ratDen s.factor • s.den)
        * Azurite.AzPolynomial.pow (ratDen s.factor • s.den)
            (r.num.natDegree - r.den.natDegree)) ≠ 0 := by
    intro h0
    have h1 := congrArg toPolyQ h0
    rw [toPolyQ_smul, toPolyQ_mul, toPolyQ_pow, toPolyQ_zero] at h1
    rcases mul_eq_zero.mp h1 with h2 | h2
    · exact Polynomial.C_ne_zero.mpr hβ₁ h2
    · rcases mul_eq_zero.mp h2 with h3 | h3
      · exact toPolyQ_ne_zero hTD0 h3
      · exact pow_ne_zero _ hBQ0 h3
  show toRatFunc (ofNumDen
      (ratNum r.factor
        • (evalSpecialComp r.num (ratNum s.factor • s.num) (ratDen s.factor • s.den)
          * Azurite.AzPolynomial.pow (ratDen s.factor • s.den)
              (r.den.natDegree - r.num.natDegree)))
      (ratDen r.factor
        • (evalSpecialComp r.den (ratNum s.factor • s.num) (ratDen s.factor • s.den)
          * Azurite.AzPolynomial.pow (ratDen s.factor • s.den)
              (r.num.natDegree - r.den.natDegree)))) = _
  rw [toRatFunc_ofNumDen _ _ hd0, toPolyQ_smul, toPolyQ_smul, toPolyQ_mul, toPolyQ_mul,
    toPolyQ_pow, toPolyQ_pow]
  simp only [map_mul, map_pow]
  rw [RatFunc.algebraMap_C, RatFunc.algebraMap_C, ← algebraMapQ_eq_C, hS, ← hN, ← hD,
    toRat_factored, map_div₀]
  have hexp : r.num.natDegree + (r.den.natDegree - r.num.natDegree)
      = r.den.natDegree + (r.num.natDegree - r.den.natDegree) := by omega
  have hshift : ∀ (u v : RatFunc ℚ) (m e : ℕ),
      u * (v * algebraMap ℚ[X] (RatFunc ℚ) (toPolyQ (ratDen s.factor • s.den)) ^ m
        * algebraMap ℚ[X] (RatFunc ℚ) (toPolyQ (ratDen s.factor • s.den)) ^ e)
      = u * v
        * algebraMap ℚ[X] (RatFunc ℚ) (toPolyQ (ratDen s.factor • s.den)) ^ (m + e) := by
    intro u v m e
    rw [pow_add]
    ring
  rw [hshift, hshift, hexp,
    mul_div_mul_right _ _ (pow_ne_zero _ hφB0), div_mul_div_comm]

/-- **The junk case**: when the denominator part of `r` vanishes at `s`
(a constant sitting at a pole of `r`), the composition is the junk value
`0`, consistent with the `ofNumDen`/`eval` conventions. -/
theorem comp_eq_zero_of_aeval_den_eq_zero (r s : AzRationalFunction)
    (hd : Polynomial.aeval (toRatFunc s) (toPolyQ r.den) = 0) :
    comp r s = 0 := by
  classical
  have hβ₂ : ((ratDen s.factor).toInt : ℚ) ≠ 0 :=
    Int.cast_ne_zero.mpr (ratDen_toInt_pos s.factor).ne'
  have hBQ0 : toPolyQ (ratDen s.factor • s.den) ≠ 0 := by
    rw [toPolyQ_smul]
    exact mul_ne_zero (Polynomial.C_ne_zero.mpr hβ₂) (toPolyQ_den_ne_zero s)
  have hS : toRatFunc s
      = algebraMap ℚ[X] (RatFunc ℚ) (toPolyQ (ratNum s.factor • s.num))
        / algebraMap ℚ[X] (RatFunc ℚ) (toPolyQ (ratDen s.factor • s.den)) := by
    rw [toRatFunc, toRat_factored, map_div₀, algebraMapQ_eq_C, ← RatFunc.algebraMap_C,
      ← RatFunc.algebraMap_C, div_mul_div_comm, ← map_mul, ← map_mul, ← toPolyQ_smul,
      ← toPolyQ_smul]
  have hD := aeval_evalSpecialComp r.den_ne_zero (ratNum s.factor • s.num)
    (ratDen s.factor • s.den) hBQ0
  have hTD0 : evalSpecialComp r.den (ratNum s.factor • s.num) (ratDen s.factor • s.den)
      = 0 := by
    have h1 := hD
    rw [← hS, hd, zero_mul] at h1
    have h2 : toPolyQ (evalSpecialComp r.den (ratNum s.factor • s.num)
        (ratDen s.factor • s.den)) = 0 := by
      by_contra hne
      exact RatFunc.algebraMap_ne_zero hne h1.symm
    by_contra hne
    exact toPolyQ_ne_zero hne h2
  show ofNumDen
      (ratNum r.factor
        • (evalSpecialComp r.num (ratNum s.factor • s.num) (ratDen s.factor • s.den)
          * Azurite.AzPolynomial.pow (ratDen s.factor • s.den)
              (r.den.natDegree - r.num.natDegree)))
      (ratDen r.factor
        • (evalSpecialComp r.den (ratNum s.factor • s.num) (ratDen s.factor • s.den)
          * Azurite.AzPolynomial.pow (ratDen s.factor • s.den)
              (r.num.natDegree - r.den.natDegree))) = 0
  rw [hTD0, az_zero_mul, az_smul_zero, ofNumDen_den_zero]

/-! ### Bridges for the derivative, degree, asymptotic signs, and the
polynomial retraction -/

private theorem toPolyQ_sub (p q : Azurite.AzPolynomial AzInt) :
    toPolyQ (p - q) = toPolyQ p - toPolyQ q := by
  rw [toPolyQ, toPolyQ, toPolyQ, Azurite.AzPolynomial.toPoly_sub, Polynomial.map_sub]

private theorem toPolyQ_derivative (p : Azurite.AzPolynomial AzInt) :
    toPolyQ (Azurite.AzPolynomial.derivative p)
      = Polynomial.derivative (toPolyQ p) := by
  rw [toPolyQ, toPolyQ, Azurite.AzPolynomial.toPoly_derivative, Polynomial.derivative_map]

private theorem natDegree_toPolyQ (p : Azurite.AzPolynomial AzInt) :
    (toPolyQ p).natDegree = p.natDegree := by
  rw [toPolyQ, Polynomial.natDegree_map_eq_of_injective
    (fun _ _ h => hιinj (hκinj h)), AzPolynomial.natDegree_toPoly]

private theorem eq_zero_of_factor_eq_zero {r : AzRationalFunction}
    (hf : r.factor = 0) : r = 0 := by
  obtain ⟨h1, h2⟩ := r.zero_norm hf
  exact ext (by rw [hf]; rfl) (by rw [h1]; rfl) (by rw [h2]; rfl)

private theorem toRat_pos_iff {q : Azurite.AzRat} (hq : q ≠ 0) :
    0 < Azurite.AzRat.toRat q ↔ q.sign = true := by
  have hα0 : (ratNum q).toInt ≠ 0 := ratNum_toInt_ne_zero hq
  have hαne : ratNum q ≠ 0 := fun h => hα0 (by rw [h]; rfl)
  have hβ : (0 : ℚ) < ((ratDen q).toInt : ℚ) := by
    exact_mod_cast ratDen_toInt_pos q
  rw [toRat_factored, div_pos_iff]
  constructor
  · rintro (⟨h1, _⟩ | ⟨_, h2⟩)
    · exact (toInt_pos_iff_sign hαne).mp (by exact_mod_cast h1)
    · exact absurd hβ (by linarith)
  · intro hs
    exact Or.inl ⟨by exact_mod_cast (toInt_pos_iff_sign hαne).mpr hs, hβ⟩

/-- **The derivative is correct** — the quotient rule in `ℚ(x)`:
`toRatFunc (derivative r) = factor · (N′D − ND′) / D²`. (Mathlib has no
derivation on `RatFunc`, so the formula is stated against the `ℚ[X]`
images.) -/
theorem toRatFunc_derivative (r : AzRationalFunction) :
    toRatFunc (derivative r)
      = algebraMap ℚ (RatFunc ℚ) (Azurite.AzRat.toRat r.factor)
        * (algebraMap ℚ[X] (RatFunc ℚ)
            (Polynomial.derivative (toPolyQ r.num) * toPolyQ r.den
              - toPolyQ r.num * Polynomial.derivative (toPolyQ r.den))
          / algebraMap ℚ[X] (RatFunc ℚ) (toPolyQ r.den * toPolyQ r.den)) := by
  have hβ₁ : ((ratDen r.factor).toInt : ℚ) ≠ 0 :=
    Int.cast_ne_zero.mpr (ratDen_toInt_pos r.factor).ne'
  have hd0 : ratDen r.factor • (r.den * r.den) ≠ 0 := by
    intro h0
    have h1 := congrArg toPolyQ h0
    rw [toPolyQ_smul, toPolyQ_mul, toPolyQ_zero] at h1
    rcases mul_eq_zero.mp h1 with h2 | h2
    · exact Polynomial.C_ne_zero.mpr hβ₁ h2
    · rcases mul_eq_zero.mp h2 with h3 | h3 <;> exact toPolyQ_den_ne_zero r h3
  show toRatFunc (ofNumDen
      (ratNum r.factor • (Azurite.AzPolynomial.derivative r.num * r.den
        - r.num * Azurite.AzPolynomial.derivative r.den))
      (ratDen r.factor • (r.den * r.den))) = _
  rw [toRatFunc_ofNumDen _ _ hd0, toPolyQ_smul, toPolyQ_smul, toPolyQ_sub, toPolyQ_mul,
    toPolyQ_mul, toPolyQ_mul, toPolyQ_derivative, toPolyQ_derivative, map_mul, map_mul,
    RatFunc.algebraMap_C, RatFunc.algebraMap_C, ← algebraMapQ_eq_C, toRat_factored,
    map_div₀, div_mul_div_comm]

/-- **The integer degree is correct**: it is Mathlib's `RatFunc.intDegree`
of the represented rational function (both conventions give `0` at `0`). -/
theorem intDegree_eq (r : AzRationalFunction) :
    intDegree r = (toRatFunc r).intDegree := by
  by_cases hf : r.factor = 0
  · have hr0 : toRatFunc r = 0 := by
      rw [toRatFunc, hf, Azurite.AzRat.toRat_zero, map_zero, zero_mul]
    obtain ⟨hn1, hd1⟩ := r.zero_norm hf
    have h1 : (1 : Azurite.AzPolynomial AzInt).natDegree = 0 := by
      rw [← AzPolynomial.natDegree_toPoly, toPoly_one, Polynomial.natDegree_one]
    rw [hr0, RatFunc.intDegree_zero, intDegree, hn1, hd1, h1]
    norm_num
  · have hα₁ : ((ratNum r.factor).toInt : ℚ) ≠ 0 :=
      Int.cast_ne_zero.mpr (ratNum_toInt_ne_zero hf)
    have hβ₁ : ((ratDen r.factor).toInt : ℚ) ≠ 0 :=
      Int.cast_ne_zero.mpr (ratDen_toInt_pos r.factor).ne'
    have hAQ0 : toPolyQ (ratNum r.factor • r.num) ≠ 0 := by
      rw [toPolyQ_smul]
      exact mul_ne_zero (Polynomial.C_ne_zero.mpr hα₁) (toPolyQ_num_ne_zero r)
    have hBQ0 : toPolyQ (ratDen r.factor • r.den) ≠ 0 := by
      rw [toPolyQ_smul]
      exact mul_ne_zero (Polynomial.C_ne_zero.mpr hβ₁) (toPolyQ_den_ne_zero r)
    have hS : toRatFunc r
        = algebraMap ℚ[X] (RatFunc ℚ) (toPolyQ (ratNum r.factor • r.num))
          / algebraMap ℚ[X] (RatFunc ℚ) (toPolyQ (ratDen r.factor • r.den)) := by
      rw [toRatFunc, toRat_factored, map_div₀, algebraMapQ_eq_C, ← RatFunc.algebraMap_C,
        ← RatFunc.algebraMap_C, div_mul_div_comm, ← map_mul, ← map_mul, ← toPolyQ_smul,
        ← toPolyQ_smul]
    have hn : (toPolyQ (ratNum r.factor • r.num)).natDegree = r.num.natDegree := by
      rw [toPolyQ_smul, Polynomial.natDegree_C_mul hα₁, natDegree_toPolyQ]
    have hd : (toPolyQ (ratDen r.factor • r.den)).natDegree = r.den.natDegree := by
      rw [toPolyQ_smul, Polynomial.natDegree_C_mul hβ₁, natDegree_toPolyQ]
    rw [hS, RatFunc.intDegree_div (RatFunc.algebraMap_ne_zero hAQ0)
      (RatFunc.algebraMap_ne_zero hBQ0), RatFunc.intDegree_polynomial,
      RatFunc.intDegree_polynomial, hn, hd, intDegree]

/-- `signTop` vanishes exactly at `0`. (Analytically, `signTop r` is the
sign of `r(x)` for all large `x`: both parts have positive leading
coefficients, so the leading behavior at `+∞` carries exactly the sign of
the rational factor.) -/
theorem signTop_eq_zero_iff (r : AzRationalFunction) : signTop r = 0 ↔ r = 0 := by
  rw [signTop]
  by_cases hf : r.factor = 0
  · rw [if_pos hf]
    exact ⟨fun _ => eq_zero_of_factor_eq_zero hf, fun _ => rfl⟩
  · rw [if_neg hf]
    constructor
    · intro h0
      by_cases hs : r.factor.sign = true
      · rw [if_pos hs] at h0
        exact absurd h0 (by decide)
      · rw [if_neg hs] at h0
        exact absurd h0 (by decide)
    · intro h0
      rw [h0] at hf
      exact absurd rfl hf

/-- **The factor-sign characterization of `signTop`, positive case**:
`signTop r = 1` exactly when the rational factor is positive. -/
theorem signTop_eq_one_iff (r : AzRationalFunction) :
    signTop r = 1 ↔ 0 < Azurite.AzRat.toRat r.factor := by
  rw [signTop]
  by_cases hf : r.factor = 0
  · rw [if_pos hf, hf, Azurite.AzRat.toRat_zero]
    constructor
    · intro h0
      exact absurd h0 (by decide)
    · intro h0
      exact absurd h0 (lt_irrefl 0)
  · rw [if_neg hf, show (0 < Azurite.AzRat.toRat r.factor) = (r.factor.sign = true) from
      propext (toRat_pos_iff hf)]
    by_cases hs : r.factor.sign = true
    · rw [if_pos hs]
      simp [hs]
    · rw [if_neg hs]
      constructor
      · intro h0
        exact absurd h0 (by decide)
      · intro h0
        exact absurd h0 hs

/-- **The factor-sign characterization of `signTop`, negative case**:
`signTop r = -1` exactly when the rational factor is negative. -/
theorem signTop_eq_neg_one_iff (r : AzRationalFunction) :
    signTop r = -1 ↔ Azurite.AzRat.toRat r.factor < 0 := by
  rw [signTop]
  by_cases hf : r.factor = 0
  · rw [if_pos hf, hf, Azurite.AzRat.toRat_zero]
    constructor
    · intro h0
      exact absurd h0 (by decide)
    · intro h0
      exact absurd h0 (lt_irrefl 0)
  · have htr0 : Azurite.AzRat.toRat r.factor ≠ 0 := fun h =>
      hf (Azurite.AzRat.toRat_injective (by rw [h, Azurite.AzRat.toRat_zero]))
    rw [if_neg hf]
    by_cases hs : r.factor.sign = true
    · rw [if_pos hs]
      constructor
      · intro h0
        exact absurd h0 (by decide)
      · intro h0
        exact absurd ((toRat_pos_iff hf).mpr hs) (by linarith)
    · rw [if_neg hs]
      constructor
      · intro _
        rcases lt_trichotomy (Azurite.AzRat.toRat r.factor) 0 with h | h | h
        · exact h
        · exact absurd h htr0
        · exact absurd ((toRat_pos_iff hf).mp h) hs
      · intro _
        rfl

/-- `signBot` vanishes exactly at `0` (the parity flip never kills a
sign). -/
theorem signBot_eq_zero_iff (r : AzRationalFunction) : signBot r = 0 ↔ r = 0 := by
  rw [signBot]
  split
  · exact signTop_eq_zero_iff r
  · rw [neg_eq_zero]
    exact signTop_eq_zero_iff r

/-- **`toPolynomial` retracts `ofPolynomial`**: the canonical form of a
polynomial is recognized and its displayed numerator is the polynomial. -/
theorem toPolynomial_ofPolynomial (p : Azurite.AzPolynomial AzInt) :
    toPolynomial (ofPolynomial p) = some p := by
  have hdd : toPolyQ (displayDen (ofPolynomial p)) = toPolyQ 1 := by
    rw [displayDen_ofPolynomial]
  rw [displayDen, ratDen_def, toPolyQ_smul, toPolyQ_one] at hdd
  have hβ : ((ratDen (ofPolynomial p).factor).toInt : ℚ) ≠ 0 :=
    Int.cast_ne_zero.mpr (ratDen_toInt_pos (ofPolynomial p).factor).ne'
  have hdeg : (ofPolynomial p).den.natDegree = 0 := by
    have h1 := congrArg Polynomial.natDegree hdd
    rw [Polynomial.natDegree_C_mul hβ, natDegree_toPolyQ, Polynomial.natDegree_one] at h1
    exact h1
  have hden1 : (ofPolynomial p).den = 1 := by
    have hdc : ((AzPolynomial.toPoly (ofPolynomial p).den).map
        AzInt.toIntRingHom).natDegree = 0 := by
      rw [Polynomial.natDegree_map_eq_of_injective hιinj, AzPolynomial.natDegree_toPoly]
      exact hdeg
    have hC := Polynomial.eq_C_of_natDegree_eq_zero hdc
    have hlc : 0 < ((AzPolynomial.toPoly (ofPolynomial p).den).map
        AzInt.toIntRingHom).coeff 0 := by
      have h1 := lcPos_int (ofPolynomial p).den_lc_pos
      rwa [Polynomial.leadingCoeff, hdc] at h1
    have hcont := isPrimitive_intPoly (ofPolynomial p).den_content
    rw [Polynomial.isPrimitive_iff_content_eq_one, hC, Polynomial.content_C,
      ← Int.abs_eq_normalize] at hcont
    have hone : ((AzPolynomial.toPoly (ofPolynomial p).den).map
        AzInt.toIntRingHom).coeff 0 = 1 := by
      rcases (abs_eq (by norm_num : (0 : ℤ) ≤ 1)).mp hcont with h | h
      · exact h
      · rw [h] at hlc
        norm_num at hlc
    apply toPoly_inj.mp
    apply Polynomial.map_injective _ hιinj
    rw [hC, hone, Polynomial.C_1, toPoly_one, Polynomial.map_one]
  have hfden1 : (ofPolynomial p).factor.den = 1 := by
    rw [hden1, toPolyQ_one, mul_one] at hdd
    have h1 : ((ratDen (ofPolynomial p).factor).toInt : ℚ) = 1 := by
      have h2 := congrArg (fun q : ℚ[X] => q.coeff 0) hdd
      simpa using h2
    rw [ratDen_toInt] at h1
    have h2 : (ofPolynomial p).factor.den.toNat = 1 := by exact_mod_cast h1
    apply Azurite.AzNat.toNat_injective
    rw [h2]
    rfl
  rw [toPolynomial, if_pos ⟨hden1, hfden1⟩, displayNum_ofPolynomial]

/-- **`toPolynomial` only hits polynomials**: a `some`-value pins `r` down
as the canonical form of that polynomial (with `toPolynomial_ofPolynomial`,
the `some`-range is exactly the polynomials). -/
theorem eq_ofPolynomial_of_toPolynomial {r : AzRationalFunction}
    {p : Azurite.AzPolynomial AzInt} (h : toPolynomial r = some p) :
    r = ofPolynomial p := by
  rw [toPolynomial] at h
  by_cases hc : r.den = 1 ∧ r.factor.den = 1
  · rw [if_pos hc] at h
    have hp : displayNum r = p := Option.some_injective _ h
    apply toRatFunc_injective
    rw [toRatFunc_ofPolynomial, ← hp, displayNum, ratNum_def, toPolyQ_smul, map_mul,
      RatFunc.algebraMap_C, ← algebraMapQ_eq_C, toRatFunc, toRat_factored]
    have h0 : (1 : AzNat).toNat = 1 := rfl
    have hβ1 : ((ratDen r.factor).toInt : ℚ) = 1 := by
      rw [ratDen_toInt, hc.2, h0]
      norm_num
    have hD1 : toPolyQ r.den = 1 := by
      rw [hc.1, toPolyQ_one]
    rw [hβ1, hD1, div_one, map_one, div_one]
  · rw [if_neg hc] at h
    simp at h

/-! ### The Mathlib `num`/`denom` identification and the `RatFunc.eval`
connection -/

/-- **Uniqueness of the coprime-monic representation**: a coprime pair with
monic denominator representing `f` is exactly `(f.num, f.denom)`. -/
private theorem num_denom_ext {A B : ℚ[X]} (hB : B.Monic) (hcop : IsCoprime A B)
    {f : RatFunc ℚ}
    (hf : f = algebraMap ℚ[X] (RatFunc ℚ) A / algebraMap ℚ[X] (RatFunc ℚ) B) :
    f.num = A ∧ f.denom = B := by
  have hB0 : B ≠ 0 := hB.ne_zero
  have hφB : algebraMap ℚ[X] (RatFunc ℚ) B ≠ 0 := RatFunc.algebraMap_ne_zero hB0
  have hφd : algebraMap ℚ[X] (RatFunc ℚ) f.denom ≠ 0 :=
    RatFunc.algebraMap_ne_zero (RatFunc.denom_ne_zero f)
  have hcross : f.num * B = A * f.denom := by
    have h1 : algebraMap ℚ[X] (RatFunc ℚ) f.num / algebraMap ℚ[X] (RatFunc ℚ) f.denom
        = algebraMap ℚ[X] (RatFunc ℚ) A / algebraMap ℚ[X] (RatFunc ℚ) B := by
      rw [RatFunc.num_div_denom, hf]
    rw [div_eq_div_iff hφd hφB, ← map_mul, ← map_mul] at h1
    exact RatFunc.algebraMap_injective ℚ h1
  have hfcop := RatFunc.isCoprime_num_denom f
  have hd1 : f.denom ∣ B :=
    hfcop.symm.dvd_of_dvd_mul_left ⟨A, by rw [hcross]; ring⟩
  have hd2 : B ∣ f.denom :=
    hcop.symm.dvd_of_dvd_mul_left ⟨f.num, by rw [← hcross]; ring⟩
  have hdeq : f.denom = B :=
    Polynomial.eq_of_monic_of_associated (RatFunc.monic_denom f) hB
      (associated_of_dvd_dvd hd1 hd2)
  refine ⟨?_, hdeq⟩
  have h3 : f.num * B = A * B := by rw [hcross, hdeq]
  exact mul_right_cancel₀ hB0 h3

/-- The rescaled display pair of a nonzero `AzRationalFunction` is the
Mathlib `num`/`denom` pair. -/
private theorem num_denom_aux (r : AzRationalFunction) (hf : r.factor ≠ 0) :
    (toRatFunc r).num
        = Polynomial.C (Azurite.AzRat.toRat r.factor / (toPolyQ r.den).leadingCoeff)
          * toPolyQ r.num
      ∧ (toRatFunc r).denom
        = Polynomial.C ((toPolyQ r.den).leadingCoeff)⁻¹ * toPolyQ r.den := by
  have hD0 := toPolyQ_den_ne_zero r
  have hℓ0 : (toPolyQ r.den).leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hD0
  have hc0 : Azurite.AzRat.toRat r.factor ≠ 0 := fun h =>
    hf (Azurite.AzRat.toRat_injective (by rw [h, Azurite.AzRat.toRat_zero]))
  have hmonic : (Polynomial.C ((toPolyQ r.den).leadingCoeff)⁻¹ * toPolyQ r.den).Monic := by
    have h1 := Polynomial.monic_mul_leadingCoeff_inv hD0
    rwa [mul_comm] at h1
  have hND : IsCoprime (toPolyQ r.num) (toPolyQ r.den) :=
    (coprime_toPolyQ_iff r.num r.den).mp r.reduced
  have hcop : IsCoprime
      (Polynomial.C (Azurite.AzRat.toRat r.factor / (toPolyQ r.den).leadingCoeff)
        * toPolyQ r.num)
      (Polynomial.C ((toPolyQ r.den).leadingCoeff)⁻¹ * toPolyQ r.den) := by
    rw [isCoprime_mul_unit_left_left (Polynomial.isUnit_C.mpr
        (isUnit_iff_ne_zero.mpr (div_ne_zero hc0 hℓ0))) _ _,
      isCoprime_mul_unit_left_right (Polynomial.isUnit_C.mpr
        (isUnit_iff_ne_zero.mpr (inv_ne_zero hℓ0))) _ _]
    exact hND
  have hCq : algebraMap ℚ (RatFunc ℚ) ((toPolyQ r.den).leadingCoeff) ≠ 0 :=
    fun h => hℓ0 ((algebraMap ℚ (RatFunc ℚ)).injective (h.trans (map_zero _).symm))
  have hfeq : toRatFunc r
      = algebraMap ℚ[X] (RatFunc ℚ)
          (Polynomial.C (Azurite.AzRat.toRat r.factor / (toPolyQ r.den).leadingCoeff)
            * toPolyQ r.num)
        / algebraMap ℚ[X] (RatFunc ℚ)
          (Polynomial.C ((toPolyQ r.den).leadingCoeff)⁻¹ * toPolyQ r.den) := by
    rw [toRatFunc, map_mul, map_mul, RatFunc.algebraMap_C, RatFunc.algebraMap_C,
      ← algebraMapQ_eq_C, map_div₀, map_inv₀, div_mul_eq_mul_div, div_div,
      ← mul_assoc, mul_inv_cancel₀ hCq, one_mul, mul_div_assoc]
  exact num_denom_ext hmonic hcop hfeq

/-- **The Mathlib denominator of the represented function** — the monic
rescaling of the denominator image (unconditional: at `r = 0` both sides
are `1`). -/
theorem denom_toRatFunc (r : AzRationalFunction) :
    (toRatFunc r).denom
      = Polynomial.C ((toPolyQ r.den).leadingCoeff)⁻¹ * toPolyQ r.den := by
  by_cases hf : r.factor = 0
  · have hr0 : toRatFunc r = 0 := by
      rw [toRatFunc, hf, Azurite.AzRat.toRat_zero, map_zero, zero_mul]
    obtain ⟨_, hd1⟩ := r.zero_norm hf
    rw [hr0, RatFunc.denom_zero, hd1, toPolyQ_one, Polynomial.leadingCoeff_one,
      inv_one, Polynomial.C_1, one_mul]
  · exact (num_denom_aux r hf).2

/-- **The Mathlib numerator of the represented function** — the
correspondingly-rescaled numerator image (unconditional: at `r = 0` the
scalar vanishes). -/
theorem num_toRatFunc (r : AzRationalFunction) :
    (toRatFunc r).num
      = Polynomial.C (Azurite.AzRat.toRat r.factor / (toPolyQ r.den).leadingCoeff)
        * toPolyQ r.num := by
  by_cases hf : r.factor = 0
  · have hr0 : toRatFunc r = 0 := by
      rw [toRatFunc, hf, Azurite.AzRat.toRat_zero, map_zero, zero_mul]
    rw [hr0, RatFunc.num_zero, hf, Azurite.AzRat.toRat_zero, zero_div,
      Polynomial.C_0, zero_mul]
  · exact (num_denom_aux r hf).1

/-- **The `RatFunc.eval` connection**: at a non-pole, the computable
evaluator returns exactly Mathlib's evaluation of the represented rational
function. -/
theorem toRat_evalAzRat_eq_ratFuncEval (r : AzRationalFunction) (x v : AzRat)
    (h : r.evalAzRat x = some v) :
    Azurite.AzRat.toRat v
      = RatFunc.eval (RingHom.id ℚ) (Azurite.AzRat.toRat x) (toRatFunc r) := by
  have hℓ0 : (toPolyQ r.den).leadingCoeff ≠ 0 :=
    Polynomial.leadingCoeff_ne_zero.mpr (toPolyQ_den_ne_zero r)
  have heval : RatFunc.eval (RingHom.id ℚ) (Azurite.AzRat.toRat x) (toRatFunc r)
      = Azurite.AzRat.toRat r.factor
        * ((toPolyQ r.num).eval (Azurite.AzRat.toRat x)
            / (toPolyQ r.den).eval (Azurite.AzRat.toRat x)) := by
    rw [RatFunc.eval, num_toRatFunc, denom_toRatFunc]
    show (Polynomial.C (Azurite.AzRat.toRat r.factor / (toPolyQ r.den).leadingCoeff)
          * toPolyQ r.num).eval (Azurite.AzRat.toRat x)
        / (Polynomial.C ((toPolyQ r.den).leadingCoeff)⁻¹ * toPolyQ r.den).eval
            (Azurite.AzRat.toRat x) = _
    rw [Polynomial.eval_mul, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_C,
      div_mul_eq_mul_div, div_div, ← mul_assoc, mul_inv_cancel₀ hℓ0, one_mul,
      mul_div_assoc]
  rw [heval]
  exact toRat_evalAzRat_rf r x v h

/-- **Pole alignment**: the computable evaluator returns `none` exactly at
the roots of Mathlib's (monic) denominator. -/
theorem evalAzRat_eq_none_iff_denom (r : AzRationalFunction) (x : AzRat) :
    r.evalAzRat x = none
      ↔ ((toRatFunc r).denom).eval (Azurite.AzRat.toRat x) = 0 := by
  rw [evalAzRat_eq_none_iff, denom_toRatFunc, Polynomial.eval_mul, Polynomial.eval_C]
  constructor
  · intro h0
    rw [h0, mul_zero]
  · intro h0
    rcases mul_eq_zero.mp h0 with h1 | h1
    · exact absurd h1 (inv_ne_zero (Polynomial.leadingCoeff_ne_zero.mpr
        (toPolyQ_den_ne_zero r)))
    · exact h1

/-! ### `signTop` against the Mathlib numerator -/

private theorem leadingCoeff_toPolyQ (p : Azurite.AzPolynomial AzInt) :
    (toPolyQ p).leadingCoeff = ((p.leadingCoeff).toInt : ℚ) := by
  rw [toPolyQ_eq, Polynomial.leadingCoeff, Polynomial.natDegree_map_eq_of_injective
    hκinj, Polynomial.coeff_map, ← Polynomial.leadingCoeff, leadingCoeff_intPoly]
  rfl

private theorem toPolyQ_num_lc_pos (r : AzRationalFunction) :
    0 < (toPolyQ r.num).leadingCoeff := by
  rw [leadingCoeff_toPolyQ]
  have h := r.num_lc_pos
  rw [Azurite.AzInt.lt_iff_toInt_lt, toInt_zero] at h
  exact_mod_cast h

private theorem toPolyQ_den_lc_pos (r : AzRationalFunction) :
    0 < (toPolyQ r.den).leadingCoeff := by
  rw [leadingCoeff_toPolyQ]
  have h := r.den_lc_pos
  rw [Azurite.AzInt.lt_iff_toInt_lt, toInt_zero] at h
  exact_mod_cast h

/-- **`signTop` against Mathlib, positive case**: `signTop r = 1` exactly
when the Mathlib numerator's leading coefficient is positive (the monic
denominator makes the numerator carry the asymptotic sign). -/
theorem signTop_eq_one_iff_num (r : AzRationalFunction) :
    signTop r = 1 ↔ 0 < (toRatFunc r).num.leadingCoeff := by
  have hlcpos := toPolyQ_num_lc_pos r
  have hℓpos := toPolyQ_den_lc_pos r
  rw [signTop_eq_one_iff, num_toRatFunc, Polynomial.leadingCoeff_mul,
    Polynomial.leadingCoeff_C]
  constructor
  · intro h
    exact mul_pos (div_pos h hℓpos) hlcpos
  · intro h
    rcases mul_pos_iff.mp h with ⟨h1, _⟩ | ⟨_, h2⟩
    · rcases div_pos_iff.mp h1 with ⟨hc, _⟩ | ⟨_, hℓ⟩
      · exact hc
      · exact absurd hℓpos (by linarith)
    · exact absurd hlcpos (by linarith)

/-- **`signTop` against Mathlib, negative case**. -/
theorem signTop_eq_neg_one_iff_num (r : AzRationalFunction) :
    signTop r = -1 ↔ (toRatFunc r).num.leadingCoeff < 0 := by
  have hlcpos := toPolyQ_num_lc_pos r
  have hℓpos := toPolyQ_den_lc_pos r
  rw [signTop_eq_neg_one_iff, num_toRatFunc, Polynomial.leadingCoeff_mul,
    Polynomial.leadingCoeff_C]
  constructor
  · intro h
    exact mul_neg_of_neg_of_pos (div_neg_of_neg_of_pos h hℓpos) hlcpos
  · intro h
    rcases mul_neg_iff.mp h with ⟨_, h2⟩ | ⟨h1, _⟩
    · exact absurd hlcpos (by linarith)
    · rcases div_neg_iff.mp h1 with ⟨_, hℓ⟩ | ⟨hc, _⟩
      · exact absurd hℓpos (by linarith)
      · exact hc

/-- **`signTop` against Mathlib, zero case**. -/
theorem signTop_eq_zero_iff_num (r : AzRationalFunction) :
    signTop r = 0 ↔ (toRatFunc r).num.leadingCoeff = 0 := by
  rw [signTop_eq_zero_iff, Polynomial.leadingCoeff_eq_zero, RatFunc.num_eq_zero_iff]
  constructor
  · intro h
    rw [h, toRatFunc_zero]
  · intro h
    apply toRatFunc_injective
    rw [h, toRatFunc_zero]

end Azurite.AzRationalFunction
