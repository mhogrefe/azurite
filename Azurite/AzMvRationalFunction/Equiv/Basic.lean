/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzMvRationalFunction.Basic
import Azurite.AzMvPolynomial.Equiv.GcdCofactor
import Azurite.AzMvPolynomial.Equiv.ContentDescent
import Azurite.AzRat.Equiv.Basic
import Azurite.AzRat.Equiv.Construct
import Azurite.AzRat.Equiv.Conversion
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Localization.Integral

/-!
# The multivariate rational function represented by an `AzMvRationalFunction`

The semantic anchor for the factored canonical form: `toMvRatFunc r` is the
element `factor · num / den` of `ℚ(x⃗) = FractionRing (MvPolynomial (Fin n) ℚ)`,
through the `AzInt → ℤ → ℚ` coefficient embedding. Mirrors the univariate
`AzRationalFunction/Equiv/Basic.lean`.
-/

namespace Azurite.AzMvRationalFunction

open Azurite.AzMvPolynomial

variable {n : ℕ} {ord : MonomialOrder}

/-- The coefficient homomorphism `AzInt → ℚ`: `ℤ`-cast after `toInt`. -/
noncomputable def coeffQ : AzInt →+* ℚ := (Int.castRingHom ℚ).comp AzInt.toIntRingHom

theorem coeffQ_injective : Function.Injective coeffQ := fun a b h =>
  Azurite.AzInt.ringEquivInt.injective (by
    have := Int.cast_injective (α := ℚ) (by simpa [coeffQ] using h)
    simpa using this)

/-- The fused `ℚ[x⃗]`-image homomorphism. -/
noncomputable def toMvPolyQHom : AzMvPolynomial n AzInt ord →+* MvPolynomial (Fin n) ℚ :=
  (MvPolynomial.map coeffQ).comp toMvPolyHom

/-- The `ℚ[x⃗]`-image of a polynomial part. -/
noncomputable def toMvPolyQ (P : AzMvPolynomial n AzInt ord) : MvPolynomial (Fin n) ℚ :=
  toMvPolyQHom P

theorem toMvPolyQ_eq_map (P : AzMvPolynomial n AzInt ord) :
    toMvPolyQ P = MvPolynomial.map coeffQ P.toMvPoly := rfl

@[simp] theorem toMvPolyQ_mul (P Q : AzMvPolynomial n AzInt ord) :
    toMvPolyQ (P * Q) = toMvPolyQ P * toMvPolyQ Q := map_mul toMvPolyQHom P Q

@[simp] theorem toMvPolyQ_one : toMvPolyQ (1 : AzMvPolynomial n AzInt ord) = 1 :=
  map_one toMvPolyQHom

@[simp] theorem toMvPolyQ_zero : toMvPolyQ (0 : AzMvPolynomial n AzInt ord) = 0 :=
  map_zero toMvPolyQHom

theorem toMvPolyQ_C (c : AzInt) :
    toMvPolyQ (AzMvPolynomial.C c : AzMvPolynomial n AzInt ord)
      = MvPolynomial.C (coeffQ c) := by
  rw [toMvPolyQ_eq_map, toMvPoly_C, MvPolynomial.map_C]

theorem toMvPolyQ_ne_zero {P : AzMvPolynomial n AzInt ord} (hP : P ≠ 0) :
    toMvPolyQ P ≠ 0 := by
  rw [toMvPolyQ_eq_map]
  intro h
  have h0 : P.toMvPoly = 0 :=
    MvPolynomial.map_injective coeffQ coeffQ_injective (by rw [h, map_zero])
  exact hP (toMvPoly_injective (h0.trans toMvPoly_zero.symm))

/-- **The represented rational function**: `factor · num / den` in `ℚ(x⃗)`. -/
noncomputable def toMvRatFunc (r : AzMvRationalFunction n ord) :
    FractionRing (MvPolynomial (Fin n) ℚ) :=
  algebraMap ℚ (FractionRing (MvPolynomial (Fin n) ℚ)) (Azurite.AzRat.toRat r.factor)
    * (algebraMap (MvPolynomial (Fin n) ℚ) (FractionRing (MvPolynomial (Fin n) ℚ))
          (toMvPolyQ r.num)
        / algebraMap (MvPolynomial (Fin n) ℚ) (FractionRing (MvPolynomial (Fin n) ℚ))
          (toMvPolyQ r.den))

theorem toMvPolyQ_num_ne_zero (r : AzMvRationalFunction n ord) :
    toMvPolyQ r.num ≠ 0 := toMvPolyQ_ne_zero (num_ne_zero r)

theorem toMvPolyQ_den_ne_zero (r : AzMvRationalFunction n ord) :
    toMvPolyQ r.den ≠ 0 := toMvPolyQ_ne_zero (den_ne_zero r)

/-! ### The scalar factor is nonzero away from `0` -/

private theorem toInt_ne_zero {z : AzInt} (hz : z ≠ 0) : z.toInt ≠ 0 :=
  fun h => hz (Azurite.AzInt.ringEquivInt.injective (by simpa using h))

/-- `ofAzInts a b ≠ 0` when both `a` and `b` are nonzero. -/
theorem ofAzInts_ne_zero {a b : AzInt} (ha : a ≠ 0) (hb : b ≠ 0) :
    AzRat.ofAzInts a b ≠ 0 := by
  intro h
  have h1 := congrArg Azurite.AzRat.toRat h
  rw [Azurite.AzRat.toRat_ofAzInts, Azurite.AzRat.toRat_zero] at h1
  rcases div_eq_zero_iff.mp h1 with h2 | h2
  · exact toInt_ne_zero ha (by exact_mod_cast h2)
  · exact toInt_ne_zero hb (by exact_mod_cast h2)

/-! ### Resolving the `ofNumDen` guard -/

section Guard

variable {num den : AzMvPolynomial n AzInt ord}

/-- The cofactor gcd, sign-normalized (as used by `ofNumDen`). -/
private noncomputable abbrev gNum (num den : AzMvPolynomial n AzInt ord) :=
  signNorm (AzMvPolynomial.gcd (primPos num) (primPos den))

/-- **Canonicity guard**: for nonzero inputs all six `ofNumDen` invariant
conjuncts hold, so the `dite` takes its `then`-branch. Assembled from the
`signNorm` cofactor facts (A/B) and the primitivity/positivity facts (6/7). -/
theorem ofNumDen_guard (hnum : num ≠ 0) (hden : den ≠ 0) :
    (Azurite.ExactDiv.exactDiv (primPos num) (gNum num den)).intContent = 1
    ∧ (Azurite.ExactDiv.exactDiv (primPos den) (gNum num den)).intContent = 1
    ∧ (0 : AzInt) < (Azurite.ExactDiv.exactDiv (primPos num) (gNum num den)).leadingCoeff
    ∧ (0 : AzInt) < (Azurite.ExactDiv.exactDiv (primPos den) (gNum num den)).leadingCoeff
    ∧ AzMvPolynomial.coprime (Azurite.ExactDiv.exactDiv (primPos num) (gNum num den))
        (Azurite.ExactDiv.exactDiv (primPos den) (gNum num den)) = true
    ∧ (AzRat.ofAzInts (signedIntContent num) (signedIntContent den) = 0 →
        Azurite.ExactDiv.exactDiv (primPos num) (gNum num den) = 1
        ∧ Azurite.ExactDiv.exactDiv (primPos den) (gNum num den) = 1) := by
  have hn₁0 : primPos num ≠ 0 := primPos_ne_zero hnum
  have hd₁0 : primPos den ≠ 0 := primPos_ne_zero hden
  have hg0 : gNum num den ≠ 0 := signNorm_ne_zero (gcd_ne_zero_left hn₁0)
  have hga : gNum num den ∣ primPos num := (signNorm_dvd _).trans (gcd_dvd_left _ _)
  have hgb : gNum num den ∣ primPos den := (signNorm_dvd _).trans (gcd_dvd_right _ _)
  have hglc : 0 < leadingCoeff (gNum num den) :=
    leadingCoeff_signNorm_pos (gcd_ne_zero_left hn₁0)
  exact ⟨intContent_exactDiv_eq_one hga hg0 (intContent_primPos hnum),
    intContent_exactDiv_eq_one hgb hg0 (intContent_primPos hden),
    leadingCoeff_exactDiv_pos hga hg0 hglc (leadingCoeff_primPos_pos hnum),
    leadingCoeff_exactDiv_pos hgb hg0 hglc (leadingCoeff_primPos_pos hden),
    coprime_exactDiv_signNorm hn₁0 hd₁0,
    fun h0 => absurd h0 (ofAzInts_ne_zero (signedIntContent_ne_zero hnum)
      (signedIntContent_ne_zero hden))⟩

theorem ofNumDen_factor (hnum : num ≠ 0) (hden : den ≠ 0) :
    (ofNumDen num den).factor
      = AzRat.ofAzInts (signedIntContent num) (signedIntContent den) := by
  rw [ofNumDen, ite_eq_right (not_or.mpr ⟨hnum, hden⟩), dite_eq_left (ofNumDen_guard hnum hden)]

theorem ofNumDen_num (hnum : num ≠ 0) (hden : den ≠ 0) :
    (ofNumDen num den).num
      = Azurite.ExactDiv.exactDiv (primPos num) (gNum num den) := by
  rw [ofNumDen, ite_eq_right (not_or.mpr ⟨hnum, hden⟩), dite_eq_left (ofNumDen_guard hnum hden)]

theorem ofNumDen_den (hnum : num ≠ 0) (hden : den ≠ 0) :
    (ofNumDen num den).den
      = Azurite.ExactDiv.exactDiv (primPos den) (gNum num den) := by
  rw [ofNumDen, ite_eq_right (not_or.mpr ⟨hnum, hden⟩), dite_eq_left (ofNumDen_guard hnum hden)]

end Guard

/-! ### Value correctness of `ofNumDen` -/

theorem toMvRatFunc_zero :
    toMvRatFunc (0 : AzMvRationalFunction n ord) = 0 := by
  rw [toMvRatFunc, show (0 : AzMvRationalFunction n ord).factor = 0 from rfl,
    Azurite.AzRat.toRat_zero, map_zero, zero_mul]

theorem algebraMapQ_C (q : ℚ) :
    algebraMap ℚ (FractionRing (MvPolynomial (Fin n) ℚ)) q
      = algebraMap (MvPolynomial (Fin n) ℚ) (FractionRing (MvPolynomial (Fin n) ℚ))
        (MvPolynomial.C q) := by
  rw [IsScalarTower.algebraMap_apply ℚ (MvPolynomial (Fin n) ℚ)
    (FractionRing (MvPolynomial (Fin n) ℚ))]
  rfl

private theorem coeffQ_toInt (a : AzInt) : coeffQ a = (a.toInt : ℚ) := rfl

/-- **Value correctness of the normalizing constructor**: `ofNumDen num den`
represents `num / den` in `ℚ(x⃗)`. -/
theorem toMvRatFunc_ofNumDen (num den : AzMvPolynomial n AzInt ord) (hden : den ≠ 0) :
    toMvRatFunc (ofNumDen num den)
      = algebraMap (MvPolynomial (Fin n) ℚ) (FractionRing (MvPolynomial (Fin n) ℚ))
          (toMvPolyQ num)
        / algebraMap (MvPolynomial (Fin n) ℚ) (FractionRing (MvPolynomial (Fin n) ℚ))
          (toMvPolyQ den) := by
  by_cases hnum : num = 0
  · subst hnum
    rw [show ofNumDen (0 : AzMvPolynomial n AzInt ord) den = 0 from by
        rw [ofNumDen, ite_eq_left (Or.inl rfl)],
      toMvRatFunc_zero, toMvPolyQ_zero, map_zero, zero_div]
  set g := gNum num den with hgdef
  set N := Azurite.ExactDiv.exactDiv (primPos num) g with hNdef
  set D := Azurite.ExactDiv.exactDiv (primPos den) g with hDdef
  set a := signedIntContent num with hadef
  set b := signedIntContent den with hbdef
  have hn₁0 : primPos num ≠ 0 := primPos_ne_zero hnum
  have hd₁0 : primPos den ≠ 0 := primPos_ne_zero hden
  have hg0 : g ≠ 0 := signNorm_ne_zero (gcd_ne_zero_left hn₁0)
  have hga : g ∣ primPos num := (signNorm_dvd _).trans (gcd_dvd_left _ _)
  have hgb : g ∣ primPos den := (signNorm_dvd _).trans (gcd_dvd_right _ _)
  have hgqFrac : algebraMap (MvPolynomial (Fin n) ℚ)
        (FractionRing (MvPolynomial (Fin n) ℚ)) (toMvPolyQ g) ≠ 0 := fun h =>
    toMvPolyQ_ne_zero hg0 (FaithfulSMul.algebraMap_injective _ _ (by rw [h, map_zero]))
  have hcancel : ∀ (u v : MvPolynomial (Fin n) ℚ),
      algebraMap (MvPolynomial (Fin n) ℚ) (FractionRing (MvPolynomial (Fin n) ℚ))
          (u * toMvPolyQ g)
        / algebraMap (MvPolynomial (Fin n) ℚ) (FractionRing (MvPolynomial (Fin n) ℚ))
          (v * toMvPolyQ g)
      = algebraMap (MvPolynomial (Fin n) ℚ) (FractionRing (MvPolynomial (Fin n) ℚ)) u
        / algebraMap (MvPolynomial (Fin n) ℚ) (FractionRing (MvPolynomial (Fin n) ℚ)) v := by
    intro u v
    rw [map_mul, map_mul, mul_div_mul_right _ _ hgqFrac]
  have hnQ : toMvPolyQ num = MvPolynomial.C (coeffQ a) * toMvPolyQ N * toMvPolyQ g := by
    have hf : num = AzMvPolynomial.C a * (N * g) := by
      rw [hNdef]
      conv_lhs => rw [← primPos_factorization num]
      rw [Azurite.ExactDiv.exactDiv_mul_self (primPos num) g hga hg0]
    rw [hf, toMvPolyQ_mul, toMvPolyQ_mul, toMvPolyQ_C]; ring
  have hdQ : toMvPolyQ den = MvPolynomial.C (coeffQ b) * toMvPolyQ D * toMvPolyQ g := by
    have hf : den = AzMvPolynomial.C b * (D * g) := by
      rw [hDdef]
      conv_lhs => rw [← primPos_factorization den]
      rw [Azurite.ExactDiv.exactDiv_mul_self (primPos den) g hgb hg0]
    rw [hf, toMvPolyQ_mul, toMvPolyQ_mul, toMvPolyQ_C]; ring
  rw [toMvRatFunc, ofNumDen_factor hnum hden, ofNumDen_num hnum hden, ofNumDen_den hnum hden]
  rw [hnQ, hdQ, hcancel]
  rw [Azurite.AzRat.toRat_ofAzInts, map_mul, map_mul, map_div₀,
    ← coeffQ_toInt, ← coeffQ_toInt, algebraMapQ_C, algebraMapQ_C, div_mul_div_comm]

/-! ### The conversions -/

theorem toMvRatFunc_one : toMvRatFunc (1 : AzMvRationalFunction n ord) = 1 := by
  rw [toMvRatFunc, show (1 : AzMvRationalFunction n ord).factor = 1 from rfl,
    show (1 : AzMvRationalFunction n ord).num = 1 from rfl,
    show (1 : AzMvRationalFunction n ord).den = 1 from rfl]
  simp only [Azurite.AzRat.toRat_one, map_one, toMvPolyQ_one, div_one, mul_one]

theorem toMvRatFunc_ofAzRat (q : AzRat) :
    toMvRatFunc (ofAzRat q : AzMvRationalFunction n ord)
      = algebraMap ℚ (FractionRing (MvPolynomial (Fin n) ℚ)) (Azurite.AzRat.toRat q) := by
  rw [toMvRatFunc, show (ofAzRat q : AzMvRationalFunction n ord).factor = q from rfl,
    show (ofAzRat q : AzMvRationalFunction n ord).num = 1 from rfl,
    show (ofAzRat q : AzMvRationalFunction n ord).den = 1 from rfl]
  simp only [toMvPolyQ_one, map_one, div_one, mul_one]

theorem toMvRatFunc_ofAzInt (z : AzInt) :
    toMvRatFunc (ofAzInt z : AzMvRationalFunction n ord)
      = algebraMap ℚ (FractionRing (MvPolynomial (Fin n) ℚ)) ((z.toInt : ℚ)) := by
  show toMvRatFunc (ofAzRat z.toAzRat) = _
  rw [toMvRatFunc_ofAzRat, Azurite.AzRat.toRat_toAzRat_int]

theorem toMvRatFunc_ofMvPolynomial (p : AzMvPolynomial n AzInt ord) :
    toMvRatFunc (ofMvPolynomial p)
      = algebraMap (MvPolynomial (Fin n) ℚ) (FractionRing (MvPolynomial (Fin n) ℚ))
          (toMvPolyQ p) := by
  show toMvRatFunc (ofNumDen p 1) = _
  rw [toMvRatFunc_ofNumDen p 1 one_ne_zero, toMvPolyQ_one, map_one, div_one]

/-! ### Canonicity (injectivity) -/

/-- `toMvPolyQ` factors through `intImg` and the `ℤ → ℚ` cast. -/
theorem toMvPolyQ_eq_map_intImg (P : AzMvPolynomial n AzInt ord) :
    toMvPolyQ P = (intImg P).map (Int.castRingHom ℚ) := by
  rw [toMvPolyQ_eq_map, intImg, ringEquivMvPolynomialInt_apply, MvPolynomial.map_map]
  rfl

/-- `toMvPolyQ` agrees with `ratImg`. -/
theorem toMvPolyQ_eq_ratImg (P : AzMvPolynomial n AzInt ord) : toMvPolyQ P = ratImg P :=
  (toMvPolyQ_eq_map_intImg P).trans (ratImg_eq_map_intImg P).symm

/-- The numerator/denominator parts are relatively prime over `ℚ[x⃗]`
(the hard multivariate-Gauss direction, via `coprime_isRelPrime`). -/
theorem isRelPrime_num_den (r : AzMvRationalFunction n ord) :
    IsRelPrime (toMvPolyQ r.num) (toMvPolyQ r.den) := by
  rw [toMvPolyQ_eq_ratImg, toMvPolyQ_eq_ratImg]
  exact AzMvPolynomial.coprime_isRelPrime r.reduced

private theorem azInt_unit_pos_eq_one {c : AzInt} (hu : IsUnit c) (hpos : 0 < c) : c = 1 := by
  have h1 : IsUnit c.toInt := hu.map Azurite.AzInt.ringEquivInt
  rw [Int.isUnit_iff] at h1
  rcases h1 with h | h
  · exact Azurite.AzInt.ringEquivInt.injective (by rw [map_one]; exact h)
  · exfalso
    rw [Azurite.AzInt.lt_iff_toInt_lt, show (0 : AzInt).toInt = 0 from rfl, h] at hpos
    exact absurd hpos (by decide)

/-- Two positive-leading polynomials that divide each other are equal. -/
theorem eq_of_dvd_dvd {P Q : AzMvPolynomial n AzInt ord}
    (hlcP : 0 < leadingCoeff P) (hlcQ : 0 < leadingCoeff Q)
    (hPQ : P ∣ Q) (hQP : Q ∣ P) : P = Q := by
  have hP0 : P ≠ 0 := by
    intro h; rw [h, show leadingCoeff (0 : AzMvPolynomial n AzInt ord) = 0 from rfl] at hlcP
    exact lt_irrefl 0 hlcP
  obtain ⟨A, hA⟩ := hPQ
  obtain ⟨B, hB⟩ := hQP
  have hAB : A * B = 1 :=
    mul_left_cancel₀ hP0 (by rw [mul_one, ← mul_assoc, ← hA, ← hB])
  have hAunit : IsUnit (toMvPoly A) := (IsUnit.of_mul_eq_one B hAB).map toMvPolyHom
  have hspec := MvPolynomial.isUnit_iff_totalDegree_of_isReduced.mp hAunit
  set c := (toMvPoly A).coeff 0 with hc
  have hcunit : IsUnit c := hspec.1
  have hcne : c ≠ 0 := hcunit.ne_zero
  have hCcne : (AzMvPolynomial.C c : AzMvPolynomial n AzInt ord) ≠ 0 := fun h =>
    hcne (MvPolynomial.C_eq_zero.mp (by rw [← toMvPoly_C, h, toMvPoly_zero]))
  have hAC : A = AzMvPolynomial.C c := by
    apply toMvPoly_injective
    rw [toMvPoly_C, MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp hspec.2]
  have hlcQeq : leadingCoeff Q = leadingCoeff P * c := by
    rw [hA, hAC, leadingCoeff_mul hP0 hCcne, leadingCoeff_C hcne]
  have hcpos : 0 < c := by
    rw [hlcQeq] at hlcQ
    exact (pos_iff_pos_of_mul_pos hlcQ).mp hlcP
  rw [hA, hAC, azInt_unit_pos_eq_one hcunit hcpos,
    show (AzMvPolynomial.C (1 : AzInt) : AzMvPolynomial n AzInt ord) = 1 from rfl, mul_one]

/-- Associate (over `ℚ[x⃗]`) primitive positive-leading parts are equal. -/
theorem eq_of_associated_toMvPolyQ {P Q : AzMvPolynomial n AzInt ord}
    (hPint : intContent P = 1) (hQint : intContent Q = 1)
    (hlcP : 0 < leadingCoeff P) (hlcQ : 0 < leadingCoeff Q)
    (hassoc : Associated (toMvPolyQ P) (toMvPolyQ Q)) : P = Q := by
  have hd1 : toMvPolyQ P ∣ toMvPolyQ Q := hassoc.dvd
  have hd2 : toMvPolyQ Q ∣ toMvPolyQ P := hassoc.symm.dvd
  rw [toMvPolyQ_eq_map_intImg P, toMvPolyQ_eq_map_intImg Q] at hd1 hd2
  exact eq_of_dvd_dvd hlcP hlcQ
    (dvd_of_map_intImg_dvd hPint hd1) (dvd_of_map_intImg_dvd hQint hd2)

/-- **Canonicity**: the factored form is unique — `toMvRatFunc` is injective. -/
theorem toMvRatFunc_injective :
    Function.Injective (toMvRatFunc (n := n) (ord := ord)) := by
  intro r s h
  have hφinj : Function.Injective
      (algebraMap (MvPolynomial (Fin n) ℚ) (FractionRing (MvPolynomial (Fin n) ℚ))) :=
    FaithfulSMul.algebraMap_injective _ _
  have hφNr := (map_ne_zero_iff _ hφinj).mpr (toMvPolyQ_num_ne_zero r)
  have hφDr := (map_ne_zero_iff _ hφinj).mpr (toMvPolyQ_den_ne_zero r)
  have hφNs := (map_ne_zero_iff _ hφinj).mpr (toMvPolyQ_num_ne_zero s)
  have hφDs := (map_ne_zero_iff _ hφinj).mpr (toMvPolyQ_den_ne_zero s)
  have halgQinj : Function.Injective (algebraMap ℚ (FractionRing (MvPolynomial (Fin n) ℚ))) :=
    (algebraMap ℚ _).injective
  have hQr := div_ne_zero hφNr hφDr
  have hQs := div_ne_zero hφNs hφDs
  simp only [toMvRatFunc] at h
  by_cases hf : Azurite.AzRat.toRat r.factor = 0
  · have h0 : algebraMap ℚ (FractionRing (MvPolynomial (Fin n) ℚ)) (Azurite.AzRat.toRat s.factor)
        * (algebraMap _ _ (toMvPolyQ s.num) / algebraMap _ _ (toMvPolyQ s.den)) = 0 := by
      rw [← h, hf, map_zero, zero_mul]
    have h1 : Azurite.AzRat.toRat s.factor = 0 := by
      rcases mul_eq_zero.mp h0 with h2 | h2
      · exact halgQinj (by rw [h2, map_zero])
      · exact absurd h2 hQs
    have hfr : r.factor = 0 := Azurite.AzRat.toRat_injective (by rw [hf, Azurite.AzRat.toRat_zero])
    have hfs : s.factor = 0 := Azurite.AzRat.toRat_injective (by rw [h1, Azurite.AzRat.toRat_zero])
    obtain ⟨hrn, hrd⟩ := r.zero_norm hfr
    obtain ⟨hsn, hsd⟩ := s.zero_norm hfs
    exact ext (hfr.trans hfs.symm) (hrn.trans hsn.symm) (hrd.trans hsd.symm)
  have hfs : Azurite.AzRat.toRat s.factor ≠ 0 := by
    intro h0
    apply hf
    have h1 : algebraMap ℚ (FractionRing (MvPolynomial (Fin n) ℚ)) (Azurite.AzRat.toRat r.factor)
        * (algebraMap _ _ (toMvPolyQ r.num) / algebraMap _ _ (toMvPolyQ r.den)) = 0 := by
      rw [h, h0, map_zero, zero_mul]
    rcases mul_eq_zero.mp h1 with h2 | h2
    · exact halgQinj (by rw [h2, map_zero])
    · exact absurd h2 hQr
  -- nonzero scalars: cross identity in `ℚ[x⃗]`
  rw [algebraMapQ_C, algebraMapQ_C] at h
  rw [← mul_div_assoc, ← mul_div_assoc] at h
  rw [← map_mul, ← map_mul] at h
  rw [div_eq_div_iff hφDr hφDs] at h
  rw [← map_mul, ← map_mul] at h
  have hcross := hφinj h
  have hCrf_unit : IsUnit (MvPolynomial.C (Azurite.AzRat.toRat r.factor)
      : MvPolynomial (Fin n) ℚ) := (isUnit_iff_ne_zero.mpr hf).map MvPolynomial.C
  have hCsf_unit : IsUnit (MvPolynomial.C (Azurite.AzRat.toRat s.factor)
      : MvPolynomial (Fin n) ℚ) := (isUnit_iff_ne_zero.mpr hfs).map MvPolynomial.C
  have hRPr : IsRelPrime (toMvPolyQ r.den)
      (MvPolynomial.C (Azurite.AzRat.toRat r.factor) * toMvPolyQ r.num) :=
    (hCrf_unit.isRelPrime_left.symm).mul_right (isRelPrime_num_den r).symm
  have hRPs : IsRelPrime (toMvPolyQ s.den)
      (MvPolynomial.C (Azurite.AzRat.toRat s.factor) * toMvPolyQ s.num) :=
    (hCsf_unit.isRelPrime_left.symm).mul_right (isRelPrime_num_den s).symm
  have hdvd_rs : toMvPolyQ r.den ∣ toMvPolyQ s.den :=
    hRPr.dvd_of_dvd_mul_left (by rw [hcross]; exact dvd_mul_left _ _)
  have hdvd_sr : toMvPolyQ s.den ∣ toMvPolyQ r.den :=
    hRPs.dvd_of_dvd_mul_left (by rw [← hcross]; exact dvd_mul_left _ _)
  have hdeneq : r.den = s.den :=
    eq_of_associated_toMvPolyQ r.den_primitive s.den_primitive r.den_lc_pos s.den_lc_pos
      (associated_of_dvd_dvd hdvd_rs hdvd_sr)
  -- cancel the denominator, match numerators
  rw [hdeneq] at hcross
  have heq : MvPolynomial.C (Azurite.AzRat.toRat r.factor) * toMvPolyQ r.num
      = MvPolynomial.C (Azurite.AzRat.toRat s.factor) * toMvPolyQ s.num :=
    mul_right_cancel₀ (toMvPolyQ_den_ne_zero s) hcross
  have hnum_assoc : Associated (toMvPolyQ r.num) (toMvPolyQ s.num) := by
    have a1 : Associated (toMvPolyQ r.num)
        (MvPolynomial.C (Azurite.AzRat.toRat r.factor) * toMvPolyQ r.num) :=
      associated_unit_mul_right _ _ hCrf_unit
    have a2 : Associated (MvPolynomial.C (Azurite.AzRat.toRat s.factor) * toMvPolyQ s.num)
        (toMvPolyQ s.num) := (associated_unit_mul_right _ _ hCsf_unit).symm
    rw [heq] at a1
    exact a1.trans a2
  have hnumeq : r.num = s.num :=
    eq_of_associated_toMvPolyQ r.num_primitive s.num_primitive r.num_lc_pos s.num_lc_pos hnum_assoc
  have hfaceq : r.factor = s.factor := by
    apply Azurite.AzRat.toRat_injective
    apply MvPolynomial.C_injective (Fin n) ℚ
    rw [hnumeq] at heq
    exact mul_right_cancel₀ (toMvPolyQ_num_ne_zero s) heq
  exact ext hfaceq hnumeq hdeneq

/-! ### Surjectivity and the equivalence -/

private theorem intImg_symm_ne_zero {A : MvPolynomial (Fin n) ℤ} (hA : A ≠ 0) :
    (AzMvPolynomial.ringEquivMvPolynomialInt (n := n) (ord := ord)).symm A ≠ 0 := by
  intro h
  apply hA
  have := congrArg AzMvPolynomial.ringEquivMvPolynomialInt h
  rwa [(AzMvPolynomial.ringEquivMvPolynomialInt).apply_symm_apply, map_zero] at this

/-- **The inverse conversion**: a canonical `AzMvRationalFunction` representing
`f ∈ ℚ(x⃗)`. Pick (via `IsLocalization.sec`) a `ℚ[x⃗]` numerator/denominator
pair for `f`, clear denominators to an integer pair (`mvClearDenom`), pull back
to `AzInt` coefficients, and renormalize with `ofNumDen`. Noncomputable — both
the `ℚ(x⃗)` representative and the denominator-clearing are obtained by choice
(a bare `FractionRing` element has no canonical numerator/denominator). -/
noncomputable def ofMvRatFunc (f : FractionRing (MvPolynomial (Fin n) ℚ)) :
    AzMvRationalFunction n ord :=
  ofNumDen
    (AzMvPolynomial.C (Azurite.AzInt.ringEquivInt.symm
        (mvClearDenom ((IsLocalization.sec (nonZeroDivisors (MvPolynomial (Fin n) ℚ)) f).2
          : MvPolynomial (Fin n) ℚ)).choose)
      * (AzMvPolynomial.ringEquivMvPolynomialInt (n := n) (ord := ord)).symm
        (mvClearDenom (IsLocalization.sec (nonZeroDivisors (MvPolynomial (Fin n) ℚ)) f).1).choose_spec.2.choose)
    (AzMvPolynomial.C (Azurite.AzInt.ringEquivInt.symm
        (mvClearDenom (IsLocalization.sec (nonZeroDivisors (MvPolynomial (Fin n) ℚ)) f).1).choose)
      * (AzMvPolynomial.ringEquivMvPolynomialInt (n := n) (ord := ord)).symm
        (mvClearDenom ((IsLocalization.sec (nonZeroDivisors (MvPolynomial (Fin n) ℚ)) f).2
          : MvPolynomial (Fin n) ℚ)).choose_spec.2.choose)

/-- **Right inverse**: `ofMvRatFunc` reconstructs its `ℚ(x⃗)` argument. -/
theorem toMvRatFunc_ofMvRatFunc (f : FractionRing (MvPolynomial (Fin n) ℚ)) :
    toMvRatFunc (ofMvRatFunc f : AzMvRationalFunction n ord) = f := by
  rw [ofMvRatFunc]
  set a := (IsLocalization.sec (nonZeroDivisors (MvPolynomial (Fin n) ℚ)) f).1 with ha_def
  set b := ((IsLocalization.sec (nonZeroDivisors (MvPolynomial (Fin n) ℚ)) f).2
    : MvPolynomial (Fin n) ℚ) with hb_def
  set ca := (mvClearDenom a).choose with hca_def
  set A := (mvClearDenom a).choose_spec.2.choose with hA_def
  set cb := (mvClearDenom b).choose with hcb_def
  set B := (mvClearDenom b).choose_spec.2.choose with hB_def
  have hca : ca ≠ 0 := (mvClearDenom a).choose_spec.1
  have hA : MvPolynomial.C (ca : ℚ) * a = A.map (Int.castRingHom ℚ) :=
    (mvClearDenom a).choose_spec.2.choose_spec
  have hcb : cb ≠ 0 := (mvClearDenom b).choose_spec.1
  have hB : MvPolynomial.C (cb : ℚ) * b = B.map (Int.castRingHom ℚ) :=
    (mvClearDenom b).choose_spec.2.choose_spec
  have hb0 : b ≠ 0 :=
    nonZeroDivisors.coe_ne_zero (IsLocalization.sec (nonZeroDivisors (MvPolynomial (Fin n) ℚ)) f).2
  have hbne : algebraMap (MvPolynomial (Fin n) ℚ) (FractionRing (MvPolynomial (Fin n) ℚ)) b ≠ 0 :=
    (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective _ _)).mpr hb0
  have hfab : f = algebraMap (MvPolynomial (Fin n) ℚ) (FractionRing (MvPolynomial (Fin n) ℚ)) a
      / algebraMap _ _ b := by
    rw [eq_div_iff hbne]
    exact IsLocalization.sec_spec (nonZeroDivisors (MvPolynomial (Fin n) ℚ)) f
  set caz := Azurite.AzInt.ringEquivInt.symm ca with hcazdef
  set cbz := Azurite.AzInt.ringEquivInt.symm cb with hcbzdef
  set Aaz := (AzMvPolynomial.ringEquivMvPolynomialInt (n := n) (ord := ord)).symm A with hAazdef
  set Baz := (AzMvPolynomial.ringEquivMvPolynomialInt (n := n) (ord := ord)).symm B with hBazdef
  have hintA : intImg Aaz = A := (AzMvPolynomial.ringEquivMvPolynomialInt).apply_symm_apply A
  have hintB : intImg Baz = B := (AzMvPolynomial.ringEquivMvPolynomialInt).apply_symm_apply B
  have hcaz : caz.toInt = ca := Azurite.AzInt.ringEquivInt.apply_symm_apply ca
  have hcbz : cbz.toInt = cb := Azurite.AzInt.ringEquivInt.apply_symm_apply cb
  have hcaQ : (ca : ℚ) ≠ 0 := by exact_mod_cast hca
  have hcbQ : (cb : ℚ) ≠ 0 := by exact_mod_cast hcb
  have hBne : B ≠ 0 := by
    intro h; rw [h, map_zero] at hB
    rcases mul_eq_zero.mp hB with h2 | h2
    · exact hcbQ (MvPolynomial.C_eq_zero.mp h2)
    · exact hb0 h2
  have hcazne : caz ≠ 0 := fun h => hca (by rw [← hcaz, h]; rfl)
  have hCcaz_ne : (AzMvPolynomial.C caz : AzMvPolynomial n AzInt ord) ≠ 0 := fun h =>
    hcazne (by
      have := congrArg toMvPoly h; rw [toMvPoly_C, toMvPoly_zero] at this
      exact MvPolynomial.C_eq_zero.mp this)
  have hden_ne : AzMvPolynomial.C caz * Baz ≠ 0 :=
    mul_ne_zero hCcaz_ne (intImg_symm_ne_zero hBne)
  have hnumQ : toMvPolyQ (AzMvPolynomial.C cbz * Aaz)
      = MvPolynomial.C (cb : ℚ) * (MvPolynomial.C (ca : ℚ) * a) := by
    rw [toMvPolyQ_mul, toMvPolyQ_C, toMvPolyQ_eq_map_intImg, hintA, ← hA, coeffQ_toInt, hcbz]
  have hdenQ : toMvPolyQ (AzMvPolynomial.C caz * Baz)
      = MvPolynomial.C (ca : ℚ) * (MvPolynomial.C (cb : ℚ) * b) := by
    rw [toMvPolyQ_mul, toMvPolyQ_C, toMvPolyQ_eq_map_intImg, hintB, ← hB, coeffQ_toInt, hcaz]
  rw [hfab, toMvRatFunc_ofNumDen _ _ hden_ne, hnumQ, hdenQ]
  have hinj : Function.Injective
      (algebraMap (MvPolynomial (Fin n) ℚ) (FractionRing (MvPolynomial (Fin n) ℚ))) :=
    FaithfulSMul.algebraMap_injective _ _
  have hpq_ne : algebraMap (MvPolynomial (Fin n) ℚ) (FractionRing (MvPolynomial (Fin n) ℚ))
        (MvPolynomial.C (ca : ℚ))
      * algebraMap (MvPolynomial (Fin n) ℚ) (FractionRing (MvPolynomial (Fin n) ℚ))
        (MvPolynomial.C (cb : ℚ)) ≠ 0 :=
    mul_ne_zero
      ((map_ne_zero_iff _ hinj).mpr (fun h => hcaQ (MvPolynomial.C_eq_zero.mp h)))
      ((map_ne_zero_iff _ hinj).mpr (fun h => hcbQ (MvPolynomial.C_eq_zero.mp h)))
  rw [map_mul, map_mul, map_mul, map_mul,
    show algebraMap (MvPolynomial (Fin n) ℚ) (FractionRing (MvPolynomial (Fin n) ℚ))
        (MvPolynomial.C (cb : ℚ))
        * (algebraMap _ _ (MvPolynomial.C (ca : ℚ)) * algebraMap _ _ a)
      = (algebraMap _ _ (MvPolynomial.C (ca : ℚ)) * algebraMap _ _ (MvPolynomial.C (cb : ℚ)))
        * algebraMap _ _ a from by ring,
    show algebraMap (MvPolynomial (Fin n) ℚ) (FractionRing (MvPolynomial (Fin n) ℚ))
        (MvPolynomial.C (ca : ℚ))
        * (algebraMap _ _ (MvPolynomial.C (cb : ℚ)) * algebraMap _ _ b)
      = (algebraMap _ _ (MvPolynomial.C (ca : ℚ)) * algebraMap _ _ (MvPolynomial.C (cb : ℚ)))
        * algebraMap _ _ b from by ring,
    mul_div_mul_left _ _ hpq_ne]

/-- **Left inverse**: `ofMvRatFunc` recovers the original representation. -/
theorem ofMvRatFunc_toMvRatFunc (r : AzMvRationalFunction n ord) :
    ofMvRatFunc (toMvRatFunc r) = r :=
  toMvRatFunc_injective (toMvRatFunc_ofMvRatFunc (toMvRatFunc r))

/-- **Surjectivity**: every element of `ℚ(x⃗)` is represented (a corollary of
the right inverse). -/
theorem toMvRatFunc_surjective :
    Function.Surjective (toMvRatFunc (n := n) (ord := ord)) :=
  fun f => ⟨ofMvRatFunc f, toMvRatFunc_ofMvRatFunc f⟩

/-- **The equivalence** `AzMvRationalFunction n ord ≃ ℚ(x⃗)`, with the explicit
inverse `ofMvRatFunc` (so `equivRatFunc.symm` computes `ofMvRatFunc`). -/
noncomputable def equivRatFunc :
    AzMvRationalFunction n ord ≃ FractionRing (MvPolynomial (Fin n) ℚ) where
  toFun := toMvRatFunc
  invFun := ofMvRatFunc
  left_inv := ofMvRatFunc_toMvRatFunc
  right_inv := toMvRatFunc_ofMvRatFunc

end Azurite.AzMvRationalFunction
