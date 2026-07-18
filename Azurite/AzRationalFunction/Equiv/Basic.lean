import Azurite.AzRationalFunction.Basic
import Azurite.AzPolynomial.Equiv.GcdInt
import Azurite.AzPolynomial.Equiv.Predicates
import Azurite.AzRat.Equiv.Basic
import Azurite.AzRat.Equiv.Construct
import Azurite.AzRat.Equiv.Conversion
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.RingTheory.Localization.Integral

/-!
# The rational function represented by an `AzRationalFunction`

The semantic anchor for the factored canonical form: `toRatFunc r` is the
element `factor · num / den` of `ℚ(x)` (Mathlib's `RatFunc ℚ`), through the
`AzInt → ℤ → ℚ` coefficient embedding. Canonicity (injectivity of
`toRatFunc`), correctness of `ofNumDen` and the conversions, and the
equivalence with `RatFunc ℚ` build on this.
-/

namespace Azurite.AzRationalFunction

open Polynomial

/-- The `ℚ[x]` image of a polynomial part. -/
noncomputable def toPolyQ (p : Azurite.AzPolynomial AzInt) : ℚ[X] :=
  (AzPolynomial.toPoly p).map ((Int.castRingHom ℚ).comp AzInt.toIntRingHom)

/-- **The represented rational function**: `factor · num / den` in `ℚ(x)`. -/
noncomputable def toRatFunc (r : AzRationalFunction) : RatFunc ℚ :=
  algebraMap ℚ (RatFunc ℚ) (Azurite.AzRat.toRat r.factor)
    * (algebraMap ℚ[X] (RatFunc ℚ) (toPolyQ r.num)
        / algebraMap ℚ[X] (RatFunc ℚ) (toPolyQ r.den))

/-- The numerator part's image is nonzero. -/
theorem toPolyQ_num_ne_zero (r : AzRationalFunction) : toPolyQ r.num ≠ 0 := by
  rw [toPolyQ, Ne, Polynomial.map_eq_zero_iff
    (fun a b h => Azurite.AzInt.ringEquivInt.injective (by
      have := Int.cast_injective (α := ℚ) h
      simpa using this))]
  intro h
  exact r.num_ne_zero (toPoly_inj.mp (h.trans toPoly_zero.symm))

/-- The denominator part's image is nonzero. -/
theorem toPolyQ_den_ne_zero (r : AzRationalFunction) : toPolyQ r.den ≠ 0 := by
  rw [toPolyQ, Ne, Polynomial.map_eq_zero_iff
    (fun a b h => Azurite.AzInt.ringEquivInt.injective (by
      have := Int.cast_injective (α := ℚ) h
      simpa using this))]
  intro h
  exact r.den_ne_zero (toPoly_inj.mp (h.trans toPoly_zero.symm))

/-! ### Coefficient-map bridges (`AzInt → ℤ → ℚ`) -/

private theorem hιinj : Function.Injective AzInt.toIntRingHom :=
  fun a b h => Azurite.AzInt.ringEquivInt.injective (by simpa using h)

private theorem hκinj : Function.Injective (Int.castRingHom ℚ) := Int.cast_injective

/-- The fused `ℚ[X]` image factors through the `ℤ[X]` image. -/
private theorem toPolyQ_eq (p : Azurite.AzPolynomial AzInt) :
    toPolyQ p
      = ((AzPolynomial.toPoly p).map AzInt.toIntRingHom).map (Int.castRingHom ℚ) := by
  rw [toPolyQ, Polynomial.map_map]

private theorem intPoly_ne_zero {p : Azurite.AzPolynomial AzInt} (hp : p ≠ 0) :
    (AzPolynomial.toPoly p).map AzInt.toIntRingHom ≠ 0 := by
  rw [Ne, Polynomial.map_eq_zero_iff hιinj]
  exact AzPolynomial.toPoly_ne_zero hp

private theorem toPolyQ_one : toPolyQ (1 : Azurite.AzPolynomial AzInt) = 1 := by
  rw [toPolyQ, toPoly_one, Polynomial.map_one]

/-- Leading coefficient of the `ℤ[X]` image. -/
private theorem leadingCoeff_intPoly (p : Azurite.AzPolynomial AzInt) :
    ((AzPolynomial.toPoly p).map AzInt.toIntRingHom).leadingCoeff
      = p.leadingCoeff.toInt := by
  rw [Polynomial.leadingCoeff, Polynomial.natDegree_map_eq_of_injective hιinj,
    Polynomial.coeff_map, ← Polynomial.leadingCoeff, leadingCoeff_toPoly]
  rfl

private theorem toInt_ne_zero {z : AzInt} (hz : z ≠ 0) : z.toInt ≠ 0 :=
  fun h => hz (Azurite.AzInt.ringEquivInt.injective (by simpa using h))

private theorem toInt_zero : (0 : AzInt).toInt = 0 := rfl

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

/-- A primitive part (in the computable sense) is a primitive `ℤ[X]` polynomial. -/
private theorem isPrimitive_intPoly {p : Azurite.AzPolynomial AzInt} (h : p.content = 1) :
    ((AzPolynomial.toPoly p).map AzInt.toIntRingHom).IsPrimitive := by
  rw [Polynomial.isPrimitive_iff_content_eq_one, Azurite.AzPolynomial.content_toPoly, h]
  rfl

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

/-- Ring homs out of `ℚ` are unique, so the ambient `algebraMap ℚ (RatFunc ℚ)`
agrees with `RatFunc.C` whatever `Algebra ℚ (RatFunc ℚ)` instance is in play. -/
private theorem algebraMapQ_eq_C :
    algebraMap ℚ (RatFunc ℚ) = (RatFunc.C : ℚ →+* RatFunc ℚ) :=
  RingHom.ext_rat _ _

/-! ### Gauss descent: primitive models of `ℚ[X]` polynomials -/

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
        h1).trans T.primPart_dvd
  have hE'unit : IsUnit E' :=
    isUnit_of_dvd_unit
      (dvd_gcd (hdvd A (EuclideanDomain.gcd_dvd_left _ _))
        (hdvd B (EuclideanDomain.gcd_dvd_right _ _))) h
  have h2 : IsUnit (E'.map (Int.castRingHom ℚ)) := by
    have h3 := hE'unit.map (Polynomial.mapRingHom (Int.castRingHom ℚ))
    simpa using h3
  exact hassoc.isUnit h2

/-- Primitive positive `ℤ[X]` polynomials associated over `ℚ` are equal. -/
private theorem intPoly_eq_of_assoc {A B : ℤ[X]} (hA : A.IsPrimitive) (hB : B.IsPrimitive)
    (hlcA : 0 < A.leadingCoeff) (hlcB : 0 < B.leadingCoeff)
    (h : Associated (A.map (Int.castRingHom ℚ)) (B.map (Int.castRingHom ℚ))) : A = B := by
  have hAB : A ∣ B := hA.dvd_of_fraction_map_dvd_fraction_map (K := ℚ) h.dvd
  have hBA : B ∣ A := hB.dvd_of_fraction_map_dvd_fraction_map (K := ℚ) h.symm.dvd
  obtain ⟨u, hu⟩ := associated_of_dvd_dvd hAB hBA
  obtain ⟨w, hw_unit, hwC⟩ := Polynomial.isUnit_iff.mp u.isUnit
  have hlcu := congrArg Polynomial.leadingCoeff hu
  rw [Polynomial.leadingCoeff_mul, ← hwC, Polynomial.leadingCoeff_C] at hlcu
  rcases Int.isUnit_iff.mp hw_unit with hw1 | hwm1
  · rw [← hu, ← hwC, hw1, Polynomial.C_1, mul_one]
  · exfalso
    rw [hwm1] at hlcu
    omega

/-- Multiplication by a nonzero constant is an association in `ℚ[X]`. -/
private theorem assoc_C_mul {c : ℚ} (hc : c ≠ 0) (p : ℚ[X]) :
    Associated (Polynomial.C c * p) p := by
  have hu : IsUnit (Polynomial.C c : ℚ[X]) :=
    Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr hc)
  exact Associated.symm ⟨hu.unit, by rw [IsUnit.unit_spec, mul_comm]⟩

/-- Nonzero constants are coprime with everything. -/
private theorem isCoprime_C_right {c : ℚ} (hc : c ≠ 0) (p : ℚ[X]) :
    IsCoprime p (Polynomial.C c) :=
  ⟨0, Polynomial.C c⁻¹, by
    rw [zero_mul, zero_add, ← Polynomial.C_mul, inv_mul_cancel₀ hc, Polynomial.C_1]⟩

/-- Nonzero normalized `ℤ[X]` polynomials have positive leading coefficient. -/
private theorem lc_pos_of_normalized {p : ℤ[X]} (hp : p ≠ 0)
    (hnorm : _root_.normalize p = p) : 0 < p.leadingCoeff := by
  have h1 : p.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hp
  have h2 := Polynomial.leadingCoeff_normalize p
  rw [hnorm, ← Int.abs_eq_normalize] at h2
  have h3 : 0 ≤ p.leadingCoeff := h2 ▸ abs_nonneg _
  exact lt_of_le_of_ne h3 (Ne.symm h1)

/-! ### The `primPos` specification -/

/-- **The `primPos` specification** (mirror of the private lemma in
`Equiv/GcdInt.lean`): the signed content times the primitive positive part
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

/-- The `ofNumDen` scalar in its `primPos`-matching (Boolean-sign) form. -/
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

/-! ### The normalizing constructor's gcd and cofactors in `ℤ[X]` -/

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

/-! ### The constants -/

theorem toRatFunc_zero : toRatFunc 0 = 0 := by
  rw [toRatFunc, show (0 : AzRationalFunction).factor = 0 from rfl,
    Azurite.AzRat.toRat_zero, map_zero, zero_mul]

theorem toRatFunc_one : toRatFunc 1 = 1 := by
  rw [toRatFunc, show (1 : AzRationalFunction).factor = 1 from rfl,
    Azurite.AzRat.toRat_one, map_one, one_mul,
    show (1 : AzRationalFunction).num = 1 from rfl,
    show (1 : AzRationalFunction).den = 1 from rfl, toPolyQ_one, map_one, div_one]

/-! ### Canonicity: `toRatFunc` is injective -/

/-- **Canonicity.** The factored canonical representation is unique: two
`AzRationalFunction`s representing the same rational function are equal. -/
theorem toRatFunc_injective : Function.Injective toRatFunc := by
  intro r s h
  have hφNr := RatFunc.algebraMap_ne_zero (toPolyQ_num_ne_zero r)
  have hφDr := RatFunc.algebraMap_ne_zero (toPolyQ_den_ne_zero r)
  have hφNs := RatFunc.algebraMap_ne_zero (toPolyQ_num_ne_zero s)
  have hφDs := RatFunc.algebraMap_ne_zero (toPolyQ_den_ne_zero s)
  have hQr : algebraMap ℚ[X] (RatFunc ℚ) (toPolyQ r.num)
      / algebraMap ℚ[X] (RatFunc ℚ) (toPolyQ r.den) ≠ 0 := div_ne_zero hφNr hφDr
  have hQs : algebraMap ℚ[X] (RatFunc ℚ) (toPolyQ s.num)
      / algebraMap ℚ[X] (RatFunc ℚ) (toPolyQ s.den) ≠ 0 := div_ne_zero hφNs hφDs
  have halgQinj : Function.Injective (algebraMap ℚ (RatFunc ℚ)) :=
    (algebraMap ℚ (RatFunc ℚ)).injective
  simp only [toRatFunc] at h
  -- zero scalar: both sides are the canonical zero
  by_cases hf : Azurite.AzRat.toRat r.factor = 0
  · have h0 : algebraMap ℚ (RatFunc ℚ) (Azurite.AzRat.toRat s.factor)
        * (algebraMap ℚ[X] (RatFunc ℚ) (toPolyQ s.num)
            / algebraMap ℚ[X] (RatFunc ℚ) (toPolyQ s.den)) = 0 := by
      rw [← h, hf, map_zero, zero_mul]
    have h1 : Azurite.AzRat.toRat s.factor = 0 := by
      rcases mul_eq_zero.mp h0 with h2 | h2
      · exact halgQinj (by rw [h2, map_zero])
      · exact absurd h2 hQs
    have hfr : r.factor = 0 :=
      Azurite.AzRat.toRat_injective (by rw [hf, Azurite.AzRat.toRat_zero])
    have hfs : s.factor = 0 :=
      Azurite.AzRat.toRat_injective (by rw [h1, Azurite.AzRat.toRat_zero])
    obtain ⟨hrn, hrd⟩ := r.zero_norm hfr
    obtain ⟨hsn, hsd⟩ := s.zero_norm hfs
    exact ext (hfr.trans hfs.symm) (hrn.trans hsn.symm) (hrd.trans hsd.symm)
  have hfs : Azurite.AzRat.toRat s.factor ≠ 0 := by
    intro h0
    apply hf
    have h1 : algebraMap ℚ (RatFunc ℚ) (Azurite.AzRat.toRat r.factor)
        * (algebraMap ℚ[X] (RatFunc ℚ) (toPolyQ r.num)
            / algebraMap ℚ[X] (RatFunc ℚ) (toPolyQ r.den)) = 0 := by
      rw [h, h0, map_zero, zero_mul]
    rcases mul_eq_zero.mp h1 with h2 | h2
    · exact halgQinj (by rw [h2, map_zero])
    · exact absurd h2 hQr
  -- nonzero scalars: the cross identity in `ℚ[X]`, with the scalars as constants
  rw [algebraMapQ_eq_C, ← RatFunc.algebraMap_C, ← RatFunc.algebraMap_C,
    ← mul_div_assoc, ← mul_div_assoc, ← map_mul, ← map_mul,
    div_eq_div_iff hφDr hφDs, ← map_mul, ← map_mul] at h
  have hcross : Polynomial.C (Azurite.AzRat.toRat r.factor) * toPolyQ r.num
        * toPolyQ s.den
      = Polynomial.C (Azurite.AzRat.toRat s.factor) * toPolyQ s.num * toPolyQ r.den :=
    RatFunc.algebraMap_injective ℚ h
  have hcopr : IsCoprime (toPolyQ r.num) (toPolyQ r.den) :=
    (Azurite.AzPolynomial.coprime_int_iff r.num r.den).mp r.reduced
  have hcops : IsCoprime (toPolyQ s.num) (toPolyQ s.den) :=
    (Azurite.AzPolynomial.coprime_int_iff s.num s.den).mp s.reduced
  -- denominators are associated over `ℚ[X]`, hence equal
  have hdvd_rs : toPolyQ r.den ∣ toPolyQ s.den := by
    have h1 : toPolyQ r.den ∣ Polynomial.C (Azurite.AzRat.toRat r.factor)
        * toPolyQ r.num * toPolyQ s.den := by
      rw [hcross]
      exact dvd_mul_left _ _
    exact ((isCoprime_C_right hf (toPolyQ r.den)).mul_right
      hcopr.symm).dvd_of_dvd_mul_left h1
  have hdvd_sr : toPolyQ s.den ∣ toPolyQ r.den := by
    have h1 : toPolyQ s.den ∣ Polynomial.C (Azurite.AzRat.toRat s.factor)
        * toPolyQ s.num * toPolyQ r.den := by
      rw [← hcross]
      exact dvd_mul_left _ _
    exact ((isCoprime_C_right hfs (toPolyQ s.den)).mul_right
      hcops.symm).dvd_of_dvd_mul_left h1
  have hdeneq : r.den = s.den := by
    apply toPoly_inj.mp
    apply Polynomial.map_injective _ hιinj
    apply intPoly_eq_of_assoc (isPrimitive_intPoly r.den_content)
      (isPrimitive_intPoly s.den_content) (lcPos_int r.den_lc_pos)
      (lcPos_int s.den_lc_pos)
    have h1 := associated_of_dvd_dvd hdvd_rs hdvd_sr
    rwa [toPolyQ_eq, toPolyQ_eq] at h1
  -- cancel the denominator, then match numerators and scalars
  have hDeq : toPolyQ r.den = toPolyQ s.den := by rw [hdeneq]
  rw [← hDeq] at hcross
  have heq : Polynomial.C (Azurite.AzRat.toRat r.factor) * toPolyQ r.num
      = Polynomial.C (Azurite.AzRat.toRat s.factor) * toPolyQ s.num :=
    mul_right_cancel₀ (toPolyQ_den_ne_zero r) hcross
  have hnumeq : r.num = s.num := by
    apply toPoly_inj.mp
    apply Polynomial.map_injective _ hιinj
    apply intPoly_eq_of_assoc (isPrimitive_intPoly r.num_content)
      (isPrimitive_intPoly s.num_content) (lcPos_int r.num_lc_pos)
      (lcPos_int s.num_lc_pos)
    have h1 : Associated (toPolyQ r.num) (toPolyQ s.num) := by
      have h2 := (assoc_C_mul hf (toPolyQ r.num)).symm
      rw [heq] at h2
      exact h2.trans (assoc_C_mul hfs (toPolyQ s.num))
    rwa [toPolyQ_eq, toPolyQ_eq] at h1
  have hfaceq : r.factor = s.factor := by
    apply Azurite.AzRat.toRat_injective
    apply Polynomial.C_injective (R := ℚ)
    have h1 := heq
    rw [hnumeq] at h1
    exact mul_right_cancel₀ (toPolyQ_num_ne_zero s) h1
  exact ext hfaceq hnumeq hdeneq

/-! ### Full correctness of the normalizing constructor -/

/-- Resolve `ofNumDen` once the guard conjuncts are known to hold (so the
fallback `0` branch is skipped). -/
private theorem ofNumDen_eq_of_guard (n d : Azurite.AzPolynomial AzInt)
    (hnd : ¬(n = 0 ∨ d = 0))
    (h1 : (Azurite.AzPolynomial.exactDivQuoRem (Azurite.AzPolynomial.primPos n)
        (Azurite.AzPolynomial.gcdNormalizedInt (Azurite.AzPolynomial.primPos n)
          (Azurite.AzPolynomial.primPos d))).1.content = 1)
    (h2 : (Azurite.AzPolynomial.exactDivQuoRem (Azurite.AzPolynomial.primPos d)
        (Azurite.AzPolynomial.gcdNormalizedInt (Azurite.AzPolynomial.primPos n)
          (Azurite.AzPolynomial.primPos d))).1.content = 1)
    (h3 : (0 : AzInt) < (Azurite.AzPolynomial.exactDivQuoRem
        (Azurite.AzPolynomial.primPos n)
        (Azurite.AzPolynomial.gcdNormalizedInt (Azurite.AzPolynomial.primPos n)
          (Azurite.AzPolynomial.primPos d))).1.leadingCoeff)
    (h4 : (0 : AzInt) < (Azurite.AzPolynomial.exactDivQuoRem
        (Azurite.AzPolynomial.primPos d)
        (Azurite.AzPolynomial.gcdNormalizedInt (Azurite.AzPolynomial.primPos n)
          (Azurite.AzPolynomial.primPos d))).1.leadingCoeff)
    (h5 : Azurite.AzPolynomial.coprime
        (Azurite.AzPolynomial.exactDivQuoRem (Azurite.AzPolynomial.primPos n)
          (Azurite.AzPolynomial.gcdNormalizedInt (Azurite.AzPolynomial.primPos n)
            (Azurite.AzPolynomial.primPos d))).1
        (Azurite.AzPolynomial.exactDivQuoRem (Azurite.AzPolynomial.primPos d)
          (Azurite.AzPolynomial.gcdNormalizedInt (Azurite.AzPolynomial.primPos n)
            (Azurite.AzPolynomial.primPos d))).1 = true)
    (h6 : AzRat.ofAzInts
          (if (0 : AzInt) < n.leadingCoeff then n.content.toAzInt else -n.content.toAzInt)
          (if (0 : AzInt) < d.leadingCoeff then d.content.toAzInt else -d.content.toAzInt)
          = 0
      → (Azurite.AzPolynomial.exactDivQuoRem (Azurite.AzPolynomial.primPos n)
            (Azurite.AzPolynomial.gcdNormalizedInt (Azurite.AzPolynomial.primPos n)
              (Azurite.AzPolynomial.primPos d))).1 = 1
        ∧ (Azurite.AzPolynomial.exactDivQuoRem (Azurite.AzPolynomial.primPos d)
            (Azurite.AzPolynomial.gcdNormalizedInt (Azurite.AzPolynomial.primPos n)
              (Azurite.AzPolynomial.primPos d))).1 = 1) :
    ofNumDen n d = ⟨AzRat.ofAzInts
        (if (0 : AzInt) < n.leadingCoeff then n.content.toAzInt else -n.content.toAzInt)
        (if (0 : AzInt) < d.leadingCoeff then d.content.toAzInt else -d.content.toAzInt),
      (Azurite.AzPolynomial.exactDivQuoRem (Azurite.AzPolynomial.primPos n)
        (Azurite.AzPolynomial.gcdNormalizedInt (Azurite.AzPolynomial.primPos n)
          (Azurite.AzPolynomial.primPos d))).1,
      (Azurite.AzPolynomial.exactDivQuoRem (Azurite.AzPolynomial.primPos d)
        (Azurite.AzPolynomial.gcdNormalizedInt (Azurite.AzPolynomial.primPos n)
          (Azurite.AzPolynomial.primPos d))).1,
      h1, h2, h3, h4, h5, h6⟩ := by
  simp only [ofNumDen, if_neg hnd]
  rw [dif_pos (⟨h1, h2, h3, h4, h5, h6⟩ : _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _)]

set_option maxHeartbeats 1600000 in
/-- **Correctness of `ofNumDen`.** For a nonzero denominator, the constructor
represents exactly `n / d` — in particular its invariant checks always pass
(the fallback `0` branch is unreachable). -/
theorem toRatFunc_ofNumDen (n d : Azurite.AzPolynomial AzInt) (hd : d ≠ 0) :
    toRatFunc (ofNumDen n d)
      = algebraMap ℚ[X] (RatFunc ℚ) (toPolyQ n)
        / algebraMap ℚ[X] (RatFunc ℚ) (toPolyQ d) := by
  classical
  by_cases hn : n = 0
  · subst hn
    have h0 : ofNumDen 0 d = 0 := by rw [ofNumDen, if_pos (Or.inl rfl)]
    have hz : toPolyQ (0 : Azurite.AzPolynomial AzInt) = 0 := by
      rw [toPolyQ, toPoly_zero, Polynomial.map_zero]
    rw [h0, toRatFunc_zero, hz, map_zero, zero_div]
  have hnd : ¬(n = 0 ∨ d = 0) := fun h0 => h0.elim hn hd
  -- the primitive positive parts and their signed contents
  obtain ⟨ha0, haKey, hn₁prim, hn₁lc⟩ := primPos_spec hn
  rw [← scalar_eq hn] at ha0 haKey
  obtain ⟨hb0, hbKey, hd₁prim, hd₁lc⟩ := primPos_spec hd
  rw [← scalar_eq hd] at hb0 hbKey
  set n₁ := Azurite.AzPolynomial.primPos n with hn₁
  set d₁ := Azurite.AzPolynomial.primPos d with hd₁
  set g := Azurite.AzPolynomial.gcdNormalizedInt n₁ d₁ with hg
  set N := (Azurite.AzPolynomial.exactDivQuoRem n₁ g).1 with hN
  set D := (Azurite.AzPolynomial.exactDivQuoRem d₁ g).1 with hD
  set a := if (0 : AzInt) < n.leadingCoeff then n.content.toAzInt
    else -n.content.toAzInt with ha
  set b := if (0 : AzInt) < d.leadingCoeff then d.content.toAzInt
    else -d.content.toAzInt with hb
  -- the parts, the gcd, and the cofactors are all nonzero
  have hn₁0 : n₁ ≠ 0 := by
    intro h0
    rw [h0, toPoly_zero, Polynomial.map_zero, mul_zero] at haKey
    exact intPoly_ne_zero hn haKey.symm
  have hd₁0 : d₁ ≠ 0 := by
    intro h0
    rw [h0, toPoly_zero, Polynomial.map_zero, mul_zero] at hbKey
    exact intPoly_ne_zero hd hbKey.symm
  have hGZ : (AzPolynomial.toPoly g).map AzInt.toIntRingHom
      = GCDMonoid.gcd ((AzPolynomial.toPoly n₁).map AzInt.toIntRingHom)
          ((AzPolynomial.toPoly d₁).map AzInt.toIntRingHom) := by
    rw [hg]
    exact Azurite.AzPolynomial.map_toPoly_gcdNormalizedInt n₁ d₁
  have hg0 : g ≠ 0 := by
    intro h0
    have h1 : GCDMonoid.gcd ((AzPolynomial.toPoly n₁).map AzInt.toIntRingHom)
        ((AzPolynomial.toPoly d₁).map AzInt.toIntRingHom) = 0 := by
      rw [← hGZ, h0, toPoly_zero, Polynomial.map_zero]
    exact intPoly_ne_zero hd₁0 ((gcd_eq_zero_iff _ _).mp h1).2
  have hgZ0 : (AzPolynomial.toPoly g).map AzInt.toIntRingHom ≠ 0 :=
    intPoly_ne_zero hg0
  have hNid : (AzPolynomial.toPoly g).map AzInt.toIntRingHom
        * (AzPolynomial.toPoly N).map AzInt.toIntRingHom
      = (AzPolynomial.toPoly n₁).map AzInt.toIntRingHom := by
    rw [hN, hg]
    exact cofactor_mul n₁ d₁ (by rw [← hg]; exact hg0)
  have hcomm : Azurite.AzPolynomial.gcdNormalizedInt d₁ n₁ = g := by
    rw [hg]
    exact gcdNormalizedInt_comm n₁ d₁
  have hDid : (AzPolynomial.toPoly g).map AzInt.toIntRingHom
        * (AzPolynomial.toPoly D).map AzInt.toIntRingHom
      = (AzPolynomial.toPoly d₁).map AzInt.toIntRingHom := by
    have h1 := cofactor_mul d₁ n₁ (by rw [hcomm]; exact hg0)
    rw [hcomm] at h1
    rw [hD]
    exact h1
  have hN0 : N ≠ 0 := by
    intro h0
    rw [h0, toPoly_zero, Polynomial.map_zero, mul_zero] at hNid
    exact intPoly_ne_zero hn₁0 hNid.symm
  have hD0 : D ≠ 0 := by
    intro h0
    rw [h0, toPoly_zero, Polynomial.map_zero, mul_zero] at hDid
    exact intPoly_ne_zero hd₁0 hDid.symm
  -- the gcd is normalized: positive leading coefficient
  have hglc : 0 < ((AzPolynomial.toPoly g).map AzInt.toIntRingHom).leadingCoeff := by
    apply lc_pos_of_normalized hgZ0
    rw [hGZ]
    exact normalize_gcd _ _
  -- guard: contents of the cofactors are `1`
  have hNcont : N.content = 1 := by
    have h1 := congrArg Polynomial.content hNid
    rw [Polynomial.content_mul, Polynomial.isPrimitive_iff_content_eq_one.mp hn₁prim,
      Azurite.AzPolynomial.content_toPoly, Azurite.AzPolynomial.content_toPoly] at h1
    rcases Int.mul_eq_one_iff_eq_one_or_neg_one.mp h1 with ⟨_, h2⟩ | ⟨_, h2⟩
    · apply Azurite.AzNat.toNat_injective
      have h3 : N.content.toNat = 1 := by exact_mod_cast h2
      rw [h3]
      rfl
    · exfalso
      have h3 : (0 : ℤ) ≤ (N.content.toNat : ℤ) := Int.natCast_nonneg _
      omega
  have hDcont : D.content = 1 := by
    have h1 := congrArg Polynomial.content hDid
    rw [Polynomial.content_mul, Polynomial.isPrimitive_iff_content_eq_one.mp hd₁prim,
      Azurite.AzPolynomial.content_toPoly, Azurite.AzPolynomial.content_toPoly] at h1
    rcases Int.mul_eq_one_iff_eq_one_or_neg_one.mp h1 with ⟨_, h2⟩ | ⟨_, h2⟩
    · apply Azurite.AzNat.toNat_injective
      have h3 : D.content.toNat = 1 := by exact_mod_cast h2
      rw [h3]
      rfl
    · exfalso
      have h3 : (0 : ℤ) ≤ (D.content.toNat : ℤ) := Int.natCast_nonneg _
      omega
  -- guard: positive leading coefficients of the cofactors
  have hNlc : (0 : AzInt) < N.leadingCoeff := by
    apply lcPos_az
    have h1 := congrArg Polynomial.leadingCoeff hNid
    rw [Polynomial.leadingCoeff_mul] at h1
    nlinarith [hglc, hn₁lc, h1]
  have hDlc : (0 : AzInt) < D.leadingCoeff := by
    apply lcPos_az
    have h1 := congrArg Polynomial.leadingCoeff hDid
    rw [Polynomial.leadingCoeff_mul] at h1
    nlinarith [hglc, hd₁lc, h1]
  -- guard: coprimality of the cofactors
  have hgcd1 : GCDMonoid.gcd ((AzPolynomial.toPoly N).map AzInt.toIntRingHom)
      ((AzPolynomial.toPoly D).map AzInt.toIntRingHom) = 1 := by
    have h1 : GCDMonoid.gcd ((AzPolynomial.toPoly n₁).map AzInt.toIntRingHom)
          ((AzPolynomial.toPoly d₁).map AzInt.toIntRingHom)
        = _root_.normalize ((AzPolynomial.toPoly g).map AzInt.toIntRingHom)
          * GCDMonoid.gcd ((AzPolynomial.toPoly N).map AzInt.toIntRingHom)
              ((AzPolynomial.toPoly D).map AzInt.toIntRingHom) := by
      rw [← hNid, ← hDid]
      exact gcd_mul_left _ _ _
    have h2 : _root_.normalize ((AzPolynomial.toPoly g).map AzInt.toIntRingHom)
        = (AzPolynomial.toPoly g).map AzInt.toIntRingHom := by
      rw [hGZ]
      exact normalize_gcd _ _
    rw [h2, ← hGZ] at h1
    exact (mul_left_cancel₀ hgZ0 (by rw [mul_one]; exact h1)).symm
  have hcop : Azurite.AzPolynomial.coprime N D = true := by
    rw [Azurite.AzPolynomial.coprime_int_iff]
    have h1 := isCoprime_map_of_gcd_isUnit (intPoly_ne_zero hD0)
      (by rw [hgcd1]; exact isUnit_one)
    rwa [Polynomial.map_map, Polynomial.map_map] at h1
  -- guard: the scalar is nonzero
  have hab0 : AzRat.ofAzInts a b ≠ 0 := by
    intro h0
    have h1 := congrArg Azurite.AzRat.toRat h0
    rw [Azurite.AzRat.toRat_ofAzInts, Azurite.AzRat.toRat_zero] at h1
    rcases div_eq_zero_iff.mp h1 with h2 | h2
    · exact ha0 (by exact_mod_cast h2)
    · exact hb0 (by exact_mod_cast h2)
  -- the represented value
  have hφg0 : algebraMap ℚ[X] (RatFunc ℚ)
      (((AzPolynomial.toPoly g).map AzInt.toIntRingHom).map (Int.castRingHom ℚ)) ≠ 0 :=
    RatFunc.algebraMap_ne_zero
      (by rw [Ne, Polynomial.map_eq_zero_iff hκinj]; exact hgZ0)
  have hmain : algebraMap ℚ (RatFunc ℚ) (Azurite.AzRat.toRat (AzRat.ofAzInts a b))
        * (algebraMap ℚ[X] (RatFunc ℚ) (toPolyQ N)
            / algebraMap ℚ[X] (RatFunc ℚ) (toPolyQ D))
      = algebraMap ℚ[X] (RatFunc ℚ) (toPolyQ n)
        / algebraMap ℚ[X] (RatFunc ℚ) (toPolyQ d) := by
    have hnQ : toPolyQ n
        = ((AzPolynomial.toPoly g).map AzInt.toIntRingHom).map (Int.castRingHom ℚ)
          * (Polynomial.C ((a.toInt : ℚ)) * toPolyQ N) := by
      have h1 : (AzPolynomial.toPoly n).map AzInt.toIntRingHom
          = Polynomial.C a.toInt
            * ((AzPolynomial.toPoly g).map AzInt.toIntRingHom
              * (AzPolynomial.toPoly N).map AzInt.toIntRingHom) := by
        rw [hNid, haKey]
      rw [toPolyQ_eq n, h1, Polynomial.map_mul, Polynomial.map_mul, Polynomial.map_C,
        Int.coe_castRingHom, toPolyQ_eq N]
      ring
    have hdQ : toPolyQ d
        = ((AzPolynomial.toPoly g).map AzInt.toIntRingHom).map (Int.castRingHom ℚ)
          * (Polynomial.C ((b.toInt : ℚ)) * toPolyQ D) := by
      have h1 : (AzPolynomial.toPoly d).map AzInt.toIntRingHom
          = Polynomial.C b.toInt
            * ((AzPolynomial.toPoly g).map AzInt.toIntRingHom
              * (AzPolynomial.toPoly D).map AzInt.toIntRingHom) := by
        rw [hDid, hbKey]
      rw [toPolyQ_eq d, h1, Polynomial.map_mul, Polynomial.map_mul, Polynomial.map_C,
        Int.coe_castRingHom, toPolyQ_eq D]
      ring
    have hcancel : ∀ (c : ℚ[X]), algebraMap ℚ[X] (RatFunc ℚ) c ≠ 0 → ∀ (u v : ℚ[X]),
        algebraMap ℚ[X] (RatFunc ℚ) (c * u) / algebraMap ℚ[X] (RatFunc ℚ) (c * v)
          = algebraMap ℚ[X] (RatFunc ℚ) u / algebraMap ℚ[X] (RatFunc ℚ) v := by
      intro c hc u v
      rw [map_mul, map_mul, mul_div_mul_left _ _ hc]
    rw [hnQ, hdQ, hcancel _ hφg0, Azurite.AzRat.toRat_ofAzInts, algebraMapQ_eq_C,
      map_div₀, ← RatFunc.algebraMap_C, ← RatFunc.algebraMap_C, div_mul_div_comm,
      ← map_mul, ← map_mul]
  -- discharge the constructor's guard
  rw [ofNumDen_eq_of_guard n d hnd hNcont hDcont hNlc hDlc hcop
    (fun h0 => absurd h0 hab0)]
  show algebraMap ℚ (RatFunc ℚ) (Azurite.AzRat.toRat (AzRat.ofAzInts a b))
      * (algebraMap ℚ[X] (RatFunc ℚ) (toPolyQ N)
          / algebraMap ℚ[X] (RatFunc ℚ) (toPolyQ D)) = _
  exact hmain

/-! ### The conversions -/

theorem toRatFunc_ofAzRat (q : Azurite.AzRat) :
    toRatFunc (ofAzRat q) = algebraMap ℚ (RatFunc ℚ) (Azurite.AzRat.toRat q) := by
  rw [toRatFunc, show (ofAzRat q).num = 1 from rfl, show (ofAzRat q).den = 1 from rfl,
    toPolyQ_one, map_one, div_one, mul_one]
  rfl

theorem toRatFunc_ofAzInt (z : AzInt) :
    toRatFunc (ofAzInt z) = algebraMap ℚ (RatFunc ℚ) ((z.toInt : ℚ)) := by
  show toRatFunc (ofAzRat z.toAzRat) = _
  rw [toRatFunc_ofAzRat, Azurite.AzRat.toRat_toAzRat_int]

theorem toRatFunc_ofPolynomial (p : Azurite.AzPolynomial AzInt) :
    toRatFunc (ofPolynomial p) = algebraMap ℚ[X] (RatFunc ℚ) (toPolyQ p) := by
  show toRatFunc (ofNumDen p 1) = _
  rw [toRatFunc_ofNumDen p 1 (by decide), toPolyQ_one, map_one, div_one]

/-! ### The equivalence with `RatFunc ℚ` -/

private theorem hσinj : Function.Injective AzInt.ringEquivInt.symm.toRingHom :=
  fun _ _ h => Azurite.AzInt.ringEquivInt.symm.injective h

/-- The fused image of a pulled-back `ℤ[X]` polynomial. -/
private theorem toPolyQ_ofPoly_map (p : Polynomial ℤ) :
    toPolyQ (AzPolynomial.ofPoly (p.map AzInt.ringEquivInt.symm.toRingHom))
      = p.map (Int.castRingHom ℚ) := by
  rw [toPolyQ, toPoly_ofPoly, Polynomial.map_map]
  have hcomp : ((Int.castRingHom ℚ).comp AzInt.toIntRingHom).comp
      AzInt.ringEquivInt.symm.toRingHom = Int.castRingHom ℚ := by
    apply RingHom.ext
    intro x
    show ((AzInt.toIntRingHom (AzInt.ringEquivInt.symm.toRingHom x) : ℤ) : ℚ)
      = ((x : ℤ) : ℚ)
    rw [show AzInt.toIntRingHom (AzInt.ringEquivInt.symm.toRingHom x) = x from
      Azurite.AzInt.ringEquivInt.apply_symm_apply x]
  rw [hcomp]

/-- `toRatFunc_ofNumDen` specialized to pulled-back `ℤ[X]` inputs. -/
private theorem toRatFunc_ofNumDen_ofPoly (P Q : Polynomial ℤ) (hQ : Q ≠ 0) :
    toRatFunc (ofNumDen
        (AzPolynomial.ofPoly (P.map AzInt.ringEquivInt.symm.toRingHom))
        (AzPolynomial.ofPoly (Q.map AzInt.ringEquivInt.symm.toRingHom)))
      = algebraMap ℚ[X] (RatFunc ℚ) (P.map (Int.castRingHom ℚ))
        / algebraMap ℚ[X] (RatFunc ℚ) (Q.map (Int.castRingHom ℚ)) := by
  have hQ' : AzPolynomial.ofPoly (Q.map AzInt.ringEquivInt.symm.toRingHom)
      ≠ (0 : Azurite.AzPolynomial AzInt) := by
    intro h0
    apply hQ
    have h1 := congrArg AzPolynomial.toPoly h0
    rw [toPoly_ofPoly, toPoly_zero] at h1
    exact (Polynomial.map_eq_zero_iff hσinj).mp h1
  rw [toRatFunc_ofNumDen _ _ hQ', toPolyQ_ofPoly_map, toPolyQ_ofPoly_map]

/-- **The inverse conversion**: the canonical `AzRationalFunction` representing
a Mathlib rational function. Clear the denominators of `f.num` and `f.denom`
(cross-applying the two integer scalars so that the represented fraction is
unchanged), pull back to `AzInt` coefficients, and renormalize with
`ofNumDen`. Noncomputable — the denominator-clearing scalars are obtained by
choice (as is the coefficient pullback, mirroring `ofPoly`). -/
noncomputable def ofRatFunc (f : RatFunc ℚ) : AzRationalFunction :=
  let N : Polynomial ℤ := IsLocalization.integerNormalization (nonZeroDivisors ℤ) f.num
  let D : Polynomial ℤ := IsLocalization.integerNormalization (nonZeroDivisors ℤ) f.denom
  let b₁ : ℤ := (IsLocalization.integerNormalization_spec (nonZeroDivisors ℤ) f.num).choose
  let b₂ : ℤ :=
    (IsLocalization.integerNormalization_spec (nonZeroDivisors ℤ) f.denom).choose
  ofNumDen
    (AzPolynomial.ofPoly ((Polynomial.C b₂ * N).map AzInt.ringEquivInt.symm.toRingHom))
    (AzPolynomial.ofPoly ((Polynomial.C b₁ * D).map AzInt.ringEquivInt.symm.toRingHom))

/-- Round trip `RatFunc ℚ → AzRationalFunction → RatFunc ℚ`. -/
theorem toRatFunc_ofRatFunc (f : RatFunc ℚ) : toRatFunc (ofRatFunc f) = f := by
  obtain ⟨hmem₁, hspec₁⟩ :=
    (IsLocalization.integerNormalization_spec (nonZeroDivisors ℤ) f.num).choose_spec
  obtain ⟨hmem₂, hspec₂⟩ :=
    (IsLocalization.integerNormalization_spec (nonZeroDivisors ℤ) f.denom).choose_spec
  set N := IsLocalization.integerNormalization (nonZeroDivisors ℤ) f.num with hN
  set D := IsLocalization.integerNormalization (nonZeroDivisors ℤ) f.denom with hD
  set b₁ := (IsLocalization.integerNormalization_spec (nonZeroDivisors ℤ) f.num).choose
    with hb₁
  set b₂ := (IsLocalization.integerNormalization_spec (nonZeroDivisors ℤ) f.denom).choose
    with hb₂
  have hb₁0 : b₁ ≠ 0 := nonZeroDivisors.ne_zero hmem₁
  have hb₂0 : b₂ ≠ 0 := nonZeroDivisors.ne_zero hmem₂
  have hD0 : D ≠ 0 := by
    rw [hD, Ne, IsLocalization.integerNormalization_eq_zero_iff le_rfl]
    exact RatFunc.denom_ne_zero f
  have hden0 : Polynomial.C b₁ * D ≠ 0 :=
    mul_ne_zero (Polynomial.C_ne_zero.mpr hb₁0) hD0
  have hof : ofRatFunc f = ofNumDen
      (AzPolynomial.ofPoly ((Polynomial.C b₂ * N).map AzInt.ringEquivInt.symm.toRingHom))
      (AzPolynomial.ofPoly ((Polynomial.C b₁ * D).map AzInt.ringEquivInt.symm.toRingHom)) :=
    rfl
  rw [hof, toRatFunc_ofNumDen_ofPoly (Polynomial.C b₂ * N) (Polynomial.C b₁ * D) hden0]
  -- the scaled images, with the scalars crossed
  have hmapCmul : ∀ (c : ℤ) (p : Polynomial ℤ),
      (Polynomial.C c * p).map (Int.castRingHom ℚ)
        = Polynomial.C ((c : ℚ)) * p.map (Int.castRingHom ℚ) := by
    intro c p
    rw [Polynomial.map_mul, Polynomial.map_C]
    rfl
  have hNmap : N.map (Int.castRingHom ℚ) = Polynomial.C ((b₁ : ℚ)) * f.num := by
    rw [← algebraMap_int_eq, hspec₁, zsmul_eq_mul, ← Polynomial.C_eq_intCast]
  have hDmap : D.map (Int.castRingHom ℚ) = Polynomial.C ((b₂ : ℚ)) * f.denom := by
    rw [← algebraMap_int_eq, hspec₂, zsmul_eq_mul, ← Polynomial.C_eq_intCast]
  have hφc0 : algebraMap ℚ[X] (RatFunc ℚ) (Polynomial.C ((b₁ : ℚ) * (b₂ : ℚ))) ≠ 0 :=
    RatFunc.algebraMap_ne_zero (Polynomial.C_ne_zero.mpr
      (mul_ne_zero (Int.cast_ne_zero.mpr hb₁0) (Int.cast_ne_zero.mpr hb₂0)))
  have hcancel : ∀ (c : ℚ[X]), algebraMap ℚ[X] (RatFunc ℚ) c ≠ 0 → ∀ (u v : ℚ[X]),
      algebraMap ℚ[X] (RatFunc ℚ) (c * u) / algebraMap ℚ[X] (RatFunc ℚ) (c * v)
        = algebraMap ℚ[X] (RatFunc ℚ) u / algebraMap ℚ[X] (RatFunc ℚ) v := by
    intro c hc u v
    rw [map_mul, map_mul, mul_div_mul_left _ _ hc]
  rw [hmapCmul, hmapCmul, hNmap, hDmap, ← mul_assoc, ← mul_assoc, ← Polynomial.C_mul,
    ← Polynomial.C_mul, mul_comm ((b₂ : ℚ)) ((b₁ : ℚ)), hcancel _ hφc0,
    RatFunc.num_div_denom]

/-- Round trip `AzRationalFunction → RatFunc ℚ → AzRationalFunction`. -/
theorem ofRatFunc_toRatFunc (r : AzRationalFunction) : ofRatFunc (toRatFunc r) = r :=
  toRatFunc_injective (by rw [toRatFunc_ofRatFunc])

/-- The mathematical equivalence between `AzRationalFunction` and `RatFunc ℚ`,
bundling the two round-trips (mirroring `equivPolynomial`). -/
noncomputable def equivRatFunc : AzRationalFunction ≃ RatFunc ℚ where
  toFun := toRatFunc
  invFun := ofRatFunc
  left_inv := ofRatFunc_toRatFunc
  right_inv := toRatFunc_ofRatFunc

/-- `ofRatFunc` version: zero pulls back to the canonical zero. -/
theorem ofRatFunc_zero : ofRatFunc 0 = 0 :=
  toRatFunc_injective (by rw [toRatFunc_ofRatFunc, toRatFunc_zero])

/-- `ofRatFunc` version: one pulls back to the canonical one. -/
theorem ofRatFunc_one : ofRatFunc 1 = 1 :=
  toRatFunc_injective (by rw [toRatFunc_ofRatFunc, toRatFunc_one])

end Azurite.AzRationalFunction
