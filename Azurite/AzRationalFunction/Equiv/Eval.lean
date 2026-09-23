import Azurite.AzRationalFunction.Eval
import Azurite.AzRationalFunction.Equiv.Basic
import Azurite.AzPolynomial.Equiv.Eval
import Azurite.AzInt.Equiv.Pow
import Azurite.AzRat.Equiv.Construct
import Azurite.AzRat.Equiv.Conversion
import Azurite.AzRat.Equiv.Mul
import Azurite.AzRat.Equiv.Div

/-!
# Correctness of evaluation

`AzPolynomial.evalAzRat` computes exactly the value of the represented
`ℚ[x]` polynomial at the represented rational point
(`toRat_evalAzRat`), and the rational-function evaluators return `none`
exactly at the poles of the denominator part and otherwise the value
`factor · num(x)/den(x)` (`evalAzRat_eq_none_iff`, `toRat_evalAzRat_rf`);
the integer-point evaluator agrees with the rational one
(`evalAzInt_eq_evalAzRat`).
-/

namespace Azurite.AzPolynomial

open Polynomial

private theorem hψinj :
    Function.Injective ((Int.castRingHom ℚ).comp AzInt.toIntRingHom) := by
  intro u v h
  apply Azurite.AzInt.ringEquivInt.injective
  have h2 : ((u.toInt : ℚ)) = ((v.toInt : ℚ)) := h
  have h3 : u.toInt = v.toInt := by exact_mod_cast h2
  simpa using h3

/-- The `evalSpecial` sum, transported to `ℚ`. -/
private theorem toInt_evalSpecial (p : AzPolynomial AzInt) (a b : AzInt) :
    (((p.evalSpecial a b).toInt : ℚ))
      = ∑ k ∈ Finset.range p.coeffs.size,
          (((p.coeff k).toInt : ℚ)) * ((a.toInt : ℚ)) ^ k
            * ((b.toInt : ℚ)) ^ (p.natDegree - k) := by
  rw [Azurite.AzPolynomial.evalSpecial_eq_sum]
  have h2 := map_sum Azurite.AzInt.ringEquivInt
    (fun k => p.coeff k * a ^ k * b ^ (p.natDegree - k)) (Finset.range p.coeffs.size)
  simp only [map_mul, map_pow, Azurite.AzInt.ringEquivInt_apply] at h2
  rw [h2]
  push_cast
  rfl

/-- The rational point, as the quotient of its sign-magnitude components. -/
private theorem toRat_eq_div (x : AzRat) :
    Azurite.AzRat.toRat x
      = (((⟨x.sign, x.num, x.zero_sign⟩ : AzInt).toInt : ℚ))
        / (((⟨true, x.den, fun _ => rfl⟩ : AzInt).toInt : ℚ)) := by
  rw [← Rat.num_div_den (Azurite.AzRat.toRat x)]
  have hnum : (Azurite.AzRat.toRat x).num
      = (⟨x.sign, x.num, x.zero_sign⟩ : AzInt).toInt := rfl
  have hden : (((Azurite.AzRat.toRat x).den : ℤ))
      = (⟨true, x.den, fun _ => rfl⟩ : AzInt).toInt := rfl
  rw [hnum, ← hden]
  norm_cast

/-- The denominator component of the point is nonzero (as a rational). -/
private theorem den_component_ne_zero (x : AzRat) :
    (((⟨true, x.den, fun _ => rfl⟩ : AzInt).toInt : ℚ)) ≠ 0 := by
  rw [show (⟨true, x.den, fun _ => rfl⟩ : AzInt).toInt = (x.den.toNat : ℤ) from rfl]
  have h1 : x.den.toNat ≠ 0 := fun h =>
    x.den_nz (Azurite.AzNat.toNat_injective (by rw [h]; rfl))
  exact_mod_cast (show ((x.den.toNat : ℤ)) ≠ 0 by omega)

/-- **Correctness of `evalAzRat`**: the homogenized integer Horner scheme
computes the value of the represented `ℚ[x]` polynomial at the represented
point. -/
theorem toRat_evalAzRat (p : AzPolynomial AzInt) (x : AzRat) :
    Azurite.AzRat.toRat (AzPolynomial.evalAzRat p x)
      = ((AzPolynomial.toPoly p).map
          ((Int.castRingHom ℚ).comp AzInt.toIntRingHom)).eval
          (Azurite.AzRat.toRat x) := by
  have hb := den_component_ne_zero x
  have hunfold : AzPolynomial.evalAzRat p x
      = AzRat.ofAzInts
          (p.evalSpecial ⟨x.sign, x.num, x.zero_sign⟩ ⟨true, x.den, fun _ => rfl⟩)
          ((⟨true, x.den, fun _ => rfl⟩ : AzInt).pow (p.coeffs.size - 1)) := rfl
  rw [hunfold, Azurite.AzRat.toRat_ofAzInts, Azurite.AzInt.toInt_pow, toRat_eq_div x,
    toInt_evalSpecial]
  push_cast
  by_cases hp : p.coeffs.size = 0
  · -- the zero polynomial: empty sum over an empty coefficient array
    have hpz : p = 0 :=
      AzPolynomial.ext (by rw [Array.size_eq_zero_iff.mp hp]; rfl)
    rw [hp, hpz, Finset.range_zero, Finset.sum_empty, toPoly_zero, Polynomial.map_zero,
      Polynomial.eval_zero, zero_div]
  · -- nonzero: `size = natDegree + 1`, divide the homogenized sum through
    have hsize : p.coeffs.size - 1 = p.natDegree := rfl
    have hsize2 : p.coeffs.size = p.natDegree + 1 := by omega
    rw [hsize, hsize2, Finset.sum_div, Polynomial.eval_eq_sum_range,
      show ((AzPolynomial.toPoly p).map
          ((Int.castRingHom ℚ).comp AzInt.toIntRingHom)).natDegree = p.natDegree from by
        rw [Polynomial.natDegree_map_eq_of_injective hψinj,
          AzPolynomial.natDegree_toPoly]]
    apply Finset.sum_congr rfl
    intro k hk
    rw [Finset.mem_range] at hk
    rw [Polynomial.coeff_map, coeff_toPoly_eq,
      show ((Int.castRingHom ℚ).comp AzInt.toIntRingHom) (p.coeff k)
        = (((p.coeff k).toInt : ℚ)) from rfl,
      div_pow, pow_sub₀ _ hb (by omega : k ≤ p.natDegree)]
    field_simp

end Azurite.AzPolynomial

namespace Azurite.AzRationalFunction

open Polynomial
open Azurite.AzPolynomial (toRat_evalAzRat)

/-- `evalAzRat` returns `none` exactly at the poles of the denominator part. -/
theorem evalAzRat_eq_none_iff (r : AzRationalFunction) (x : AzRat) :
    r.evalAzRat x = none
      ↔ (toPolyQ r.den).eval (Azurite.AzRat.toRat x) = 0 := by
  have hval : (toPolyQ r.den).eval (Azurite.AzRat.toRat x)
      = Azurite.AzRat.toRat (AzPolynomial.evalAzRat r.den x) := by
    rw [toRat_evalAzRat, toPolyQ]
  rw [evalAzRat, hval]
  by_cases h : AzPolynomial.evalAzRat r.den x = 0
  · rw [ite_eq_left h, h, Azurite.AzRat.toRat_zero]
    simp
  · rw [ite_eq_right h]
    simp only [reduceCtorEq, false_iff]
    intro h0
    exact h (Azurite.AzRat.toRat_injective (by rw [h0, Azurite.AzRat.toRat_zero]))

/-- **Correctness of `evalAzRat`** at a non-pole: the value is
`factor · num(x)/den(x)`. -/
theorem toRat_evalAzRat_rf (r : AzRationalFunction) (x : AzRat) (v : AzRat)
    (h : r.evalAzRat x = some v) :
    Azurite.AzRat.toRat v
      = Azurite.AzRat.toRat r.factor
          * ((toPolyQ r.num).eval (Azurite.AzRat.toRat x)
              / (toPolyQ r.den).eval (Azurite.AzRat.toRat x)) := by
  rw [evalAzRat] at h
  by_cases hd : AzPolynomial.evalAzRat r.den x = 0
  · rw [ite_eq_left hd] at h
    exact absurd h (by simp)
  · rw [ite_eq_right hd, Option.some_inj] at h
    rw [← h, Azurite.AzRat.toRat_mul, Azurite.AzRat.toRat_div, toRat_evalAzRat,
      toRat_evalAzRat, toPolyQ, toPolyQ]

/-- The integer-point evaluator agrees with the rational-point one. -/
theorem evalAzInt_eq_evalAzRat (r : AzRationalFunction) (z : AzInt) :
    r.evalAzInt z = r.evalAzRat z.toAzRat := by
  -- both zero tests and both values coincide through `toRat`
  have hbridge : ∀ p : Azurite.AzPolynomial AzInt,
      Azurite.AzRat.toRat (AzPolynomial.evalAzRat p z.toAzRat)
        = (((AzPolynomial.eval p z).toInt : ℚ)) := by
    intro p
    rw [toRat_evalAzRat, Azurite.AzRat.toRat_toAzRat_int,
      show ((z.toInt : ℚ)) = ((Int.castRingHom ℚ).comp AzInt.toIntRingHom) z from rfl,
      Polynomial.eval_map, Polynomial.eval₂_at_apply,
      Azurite.AzPolynomial.eval_toPoly]
    rfl
  have hzero : AzPolynomial.eval r.den z = 0
      ↔ AzPolynomial.evalAzRat r.den z.toAzRat = 0 := by
    constructor
    · intro h0
      apply Azurite.AzRat.toRat_injective
      rw [hbridge, h0, Azurite.AzRat.toRat_zero]
      rfl
    · intro h0
      have h1 := hbridge r.den
      rw [h0, Azurite.AzRat.toRat_zero] at h1
      have h2 : (AzPolynomial.eval r.den z).toInt = 0 := by exact_mod_cast h1.symm
      exact Azurite.AzInt.ringEquivInt.injective (by simpa using h2)
  rw [evalAzInt, evalAzRat]
  by_cases hd : AzPolynomial.eval r.den z = 0
  · rw [ite_eq_left hd, ite_eq_left (hzero.mp hd)]
  · rw [ite_eq_right hd, ite_eq_right (fun h0 => hd (hzero.mpr h0))]
    congr 1
    apply Azurite.AzRat.toRat_injective
    rw [Azurite.AzRat.toRat_mul, Azurite.AzRat.toRat_mul, Azurite.AzRat.toRat_div,
      Azurite.AzRat.toRat_ofAzInts, hbridge, hbridge]

end Azurite.AzRationalFunction
