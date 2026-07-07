import Azurite.AzMvRationalFunction.Derivative
import Azurite.AzMvRationalFunction.Equiv.Basic
import Azurite.AzMvRationalFunction.Equiv.Parse
import Azurite.AzMvPolynomial.Equiv.Derivative
import Mathlib.Algebra.MvPolynomial.PDeriv

/-!
# Correctness of the partial derivative

`M := FractionRing (MvPolynomial (Fin n) ℚ)`. The partial derivative satisfies
the quotient rule in `ℚ(x⃗)`, stated against the `ℚ[x⃗]`-images through
`MvPolynomial.pderiv` (Mathlib has no derivation on
`FractionRing (MvPolynomial …)`, so — exactly as the univariate
`toRatFunc_derivative` against `ℚ(x)` — the image form is the right statement).
The bridge `toMvPolyQ_pderivGeneral` (the computable polynomial partial
derivative commutes with the `ℚ[x⃗]`-image, via `MvPolynomial.pderiv_map`) plus
`toMvRatFunc_ofNumDen` give the result unconditionally.
-/

namespace Azurite.AzMvRationalFunction

open Azurite.AzMvPolynomial MvPolynomial

variable {n : ℕ} {ord : MonomialOrder}

/-- `toMvPolyQ` commutes with subtraction (it is a ring hom). -/
theorem toMvPolyQ_sub (P Q : AzMvPolynomial n AzInt ord) :
    toMvPolyQ (P - Q) = toMvPolyQ P - toMvPolyQ Q := map_sub toMvPolyQHom P Q

/-- **The pderiv bridge**: the computable polynomial partial derivative
`pderivGeneral j` commutes with the `ℚ[x⃗]`-image `toMvPolyQ`, giving
`MvPolynomial.pderiv j`. -/
theorem toMvPolyQ_pderivGeneral (j : Fin n) (p : AzMvPolynomial n AzInt ord) :
    toMvPolyQ (AzMvPolynomial.pderivGeneral j p) = MvPolynomial.pderiv j (toMvPolyQ p) := by
  rw [toMvPolyQ_eq_map, toMvPoly_pderivGeneral, ← MvPolynomial.pderiv_map, ← toMvPolyQ_eq_map]

/-- The rational factor, as the quotient of its `AzInt` sign/num and den
components (over `ℚ`). -/
private theorem toRat_fac (q : AzRat) :
    Azurite.AzRat.toRat q
      = (((⟨q.sign, q.num, q.zero_sign⟩ : AzInt).toInt : ℚ))
        / (((⟨true, q.den, fun _ => rfl⟩ : AzInt).toInt : ℚ)) := by
  rw [← Rat.num_div_den (Azurite.AzRat.toRat q)]
  have hnum : (Azurite.AzRat.toRat q).num = (⟨q.sign, q.num, q.zero_sign⟩ : AzInt).toInt := rfl
  have hden : (((Azurite.AzRat.toRat q).den : ℤ))
      = (⟨true, q.den, fun _ => rfl⟩ : AzInt).toInt := rfl
  rw [hnum, ← hden]; norm_cast

/-- The denominator component of the factor is nonzero (as a rational). -/
private theorem bden_ne_zero (q : AzRat) :
    (((⟨true, q.den, fun _ => rfl⟩ : AzInt).toInt : ℚ)) ≠ 0 := by
  rw [show (⟨true, q.den, fun _ => rfl⟩ : AzInt).toInt = (q.den.toNat : ℤ) from rfl]
  have h1 : q.den.toNat ≠ 0 := fun h =>
    q.den_nz (Azurite.AzNat.toNat_injective (by rw [h]; rfl))
  exact_mod_cast (show ((q.den.toNat : ℤ)) ≠ 0 by omega)

/-- **The partial derivative is correct** — the quotient rule in `ℚ(x⃗)`:
`toMvRatFunc (pderiv r j) = factor · ((∂ⱼN)·D − N·(∂ⱼD)) / D²` on the
`ℚ[x⃗]`-images. (Mathlib has no derivation on `FractionRing (MvPolynomial …)`,
so the formula is stated against the images.) -/
theorem toMvRatFunc_pderiv (r : AzMvRationalFunction n ord) (j : Fin n) :
    toMvRatFunc (pderiv r j)
      = algebraMap ℚ (FractionRing (MvPolynomial (Fin n) ℚ)) (Azurite.AzRat.toRat r.factor)
        * (algebraMap (MvPolynomial (Fin n) ℚ) (FractionRing (MvPolynomial (Fin n) ℚ))
            (MvPolynomial.pderiv j (toMvPolyQ r.num) * toMvPolyQ r.den
              - toMvPolyQ r.num * MvPolynomial.pderiv j (toMvPolyQ r.den))
          / algebraMap (MvPolynomial (Fin n) ℚ) (FractionRing (MvPolynomial (Fin n) ℚ))
            (toMvPolyQ r.den * toMvPolyQ r.den)) := by
  have hβ : (((⟨true, r.factor.den, fun _ => rfl⟩ : AzInt).toInt : ℚ)) ≠ 0 :=
    bden_ne_zero r.factor
  have hd0 : (⟨true, r.factor.den, fun _ => rfl⟩ : AzInt) • (r.den * r.den) ≠ 0 := by
    intro h0
    have h1 := congrArg toMvPolyQ h0
    rw [toMvPolyQ_smul, toMvPolyQ_mul, toMvPolyQ_zero] at h1
    rcases mul_eq_zero.mp h1 with h2 | h2
    · exact MvPolynomial.C_ne_zero.mpr hβ h2
    · rcases mul_eq_zero.mp h2 with h3 | h3 <;> exact toMvPolyQ_den_ne_zero r h3
  show toMvRatFunc (ofNumDen
      ((⟨r.factor.sign, r.factor.num, r.factor.zero_sign⟩ : AzInt)
        • (AzMvPolynomial.pderivGeneral j r.num * r.den
            - r.num * AzMvPolynomial.pderivGeneral j r.den))
      ((⟨true, r.factor.den, fun _ => rfl⟩ : AzInt) • (r.den * r.den))) = _
  rw [toMvRatFunc_ofNumDen _ _ hd0, toMvPolyQ_smul, toMvPolyQ_smul, toMvPolyQ_sub,
    toMvPolyQ_mul, toMvPolyQ_mul, toMvPolyQ_pderivGeneral, toMvPolyQ_pderivGeneral,
    toMvPolyQ_mul, map_mul, map_mul, ← algebraMapQ_C, ← algebraMapQ_C, toRat_fac,
    map_div₀, div_mul_div_comm]

end Azurite.AzMvRationalFunction
