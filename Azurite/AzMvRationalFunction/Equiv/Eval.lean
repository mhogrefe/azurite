import Azurite.AzMvRationalFunction.Eval
import Azurite.AzMvRationalFunction.Equiv.Basic
import Azurite.AzMvPolynomial.Equiv.Eval
import Azurite.AzMvPolynomial.Equiv.Cast
import Azurite.AzInt.Equiv.RingEquiv
import Azurite.AzRat.Equiv.RingEquiv
import Azurite.AzRat.Equiv.Construct
import Azurite.AzRat.Equiv.Mul
import Azurite.AzRat.Equiv.Div

/-!
# Correctness of evaluation

`AzMvPolynomial.evalAzRat` computes exactly the value of the represented
`ℚ[x⃗]` polynomial at the represented rational tuple (`toRat_evalAzRat`), and
the rational-function evaluators return `none` exactly at the poles of the
denominator part and otherwise the value `factor · num(x)/den(x)`
(`evalAzRat_eq_none_iff`, `toRat_evalAzRat_rf`); the integer-tuple evaluator
agrees with the rational one (`evalAzInt_eq_evalAzRat`).
-/

namespace Azurite

open _root_.Azurite.MvPolynomial Azurite.AzMvRationalFunction

variable {n : ℕ} {ord : MonomialOrder}

/-- The bundled `AzInt → AzRat` embedding, followed by `AzRat → ℚ`, is the
coefficient homomorphism `coeffQ`. -/
private theorem comp_eq_coeffQ :
    AzRat.toRatRingHom.comp AzInt.toAzRatRingHom = coeffQ := by
  apply RingHom.ext
  intro a
  show AzRat.toRat a.toAzRat = coeffQ a
  rw [AzRat.toRat_toAzRat_int]; rfl

/-- **Correctness of `evalAzRat`**: the value of the cast-and-evaluate scheme
equals the value of the represented `ℚ[x⃗]` polynomial at the represented
rational point. -/
theorem AzMvPolynomial.toRat_evalAzRat
    (p : AzMvPolynomial n AzInt ord) (x : Fin n → AzRat) :
    AzRat.toRat (AzMvPolynomial.evalAzRat p x)
      = MvPolynomial.eval (fun i => AzRat.toRat (x i)) (toMvPolyQ p) := by
  rw [AzMvPolynomial.evalAzRat, AzMvPolynomial.eval_eq_mvPoly_eval,
    show AzRat.toRat = ⇑AzRat.toRatRingHom from rfl,
    MvPolynomial.map_eval AzRat.toRatRingHom x (mapAzIntToAzRat p).toMvPoly,
    AzMvPolynomial.toMvPoly_mapAzIntToAzRat, MvPolynomial.map_map, comp_eq_coeffQ,
    toMvPolyQ_eq_map]
  rfl

namespace AzMvRationalFunction

open AzMvPolynomial (toRat_evalAzRat)

/-- `evalAzRat` returns `none` exactly at the poles of the denominator part. -/
theorem evalAzRat_eq_none_iff (r : AzMvRationalFunction n ord) (x : Fin n → AzRat) :
    r.evalAzRat x = none
      ↔ MvPolynomial.eval (fun i => AzRat.toRat (x i)) (toMvPolyQ r.den) = 0 := by
  have hval : MvPolynomial.eval (fun i => AzRat.toRat (x i)) (toMvPolyQ r.den)
      = AzRat.toRat (AzMvPolynomial.evalAzRat r.den x) := (toRat_evalAzRat r.den x).symm
  rw [evalAzRat, hval]
  by_cases h : AzMvPolynomial.evalAzRat r.den x = 0
  · rw [ite_eq_left h, h, AzRat.toRat_zero]; simp
  · rw [ite_eq_right h]
    simp only [reduceCtorEq, false_iff]
    intro h0
    exact h (AzRat.toRat_injective (by rw [h0, AzRat.toRat_zero]))

/-- **Correctness of `evalAzRat`** at a non-pole: the value is
`factor · num(x)/den(x)`. -/
theorem toRat_evalAzRat_rf (r : AzMvRationalFunction n ord) (x : Fin n → AzRat) (v : AzRat)
    (h : r.evalAzRat x = some v) :
    AzRat.toRat v
      = AzRat.toRat r.factor
          * (MvPolynomial.eval (fun i => AzRat.toRat (x i)) (toMvPolyQ r.num)
              / MvPolynomial.eval (fun i => AzRat.toRat (x i)) (toMvPolyQ r.den)) := by
  rw [evalAzRat] at h
  by_cases hd : AzMvPolynomial.evalAzRat r.den x = 0
  · rw [ite_eq_left hd] at h; exact absurd h (by simp)
  · rw [ite_eq_right hd, Option.some_inj] at h
    rw [← h, AzRat.toRat_mul, AzRat.toRat_div, toRat_evalAzRat, toRat_evalAzRat]

/-- The integer-tuple evaluator agrees with the rational-tuple one. -/
theorem evalAzInt_eq_evalAzRat (r : AzMvRationalFunction n ord) (z : Fin n → AzInt) :
    r.evalAzInt z = r.evalAzRat (fun i => (z i).toAzRat) := by
  have hbridge : ∀ p : AzMvPolynomial n AzInt ord,
      AzRat.toRat (AzMvPolynomial.evalAzRat p (fun i => (z i).toAzRat))
        = ((AzMvPolynomial.eval p z).toInt : ℚ) := by
    intro p
    have hpt : (fun i => AzRat.toRat (z i).toAzRat) = (fun i => coeffQ (z i)) := by
      funext i; rw [AzRat.toRat_toAzRat_int]; rfl
    rw [toRat_evalAzRat, hpt, AzMvPolynomial.eval_eq_mvPoly_eval,
      show ((MvPolynomial.eval z p.toMvPoly).toInt : ℚ)
        = coeffQ (MvPolynomial.eval z p.toMvPoly) from rfl,
      MvPolynomial.map_eval coeffQ z p.toMvPoly, toMvPolyQ_eq_map]
    rfl
  have hzero : AzMvPolynomial.eval r.den z = 0
      ↔ AzMvPolynomial.evalAzRat r.den (fun i => (z i).toAzRat) = 0 := by
    constructor
    · intro h0
      apply AzRat.toRat_injective
      rw [hbridge, h0, AzRat.toRat_zero]; rfl
    · intro h0
      have h1 := hbridge r.den
      rw [h0, AzRat.toRat_zero] at h1
      have h2 : (AzMvPolynomial.eval r.den z).toInt = 0 := by exact_mod_cast h1.symm
      exact AzInt.ringEquivInt.injective (by simpa using h2)
  rw [evalAzInt, evalAzRat]
  by_cases hd : AzMvPolynomial.eval r.den z = 0
  · rw [ite_eq_left hd, ite_eq_left (hzero.mp hd)]
  · rw [ite_eq_right hd, ite_eq_right (fun h0 => hd (hzero.mpr h0))]
    congr 1
    apply AzRat.toRat_injective
    rw [AzRat.toRat_mul, AzRat.toRat_mul, AzRat.toRat_div, AzRat.toRat_ofAzInts,
      hbridge, hbridge]

end AzMvRationalFunction

end Azurite
