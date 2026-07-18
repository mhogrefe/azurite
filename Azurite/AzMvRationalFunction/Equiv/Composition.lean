import Azurite.AzMvRationalFunction.Composition
import Azurite.AzMvRationalFunction.Equiv.Arithmetic

/-!
# Correctness of composition

Let `M := FractionRing (MvPolynomial (Fin m) ℚ)` and `g i := toMvRatFunc (s i)`.

The composition kernel `evalMv` is intertwined by `toMvRatFunc` with
`MvPolynomial.aeval` at the tuple `g`: `toMvRatFunc` is a ring homomorphism
(it is `ringEquivRatFunc`), so it commutes with the `evalMv` fold term by
term (`toMvRatFunc_evalMv`). Hence composition maps to substitution in the
fraction field (`toMvRatFunc_comp`), *unconditionally* — when the denominator
image vanishes at `g` both sides are `0` by the field division convention.
-/

namespace Azurite.AzMvRationalFunction

open Azurite.AzMvPolynomial _root_.Azurite.MvPolynomial

variable {n m : ℕ} {ord ord' : MonomialOrder}

/-- `ringEquivRatFunc` and `toMvRatFunc` agree (the former just bundles the
latter with `map_add`/`map_mul`), so `toMvRatFunc` inherits the ring-hom
lemmas. -/
private theorem ringEquivRatFunc_eq (r : AzMvRationalFunction m ord') :
    ringEquivRatFunc r = toMvRatFunc r := rfl

/-- **Term identity**: `toMvRatFunc` sends one `evalMv` term to the matching
`aeval` monomial. -/
private theorem toMvRatFunc_term (t : Monomial n AzInt ord)
    (s : Fin n → AzMvRationalFunction m ord') :
    toMvRatFunc (ofAzInt t.coeff.val * t.monic.eval s)
      = MvPolynomial.aeval (fun i => toMvRatFunc (s i)) (MvPolynomial.map coeffQ t.toMvPoly) := by
  rw [Monomial.toMvPoly, MvPolynomial.map_monomial, MvPolynomial.aeval_monomial,
    toMvRatFunc_mul, toMvRatFunc_ofAzInt]
  congr 1
  rw [MonicMonomial.eval, ← ringEquivRatFunc_eq, map_prod,
    MonicMonomial.toFinsupp, Finsupp.onFinset_prod _ (by intros; simp)]
  apply Finset.prod_congr rfl
  intro i _
  rw [map_pow, ringEquivRatFunc_eq]

/-- The `evalMv` fold, intertwined with the `aeval`-over-`toMvPoly` fold. -/
private theorem foldl_evalMv_eq (s : Fin n → AzMvRationalFunction m ord')
    (l : List (Monomial n AzInt ord)) (acc : AzMvRationalFunction m ord')
    (pacc : MvPolynomial (Fin n) AzInt)
    (hacc : toMvRatFunc acc
      = MvPolynomial.aeval (fun i => toMvRatFunc (s i)) (MvPolynomial.map coeffQ pacc)) :
    toMvRatFunc (l.foldl (fun a t => a + ofAzInt t.coeff.val * t.monic.eval s) acc)
      = MvPolynomial.aeval (fun i => toMvRatFunc (s i))
          (MvPolynomial.map coeffQ (l.foldl (fun a t => a + t.toMvPoly) pacc)) := by
  induction l generalizing acc pacc with
  | nil => exact hacc
  | cons t ts ih =>
    simp only [List.foldl_cons]
    apply ih
    rw [toMvRatFunc_add, hacc, map_add, map_add, toMvRatFunc_term]

/-- **Correctness of `evalMv`**: evaluating an integer polynomial at the tuple
`s` (in the field) matches `MvPolynomial.aeval` at `g i = toMvRatFunc (s i)`
applied to the `ℚ[x⃗]`-image of the polynomial. -/
theorem toMvRatFunc_evalMv (p : AzMvPolynomial n AzInt ord)
    (s : Fin n → AzMvRationalFunction m ord') :
    toMvRatFunc (evalMv p s)
      = MvPolynomial.aeval (fun i => toMvRatFunc (s i)) (toMvPolyQ p) := by
  rw [toMvPolyQ_eq_map, AzMvPolynomial.toMvPoly_eq_list_sum,
    ← foldl_add_map_eq_sum Monomial.toMvPoly p.terms.toList, evalMv, ← Array.foldl_toList]
  exact foldl_evalMv_eq s p.terms.toList 0 0 (by rw [toMvRatFunc_zero, map_zero, map_zero])

/-- **Correctness of `comp`** (unconditional): composition maps to substitution
of `g i = toMvRatFunc (s i)` in the fraction field. When the denominator image
`aeval g (toMvPolyQ r.den)` vanishes, both sides are `0` (field division). -/
theorem toMvRatFunc_comp (r : AzMvRationalFunction n ord)
    (s : Fin n → AzMvRationalFunction m ord') :
    toMvRatFunc (comp r s)
      = algebraMap ℚ (FractionRing (MvPolynomial (Fin m) ℚ)) (Azurite.AzRat.toRat r.factor)
        * (MvPolynomial.aeval (fun i => toMvRatFunc (s i)) (toMvPolyQ r.num)
            / MvPolynomial.aeval (fun i => toMvRatFunc (s i)) (toMvPolyQ r.den)) := by
  rw [comp, toMvRatFunc_mul, toMvRatFunc_ofAzRat, toMvRatFunc_div,
    toMvRatFunc_evalMv, toMvRatFunc_evalMv]

end Azurite.AzMvRationalFunction
