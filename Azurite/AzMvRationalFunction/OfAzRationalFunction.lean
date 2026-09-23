/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzMvRationalFunction.Basic
import Azurite.AzRationalFunction.Basic
import Azurite.AzMvPolynomial.Equiv.OfAzPolynomial
import Azurite.AzMvPolynomial.Equiv.Gcd
import Azurite.AzPolynomial.Parse
import Azurite.AzRat.ToString

/-!
# Lifting a univariate rational function into `AzMvRationalFunction`

`AzRationalFunction.toAzMvRationalFunction i ord` lifts a univariate rational
function into the `i`-th variable — the rational-function analogue of
`AzPolynomial.toAzMvPolynomial i ord`. The scalar `factor` is unchanged; the
numerator and denominator lift via `AzPolynomial.toAzMvPolynomial`, and the five
structural invariants transfer:

* **primitive** via `intContent_toAzMvPolynomial` (`= content`);
* **positive leading coefficient** via `leadingCoeff_toAzMvPolynomial`;
* **coprime** via `coprime_toAzMvPolynomial` (the full equality);
* **zero-normal** via `toAzMvPolynomial_one` (the lift of `1`).
-/

namespace Azurite

open Azurite.AzMvPolynomial

variable {n : ℕ} {ord : MonomialOrder}

/-- The lift of the constant `1` is `1`. -/
theorem AzPolynomial.toAzMvPolynomial_one (i : Fin n) :
    (1 : AzPolynomial AzInt).toAzMvPolynomial i ord = 1 := by
  apply toMvPoly_injective
  rw [toMvPoly_toAzMvPolynomial, toPoly_one, Polynomial.eval₂_one]
  exact (map_one toMvPolyHom).symm

/-- **Lift a univariate rational function into the `i`-th variable.** The
scalar factor is unchanged; the numerator/denominator lift via
`AzPolynomial.toAzMvPolynomial`. -/
def AzRationalFunction.toAzMvRationalFunction {n : ℕ} (i : Fin n)
    (ord : MonomialOrder := .Degrevlex) (r : AzRationalFunction) :
    AzMvRationalFunction n ord where
  factor := r.factor
  num := r.num.toAzMvPolynomial i ord
  den := r.den.toAzMvPolynomial i ord
  num_primitive := by
    rw [AzMvPolynomial.intContent_toAzMvPolynomial]; exact r.num_content
  den_primitive := by
    rw [AzMvPolynomial.intContent_toAzMvPolynomial]; exact r.den_content
  num_lc_pos := by
    rw [AzMvPolynomial.leadingCoeff_toAzMvPolynomial]; exact r.num_lc_pos
  den_lc_pos := by
    rw [AzMvPolynomial.leadingCoeff_toAzMvPolynomial]; exact r.den_lc_pos
  reduced := by
    rw [AzMvPolynomial.coprime_toAzMvPolynomial]; exact r.reduced
  zero_norm := fun h => by
    obtain ⟨hn, hd⟩ := r.zero_norm h
    exact ⟨by rw [hn]; exact AzPolynomial.toAzMvPolynomial_one i,
      by rw [hd]; exact AzPolynomial.toAzMvPolynomial_one i⟩

@[simp] theorem AzRationalFunction.toAzMvRationalFunction_factor (i : Fin n)
    (r : AzRationalFunction) :
    (r.toAzMvRationalFunction i ord).factor = r.factor := rfl

@[simp] theorem AzRationalFunction.toAzMvRationalFunction_num (i : Fin n)
    (r : AzRationalFunction) :
    (r.toAzMvRationalFunction i ord).num = r.num.toAzMvPolynomial i ord := rfl

@[simp] theorem AzRationalFunction.toAzMvRationalFunction_den (i : Fin n)
    (r : AzRationalFunction) :
    (r.toAzMvRationalFunction i ord).den = r.den.toAzMvPolynomial i ord := rfl

-- ═══════════════════════════════════════════════════════════════════
-- Tests
-- ═══════════════════════════════════════════════════════════════════

section Tests

private instance : Fact (2 ≤ 26) := ⟨by omega⟩

private def pu (s : String) : AzPolynomial AzInt :=
  (AzPolynomial.parseAzPolynomial (R := AzInt) s).get!

private def render2 (r : AzMvRationalFunction 2 .Degrevlex) : String × String × String :=
  (toString r.factor, r.num.toStrWith (XyzVar 2), r.den.toStrWith (XyzVar 2))

-- `(x-1)/2` lifted into variable `x₀`: factor `1/2`, num `x-1`, den `1`
#guard render2 ((AzRationalFunction.ofNumDen (pu "x-1") (pu "2")).toAzMvRationalFunction 0)
  == ("1/2", "x-1", "1")
-- `(2x²-2)/(x+1) = 2·(x-1)` lifted into variable `x₁`: factor `2`, num `y-1`, den `1`
#guard render2 ((AzRationalFunction.ofNumDen (pu "2*x^2-2") (pu "x+1")).toAzMvRationalFunction 1)
  == ("2", "y-1", "1")
-- the scalar factor is unchanged by the lift
#guard toString
    ((AzRationalFunction.ofNumDen (pu "x-1") (pu "2")).toAzMvRationalFunction (0 : Fin 2)).factor
  == "1/2"

end Tests

end Azurite
