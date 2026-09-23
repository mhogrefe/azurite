/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzMvPolynomial.IntContent
import Azurite.AzMvPolynomial.Equiv.Gcd
import Azurite.AzMvPolynomial.Parse
import Azurite.AzMvPolynomial.ToString
import Azurite.AzRat.Construct
import Azurite.AzRat.Conversion

/-!
# `AzMvRationalFunction`: computable multivariate rational functions over `ℤ`

The multivariate analogue of `AzRationalFunction`. A rational function in
**factored canonical form** `factor · (num / den)`:

* `factor : AzRat` — a rational scalar carrying the sign and the contents;
* `num, den : AzMvPolynomial n AzInt ord` — both **primitive** (integer
  content `1`), with **positive leading coefficients** (of the `ord`-largest
  monomial), and **coprime** as polynomials (fraction-field sense);
* the zero function is exactly `factor = 0` with `num = den = 1`.

The factored form is genuinely needed multivariately too — e.g.
`2 / (3x) = (2/3) · (1/x)`. Uniqueness: `num`/`den` are each canonical within
their `ℚ*`-scaling class (primitive + positive-leading) and coprime, and
`factor` absorbs the content ratio.

This file: the structure, the normalizing constructor `ofNumDen`, and
conversions from `AzMvPolynomial n AzInt ord`, `AzInt`, and `AzRat` (no
string conversions yet). Canonicity/correctness proofs are deferred to a
later turn — as in `AzRationalFunction/Basic.lean`, the constructor's final
invariant check is a `dite` whose unreachable `0` fallback is retired then.
-/

namespace Azurite

open Azurite.AzMvPolynomial

/-- A multivariate rational function over `ℤ` in factored canonical form:
`factor · num / den` with a rational scalar and primitive,
positive-leading-coefficient, coprime polynomial parts. -/
structure AzMvRationalFunction (n : ℕ) (ord : MonomialOrder := .Degrevlex) where
  /-- The rational scalar (sign and contents live here). -/
  factor : AzRat
  /-- Numerator part: primitive with positive leading coefficient. -/
  num : AzMvPolynomial n AzInt ord
  /-- Denominator part: primitive with positive leading coefficient. -/
  den : AzMvPolynomial n AzInt ord
  /-- The numerator part is primitive (integer content `1`). -/
  num_primitive : num.intContent = 1
  /-- The denominator part is primitive (integer content `1`). -/
  den_primitive : den.intContent = 1
  /-- The numerator part's leading coefficient is positive. -/
  num_lc_pos : (0 : AzInt) < num.leadingCoeff
  /-- The denominator part's leading coefficient is positive. -/
  den_lc_pos : (0 : AzInt) < den.leadingCoeff
  /-- The parts are coprime as polynomials. -/
  reduced : AzMvPolynomial.coprime num den = true
  /-- The zero function is `0 · 1/1` (canonical zero). -/
  zero_norm : factor = 0 → num = 1 ∧ den = 1
  deriving DecidableEq

namespace AzMvRationalFunction

variable {n : ℕ} {ord : MonomialOrder}

/-! ### Invariants of the constant `1` -/

private theorem one_intContent :
    (1 : AzMvPolynomial n AzInt ord).intContent = 1 := rfl

private theorem one_lc_pos :
    (0 : AzInt) < (1 : AzMvPolynomial n AzInt ord).leadingCoeff := by
  rw [show (1 : AzMvPolynomial n AzInt ord).leadingCoeff = 1 from rfl]; decide

private theorem gcd_one_one :
    AzMvPolynomial.gcd (1 : AzMvPolynomial n AzInt ord) 1 = 1 := by
  rw [AzMvPolynomial.gcd_self]
  apply toNested_injective (n := n)
  apply (towerBridge n).injective
  rw [towerBridge_toNested_normalized, toNested_one, map_one, normalize_one]

private theorem one_totalDegree :
    (1 : AzMvPolynomial n AzInt ord).totalDegree = 0 := by
  rw [totalDegree_toMvPoly,
    show toMvPoly (1 : AzMvPolynomial n AzInt ord) = 1 from map_one toMvPolyHom,
    MvPolynomial.totalDegree_one]

private theorem coprime_one_one :
    AzMvPolynomial.coprime (1 : AzMvPolynomial n AzInt ord) 1 = true := by
  rw [AzMvPolynomial.coprime, gcd_one_one, Bool.and_eq_true, bne_iff_ne, beq_iff_eq]
  exact ⟨one_ne_zero, one_totalDegree⟩

/-! ### Zero, one, inhabited -/

instance : Zero (AzMvRationalFunction n ord) :=
  ⟨⟨0, 1, 1, one_intContent, one_intContent, one_lc_pos, one_lc_pos,
    coprime_one_one, fun _ => ⟨rfl, rfl⟩⟩⟩

instance : One (AzMvRationalFunction n ord) :=
  ⟨⟨1, 1, 1, one_intContent, one_intContent, one_lc_pos, one_lc_pos,
    coprime_one_one, fun h => absurd h (by decide)⟩⟩

instance : Inhabited (AzMvRationalFunction n ord) := ⟨0⟩

/-! ### The normalizing constructor -/

/-- **The normalizing constructor**: `ofNumDen num den` is the canonical
factored representation of `num / den`. Extract the primitive positive parts,
divide out their (primitive positive) polynomial gcd, and collect the signs
and contents into the rational factor. A zero denominator has no meaning;
`ofNumDen num 0 = 0` by convention. (The final invariant checks are decidable
and always succeed on this construction — proven in a later turn; the
fallback `0` branch is unreachable.) -/
def ofNumDen (num den : AzMvPolynomial n AzInt ord) : AzMvRationalFunction n ord :=
  if num = 0 ∨ den = 0 then 0
  else
    let n₁ := primPos num
    let d₁ := primPos den
    let g := AzMvPolynomial.signNorm (AzMvPolynomial.gcd n₁ d₁)
    let N := Azurite.ExactDiv.exactDiv n₁ g
    let D := Azurite.ExactDiv.exactDiv d₁ g
    let a := signedIntContent num
    let b := signedIntContent den
    if h : N.intContent = 1 ∧ D.intContent = 1 ∧ (0 : AzInt) < N.leadingCoeff
        ∧ (0 : AzInt) < D.leadingCoeff ∧ AzMvPolynomial.coprime N D = true
        ∧ (AzRat.ofAzInts a b = 0 → N = 1 ∧ D = 1) then
      ⟨AzRat.ofAzInts a b, N, D, h.1, h.2.1, h.2.2.1, h.2.2.2.1,
        h.2.2.2.2.1, h.2.2.2.2.2⟩
    else 0

/-! ### Conversions -/

/-- A rational number, as a constant rational function — computation-free
(`O(1)`): the scalar is the `AzRat` itself. -/
def ofAzRat (q : AzRat) : AzMvRationalFunction n ord :=
  ⟨q, 1, 1, one_intContent, one_intContent, one_lc_pos, one_lc_pos,
    coprime_one_one, fun _ => ⟨rfl, rfl⟩⟩

/-- An integer, as a constant rational function — computation-free. -/
def ofAzInt (z : AzInt) : AzMvRationalFunction n ord :=
  ofAzRat z.toAzRat

/-- A polynomial, as the rational function `p / 1` (through the normalizing
constructor: the content and sign of `p` move into the factor). -/
def ofMvPolynomial (p : AzMvPolynomial n AzInt ord) : AzMvRationalFunction n ord :=
  ofNumDen p 1

/-! ### Basic facts -/

/-- The numerator part is nonzero. -/
theorem num_ne_zero (r : AzMvRationalFunction n ord) : r.num ≠ 0 := by
  intro h
  have h2 := r.num_lc_pos
  rw [h, show leadingCoeff (0 : AzMvPolynomial n AzInt ord) = 0 from rfl] at h2
  exact absurd h2 (by decide)

/-- The denominator part is nonzero. -/
theorem den_ne_zero (r : AzMvRationalFunction n ord) : r.den ≠ 0 := by
  intro h
  have h2 := r.den_lc_pos
  rw [h, show leadingCoeff (0 : AzMvPolynomial n AzInt ord) = 0 from rfl] at h2
  exact absurd h2 (by decide)

/-- Two representations are equal iff all three components agree. -/
@[ext] theorem ext {r s : AzMvRationalFunction n ord} (hfac : r.factor = s.factor)
    (hnum : r.num = s.num) (hden : r.den = s.den) : r = s := by
  cases r
  cases s
  simp only at hfac hnum hden
  subst hfac hnum hden
  rfl

/-- `ofNumDen` with a zero denominator is the zero function. -/
theorem ofNumDen_den_zero (num : AzMvPolynomial n AzInt ord) :
    ofNumDen num 0 = 0 := by
  rw [ofNumDen, ite_eq_left (Or.inr rfl)]

-- ═══════════════════════════════════════════════════════════════════
-- Tests
-- ═══════════════════════════════════════════════════════════════════

section Tests

private instance : Fact (2 ≤ 26) := ⟨by omega⟩

private def p2 (s : String) : AzMvPolynomial 2 AzInt .Degrevlex :=
  (AzMvPolynomial.parseStrWith (XyzVar 2) s).getD 0

private def render (r : AzMvRationalFunction 2 .Degrevlex) : String × String × String :=
  (toString r.factor, r.num.toStrWith (XyzVar 2), r.den.toStrWith (XyzVar 2))

-- `2*x / 3`: factor `2/3`, num `x`, den `1` (content and sign into the factor)
#guard render (ofNumDen (p2 "2*x") (p2 "3")) == ("2/3", "x", "1")
-- reducing example: `(x²−y²)/(x−y)` normalizes to num `x+y`, den `1`, factor `1`
#guard render (ofNumDen (p2 "x^2-y^2") (p2 "x-y")) == ("1", "x+y", "1")
-- sign/content into the factor: `(-2x-2)/(4)` → factor `-1/2`, num `x+1`, den `1`
#guard render (ofNumDen (p2 "-2*x-2") (p2 "4")) == ("-1/2", "x+1", "1")
-- zero denominator is the zero function
#guard ofNumDen (p2 "2*x") 0 == 0
#guard ofNumDen (p2 "2*x") (p2 "0") == 0
-- zero numerator is the zero function
#guard ofNumDen (p2 "0") (p2 "x") == 0
-- conversions
#guard render (ofAzRat (AzRat.parse "3/4").get!) == ("3/4", "1", "1")
#guard render (ofAzInt (-5 : AzInt)) == ("-5", "1", "1")
#guard render (ofMvPolynomial (p2 "6*x+4*y")) == ("2", "3*x+2*y", "1")
-- 0 and 1 render as `0·1/1` and `1·1/1`
#guard render (0 : AzMvRationalFunction 2 .Degrevlex) == ("0", "1", "1")
#guard render (1 : AzMvRationalFunction 2 .Degrevlex) == ("1", "1", "1")

end Tests

end AzMvRationalFunction

end Azurite
