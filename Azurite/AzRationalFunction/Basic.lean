import Azurite.AzPolynomial.Gcd
import Azurite.AzPolynomial.Compare
import Azurite.AzPolynomial.Content
import Azurite.AzPolynomial.Neg
import Azurite.AzPolynomial.Monomial
import Azurite.AzNat.Equiv.Gcd
import Azurite.AzInt.Equiv.Compare
import Azurite.AzRat.Construct
import Azurite.AzRat.Conversion

/-!
# `AzRationalFunction`: computable rational functions over `ℤ`

A rational function in **factored canonical form**
`factor · (num / den)`:

* `factor : AzRat` — a rational scalar carrying the sign and the contents;
* `num, den : AzPolynomial AzInt` — both **primitive** (content `1`), with
  **positive leading coefficients**, and **coprime** as polynomials;
* the zero function is exactly `factor = 0` with `num = den = 1`.

Representations are unique, and the factored form pays off operationally:
negation and inversion touch only the scalar / swap the parts (`O(1)`),
multiplication reduces content-free polynomials (smaller subresultant
chains) and needs no content re-extraction (Gauss: primitive × primitive is
primitive), and the coefficient arrays never carry a content factor
(space). Addition pays a modest re-scaling cost — the chosen trade-off.

Coefficients are fixed to `AzInt`: over `ℤ` this canonical form is
available; an arbitrary coefficient ring has no comparable normal form.

This file: the structure, the normalizing constructor `ofNumDen`, and
conversions from `AzPolynomial AzInt`, `AzInt`, and `AzRat` (no string
conversions yet). The semantic anchor (`RatFunc ℚ`) lives in the `Equiv`
layer.
-/

namespace Azurite

open Azurite.AzPolynomial

/-- A rational function over `ℤ` in factored canonical form:
`factor · num / den` with a rational scalar and primitive,
positive-leading-coefficient, coprime polynomial parts. -/
structure AzRationalFunction where
  /-- The rational scalar (sign and contents live here). -/
  factor : AzRat
  /-- Numerator part: primitive with positive leading coefficient. -/
  num : AzPolynomial AzInt
  /-- Denominator part: primitive with positive leading coefficient. -/
  den : AzPolynomial AzInt
  /-- The numerator part is primitive. -/
  num_content : num.content = 1
  /-- The denominator part is primitive. -/
  den_content : den.content = 1
  /-- The numerator part's leading coefficient is positive. -/
  num_lc_pos : (0 : AzInt) < num.leadingCoeff
  /-- The denominator part's leading coefficient is positive. -/
  den_lc_pos : (0 : AzInt) < den.leadingCoeff
  /-- The parts are coprime as polynomials. -/
  reduced : AzPolynomial.coprime num den = true
  /-- The zero function is `0 · 1/1` (canonical zero). -/
  zero_norm : factor = 0 → num = 1 ∧ den = 1
  deriving DecidableEq

namespace AzRationalFunction

private theorem one_content : (1 : AzPolynomial AzInt).content = 1 := by decide

private theorem one_lc_pos : (0 : AzInt) < (1 : AzPolynomial AzInt).leadingCoeff := by
  decide

private theorem coprime_one_one :
    AzPolynomial.coprime (1 : AzPolynomial AzInt) 1 = true := by decide

instance : Zero AzRationalFunction :=
  ⟨⟨0, 1, 1, one_content, one_content, one_lc_pos, one_lc_pos, coprime_one_one,
    fun _ => ⟨rfl, rfl⟩⟩⟩

instance : One AzRationalFunction :=
  ⟨⟨1, 1, 1, one_content, one_content, one_lc_pos, one_lc_pos, coprime_one_one,
    fun h => absurd h (by decide)⟩⟩

instance : Inhabited AzRationalFunction := ⟨0⟩

/-- **The normalizing constructor**: `ofNumDen n d` is the canonical
factored representation of `n / d`. Extract the primitive positive parts,
divide out their (primitive positive) polynomial gcd, and collect the signs
and contents into the rational factor. A zero denominator has no meaning;
`ofNumDen n 0 = 0` by convention. (The final invariant checks are decidable
and always succeed on this construction — proven in the `Equiv` layer; the
fallback `0` branch is unreachable.) -/
def ofNumDen (n d : AzPolynomial AzInt) : AzRationalFunction :=
  if n = 0 ∨ d = 0 then 0
  else
    let n₁ := primPos n
    let d₁ := primPos d
    let g := gcdNormalizedInt n₁ d₁
    let N := (exactDivQuoRem n₁ g).1
    let D := (exactDivQuoRem d₁ g).1
    let a := if (0 : AzInt) < n.leadingCoeff then n.content.toAzInt
             else -n.content.toAzInt
    let b := if (0 : AzInt) < d.leadingCoeff then d.content.toAzInt
             else -d.content.toAzInt
    if h : N.content = 1 ∧ D.content = 1 ∧ (0 : AzInt) < N.leadingCoeff
        ∧ (0 : AzInt) < D.leadingCoeff ∧ AzPolynomial.coprime N D = true
        ∧ (AzRat.ofAzInts a b = 0 → N = 1 ∧ D = 1) then
      ⟨AzRat.ofAzInts a b, N, D, h.1, h.2.1, h.2.2.1, h.2.2.2.1,
        h.2.2.2.2.1, h.2.2.2.2.2⟩
    else 0

/-- A rational number, as a constant rational function — computation-free
(`O(1)`): the scalar is the `AzRat` itself. -/
def ofAzRat (q : AzRat) : AzRationalFunction :=
  ⟨q, 1, 1, one_content, one_content, one_lc_pos, one_lc_pos, coprime_one_one,
    fun _ => ⟨rfl, rfl⟩⟩

/-- An integer, as a constant rational function — computation-free. -/
def ofAzInt (z : AzInt) : AzRationalFunction :=
  ofAzRat z.toAzRat

/-- A polynomial, as the rational function `p / 1` (through the normalizing
constructor: the content and sign of `p` move into the factor). -/
def ofPolynomial (p : AzPolynomial AzInt) : AzRationalFunction :=
  ofNumDen p 1

/-- The numerator part is nonzero. -/
theorem num_ne_zero (r : AzRationalFunction) : r.num ≠ 0 := by
  intro h
  have h2 := r.num_lc_pos
  rw [h] at h2
  exact absurd h2 (by decide)

/-- The denominator part is nonzero. -/
theorem den_ne_zero (r : AzRationalFunction) : r.den ≠ 0 := by
  intro h
  have h2 := r.den_lc_pos
  rw [h] at h2
  exact absurd h2 (by decide)

/-- Two representations are equal iff all three components agree. -/
@[ext] theorem ext {r s : AzRationalFunction} (hfac : r.factor = s.factor)
    (hnum : r.num = s.num) (hden : r.den = s.den) : r = s := by
  cases r
  cases s
  simp only at hfac hnum hden
  subst hfac hnum hden
  rfl

/-- `ofNumDen` with a zero denominator is the zero function. -/
theorem ofNumDen_den_zero (n : AzPolynomial AzInt) : ofNumDen n 0 = 0 := by
  rw [ofNumDen, if_pos (Or.inr rfl)]

end AzRationalFunction

end Azurite
