/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzRationalFunction.Parse
import Azurite.AzPolynomial.Equiv.Predicates
import Azurite.AzPolynomial.Pow
import Azurite.AzPolynomial.Sub
import Azurite.AzPolynomial.Derivative
import Azurite.AzRat.Pow

/-!
# Arithmetic on `AzRationalFunction`: negation and reciprocal

The factored canonical form makes both `O(1)`:

* **negation** flips the sign of the rational factor — the polynomial parts
  and all their invariants are untouched;
* **reciprocal** inverts the factor and swaps the parts (their invariants
  swap along; polynomial coprimality is symmetric). `0⁻¹ = 0` by the usual
  field convention.
-/

namespace Azurite.AzRationalFunction

open Azurite.AzPolynomial

/-- Polynomial coprimality is symmetric (through the `ℚ[X]` semantics). -/
private theorem coprime_symm {P Q : AzPolynomial AzInt}
    (h : AzPolynomial.coprime P Q = true) : AzPolynomial.coprime Q P = true :=
  (AzPolynomial.coprime_int_iff Q P).mpr ((AzPolynomial.coprime_int_iff P Q).mp h).symm

/-- **Negation**: flip the factor's sign (`O(1)`). -/
def neg (r : AzRationalFunction) : AzRationalFunction :=
  ⟨-r.factor, r.num, r.den, r.num_content, r.den_content, r.num_lc_pos,
    r.den_lc_pos, r.reduced, fun h => r.zero_norm (neg_eq_zero.mp h)⟩

instance : Neg AzRationalFunction := ⟨neg⟩

/-- **Reciprocal**: invert the factor and swap the parts (`O(1)`);
`0⁻¹ = 0`. -/
def inv (r : AzRationalFunction) : AzRationalFunction :=
  if h : r.factor = 0 then 0
  else
    ⟨r.factor⁻¹, r.den, r.num, r.den_content, r.num_content, r.den_lc_pos,
      r.num_lc_pos, coprime_symm r.reduced,
      fun h0 => absurd (inv_eq_zero.mp h0) h⟩

instance : Inv AzRationalFunction := ⟨inv⟩

/-- **Multiplication** (the `AzRat.mul` cross-gcd pattern, polynomial-lifted):
for `p·N₁/D₁ · q·N₂/D₂`, reduce by the two *cross* gcds
`G₁ := gcd(N₁, D₂)`, `G₂ := gcd(N₂, D₁)` — computed on the content-free
parts, so the subresultant chains stay small — and multiply the reduced
parts. By Gauss's lemma the products of primitives are primitive: no
content re-extraction. The scalar factors multiply as `AzRat`s (their own
cross-gcd reduction). (Invariant checks are decidable and always succeed —
proven in the `Equiv` layer; the fallback `0` branch is unreachable.) -/
def mul (r s : AzRationalFunction) : AzRationalFunction :=
  if r.factor = 0 ∨ s.factor = 0 then 0
  else
    let g₁ := gcdNormalizedInt r.num s.den
    let g₂ := gcdNormalizedInt s.num r.den
    let n := (exactDivQuoRem r.num g₁).1 * (exactDivQuoRem s.num g₂).1
    let d := (exactDivQuoRem r.den g₂).1 * (exactDivQuoRem s.den g₁).1
    if h : n.content = 1 ∧ d.content = 1 ∧ (0 : AzInt) < n.leadingCoeff
        ∧ (0 : AzInt) < d.leadingCoeff ∧ AzPolynomial.coprime n d = true
        ∧ (r.factor * s.factor = 0 → n = 1 ∧ d = 1) then
      ⟨r.factor * s.factor, n, d, h.1, h.2.1, h.2.2.1, h.2.2.2.1,
        h.2.2.2.2.1, h.2.2.2.2.2⟩
    else 0

instance : Mul AzRationalFunction := ⟨mul⟩

/-- **Division**: multiply by the reciprocal (the reciprocal is `O(1)`, so
this is exactly one cross-gcd multiplication; `r / 0 = 0`). -/
def div (r s : AzRationalFunction) : AzRationalFunction :=
  r * s⁻¹

instance : Div AzRationalFunction := ⟨div⟩

/-- **Addition** (the `AzRat.add` Knuth pattern, polynomial-lifted, with the
factored-form subtleties): the scalar factors cross-multiply into the
combined numerator `T := a₁b₂·N₁·(D₂/G) + a₂b₁·N₂·(D₁/G)` where
`G := gcd(D₁, D₂)`; when `G = 1` (coprime denominator parts) no further
polynomial reduction is needed (fast path); otherwise the only possible
common part is confined to `G`, so the second gcd is the small
`H := gcd(T, G)` and the denominator part is `(D₁/G)·(D₂/H)`. Finally the
content and sign of the numerator extract into the rational factor
(`b₁b₂` joins its denominator). (Invariant checks decidable; fallback `0`
unreachable — proven in the `Equiv` layer.) -/
def add (r s : AzRationalFunction) : AzRationalFunction :=
  if r.factor = 0 then s
  else if s.factor = 0 then r
  else
    let a₁ : AzInt := ⟨r.factor.sign, r.factor.num, r.factor.zero_sign⟩
    let b₁ : AzInt := ⟨true, r.factor.den, fun _ => rfl⟩
    let a₂ : AzInt := ⟨s.factor.sign, s.factor.num, s.factor.zero_sign⟩
    let b₂ : AzInt := ⟨true, s.factor.den, fun _ => rfl⟩
    let G := gcdNormalizedInt r.den s.den
    let Td :=
      if G.natDegree = 0 then
        ((a₁ * b₂) • (r.num * s.den) + (a₂ * b₁) • (s.num * r.den),
         r.den * s.den)
      else
        let D₁' := (exactDivQuoRem r.den G).1
        let D₂' := (exactDivQuoRem s.den G).1
        let T₀ := (a₁ * b₂) • (r.num * D₂') + (a₂ * b₁) • (s.num * D₁')
        if T₀ = 0 then (0, 1)
        else
          let H := gcdNormalizedInt T₀ G
          ((exactDivQuoRem T₀ H).1, D₁' * (exactDivQuoRem s.den H).1)
    if Td.1 = 0 then 0
    else
      let a := if (0 : AzInt) < Td.1.leadingCoeff then Td.1.content.toAzInt
               else -Td.1.content.toAzInt
      let n := primPos Td.1
      if h : n.content = 1 ∧ Td.2.content = 1 ∧ (0 : AzInt) < n.leadingCoeff
          ∧ (0 : AzInt) < Td.2.leadingCoeff ∧ AzPolynomial.coprime n Td.2 = true
          ∧ (AzRat.ofAzInts a (b₁ * b₂) = 0 → n = 1 ∧ Td.2 = 1) then
        ⟨AzRat.ofAzInts a (b₁ * b₂), n, Td.2, h.1, h.2.1, h.2.2.1, h.2.2.2.1,
          h.2.2.2.2.1, h.2.2.2.2.2⟩
      else 0

instance : Add AzRationalFunction := ⟨add⟩

/-- **Subtraction**: add the negation (negation is `O(1)`). -/
def sub (r s : AzRationalFunction) : AzRationalFunction :=
  r + (-s)

instance : Sub AzRationalFunction := ⟨sub⟩

/-- **Exponentiation by `ℕ`** — fully componentwise, the factored form's
third free operation: no gcd at all. The parts stay coprime (powers of
coprime polynomials are coprime), primitive (Gauss), and positive-leading
(powers of positives), and the scalar factor powers as an `AzRat`
(componentwise sliding-window `AzNat` powers). The edges come out natively:
`n = 0` gives `1·(1/1) = 1` and a zero factor keeps parts `1` since
`1 ^ n = 1`. (Invariant checks decidable; fallback `0` unreachable —
proven in the `Equiv` layer.) -/
def pow (r : AzRationalFunction) (n : ℕ) : AzRationalFunction :=
  let f := r.factor.pow n
  let nm := AzPolynomial.pow r.num n
  let dn := AzPolynomial.pow r.den n
  if h : nm.content = 1 ∧ dn.content = 1 ∧ (0 : AzInt) < nm.leadingCoeff
      ∧ (0 : AzInt) < dn.leadingCoeff ∧ AzPolynomial.coprime nm dn = true
      ∧ (f = 0 → nm = 1 ∧ dn = 1) then
    ⟨f, nm, dn, h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩
  else 0

/-- **Exponentiation by `ℤ`**: a `ℕ`-power plus (for negative exponents)
one `O(1)` reciprocal. -/
def zpow (r : AzRationalFunction) (z : ℤ) : AzRationalFunction :=
  if 0 ≤ z then pow r z.toNat else (pow r (-z).toNat)⁻¹

/-- **Homogenized composition kernel**:
`evalSpecialComp p b c = ∑ pᵢ · bⁱ · c^{n−i}` with `n = natDegree p` — the
`evalSpecial` fold with polynomial arguments and coefficient scalars, so
that `p(b/c) = evalSpecialComp p b c / c^n` over the fraction field. -/
def evalSpecialComp (p b c : AzPolynomial AzInt) : AzPolynomial AzInt :=
  (p.coeffs.foldr (init := ((0 : AzPolynomial AzInt), (1 : AzPolynomial AzInt)))
    (fun a x => (a • x.2 + x.1 * b, x.2 * c))).1

/-- **Composition** `r ∘ s`: homogenize the parts of `r` at the fraction
`s = aA / bB` (with `aA := a₂ • N₂`, `bB := b₂ • D₂` collecting `s`'s scalar
components as in `add`), balance the two `bB`-power denominators
(`ℕ`-subtraction truncation implements the max-split — exactly one factor
is nontrivial), fold `r`'s scalar components in, and normalize **once**
through `ofNumDen`. Defined whenever the denominator of `r` does not vanish
at `s` as a rational function; the junk case — `s` a constant sitting at a
pole of `r` — collapses to `ofNumDen _ 0 = 0`, consistent with the
`eval`/`ofNumDen` conventions. -/
def comp (r s : AzRationalFunction) : AzRationalFunction :=
  let aA := (⟨s.factor.sign, s.factor.num, s.factor.zero_sign⟩ : AzInt) • s.num
  let bB := (⟨true, s.factor.den, fun _ => rfl⟩ : AzInt) • s.den
  let TN := evalSpecialComp r.num aA bB
  let TD := evalSpecialComp r.den aA bB
  ofNumDen
    ((⟨r.factor.sign, r.factor.num, r.factor.zero_sign⟩ : AzInt)
      • (TN * AzPolynomial.pow bB (r.den.natDegree - r.num.natDegree)))
    ((⟨true, r.factor.den, fun _ => rfl⟩ : AzInt)
      • (TD * AzPolynomial.pow bB (r.num.natDegree - r.den.natDegree)))

/-- **Derivative** — the quotient rule through one normalization: the
integer-polynomial combination `N′·D − N·D′` over `D²`, with the constant
rational factor multiplying through unchanged (its own derivative
contributes nothing). Junk-free: the denominator is always nonzero. -/
def derivative (r : AzRationalFunction) : AzRationalFunction :=
  let T := AzPolynomial.derivative r.num * r.den - r.num * AzPolynomial.derivative r.den
  ofNumDen
    ((⟨r.factor.sign, r.factor.num, r.factor.zero_sign⟩ : AzInt) • T)
    ((⟨true, r.factor.den, fun _ => rfl⟩ : AzInt) • (r.den * r.den))

/-- **The degree** of a rational function, as an integer:
`natDegree num − natDegree den`. Automatically `0` for `r = 0` (both parts
are `1`), matching Mathlib's `RatFunc.intDegree` convention. -/
def intDegree (r : AzRationalFunction) : ℤ :=
  (r.num.natDegree : ℤ) - r.den.natDegree

/-- **The sign of `r(x)` as `x → +∞`** — `O(1)` in the factored form: both
parts have positive leading coefficients, so the leading behavior carries
exactly the sign of the rational factor (`0` iff `r = 0`, else `±1`). -/
def signTop (r : AzRationalFunction) : AzInt :=
  if r.factor = 0 then 0 else if r.factor.sign then 1 else -1

/-- **The sign of `r(x)` as `x → −∞`**: `signTop` flipped by the parity of
`natDegree num + natDegree den` (each part flips its leading sign at `−∞`
exactly when its degree is odd). -/
def signBot (r : AzRationalFunction) : AzInt :=
  if (r.num.natDegree + r.den.natDegree) % 2 = 0 then signTop r else -signTop r

/-- **The retraction of `ofPolynomial`**: `some p` exactly when `r` is (the
canonical form of) the polynomial `p` — i.e. both denominator components
are `1` — in which case `p` is the displayed numerator `(±a) • num`. -/
def toPolynomial (r : AzRationalFunction) : Option (AzPolynomial AzInt) :=
  if r.den = 1 ∧ r.factor.den = 1 then some (displayNum r) else none

-- ═══════════════════════════════════════════════════════════════════
-- Tests
-- ═══════════════════════════════════════════════════════════════════

section Tests

private def rr (s : String) : AzRationalFunction := (parse s).get!

#guard toString (-(rr "(x-1)/2")) == "(-x+1)/2"
#guard toString (-(rr "-3/4")) == "3/4"
#guard toString (-(0 : AzRationalFunction)) == "0"
#guard -(-(rr "(x^2+1)/(x-1)")) == rr "(x^2+1)/(x-1)"
#guard toString ((rr "(x-1)/2")⁻¹) == "2/(x-1)"
#guard toString ((rr "-3/4")⁻¹) == "-4/3"
#guard toString ((0 : AzRationalFunction)⁻¹) == "0"
#guard ((rr "(x^2+1)/(x-1)")⁻¹)⁻¹ == rr "(x^2+1)/(x-1)"
#guard toString ((rr "3*x^2/(x+1)")⁻¹) == "(x+1)/(3*x^2)"
-- multiplication: cross-reduction, contents into the factor
#guard toString (rr "(x-1)/2" * rr "4/(x-1)") == "2"
#guard toString (rr "(x^2-1)/(x+2)" * rr "(x+2)/(x+1)") == "x-1"
#guard toString (rr "2*x/3" * rr "3/(2*x)") == "1"
#guard toString (rr "(x+1)/(x-1)" * rr "(x+1)/(x-1)") == "(x^2+2*x+1)/(x^2-2*x+1)"
#guard toString (rr "x/2" * 0) == "0"
#guard toString (rr "x/2" * 1) == "x/2"
-- division
#guard toString (rr "(x^2-1)/2" / rr "(x-1)/2") == "x+1"
#guard toString (rr "x/2" / rr "x/2") == "1"
#guard toString (rr "x/2" / 0) == "0"
#guard toString (rr "3/4" / rr "x") == "3/(4*x)"
-- addition: contents into the factor, coprime-denominator fast path
#guard toString (rr "(x-1)/2" + rr "(x+1)/2") == "x"
#guard toString (rr "1/2" + rr "1/3") == "5/6"
#guard toString (rr "x" + rr "1/x") == "(x^2+1)/x"
-- addition: the Knuth H-path (common denominator factor)
#guard toString (rr "1/x" + rr "1/x^2") == "(x+1)/x^2"
#guard toString (rr "1/(2*x)" + rr "1/(2*x)") == "1/x"
-- cancellation to zero and identities
#guard rr "(x^2+1)/(x-1)" + (-(rr "(x^2+1)/(x-1)")) == 0
#guard toString (rr "x/2" + 0) == "x/2"
#guard toString ((0 : AzRationalFunction) + rr "x/2") == "x/2"
-- subtraction
#guard toString (rr "1/(x-1)" - rr "1/(x+1)") == "2/(x^2-1)"
#guard toString (rr "x" - rr "x") == "0"
#guard toString (rr "(x^2+1)/(x-1)" - rr "2*x/(x-1)") == "x-1"
-- exponentiation: componentwise, no reduction
#guard toString (pow (rr "(x+1)/(x-1)") 2) == "(x^2+2*x+1)/(x^2-2*x+1)"
#guard pow (rr "x/2") 3 == rr "x^3/8"
#guard pow (rr "(x^2+1)/(x-1)") 0 == 1
#guard pow (0 : AzRationalFunction) 3 == 0
#guard zpow (rr "x/2") (-2) == rr "4/x^2"
#guard zpow (rr "(x^2+1)/(x-1)") 0 == 1
-- composition
#guard comp (rr "(x+1)/(x-1)") (rr "x^2") == rr "(x^2+1)/(x^2-1)"
#guard comp (rr "(x+1)/(x-1)") (rr "x+2") == rr "(x+3)/(x+1)"
#guard comp (rr "(x+1)/(x-1)") (rr "3") == rr "2"
#guard comp (rr "(x+1)/(x-1)") (rr "1") == 0
#guard comp (rr "(x^2+1)/(x-1)") (rr "x") == rr "(x^2+1)/(x-1)"
#guard comp (rr "x") (rr "(x^2+1)/(x-1)") == rr "(x^2+1)/(x-1)"
#guard comp (rr "x^2/(x+1)") (rr "1/x") == rr "1/(x^2+x)"
-- derivative: the quotient rule
#guard derivative (rr "1/x") == rr "-1/x^2"
#guard derivative (rr "(x^2+1)/(x-1)") == rr "(x^2-2*x-1)/(x^2-2*x+1)"
#guard derivative (rr "x^3+x") == rr "3*x^2+1"
#guard derivative (rr "5/7") == 0
#guard derivative (rr "x/2") == rr "1/2"
-- integer degree
#guard intDegree (rr "(x^3+1)/x") == 2
#guard intDegree (rr "1/(x^2-1)") == -2
#guard intDegree (0 : AzRationalFunction) == 0
-- asymptotic signs
#guard signTop (rr "(x+1)/(x-1)") == 1
#guard signTop (rr "-x/2") == -1
#guard signTop (0 : AzRationalFunction) == 0
#guard signBot (rr "x") == -1
#guard signBot (rr "x^2") == 1
#guard signBot (rr "1/x") == -1
-- polynomial retraction
#guard toPolynomial (rr "x^2+3")
    == some ((AzPolynomial.parseAzPolynomial (R := AzInt) "x^2+3").get!)
#guard toPolynomial (rr "-2*x")
    == some ((AzPolynomial.parseAzPolynomial (R := AzInt) "-2*x").get!)
#guard toPolynomial (rr "x/2") == none
#guard toPolynomial (rr "1/x") == none
#guard toPolynomial (0 : AzRationalFunction) == some 0

end Tests

end Azurite.AzRationalFunction
