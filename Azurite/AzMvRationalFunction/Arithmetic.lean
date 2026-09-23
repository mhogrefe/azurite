/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzMvRationalFunction.Parse
import Azurite.AzMvPolynomial.Equiv.Gcd

/-!
# Arithmetic on `AzMvRationalFunction`: negation and reciprocal

The factored canonical form makes both `O(1)`, exactly as in the univariate
`AzRationalFunction`:

* **negation** flips the sign of the rational factor — the polynomial parts
  and all their invariants are untouched;
* **reciprocal** inverts the factor and swaps the parts (their invariants
  swap along; polynomial coprimality is symmetric). `0⁻¹ = 0` by the usual
  field convention.
-/

namespace Azurite.AzMvPolynomial

variable {n : ℕ} {ord : MonomialOrder}

/-- Polynomial coprimality is symmetric in its arguments (`gcd` is). -/
theorem coprime_comm (P Q : AzMvPolynomial n AzInt ord) :
    AzMvPolynomial.coprime P Q = AzMvPolynomial.coprime Q P := by
  unfold AzMvPolynomial.coprime
  rw [AzMvPolynomial.gcd_comm P Q]

/-- Symmetry of `coprime` in `Prop`-eq form (for the `reduced` invariant). -/
theorem coprime_symm {P Q : AzMvPolynomial n AzInt ord}
    (h : AzMvPolynomial.coprime P Q = true) : AzMvPolynomial.coprime Q P = true := by
  rw [← coprime_comm]; exact h

end Azurite.AzMvPolynomial

namespace Azurite.AzMvRationalFunction

open Azurite.AzMvPolynomial

variable {n : ℕ} {ord : MonomialOrder}

/-- **Negation**: flip the factor's sign (`O(1)`). -/
def neg (r : AzMvRationalFunction n ord) : AzMvRationalFunction n ord :=
  ⟨-r.factor, r.num, r.den, r.num_primitive, r.den_primitive, r.num_lc_pos,
    r.den_lc_pos, r.reduced, fun h => r.zero_norm (neg_eq_zero.mp h)⟩

instance : Neg (AzMvRationalFunction n ord) := ⟨neg⟩

/-- **Reciprocal**: invert the factor and swap the parts (`O(1)`);
`0⁻¹ = 0`. -/
def inv (r : AzMvRationalFunction n ord) : AzMvRationalFunction n ord :=
  if h : r.factor = 0 then 0
  else
    ⟨r.factor⁻¹, r.den, r.num, r.den_primitive, r.num_primitive, r.den_lc_pos,
      r.num_lc_pos, coprime_symm r.reduced,
      fun h0 => absurd (inv_eq_zero.mp h0) h⟩

instance : Inv (AzMvRationalFunction n ord) := ⟨inv⟩

/-- **Multiplication** (the `AzRat.mul` cross-gcd pattern, polynomial-lifted):
for `p·N₁/D₁ · q·N₂/D₂`, reduce by the two *cross* gcds `G₁ := gcd(N₁, D₂)`,
`G₂ := gcd(N₂, D₁)` — computed on the (already content-free) parts and
**sign-normalized** (the tower gcd is iterated-leading-coefficient-normalized,
not `ord`-lc-positive, so `signNorm` is needed for cofactor positivity exactly
as in `ofNumDen`) — and multiply the reduced parts. By Gauss's lemma the
products of primitives are primitive: no content re-extraction. The scalar
factors multiply as `AzRat`s. (Invariant checks are decidable and always
succeed — proven in the `Equiv` layer; the fallback `0` branch is
unreachable.) -/
def mul (r s : AzMvRationalFunction n ord) : AzMvRationalFunction n ord :=
  if r.factor = 0 ∨ s.factor = 0 then 0
  else
    let G₁ := signNorm (AzMvPolynomial.gcd r.num s.den)
    let G₂ := signNorm (AzMvPolynomial.gcd s.num r.den)
    let nm := Azurite.ExactDiv.exactDiv r.num G₁ * Azurite.ExactDiv.exactDiv s.num G₂
    let dn := Azurite.ExactDiv.exactDiv r.den G₂ * Azurite.ExactDiv.exactDiv s.den G₁
    if h : nm.intContent = 1 ∧ dn.intContent = 1 ∧ (0 : AzInt) < nm.leadingCoeff
        ∧ (0 : AzInt) < dn.leadingCoeff ∧ AzMvPolynomial.coprime nm dn = true
        ∧ (r.factor * s.factor = 0 → nm = 1 ∧ dn = 1) then
      ⟨r.factor * s.factor, nm, dn, h.1, h.2.1, h.2.2.1, h.2.2.2.1,
        h.2.2.2.2.1, h.2.2.2.2.2⟩
    else 0

instance : Mul (AzMvRationalFunction n ord) := ⟨mul⟩

/-- **Division**: multiply by the reciprocal (the reciprocal is `O(1)`, so
this is exactly one cross-gcd multiplication; `r / 0 = 0`). -/
def div (r s : AzMvRationalFunction n ord) : AzMvRationalFunction n ord :=
  r * s⁻¹

instance : Div (AzMvRationalFunction n ord) := ⟨div⟩

/-- **Addition** (the `AzRat.add` Knuth pattern, polynomial-lifted, with the
factored-form subtleties): the scalar factors cross-multiply into the combined
numerator `T := a₁b₂·N₁·(D₂/G) + a₂b₁·N₂·(D₁/G)` where `G := signNorm (gcd D₁ D₂)`;
when `G` is a constant (`totalDegree 0`, i.e. coprime denominator parts) no
further polynomial reduction is needed (fast path); otherwise the only possible
common part is confined to `G`, so the second gcd is the small
`H := signNorm (gcd T₀ G)` and the denominator part is `(D₁/G)·(D₂/H)`. Finally
the content and sign of the numerator extract into the rational factor
(`b₁b₂` joins its denominator). `signNorm` normalizes the (tower-normalized,
not `ord`-leading-positive) multivariate gcds, as in `ofNumDen`/`mul`.
(Invariant checks decidable; fallback `0` unreachable — proven in the `Equiv`
layer.) -/
def add (r s : AzMvRationalFunction n ord) : AzMvRationalFunction n ord :=
  if r.factor = 0 then s
  else if s.factor = 0 then r
  else
    let a₁ : AzInt := ⟨r.factor.sign, r.factor.num, r.factor.zero_sign⟩
    let b₁ : AzInt := ⟨true, r.factor.den, fun _ => rfl⟩
    let a₂ : AzInt := ⟨s.factor.sign, s.factor.num, s.factor.zero_sign⟩
    let b₂ : AzInt := ⟨true, s.factor.den, fun _ => rfl⟩
    let G := signNorm (AzMvPolynomial.gcd r.den s.den)
    let Td : AzMvPolynomial n AzInt ord × AzMvPolynomial n AzInt ord :=
      if G.totalDegree = 0 then
        ((a₁ * b₂) • (r.num * s.den) + (a₂ * b₁) • (s.num * r.den),
         r.den * s.den)
      else
        let D₁' := Azurite.ExactDiv.exactDiv r.den G
        let D₂' := Azurite.ExactDiv.exactDiv s.den G
        let T₀ := (a₁ * b₂) • (r.num * D₂') + (a₂ * b₁) • (s.num * D₁')
        if T₀ = 0 then (0, 1)
        else
          let H := signNorm (AzMvPolynomial.gcd T₀ G)
          (Azurite.ExactDiv.exactDiv T₀ H, D₁' * Azurite.ExactDiv.exactDiv s.den H)
    if Td.1 = 0 then 0
    else
      let a := signedIntContent Td.1
      let nm := primPos Td.1
      if h : nm.intContent = 1 ∧ Td.2.intContent = 1 ∧ (0 : AzInt) < nm.leadingCoeff
          ∧ (0 : AzInt) < Td.2.leadingCoeff ∧ AzMvPolynomial.coprime nm Td.2 = true
          ∧ (AzRat.ofAzInts a (b₁ * b₂) = 0 → nm = 1 ∧ Td.2 = 1) then
        ⟨AzRat.ofAzInts a (b₁ * b₂), nm, Td.2, h.1, h.2.1, h.2.2.1, h.2.2.2.1,
          h.2.2.2.2.1, h.2.2.2.2.2⟩
      else 0

instance : Add (AzMvRationalFunction n ord) := ⟨add⟩

/-- **Subtraction**: add the negation (negation is `O(1)`). -/
def sub (r s : AzMvRationalFunction n ord) : AzMvRationalFunction n ord :=
  r + (-s)

instance : Sub (AzMvRationalFunction n ord) := ⟨sub⟩

/-- **Exponentiation by `ℕ`** — fully componentwise, the factored form's third
free operation: no gcd at all. The parts stay coprime (powers of coprime
polynomials are coprime), primitive (Gauss), and positive-leading (powers of
positives), and the scalar factor powers as an `AzRat`. The `AzMvPolynomial`
`^` is the sliding-window npow. The edges come out natively: `m = 0` gives
`1·(1/1) = 1` and a zero factor keeps parts `1` since `1 ^ m = 1`. (Invariant
checks decidable; fallback `0` unreachable — proven in the `Equiv` layer.) -/
def pow (r : AzMvRationalFunction n ord) (m : ℕ) : AzMvRationalFunction n ord :=
  let f := r.factor.pow m
  let nm := r.num ^ m
  let dn := r.den ^ m
  if h : nm.intContent = 1 ∧ dn.intContent = 1 ∧ (0 : AzInt) < nm.leadingCoeff
      ∧ (0 : AzInt) < dn.leadingCoeff ∧ AzMvPolynomial.coprime nm dn = true
      ∧ (f = 0 → nm = 1 ∧ dn = 1) then
    ⟨f, nm, dn, h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩
  else 0

/-- **Exponentiation by `ℤ`**: a `ℕ`-power plus (for negative exponents) one
`O(1)` reciprocal. -/
def zpow (r : AzMvRationalFunction n ord) (z : ℤ) : AzMvRationalFunction n ord :=
  if 0 ≤ z then pow r z.toNat else (pow r (-z).toNat)⁻¹

-- ═══════════════════════════════════════════════════════════════════
-- Tests
-- ═══════════════════════════════════════════════════════════════════

section Tests

private instance : Fact (2 ≤ 26) := ⟨by omega⟩

private def r2 (s : String) : AzMvRationalFunction 2 .Degrevlex :=
  (parseStrWith (XyzVar 2) s).getD 0

private def render (r : AzMvRationalFunction 2 .Degrevlex) : String :=
  toStrWith (XyzVar 2) r

-- negation
#guard render (-(r2 "(x*y-1)/2")) == "(-x*y+1)/2"
#guard render (-(r2 "-3/4")) == "3/4"
#guard render (-(0 : AzMvRationalFunction 2 .Degrevlex)) == "0"
-- double negation is the identity
#guard -(-(r2 "(x^2+y^2)/(x-y)")) == r2 "(x^2+y^2)/(x-y)"
-- reciprocal: swap the parts
#guard render ((r2 "(x^2+y^2)/(x-y)")⁻¹) == "(x-y)/(x^2+y^2)"
#guard render ((r2 "-3/4")⁻¹) == "-4/3"
#guard render ((0 : AzMvRationalFunction 2 .Degrevlex)⁻¹) == "0"
#guard render ((r2 "3*x^2/(x+y)")⁻¹) == "(x+y)/(3*x^2)"
-- double reciprocal is the identity
#guard ((r2 "(x^2+y^2)/(x-y)")⁻¹)⁻¹ == r2 "(x^2+y^2)/(x-y)"
-- multiplication: cross-reduction, contents into the factor
#guard render (r2 "(x*y-1)/2" * r2 "4/(x*y-1)") == "2"
#guard render (r2 "(x^2-y^2)/(x+2*y)" * r2 "(x+2*y)/(x+y)") == "x-y"
#guard render (r2 "2*x/3" * r2 "3/(2*x)") == "1"
#guard render (r2 "x*y/2" * (0 : AzMvRationalFunction 2 .Degrevlex)) == "0"
#guard render (r2 "x*y/2" * (1 : AzMvRationalFunction 2 .Degrevlex)) == "x*y/2"
-- division
#guard render (r2 "(x^2-y^2)/2" / r2 "(x-y)/2") == "x+y"
#guard render (r2 "x*y/2" / r2 "x*y/2") == "1"
#guard render (r2 "x*y/2" / (0 : AzMvRationalFunction 2 .Degrevlex)) == "0"
#guard render (r2 "3/4" / r2 "x") == "3/(4*x)"
-- addition: coprime-denominator fast path
#guard render (r2 "(x-1)/2" + r2 "(x+1)/2") == "x"
#guard render (r2 "1/2" + r2 "1/3") == "5/6"
#guard render (r2 "x" + r2 "1/x") == "(x^2+1)/x"
-- addition: common-denominator-factor path
#guard render (r2 "1/x" + r2 "1/x^2") == "(x+1)/x^2"
#guard render (r2 "1/(x*y)" + r2 "1/(x*y)") == "2/(x*y)"
#guard render (r2 "1/(x-y)" + r2 "1/(x+y)") == "2*x/(x^2-y^2)"
-- cancellation to zero and identities
#guard (r2 "(x^2+y^2)/(x-y)" + (-(r2 "(x^2+y^2)/(x-y)"))) == 0
#guard render (r2 "x*y/2" + (0 : AzMvRationalFunction 2 .Degrevlex)) == "x*y/2"
#guard render ((0 : AzMvRationalFunction 2 .Degrevlex) + r2 "x*y/2") == "x*y/2"
-- subtraction
#guard render (r2 "1/(x-y)" - r2 "1/(x+y)") == "2*y/(x^2-y^2)"
#guard render (r2 "x*y" - r2 "x*y") == "0"
#guard render (r2 "(x^2-y^2)/(x-y)" - r2 "x") == "y"
-- exponentiation: componentwise, no reduction
#guard pow (r2 "(x*y+1)/(x-y)") 2 == r2 "(x^2*y^2+2*x*y+1)/(x^2-2*x*y+y^2)"
#guard pow (r2 "x/2") 3 == r2 "x^3/8"
#guard pow (r2 "(x^2+y^2)/(x-y)") 0 == 1
#guard pow (0 : AzMvRationalFunction 2 .Degrevlex) 3 == 0
#guard zpow (r2 "x*y/2") (-2) == r2 "4/(x^2*y^2)"
#guard zpow (r2 "(x^2+y^2)/(x-y)") 0 == 1

end Tests

end Azurite.AzMvRationalFunction
