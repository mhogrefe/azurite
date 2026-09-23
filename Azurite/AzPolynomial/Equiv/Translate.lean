/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzPolynomial.Translate
import Azurite.AzPolynomial.Equiv.Comp
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.Polynomial.Taylor

/-!
# Equivalence: AzPolynomial.translate ↔ Polynomial.comp (X - C c)

Proves that `AzPolynomial.translate p c` agrees with Mathlib's
`Polynomial.comp p (X - C c)` — equivalently, with the Taylor expansion
`Polynomial.taylor (-c) p` — and establishes the root translation property.

## Main results

- `toPoly_xSubC` — `toPoly (xSubC c) = X - C c`
- `toPoly_translate` — `toPoly (translate p c) = (toPoly p).comp (X - C c)`
- `toPoly_translate_eq_taylor` — `toPoly (translate p c) = taylor (-c) (toPoly p)`
- `ofPoly_translate` — `(ofPoly p).translate c = ofPoly (p.comp (X - C c))`
- `eval_translate` — `eval r (toPoly (translate p c)) = eval (r - c) (toPoly p)`
- `isRoot_translate_iff` — root of `P(X-c)` at `r` ↔ root of `P` at `r-c`
- `isRoot_translate_map_iff` — for `f : R →+* S`, root of `map f (P(X-c))` at `z` ↔ root of `map f P` at `z - f(c)`
- `natDegree_translate`, `leadingCoeff_translate`, `translate_eq_zero_iff`,
  `monic_toPoly_translate_iff` — translation preserves the degree, the leading
  coefficient, nonvanishing, and monicity (unconditionally, via `taylor`)
-/

set_option autoImplicit false

open Polynomial

namespace Azurite.AzPolynomial

variable {R : Type _} [CommRing R] [DecidableEq R]

/-- `toPoly (xSubC c) = X - C c`. -/
@[simp] theorem toPoly_xSubC (c : R) :
    AzPolynomial.toPoly (xSubC c) = Polynomial.X - Polynomial.C c := by
  unfold xSubC; split
  · next h =>
    have : Subsingleton R := subsingleton_of_zero_eq_one (h ▸ rfl)
    rw [toPoly_zero]; exact (Subsingleton.elim _ _).symm
  · next h =>
    show AzPolynomial.toPoly ⟨#[-c, 1], _⟩ = _
    simp only [AzPolynomial.toPoly, List.toPoly, map_one, mul_zero, add_zero, mul_one,
               Polynomial.C_neg]
    rw [add_comm, sub_eq_add_neg]

/-- **Forward equivalence.** `toPoly (translate p c) = (toPoly p).comp (X - C c)`. -/
@[simp] theorem toPoly_translate (p : AzPolynomial R) (c : R) :
    AzPolynomial.toPoly (p.translate c) =
    (AzPolynomial.toPoly p).comp (Polynomial.X - Polynomial.C c) := by
  simp only [translate]; rw [toPoly_comp, toPoly_xSubC]

/-- **Backward equivalence.** `ofPoly` preserves translation. -/
@[simp] theorem ofPoly_translate (p : Polynomial R) (c : R) :
    (AzPolynomial.ofPoly p).translate c =
    AzPolynomial.ofPoly (p.comp (Polynomial.X - Polynomial.C c)) := by
  rw [← toPoly_inj, toPoly_translate]; simp [toPoly_ofPoly]

/-- **Evaluation identity.** `P(X-c)` evaluated at `r` equals `P(r-c)`. -/
theorem eval_translate (p : AzPolynomial R) (c r : R) :
    Polynomial.eval r (AzPolynomial.toPoly (p.translate c)) =
    Polynomial.eval (r - c) (AzPolynomial.toPoly p) := by
  rw [toPoly_translate, Polynomial.eval_comp, Polynomial.eval_sub,
      Polynomial.eval_X, Polynomial.eval_C]

/-- **Root translation.** `r` is a root of `P(X-c)` iff `r-c` is a root of `P`.

    Equivalently, the roots of `P(X-c)` are the roots of `P`, each shifted by `+c`:
    if `s` is a root of `P`, then `s + c` is a root of `P(X-c)`. -/
theorem isRoot_translate_iff (p : AzPolynomial R) (c r : R) :
    Polynomial.IsRoot (AzPolynomial.toPoly (p.translate c)) r ↔
    Polynomial.IsRoot (AzPolynomial.toPoly p) (r - c) := by
  simp only [Polynomial.IsRoot, eval_translate]

/-- **Root translation across a ring homomorphism.**
    If `f : R →+* S` is a ring homomorphism (e.g. `ℤ →+* ℂ` or `ℚ →+* ℂ`),
    then `z ∈ S` is a root of `P(X - c)` (with coefficients mapped via `f`)
    iff `z - f(c)` is a root of `P` (with coefficients mapped via `f`).

    **Application:** If `P ∈ ℤ[X]` represents the minimal polynomial of an
    algebraic number `α`, then the complex roots of `P(X - c)` are exactly
    `α₁ + c, α₂ + c, …` where `αᵢ` are the complex roots of `P`.
    This gives a minimal polynomial for `α + c` when `c ∈ ℚ`. -/
theorem isRoot_translate_map_iff {S : Type _} [CommRing S]
    (f : R →+* S) (p : AzPolynomial R) (c : R) (z : S) :
    Polynomial.IsRoot (Polynomial.map f (AzPolynomial.toPoly (p.translate c))) z ↔
    Polynomial.IsRoot (Polynomial.map f (AzPolynomial.toPoly p)) (z - f c) := by
  simp only [Polynomial.IsRoot, toPoly_translate, Polynomial.map_comp,
             Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C,
             Polynomial.eval_comp, Polynomial.eval_sub,
             Polynomial.eval_X, Polynomial.eval_C]

/-! ### Degree data

Translation is the Taylor expansion `taylor (-c)`, which preserves the degree, the
leading coefficient, nonvanishing, and monicity — unconditionally, over any
commutative ring. -/

/-- `translate` is Mathlib's Taylor expansion at `-c`. -/
theorem toPoly_translate_eq_taylor (p : AzPolynomial R) (c : R) :
    AzPolynomial.toPoly (p.translate c) = Polynomial.taylor (-c) (AzPolynomial.toPoly p) := by
  rw [toPoly_translate, Polynomial.taylor_apply, Polynomial.C_neg, ← sub_eq_add_neg]

/-- Translation preserves the degree. -/
theorem natDegree_translate (p : AzPolynomial R) (c : R) :
    (p.translate c).natDegree = p.natDegree := by
  rw [← AzPolynomial.natDegree_toPoly, toPoly_translate_eq_taylor, Polynomial.natDegree_taylor,
    AzPolynomial.natDegree_toPoly]

/-- Translation preserves the leading coefficient. -/
theorem leadingCoeff_translate (p : AzPolynomial R) (c : R) :
    (p.translate c).leadingCoeff = p.leadingCoeff := by
  rw [← leadingCoeff_toPoly, toPoly_translate_eq_taylor, Polynomial.leadingCoeff_taylor,
    leadingCoeff_toPoly]

/-- Translation preserves nonvanishing. -/
theorem translate_eq_zero_iff (p : AzPolynomial R) (c : R) :
    p.translate c = 0 ↔ p = 0 := by
  rw [← toPoly_inj (p := p.translate c) (q := 0), ← toPoly_inj (p := p) (q := 0), toPoly_zero,
    toPoly_translate_eq_taylor, ← map_zero (Polynomial.taylor (-c)),
    (Polynomial.taylor_injective (-c)).eq_iff, map_zero]

/-- Translation preserves monicity. -/
theorem monic_toPoly_translate_iff (p : AzPolynomial R) (c : R) :
    (AzPolynomial.toPoly (p.translate c)).Monic ↔ (AzPolynomial.toPoly p).Monic := by
  unfold Polynomial.Monic
  rw [leadingCoeff_toPoly, leadingCoeff_toPoly, leadingCoeff_translate]

end Azurite.AzPolynomial
