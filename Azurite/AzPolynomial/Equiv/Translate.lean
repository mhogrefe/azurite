import Azurite.AzPolynomial.Translate
import Azurite.AzPolynomial.Equiv.Comp
import Mathlib.Algebra.Polynomial.Eval.Degree

/-!
# Equivalence: AzPolynomial.translate ↔ Polynomial.comp (X - C c)

Proves that `AzPolynomial.translate p c` agrees with Mathlib's
`Polynomial.comp p (X - C c)`, and establishes the root translation property.

## Main results

- `toPoly_xSubC` — `toPoly (xSubC c) = X - C c`
- `toPoly_translate` — `toPoly (translate p c) = (toPoly p).comp (X - C c)`
- `ofPoly_translate` — `(ofPoly p).translate c = ofPoly (p.comp (X - C c))`
- `eval_translate` — `eval r (toPoly (translate p c)) = eval (r - c) (toPoly p)`
- `isRoot_translate_iff` — root of `P(X-c)` at `r` ↔ root of `P` at `r-c`
- `isRoot_translate_map_iff` — for `f : R →+* S`, root of `map f (P(X-c))` at `z` ↔ root of `map f P` at `z - f(c)`
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

end Azurite.AzPolynomial
