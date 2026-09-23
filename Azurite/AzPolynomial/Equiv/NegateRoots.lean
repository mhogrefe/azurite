import Azurite.AzPolynomial.NegateRoots
import Azurite.AzPolynomial.Equiv.Add

/-!
# Equivalence: AzPolynomial.negateRoots ↔ Polynomial.comp (-X)

Proves that `AzPolynomial.negateRoots p` agrees with Mathlib's
`Polynomial.comp p (-X)`, and establishes the root negation property.

## Main results

- `Polynomial.coeff_comp_neg_X` — `(q.comp (-X)).coeff n = (-1)^n * q.coeff n`
- `toPoly_negateRoots` — `toPoly (negateRoots p) = (toPoly p).comp (-X)`
- `ofPoly_negateRoots` — `(ofPoly q).negateRoots = ofPoly (q.comp (-X))`
- `eval_negateRoots` — `eval r (toPoly (negateRoots p)) = eval (-r) (toPoly p)`
- `isRoot_negateRoots_iff` — root of `P(-X)` at `r` ↔ root of `P` at `-r`
- `isRoot_negateRoots_map_iff` — for `f : R →+* S`, root of `map f (P(-X))` at `z`
  ↔ root of `map f P` at `-z`
- `negateRoots_negateRoots`, `negateRoots_eq_zero_iff` — root negation is an
  involution, hence preserves nonvanishing
-/

set_option autoImplicit false

open Polynomial

/-- The coefficient of `X^n` in `q(−X)` is `(−1)^n` times that of `q`. -/
theorem Polynomial.coeff_comp_neg_X {R : Type _} [CommRing R] (q : R[X]) (n : ℕ) :
    (q.comp (-Polynomial.X)).coeff n = (-1) ^ n * q.coeff n := by
  induction q using Polynomial.induction_on' with
  | add p q hp hq => simp [add_comp, hp, hq, mul_add]
  | monomial e a =>
    rw [monomial_comp, neg_pow, coeff_monomial,
      show Polynomial.C a * ((-1) ^ e * Polynomial.X ^ e)
          = Polynomial.C ((-1) ^ e * a) * Polynomial.X ^ e by
        rw [map_mul, map_pow, map_neg, map_one]; ring,
      coeff_C_mul_X_pow]
    by_cases h : n = e
    · subst h; rw [ite_eq_left rfl, ite_eq_left rfl]
    · rw [ite_eq_right h, ite_eq_right (fun he : e = n => h he.symm), mul_zero]

namespace Azurite.AzPolynomial

variable {R : Type _} [CommRing R] [DecidableEq R]

omit [DecidableEq R] in
/-- **Forward equivalence.** `toPoly (negateRoots p) = (toPoly p).comp (-X)`. -/
@[simp] theorem toPoly_negateRoots (p : AzPolynomial R) :
    AzPolynomial.toPoly p.negateRoots = (AzPolynomial.toPoly p).comp (-Polynomial.X) := by
  ext n
  rw [AzPolynomial.coeff_toPoly, Polynomial.coeff_comp_neg_X, AzPolynomial.coeff_toPoly,
    coeff_negateRoots]

/-- **Backward equivalence.** `ofPoly` preserves root negation. -/
@[simp] theorem ofPoly_negateRoots (q : Polynomial R) :
    (AzPolynomial.ofPoly q).negateRoots = AzPolynomial.ofPoly (q.comp (-Polynomial.X)) := by
  rw [← toPoly_inj, toPoly_negateRoots, toPoly_ofPoly, toPoly_ofPoly]

omit [DecidableEq R] in
/-- **Evaluation identity.** `P(−X)` evaluated at `r` equals `P(−r)`. -/
theorem eval_negateRoots (p : AzPolynomial R) (r : R) :
    Polynomial.eval r (AzPolynomial.toPoly p.negateRoots)
      = Polynomial.eval (-r) (AzPolynomial.toPoly p) := by
  rw [toPoly_negateRoots, Polynomial.eval_comp, Polynomial.eval_neg, Polynomial.eval_X]

omit [DecidableEq R] in
/-- **Root negation.** `r` is a root of `P(−X)` iff `−r` is a root of `P`:
the roots of `negateRoots p` are the roots of `p`, each negated. -/
theorem isRoot_negateRoots_iff (p : AzPolynomial R) (r : R) :
    Polynomial.IsRoot (AzPolynomial.toPoly p.negateRoots) r ↔
    Polynomial.IsRoot (AzPolynomial.toPoly p) (-r) := by
  simp only [Polynomial.IsRoot, eval_negateRoots]

omit [DecidableEq R] in
/-- **Root negation across a ring homomorphism.**
    If `f : R →+* S` (e.g. `ℤ →+* ℂ`), then `z ∈ S` is a root of `P(−X)` (with
    coefficients mapped via `f`) iff `−z` is a root of `P` (mapped via `f`).

    **Application:** if `P ∈ ℤ[X]` is a defining polynomial of an algebraic
    number `α`, then `negateRoots P` is a defining polynomial of `−α`, of the
    same degree. -/
theorem isRoot_negateRoots_map_iff {S : Type _} [CommRing S]
    (f : R →+* S) (p : AzPolynomial R) (z : S) :
    Polynomial.IsRoot (Polynomial.map f (AzPolynomial.toPoly p.negateRoots)) z ↔
    Polynomial.IsRoot (Polynomial.map f (AzPolynomial.toPoly p)) (-z) := by
  simp only [Polynomial.IsRoot, toPoly_negateRoots, Polynomial.map_comp, Polynomial.map_neg,
    Polynomial.map_X, Polynomial.eval_comp, Polynomial.eval_neg, Polynomial.eval_X]

/-- Root negation is an involution. -/
@[simp] theorem negateRoots_negateRoots (p : AzPolynomial R) : p.negateRoots.negateRoots = p := by
  rw [← toPoly_inj, toPoly_negateRoots, toPoly_negateRoots, Polynomial.comp_assoc]
  simp

/-- Root negation preserves nonvanishing. -/
theorem negateRoots_eq_zero_iff (p : AzPolynomial R) : p.negateRoots = 0 ↔ p = 0 :=
  ⟨fun h => by
    have h2 := congrArg negateRoots h
    rwa [negateRoots_negateRoots, negateRoots_zero] at h2,
   fun h => by rw [h, negateRoots_zero]⟩

end Azurite.AzPolynomial
