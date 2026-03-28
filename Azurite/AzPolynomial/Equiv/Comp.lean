import Azurite.AzPolynomial.Comp
import Azurite.AzPolynomial.Equiv.Algebra
import Azurite.AzPolynomial.Equiv.Monomial

/-!
# Equivalence: AzPolynomial.comp ↔ Polynomial.comp

Proves that `AzPolynomial.comp p q` (computable Horner composition)
agrees with Mathlib's `Polynomial.comp`, which is defined as `eval₂ C q p`.

## Main Theorems

- `toPoly_comp`: `toPoly (comp p q) = (toPoly p).comp (toPoly q)`
- `ofPoly_comp`: `comp (ofPoly p) (ofPoly q) = ofPoly (p.comp q)`

## Proof Strategy

1. **`toPoly_foldr_comp`**: Show that `toPoly` distributes through the `foldr`
   used by `comp`, mapping each `C a + acc * q` step to the corresponding
   `Polynomial.C a + acc * toPoly q` step.

2. **`list_foldr_eq_comp`**: Show that the Polynomial-side Horner `foldr`
   equals `Polynomial.comp` via `add_comp`, `C_comp`, `mul_comp`, `X_comp`.

3. Combine: `toPoly (comp p q)` → `foldr on Polynomial` → `comp on Polynomial`.

Requires `CommSemiring R` because `Polynomial.mul_comp` requires commutativity.
-/

open Azurite Azurite.AzPolynomial

variable {R : Type _} [CommSemiring R] [DecidableEq R]

/-- `toPoly` distributes through the Horner `foldr` defining `comp`. -/
private theorem toPoly_foldr_comp (l : List R) (q : AzPolynomial R) :
    AzPolynomial.toPoly (l.foldr (fun a acc => C a + acc * q) 0) =
    l.foldr (fun a acc => Polynomial.C a + acc * AzPolynomial.toPoly q) 0 := by
  induction l with
  | nil => exact toPoly_zero
  | cons hd tl ih =>
    simp only [List.foldr_cons]
    rw [toPoly_add, toPoly_mul, toPoly_C, ih]

omit [DecidableEq R] in
/-- The Horner `foldr` on `Polynomial` equals `Polynomial.comp` of `List.toPoly`. -/
private theorem list_foldr_eq_comp (l : List R) (q : Polynomial R) :
    l.foldr (fun a acc => Polynomial.C a + acc * q) 0 = (List.toPoly l).comp q := by
  induction l with
  | nil => simp [List.toPoly, Polynomial.zero_comp]
  | cons hd tl ih =>
    simp only [List.foldr_cons, List.toPoly, ih]
    rw [Polynomial.add_comp, Polynomial.C_comp, Polynomial.mul_comp, Polynomial.X_comp]
    ring

/-- Forward direction: `toPoly` preserves `AzPolynomial.comp`. -/
@[simp] theorem toPoly_comp (p q : AzPolynomial R) :
    AzPolynomial.toPoly (comp p q) = (AzPolynomial.toPoly p).comp (AzPolynomial.toPoly q) := by
  simp only [comp, ← Array.foldr_toList]
  rw [toPoly_foldr_comp, list_foldr_eq_comp]
  rfl

/-- Backward direction: `ofPoly` preserves `Polynomial.comp`. -/
@[simp] theorem ofPoly_comp (p q : Polynomial R) :
    comp (AzPolynomial.ofPoly p) (AzPolynomial.ofPoly q) = AzPolynomial.ofPoly (p.comp q) := by
  rw [← toPoly_inj]
  simp [toPoly_comp, toPoly_ofPoly]
