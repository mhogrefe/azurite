import Azurite.AzMvPolynomial.Equiv.ToAzPolynomial
import Azurite.AzMvPolynomial.Equiv.OfAzPolynomial
import Azurite.AzMvPolynomial.Equiv.Algebra
import Azurite.AzPolynomial.Equiv.Algebra
import Azurite.AzPolynomial.Equiv.Monomial
import Azurite.AzPolynomial.Equiv.Mul
import Mathlib.Algebra.MvPolynomial.Equiv

/-!
# `finOneAlgEquiv` for AzMvPolynomial

The `R`-algebra isomorphism between a one-variable `AzMvPolynomial` and
the Azurite univariate polynomial type:

```
AzMvPolynomial 1 R ord  ≃ₐ[R]  AzPolynomial R
```

The forward map is `AzMvPolynomial.toAzPolynomial`, the inverse is
`AzPolynomial.toAzMvPolynomial ⟨0, _⟩`. The bridge theorems
`toPoly_toAzPolynomial` and `toMvPoly_toAzMvPolynomial` reduce the
identity to a round-trip on Mathlib `MvPolynomial (Fin 1)` / `Polynomial`
which is closed by induction.

Fin-only counterpart of Mathlib's `MvPolynomial.pUnitAlgEquiv`.
-/

namespace Azurite

open AzMvPolynomial

variable {R : Type _} [CommSemiring R] [NoZeroDivisors R] [DecidableEq R]
    {ord : MonomialOrder}

/-- The unique element of `Fin 1`. -/
def finOneZero : Fin 1 := ⟨0, Nat.zero_lt_one⟩

/-! ### Round-trip identities on Mathlib `MvPolynomial (Fin 1)` / `Polynomial` -/

omit [NoZeroDivisors R] [DecidableEq R] in
private lemma mvPolyFinOne_roundtrip (p : MvPolynomial (Fin 1) R) :
    Polynomial.eval₂ MvPolynomial.C
        (MvPolynomial.X (finOneZero : Fin 1) : MvPolynomial (Fin 1) R)
        (MvPolynomial.eval₂ Polynomial.C
          (fun _ : Fin 1 => Polynomial.X) p) = p := by
  induction p using MvPolynomial.induction_on with
  | C r => simp
  | add p q hp hq =>
    rw [MvPolynomial.eval₂_add, Polynomial.eval₂_add, hp, hq]
  | mul_X p i hp =>
    have hi : i = finOneZero := by
      ext; have := i.isLt; omega
    subst hi
    rw [MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X, Polynomial.eval₂_mul,
        hp, Polynomial.eval₂_X]

omit [NoZeroDivisors R] [DecidableEq R] in
private lemma polynomial_roundtrip (p : Polynomial R) :
    MvPolynomial.eval₂ Polynomial.C (fun _ : Fin 1 => Polynomial.X)
        (Polynomial.eval₂ MvPolynomial.C
          (MvPolynomial.X (finOneZero : Fin 1) : MvPolynomial (Fin 1) R) p) = p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [Polynomial.eval₂_add, MvPolynomial.eval₂_add, hp, hq]
  | monomial k r =>
    rw [Polynomial.eval₂_monomial, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_C,
        MvPolynomial.eval₂_pow, MvPolynomial.eval₂_X,
        Polynomial.C_mul_X_pow_eq_monomial]

/-! ### Forward and backward bridges through `toMvPoly` / `toPoly` -/

omit [NoZeroDivisors R] in
lemma toAzPolynomial_toAzMvPolynomial_roundtrip
    (p : AzMvPolynomial 1 R ord) :
    (p.toAzPolynomial).toAzMvPolynomial finOneZero ord = p :=
  toMvPoly_injective (by
    rw [toMvPoly_toAzMvPolynomial, toPoly_toAzPolynomial,
        mvPolyFinOne_roundtrip])

omit [NoZeroDivisors R] in
lemma toAzMvPolynomial_toAzPolynomial_roundtrip (q : AzPolynomial R) :
    (AzPolynomial.toAzMvPolynomial finOneZero ord q :
        AzMvPolynomial 1 R ord).toAzPolynomial = q := by
  apply toPoly_inj.mp
  rw [toPoly_toAzPolynomial, toMvPoly_toAzMvPolynomial, polynomial_roundtrip]

/-! ### Ring-hom axioms via the `toPoly` bridge -/

omit [NoZeroDivisors R] in
private lemma toAzPolynomial_add (p q : AzMvPolynomial 1 R ord) :
    (p + q).toAzPolynomial = p.toAzPolynomial + q.toAzPolynomial := by
  apply toPoly_inj.mp
  rw [AzPolynomial.toPoly_add, toPoly_toAzPolynomial, toPoly_toAzPolynomial,
      toPoly_toAzPolynomial, toMvPoly_add, MvPolynomial.eval₂_add]

private lemma toAzPolynomial_mul (p q : AzMvPolynomial 1 R ord) :
    (p * q).toAzPolynomial = p.toAzPolynomial * q.toAzPolynomial := by
  apply toPoly_inj.mp
  rw [AzPolynomial.toPoly_mul, toPoly_toAzPolynomial, toPoly_toAzPolynomial,
      toPoly_toAzPolynomial, toMvPoly_mul, MvPolynomial.eval₂_mul]

omit [NoZeroDivisors R] in
private lemma toAzPolynomial_C_eq (r : R) :
    (AzMvPolynomial.C r : AzMvPolynomial 1 R ord).toAzPolynomial =
      (AzPolynomial.C r : AzPolynomial R) := by
  apply toPoly_inj.mp
  rw [toPoly_toAzPolynomial, toMvPoly_C, MvPolynomial.eval₂_C,
      AzPolynomial.toPoly_C]

private lemma toAzPolynomial_algebraMap (r : R) :
    (algebraMap R (AzMvPolynomial 1 R ord) r).toAzPolynomial =
      algebraMap R (AzPolynomial R) r := by
  show (AzMvPolynomial.C r : AzMvPolynomial 1 R ord).toAzPolynomial =
        (AzPolynomial.C r : AzPolynomial R)
  exact toAzPolynomial_C_eq r

/-! ### Bundled `R`-algebra isomorphism -/

/-- `R`-algebra isomorphism between one-variable `AzMvPolynomial` and
    `AzPolynomial`. Fin-only counterpart of `MvPolynomial.pUnitAlgEquiv`. -/
def AzMvPolynomial.finOneAlgEquiv :
    AzMvPolynomial 1 R ord ≃ₐ[R] AzPolynomial R where
  toFun := AzMvPolynomial.toAzPolynomial
  invFun := fun q => AzPolynomial.toAzMvPolynomial finOneZero ord q
  left_inv := toAzPolynomial_toAzMvPolynomial_roundtrip
  right_inv := toAzMvPolynomial_toAzPolynomial_roundtrip
  map_add' := toAzPolynomial_add
  map_mul' := toAzPolynomial_mul
  commutes' := toAzPolynomial_algebraMap

end Azurite
