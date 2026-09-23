/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzMvPolynomial.Equiv.Eval2
import Azurite.AzMvPolynomial.Equiv.Algebra
import Mathlib.Algebra.MvPolynomial.Equiv

/-!
# `finZeroAlgEquiv` for AzMvPolynomial

The `R`-algebra isomorphism between a zero-variable `AzMvPolynomial` and the
base ring:

```
AzMvPolynomial 0 R ord  ≃ₐ[R]  R
```

Forward: `p.eval₂ (RingHom.id R) Fin.elim0`, equivalently "extract the
constant coefficient". Inverse: `AzMvPolynomial.C`.

Fin-only counterpart of Mathlib's `MvPolynomial.isEmptyAlgEquiv`.
-/

namespace Azurite

open AzMvPolynomial

variable {R : Type _} [CommSemiring R] [NoZeroDivisors R] [DecidableEq R]
    {ord : MonomialOrder}

/-! ### Round-trip identity on Mathlib `MvPolynomial (Fin 0)` -/

omit [NoZeroDivisors R] [DecidableEq R] in
private lemma mvPolyFinZero_roundtrip (p : MvPolynomial (Fin 0) R) :
    MvPolynomial.C (MvPolynomial.eval₂ (RingHom.id R) Fin.elim0 p) = p := by
  induction p using MvPolynomial.induction_on with
  | C r => simp
  | add p q hp hq =>
    rw [MvPolynomial.eval₂_add, map_add, hp, hq]
  | mul_X p i hp => exact i.elim0

/-! ### Bundled `R`-algebra isomorphism -/

omit [NoZeroDivisors R] in
private lemma finZero_left_inv (p : AzMvPolynomial 0 R ord) :
    (AzMvPolynomial.C (p.eval₂ (RingHom.id R) Fin.elim0) :
        AzMvPolynomial 0 R ord) = p :=
  toMvPoly_injective (by
    rw [toMvPoly_C, AzMvPolynomial.toMvPoly_eval₂, mvPolyFinZero_roundtrip])

omit [NoZeroDivisors R] in
private lemma finZero_right_inv (r : R) :
    ((AzMvPolynomial.C r : AzMvPolynomial 0 R ord)).eval₂
        (RingHom.id R) Fin.elim0 = r := by
  rw [AzMvPolynomial.toMvPoly_eval₂, toMvPoly_C, MvPolynomial.eval₂_C,
      RingHom.id_apply]

omit [NoZeroDivisors R] in
private lemma finZero_map_add (p q : AzMvPolynomial 0 R ord) :
    (p + q).eval₂ (RingHom.id R) Fin.elim0 =
      p.eval₂ (RingHom.id R) Fin.elim0 + q.eval₂ (RingHom.id R) Fin.elim0 := by
  rw [AzMvPolynomial.toMvPoly_eval₂, AzMvPolynomial.toMvPoly_eval₂,
      AzMvPolynomial.toMvPoly_eval₂, toMvPoly_add, MvPolynomial.eval₂_add]

private lemma finZero_map_mul (p q : AzMvPolynomial 0 R ord) :
    (p * q).eval₂ (RingHom.id R) Fin.elim0 =
      p.eval₂ (RingHom.id R) Fin.elim0 * q.eval₂ (RingHom.id R) Fin.elim0 := by
  rw [AzMvPolynomial.toMvPoly_eval₂, AzMvPolynomial.toMvPoly_eval₂,
      AzMvPolynomial.toMvPoly_eval₂, toMvPoly_mul, MvPolynomial.eval₂_mul]

private lemma finZero_commutes (r : R) :
    (algebraMap R (AzMvPolynomial 0 R ord) r).eval₂
        (RingHom.id R) Fin.elim0 = r := by
  show (AzMvPolynomial.C r : AzMvPolynomial 0 R ord).eval₂
        (RingHom.id R) Fin.elim0 = r
  exact finZero_right_inv r

/-- `R`-algebra isomorphism between zero-variable `AzMvPolynomial` and `R`.
    Fin-only counterpart of `MvPolynomial.isEmptyAlgEquiv`. -/
def AzMvPolynomial.finZeroAlgEquiv :
    AzMvPolynomial 0 R ord ≃ₐ[R] R where
  toFun p := p.eval₂ (RingHom.id R) Fin.elim0
  invFun r := (AzMvPolynomial.C r : AzMvPolynomial 0 R ord)
  left_inv := finZero_left_inv
  right_inv := finZero_right_inv
  map_add' := finZero_map_add
  map_mul' := finZero_map_mul
  commutes' := finZero_commutes

end Azurite
