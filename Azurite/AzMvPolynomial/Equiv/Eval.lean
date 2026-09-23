/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

/-
  Equivalence between `AzMvPolynomial.eval` and `MvPolynomial.eval`.
-/
import Azurite.AzMvPolynomial.Eval
import Azurite.AzMvPolynomial.Equiv.Basic

namespace Azurite

open MonomialOrder MonicMonomial Monomial MvPolynomial

variable {R : Type _} [CommSemiring R] {n : ℕ} {ord : MonomialOrder}

/-! ### Monomial-level equivalence -/

/-- Evaluating a monomial via `Monomial.eval` agrees with `MvPolynomial.eval`
    applied to `Monomial.toMvPoly`. -/
theorem Monomial.eval_eq_mvPoly_eval [DecidableEq R]
    (m : Monomial n R ord) (f : Fin n → R) :
    m.eval f = MvPolynomial.eval f m.toMvPoly := by
  simp only [Monomial.eval, Monomial.toMvPoly, eval_monomial]
  congr 1
  simp only [MonicMonomial.eval, MonicMonomial.toFinsupp]
  rw [Finsupp.onFinset_prod _ (by intros; simp)]

/-! ### Polynomial-level equivalence -/

private theorem foldl_eval_eq [DecidableEq R]
    (l : List (Monomial n R ord)) (f : Fin n → R) (acc : R)
    (pacc : MvPolynomial (Fin n) R)
    (hacc : acc = MvPolynomial.eval f pacc) :
    l.foldl (fun a m => a + m.eval f) acc =
    MvPolynomial.eval f (l.foldl (fun a m => a + m.toMvPoly) pacc) := by
  induction l generalizing acc pacc with
  | nil => exact hacc
  | cons m t ih =>
    simp only [List.foldl_cons]
    apply ih
    rw [hacc, map_add, Monomial.eval_eq_mvPoly_eval]

/-- Evaluating an `AzMvPolynomial` agrees with `MvPolynomial.eval`
    applied to the equivalent `MvPolynomial`. -/
theorem AzMvPolynomial.eval_eq_mvPoly_eval [DecidableEq R]
    (p : AzMvPolynomial n R ord) (f : Fin n → R) :
    p.eval f = MvPolynomial.eval f p.toMvPoly := by
  simp only [AzMvPolynomial.eval, AzMvPolynomial.toMvPoly]
  rw [← Array.foldl_toList, ← Array.foldl_toList]
  exact foldl_eval_eq p.terms.toList f 0 0 (by simp)

/-- Evaluating an `MvPolynomial` via `MvPolynomial.eval` agrees with
    `AzMvPolynomial.eval` applied to `ofMvPoly`. -/
theorem eval_ofMvPoly [DecidableEq R]
    (p : MvPolynomial (Fin n) R) (f : Fin n → R) :
    (AzMvPolynomial.ofMvPoly p : AzMvPolynomial n R ord).eval f =
    MvPolynomial.eval f p := by
  rw [AzMvPolynomial.eval_eq_mvPoly_eval, toMvPoly_ofMvPoly]

end Azurite
