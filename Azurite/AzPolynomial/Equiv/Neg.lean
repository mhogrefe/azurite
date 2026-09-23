/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzPolynomial.Neg
import Azurite.AzPolynomial.Equiv.Basic

open Polynomial

variable {R : Type _} [Ring R]

namespace Azurite.AzPolynomial

lemma toPoly_map_neg (l : List R) : (l.map (-·)).toPoly = - l.toPoly := by
  induction l with
  | nil => simp [List.toPoly]
  | cons a as ih =>
    rw [List.map_cons]
    dsimp [List.toPoly]
    rw [ih]
    rw [map_neg, mul_neg]
    exact (neg_add (C a) (X * as.toPoly)).symm

@[simp] lemma toPoly_neg [DecidableEq R] (p : AzPolynomial R) : AzPolynomial.toPoly (-p) = - AzPolynomial.toPoly p := by
  change AzPolynomial.toPoly (mapZeroInjective _ _ p) = - AzPolynomial.toPoly p
  dsimp [AzPolynomial.mapZeroInjective, AzPolynomial.toPoly]
  have hw : (p.coeffs.map (fun x => -x)).toList = p.coeffs.toList.map (fun x => -x) := by simp
  rw [hw]
  exact toPoly_map_neg p.coeffs.toList

@[simp] lemma ofPoly_neg [DecidableEq R] (p : Polynomial R) : AzPolynomial.ofPoly (-p) = - AzPolynomial.ofPoly p := by
  apply equivPolynomial.injective
  change AzPolynomial.toPoly (AzPolynomial.ofPoly (-p)) = AzPolynomial.toPoly (- AzPolynomial.ofPoly p)
  rw [toPoly_ofPoly, toPoly_neg, toPoly_ofPoly]

end Azurite.AzPolynomial
