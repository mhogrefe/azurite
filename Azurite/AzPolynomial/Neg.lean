/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzPolynomial.Basic


variable {R : Type _} [Ring R]

namespace Azurite
namespace AzPolynomial

/-- Negates a `AzPolynomial R` by mapping negation over its coefficients. -/
instance instNegAzPolynomial : Neg (AzPolynomial R) where
  neg p := mapZeroInjective (fun x => -x) (fun r => ⟨fun hr => neg_eq_zero.mp hr, fun hr => by simp [hr]⟩) p


@[simp] lemma coeff_neg (p : AzPolynomial R) (i : ℕ) : (-p).coeff i = - p.coeff i := by
  dsimp [coeff, Neg.neg, instNegAzPolynomial, mapZeroInjective]
  rcases hp : p.coeffs[i]? with _ | c
  · have hw : (p.coeffs.map (fun x => -x))[i]? = none := by rw [Array.getElem?_map, hp]; rfl
    rw [hw]
    simp
  · have hw : (p.coeffs.map (fun x => -x))[i]? = some (-c) := by rw [Array.getElem?_map, hp]; rfl
    rw [hw]
    simp

end AzPolynomial
end Azurite
