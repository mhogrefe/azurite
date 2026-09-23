/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.AzMvRationalFunction.OfAzRationalFunction
import Azurite.AzMvRationalFunction.Equiv.Basic
import Azurite.AzRationalFunction.Equiv.Basic
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.RingTheory.Localization.FractionRing

/-!
# Correctness of `AzRationalFunction.toAzMvRationalFunction`

The lift into the `i`-th variable commutes with the field embedding
`ℚ(x) ↪ ℚ(x⃗)` induced by `x ↦ x_i`:

`toMvRatFunc (r.toAzMvRationalFunction i ord) = fracEmbed i (toRatFunc r)`,

where `fracEmbed i` is the fraction-field map induced (via `IsFractionRing.map`)
by the single-variable polynomial embedding `embVar i : ℚ[x] →+* ℚ[x⃗]`.
-/

namespace Azurite.AzMvRationalFunction

open Azurite.AzMvPolynomial

variable {n : ℕ} {ord : MonomialOrder}

/-- The single-variable polynomial embedding `x ↦ x_i` is injective (it has a
left inverse `x_i ↦ x`, other variables `↦ 0`). -/
theorem embVar_injective (i : Fin n) :
    Function.Injective (AzMvPolynomial.embVar i) := by
  have hleft : (MvPolynomial.eval₂Hom (Polynomial.C : ℚ →+* Polynomial ℚ)
        (fun j : Fin n => if j = i then Polynomial.X else 0)).comp
        (AzMvPolynomial.embVar i) = RingHom.id (Polynomial ℚ) := by
    apply Polynomial.ringHom_ext
    · intro c; simp [AzMvPolynomial.embVar]
    · simp [AzMvPolynomial.embVar]
  exact Function.LeftInverse.injective (g := MvPolynomial.eval₂Hom (Polynomial.C)
    (fun j : Fin n => if j = i then Polynomial.X else 0))
    (fun x => by have := RingHom.congr_fun hleft x; simpa using this)

/-- The fraction-field embedding `ℚ(x) →+* ℚ(x⃗)` induced by `embVar i`. -/
noncomputable def fracEmbed (i : Fin n) :
    RatFunc ℚ →+* FractionRing (MvPolynomial (Fin n) ℚ) :=
  IsFractionRing.map (embVar_injective i)

/-- `fracEmbed` sends `ℚ[x]`-images to `ℚ[x⃗]`-images via `embVar`. -/
theorem fracEmbed_algebraMap_poly (i : Fin n) (q : Polynomial ℚ) :
    fracEmbed i (algebraMap (Polynomial ℚ) (RatFunc ℚ) q)
      = algebraMap (MvPolynomial (Fin n) ℚ) (FractionRing (MvPolynomial (Fin n) ℚ))
          (AzMvPolynomial.embVar i q) := by
  rw [fracEmbed, IsFractionRing.map, IsLocalization.map_eq]

/-- `fracEmbed` fixes the scalar `ℚ`-embedding. -/
theorem fracEmbed_algebraMap_scalar (i : Fin n) (c : ℚ) :
    fracEmbed i (algebraMap ℚ (RatFunc ℚ) c)
      = algebraMap ℚ (FractionRing (MvPolynomial (Fin n) ℚ)) c := by
  have h1 : (algebraMap ℚ (RatFunc ℚ)) c
      = algebraMap (Polynomial ℚ) (RatFunc ℚ) (Polynomial.C c) := by
    rw [IsScalarTower.algebraMap_apply ℚ (Polynomial ℚ) (RatFunc ℚ)]; rfl
  have h2 : algebraMap ℚ (FractionRing (MvPolynomial (Fin n) ℚ)) c
      = algebraMap (MvPolynomial (Fin n) ℚ) (FractionRing (MvPolynomial (Fin n) ℚ))
          (MvPolynomial.C c) := by
    rw [IsScalarTower.algebraMap_apply ℚ (MvPolynomial (Fin n) ℚ)
      (FractionRing (MvPolynomial (Fin n) ℚ))]; rfl
  rw [h1, fracEmbed_algebraMap_poly, h2,
    show AzMvPolynomial.embVar i (Polynomial.C c) = MvPolynomial.C c from by
      simp [AzMvPolynomial.embVar]]

/-- The `ℚ[x⃗]`-image of a lift is the `x_i`-embedding of the univariate
`ℚ[x]`-image. -/
theorem toMvPolyQ_toAzMvPolynomial (i : Fin n) (P : AzPolynomial AzInt) :
    toMvPolyQ (P.toAzMvPolynomial i ord)
      = AzMvPolynomial.embVar i (Azurite.AzRationalFunction.toPolyQ P) := by
  rw [toMvPolyQ_eq_ratImg, AzMvPolynomial.ratImg_toAzMvPolynomial]
  rfl

/-- **Correctness**: lifting into the `i`-th variable commutes with the field
embedding `ℚ(x) ↪ ℚ(x⃗)`. -/
theorem toMvRatFunc_toAzMvRationalFunction (i : Fin n) (r : AzRationalFunction) :
    toMvRatFunc (r.toAzMvRationalFunction i ord)
      = fracEmbed i (Azurite.AzRationalFunction.toRatFunc r) := by
  rw [toMvRatFunc, AzRationalFunction.toAzMvRationalFunction_factor,
    AzRationalFunction.toAzMvRationalFunction_num,
    AzRationalFunction.toAzMvRationalFunction_den,
    toMvPolyQ_toAzMvPolynomial, toMvPolyQ_toAzMvPolynomial,
    Azurite.AzRationalFunction.toRatFunc, map_mul, map_div₀,
    fracEmbed_algebraMap_scalar, fracEmbed_algebraMap_poly, fracEmbed_algebraMap_poly]

/-- The lift is injective (distinct univariate representations lift to distinct
multivariate ones). -/
theorem toAzMvRationalFunction_injective (i : Fin n) :
    Function.Injective
      (fun r : AzRationalFunction => r.toAzMvRationalFunction i ord) := by
  intro r s h
  apply Azurite.AzRationalFunction.toRatFunc_injective
  apply (fracEmbed i).injective
  rw [← toMvRatFunc_toAzMvRationalFunction, ← toMvRatFunc_toAzMvRationalFunction]
  exact congrArg toMvRatFunc h

end Azurite.AzMvRationalFunction
