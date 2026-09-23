/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.BasuPollackRoy.Chapter4.Section4_7.ProjectiveProduct
import Azurite.BasuPollackRoy.Chapter3.Section3_5.SClass

/-!
# BPR §4.7: differentiability and the classes `𝒮^m` on projective space

Following BPR, differentiability and the smoothness classes `𝒮^m` on `ℙ_k(C)` are defined *chart by
chart*, using the realification `Cⁿ = R^{2n}` to import the affine theory of §3.5. Concretely, a
real-valued function on an open subset of `Cⁿ` is `𝒮^m` (`IsSFunctionC`) when its realification
`R^{2n} → R` is `𝒮^m` in the sense of §3.5; a `C`-valued function is `𝒮^m` when its real and
imaginary parts are; and a function on `ℙ_n(C)` (or a product) is `𝒮^m` when each chart
representation is.

These are the definitions underlying BPR's remark that "the notion of differentiability and the
classes `𝒮^m` and `𝒮^∞` can be defined in a similar way" — the setting for the projective implicit
function theorem (Theorem 4.104).
-/

namespace Azurite.BPR.Chapter4

open Azurite.BPR (IsSFunction)

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R] {n : ℕ}

/-- A real-valued function on an open subset `U ⊆ Cⁿ` is of class `𝒮^m` when its realification
`R^{2n} → R` is of class `𝒮^m` in the sense of §3.5. -/
def IsSFunctionC (m : ℕ) (U : Set (Fin n → Ri R)) (c : (Fin n → Ri R) → R) : Prop :=
  IsSFunction m (realEquiv '' U) (fun w => c (realEquiv.symm w))

/-- A `C`-valued function on `U ⊆ Cⁿ` is of class `𝒮^m` when its real and imaginary parts are. -/
def IsSFunctionCC (m : ℕ) (U : Set (Fin n → Ri R)) (c : (Fin n → Ri R) → Ri R) : Prop :=
  IsSFunctionC m U (fun z => Ri.reL (c z)) ∧ IsSFunctionC m U (fun z => Ri.imL (c z))

variable {k ℓ : ℕ}

/-- A `C`-valued function on an open subset `U ⊆ ℙ_k(C)` is of class `𝒮^m` when, for every chart `i`,
its chart representation `f ∘ φᵢ` is `𝒮^m` on the chart pullback `φᵢ⁻¹(U ∩ 𝒰ᵢ) ⊆ Cᵏ`. -/
def IsSFunctionP (m : ℕ) (U : Set (complexProjectiveSpace R k))
    (f : complexProjectiveSpace R k → Ri R) : Prop :=
  ∀ i : Fin (k + 1),
    IsSFunctionCC m (chartMap i ⁻¹' (U ∩ chartSet i)) (fun z => f (chartMap i z))

/-- A `C`-valued function on an open subset `W ⊆ ℙ_k(C) × ℙ_ℓ(C)` is of class `𝒮^m` when, for every
pair of charts `(i, j)`, its representation `f ∘ (φᵢ × φⱼ)` is `𝒮^m` on the product chart pullback in
`C^{k+ℓ}`. -/
def IsSFunctionPP (m : ℕ) (W : Set (complexProjectiveSpace R k × complexProjectiveSpace R ℓ))
    (f : complexProjectiveSpace R k × complexProjectiveSpace R ℓ → Ri R) : Prop :=
  ∀ (i : Fin (k + 1)) (j : Fin (ℓ + 1)),
    IsSFunctionCC m (prodChart i j ⁻¹' (W ∩ chartSet i ×ˢ chartSet j))
      (fun z => f (prodChart i j z))

/-- A map `ϕ : ℙ_k(C) → ℙ_ℓ(C)` is of class `𝒮^m` on `U` (mapping into `V`) when, for every pair of
charts `(i, j)`, its representation `φⱼ⁻¹ ∘ ϕ ∘ φᵢ` is `𝒮^m` on the part of `φᵢ⁻¹(U ∩ 𝒰ᵢ)` mapped into
`𝒰ⱼ`. We record this via the coordinate functions of the chart representation. -/
def IsSClassMapP (m : ℕ) (U : Set (complexProjectiveSpace R k))
    (V : Set (complexProjectiveSpace R ℓ))
    (ϕ : complexProjectiveSpace R k → complexProjectiveSpace R ℓ) : Prop :=
  Set.MapsTo ϕ U V ∧
    ∀ (i : Fin (k + 1)) (j : Fin (ℓ + 1)) (b : Fin ℓ),
      IsSFunctionCC m
        (chartMap i ⁻¹' (U ∩ chartSet i) ∩ (fun z => ϕ (chartMap i z)) ⁻¹' chartSet j)
        (fun z => chartInv j (ϕ (chartMap i z)) b)

end Azurite.BPR.Chapter4
