/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.BasuPollackRoy.Chapter3.Section3_1.Continuity

/-! # BPR §3.5 — limits, little-o, and the one-variable derivative

The ε–δ vocabulary for §3.5 (Implicit Function Theorem), over a real closed field `R`:

* `LimitAtIn f M x₀ y₀` — BPR's `lim_{x ∈ M, x → x₀} f(x) = y₀`: for every `r > 0` there is
  `δ > 0` with `‖f(x) − y₀‖ < r` for all `x ∈ M` with `0 < ‖x − x₀‖ < δ`. BPR's plain
  `lim_{x → x₀} f(x) = y₀` (for `f` defined on `U`) is this with `M = U`.
* `LimitAtInR` — the scalar-valued specialization (with `|·|` in the target, mirroring
  `ContinuousR`).
* `IsLittleO f M x₀` — BPR's `f(x) = o(‖x − x₀‖)`: `lim_{x → x₀} f(x)/‖x − x₀‖ = 0`.
* `HasDerivAtIn f M x₀ f'` — BPR's `f` differentiable at `x₀` with derivative `f'(x₀)`:
  `lim_{x → x₀} (f(x) − f(x₀))/(x − x₀) = f'(x₀)`, for `f : R → R` on an interval `M`.

Following the standard reading of `lim_{x → x₀}`, the quantification is over the *deleted*
neighborhood (`x ≠ x₀`): this is what makes the difference-quotient definition of the derivative
meaningful (at `x = x₀` the quotient is `0/0`, which Lean's field convention evaluates to `0`).

The definitions are stated for arbitrary functions (as with continuity in §3.1); §3.5's theorems
add the semialgebraicity hypotheses. `continuousWithinAt_iff_limitAtIn` ties the new vocabulary
back to §3.1: for `x₀ ∈ M`, continuity of `f` at `x₀` within `M` says exactly
`lim_{x ∈ M, x → x₀} f(x) = f(x₀)`. -/

namespace Azurite.BPR

variable {k ℓ : ℕ} {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]

/-! ### Limits along a set -/

/-- **BPR's `lim_{x ∈ M, x → x₀} f(x) = y₀`** for a map `f : R^k → R^ℓ`: for every `r > 0`
there is `δ > 0` such that `‖f(x) − y₀‖ < r` for all `x ∈ M` with `0 < ‖x − x₀‖ < δ`.
BPR's unrestricted `lim_{x → x₀} f(x) = y₀` for `f` defined on `U` is `LimitAtIn f U x₀ y₀`. -/
def LimitAtIn (f : (Fin k → R) → (Fin ℓ → R)) (M : Set (Fin k → R))
    (x₀ : Fin k → R) (y₀ : Fin ℓ → R) : Prop :=
  ∀ r, 0 < r → ∃ δ, 0 < δ ∧ ∀ x ∈ M, x ≠ x₀ →
    euclideanNorm (x - x₀) < δ → euclideanNorm (f x - y₀) < r

/-- The scalar-valued limit `lim_{x ∈ M, x → x₀} f(x) = y₀` for `f : R → R` (with `|·|` in
place of the euclidean norm, mirroring `ContinuousR`). -/
def LimitAtInR (f : R → R) (M : Set R) (x₀ y₀ : R) : Prop :=
  ∀ r, 0 < r → ∃ δ, 0 < δ ∧ ∀ x ∈ M, x ≠ x₀ → |x - x₀| < δ → |f x - y₀| < r

/-- **BPR's `f(x) = o(‖x − x₀‖)`** on `M`: `lim_{x ∈ M, x → x₀} f(x)/‖x − x₀‖ = 0`. -/
def IsLittleO (f : (Fin k → R) → (Fin ℓ → R)) (M : Set (Fin k → R))
    (x₀ : Fin k → R) : Prop :=
  LimitAtIn (fun x => (euclideanNorm (x - x₀))⁻¹ • f x) M x₀ 0

/-! ### The one-variable derivative -/

/-- **BPR's derivative.** `f : R → R` is differentiable at `x₀` (within the interval `M`,
BPR's `(a, b)`) with derivative `f'` if `lim_{x → x₀} (f(x) − f(x₀))/(x − x₀) = f'`. -/
def HasDerivAtIn (f : R → R) (M : Set R) (x₀ f' : R) : Prop :=
  LimitAtInR (fun x => (f x - f x₀) / (x - x₀)) M x₀ f'

/-! ### First properties -/

theorem limitAtIn_const (M : Set (Fin k → R)) (x₀ : Fin k → R) (c : Fin ℓ → R) :
    LimitAtIn (fun _ => c) M x₀ c :=
  fun r hr => ⟨1, one_pos, fun _ _ _ _ => by
    rw [sub_self]
    simpa [euclideanNorm_zero] using hr⟩

theorem limitAtIn_mono {f : (Fin k → R) → (Fin ℓ → R)} {M N : Set (Fin k → R)}
    {x₀ : Fin k → R} {y₀ : Fin ℓ → R} (hMN : N ⊆ M) (h : LimitAtIn f M x₀ y₀) :
    LimitAtIn f N x₀ y₀ := fun r hr =>
  let ⟨δ, hδ, hball⟩ := h r hr
  ⟨δ, hδ, fun x hx => hball x (hMN hx)⟩

/-- For `x₀ ∈ M`, continuity of `f` at `x₀` within `M` (the subspace topology of §3.1) says
exactly `lim_{x ∈ M, x → x₀} f(x) = f(x₀)`: the deleted-neighborhood restriction is invisible
when the limit value is `f(x₀)`. -/
theorem continuousWithinAt_iff_limitAtIn {f : (Fin k → R) → (Fin ℓ → R)}
    {M : Set (Fin k → R)} {x₀ : Fin k → R} (hx₀ : x₀ ∈ M) :
    ContinuousWithinAt f M x₀ ↔ LimitAtIn f M x₀ (f x₀) := by
  have hb : (nhdsWithin x₀ M).HasBasis (fun δ => 0 < δ) (fun δ => openBall x₀ δ ∩ M) :=
    (nhds_hasBasis_openBall x₀).inf_principal M
  rw [ContinuousWithinAt, hb.tendsto_iff (nhds_hasBasis_openBall (f x₀))]
  constructor
  · rintro h r hr
    obtain ⟨δ, hδ, hball⟩ := h r hr
    refine ⟨δ, hδ, fun x hxM _ hx => ?_⟩
    exact (mem_openBall_iff_norm hr).mp
      (hball x ⟨(mem_openBall_iff_norm hδ).mpr hx, hxM⟩)
  · rintro h r hr
    obtain ⟨δ, hδ, hball⟩ := h r hr
    refine ⟨δ, hδ, fun x hx => ?_⟩
    rcases eq_or_ne x x₀ with rfl | hne
    · exact mem_openBall_self _ hr
    · exact (mem_openBall_iff_norm hr).mpr
        (hball x hx.2 hne ((mem_openBall_iff_norm hδ).mp hx.1))

end Azurite.BPR
