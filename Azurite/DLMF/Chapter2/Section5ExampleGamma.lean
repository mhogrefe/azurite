/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter5.Section11Modulus

/-!
# DLMF §2.5(i): 2.5.14

Formalization of <https://dlmf.nist.gov/2.5#E14>:
`|Γ(x + iy)| = (2π)^{1/2} e^{−π|y|/2} |y|^{x−½} (1 + o(1))` as `y → ±∞`, uniformly for bounded
`|x|`, which the DLMF quotes from 5.11.9 (`dlmf_5_11_9`).
-/

open Filter Topology Set
open scoped Real

namespace Azurite.DLMF

/-- **DLMF 2.5.14**: along `𝓟 [−X, X] ×ˢ (y → ±∞)` there is an `o(1)` term `ε` with
`|Γ(x + iy)| = √(2π) e^{−π|y|/2} |y|^{x−½} (1 + ε)`. -/
theorem dlmf_2_5_14 (X : ℝ) :
    ∃ ε : ℝ × ℝ → ℝ, Tendsto ε (𝓟 (Icc (-X) X) ×ˢ Bornology.cobounded ℝ) (𝓝 0) ∧
      ∀ᶠ p : ℝ × ℝ in 𝓟 (Icc (-X) X) ×ˢ Bornology.cobounded ℝ,
        ‖Complex.Gamma (p.1 + p.2 * Complex.I)‖ =
          Real.sqrt (2 * π) * Real.exp (-(π * |p.2|) / 2) * |p.2| ^ (p.1 - 1 / 2) * (1 + ε p) := by
  have h := dlmf_5_11_9 X
  refine ⟨fun p => ‖Complex.Gamma (p.1 + p.2 * Complex.I)‖ /
    (Real.sqrt (2 * π) * |p.2| ^ (p.1 - 1 / 2) * Real.exp (-(π * |p.2|) / 2)) - 1, ?_, ?_⟩
  · simpa using h.sub_const 1
  · have hy : ∀ᶠ p : ℝ × ℝ in 𝓟 (Icc (-X) X) ×ˢ Bornology.cobounded ℝ, 1 ≤ ‖p.2‖ :=
      (tendsto_snd (f := 𝓟 (Icc (-X) X)) (g := Bornology.cobounded ℝ)).eventually
        ((tendsto_norm_cobounded_atTop (E := ℝ)).eventually (eventually_ge_atTop _))
    filter_upwards [hy] with p hp
    rw [Real.norm_eq_abs] at hp
    have hD : 0 < Real.sqrt (2 * π) * |p.2| ^ (p.1 - 1 / 2) * Real.exp (-(π * |p.2|) / 2) := by
      have := Real.rpow_pos_of_pos (by linarith : (0 : ℝ) < |p.2|) (p.1 - 1 / 2)
      have := Real.sqrt_pos.mpr (show (0 : ℝ) < 2 * π by positivity)
      positivity
    field_simp
    ring

end Azurite.DLMF
