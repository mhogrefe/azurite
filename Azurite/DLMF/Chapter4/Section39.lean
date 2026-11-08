/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter4.Section25Arcsin
import Azurite.DLMF.Chapter4.Section29InvHyp

/-!
# DLMF §4.39 Continued Fractions (hyperbolic functions)

As in §4.25, the continued fraction `b₀ + a₁/(b₁ + a₂/(b₂ + ⋯))` has convergents
`cfA a b r / cfB a b r` (§1.12). Each formula is stated as: the denominators are eventually
nonzero and the convergents tend to the function. Here `bᵣ = 2r − 1` (`lg2b`).

Each formula is the §4.25 one at `iz`. Replacing `z` by `iz` multiplies the first partial
numerator by `i` and leaves the others unchanged. So the numerators are multiplied by `i` and the
denominators are unchanged (`cf_first_mul_I`, from `cfP_scale_first` and `cfQ_change_first`).

* 4.39.1 (`z ≠ ±½πi, ±(3/2)πi, …`): `dlmf_4_39_1`, from 4.25.1 (`tan(iz) = i tanh z`).
* 4.39.2 (`z` in the open cut plane of Figure 4.37.1(i)): `dlmf_4_39_2`, from 4.25.3; `√(1 + z²)`
  is the principal root `(1 + z²)^{1/2}`.
* 4.39.3 (`z` in the open cut plane of Figure 4.37.1(iii)): `dlmf_4_39_3`, from 4.25.4.
-/

open Set Filter Topology Complex
open scoped Real

namespace Azurite.DLMF

/-- If the partial numerators `a` differ from `a'` only in `a₁ = i a'₁` (and `b₀ = 0`), then the
convergents of `a'` are `−i` times those of `a`. -/
theorem cf_first_mul_I {a a' b : ℕ → ℂ} (hb : b 0 = 0) (h1 : a 1 = I * a' 1)
    (h : ∀ r ≥ 2, a r = a' r) {L : ℂ} (hB : ∀ᶠ r in atTop, cfB a b r ≠ 0)
    (hT : Tendsto (fun r => cfA a b r / cfB a b r) atTop (𝓝 L)) :
    (∀ᶠ r in atTop, cfB a' b r ≠ 0) ∧
      Tendsto (fun r => cfA a' b r / cfB a' b r) atTop (𝓝 (-I * L)) := by
  have hP := cfP_scale_first (a := a') (a' := a) (b := b) I hb h1 h
  have hQ := cfQ_change_first (a := a') (a' := a) (b := b) h
  have hBeq : ∀ r, cfB a b r = cfB a' b r := fun r => hQ (r + 1)
  refine ⟨hB.mono fun r hr => by rwa [← hBeq], (hT.const_mul (-I)).congr fun r => ?_⟩
  show -I * (cfP a b (r + 1) / cfQ a b (r + 1)) = cfP a' b (r + 1) / cfQ a' b (r + 1)
  rw [hP r, hQ (r + 1), ← mul_div_assoc, ← mul_assoc, neg_mul, I_mul_I, neg_neg, one_mul]

/-- The partial numerators of 4.39.1: `a₁ = z`, `aᵣ = z²` (`r ≥ 2`). -/
noncomputable def tanhCFa (z : ℂ) (r : ℕ) : ℂ := if r = 1 then z else z ^ 2

/-- **DLMF 4.39.1**: `tanh z = z/(1 + z²/(3 + z²/(5 + z²/(7 + ⋯))))`,
`z ≠ ±½πi, ±(3/2)πi, …`. -/
theorem dlmf_4_39_1 {z : ℂ} (hz : ∀ k : ℤ, z ≠ (2 * k + 1) * π / 2 * I) :
    (∀ᶠ r in atTop, cfB (tanhCFa z) (lg2b z) r ≠ 0) ∧
      Tendsto (fun r => cfA (tanhCFa z) (lg2b z) r / cfB (tanhCFa z) (lg2b z) r) atTop
        (𝓝 (tanh z)) := by
  have hz' : ∀ k : ℤ, I * z ≠ (2 * k + 1) * π / 2 := fun k h => by
    apply hz (-k - 1)
    have : z = -I * (I * z) := by rw [← mul_assoc, neg_mul, I_mul_I, neg_neg, one_mul]
    rw [this, h]; push_cast; ring
  obtain ⟨hB, hT⟩ := dlmf_4_25_1 hz'
  have h := cf_first_mul_I (a' := tanhCFa z) (b := lg2b z) (by simp [lg2b])
    (by simp [tanCFa, tanhCFa])
    (fun r hr => by
      simp only [tanCFa, tanhCFa, show r ≠ 1 by omega, ↓reduceIte, mul_pow, I_sq]; ring) hB hT
  rw [dlmf_4_28_10, ← mul_assoc, neg_mul, I_mul_I, neg_neg, one_mul] at h
  exact h

/-- The partial numerators of 4.39.2: `a₁ = z`, `a_{2k} = a_{2k+1} = (2k − 1)(2k) z²`. -/
noncomputable def asinhCFa (z : ℂ) (r : ℕ) : ℂ :=
  if r = 1 then z else ((((2 * (r / 2) - 1) * (2 * (r / 2)) : ℕ) : ℂ)) * z ^ 2

/-- **DLMF 4.39.2**: `arcsinh z/√(1 + z²) = z/(1 + 1·2z²/(3 + 1·2z²/(5 + 3·4z²/(7 + 3·4z²/
(9 + ⋯)))))`, `z` in the open cut plane of Figure 4.37.1(i). -/
theorem dlmf_4_39_2 {z : ℂ} (hz : z ∈ arcsinhCut) :
    (∀ᶠ r in atTop, cfB (asinhCFa z) (lg2b z) r ≠ 0) ∧
      Tendsto (fun r => cfA (asinhCFa z) (lg2b z) r / cfB (asinhCFa z) (lg2b z) r) atTop
        (𝓝 (arcsinhD z / (1 + z ^ 2) ^ (1 / 2 : ℂ))) := by
  obtain ⟨hB, hT⟩ := dlmf_4_25_3 (I_mul_mem_arcsinCut.mpr hz)
  have h := cf_first_mul_I (a' := asinhCFa z) (b := lg2b z) (by simp [lg2b])
    (by simp [asinCFa, asinhCFa])
    (fun r hr => by
      simp only [asinCFa, asinhCFa, show r ≠ 1 by omega, ↓reduceIte, mul_pow, I_sq]; ring) hB hT
  have hs : arcsinD (I * z) = I * arcsinhD z := by
    rw [arcsinhD_eq, ← mul_assoc, mul_neg, I_mul_I, neg_neg, one_mul]
  have hr : 1 - (I * z) ^ 2 = 1 + z ^ 2 := by rw [mul_pow, I_sq]; ring
  rw [hs, hr, mul_div_assoc, ← mul_assoc, neg_mul, I_mul_I, neg_neg, one_mul] at h
  exact h

/-- The partial numerators of 4.39.3: `a₁ = z`, `aᵣ = −(r − 1)² z²` (`r ≥ 2`). -/
noncomputable def atanhCFa (z : ℂ) (r : ℕ) : ℂ :=
  if r = 1 then z else -((((r - 1) ^ 2 : ℕ) : ℂ)) * z ^ 2

/-- **DLMF 4.39.3**: `arctanh z = z/(1 − z²/(3 − 4z²/(5 − 9z²/(7 − ⋯))))`, `z` in the open cut
plane of Figure 4.37.1(iii). -/
theorem dlmf_4_39_3 {z : ℂ} (hz : z ∈ arctanhCut) :
    (∀ᶠ r in atTop, cfB (atanhCFa z) (lg2b z) r ≠ 0) ∧
      Tendsto (fun r => cfA (atanhCFa z) (lg2b z) r / cfB (atanhCFa z) (lg2b z) r) atTop
        (𝓝 (arctanhD z)) := by
  obtain ⟨hB, hT⟩ := dlmf_4_25_4 (I_mul_mem_arctanCut.mpr hz)
  have h := cf_first_mul_I (a' := atanhCFa z) (b := lg2b z) (by simp [lg2b])
    (by simp [arctanCFa, atanhCFa])
    (fun r hr => by
      simp only [arctanCFa, atanhCFa, show r ≠ 1 by omega, ↓reduceIte, mul_pow, I_sq]; ring)
    hB hT
  rw [← arctanhD_eq] at h
  exact h

end Azurite.DLMF
