/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter6.Section2Sine

/-!
# DLMF §6.2(iii): auxiliary functions

Formalizations of <https://dlmf.nist.gov/6.2.iii>, equations 6.2.17–6.2.21: the auxiliary
functions `f` (`auxF`) and `g` (`auxG`) of the sine and cosine integrals (used for large
arguments in §§6.4, 6.5 and 6.12(ii)).

* 6.2.17, 6.2.18: the definitions.
* 6.2.19, 6.2.20: `dlmf_6_2_19`, `dlmf_6_2_20` (every `z`; from `si = Si − π/2`, 6.2.10, and
  `sin² + cos² = 1`).
* 6.2.21: `dlmf_6_2_21` (`f′ = −g`, `g′ = f − 1/z` off the cut), from `Ci′ = cos z / z`
  (`hasDerivAt_Ci`, via 6.2.13) and `si′ = sin z / z` (`hasDerivAt_si`).
-/

open Complex Filter Topology Set
open scoped Real

namespace Azurite.DLMF

/-- **DLMF 6.2.17**: `f(z) = Ci(z) sin z − si(z) cos z`. -/
noncomputable def auxF (z : ℂ) : ℂ := Ci z * Complex.sin z - si z * Complex.cos z

/-- **DLMF 6.2.18**: `g(z) = −Ci(z) cos z − si(z) sin z`. -/
noncomputable def auxG (z : ℂ) : ℂ := -Ci z * Complex.cos z - si z * Complex.sin z

/-- **DLMF 6.2.19**: `Si(z) = π/2 − f(z) cos z − g(z) sin z`. -/
theorem dlmf_6_2_19 (z : ℂ) :
    Si z = π / 2 - auxF z * Complex.cos z - auxG z * Complex.sin z := by
  have h := (dlmf_6_2_10 z).2
  have hsc := Complex.sin_sq_add_cos_sq z
  rw [auxF, auxG]
  linear_combination -h - si z * hsc

/-- **DLMF 6.2.20**: `Ci(z) = f(z) sin z − g(z) cos z`. -/
theorem dlmf_6_2_20 (z : ℂ) : Ci z = auxF z * Complex.sin z - auxG z * Complex.cos z := by
  have hsc := Complex.sin_sq_add_cos_sq z
  rw [auxF, auxG]
  linear_combination -Ci z * hsc

/-- `si′(z) = sin z / z` (`sincC` at `z`; `si = Si − π/2`). -/
theorem hasDerivAt_si (z : ℂ) : HasDerivAt si (sincC z) z := by
  have h : si = fun w => SiF w - π / 2 := funext fun w => by rw [(dlmf_6_2_10 w).2, Si_eq]
  rw [h]
  exact (hasDerivAt_SiF z).sub_const _

/-- `Ci′(z) = cos z / z` off the cut (`Ci = −Cin + ln + γ` on the open set `slitPlane`). -/
theorem hasDerivAt_Ci {z : ℂ} (hz : z ∈ slitPlane) :
    HasDerivAt Ci (Complex.cos z / z) z := by
  refine (hasDerivAt_CiG hz).congr_of_eventuallyEq ?_
  filter_upwards [isOpen_slitPlane.mem_nhds hz] with w hw
  rw [(dlmf_6_2_13 hw).2, CiG]

/-- **DLMF 6.2.21**: `f′(z) = −g(z)` and `g′(z) = f(z) − 1/z`, off the cut. -/
theorem dlmf_6_2_21 {z : ℂ} (hz : z ∈ slitPlane) :
    HasDerivAt auxF (-auxG z) z ∧ HasDerivAt auxG (auxF z - 1 / z) z := by
  have hz0 := slitPlane_ne_zero hz
  have hCi := hasDerivAt_Ci hz
  have hsi := hasDerivAt_si z
  rw [sincC_of_ne hz0] at hsi
  have hsc := Complex.sin_sq_add_cos_sq z
  constructor
  · refine ((hCi.mul (Complex.hasDerivAt_sin z)).sub
      (hsi.mul (Complex.hasDerivAt_cos z))).congr_deriv ?_
    rw [auxG]
    field_simp
    ring
  · refine ((hCi.neg.mul (Complex.hasDerivAt_cos z)).sub
      (hsi.mul (Complex.hasDerivAt_sin z))).congr_deriv ?_
    rw [auxF, Pi.neg_apply]
    field_simp
    linear_combination (-1 : ℂ) * hsc

end Azurite.DLMF
