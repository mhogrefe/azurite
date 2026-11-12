/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter5.Section13

/-!
# DLMF 5.13.3: Barnes' beta integral

`(2π)⁻¹ ∫_{−∞}^{∞} Γ(a + it)Γ(b + it)Γ(c − it)Γ(d − it) dt =
Γ(a + c)Γ(a + d)Γ(b + c)Γ(b + d)/Γ(a + b + c + d)` for `ℜa, ℜb, ℜc, ℜd > 0` (`dlmf_5_13_3`).

Proof: `Γ(c − it)Γ(a + it)` and `Γ(b + it)Γ(d − it)` are the Mellin transforms of
`f = Γ(a + c)x^{c−1}(1 + x)^{−a−c}` at `1 − it` and of `g = Γ(b + d)x^b(1 + x)^{−b−d}` at `it`
(`mellin_mellinPair`), so the Mellin–Parseval formula (1.14.36, `dlmf_1_14_36`) turns the integral
into `∫₀^∞ f(x)g(x) dx = Γ(a + c)Γ(b + d)B(b + c, a + d)` (5.12.3).
-/

open Complex Filter Topology Set MeasureTheory
open scoped Real

namespace Azurite.DLMF

/-- **DLMF 5.13.3** (Barnes' beta integral). -/
theorem dlmf_5_13_3 {a b c d : ℂ} (ha : 0 < a.re) (hb : 0 < b.re) (hc : 0 < c.re)
    (hd : 0 < d.re) :
    1 / (2 * π) * ∫ t : ℝ, Gamma (a + t * I) * Gamma (b + t * I) * Gamma (c - t * I) *
      Gamma (d - t * I) =
      Gamma (a + c) * Gamma (a + d) * Gamma (b + c) * Gamma (b + d) / Gamma (a + b + c + d) := by
  set f := mellinPair (c - 1) (a + 1)
  set g := mellinPair b d
  have hf : MellinConvergent f (1 - ((0 : ℝ) : ℂ)) :=
    mellinConvergent_mellinPair (by simpa using hc) (by simpa using ha)
  have hg : MellinConvergent g ((0 : ℝ) : ℂ) :=
    mellinConvergent_mellinPair (by simpa using hb) (by simpa using hd)
  have hG : VerticalIntegrable (mellin g) (0 : ℝ) :=
    verticalIntegrable_mellinPair (by simpa using hb) (by simpa using hd)
  have hP := dlmf_1_14_36 hf hg (Or.inl hG) one_pos
  -- the right side of Parseval is our integral
  have hR : ∫ t : ℝ, ((1 : ℝ) : ℂ) ^ (-(((0 : ℝ) : ℂ) + t * I)) *
      mellin f (1 - (((0 : ℝ) : ℂ) + t * I)) * mellin g (((0 : ℝ) : ℂ) + t * I) =
      ∫ t : ℝ, Gamma (a + t * I) * Gamma (b + t * I) * Gamma (c - t * I) * Gamma (d - t * I) := by
    refine integral_congr_ae (ae_of_all _ fun t => ?_)
    simp only [f, g]
    rw [mellin_mellinPair (by simpa using hc) (by simpa using ha),
      mellin_mellinPair (by simpa using hb) (by simpa using hd), ofReal_one, one_cpow]
    push_cast
    ring_nf
  -- the left side is a beta integral
  have hbc : 0 < (b + c).re := by simp only [add_re]; linarith
  have had : 0 < (a + d).re := by simp only [add_re]; linarith
  have hL : ∫ x in Ioi (0 : ℝ), f x * g (1 * x) =
      Gamma (a + c) * Gamma (b + d) * dlmfBeta (b + c) (a + d) := by
    rw [← dlmf_5_12_3 hbc had, ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
    have hx0 : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr (ne_of_gt hx)
    have h1 : (1 : ℂ) + x ≠ 0 := by
      intro h; have := congrArg re h; simp at this; linarith [show (0 : ℝ) < x from hx]
    simp only [f, g, mellinPair, one_mul]
    rw [show c - 1 + (a + 1) = a + c by ring,
      show b + c + (a + d) = (a + c) + (b + d) by ring, cpow_add _ _ h1,
      show b + c - 1 = (c - 1) + b by ring, cpow_add _ _ hx0, div_eq_mul_inv, cpow_neg, cpow_neg,
      mul_inv]
    ring
  rw [hR, hL] at hP
  rw [one_div, ← hP, dlmfBeta, show b + c + (a + d) = a + b + c + d by ring]
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  field_simp

end Azurite.DLMF
