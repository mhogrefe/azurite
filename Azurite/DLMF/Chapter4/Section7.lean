/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter4.Section2Pow
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Analysis.Calculus.Deriv.ZPow
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# DLMF §4.7: Derivatives and differential equations

Formalizations of <https://dlmf.nist.gov/4.7>. A branch of `Ln` on an open set `U` is a function
`L`, continuous on `U`, with `exp (L z) = z` on `U` (`IsLnBranch`); the principal branch `ln` is
`Complex.log` on `ℂ ∖ (−∞, 0]`.

* 4.7.1–4.7.4: `dlmf_4_7_1`, `dlmf_4_7_2`, `dlmf_4_7_3`, `dlmf_4_7_4` (`n ≥ 1`, via
  `iteratedDeriv_succ_eq_of_deriv_eqOn`).
* 4.7.5, 4.7.6: on a domain `D`, `w′ = f′/f` iff `w = Ln f + constant` (`dlmf_4_7_6`).
* 4.7.7–4.7.11: `dlmf_4_7_7` … `dlmf_4_7_11`; 4.7.9 also for the general power with any branch
  of `Ln a` (`dlmf_4_7_9_general`).
* 4.7.12, 4.7.13: on a domain, `w′ = f w` iff `w = C exp(∫ f dz)` (`dlmf_4_7_13`). **Erratum**:
  the DLMF's "`w = exp(∫ f(z) dz) + constant`" is not a solution unless the constant is `0`
  (`dlmf_4_7_13_erratum`).
* 4.7.14, 4.7.15: `w″ = aw` (`a ≠ 0`) iff `w = A e^{√a z} + B e^{−√a z}` (`dlmf_4_7_15`).

Kamke (1977) is a reference.
-/

open Complex Set Filter Topology Finset
open scoped Real

namespace Azurite.DLMF

/-! ### Iterated derivatives from a first derivative -/

/-- If `f′ = g` on an open set, then `f^{(n+1)} = g^{(n)}` there. -/
theorem iteratedDeriv_succ_eq_of_deriv_eqOn {U : Set ℂ} (hU : IsOpen U) {f g : ℂ → ℂ}
    (h : ∀ z ∈ U, deriv f z = g z) (n : ℕ) {z : ℂ} (hz : z ∈ U) :
    iteratedDeriv (n + 1) f z = iteratedDeriv n g z := by
  rw [iteratedDeriv_succ']
  apply Filter.EventuallyEq.iteratedDeriv_eq
  filter_upwards [hU.mem_nhds hz] with w hw
  exact h w hw

/-- `(1/z)^{(n)} = (−1)ⁿ n! z^{−n−1}`. -/
theorem iteratedDeriv_inv_eq (n : ℕ) (z : ℂ) :
    iteratedDeriv n (fun w : ℂ => w⁻¹) z = (-1) ^ n * n.factorial * z ^ (-1 - n : ℤ) := by
  rw [iteratedDeriv_eq_iterate]
  exact iter_deriv_inv n z

/-! ### §4.7(i) Logarithms -/

/-- **DLMF 4.7.1**: `d/dz ln z = 1/z` (`z ∈ ℂ ∖ (−∞, 0]`). -/
theorem dlmf_4_7_1 {z : ℂ} (hz : z ∈ slitPlane) : HasDerivAt log (1 / z) z := by
  rw [one_div]; exact hasDerivAt_log hz

/-- A branch of `Ln` on `U`: continuous with `exp (L z) = z`. -/
def IsLnBranch (L : ℂ → ℂ) (U : Set ℂ) : Prop :=
  ContinuousOn L U ∧ ∀ z ∈ U, exp (L z) = z

/-- **DLMF 4.7.2**: every branch of `Ln` has `d/dz Ln z = 1/z`. -/
theorem dlmf_4_7_2 {L : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U) (hL : IsLnBranch L U) {z : ℂ}
    (hz : z ∈ U) : HasDerivAt L (1 / z) z := by
  have hcont : ContinuousAt L z := hL.1.continuousAt (hU.mem_nhds hz)
  have h := HasDerivAt.of_local_left_inverse hcont (hasDerivAt_exp (L z))
    (exp_ne_zero _) (by filter_upwards [hU.mem_nhds hz] with w hw; exact hL.2 w hw)
  rwa [hL.2 z hz, ← one_div] at h

/-- **DLMF 4.7.3**: `dⁿ/dzⁿ ln z = (−1)^{n−1}(n−1)! z^{−n}` (`n ≥ 1`). -/
theorem dlmf_4_7_3 (n : ℕ) {z : ℂ} (hz : z ∈ slitPlane) :
    iteratedDeriv (n + 1) log z = (-1) ^ n * n.factorial * z ^ (-(n + 1 : ℕ) : ℤ) := by
  rw [iteratedDeriv_succ_eq_of_deriv_eqOn (g := fun w => w⁻¹) isOpen_slitPlane
    (fun w hw => (hasDerivAt_log hw).deriv) n hz, iteratedDeriv_inv_eq]
  congr 2; push_cast; ring

/-- **DLMF 4.7.4**: the same for every branch of `Ln`. -/
theorem dlmf_4_7_4 {L : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U) (hL : IsLnBranch L U) (n : ℕ)
    {z : ℂ} (hz : z ∈ U) :
    iteratedDeriv (n + 1) L z = (-1) ^ n * n.factorial * z ^ (-(n + 1 : ℕ) : ℤ) := by
  rw [iteratedDeriv_succ_eq_of_deriv_eqOn (g := fun w => w⁻¹) hU
    (fun w hw => by rw [(dlmf_4_7_2 hU hL hw).deriv, one_div]) n hz, iteratedDeriv_inv_eq]
  congr 2; push_cast; ring

/-- **DLMF 4.7.5, 4.7.6**: for `f` analytic and nonvanishing on a domain `D`, the solutions of
`dw/dz = f′(z)/f(z)` are exactly `w(z) = Ln(f(z)) + constant` (`w − C` takes values of `Ln f`). -/
theorem dlmf_4_7_6 {D : Set ℂ} (hD : IsOpen D) (hDc : IsPreconnected D) {f w : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f D) (hf0 : ∀ z ∈ D, f z ≠ 0) (hw : DifferentiableOn ℂ w D) :
    (∀ z ∈ D, deriv w z = deriv f z / f z) ↔ ∃ C : ℂ, ∀ z ∈ D, w z - C ∈ genLogSet (f z) := by
  have hfd : ∀ z ∈ D, HasDerivAt f (deriv f z) z := fun z hz =>
    ((hf z hz).differentiableAt (hD.mem_nhds hz)).hasDerivAt
  have hwd : ∀ z ∈ D, HasDerivAt w (deriv w z) z := fun z hz =>
    ((hw z hz).differentiableAt (hD.mem_nhds hz)).hasDerivAt
  constructor
  · intro h
    set k : ℂ → ℂ := fun z => f z * exp (-w z)
    have hk : ∀ z ∈ D, HasDerivAt k 0 z := by
      intro z hz
      have := (hfd z hz).mul (hwd z hz).neg.cexp
      convert this using 1
      rw [h z hz]; field_simp [hf0 z hz]; ring
    obtain ⟨c, hc⟩ := hD.exists_is_const_of_deriv_eq_zero hDc
      (fun z hz => (hk z hz).differentiableAt.differentiableWithinAt)
      (fun z hz => (hk z hz).deriv)
    by_cases hDe : D.Nonempty
    · obtain ⟨z0, hz0⟩ := hDe
      have hc0 : c ≠ 0 := by
        rw [← hc z0 hz0]; exact mul_ne_zero (hf0 z0 hz0) (exp_ne_zero _)
      refine ⟨-log c, fun z hz => (dlmf_4_2_25 (hf0 z hz) _).mp ?_⟩
      rw [sub_neg_eq_add, exp_add, exp_log hc0, ← hc z hz]
      simp only [k, exp_neg]
      field_simp
    · exact ⟨0, fun z hz => absurd ⟨z, hz⟩ hDe⟩
  · rintro ⟨C, hC⟩ z hz
    have heq : ∀ y ∈ D, exp (w y) = exp C * f y := fun y hy => by
      have := (dlmf_4_2_25 (hf0 y hy) _).mpr (hC y hy)
      rw [← this, ← exp_add]; ring_nf
    have h1 := (hwd z hz).cexp
    have h2 := (hfd z hz).const_mul (exp C)
    have hev : (fun y => exp (w y)) =ᶠ[𝓝 z] fun y => exp C * f y := by
      filter_upwards [hD.mem_nhds hz] with y hy; exact heq y hy
    have := h1.unique (h2.congr_of_eventuallyEq hev)
    rw [heq z hz] at this
    have hC0 := exp_ne_zero C
    field_simp [hf0 z hz] at this ⊢
    linear_combination this

/-! ### §4.7(ii) Exponentials and powers -/

/-- **DLMF 4.7.7**: `d/dz e^z = e^z`. -/
theorem dlmf_4_7_7 (z : ℂ) :
    HasDerivAt (fun z : ℂ => (Real.exp 1 : ℂ) ^ z) ((Real.exp 1 : ℂ) ^ z) z := by
  simp only [dlmf_4_2_32]
  exact hasDerivAt_exp z

/-- **DLMF 4.7.8**: `d/dz e^{az} = a e^{az}`. -/
theorem dlmf_4_7_8 (a z : ℂ) :
    HasDerivAt (fun z : ℂ => (Real.exp 1 : ℂ) ^ (a * z)) (a * (Real.exp 1 : ℂ) ^ (a * z)) z := by
  simp only [dlmf_4_2_32]
  have := ((hasDerivAt_id z).const_mul a).cexp
  simpa [mul_comm] using this

/-- **DLMF 4.7.9**: `d/dz a^z = a^z ln a`, `a ≠ 0` (principal value). -/
theorem dlmf_4_7_9 {a : ℂ} (ha : a ≠ 0) (z : ℂ) :
    HasDerivAt (fun z : ℂ => a ^ z) (a ^ z * log a) z := by
  simpa using (hasDerivAt_id z).const_cpow (c := a) (Or.inl ha)

/-- **DLMF §4.7(ii)**: "When `a^z` is a general power, `ln a` is replaced by the branch of `Ln a`
used in constructing `a^z`": for `λ ∈ Ln a`, `d/dz exp(zλ) = exp(zλ) λ`. -/
theorem dlmf_4_7_9_general {a ℓ : ℂ} (_hℓ : ℓ ∈ genLogSet a) (z : ℂ) :
    HasDerivAt (fun z : ℂ => exp (z * ℓ)) (exp (z * ℓ) * ℓ) z := by
  simpa using ((hasDerivAt_id z).mul_const ℓ).cexp

/-- **DLMF 4.7.10**: `d/dz z^a = a z^{a−1}` (`z ∈ ℂ ∖ (−∞, 0]`). -/
theorem dlmf_4_7_10 (a : ℂ) {z : ℂ} (hz : z ∈ slitPlane) :
    HasDerivAt (fun z : ℂ => z ^ a) (a * z ^ (a - 1)) z := by
  simpa using (hasDerivAt_id z).cpow_const (c := a) hz

/-- **DLMF 4.7.11**: `dⁿ/dzⁿ z^a = a(a − 1)⋯(a − n + 1) z^{a−n}` (`z ∈ ℂ ∖ (−∞, 0]`). -/
theorem dlmf_4_7_11 (a : ℂ) (n : ℕ) {z : ℂ} (hz : z ∈ slitPlane) :
    iteratedDeriv n (fun z : ℂ => z ^ a) z = (∏ i ∈ range n, (a - i)) * z ^ (a - n) := by
  induction n generalizing z with
  | zero => simp
  | succ n ih =>
    rw [iteratedDeriv_succ]
    have hev : iteratedDeriv n (fun z : ℂ => z ^ a) =ᶠ[𝓝 z]
        fun w => (∏ i ∈ range n, (a - i)) * w ^ (a - n) := by
      filter_upwards [isOpen_slitPlane.mem_nhds hz] with w hw; exact ih hw
    rw [hev.deriv_eq]
    have := ((hasDerivAt_id' z).cpow_const (c := a - n) hz).const_mul (∏ i ∈ range n, (a - i))
    rw [this.deriv, prod_range_succ,
      show a - ((n + 1 : ℕ) : ℂ) = a - n - 1 by push_cast; ring]
    ring

/-- **DLMF 4.7.12, 4.7.13** (corrected): on a domain `D`, with `F′ = f`, the solutions of
`dw/dz = f(z) w` are exactly `w = C exp(∫ f dz) = C exp(F)`. -/
theorem dlmf_4_7_13 {D : Set ℂ} (hD : IsOpen D) (hDc : IsPreconnected D) {f F w : ℂ → ℂ}
    (hF : ∀ z ∈ D, HasDerivAt F (f z) z) (hw : DifferentiableOn ℂ w D) :
    (∀ z ∈ D, deriv w z = f z * w z) ↔ ∃ C : ℂ, ∀ z ∈ D, w z = C * exp (F z) := by
  have hwd : ∀ z ∈ D, HasDerivAt w (deriv w z) z := fun z hz =>
    ((hw z hz).differentiableAt (hD.mem_nhds hz)).hasDerivAt
  constructor
  · intro h
    have hk : ∀ z ∈ D, HasDerivAt (fun z => w z * exp (-F z)) 0 z := by
      intro z hz
      have := (hwd z hz).mul (hF z hz).neg.cexp
      convert this using 1
      rw [h z hz]; ring
    obtain ⟨c, hc⟩ := hD.exists_is_const_of_deriv_eq_zero hDc
      (fun z hz => (hk z hz).differentiableAt.differentiableWithinAt)
      (fun z hz => (hk z hz).deriv)
    refine ⟨c, fun z hz => ?_⟩
    rw [← hc z hz, mul_assoc, ← exp_add, neg_add_cancel, exp_zero, mul_one]
  · rintro ⟨C, hC⟩ z hz
    have hev : w =ᶠ[𝓝 z] fun y => C * exp (F y) := by
      filter_upwards [hD.mem_nhds hz] with y hy; exact hC y hy
    rw [hev.deriv_eq, ((hF z hz).cexp.const_mul C).deriv, hC z hz]
    ring

/-- **Erratum to DLMF 4.7.13**: "`w = exp(∫ f(z) dz) + constant`" is not the general solution of
`w′ = f w`: with `f = 1`, `w = e^z + 1` has `w′ = e^z ≠ w`. -/
theorem dlmf_4_7_13_erratum :
    ¬ ∀ z : ℂ, deriv (fun z => exp z + 1) z = 1 * (exp z + 1) := by
  intro h
  have := h 0
  rw [((hasDerivAt_exp 0).add_const 1).deriv] at this
  norm_num at this

/-- **DLMF 4.7.14, 4.7.15**: for `a ≠ 0`, the solutions of `d²w/dz² = aw` are exactly
`w = A e^{√a z} + B e^{−√a z}`. -/
theorem dlmf_4_7_15 {a : ℂ} (ha : a ≠ 0) {w : ℂ → ℂ} (hw : Differentiable ℂ w)
    (hw' : Differentiable ℂ (deriv w)) :
    (∀ z, deriv (deriv w) z = a * w z) ↔
      ∃ A B : ℂ, ∀ z, w z = A * exp (a ^ (2 : ℂ)⁻¹ * z) + B * exp (-(a ^ (2 : ℂ)⁻¹) * z) := by
  set s := a ^ (2 : ℂ)⁻¹
  have hs2 : s ^ 2 = a := cpow_ofNat_inv_pow a 2
  have hs0 : s ≠ 0 := fun h => ha (by rw [← hs2, h]; ring)
  have hlin : ∀ c : ℂ, ∀ z, HasDerivAt (fun z => c * z) c z := fun c z => by
    simpa using (hasDerivAt_id z).const_mul c
  constructor
  · intro h
    -- `u = w′ − s w` solves `u′ = −s u`, `v = w′ + s w` solves `v′ = s v`
    have hu := (dlmf_4_7_13 (D := univ) isOpen_univ isPreconnected_univ
      (f := fun _ => -s) (F := fun z => -s * z) (w := fun z => deriv w z - s * w z)
      (fun z _ => hlin _ z) ((hw'.sub (hw.const_mul s)).differentiableOn)).mp (fun z _ => by
        have hd : HasDerivAt (fun z => deriv w z - s * w z)
            (deriv (deriv w) z - s * deriv w z) z :=
          ((hw' z).hasDerivAt).sub ((hw z).hasDerivAt.const_mul s)
        rw [hd.deriv, h z]
        rw [← hs2]; ring)
    have hv := (dlmf_4_7_13 (D := univ) isOpen_univ isPreconnected_univ
      (f := fun _ => s) (F := fun z => s * z) (w := fun z => deriv w z + s * w z)
      (fun z _ => hlin _ z) ((hw'.add (hw.const_mul s)).differentiableOn)).mp (fun z _ => by
        have hd : HasDerivAt (fun z => deriv w z + s * w z)
            (deriv (deriv w) z + s * deriv w z) z :=
          ((hw' z).hasDerivAt).add ((hw z).hasDerivAt.const_mul s)
        rw [hd.deriv, h z]
        rw [← hs2]; ring)
    obtain ⟨C, hC⟩ := hu
    obtain ⟨E, hE⟩ := hv
    refine ⟨E / (2 * s), -C / (2 * s), fun z => ?_⟩
    have h1 := hC z (mem_univ z)
    have h2 := hE z (mem_univ z)
    simp only [neg_mul] at h1 ⊢
    field_simp
    linear_combination h2 - h1
  · rintro ⟨A, B, hAB⟩ z
    have hd : ∀ y, HasDerivAt w (s * A * exp (s * y) - s * B * exp (-s * y)) y := by
      intro y
      have e : w = fun y => A * exp (s * y) + B * exp (-s * y) := funext hAB
      rw [e]
      have := (((hlin s y).cexp).const_mul A).add (((hlin (-s) y).cexp).const_mul B)
      convert this using 1; ring
    have hdw : deriv w = fun y => s * A * exp (s * y) - s * B * exp (-s * y) :=
      funext fun y => (hd y).deriv
    rw [hdw]
    have := ((((hlin s z).cexp).const_mul (s * A))).sub (((hlin (-s) z).cexp).const_mul (s * B))
    rw [show (fun y => s * A * exp (s * y) - s * B * exp (-s * y)) =
      (fun y => s * A * exp (s * y)) - (fun y => s * B * exp (-s * y)) from rfl, this.deriv,
      hAB z, ← hs2]
    ring

end Azurite.DLMF
