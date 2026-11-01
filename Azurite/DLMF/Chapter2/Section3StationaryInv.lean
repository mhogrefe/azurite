/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/


import Azurite.DLMF.Chapter2.Section3StationaryExp
import Azurite.DLMF.Chapter2.Section3StationaryPhase

/-!
# DLMF §2.3(iv): the substitution `v = p(t) − p(a)`

* `exists_smooth_inverse`: a smooth inverse of a smooth function with positive derivative on an
  open set (via Mathlib's `HasStrictDerivAt.to_local_left_inverse`).
* `contDiffOn_statP`, `iteratedDeriv_statP_comp`: the `Pₛ` are smooth and
  `(d/dv)ᵏ (P₀ ∘ t) = Pₖ ∘ t`.
-/

open Set Filter Topology Asymptotics
open scoped ContDiff

namespace Azurite.DLMF

theorem contDiffOn_deriv_of_isOpen {f : ℝ → ℝ} {S : Set ℝ} (hS : IsOpen S)
    (hf : ContDiffOn ℝ ∞ f S) : ContDiffOn ℝ ∞ (deriv f) S :=
  ((contDiffOn_succ_iff_deriv_of_isOpen (n := ∞) hS).mp (by simpa using hf)).2.2

theorem contDiffOn_deriv_of_isOpen_complex {f : ℝ → ℂ} {S : Set ℝ} (hS : IsOpen S)
    (hf : ContDiffOn ℝ ∞ f S) : ContDiffOn ℝ ∞ (deriv f) S :=
  ((contDiffOn_succ_iff_deriv_of_isOpen (n := ∞) hS).mp (by simpa using hf)).2.2

/-- A smooth inverse of a smooth strictly increasing function with positive derivative on an open
set. -/
theorem exists_smooth_inverse {v v' : ℝ → ℝ} {S : Set ℝ} (hS : IsOpen S)
    (hv : ContDiffOn ℝ ∞ v S) (hd : ∀ t ∈ S, HasDerivAt v (v' t) t)
    (hpos : ∀ t ∈ S, 0 < v' t) (hmono : StrictMonoOn v S) :
    ∃ g : ℝ → ℝ, IsOpen (v '' S) ∧ (∀ t ∈ S, g (v t) = t) ∧
      (∀ w ∈ v '' S, g w ∈ S ∧ v (g w) = w) ∧ ContDiffOn ℝ ∞ g (v '' S) ∧
      ∀ w ∈ v '' S, HasDerivAt g (v' (g w))⁻¹ w := by
  set g := Function.invFunOn v S
  have hgw : ∀ w ∈ v '' S, g w ∈ S ∧ v (g w) = w := fun w hw =>
    Function.invFunOn_pos (by obtain ⟨t, ht, rfl⟩ := hw; exact ⟨t, ht, rfl⟩)
  have hgv : ∀ t ∈ S, g (v t) = t := fun t ht => by
    have h := hgw (v t) ⟨t, ht, rfl⟩
    exact hmono.injOn h.1 ht h.2
  have hstrict : ∀ t ∈ S, HasStrictDerivAt v (v' t) t := fun t ht => by
    have h := (hv t ht).contDiffAt (hS.mem_nhds ht) |>.hasStrictDerivAt (by simp)
    rwa [(hd t ht).deriv] at h
  have hopen : IsOpen (v '' S) := by
    rw [isOpen_iff_mem_nhds]
    rintro _ ⟨t, ht, rfl⟩
    rw [← (hstrict t ht).map_nhds_eq (hpos t ht).ne']
    exact image_mem_map (hS.mem_nhds ht)
  have hderiv : ∀ w ∈ v '' S, HasDerivAt g (v' (g w))⁻¹ w := by
    rintro _ ⟨t, ht, rfl⟩
    rw [hgv t ht]
    have h := (hstrict t ht).to_local_left_inverse (hpos t ht).ne'
      (Filter.eventually_of_mem (hS.mem_nhds ht) fun x hx => hgv x hx)
    exact h.hasDerivAt
  have hv' : ContDiffOn ℝ ∞ v' S :=
    (contDiffOn_deriv_of_isOpen hS hv).congr fun t ht => ((hd t ht).deriv).symm
  refine ⟨g, hopen, hgv, hgw, ?_, hderiv⟩
  refine contDiffOn_infty.mpr fun n => ?_
  induction n with
  | zero =>
    exact contDiffOn_zero.mpr fun w hw => (hderiv w hw).continuousAt.continuousWithinAt
  | succ n ih =>
    rw [Nat.cast_succ]
    refine (contDiffOn_succ_iff_deriv_of_isOpen (n := (n : WithTop ℕ∞)) hopen).mpr ⟨fun w hw =>
      (hderiv w hw).differentiableAt.differentiableWithinAt,
      fun h => absurd h WithTop.coe_ne_top, ?_⟩
    have h1 : ContDiffOn ℝ n (fun w => (v' (g w))⁻¹) (v '' S) :=
      ((hv'.of_le (by exact_mod_cast le_top)).comp ih fun w hw => (hgw w hw).1).inv
        fun w hw => (hpos _ (hgw w hw).1).ne'
    exact h1.congr fun w hw => (hderiv w hw).deriv

section Transport

variable {p p' : ℝ → ℝ} {q : ℝ → ℂ} {S : Set ℝ} (hS : IsOpen S) (hp : ContDiffOn ℝ ∞ p S)
  (hd : ∀ t ∈ S, HasDerivAt p (p' t) t) (hpos : ∀ t ∈ S, 0 < p' t) (hq : ContDiffOn ℝ ∞ q S)
include hS hp hd hpos hq

theorem contDiffOn_statP (k : ℕ) : ContDiffOn ℝ ∞ (statP p' q k) S := by
  have hp' : ContDiffOn ℝ ∞ p' S :=
    (contDiffOn_deriv_of_isOpen hS hp).congr fun t ht => ((hd t ht).deriv).symm
  have hp'c : ContDiffOn ℝ ∞ (fun t => (p' t : ℂ)) S :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn hp'
  have hne : ∀ t ∈ S, (p' t : ℂ) ≠ 0 := fun t ht =>
    Complex.ofReal_ne_zero.mpr (hpos t ht).ne'
  induction k with
  | zero => exact (hq.mul (hp'c.inv hne)).congr fun t _ => div_eq_mul_inv _ _
  | succ k ih =>
    exact ((contDiffOn_deriv_of_isOpen_complex hS ih).mul (hp'c.inv hne)).congr
      fun t _ => div_eq_mul_inv _ _

omit hp hd hpos hq in
theorem hasDerivAt_comp_inverse {g : ℝ → ℝ} {T : Set ℝ} (hgS : ∀ w ∈ T, g w ∈ S)
    {F : ℝ → ℂ} (hF : ContDiffOn ℝ ∞ F S)
    (hg : ∀ w ∈ T, HasDerivAt g (p' (g w))⁻¹ w) {w : ℝ} (hw : w ∈ T) :
    HasDerivAt (fun w => F (g w)) (dopF p' F (g w)) w := by
  have hFd := ((hF (g w) (hgS w hw)).contDiffAt (hS.mem_nhds (hgS w hw))).differentiableAt
    (by simp)
  have h := hFd.hasDerivAt.scomp w (hg w hw)
  refine HasDerivAt.congr_deriv (f := fun w => F (g w)) h ?_
  show (p' (g w))⁻¹ • deriv F (g w) = deriv F (g w) / (p' (g w) : ℂ)
  rw [Complex.real_smul, Complex.ofReal_inv, div_eq_inv_mul]


/-- `(d/dv)ᵏ (P₀ ∘ t) = Pₖ ∘ t`. -/
theorem iteratedDeriv_statP_comp {g : ℝ → ℝ} {T : Set ℝ} (hT : IsOpen T)
    (hgS : ∀ w ∈ T, g w ∈ S) (hg : ∀ w ∈ T, HasDerivAt g (p' (g w))⁻¹ w) (k : ℕ) {w : ℝ}
    (hw : w ∈ T) :
    iteratedDeriv k (fun w => statP p' q 0 (g w)) w = statP p' q k (g w) := by
  induction k generalizing w with
  | zero => simp
  | succ k ih =>
    have hev : iteratedDeriv k (fun w => statP p' q 0 (g w)) =ᶠ[𝓝 w]
        fun w => statP p' q k (g w) :=
      Filter.eventually_of_mem (hT.mem_nhds hw) fun u hu => ih hu
    rw [iteratedDeriv_succ, hev.deriv_eq]
    exact (hasDerivAt_comp_inverse hS hgS (contDiffOn_statP hS hp hd hpos hq k) hg hw).deriv

theorem contDiffOn_statP_comp {g : ℝ → ℝ} {T : Set ℝ} (hgS : ∀ w ∈ T, g w ∈ S)
    (hgc : ContDiffOn ℝ ∞ g T) :
    ContDiffOn ℝ ∞ (fun w => statP p' q 0 (g w)) T :=
  (contDiffOn_statP hS hp hd hpos hq 0).comp hgc hgS

end Transport

end Azurite.DLMF
