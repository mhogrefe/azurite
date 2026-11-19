/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.Chudnovsky.Zeta
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Analytic.IsolatedZeros

/-!
# Quasi-periods of `ζ`, and `℘″`

* `quasiPeriod L l = ζ(ω₁/2 + l) − ζ(ω₁/2)` for a lattice point `l`, and
  `weierstrassZeta_add_coe`: `ζ(z + l) = ζ(z) + η(l)` off the lattice (the two sides have the
  same derivative `−℘` on the connected complement of the lattice);
* `quasiPeriod_add`, `quasiPeriod_int_combo`: `η` is additive,
  `η(mω₁ + nω₂) = m η(ω₁) + n η(ω₂)`;
* `quasiPeriod_eq_two_mul_zeta_half`: `η(l) = 2ζ(l/2)` when `l/2` is not a lattice point;
* `weierstrassZeta_half_add`: `ζ(ω₁/2 + mω₁ + nω₂) = η₁/2 + mη₁ + nη₂`;
* `deriv_derivWeierstrassP`: `℘″ = 6℘² − g₂/2` off the lattice (the derivative of
  `℘′² = 4℘³ − g₂℘ − g₃`, divided by `℘′ ≢ 0`).
-/

open Module Filter
open scoped Topology

namespace Azurite.Chudnovsky

open PeriodPair

variable (L : PeriodPair)

theorem isPreconnected_compl_lattice : IsPreconnected (L.lattice : Set ℂ)ᶜ :=
  (Set.Countable.isConnected_compl_of_one_lt_rank (by simp)
    (countable_of_Lindelof_of_discrete (X := L.lattice))).2

theorem isOpen_compl_lattice : IsOpen (L.lattice : Set ℂ)ᶜ := L.isClosed_lattice.isOpen_compl

theorem add_coe_notMem {z : ℂ} (hz : z ∉ L.lattice) (l : L.lattice) : z + l ∉ L.lattice :=
  fun h => hz (by simpa using sub_mem h l.2)

/-- The quasi-period `η(l) = ζ(z + l) − ζ(z)` of `ζ` for a lattice point `l`. -/
noncomputable def quasiPeriod (l : ℂ) : ℂ :=
  weierstrassZeta L (L.ω₁ / 2 + l) - weierstrassZeta L (L.ω₁ / 2)

/-- **`ζ(z + l) = ζ(z) + η(l)`** for a lattice point `l` and `z` off the lattice. -/
theorem weierstrassZeta_add_coe (l : L.lattice) {z : ℂ} (hz : z ∉ L.lattice) :
    weierstrassZeta L (z + l) = weierstrassZeta L z + quasiPeriod L l := by
  have hd : ∀ x ∈ (L.lattice : Set ℂ)ᶜ,
      DifferentiableAt ℂ (weierstrassZeta L) x := fun x hx =>
    (differentiableOn_weierstrassZeta L).differentiableAt ((isOpen_compl_lattice L).mem_nhds hx)
  have key := (isOpen_compl_lattice L).eqOn_of_deriv_eq (isPreconnected_compl_lattice L)
    (f := fun z => weierstrassZeta L (z + l))
    (g := fun z => weierstrassZeta L z + quasiPeriod L l)
    (fun x hx => by
      have := (hd (x + l) (add_coe_notMem L hx l)).comp x
        (by fun_prop : DifferentiableAt ℂ (fun z : ℂ => z + (l : ℂ)) x)
      exact this.differentiableWithinAt)
    (fun x hx => ((hd x hx).add_const _).differentiableWithinAt)
    (fun x hx => by
      rw [deriv_comp_add_const, deriv_add_const, deriv_weierstrassZeta L hx,
        deriv_weierstrassZeta L (add_coe_notMem L hx l), L.weierstrassP_add_coe])
    (x := L.ω₁ / 2) L.ω₁_div_two_notMem_lattice (by simp [quasiPeriod])
  exact key hz

/-- `η` is additive on the lattice. -/
theorem quasiPeriod_add (l l' : L.lattice) :
    quasiPeriod L (l + l' : ℂ) = quasiPeriod L l + quasiPeriod L l' := by
  have h0 := L.ω₁_div_two_notMem_lattice
  have h1 := weierstrassZeta_add_coe L l h0
  have h2 := weierstrassZeta_add_coe L l' (add_coe_notMem L h0 l)
  have h3 := weierstrassZeta_add_coe L (l + l') h0
  rw [Submodule.coe_add, ← add_assoc, h2, h1] at h3
  linear_combination -h3

/-- `η` as a homomorphism on the lattice. -/
noncomputable def quasiPeriodHom : L.lattice →+ ℂ where
  toFun l := quasiPeriod L l
  map_zero' := by simp [quasiPeriod]
  map_add' l l' := by
    rw [Submodule.coe_add]
    exact quasiPeriod_add L l l'

/-- `η(mω₁ + nω₂) = m η(ω₁) + n η(ω₂)`. -/
theorem quasiPeriod_int_combo (m n : ℤ) :
    quasiPeriod L (m * L.ω₁ + n * L.ω₂) = m * quasiPeriod L L.ω₁ + n * quasiPeriod L L.ω₂ := by
  have h := map_add (quasiPeriodHom L) (m • ⟨L.ω₁, L.ω₁_mem_lattice⟩)
    (n • ⟨L.ω₂, L.ω₂_mem_lattice⟩)
  rw [map_zsmul, map_zsmul] at h
  simpa [quasiPeriodHom, zsmul_eq_mul] using h

/-- `η(l) = 2ζ(l/2)` when `l/2` is not a lattice point. -/
theorem quasiPeriod_eq_two_mul_zeta_half (l : L.lattice) (hl : (l : ℂ) / 2 ∉ L.lattice) :
    quasiPeriod L l = 2 * weierstrassZeta L ((l : ℂ) / 2) := by
  have hneg : -((l : ℂ) / 2) ∉ L.lattice := fun h => hl (by simpa using neg_mem h)
  have h := weierstrassZeta_add_coe L l hneg
  rw [show -((l : ℂ) / 2) + l = (l : ℂ) / 2 by ring, weierstrassZeta_neg] at h
  linear_combination -h

/-- **The values of `ζ` at the points `ω₁/2 + mω₁ + nω₂`.** -/
theorem weierstrassZeta_half_add (m n : ℤ) :
    weierstrassZeta L (L.ω₁ / 2 + (m * L.ω₁ + n * L.ω₂))
      = quasiPeriod L L.ω₁ / 2 + (m * quasiPeriod L L.ω₁ + n * quasiPeriod L L.ω₂) := by
  have hmem : (m : ℂ) * L.ω₁ + n * L.ω₂ ∈ L.lattice := L.mem_lattice.mpr ⟨m, n, rfl⟩
  have h := weierstrassZeta_add_coe L ⟨_, hmem⟩ L.ω₁_div_two_notMem_lattice
  rw [h, quasiPeriod_int_combo,
    quasiPeriod_eq_two_mul_zeta_half L ⟨L.ω₁, L.ω₁_mem_lattice⟩ L.ω₁_div_two_notMem_lattice]
  ring

end Azurite.Chudnovsky
