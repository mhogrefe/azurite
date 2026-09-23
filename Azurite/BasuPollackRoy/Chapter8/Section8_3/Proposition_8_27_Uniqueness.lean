/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.BasuPollackRoy.Chapter8.Section8_3.Proposition_8_27
import Mathlib.LinearAlgebra.Alternating.Basic
import Mathlib.LinearAlgebra.Multilinear.Basis
import Mathlib.Data.Fin.Tuple.Sort

/-!
# BPR Proposition 8.27: uniqueness

A multilinear alternating mapping `(𝓕_n)^m → 𝓕_{n-m+1}` is determined by its
values on strictly-decreasing monomial tuples. The route: bundle the predicates
into a Mathlib `AlternatingMap`, use the monomial basis of `𝓕_n` and
`Module.Basis.ext_multilinear` to reduce to monomial tuples, and reduce those to
strictly-decreasing ones via `AlternatingMap.map_perm`.
-/

namespace Azurite.BPR.Chapter8

open Polynomial

variable {K : Type*} [Field K] {m n : ℕ}

/-- `X^c` as an element of `𝓕_n` (`c : Fin n`). -/
noncomputable def monoElt (c : Fin n) : degreeLT K n :=
  ⟨X ^ (c : ℕ), by rw [mem_degreeLT, degree_X_pow]; exact_mod_cast c.isLt⟩

/-- Bundle an `IsMultilinear` map into a `MultilinearMap`. -/
noncomputable def toMLM (Φ : (Fin m → degreeLT K n) → degreeLT K (n - m + 1))
    (hΦ : IsMultilinear Φ) :
    MultilinearMap K (fun _ : Fin m => degreeLT K n) (degreeLT K (n - m + 1)) where
  toFun := Φ
  map_update_add' := by
    intro inst v i x y
    rw [Subsingleton.elim inst (instDecidableEqFin m)]
    simpa using hΦ v i 1 1 x y
  map_update_smul' := by
    intro inst v i c x
    rw [Subsingleton.elim inst (instDecidableEqFin m)]
    simpa using hΦ v i c 0 x x

/-- Bundle an `IsMultilinear`, `IsAlternating` map into an `AlternatingMap`. -/
noncomputable def toALT (Φ : (Fin m → degreeLT K n) → degreeLT K (n - m + 1))
    (hΦm : IsMultilinear Φ) (hΦa : IsAlternating Φ) :
    (degreeLT K n) [⋀^Fin m]→ₗ[K] (degreeLT K (n - m + 1)) where
  toMultilinearMap := toMLM Φ hΦm
  map_eq_zero_of_eq' := fun v i j hvij hij => hΦa v i j hij hvij

/-- The monomial basis `X^0, …, X^{n-1}` of `𝓕_n = degreeLT K n`. -/
noncomputable def monoBasis : Module.Basis (Fin n) K (degreeLT K n) :=
  (Pi.basisFun K (Fin n)).map (degreeLTEquiv K n).symm

theorem monoBasis_apply (c : Fin n) : (monoBasis (K := K) (n := n)) c = monoElt c := by
  rw [monoBasis, Module.Basis.map_apply, Pi.basisFun_apply]
  apply (degreeLTEquiv K n).injective
  rw [LinearEquiv.apply_symm_apply]
  funext i
  rw [Pi.single_apply]
  show (if i = c then (1 : K) else 0) = (X ^ (c : ℕ) : K[X]).coeff i
  rw [coeff_X_pow]
  by_cases h : i = c <;> simp [h, Fin.val_inj]

@[simp] theorem toMLM_apply (Φ : (Fin m → degreeLT K n) → degreeLT K (n - m + 1))
    (hΦ : IsMultilinear Φ) (v : Fin m → degreeLT K n) : toMLM Φ hΦ v = Φ v := rfl

@[simp] theorem toALT_apply (Φ : (Fin m → degreeLT K n) → degreeLT K (n - m + 1))
    (hΦm : IsMultilinear Φ) (hΦa : IsAlternating Φ) (v : Fin m → degreeLT K n) :
    toALT Φ hΦm hΦa v = Φ v := rfl

/-- Any injective `f : Fin m → ℕ` has a permutation sorting it strictly
    decreasing. -/
theorem exists_strictAnti_perm {m : ℕ} (f : Fin m → ℕ) (hf : Function.Injective f) :
    ∃ σ : Equiv.Perm (Fin m), StrictAnti (f ∘ ⇑σ) := by
  refine ⟨(Equiv.mk Fin.rev Fin.rev Fin.rev_rev Fin.rev_rev).trans (Tuple.sort f), ?_⟩
  have hsm : StrictMono (f ∘ ⇑(Tuple.sort f)) :=
    (Tuple.monotone_sort f).strictMono_of_injective (hf.comp (Tuple.sort f).injective)
  intro a b hab
  simp only [Function.comp_apply, Equiv.trans_apply, Equiv.coe_fn_mk]
  exact hsm (Fin.rev_lt_rev.mpr hab)

/-- **BPR Proposition 8.27 (uniqueness, key lemma).** A multilinear alternating
    mapping is determined by its values on strictly-decreasing monomial tuples. -/
theorem eq_of_multilinear_alternating
    {Φ Ψ : (Fin m → degreeLT K n) → degreeLT K (n - m + 1)}
    (hΦm : IsMultilinear Φ) (hΦa : IsAlternating Φ)
    (hΨm : IsMultilinear Ψ) (hΨa : IsAlternating Ψ)
    (hagree : ∀ c : Fin m → Fin n, StrictAnti (fun r => (c r : ℕ)) →
      Φ (fun r => monoElt (c r)) = Ψ (fun r => monoElt (c r))) :
    Φ = Ψ := by
  have hbasis : toMLM Φ hΦm = toMLM Ψ hΨm := by
    refine Module.Basis.ext_multilinear (fun _ : Fin m => monoBasis (K := K) (n := n)) ?_
    intro c
    simp only [toMLM_apply, monoBasis_apply]
    by_cases hinj : Function.Injective c
    · obtain ⟨σ, hσ⟩ := exists_strictAnti_perm (fun r => (c r : ℕ))
        (fun a b hab => hinj (Fin.val_injective hab))
      have hΦp := (toALT Φ hΦm hΦa).map_congr_perm (v := fun r => monoElt (c r)) σ
      have hΨp := (toALT Ψ hΨm hΨa).map_congr_perm (v := fun r => monoElt (c r)) σ
      simp only [toALT_apply, Function.comp_def] at hΦp hΨp
      rw [hΦp, hΨp]
      congr 1
      exact hagree (fun r => c (σ r)) hσ
    · obtain ⟨a, b, hcab, hab⟩ := Function.not_injective_iff.mp hinj
      rw [hΦa _ a b hab (congrArg monoElt hcab), hΨa _ a b hab (congrArg monoElt hcab)]
  funext v
  simpa using DFunLike.congr_fun hbasis v

/-- The last exponent of a strictly-decreasing tuple in `[0,n)` is `≤ n-m`. -/
theorem strictAnti_last_le {e : Fin m → ℕ} (hAnti : StrictAnti e) (he : ∀ r, e r < n)
    (last : Fin m) (hlast : (last : ℕ) + 1 = m) : e last ≤ n - m := by
  have hsub : Finset.univ.image e ⊆ Finset.Ico (e last) n := by
    intro x hx
    rw [Finset.mem_image] at hx
    obtain ⟨r, _, rfl⟩ := hx
    rw [Finset.mem_Ico]
    refine ⟨hAnti.antitone ?_, he r⟩
    rw [Fin.le_def]; have := r.isLt; omega
  have hcard : m ≤ n - e last :=
    calc m = (Finset.univ.image e).card := by
            rw [Finset.card_image_of_injective _ hAnti.injective, Finset.card_univ,
              Fintype.card_fin]
      _ ≤ (Finset.Ico (e last) n).card := Finset.card_le_card hsub
      _ = n - e last := Nat.card_Ico _ _
  omega

/-- The normalization condition of Proposition 8.27. -/
def Normalized (Φ : (Fin m → degreeLT K n) → degreeLT K (n - m + 1)) : Prop :=
  (∀ (e : Fin m → ℕ) (he : ∀ r, e r < n) (last : Fin m), (last : ℕ) + 1 = m →
    (∀ r : Fin m, (r : ℕ) + 1 < m → e r = n - 1 - (r : ℕ)) → ∀ (hi : e last ≤ n - m),
    Φ (monoFamily e he) = pdetMono ⟨e last, by omega⟩) ∧
  (∀ (e : Fin m → ℕ) (he : ∀ r, e r < n), StrictAnti e →
    (∃ r₀ : Fin m, (r₀ : ℕ) + 1 < m ∧ e r₀ ≠ n - 1 - (r₀ : ℕ)) →
    Φ (monoFamily e he) = 0)

/-- `pdet` is normalized. -/
theorem normalized_pdet (hmn : m ≤ n) :
    Normalized (pdet : (Fin m → degreeLT K n) → degreeLT K (n - m + 1)) :=
  ⟨fun e he last hlast hcond hi => normalization_pdet_pos e hmn last hlast he hcond hi,
   fun e he hAnti hne => normalization_pdet_zero e hmn he hAnti hne⟩

/-- A multilinear alternating normalized map agrees with another such map on
    strictly-decreasing monomial tuples; hence the two are equal. -/
theorem proposition_8_27_uniqueness (hm : 0 < m)
    {Φ Ψ : (Fin m → degreeLT K n) → degreeLT K (n - m + 1)}
    (hΦm : IsMultilinear Φ) (hΦa : IsAlternating Φ) (hΦn : Normalized Φ)
    (hΨm : IsMultilinear Ψ) (hΨa : IsAlternating Ψ) (hΨn : Normalized Ψ) :
    Φ = Ψ := by
  apply eq_of_multilinear_alternating hΦm hΦa hΨm hΨa
  intro c hc
  set e := fun r => (c r : ℕ) with he_def
  have he : ∀ r, e r < n := fun r => (c r).isLt
  have htuple : (fun r => monoElt (c r)) = monoFamily (K := K) e he := rfl
  rw [htuple]
  set last : Fin m := ⟨m - 1, by omega⟩ with hlast_def
  have hlast : (last : ℕ) + 1 = m := by simp only [hlast_def]; omega
  have hilast : e last ≤ n - m := strictAnti_last_le hc he last hlast
  by_cases hcond : ∀ r : Fin m, (r : ℕ) + 1 < m → e r = n - 1 - (r : ℕ)
  · rw [hΦn.1 e he last hlast hcond hilast, hΨn.1 e he last hlast hcond hilast]
  · push Not at hcond
    obtain ⟨r₀, hr₀⟩ := hcond
    rw [hΦn.2 e he hc ⟨r₀, hr₀.1, hr₀.2⟩, hΨn.2 e he hc ⟨r₀, hr₀.1, hr₀.2⟩]

/-- **BPR Proposition 8.27.** There is a unique multilinear alternating mapping
    `(𝓕_n)^m → 𝓕_{n-m+1}` with the normalization values of Proposition 8.27, namely
    the polynomial determinant `pdet`. -/
theorem proposition_8_27 (hm : 0 < m) (hmn : m ≤ n) :
    ∃! Φ : (Fin m → degreeLT K n) → degreeLT K (n - m + 1),
      IsMultilinear Φ ∧ IsAlternating Φ ∧ Normalized Φ := by
  refine ⟨pdet, ⟨isMultilinear_pdet, isAlternating_pdet, normalized_pdet hmn⟩, ?_⟩
  rintro Ψ ⟨hΨm, hΨa, hΨn⟩
  exact proposition_8_27_uniqueness hm hΨm hΨa hΨn isMultilinear_pdet isAlternating_pdet
    (normalized_pdet hmn)

end Azurite.BPR.Chapter8
