/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.BasuPollackRoy.Chapter2.Section2_6.BoundedDenom
import Mathlib.RingTheory.HahnSeries.Summable

/-! # BPR §2.6 — the cumulative exponents and the limit Puiseux series `x̄`

Once the multiplicity stabilizes the recursion runs with `xₙ ≠ 0`, `ξₙ > 0`, and strictly increasing
exponents `ηₙ = Σ_{k≤n} ξₖ ∈ (1/M)ℤ`. This file builds the root `x̄ = Σₙ xₙ ε^{ηₙ}`.

* `InLattice M q` ("`q ∈ (1/M)ℤ`") + closure; `etaSeq`/`strictMono_etaSeq`/`etaSeq_inLattice`.
* The limit at integer-exponent level: `lfam : SummableFamily ℤ R ℕ`, `zlim := lfam.hsum`, and
  `xbar := puiseuxEmb R M zlim` — automatically a Puiseux series (`xbarP`), with its
  coefficients/order read off through `embDomain` (`xbar_coeff_eta`, `xbar_coeff_notMem`). -/

namespace Azurite.BPR

open Polynomial HahnSeries

variable {R : Type*} [Field R] [IsRealClosed R]

/-- `q` lies in the lattice `(1/M)ℤ`. -/
def InLattice (M : ℕ+) (q : ℚ) : Prop := ∃ k : ℤ, q = (k : ℚ) / (M : ℚ)

/-- The lattice grows as the denominator grows: `M₁ ∣ M₂ ⇒ (1/M₁)ℤ ⊆ (1/M₂)ℤ`. -/
theorem InLattice.mono {q : ℚ} {M₁ M₂ : ℕ+} (h : M₁ ∣ M₂) (hq : InLattice M₁ q) :
    InLattice M₂ q := by
  obtain ⟨k, hk⟩ := hq
  obtain ⟨t, ht⟩ := h
  have hdt : ((t : ℕ) : ℚ) ≠ 0 := by exact_mod_cast t.pos.ne'
  have hM₂ : ((M₂ : ℕ) : ℚ) = ((M₁ : ℕ) : ℚ) * ((t : ℕ) : ℚ) := by exact_mod_cast ht
  refine ⟨k * (t : ℤ), ?_⟩
  rw [hk, hM₂]; push_cast; rw [mul_div_mul_right _ _ hdt]

theorem inLattice_zero (M : ℕ+) : InLattice M 0 := ⟨0, by simp⟩

theorem InLattice.add {M : ℕ+} {a b : ℚ} (ha : InLattice M a) (hb : InLattice M b) :
    InLattice M (a + b) := by
  obtain ⟨k, hk⟩ := ha; obtain ⟨l, hl⟩ := hb
  exact ⟨k + l, by rw [hk, hl]; push_cast; ring⟩

theorem InLattice.sum {M : ℕ+} {ι : Type*} (s : Finset ι) {f : ι → ℚ}
    (hf : ∀ i ∈ s, InLattice M (f i)) : InLattice M (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction with
  | empty => rw [Finset.sum_empty]; exact inLattice_zero M
  | @insert a t ha ih =>
    rw [Finset.sum_insert ha]
    exact (hf a (Finset.mem_insert_self a t)).add
      (ih (fun i hi => hf i (Finset.mem_insert_of_mem hi)))

/-- Every rational lies in the lattice with denominator its own denominator. -/
theorem inLattice_den (q : ℚ) : InLattice ⟨q.den, q.pos⟩ q := by
  refine ⟨q.num, ?_⟩
  show q = (q.num : ℚ) / (q.den : ℚ)
  exact (Rat.num_div_den q).symm

/-- Finitely many rationals share a common denominator. -/
theorem exists_inLattice_finset {ι : Type*} (s : Finset ι) (f : ι → ℚ) :
    ∃ M : ℕ+, ∀ i ∈ s, InLattice M (f i) := by
  classical
  refine ⟨∏ i ∈ s, ⟨(f i).den, (f i).pos⟩, fun i hi => ?_⟩
  exact (inLattice_den (f i)).mono (Finset.dvd_prod_of_mem _ hi)

/-- The cumulative exponent `ηₙ = ξ₀ + ⋯ + ξₙ`, where `xₙ` sits at exponent `ηₙ` in `x̄`. -/
noncomputable def etaSeq (s0 : RecState R) (n : ℕ) : ℚ := ∑ k ∈ Finset.range (n + 1), xiSeq s0 k

/-- The cumulative exponents strictly increase (each increment `ξₙ > 0` away from the barrier). -/
theorem strictMono_etaSeq (s0 : RecState R) (hnb : ∀ n, (stateSeq s0 n).poly.coeff 0 ≠ 0) :
    StrictMono (etaSeq s0) := by
  apply strictMono_nat_of_lt_succ
  intro n
  have h : etaSeq s0 (n + 1) = etaSeq s0 n + xiSeq s0 (n + 1) := by
    simp only [etaSeq, Finset.sum_range_succ]
  rw [h]; linarith [xiSeq_pos s0 hnb (n + 1)]

/-- All cumulative exponents share one denominator: `ηₙ ∈ (1/M)ℤ`. -/
theorem etaSeq_inLattice (s0 : RecState R) : ∃ M : ℕ+, ∀ n, InLattice M (etaSeq s0 n) := by
  obtain ⟨N, Mt, hmem⟩ := stateSeq_xibeta_mem s0
  obtain ⟨Mh, hMh⟩ := exists_inLattice_finset (Finset.range N) (xiSeq s0)
  refine ⟨Mh * Mt, fun n => ?_⟩
  rw [etaSeq]
  apply InLattice.sum
  intro k _
  rcases lt_or_ge k N with hkN | hkN
  · exact (hMh k (Finset.mem_range.mpr hkN)).mono (dvd_mul_right Mh Mt)
  · exact InLattice.mono (dvd_mul_left Mt Mh) (hmem k hkN).1

/-- A common denominator `M` for every cumulative exponent `ηₙ`. -/
noncomputable def limM (s0 : RecState R) : ℕ+ := (etaSeq_inLattice s0).choose

/-- `ηₙ = γₙ / M`: the integer numerator of the cumulative exponent. -/
noncomputable def gammaSeq (s0 : RecState R) (n : ℕ) : ℤ := ((etaSeq_inLattice s0).choose_spec n).choose

theorem etaSeq_eq_gamma (s0 : RecState R) (n : ℕ) :
    etaSeq s0 n = (gammaSeq s0 n : ℚ) / (limM s0 : ℚ) :=
  ((etaSeq_inLattice s0).choose_spec n).choose_spec

/-- The integer numerators strictly increase (since `ηₙ` does and `M > 0`). -/
theorem strictMono_gammaSeq (s0 : RecState R) (hnb : ∀ n, (stateSeq s0 n).poly.coeff 0 ≠ 0) :
    StrictMono (gammaSeq s0) := by
  intro a b hab
  have h := strictMono_etaSeq s0 hnb hab
  rw [etaSeq_eq_gamma, etaSeq_eq_gamma] at h
  have hM : (0 : ℚ) < (limM s0 : ℚ) := by exact_mod_cast (limM s0).pos
  rw [div_lt_div_iff_of_pos_right hM] at h
  exact_mod_cast h

/-- The summable family `n ↦ xₙ ε^{γₙ}` of integer-exponent monomials. -/
noncomputable def lfam (s0 : RecState R) (hnb : ∀ n, (stateSeq s0 n).poly.coeff 0 ≠ 0) :
    SummableFamily ℤ R ℕ where
  toFun n := HahnSeries.single (gammaSeq s0 n) (xSeq s0 n)
  isPWO_iUnion_support' := by
    have hwf : WellFounded (Function.onFun (· < ·) (gammaSeq s0)) := by
      have heq : Function.onFun (· < ·) (gammaSeq s0) = ((· < ·) : ℕ → ℕ → Prop) := by
        ext a b; exact (strictMono_gammaSeq s0 hnb).lt_iff_lt
      rw [heq]; exact wellFounded_lt
    have hWF : (Set.range (gammaSeq s0)).IsWF := Set.wellFoundedOn_range.mpr hwf
    refine (hWF.isPWO).mono (Set.iUnion_subset (fun n => ?_))
    exact support_single_subset.trans (Set.singleton_subset_iff.mpr ⟨n, rfl⟩)
  finite_co_support' g := by
    refine Set.Finite.subset (s := {n | gammaSeq s0 n = g}) ?_ ?_
    · refine Set.Subsingleton.finite (fun a ha b hb => ?_)
      rw [Set.mem_ofPred_eq] at ha hb
      exact (strictMono_gammaSeq s0 hnb).injective (ha.trans hb.symm)
    · intro n hn
      rw [Set.mem_ofPred_eq] at hn ⊢
      by_contra hne
      exact hn (coeff_single_of_ne (Ne.symm hne))

/-- The integer-exponent limit `z = Σₙ xₙ ε^{γₙ} ∈ R⟦ℤ⟧`. -/
noncomputable def zlim (s0 : RecState R) (hnb : ∀ n, (stateSeq s0 n).poly.coeff 0 ≠ 0) :
    HahnSeries ℤ R := (lfam s0 hnb).hsum

/-- `z`'s coefficient at `γₘ` is exactly `xₘ` (only `n = m` contributes to the sum). -/
theorem zlim_coeff_gamma (s0 : RecState R) (hnb : ∀ n, (stateSeq s0 n).poly.coeff 0 ≠ 0) (m : ℕ) :
    (zlim s0 hnb).coeff (gammaSeq s0 m) = xSeq s0 m := by
  rw [zlim, SummableFamily.coeff_hsum]
  rw [finsum_eq_single _ m (fun n hn => ?_)]
  · show (HahnSeries.single (gammaSeq s0 m) (xSeq s0 m)).coeff (gammaSeq s0 m) = xSeq s0 m
    exact coeff_single_same _ _
  · show (HahnSeries.single (gammaSeq s0 n) (xSeq s0 n)).coeff (gammaSeq s0 m) = 0
    refine coeff_single_of_ne (fun h => hn ?_)
    exact (strictMono_gammaSeq s0 hnb).injective h.symm

/-- The support of `z` lives among the `γₙ`. -/
theorem zlim_support_subset (s0 : RecState R) (hnb : ∀ n, (stateSeq s0 n).poly.coeff 0 ≠ 0) :
    (zlim s0 hnb).support ⊆ Set.range (gammaSeq s0) := by
  refine SummableFamily.support_hsum_subset.trans (Set.iUnion_subset (fun n => ?_))
  exact support_single_subset.trans (Set.singleton_subset_iff.mpr ⟨n, rfl⟩)

omit [IsRealClosed R] in
/-- The exponent-scaling embedding reads off coefficients at the scaled exponent. -/
theorem puiseuxEmb_coeff (q : ℕ+) (a : HahnSeries ℤ R) (n : ℤ) :
    (puiseuxEmb R q a).coeff ((n : ℚ) / (q : ℚ)) = a.coeff n := by
  rw [puiseuxEmb, HahnSeries.embDomainRingHom_apply, ← puiseuxExpHom_apply q n]
  exact HahnSeries.embDomain_coeff

/-- The limit Puiseux series `x̄` as a raw Hahn series (`= ε`-scaling of `z`). -/
noncomputable def xbar (s0 : RecState R) (hnb : ∀ n, (stateSeq s0 n).poly.coeff 0 ≠ 0) :
    HahnSeries ℚ R := puiseuxEmb R (limM s0) (zlim s0 hnb)

theorem xbar_mem (s0 : RecState R) (hnb : ∀ n, (stateSeq s0 n).poly.coeff 0 ≠ 0) :
    xbar s0 hnb ∈ puiseuxSubfield R (limM s0) := by
  rw [xbar, puiseuxSubfield, RingHom.mem_fieldRange]; exact ⟨zlim s0 hnb, rfl⟩

/-- `x̄`'s coefficient at the exponent `ηₘ` is the root coefficient `xₘ`. -/
theorem xbar_coeff_eta (s0 : RecState R) (hnb : ∀ n, (stateSeq s0 n).poly.coeff 0 ≠ 0) (m : ℕ) :
    (xbar s0 hnb).coeff (etaSeq s0 m) = xSeq s0 m := by
  rw [xbar, etaSeq_eq_gamma, puiseuxEmb_coeff]
  exact zlim_coeff_gamma s0 hnb m

/-- The limit as an element of the field `R⟨⟨ε⟩⟩` (it is a Laurent series in `ε^{1/M}`). -/
noncomputable def xbarP (s0 : RecState R) (hnb : ∀ n, (stateSeq s0 n).poly.coeff 0 ≠ 0) :
    PuiseuxSeries R :=
  ⟨xbar s0 hnb, (mem_puiseuxSeries_iff R).mpr ⟨limM s0, xbar_mem s0 hnb⟩⟩

@[simp] theorem xbarP_coe (s0 : RecState R) (hnb : ∀ n, (stateSeq s0 n).poly.coeff 0 ≠ 0) :
    ((xbarP s0 hnb : PuiseuxSeries R) : HahnSeries ℚ R) = xbar s0 hnb := rfl

/-- `x̄` is supported only at the exponents `ηₙ`: off them, its coefficient vanishes. -/
theorem xbar_coeff_notMem (s0 : RecState R) (hnb : ∀ n, (stateSeq s0 n).poly.coeff 0 ≠ 0)
    {d : ℚ} (hd : ∀ n, d ≠ etaSeq s0 n) : (xbar s0 hnb).coeff d = 0 := by
  by_cases hdM : ∃ k : ℤ, d = (k : ℚ) / (limM s0 : ℚ)
  · obtain ⟨k, rfl⟩ := hdM
    rw [xbar, puiseuxEmb_coeff]
    by_contra hz
    have hk : k ∈ Set.range (gammaSeq s0) :=
      zlim_support_subset s0 hnb ((HahnSeries.mem_support _ _).mpr hz)
    obtain ⟨n, rfl⟩ := hk
    exact hd n (etaSeq_eq_gamma s0 n).symm
  · rw [xbar, puiseuxEmb, HahnSeries.embDomainRingHom_apply]
    apply HahnSeries.embDomain_of_notMem_range
    rintro ⟨k, hk⟩
    exact hdM ⟨k, by rw [← hk]; exact puiseuxExpHom_apply (limM s0) k⟩

end Azurite.BPR
