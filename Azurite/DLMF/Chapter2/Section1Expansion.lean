/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/


import Azurite.DLMF.Chapter2.Section1Ritt
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Topology.Algebra.Polynomial

/-!
# DLMF §2.1(iii): asymptotic expansions

* `HasPowExpansion l y f A`: `f − ∑_{s<n} aₛyˢ = O(yⁿ)` for all `n`, `y → 0` along `l`, with
  `A` a formal power series; addition, scalar multiplication, multiplication (Cauchy product),
  reciprocal and division (`HasPowExpansion.mul`, `.inv`, `.div`), the limit form
  `hasPowExpansion_iff_tendsto`, and uniqueness `HasPowExpansion.unique`.
* 2.1.13–2.1.14: `IsAsympExpansionDLMF X f a` (literal, `x → ∞` in `𝐗`), equivalent to
  `HasPowExpansion` in `y = x⁻¹`; `dlmf_2_1_15`; `dlmf_2_1_iii_unique` (`𝐗` unbounded).
* 2.1.16: `IsAsympExpansionAtDLMF X c f a`, `dlmf_2_1_16_iff_tendsto`, `dlmf_2_1_iii_unique_at`.
* `dlmf_2_1_iii_convergent`: a convergent `∑ aₛx^{−s}` is the expansion of its sum.
* `dlmf_2_1_iii_add`, `_sub`, `_const_mul`, `_mul`, `_div`: algebraic operations.
* `dlmf_2_1_iii_deriv`: termwise differentiation in a properly interior closed sector (Ritt);
  `dlmf_2_1_iii_deriv_counterexample`: without such conditions it fails (`e^{−x} sin(eˣ)`).
* `dlmf_2_1_17`: null expansions of `0`, `e^{−z}`, `e^{−√z}` in `|ph z| ≤ ½π − δ`.
-/

open Set Filter Topology Asymptotics PowerSeries

namespace Azurite.DLMF

/-! ### Expansions in powers of a variable tending to `0` -/

section General

variable {α 𝕜 : Type*} [NormedField 𝕜] {l : Filter α} {y f g : α → 𝕜}

theorem eval_trunc_eq_sum (n : ℕ) (A : 𝕜⟦X⟧) (t : 𝕜) :
    (trunc n A).eval t = ∑ i ∈ Finset.range n, coeff i A * t ^ i :=
  eval₂_trunc_eq_sum_range t (RingHom.id 𝕜) n A

/-- `f` has the (Poincaré) expansion `A` in powers of `y → 0` along `l`: for every `n`,
`f − ∑_{s<n} aₛ yˢ = O(yⁿ)`. -/
def HasPowExpansion (l : Filter α) (y f : α → 𝕜) (A : 𝕜⟦X⟧) : Prop :=
  ∀ n : ℕ, (fun x => f x - (trunc n A).eval (y x)) =O[l] fun x => y x ^ n

/-- A polynomial with no terms below degree `n` is `O(yⁿ)`. -/
theorem isBigO_eval_of_coeff_eq_zero (hy : Tendsto y l (𝓝 0)) {p : Polynomial 𝕜} {n : ℕ}
    (hp : ∀ d < n, p.coeff d = 0) : (fun x => p.eval (y x)) =O[l] fun x => y x ^ n := by
  obtain ⟨q, rfl⟩ := Polynomial.X_pow_dvd_iff.mpr hp
  have hq : Tendsto (fun x => q.eval (y x)) l (𝓝 (q.eval 0)) :=
    (q.continuous.tendsto 0).comp hy
  have := (isBigO_refl (fun x => y x ^ n) l).mul (hq.isBigO_one 𝕜)
  simpa using this

/-- A polynomial in `y` is its own expansion. -/
theorem hasPowExpansion_polynomial (hy : Tendsto y l (𝓝 0)) (p : Polynomial 𝕜) :
    HasPowExpansion l y (fun x => p.eval (y x)) (p : 𝕜⟦X⟧) := fun n => by
  have := isBigO_eval_of_coeff_eq_zero hy (p := p - trunc n (p : 𝕜⟦X⟧)) (n := n) fun d hd => by
    rw [Polynomial.coeff_sub, coeff_trunc, ite_eq_left_iff.mpr (fun h => absurd hd h),
      Polynomial.coeff_coe, sub_self]
  simpa only [Polynomial.eval_sub] using this

theorem HasPowExpansion.isBigO_one (hy : Tendsto y l (𝓝 0)) {A : 𝕜⟦X⟧}
    (hf : HasPowExpansion l y f A) : f =O[l] fun _ => (1 : 𝕜) := by
  have h1 := hf 1
  simp only [pow_one] at h1
  have hc : (fun x => (trunc 1 A).eval (y x)) =O[l] fun _ => (1 : 𝕜) :=
    ((Polynomial.continuous _).tendsto 0 |>.comp hy).isBigO_one 𝕜
  simpa using (h1.trans (hy.isBigO_one 𝕜)).add hc

theorem HasPowExpansion.tendsto (hy : Tendsto y l (𝓝 0)) {A : 𝕜⟦X⟧}
    (hf : HasPowExpansion l y f A) : Tendsto f l (𝓝 (constantCoeff A)) := by
  have h1 := (hf 1).trans_tendsto (by simpa using hy)
  simp only [trunc_one_left, Polynomial.eval_C] at h1
  simpa using h1.add_const (coeff 0 A)

theorem HasPowExpansion.add {A B : 𝕜⟦X⟧} (hf : HasPowExpansion l y f A)
    (hg : HasPowExpansion l y g B) : HasPowExpansion l y (f + g) (A + B) := fun n => by
  refine ((hf n).add (hg n)).congr_left fun x => ?_
  simp only [Pi.add_apply, map_add, Polynomial.eval_add]; ring

theorem HasPowExpansion.neg {A : 𝕜⟦X⟧} (hf : HasPowExpansion l y f A) :
    HasPowExpansion l y (-f) (-A) := fun n => by
  refine (hf n).neg_left.congr_left fun x => ?_
  simp only [Pi.neg_apply, map_neg, Polynomial.eval_neg]; ring

theorem HasPowExpansion.sub {A B : 𝕜⟦X⟧} (hf : HasPowExpansion l y f A)
    (hg : HasPowExpansion l y g B) : HasPowExpansion l y (f - g) (A - B) := by
  simpa [sub_eq_add_neg] using hf.add hg.neg

theorem HasPowExpansion.const_mul (c : 𝕜) {A : 𝕜⟦X⟧} (hf : HasPowExpansion l y f A) :
    HasPowExpansion l y (fun x => c * f x) (C c * A) := fun n => by
  refine ((hf n).const_mul_left c).congr_left fun x => ?_
  rw [trunc_C_mul, Polynomial.eval_mul, Polynomial.eval_C]; ring

/-- Multiplication of asymptotic expansions (Cauchy product). -/
theorem HasPowExpansion.mul (hy : Tendsto y l (𝓝 0)) {A B : 𝕜⟦X⟧}
    (hf : HasPowExpansion l y f A) (hg : HasPowExpansion l y g B) :
    HasPowExpansion l y (f * g) (A * B) := fun n => by
  have hg1 := hg.isBigO_one hy
  have hTA : (fun x => (trunc n A).eval (y x)) =O[l] fun _ => (1 : 𝕜) :=
    ((Polynomial.continuous _).tendsto 0 |>.comp hy).isBigO_one 𝕜
  have h3 := isBigO_eval_of_coeff_eq_zero hy
    (p := trunc n A * trunc n B - trunc n (A * B)) (n := n) fun d hd => by
      have e : (trunc n A * trunc n B).coeff d =
          (trunc n ((trunc n A : 𝕜⟦X⟧) * (trunc n B : 𝕜⟦X⟧))).coeff d := by
        rw [coeff_trunc, ite_eq_left_iff.mpr (fun h => absurd hd h), ← Polynomial.coe_mul,
          Polynomial.coeff_coe]
      rw [Polynomial.coeff_sub, e, trunc_trunc_mul_trunc, sub_self]
  have h1 := ((hf n).mul hg1).congr_right (fun x => mul_one _)
  have h2 := (hTA.mul (hg n)).congr_right (fun x => one_mul _)
  refine ((h1.add h2).add h3).congr_left fun x => ?_
  simp only [Pi.mul_apply, Polynomial.eval_sub, Polynomial.eval_mul]; ring

theorem trunc_zero' (A : 𝕜⟦X⟧) : trunc 0 A = 0 := by
  ext d; simp

/-- Reciprocal of an asymptotic expansion with nonzero leading coefficient. -/
theorem HasPowExpansion.inv (hy : Tendsto y l (𝓝 0)) {B : 𝕜⟦X⟧}
    (hg : HasPowExpansion l y g B) (hB : constantCoeff B ≠ 0) :
    HasPowExpansion l y (fun x => (g x)⁻¹) B⁻¹ := by
  have hgt := hg.tendsto hy
  have hginv : (fun x => (g x)⁻¹) =O[l] fun _ => (1 : 𝕜) := (hgt.inv₀ hB).isBigO_one 𝕜
  have hg0 : ∀ᶠ x in l, g x ≠ 0 := hgt.eventually_ne hB
  intro n
  cases n with
  | zero => simpa [trunc_zero'] using hginv
  | succ n =>
    set P := trunc (n + 1) B⁻¹
    have hprod := (hg.mul hy (hasPowExpansion_polynomial hy P)) (n + 1)
    have h1 : trunc (n + 1) (B * (P : 𝕜⟦X⟧)) = 1 := by
      rw [trunc_mul_trunc, PowerSeries.mul_inv_cancel B hB, trunc_one]
    rw [h1] at hprod
    refine ((hginv.mul hprod).neg_left.congr' ?_ (Eventually.of_forall fun x => one_mul _))
    filter_upwards [hg0] with x hx
    simp only [Pi.mul_apply, Polynomial.eval_one]
    field_simp
    ring

/-- Division of asymptotic expansions. -/
theorem HasPowExpansion.div (hy : Tendsto y l (𝓝 0)) {A B : 𝕜⟦X⟧}
    (hf : HasPowExpansion l y f A) (hg : HasPowExpansion l y g B) (hB : constantCoeff B ≠ 0) :
    HasPowExpansion l y (f / g) (A * B⁻¹) := by
  have := hf.mul hy (hg.inv hy hB)
  convert this using 1
  funext x; simp [div_eq_mul_inv]

theorem HasPowExpansion.comp_tendsto {β : Type*} {l' : Filter β} {k : β → α} {A : 𝕜⟦X⟧}
    (hf : HasPowExpansion l y f A) (hk : Tendsto k l' l) :
    HasPowExpansion l' (y ∘ k) (f ∘ k) A := fun n => (hf n).comp_tendsto hk

/-- The coefficients as limits (the form of 2.1.15). -/
theorem hasPowExpansion_iff_tendsto (hy : Tendsto y l (𝓝 0)) (hy0 : ∀ᶠ x in l, y x ≠ 0)
    {A : 𝕜⟦X⟧} : HasPowExpansion l y f A ↔
      ∀ n, Tendsto (fun x => (f x - (trunc n A).eval (y x)) / y x ^ n) l (𝓝 (coeff n A)) := by
  constructor
  · intro hf n
    have h := (hf (n + 1)).mul (isBigO_refl (fun x => (y x ^ n)⁻¹) l)
    have h' : (fun x => (f x - (trunc (n + 1) A).eval (y x)) * (y x ^ n)⁻¹) =O[l] y :=
      h.congr' EventuallyEq.rfl (by
        filter_upwards [hy0] with x hx
        field_simp
        ring)
    have ht := (h'.trans_tendsto hy).add_const (coeff n A)
    rw [zero_add] at ht
    refine ht.congr' ?_
    filter_upwards [hy0] with x hx
    rw [trunc_succ, Polynomial.eval_add, Polynomial.eval_monomial]
    field_simp
    ring
  · intro h n
    have hb := (h n).isBigO_one 𝕜
    refine (hb.mul (isBigO_refl (fun x => y x ^ n) l)).congr' ?_ (Eventually.of_forall
      fun x => one_mul _)
    filter_upwards [hy0] with x hx
    field_simp

/-- Uniqueness of asymptotic expansions. -/
theorem HasPowExpansion.unique [l.NeBot] (hy : Tendsto y l (𝓝 0)) (hy0 : ∀ᶠ x in l, y x ≠ 0)
    {A B : 𝕜⟦X⟧} (hA : HasPowExpansion l y f A) (hB : HasPowExpansion l y f B) : A = B := by
  have hA' := (hasPowExpansion_iff_tendsto hy hy0).mp hA
  have hB' := (hasPowExpansion_iff_tendsto hy hy0).mp hB
  have key : ∀ n, trunc n A = trunc n B := by
    intro n
    induction n with
    | zero => rw [trunc_zero', trunc_zero']
    | succ n ih =>
      have hc : coeff n A = coeff n B := by
        have := hB' n
        rw [← ih] at this
        exact tendsto_nhds_unique (hA' n) this
      rw [trunc_succ, trunc_succ, ih, hc]
  ext m
  have h := congrArg (fun p : Polynomial 𝕜 => p.coeff m) (key (m + 1))
  simpa [coeff_trunc] using h

end General

/-! ### Poincaré expansions at infinity (2.1.13–2.1.15) -/

section Infinity

variable {𝕜 : Type*} [NormedField 𝕜]

/-- **DLMF 2.1.13–2.1.14**: `f(x) ∼ a₀ + a₁x⁻¹ + a₂x⁻² + ⋯` as `x → ∞` in `𝐗`: for each positive
integer `n`, `f(x) = ∑_{s=0}^{n−1} aₛx^{−s} + O(x^{−n})`. -/
def IsAsympExpansionDLMF (X : Set 𝕜) (f : 𝕜 → 𝕜) (a : ℕ → 𝕜) : Prop :=
  ∀ n : ℕ, 0 < n → IsBigODLMF (Bornology.cobounded 𝕜 ⊓ 𝓟 X)
    (fun x => f x - ∑ s ∈ Finset.range n, a s * x ^ (-(s : ℤ))) fun x => x ^ (-(n : ℤ))

theorem tendsto_inv_atInf (X : Set 𝕜) :
    Tendsto (fun x : 𝕜 => x⁻¹) (Bornology.cobounded 𝕜 ⊓ 𝓟 X) (𝓝 0) :=
  tendsto_inv₀_cobounded.mono_left inf_le_left

theorem eventually_ne_zero_atInf (X : Set 𝕜) :
    ∀ᶠ x in Bornology.cobounded 𝕜 ⊓ 𝓟 X, x ≠ 0 := by
  have h : ({0}ᶜ : Set 𝕜) ∈ Bornology.cobounded 𝕜 :=
    Bornology.isBounded_def.mp Bornology.isBounded_singleton
  exact mem_inf_of_left h

theorem zpow_neg_natCast_eq (x : 𝕜) (n : ℕ) : x ^ (-(n : ℤ)) = x⁻¹ ^ n := by
  rw [zpow_neg, zpow_natCast, inv_pow]

theorem sum_zpow_eq_eval (a : ℕ → 𝕜) (n : ℕ) (x : 𝕜) :
    ∑ s ∈ Finset.range n, a s * x ^ (-(s : ℤ)) = (trunc n (mk a)).eval x⁻¹ := by
  rw [eval_trunc_eq_sum]
  simp only [coeff_mk, zpow_neg_natCast_eq]

theorem isAsympExpansionDLMF_iff {X : Set 𝕜} {f : 𝕜 → 𝕜} {a : ℕ → 𝕜} :
    IsAsympExpansionDLMF X f a ↔
      HasPowExpansion (Bornology.cobounded 𝕜 ⊓ 𝓟 X) (fun x => x⁻¹) f (mk a) := by
  have hne := eventually_ne_zero_atInf X
  have hφ : ∀ n : ℕ, ∀ᶠ x in Bornology.cobounded 𝕜 ⊓ 𝓟 X, x ^ (-(n : ℤ)) ≠ 0 := fun n =>
    hne.mono fun x hx => zpow_ne_zero _ hx
  have key : ∀ n : ℕ, IsBigODLMF (Bornology.cobounded 𝕜 ⊓ 𝓟 X)
      (fun x => f x - ∑ s ∈ Finset.range n, a s * x ^ (-(s : ℤ))) (fun x => x ^ (-(n : ℤ))) ↔
      (fun x => f x - (trunc n (mk a)).eval x⁻¹) =O[Bornology.cobounded 𝕜 ⊓ 𝓟 X]
        fun x => x⁻¹ ^ n := fun n => by
    rw [dlmf_2_1_3 (hφ n)]
    simp only [sum_zpow_eq_eval]
    simp only [zpow_neg_natCast_eq]
  constructor
  · intro h n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · have h1 := (key 1).mp (h 1 one_pos)
      simp only [pow_one] at h1
      have hc : (fun x : 𝕜 => (trunc 1 (mk a)).eval x⁻¹) =O[Bornology.cobounded 𝕜 ⊓ 𝓟 X]
          fun _ => (1 : 𝕜) := by
        simp only [trunc_one_left, Polynomial.eval_C]
        exact isBigO_const_const _ one_ne_zero _
      simpa [trunc_zero'] using (h1.trans ((tendsto_inv_atInf X).isBigO_one 𝕜)).add hc
    · exact (key n).mp (h n hn)
  · exact fun h n _ => (key n).mpr (h n)

/-- **DLMF 2.1.15**: 2.1.13 is equivalent to `xⁿ(f(x) − ∑_{s=0}^{n−1} aₛx^{−s}) → aₙ` for each
`n ≥ 0`. -/
theorem dlmf_2_1_15 {X : Set 𝕜} {f : 𝕜 → 𝕜} {a : ℕ → 𝕜} :
    IsAsympExpansionDLMF X f a ↔ ∀ n : ℕ, Tendsto
      (fun x => x ^ n * (f x - ∑ s ∈ Finset.range n, a s * x ^ (-(s : ℤ))))
      (Bornology.cobounded 𝕜 ⊓ 𝓟 X) (𝓝 (a n)) := by
  rw [isAsympExpansionDLMF_iff, hasPowExpansion_iff_tendsto (tendsto_inv_atInf X)
    ((eventually_ne_zero_atInf X).mono fun _ h => inv_ne_zero h)]
  refine forall_congr' fun n => ?_
  simp only [coeff_mk, sum_zpow_eq_eval, inv_pow, div_inv_eq_mul, mul_comm]

theorem atInf_neBot {X : Set 𝕜} (hX : ¬ Bornology.IsBounded X) :
    (Bornology.cobounded 𝕜 ⊓ 𝓟 X).NeBot := by
  rw [inf_principal_neBot_iff]
  intro U hU
  by_contra h
  rw [not_nonempty_iff_eq_empty] at h
  apply hX
  have hb : Bornology.IsBounded Uᶜ := Bornology.isBounded_def.mpr (by rwa [compl_compl])
  refine hb.subset fun x hx hxU => ?_
  exact (eq_empty_iff_forall_notMem.mp h) x ⟨hxU, hx⟩

/-- **DLMF §2.1(iii)**: asymptotic expansions of the form 2.1.14 are unique (`𝐗` unbounded). -/
theorem dlmf_2_1_iii_unique {X : Set 𝕜} (hX : ¬ Bornology.IsBounded X) {f : 𝕜 → 𝕜}
    {a b : ℕ → 𝕜} (ha : IsAsympExpansionDLMF X f a) (hb : IsAsympExpansionDLMF X f b) : a = b := by
  have := atInf_neBot hX
  have h := (isAsympExpansionDLMF_iff.mp ha).unique (tendsto_inv_atInf X)
    ((eventually_ne_zero_atInf X).mono fun _ h => inv_ne_zero h) (isAsympExpansionDLMF_iff.mp hb)
  funext n
  simpa using congrArg (coeff n) h

end Infinity

/-! ### Expansions at a finite limit point (2.1.16) -/

section Finite

variable {𝕜 : Type*} [NormedField 𝕜]

/-- **DLMF 2.1.16**: `f(x) ∼ a₀ + a₁(x − c) + a₂(x − c)² + ⋯` as `x → c` in `𝐗`: for each `n`,
`f(x) − ∑_{s=0}^{n−1} aₛ(x − c)ˢ = O((x − c)ⁿ)`. -/
def IsAsympExpansionAtDLMF (X : Set 𝕜) (c : 𝕜) (f : 𝕜 → 𝕜) (a : ℕ → 𝕜) : Prop :=
  ∀ n : ℕ, IsBigODLMF (approachIn X c)
    (fun x => f x - ∑ s ∈ Finset.range n, a s * (x - c) ^ s) fun x => (x - c) ^ n

theorem tendsto_sub_approachIn (X : Set 𝕜) (c : 𝕜) :
    Tendsto (fun x => x - c) (approachIn X c) (𝓝 0) := by
  have := ((continuous_sub_right c).tendsto c).mono_left (nhdsWithin_le_nhds (s := X \ {c}))
  simpa [approachIn] using this

theorem eventually_sub_ne_zero_approachIn (X : Set 𝕜) (c : 𝕜) :
    ∀ᶠ x in approachIn X c, x - c ≠ 0 :=
  Filter.mem_of_superset (self_mem_nhdsWithin (s := X \ {c}) (a := c))
    fun _ hx => sub_ne_zero.mpr hx.2

theorem isAsympExpansionAtDLMF_iff {X : Set 𝕜} {c : 𝕜} {f : 𝕜 → 𝕜} {a : ℕ → 𝕜} :
    IsAsympExpansionAtDLMF X c f a ↔
      HasPowExpansion (approachIn X c) (fun x => x - c) f (mk a) := by
  refine forall_congr' fun n => ?_
  rw [dlmf_2_1_3 ((eventually_sub_ne_zero_approachIn X c).mono fun x hx => pow_ne_zero _ hx)]
  simp only [eval_trunc_eq_sum, coeff_mk]

/-- 2.1.16 in the form of 2.1.15: `(f(x) − ∑_{s<n} aₛ(x − c)ˢ)/(x − c)ⁿ → aₙ`. -/
theorem dlmf_2_1_16_iff_tendsto {X : Set 𝕜} {c : 𝕜} {f : 𝕜 → 𝕜} {a : ℕ → 𝕜} :
    IsAsympExpansionAtDLMF X c f a ↔ ∀ n : ℕ, Tendsto
      (fun x => (f x - ∑ s ∈ Finset.range n, a s * (x - c) ^ s) / (x - c) ^ n)
      (approachIn X c) (𝓝 (a n)) := by
  rw [isAsympExpansionAtDLMF_iff, hasPowExpansion_iff_tendsto (tendsto_sub_approachIn X c)
    (eventually_sub_ne_zero_approachIn X c)]
  simp only [eval_trunc_eq_sum, coeff_mk]

/-- **DLMF §2.1(iii)**: asymptotic expansions of the form 2.1.16 are unique (`c` a limit point
of `𝐗`). -/
theorem dlmf_2_1_iii_unique_at {X : Set 𝕜} {c : 𝕜} (hc : AccPt c (𝓟 X)) {f : 𝕜 → 𝕜}
    {a b : ℕ → 𝕜} (ha : IsAsympExpansionAtDLMF X c f a) (hb : IsAsympExpansionAtDLMF X c f b) :
    a = b := by
  have := (approachIn_neBot_iff X c).mpr hc
  have h := (isAsympExpansionAtDLMF_iff.mp ha).unique (tendsto_sub_approachIn X c)
    (eventually_sub_ne_zero_approachIn X c) (isAsympExpansionAtDLMF_iff.mp hb)
  funext n
  simpa using congrArg (coeff n) h

end Finite

/-! ### Algebraic operations -/

section Operations

variable {𝕜 : Type*} [NormedField 𝕜] {X : Set 𝕜} {f g : 𝕜 → 𝕜} {a b : ℕ → 𝕜}

/-- **DLMF §2.1(iii)**: addition of asymptotic expansions. -/
theorem dlmf_2_1_iii_add (hf : IsAsympExpansionDLMF X f a) (hg : IsAsympExpansionDLMF X g b) :
    IsAsympExpansionDLMF X (f + g) (a + b) := by
  rw [isAsympExpansionDLMF_iff] at *
  have : mk (a + b) = mk a + mk b := by ext; simp
  rw [this]; exact hf.add hg

/-- **DLMF §2.1(iii)**: subtraction of asymptotic expansions. -/
theorem dlmf_2_1_iii_sub (hf : IsAsympExpansionDLMF X f a) (hg : IsAsympExpansionDLMF X g b) :
    IsAsympExpansionDLMF X (f - g) (a - b) := by
  rw [isAsympExpansionDLMF_iff] at *
  have : mk (a - b) = mk a - mk b := by ext; simp
  rw [this]; exact hf.sub hg

/-- Constant multiples of asymptotic expansions. -/
theorem dlmf_2_1_iii_const_mul (c : 𝕜) (hf : IsAsympExpansionDLMF X f a) :
    IsAsympExpansionDLMF X (fun x => c * f x) fun n => c * a n := by
  rw [isAsympExpansionDLMF_iff] at *
  have : mk (fun n => c * a n) = C c * mk a := by ext; simp
  rw [this]; exact hf.const_mul c

/-- **DLMF §2.1(iii)**: multiplication of asymptotic expansions (Cauchy product). -/
theorem dlmf_2_1_iii_mul (hf : IsAsympExpansionDLMF X f a) (hg : IsAsympExpansionDLMF X g b) :
    IsAsympExpansionDLMF X (f * g)
      fun n => ∑ p ∈ Finset.antidiagonal n, a p.1 * b p.2 := by
  rw [isAsympExpansionDLMF_iff] at *
  have : mk (fun n => ∑ p ∈ Finset.antidiagonal n, a p.1 * b p.2) = mk a * mk b := by
    ext; simp [coeff_mul]
  rw [this]; exact hf.mul (tendsto_inv_atInf X) hg

/-- **DLMF §2.1(iii)**: division of asymptotic expansions (`b₀ ≠ 0`); the coefficients are
those of the quotient of the formal power series. -/
theorem dlmf_2_1_iii_div (hf : IsAsympExpansionDLMF X f a) (hg : IsAsympExpansionDLMF X g b)
    (hb : b 0 ≠ 0) : IsAsympExpansionDLMF X (f / g) fun n => coeff n (mk a * (mk b)⁻¹) := by
  rw [isAsympExpansionDLMF_iff] at *
  have : mk (fun n => coeff n (mk a * (mk b)⁻¹)) = mk a * (mk b)⁻¹ := by ext; simp
  rw [this]
  exact hf.div (tendsto_inv_atInf X) hg (by simpa using hb)

end Operations

/-! ### Convergent series -/

theorem eventually_summable_of_seriesConverges (a : ℕ → ℂ)
    (h : ∀ᶠ z in 𝓝 (0 : ℂ), ∃ S, SeriesConverges (fun s => a s * z ^ s) S) :
    ∀ᶠ z in 𝓝 (0 : ℂ), Summable fun s => a s * z ^ s := by
  obtain ⟨z₀, ⟨S, hS⟩, hz₀⟩ := ((h.filter_mono nhdsWithin_le_nhds).and
    (self_mem_nhdsWithin (s := {(0 : ℂ)}ᶜ))).exists
  obtain ⟨M, hM⟩ := hS.tendsto_zero.norm.bddAbove_range
  have hM' : ∀ s, ‖a s * z₀ ^ s‖ ≤ M := fun s => hM ⟨s, rfl⟩
  have hr : 0 < ‖z₀‖ := norm_pos_iff.mpr hz₀
  filter_upwards [Metric.ball_mem_nhds (0 : ℂ) (half_pos hr)] with z hz
  rw [Metric.mem_ball, dist_zero_right] at hz
  refine Summable.of_norm_bounded (g := fun s => M * (1 / 2) ^ s)
    (summable_geometric_two.mul_left M) fun s => ?_
  have hρ : ‖z‖ / ‖z₀‖ ≤ 1 / 2 := by rw [div_le_iff₀ hr]; linarith
  have e : ‖a s * z ^ s‖ = ‖a s * z₀ ^ s‖ * (‖z‖ / ‖z₀‖) ^ s := by
    simp only [norm_mul, norm_pow, div_pow]; field_simp
  rw [e]
  exact mul_le_mul (hM' s) (pow_le_pow_left₀ (by positivity) hρ s) (by positivity)
    ((norm_nonneg _).trans (hM' s))

/-- **DLMF §2.1(iii)**: if `∑ aₛx^{−s}` converges for all sufficiently large `|x|`, then it is the
asymptotic expansion of its sum as `x → ∞` in `ℂ`. -/
theorem dlmf_2_1_iii_convergent (a : ℕ → ℂ)
    (h : ∀ᶠ x in Bornology.cobounded ℂ, ∃ S, SeriesConverges (fun s => a s * x ^ (-(s : ℤ))) S) :
    IsAsympExpansionDLMF univ (fun x => ∑' s, a s * x ^ (-(s : ℤ))) a := by
  -- the series in `w = 1/x`
  have h0 : ∀ᶠ w in 𝓝 (0 : ℂ), ∃ S, SeriesConverges (fun s => a s * w ^ s) S := by
    have h1 : ∀ᶠ w in 𝓝[≠] (0 : ℂ), ∃ S, SeriesConverges (fun s => a s * w ^ s) S := by
      filter_upwards [tendsto_inv₀_nhdsNE_zero.eventually h] with w hw
      simpa [zpow_neg_natCast_eq] using hw
    rw [eventually_nhdsWithin_iff] at h1
    filter_upwards [h1] with w hw
    by_cases hw0 : w = 0
    · refine ⟨a 0, tendsto_const_nhds.congr fun n => ?_⟩
      simp [partialSum, hw0, Finset.sum_range_succ']
    · exact hw hw0
  have hsum := eventually_summable_of_seriesConverges a h0
  have hG : HasPowExpansion (𝓝[≠] (0 : ℂ)) id (fun w => ∑' s, a s * w ^ s) (mk a) := by
    intro n
    have h8 := dlmf_2_1_8 a h0 n
    rw [approachIn_univ, dlmf_2_1_3 (l := 𝓝[≠] (0 : ℂ)) (φ := fun z : ℂ => z ^ n)
      (eventually_mem_nhdsWithin.mono fun w (hw : w ≠ 0) => pow_ne_zero n hw)] at h8
    refine h8.congr' ?_ EventuallyEq.rfl
    filter_upwards [nhdsWithin_le_nhds hsum] with w hw
    rw [eval_trunc_eq_sum, ← hw.sum_add_tsum_nat_add n]
    simp
  have hc := hG.comp_tendsto (tendsto_inv₀_cobounded' (α := ℂ))
  rw [isAsympExpansionDLMF_iff, principal_univ, inf_top_eq]
  have e : (fun x : ℂ => x⁻¹) = id ∘ Inv.inv := rfl
  rw [e]
  convert hc using 1
  funext x
  show ∑' s, a s * x ^ (-(s : ℤ)) = ∑' s, a s * x⁻¹ ^ s
  simp only [zpow_neg_natCast_eq]

/-! ### Differentiation -/

theorem IsBigODLMF.congr' {α 𝕜 : Type*} [NormedField 𝕜] {l : Filter α} {u₁ u₂ φ₁ φ₂ : α → 𝕜}
    (h : IsBigODLMF l u₁ φ₁) (hu : u₁ =ᶠ[l] u₂) (hφ : φ₁ =ᶠ[l] φ₂) : IsBigODLMF l u₂ φ₂ := by
  obtain ⟨C, hC⟩ := h
  refine ⟨C, eventually_map.mpr ?_⟩
  filter_upwards [eventually_map.mp hC, hu, hφ] with x h1 h2 h3
  rwa [← h2, ← h3]

theorem cpow_neg_natCast_real (z : ℂ) (m : ℕ) : z ^ (((-(m : ℝ)) : ℝ) : ℂ) = z⁻¹ ^ m := by
  push_cast
  rw [Complex.cpow_neg, Complex.cpow_natCast, inv_pow]

theorem cpow_neg_natCast_real_sub_one (z : ℂ) (m : ℕ) :
    z ^ ((((-(m : ℝ)) : ℝ) : ℂ) - 1) = z ^ (-((m + 1 : ℕ) : ℤ)) := by
  rw [show (((-(m : ℝ)) : ℝ) : ℂ) - 1 = -(((m + 1 : ℕ) : ℂ)) by push_cast; ring,
    Complex.cpow_neg, Complex.cpow_natCast, zpow_neg, zpow_natCast]

theorem hasDerivAt_sum_inv_pow (a : ℕ → ℂ) (m : ℕ) {z : ℂ} (hz : z ≠ 0) :
    HasDerivAt (fun z => ∑ s ∈ Finset.range m, a s * z⁻¹ ^ s)
      (∑ s ∈ Finset.range m, -(s : ℂ) * a s * z⁻¹ ^ (s + 1)) z := by
  refine (HasDerivAt.fun_sum (A := fun s y => a s * y⁻¹ ^ s)
    fun s _ => ((hasDerivAt_inv hz).pow s).const_mul (a s)).congr_deriv ?_
  refine Finset.sum_congr rfl fun s _ => ?_
  rcases s with _ | s
  · simp
  · simp only [Nat.add_sub_cancel]
    push_cast
    ring

/-- **DLMF §2.1(iii)**, differentiation (with the conditions of §2.1(ii)): if `f` is analytic
for large `|z|` in a sector `𝐒` and `f(z) ∼ ∑ aₛz^{−s}` there, then `f′(z) ∼ ∑ bₛz^{−s}`,
`b₀ = 0`, `bₛ = −(s − 1)aₛ₋₁`, in any closed sector properly interior to `𝐒` (Ritt). -/
theorem dlmf_2_1_iii_deriv {θ ω θ' ω' : ℝ} (hω : ω ≤ Real.pi) (hsub : |θ' - θ| + ω' < ω)
    {f : ℂ → ℂ} (hf : ∃ R, DifferentiableOn ℂ f (sectorDLMF θ ω ∩ {z | R < ‖z‖}))
    {a : ℕ → ℂ} (ha : IsAsympExpansionDLMF (sectorDLMF θ ω) f a) :
    IsAsympExpansionDLMF (closedSectorDLMF θ' ω') (deriv f)
      fun s => if s = 0 then 0 else -((s : ℂ) - 1) * a (s - 1) := by
  obtain ⟨R, hR⟩ := hf
  have hA := isAsympExpansionDLMF_iff.mp ha
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  set P : ℂ → ℂ := fun z => ∑ s ∈ Finset.range m, a s * z⁻¹ ^ s
  have hPm : (fun z => f z - P z) =O[Bornology.cobounded ℂ ⊓ 𝓟 (sectorDLMF θ ω)]
      fun z => z⁻¹ ^ m := by
    simpa [P, eval_trunc_eq_sum] using hA m
  have hFO : IsBigODLMF (Bornology.cobounded ℂ ⊓ 𝓟 (sectorDLMF θ ω)) (fun z => f z - P z)
      fun z => z ^ (((-(m : ℝ)) : ℝ) : ℂ) := by
    rw [dlmf_2_1_3 ((eventually_ne_zero_atInf _).mono fun z hz => by
      rw [cpow_neg_natCast_real]; exact pow_ne_zero _ (inv_ne_zero hz))]
    simpa only [cpow_neg_natCast_real] using hPm
  have hPd : DifferentiableOn ℂ P {z | z ≠ 0} := fun z hz =>
    (hasDerivAt_sum_inv_pow a m hz).differentiableAt.differentiableWithinAt
  have hFd : DifferentiableOn ℂ (fun z => f z - P z)
      (sectorDLMF θ ω ∩ {z | max R 0 < ‖z‖}) :=
    (hR.mono fun z hz =>
      ⟨hz.1, lt_of_le_of_lt (le_max_left _ _) (show max R 0 < ‖z‖ from hz.2)⟩).sub
      (hPd.mono fun z hz => hz.1.1)
  have hRitt := dlmf_2_1_ii_ritt hω hsub ⟨_, hFd⟩ hFO
  refine hRitt.congr' ?_ (Eventually.of_forall fun z => cpow_neg_natCast_real_sub_one z m)
  -- `deriv (f − P) = f′ − ∑ bₛ z^{−s}` far out in the closed sector
  have hκ := ritt_κ_pos hsub
  rw [EventuallyEq, eventually_cobounded_inf_principal]
  refine ⟨2 * max R 0 + 1, fun z hz hzR => ?_⟩
  have hR0 : 0 ≤ max R 0 := le_max_right _ _
  have hnz : 0 < ‖z‖ := by linarith
  have hz0 : z ≠ 0 := hz.1
  have hball := closedBall_subset_sectorDLMF hω hsub hz
  have hnbhd : sectorDLMF θ ω ∩ {w | R < ‖w‖} ∈ 𝓝 z := by
    refine Filter.mem_of_superset (Metric.ball_mem_nhds z (mul_pos hκ hnz)) fun w hw => ?_
    have hw' := Metric.ball_subset_closedBall hw
    refine ⟨hball hw', ?_⟩
    rw [Metric.mem_ball, dist_eq_norm] at hw
    have h1 := norm_sub_norm_le z w
    rw [norm_sub_rev] at h1
    have hκ2 := ritt_κ_le (θ := θ) (ω := ω) (θ' := θ') (ω' := ω')
    show R < ‖w‖
    nlinarith [le_max_left R 0]
  have hfd := hR.differentiableAt hnbhd
  have hPh := hasDerivAt_sum_inv_pow a m hz0
  rw [deriv_fun_sub hfd hPh.differentiableAt, hPh.deriv]
  congr 1
  rw [Finset.sum_range_succ']
  simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte,
    Nat.add_sub_cancel, zero_mul, add_zero, zpow_neg_natCast_eq]
  refine Finset.sum_congr rfl fun s _ => ?_
  push_cast; ring

/-! ### Null expansions (2.1.17) -/

theorem isAsympExpansionDLMF_zero_of_tendsto {𝕜 : Type*} [NormedField 𝕜] {X : Set 𝕜}
    {f : 𝕜 → 𝕜} (h : ∀ n : ℕ, Tendsto (fun x => x ^ n * f x) (Bornology.cobounded 𝕜 ⊓ 𝓟 X) (𝓝 0)) :
    IsAsympExpansionDLMF X f 0 :=
  dlmf_2_1_15.mpr fun n => by simpa using h n

theorem re_ge_norm_mul_sin {δ : ℝ} (hδ : 0 ≤ δ) {z : ℂ}
    (hz : |Complex.arg z| ≤ Real.pi / 2 - δ) :
    ‖z‖ * Real.sin δ ≤ z.re := by
  rcases eq_or_ne z 0 with rfl | h0
  · simp
  have hc := Complex.cos_arg h0
  have hcos : Real.sin δ ≤ Real.cos (Complex.arg z) := by
    rw [← Real.cos_abs (Complex.arg z), ← Real.cos_pi_div_two_sub]
    exact Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) (by linarith [Real.pi_pos]) hz
  rw [hc, le_div_iff₀ (norm_pos_iff.mpr h0)] at hcos
  linarith

theorem tendsto_pow_mul_exp_neg_mul (n : ℕ) {c : ℝ} (hc : 0 < c) :
    Tendsto (fun t : ℝ => t ^ n * Real.exp (-(c * t))) atTop (𝓝 0) := by
  have h := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero n).comp
    (tendsto_id.const_mul_atTop hc)
  have h2 := h.const_mul (c ^ n)⁻¹
  rw [mul_zero] at h2
  refine h2.congr fun t => ?_
  simp only [Function.comp_apply, id, mul_pow]
  field_simp

theorem re_cpow_half_ge {z : ℂ} (hz : |Complex.arg z| ≤ Real.pi / 2) :
    √‖z‖ / 2 ≤ (z ^ (1 / 2 : ℂ)).re := by
  rcases eq_or_ne z 0 with rfl | h0
  · simp
  rw [Complex.cpow_def_of_ne_zero h0, Complex.exp_re]
  have hre : (Complex.log z * (1 / 2)).re = Real.log ‖z‖ / 2 := by
    simp [Complex.log_re]; ring
  have him : (Complex.log z * (1 / 2)).im = Complex.arg z / 2 := by
    simp [Complex.log_im]; ring
  rw [hre, him]
  have hsq : Real.exp (Real.log ‖z‖ / 2) = √‖z‖ := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos (norm_pos_iff.mpr h0)]; ring_nf
  rw [hsq]
  have hcos : 1 / 2 ≤ Real.cos (Complex.arg z / 2) := by
    rw [← Real.cos_abs, ← Real.cos_pi_div_three]
    refine Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) (by linarith [Real.pi_pos]) ?_
    rw [abs_div, abs_two]; linarith [Real.pi_pos]
  nlinarith [Real.sqrt_nonneg ‖z‖]

/-- **DLMF 2.1.17**: in `|ph z| ≤ ½π − δ` each of `0`, `e^{−z}` and `e^{−√z}` (principal value)
has the null asymptotic expansion `0 + 0·z^{−1} + 0·z^{−2} + ⋯` as `z → ∞`. -/
theorem dlmf_2_1_17 {δ : ℝ} (hδ : 0 < δ) (hδ' : δ ≤ Real.pi / 2) :
    IsAsympExpansionDLMF {z : ℂ | |Complex.arg z| ≤ Real.pi / 2 - δ} 0 0 ∧
      IsAsympExpansionDLMF {z : ℂ | |Complex.arg z| ≤ Real.pi / 2 - δ}
        (fun z => Complex.exp (-z)) 0 ∧
      IsAsympExpansionDLMF {z : ℂ | |Complex.arg z| ≤ Real.pi / 2 - δ}
        (fun z => Complex.exp (-z ^ (1 / 2 : ℂ))) 0 := by
  set X := {z : ℂ | |Complex.arg z| ≤ Real.pi / 2 - δ}
  have hnorm : Tendsto (fun z : ℂ => ‖z‖) (Bornology.cobounded ℂ ⊓ 𝓟 X) atTop :=
    tendsto_norm_cobounded_atTop.mono_left inf_le_left
  have hsin : 0 < Real.sin δ := Real.sin_pos_of_pos_of_lt_pi hδ (by linarith [Real.pi_pos])
  refine ⟨isAsympExpansionDLMF_zero_of_tendsto fun n => by simpa using tendsto_const_nhds, ?_, ?_⟩
  · refine isAsympExpansionDLMF_zero_of_tendsto fun n => ?_
    refine squeeze_zero_norm' ?_ ((tendsto_pow_mul_exp_neg_mul n hsin).comp hnorm)
    filter_upwards [mem_inf_of_right (mem_principal_self X)] with z hz
    rw [norm_mul, norm_pow, Complex.norm_exp, Function.comp_apply, Complex.neg_re]
    gcongr
    linarith [re_ge_norm_mul_sin hδ.le hz]
  · refine isAsympExpansionDLMF_zero_of_tendsto fun n => ?_
    have hsq := (tendsto_pow_mul_exp_neg_mul (2 * n) (c := 1 / 2) (by norm_num)).comp
      (Real.tendsto_sqrt_atTop.comp hnorm)
    refine squeeze_zero_norm' ?_ hsq
    filter_upwards [mem_inf_of_right (mem_principal_self X)] with z hz
    rw [norm_mul, norm_pow, Complex.norm_exp, Function.comp_apply, Function.comp_apply,
      Complex.neg_re, pow_mul, Real.sq_sqrt (norm_nonneg _)]
    gcongr
    have := re_cpow_half_ge (z := z) (by linarith [show |Complex.arg z| ≤ _ from hz])
    linarith

/-! ### Differentiation needs extra conditions -/

/-- **DLMF §2.1(iii)**: differentiation of asymptotic expansions requires extra conditions.
On `(0, ∞)`, `f(x) = e^{−x} sin(eˣ)` has the null expansion, but `f′(x) = −e^{−x} sin(eˣ) + cos(eˣ)`
has no asymptotic expansion at all (it does not converge as `x → +∞`). -/
theorem dlmf_2_1_iii_deriv_counterexample :
    IsAsympExpansionDLMF (Ioi (0 : ℝ)) (fun x => Real.exp (-x) * Real.sin (Real.exp x)) 0 ∧
      ¬ ∃ b, IsAsympExpansionDLMF (Ioi (0 : ℝ))
        (deriv fun x => Real.exp (-x) * Real.sin (Real.exp x)) b := by
  set L := Bornology.cobounded ℝ ⊓ 𝓟 (Ioi (0 : ℝ))
  have hL : Tendsto (fun x : ℝ => x) L atTop := by
    have h := tendsto_norm_cobounded_atTop.mono_left (inf_le_left : L ≤ _)
    refine h.congr' ?_
    filter_upwards [mem_inf_of_right (mem_principal_self (Ioi (0 : ℝ)))] with x hx
    exact Real.norm_of_nonneg (le_of_lt hx)
  refine ⟨isAsympExpansionDLMF_zero_of_tendsto fun n => ?_, ?_⟩
  · have h := (tendsto_pow_mul_exp_neg_mul n one_pos).comp hL
    refine squeeze_zero_norm' ?_ h
    filter_upwards [mem_inf_of_right (mem_principal_self (Ioi (0 : ℝ)))] with x hx
    have hx0 : (0 : ℝ) < x := hx
    rw [norm_mul, norm_mul, norm_pow, Real.norm_of_nonneg hx0.le, Function.comp_apply, one_mul,
      Real.norm_of_nonneg (Real.exp_pos _).le]
    have := Real.abs_sin_le_one (Real.exp x)
    rw [← Real.norm_eq_abs] at this
    have := Real.exp_pos (-x)
    gcongr
    calc Real.exp (-x) * ‖Real.sin (Real.exp x)‖ ≤ Real.exp (-x) * 1 := by gcongr
      _ = Real.exp (-x) := mul_one _
  · rintro ⟨b, hb⟩
    have h0 := (dlmf_2_1_15.mp hb) 0
    simp only [pow_zero, one_mul, Finset.range_zero, Finset.sum_empty, sub_zero] at h0
    have hd : ∀ x, deriv (fun x => Real.exp (-x) * Real.sin (Real.exp x)) x =
        -(Real.exp (-x) * Real.sin (Real.exp x)) + Real.cos (Real.exp x) := fun x => by
      have := ((Real.hasDerivAt_exp (-x)).comp x (hasDerivAt_neg x)).mul
        ((Real.hasDerivAt_sin (Real.exp x)).comp x (Real.hasDerivAt_exp x))
      have h' : HasDerivAt (fun x => Real.exp (-x) * Real.sin (Real.exp x)) _ x := this
      rw [h'.deriv]
      have : Real.exp (-x) * Real.exp x = 1 := by rw [← Real.exp_add]; simp
      simp only [Function.comp_apply, mul_neg, mul_one]
      linear_combination Real.cos (Real.exp x) * this
    -- two sequences to `+∞` with `f′ = 1` and `f′ = −1`
    have hseq : ∀ c : ℝ, 0 < c → Tendsto (fun k : ℕ => Real.log (c + 2 * Real.pi * k)) atTop L := by
      intro c hc
      have ht : Tendsto (fun k : ℕ => c + 2 * Real.pi * k) atTop atTop :=
        tendsto_atTop_add_const_left _ c
          ((tendsto_natCast_atTop_atTop).const_mul_atTop (by positivity))
      have hlog := Real.tendsto_log_atTop.comp ht
      refine tendsto_inf.mpr ⟨tendsto_norm_atTop_iff_cobounded.mp ?_, tendsto_principal.mpr ?_⟩
      · exact tendsto_atTop_mono (fun k => le_abs_self _) hlog
      · filter_upwards [hlog.eventually_gt_atTop 0] with k hk using hk
    have hval : ∀ c : ℝ, 0 < c → ∀ k : ℕ,
        deriv (fun x => Real.exp (-x) * Real.sin (Real.exp x)) (Real.log (c + 2 * Real.pi * k)) =
          -(Real.exp (-Real.log (c + 2 * Real.pi * k)) * Real.sin c) + Real.cos c := by
      intro c hc k
      have hpos : 0 < c + 2 * Real.pi * k := by positivity
      rw [hd, Real.exp_log hpos, show c + 2 * Real.pi * k = c + k * (2 * Real.pi) by ring,
        Real.sin_add_nat_mul_two_pi, Real.cos_add_nat_mul_two_pi]
    have h1 := h0.comp (hseq (2 * Real.pi) (by positivity))
    have h2 := h0.comp (hseq Real.pi Real.pi_pos)
    have e1 : (fun k : ℕ => deriv (fun x => Real.exp (-x) * Real.sin (Real.exp x))
        (Real.log (2 * Real.pi + 2 * Real.pi * k))) = fun _ => 1 := by
      funext k; rw [hval _ (by positivity), Real.sin_two_pi, Real.cos_two_pi]; simp
    have e2 : (fun k : ℕ => deriv (fun x => Real.exp (-x) * Real.sin (Real.exp x))
        (Real.log (Real.pi + 2 * Real.pi * k))) = fun _ => -1 := by
      funext k; rw [hval _ Real.pi_pos, Real.sin_pi, Real.cos_pi]; simp
    simp only [Function.comp_def] at h1 h2
    rw [e1] at h1
    rw [e2] at h2
    have := tendsto_nhds_unique (tendsto_const_nhds.congr fun _ => rfl) h1
    have := tendsto_nhds_unique (tendsto_const_nhds.congr fun _ => rfl) h2
    linarith

end Azurite.DLMF
