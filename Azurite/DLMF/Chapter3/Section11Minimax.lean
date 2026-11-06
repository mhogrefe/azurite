/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.ContinuousMap.Polynomial
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.RingTheory.Polynomial.Basic

/-!
# DLMF §3.11(i): Minimax polynomial approximations

For `f` continuous on `[a, b]` (`f : C([a, b], ℝ)`) and `n ∈ ℕ`:

* `minimaxErr f p = max_{a≤x≤b} |εₙ(x)|`, `εₙ = f − pₙ` (the sup norm), and `IsMinimax f n p`.
* "There exists a unique `n`th degree polynomial `pₙ(x)` … that minimizes
  `max |εₙ(x)|`" (`dlmf_3_11_i_exists_unique`): existence by compactness in the finite-dimensional
  space of polynomials of degree `≤ n` (`minimax_exists`); uniqueness from the fact that the
  extremal set `{x : |εₙ(x)| = max |εₙ|}` of a best approximation has at least `n + 1` points
  (`minimax_extremal_card`; otherwise an interpolating perturbation improves it), applied to the
  average of two best approximations (`minimax_unique`).
* "A sufficient condition … is that `|εₙ(x)|` attains its maximum at `n + 2` distinct points …
  and `εₙ(x)` changes sign at these consecutive maxima" (`dlmf_3_11_i_sufficient`).
* 3.11.1–3.11.5 (`remezSystem`, `dlmf_3_11_5`): the `n + 2` equations
  `∑ x_j^k δa_k = (−1)^j (m_j − m)` for the `n + 2` unknowns `δa₀, …, δaₙ, m` have a unique
  solution for nodes `x₀ < ⋯ < x_{n+1}`; at an equioscillating `pₙ` (`m_j = m`) the correction
  vanishes (`remez_fixed`).
* The key fact: a polynomial of degree `≤ n` cannot strictly alternate in sign at `n + 2`
  points (`not_alternates`).
-/

open Polynomial Finset Set

namespace Azurite.DLMF

/-! ### Sign alternation -/

/-- A polynomial of degree `≤ n` that strictly alternates in sign at `n + 2` increasing points
vanishes identically — so it cannot alternate. -/
theorem not_alternates {n : ℕ} {P : ℝ[X]} (hP : P.natDegree ≤ n) {x : Fin (n + 2) → ℝ}
    (hx : StrictMono x)
    (halt : ∀ j : Fin (n + 1), P.eval (x j.castSucc) * P.eval (x j.succ) < 0) : False := by
  -- a root in each `(x_j, x_{j+1})`
  have hroot : ∀ j : Fin (n + 1), ∃ y ∈ Ioo (x j.castSucc) (x j.succ), P.eval y = 0 := by
    intro j
    have hlt : x j.castSucc < x j.succ := hx Fin.castSucc_lt_succ
    have hc : ContinuousOn (fun t => P.eval t) (Icc (x j.castSucc) (x j.succ)) :=
      P.continuous.continuousOn
    have h := halt j
    rcases lt_or_gt_of_ne (show P.eval (x j.castSucc) ≠ 0 by
      intro h0; rw [h0, zero_mul] at h; exact lt_irrefl 0 h) with h1 | h1
    · have h2 : 0 < P.eval (x j.succ) := by nlinarith
      obtain ⟨y, hy, hy0⟩ := intermediate_value_Ioo hlt.le hc ⟨h1, h2⟩
      exact ⟨y, hy, hy0⟩
    · have h2 : P.eval (x j.succ) < 0 := by nlinarith
      obtain ⟨y, hy, hy0⟩ := intermediate_value_Ioo' hlt.le hc ⟨h2, h1⟩
      exact ⟨y, hy, hy0⟩
  choose y hy hy0 using hroot
  have hinj : Function.Injective y := by
    intro i j hij
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · have : y i < y j := by
        have h1 := (hy i).2
        have h2 := (hy j).1
        have : x i.succ ≤ x j.castSucc := hx.monotone (by
          rw [Fin.le_def]; simp; exact h)
        linarith
      exact absurd hij this.ne
    · have : y j < y i := by
        have h1 := (hy j).2
        have h2 := (hy i).1
        have : x j.succ ≤ x i.castSucc := hx.monotone (by
          rw [Fin.le_def]; simp; exact h)
        linarith
      exact absurd hij this.ne'
  have hP0 : P = 0 := eq_zero_of_natDegree_lt_card_of_eval_eq_zero P hinj hy0
    (by simp; omega)
  have := halt 0
  rw [hP0] at this
  simp at this

/-! ### Errors and best approximations -/

variable {a b : ℝ}

/-- The polynomial `p` as a continuous function on `[a, b]`. -/
noncomputable def polyOn (a b : ℝ) (p : ℝ[X]) : C(Icc a b, ℝ) := p.toContinuousMapOn (Icc a b)

@[simp] theorem polyOn_apply (p : ℝ[X]) (x : Icc a b) : polyOn a b p x = p.eval (x : ℝ) := by
  simp [polyOn]

/-- `max_{a ≤ x ≤ b} |εₙ(x)|`, `εₙ = f − pₙ`. -/
noncomputable def minimaxErr (f : C(Icc a b, ℝ)) (p : ℝ[X]) : ℝ := ‖f - polyOn a b p‖

/-- **DLMF §3.11(i)**: `p` (of degree `≤ n`) is a minimax (best uniform) polynomial approximation
to `f` on `[a, b]`. -/
def IsMinimax (f : C(Icc a b, ℝ)) (n : ℕ) (p : ℝ[X]) : Prop :=
  p.natDegree ≤ n ∧ ∀ q : ℝ[X], q.natDegree ≤ n → minimaxErr f p ≤ minimaxErr f q

theorem abs_err_le (f : C(Icc a b, ℝ)) (p : ℝ[X]) (x : Icc a b) :
    |f x - p.eval (x : ℝ)| ≤ minimaxErr f p := by
  have := (f - polyOn a b p).norm_coe_le_norm x
  simpa [minimaxErr, Real.norm_eq_abs] using this

/-- **DLMF §3.11(i)**: "A sufficient condition for `pₙ(x)` to be the minimax polynomial is that
`|εₙ(x)|` attains its maximum at `n + 2` distinct points in `[a, b]` and `εₙ(x)` changes sign at
these consecutive maxima." -/
theorem dlmf_3_11_i_sufficient (f : C(Icc a b, ℝ)) {n : ℕ} {p : ℝ[X]} (hp : p.natDegree ≤ n)
    {x : Fin (n + 2) → Icc a b} (hx : StrictMono fun j => (x j : ℝ))
    (hmax : ∀ j, |f (x j) - p.eval (x j : ℝ)| = minimaxErr f p)
    (hsign : ∀ j : Fin (n + 1), f (x j.succ) - p.eval (x j.succ : ℝ) =
      -(f (x j.castSucc) - p.eval (x j.castSucc : ℝ))) :
    IsMinimax f n p := by
  refine ⟨hp, fun q hq => ?_⟩
  by_contra hlt
  push Not at hlt
  set E := minimaxErr f p
  have hq' : ∀ y : Icc a b, |f y - q.eval (y : ℝ)| < E := fun y =>
    lt_of_le_of_lt (abs_err_le f q y) hlt
  -- `d = q − p` alternates in sign at the `x_j`
  refine not_alternates (P := q - p) ?_ hx fun j => ?_
  · exact (natDegree_sub_le _ _).trans (max_le hq hp)
  · simp only [eval_sub]
    set u := f (x j.castSucc) - p.eval (x j.castSucc : ℝ)
    have hu : |u| = E := hmax _
    have hv := hsign j
    have h1 := hq' (x j.castSucc)
    have h2 := hq' (x j.succ)
    have e1 : q.eval (x j.castSucc : ℝ) - p.eval (x j.castSucc : ℝ) =
        u - (f (x j.castSucc) - q.eval (x j.castSucc : ℝ)) := by simp only [u]; ring
    have e2 : q.eval (x j.succ : ℝ) - p.eval (x j.succ : ℝ) =
        -u - (f (x j.succ) - q.eval (x j.succ : ℝ)) := by rw [← hv]; ring
    rw [e1, e2]
    rcases abs_lt.mp h1 with ⟨h1a, h1b⟩
    rcases abs_lt.mp h2 with ⟨h2a, h2b⟩
    have hE0 : 0 ≤ E := hu ▸ abs_nonneg u
    rcases (abs_eq hE0).mp hu with hu' | hu' <;> rw [hu'] <;> nlinarith

/-! ### The Remez system 3.11.5 -/

/-- The linear map `(δa, m) ↦ (∑_k x_j^k δa_k + (−1)^j m)_j` of 3.11.5. -/
noncomputable def remezSystem {n : ℕ} (x : Fin (n + 2) → ℝ) :
    ((Fin (n + 1) → ℝ) × ℝ) →ₗ[ℝ] (Fin (n + 2) → ℝ) where
  toFun v j := ∑ k : Fin (n + 1), x j ^ (k : ℕ) * v.1 k + (-1) ^ (j : ℕ) * v.2
  map_add' v w := by funext j; simp [mul_add, Finset.sum_add_distrib]; ring
  map_smul' c v := by
    funext j
    simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul, RingHom.id_apply,
      Finset.mul_sum, mul_add]
    congr 1
    · exact Finset.sum_congr rfl fun k _ => by ring
    · ring

theorem remezSystem_injective {n : ℕ} {x : Fin (n + 2) → ℝ} (hx : StrictMono x) :
    Function.Injective (remezSystem x) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  rintro ⟨δ, m⟩ hv
  set P : ℝ[X] := ∑ k : Fin (n + 1), C (δ k) * X ^ (k : ℕ)
  have hPdeg : P.natDegree ≤ n := by
    refine natDegree_sum_le_of_forall_le _ _ fun k _ => ?_
    refine (natDegree_C_mul_le _ _).trans ?_
    rw [natDegree_X_pow]; exact Nat.lt_succ_iff.mp k.isLt
  have hPx : ∀ j, P.eval (x j) = -((-1) ^ (j : ℕ) * m) := fun j => by
    have := congrFun hv j
    simp only [remezSystem, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply] at this
    simp only [P, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X]
    rw [show ∑ i : Fin (n + 1), δ i * x j ^ (i : ℕ) = ∑ i : Fin (n + 1), x j ^ (i : ℕ) * δ i from
      Finset.sum_congr rfl fun i _ => mul_comm _ _]
    linear_combination this
  have hm : m = 0 := by
    by_contra hm
    refine not_alternates hPdeg hx fun j => ?_
    rw [hPx, hPx]
    simp only [Fin.val_castSucc, Fin.val_succ, pow_succ]
    nlinarith [sq_pos_of_ne_zero hm, pow_two_nonneg ((-1 : ℝ) ^ (j : ℕ)),
      show ((-1 : ℝ) ^ (j : ℕ)) ^ 2 = 1 by rw [← pow_mul, mul_comm, pow_mul]; norm_num]
  have hP0 : P = 0 := eq_zero_of_natDegree_lt_card_of_eval_eq_zero P hx.injective
    (fun j => by rw [hPx, hm]; ring) (by simp; omega)
  have hδ : δ = 0 := by
    funext k
    have := congrArg (fun Q => Q.coeff k) hP0
    simp only [P, finsetSum_coeff, coeff_C_mul, coeff_X_pow, coeff_zero] at this
    rw [Finset.sum_eq_single k (fun i _ hi => by
      rw [ite_eq_right (fun h => hi (Fin.ext h.symm)), mul_zero]) (by simp)] at this
    simpa using this
  simp [hδ, hm]

/-- **DLMF 3.11.5**: for nodes `x₀ < x₁ < ⋯ < x_{n+1}` and any `m₀, …, m_{n+1}`, the system
`∑_{k=0}^{n} x_j^k δa_k = (−1)^j (m_j − m)`, `j = 0, …, n + 1`, has a unique solution
`(δa₀, …, δaₙ, m)`. -/
theorem dlmf_3_11_5 {n : ℕ} {x : Fin (n + 2) → ℝ} (hx : StrictMono x) (mj : Fin (n + 2) → ℝ) :
    ∃! v : (Fin (n + 1) → ℝ) × ℝ, ∀ j : Fin (n + 2),
      ∑ k : Fin (n + 1), x j ^ (k : ℕ) * v.1 k = (-1) ^ (j : ℕ) * (mj j - v.2) := by
  have hinj := remezSystem_injective hx
  have hsurj : Function.Surjective (remezSystem x) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by simp)).mp hinj
  have hiff : ∀ v : (Fin (n + 1) → ℝ) × ℝ, (∀ j : Fin (n + 2),
      ∑ k : Fin (n + 1), x j ^ (k : ℕ) * v.1 k = (-1) ^ (j : ℕ) * (mj j - v.2)) ↔
      remezSystem x v = fun j : Fin (n + 2) => (-1) ^ (j : ℕ) * mj j := by
    intro v
    simp only [remezSystem, LinearMap.coe_mk, AddHom.coe_mk, funext_iff]
    exact forall_congr' fun j => ⟨fun h => by rw [h]; ring, fun h => by linear_combination h⟩
  obtain ⟨v, hv⟩ := hsurj fun j : Fin (n + 2) => (-1) ^ (j : ℕ) * mj j
  refine ⟨v, (hiff v).mpr hv, fun w hw => hinj ?_⟩
  rw [(hiff w).mp hw, hv]

/-- At an equioscillating approximation (`m_j = m` for all `j`), the correction of 3.11.4 is
zero: the unique solution of 3.11.5 is `δa = 0` with the common value `m`. -/
theorem remez_fixed {n : ℕ} {x : Fin (n + 2) → ℝ} (hx : StrictMono x) (m : ℝ)
    (v : (Fin (n + 1) → ℝ) × ℝ)
    (hv : ∀ j : Fin (n + 2), ∑ k : Fin (n + 1), x j ^ (k : ℕ) * v.1 k =
      (-1) ^ (j : ℕ) * (m - v.2)) :
    v = (0, m) := by
  obtain ⟨w, -, huniq⟩ := dlmf_3_11_5 hx fun _ => m
  exact (huniq v hv).trans (huniq (0, m) (fun j => by simp)).symm

/-! ### Existence -/

theorem natDegree_le_of_mem_degreeLT {p : ℝ[X]} {n : ℕ} (h : p ∈ degreeLT ℝ (n + 1)) :
    p.natDegree ≤ n := by
  rw [degreeLT_succ_eq_degreeLE, mem_degreeLE] at h
  exact natDegree_le_iff_degree_le.mpr h

theorem mem_degreeLT_of_natDegree_le {p : ℝ[X]} {n : ℕ} (h : p.natDegree ≤ n) :
    p ∈ degreeLT ℝ (n + 1) := by
  rw [degreeLT_succ_eq_degreeLE, mem_degreeLE]
  exact natDegree_le_iff_degree_le.mp h

/-- **DLMF §3.11(i)**: a minimax polynomial approximation of degree `≤ n` exists. -/
theorem minimax_exists (f : C(Icc a b, ℝ)) (n : ℕ) : ∃ p, IsMinimax f n p := by
  set L : ℝ[X] →ₗ[ℝ] C(Icc a b, ℝ) := (toContinuousMapOnAlgHom (Icc a b)).toLinearMap
  set S := (degreeLT ℝ (n + 1)).map L
  have : FiniteDimensional ℝ (degreeLT ℝ (n + 1)) :=
    LinearEquiv.finiteDimensional (degreeLTEquiv ℝ (n + 1)).symm
  have : FiniteDimensional ℝ S := Module.Finite.map _ L
  have : ProperSpace S := FiniteDimensional.proper_real S
  set g : S → ℝ := fun s => ‖f - (s : C(Icc a b, ℝ))‖
  have hg : Continuous g := (continuous_const.sub continuous_subtype_val).norm
  obtain ⟨s0, -, hmin⟩ := (isCompact_closedBall (0 : S) (2 * ‖f‖)).exists_isMinOn
    ⟨0, Metric.mem_closedBall_self (by positivity)⟩ hg.continuousOn
  have hglob : ∀ s : S, g s0 ≤ g s := by
    intro s
    by_cases hs : ‖s‖ ≤ 2 * ‖f‖
    · exact hmin (by rwa [Metric.mem_closedBall, dist_zero_right])
    · push Not at hs
      have h0 : g s0 ≤ g 0 := hmin (Metric.mem_closedBall_self (by positivity))
      have hg0 : g 0 = ‖f‖ := by simp [g]
      have : ‖f‖ < g s := by
        have := norm_sub_norm_le (s : C(Icc a b, ℝ)) f
        rw [norm_sub_rev] at this
        have hns : ‖(s : C(Icc a b, ℝ))‖ = ‖s‖ := rfl
        simp only [g]; linarith
      linarith
  obtain ⟨p, hp, hps⟩ := Submodule.mem_map.mp s0.2
  refine ⟨p, natDegree_le_of_mem_degreeLT hp, fun q hq => ?_⟩
  have hqS : L q ∈ S := Submodule.mem_map.mpr ⟨q, mem_degreeLT_of_natDegree_le hq, rfl⟩
  have := hglob ⟨L q, hqS⟩
  simp only [g, ← hps] at this
  exact this

/-! ### Uniqueness -/

/-- The extremal set of a best approximation with positive error has at least `n + 1` points:
otherwise adding a small multiple of the polynomial interpolating `εₙ` on it improves `pₙ`. -/
theorem minimax_extremal {f : C(Icc a b, ℝ)} {n : ℕ} {p : ℝ[X]} (hab : a ≤ b)
    (hp : IsMinimax f n p) (hE : 0 < minimaxErr f p) :
    ∃ T : Finset (Icc a b), T.card = n + 1 ∧
      ∀ x ∈ T, |f x - p.eval (x : ℝ)| = minimaxErr f p := by
  classical
  set E := minimaxErr f p
  set ε : Icc a b → ℝ := fun x => f x - p.eval (x : ℝ)
  have hε : Continuous ε := (f - polyOn a b p).continuous.congr fun x => by simp [ε]
  have hεle : ∀ x, |ε x| ≤ E := abs_err_le f p
  by_contra hcon
  push Not at hcon
  set Z := {x : Icc a b | |ε x| = E}
  have hZfin : Z.Finite := by
    by_contra hinf
    obtain ⟨T, hTZ, hTc⟩ := Set.Infinite.exists_subset_card_eq hinf (n + 1)
    obtain ⟨x, hx, hne⟩ := hcon T hTc
    exact hne (hTZ hx)
  set Zs := hZfin.toFinset
  have hZcard : Zs.card ≤ n := by
    by_contra h
    push Not at h
    obtain ⟨T, hT, hTc⟩ := Finset.exists_subset_card_eq (show n + 1 ≤ Zs.card by omega)
    obtain ⟨x, hx, hne⟩ := hcon T hTc
    exact hne ((Set.Finite.mem_toFinset hZfin).mp (hT hx))
  -- the interpolating polynomial
  have hinj : Set.InjOn (fun x : Icc a b => (x : ℝ)) Zs := fun x _ y _ h => Subtype.ext h
  set q := Lagrange.interpolate Zs (fun x : Icc a b => (x : ℝ)) ε
  have hqdeg : q.natDegree ≤ n := by
    refine natDegree_le_of_mem_degreeLT (mem_degreeLT.mpr ?_)
    refine lt_of_lt_of_le (Lagrange.degree_interpolate_lt _ hinj) ?_
    exact_mod_cast (show Zs.card ≤ n + 1 by omega)
  have hqZ : ∀ x ∈ Z, q.eval (x : ℝ) = ε x := fun x hx =>
    Lagrange.eval_interpolate_at_node _ hinj ((Set.Finite.mem_toFinset hZfin).mpr hx)
  set h : Icc a b → ℝ := fun x => ε x - q.eval (x : ℝ)
  have hh : Continuous h := hε.sub ((q.continuous).comp continuous_subtype_val)
  -- the bound away from the extremal set
  set K := {x : Icc a b | E ≤ |h x|}
  have hKc : IsCompact K := (isClosed_le continuous_const hh.abs).isCompact
  obtain ⟨E', hE'0, hE'E, hE'⟩ : ∃ E', 0 ≤ E' ∧ E' < E ∧ ∀ x ∈ K, |ε x| ≤ E' := by
    rcases K.eq_empty_or_nonempty with hK | hK
    · exact ⟨0, le_rfl, hE, fun x hx => by rw [hK] at hx; exact hx.elim⟩
    · obtain ⟨x1, hx1, hmax⟩ := hKc.exists_isMaxOn hK hε.abs.continuousOn
      refine ⟨|ε x1|, abs_nonneg _, lt_of_le_of_ne (hεle x1) fun heq => ?_, fun x hx => hmax hx⟩
      have h0 : h x1 = 0 := by simp only [h]; rw [hqZ x1 heq]; ring
      have hk : E ≤ |h x1| := hx1
      rw [h0, abs_zero] at hk
      linarith
  set M := ‖polyOn a b q‖
  have hM : 0 ≤ M := norm_nonneg _
  set lam := min (1 / 2) ((E - E') / (2 * (M + 1)))
  have hlam0 : 0 < lam := lt_min (by norm_num) (by apply div_pos <;> linarith)
  have hlam1 : lam ≤ 1 / 2 := min_le_left _ _
  have hlam2 : lam ≤ (E - E') / (2 * (M + 1)) := min_le_right _ _
  have hqM : ∀ x : Icc a b, |q.eval (x : ℝ)| ≤ M := fun x => by
    have := (polyOn a b q).norm_coe_le_norm x
    simpa [Real.norm_eq_abs] using this
  have hne : Nonempty (Icc a b) := ⟨⟨a, left_mem_Icc.mpr hab⟩⟩
  have hbetter : minimaxErr f (p + C lam * q) < E := by
    rw [minimaxErr, ContinuousMap.norm_lt_iff_of_nonempty]
    intro x
    simp only [ContinuousMap.sub_apply, polyOn_apply, eval_add, eval_mul, eval_C,
      Real.norm_eq_abs]
    rw [show f x - (p.eval (x : ℝ) + lam * q.eval (x : ℝ)) = ε x - lam * q.eval (x : ℝ) by
      simp only [ε]; ring]
    by_cases hxK : x ∈ K
    · have h1 := hE' x hxK
      have h2 := hqM x
      have h3 : lam * M ≤ (E - E') / 2 := by
        calc lam * M ≤ (E - E') / (2 * (M + 1)) * M := by gcongr
          _ ≤ (E - E') / 2 := by
            rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
            nlinarith
      calc |ε x - lam * q.eval (x : ℝ)| ≤ |ε x| + lam * |q.eval (x : ℝ)| := by
            refine (abs_sub _ _).trans (le_of_eq ?_)
            rw [abs_mul, abs_of_pos hlam0]
        _ ≤ E' + lam * M := by gcongr
        _ < E := by linarith
    · simp only [K, Set.mem_ofPred_eq, not_le] at hxK
      have e : ε x - lam * q.eval (x : ℝ) = (1 - lam) * ε x + lam * h x := by
        simp only [h]; ring
      rw [e]
      calc |(1 - lam) * ε x + lam * h x| ≤ (1 - lam) * |ε x| + lam * |h x| := by
            refine (abs_add_le _ _).trans ?_
            rw [abs_mul, abs_mul, abs_of_pos (by linarith : (0 : ℝ) < 1 - lam),
              abs_of_pos hlam0]
        _ < (1 - lam) * E + lam * E := by
            have := hεle x
            have : (1 - lam) * |ε x| ≤ (1 - lam) * E := by gcongr; linarith
            nlinarith
        _ = E := by ring
  have hdeg : (p + C lam * q).natDegree ≤ n :=
    (natDegree_add_le _ _).trans (max_le hp.1 ((natDegree_C_mul_le _ _).trans hqdeg))
  exact absurd (hp.2 _ hdeg) (not_le.mpr hbetter)

theorem avg_eq {u v E : ℝ} (hu : |u| ≤ E) (hv : |v| ≤ E) (h : |(u + v) / 2| = E) : u = v := by
  rcases abs_le.mp hu with ⟨hu1, hu2⟩
  rcases abs_le.mp hv with ⟨hv1, hv2⟩
  rcases (abs_eq (le_trans (abs_nonneg _) hu)).mp h with h | h <;> linarith

/-- **DLMF §3.11(i)**: the minimax polynomial is unique. -/
theorem minimax_unique {f : C(Icc a b, ℝ)} {n : ℕ} {p q : ℝ[X]} (hab : a < b)
    (hp : IsMinimax f n p) (hq : IsMinimax f n q) : p = q := by
  have hE : minimaxErr f p = minimaxErr f q := le_antisymm (hp.2 q hq.1) (hq.2 p hp.1)
  set E := minimaxErr f p
  set r := C (1 / 2 : ℝ) * (p + q)
  have hrdeg : r.natDegree ≤ n :=
    (natDegree_C_mul_le _ _).trans ((natDegree_add_le _ _).trans (max_le hp.1 hq.1))
  have hE0 : 0 ≤ E := norm_nonneg _
  have hrle : minimaxErr f r ≤ E := by
    rw [minimaxErr, ContinuousMap.norm_le _ hE0]
    intro x
    have h1 := abs_err_le f p x
    have h2 := abs_err_le f q x
    rw [← hE] at h2
    simp only [ContinuousMap.sub_apply, polyOn_apply, Real.norm_eq_abs, r, eval_mul, eval_C,
      eval_add]
    rw [show f x - 1 / 2 * (p.eval (x : ℝ) + q.eval (x : ℝ)) =
      ((f x - p.eval (x : ℝ)) + (f x - q.eval (x : ℝ))) / 2 by ring]
    rw [abs_div, abs_two]
    have := abs_add_le (f x - p.eval (x : ℝ)) (f x - q.eval (x : ℝ))
    linarith
  have hr : IsMinimax f n r := ⟨hrdeg, fun s hs => le_trans hrle (hp.2 s hs)⟩
  have hrE : minimaxErr f r = E := le_antisymm hrle (hp.2 r hrdeg)
  -- `n + 1` points where `p = q`
  obtain ⟨T, hTc, hT⟩ : ∃ T : Finset ℝ, T.card = n + 1 ∧ ∀ x ∈ T, p.eval x = q.eval x := by
    rcases hE0.lt_or_eq with hpos | hzero
    · obtain ⟨T, hTc, hTE⟩ := minimax_extremal hab.le hr (by rw [hrE]; exact hpos)
      refine ⟨T.map ⟨Subtype.val, Subtype.val_injective⟩, by simp [hTc], fun x hx => ?_⟩
      obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hx
      have h := hTE y hy
      simp only [r, eval_mul, eval_C, eval_add, hrE] at h
      have h' : |((f y - p.eval (y : ℝ)) + (f y - q.eval (y : ℝ))) / 2| = E := by
        rw [← h]; congr 1; ring
      have := avg_eq (abs_err_le f p y) ((abs_err_le f q y).trans (le_of_eq hE.symm)) h'
      simp only [Function.Embedding.coeFn_mk]
      linarith
    · -- `E = 0`: `p = f = q` on `[a, b]`
      set t : ℕ → ℝ := fun i => a + (b - a) * i / (n + 1)
      have ht : ∀ i ≤ n, t i ∈ Icc a b := fun i hi => by
        have : (i : ℝ) ≤ n := by exact_mod_cast hi
        constructor
        · simp only [t]; have : 0 ≤ (b - a) * i / (n + 1) := by
            apply div_nonneg _ (by positivity); exact mul_nonneg (by linarith) (by positivity)
          linarith
        · simp only [t]
          rw [add_comm, ← le_sub_iff_add_le, div_le_iff₀ (by positivity)]
          nlinarith
      have htinj : Function.Injective fun i : Fin (n + 1) => t i := by
        intro i j hij
        simp only [t] at hij
        have hba : b - a ≠ 0 := by linarith
        field_simp at hij
        have : (i : ℝ) = j := by
          rcases mul_eq_mul_left_iff.mp (show (b - a) * (i : ℝ) = (b - a) * j by linarith)
            with h | h
          · exact h
          · exact absurd h hba
        exact Fin.ext (by exact_mod_cast this)
      refine ⟨Finset.univ.map ⟨fun i : Fin (n + 1) => t i, htinj⟩, by simp, fun x hx => ?_⟩
      obtain ⟨i, -, rfl⟩ := Finset.mem_map.mp hx
      have hi := ht i (Nat.lt_succ_iff.mp i.isLt)
      have h1 : |f ⟨_, hi⟩ - p.eval (t i)| ≤ 0 :=
        (abs_err_le f p ⟨_, hi⟩).trans (le_of_eq hzero.symm)
      have h2 : |f ⟨_, hi⟩ - q.eval (t i)| ≤ 0 :=
        (abs_err_le f q ⟨_, hi⟩).trans (le_of_eq (hE.symm.trans hzero.symm))
      show p.eval (t i) = q.eval (t i)
      have := abs_nonpos_iff.mp h1
      have := abs_nonpos_iff.mp h2
      linarith
  exact eq_of_natDegree_lt_card_of_eval_eq p q (f := fun x : T => (x : ℝ)) Subtype.val_injective
    (fun x => hT x x.2) (by rw [Fintype.card_coe, hTc]; exact Nat.lt_succ_of_le (max_le hp.1 hq.1))

/-- **DLMF §3.11(i)**: for `f` continuous on `[a, b]` (`a < b`) there exists a unique polynomial
of degree `≤ n`, the minimax (best uniform) approximation, minimizing `max_{a≤x≤b} |εₙ(x)|`. -/
theorem dlmf_3_11_i_exists_unique (hab : a < b) (f : C(Icc a b, ℝ)) (n : ℕ) :
    ∃! p, IsMinimax f n p := by
  obtain ⟨p, hp⟩ := minimax_exists f n
  exact ⟨p, hp, fun q hq => minimax_unique hab hq hp⟩

end Azurite.DLMF
