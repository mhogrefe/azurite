/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/


import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Analysis.Calculus.LocalExtr.Rolle
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.Deriv.Polynomial

/-!
# DLMF §3.3(i): Lagrange interpolation

Lagrange interpolation over a field (real or complex nodes), with nodes `z : Fin (n + 1) → F`.
The basis `ℓ_k`, nodal polynomial `ω_{n+1}`, weights `ω̃_k` and the interpolation polynomial are
Mathlib's `Lagrange.basis`, `Lagrange.nodal`, `Lagrange.nodalWeight` and `Lagrange.interpolate`.

* 3.3.1: `dlmf_3_3_1` (`∑ ℓ_k f_k`), `dlmf_3_3_1_nodal`, `dlmf_3_3_1_barycentric`; existence,
  degree and uniqueness: `lagrange_unique`.
* 3.3.2: `dlmf_3_3_2`, `dlmf_3_3_2_delta`; 3.3.3: `dlmf_3_3_3`; 3.3.3_1: `dlmf_3_3_3_1`;
  3.3.3_2: `dlmf_3_3_3_2`.
* 3.3.4: the remainder `lagrangeRem`.
* 3.3.5: `dlmf_3_3_5`, for `f` that is `n + 1` times differentiable on an open set containing `I`
  (DLMF: `f^{(n+1)}` continuous on `I`; continuity is not needed). Proof: the auxiliary function
  `f − P_n − K ω_{n+1}` has `n + 2` zeros in `I`, and the generalized Rolle theorem
  `exists_iteratedDeriv_eq_zero` gives a zero of its `(n + 1)`-st derivative
  `f^{(n+1)} − K (n + 1)!` (`iteratedDeriv_sub_poly_eqOn`, `iterate_derivative_monic_natDegree`).

The contour-integral form 3.3.6 is in `Section3Contour`.
-/

namespace Azurite.DLMF

open Polynomial Finset Lagrange

/-! ### The interpolation polynomial 3.3.1–3.3.3 -/

section Field

variable {F : Type*} [Field F] {n : ℕ} (z : Fin (n + 1) → F)

/-- **DLMF 3.3.2**: `ℓ_k(z) = ∏'_{j} (z − z_j)/(z_k − z_j)` (Mathlib's `Lagrange.basis`). -/
theorem dlmf_3_3_2 (k : Fin (n + 1)) (w : F) :
    (Lagrange.basis univ z k).eval w = ∏ j ∈ univ.erase k, (w - z j) / (z k - z j) := by
  rw [Lagrange.basis, eval_prod]
  refine prod_congr rfl fun j _ => ?_
  rw [basisDivisor, eval_mul, eval_C, eval_sub, eval_X, eval_C, div_eq_inv_mul]

/-- **DLMF 3.3.2**: `ℓ_k(z_j) = δ_{k,j}`. -/
theorem dlmf_3_3_2_delta (hz : Function.Injective z) (k j : Fin (n + 1)) :
    (Lagrange.basis univ z k).eval (z j) = if k = j then 1 else 0 := by
  split_ifs with h
  · subst h; exact eval_basis_self (fun _ _ _ _ h => hz h) (mem_univ _)
  · exact eval_basis_of_ne h (mem_univ _)

/-- **DLMF 3.3.3**: the nodal polynomial `ω_{n+1}(z) = ∏ (z − z_k)`. -/
theorem dlmf_3_3_3 (w : F) : (nodal univ z).eval w = ∏ k, (w - z k) := eval_nodal

/-- **DLMF 3.3.3_1**: `ω̃_k = 1/ω'_{n+1}(z_k) = ∏'_j 1/(z_k − z_j)`. -/
theorem dlmf_3_3_3_1 (k : Fin (n + 1)) :
    nodalWeight univ z k = 1 / (derivative (nodal univ z)).eval (z k) ∧
      nodalWeight univ z k = ∏ j ∈ univ.erase k, 1 / (z k - z j) := by
  refine ⟨by rw [nodalWeight_eq_eval_derivative_nodal (mem_univ _), one_div], ?_⟩
  rw [nodalWeight]
  exact prod_congr rfl fun j _ => (one_div _).symm

/-- **The Lagrange interpolation polynomial** (`P_n = interpolate`): of degree at most `n`, with
`P_n(z_k) = f_k`, and the unique such polynomial. -/
theorem lagrange_unique (hz : Function.Injective z) (f : Fin (n + 1) → F) :
    (interpolate univ z f).natDegree ≤ n ∧ (∀ k, (interpolate univ z f).eval (z k) = f k) ∧
      ∀ Q : F[X], Q.natDegree ≤ n → (∀ k, Q.eval (z k) = f k) → Q = interpolate univ z f := by
  have hinj : Set.InjOn z (univ : Finset (Fin (n + 1))) := fun _ _ _ _ h => hz h
  refine ⟨?_, fun k => eval_interpolate_at_node f hinj (mem_univ _), fun Q hQ hQf => ?_⟩
  · have := degree_interpolate_lt (r := f) hinj
    rw [card_univ, Fintype.card_fin] at this
    by_cases h0 : interpolate univ z f = 0
    · rw [h0]; simp
    · rw [degree_eq_natDegree h0] at this
      exact_mod_cast Nat.lt_succ_iff.mp (by exact_mod_cast this)
  · refine eq_interpolate_of_eval_eq f hinj ?_ fun k _ => hQf k
    rw [card_univ, Fintype.card_fin]
    exact (degree_le_natDegree).trans_lt (by exact_mod_cast Nat.lt_succ_of_le hQ)

/-- **DLMF 3.3.1**, first form: `P_n(z) = ∑ ℓ_k(z) f_k`. -/
theorem dlmf_3_3_1 (f : Fin (n + 1) → F) (w : F) :
    (interpolate univ z f).eval w = ∑ k, (Lagrange.basis univ z k).eval w * f k := by
  rw [interpolate_apply, eval_finsetSum]
  exact sum_congr rfl fun k _ => by rw [eval_mul, eval_C, mul_comm]

/-- **DLMF 3.3.1**, second form: `P_n(z) = ω_{n+1}(z) ∑ ω̃_k f_k/(z − z_k)`, `z` not a node. -/
theorem dlmf_3_3_1_nodal (f : Fin (n + 1) → F) {w : F} (hw : ∀ k, w ≠ z k) :
    (interpolate univ z f).eval w =
      (nodal univ z).eval w * ∑ k, nodalWeight univ z k * f k / (w - z k) := by
  rw [eval_interpolate_not_at_node f fun k _ => hw k]
  congr 1
  exact sum_congr rfl fun k _ => by rw [div_eq_mul_inv]; ring

/-- **DLMF 3.3.1**, the barycentric form `P_n(z) = ∑ (ω̃_k f_k/(z − z_k)) / ∑ ω̃_k/(z − z_k)`. -/
theorem dlmf_3_3_1_barycentric (hz : Function.Injective z) (f : Fin (n + 1) → F) {w : F}
    (hw : ∀ k, w ≠ z k) :
    (interpolate univ z f).eval w =
      (∑ k, nodalWeight univ z k * f k / (w - z k)) / ∑ k, nodalWeight univ z k / (w - z k) := by
  rw [eval_interpolate_not_at_node' f (fun _ _ _ _ h => hz h) univ_nonempty fun k _ => hw k]
  congr 1 <;> exact sum_congr rfl fun k _ => by ring

/-- **DLMF 3.3.3_2**: `1 = ∑ ℓ_k(z) = ω_{n+1}(z) ∑ ω̃_k/(z − z_k)` (`z` not a node in the second
form). -/
theorem dlmf_3_3_3_2 (hz : Function.Injective z) (w : F) :
    1 = ∑ k, (Lagrange.basis univ z k).eval w ∧
      ((∀ k, w ≠ z k) → 1 = (nodal univ z).eval w * ∑ k, nodalWeight univ z k / (w - z k)) := by
  have hinj : Set.InjOn z (univ : Finset (Fin (n + 1))) := fun _ _ _ _ h => hz h
  refine ⟨?_, fun hw => ?_⟩
  · rw [← eval_finsetSum, sum_basis hinj univ_nonempty, eval_one]
  · have h := dlmf_3_3_1_nodal z 1 hw
    rw [interpolate_one hinj univ_nonempty, eval_one] at h
    simpa using h

end Field

/-! ### The error term 3.3.4–3.3.5 -/

/-- **DLMF 3.3.4**: the remainder `R_n(z) = f(z) − ∑ ℓ_k(z) f_k`. -/
noncomputable def lagrangeRem {F : Type*} [Field F] {n : ℕ} (z : Fin (n + 1) → F) (f : F → F)
    (w : F) : F :=
  f w - (interpolate univ z (fun k => f (z k))).eval w

theorem iteratedDeriv_eval (p : ℝ[X]) (k : ℕ) :
    iteratedDeriv k (fun t => p.eval t) = fun t => (derivative^[k] p).eval t := by
  induction k generalizing p with
  | zero => rfl
  | succ k ih =>
    rw [iteratedDeriv_succ', show deriv (fun t => p.eval t) = fun t => (derivative p).eval t from
      funext fun t => Polynomial.deriv p, ih, Function.iterate_succ_apply]

/-- **Generalized Rolle's theorem**: if `g` is `m` times differentiable on an open `U` and
vanishes at `m + 1` increasing points `t₀ < ⋯ < t_m` of `U` with `[t₀, t_m] ⊆ U`, then
`g^{(m)}` vanishes somewhere in `[t₀, t_m]`. -/
theorem exists_iteratedDeriv_eq_zero : ∀ (m : ℕ) (g : ℝ → ℝ) (U : Set ℝ),
    (∀ k < m, DifferentiableOn ℝ (iteratedDeriv k g) U) → ∀ t : Fin (m + 1) → ℝ, StrictMono t →
      Set.Icc (t 0) (t (Fin.last m)) ⊆ U → (∀ i, g (t i) = 0) →
      ∃ ξ ∈ Set.Icc (t 0) (t (Fin.last m)), iteratedDeriv m g ξ = 0
  | 0, g, U, _, t, _, _, hz => ⟨t 0, ⟨le_rfl, le_rfl⟩, by simpa using hz 0⟩
  | m + 1, g, U, hd, t, ht, hU, hz => by
    -- Rolle on each `[t_i, t_{i+1}]`
    have hg : DifferentiableOn ℝ g U := by simpa using hd 0 (by omega)
    have hR : ∀ i : Fin (m + 1), ∃ s ∈ Set.Ioo (t i.castSucc) (t i.succ), deriv g s = 0 := by
      intro i
      have hlt := ht (Fin.castSucc_lt_succ (i := i))
      have hsub : Set.Icc (t i.castSucc) (t i.succ) ⊆ U := fun x hx => hU
        ⟨(ht.monotone (Fin.zero_le _)).trans hx.1, hx.2.trans (ht.monotone (Fin.le_last _))⟩
      exact exists_deriv_eq_zero hlt (hg.continuousOn.mono hsub) (by rw [hz, hz])
    choose s hs hs0 using hR
    have hsm : StrictMono s := by
      refine Fin.strictMono_iff_lt_succ.mpr fun i => ?_
      exact (hs i.castSucc).2.trans (by simpa using (hs i.succ).1)
    have hdg : ∀ k < m, DifferentiableOn ℝ (iteratedDeriv k (deriv g)) U := fun k hk => by
      rw [← iteratedDeriv_succ']; exact hd (k + 1) (by omega)
    have hsU : Set.Icc (s 0) (s (Fin.last m)) ⊆ U := fun x hx => hU
      ⟨((hs 0).1.le.trans hx.1), hx.2.trans ((hs (Fin.last m)).2.le)⟩
    obtain ⟨ξ, hξ, hξ0⟩ := exists_iteratedDeriv_eq_zero m (deriv g) U hdg s hsm hsU hs0
    refine ⟨ξ, ⟨(hs 0).1.le.trans hξ.1, hξ.2.trans (hs (Fin.last m)).2.le⟩, ?_⟩
    rw [iteratedDeriv_succ']; exact hξ0

theorem iterate_derivative_monic_natDegree {p : ℝ[X]} (hp : p.Monic) :
    derivative^[p.natDegree] p = C (p.natDegree.factorial : ℝ) := by
  have hdeg : (derivative^[p.natDegree] p).natDegree = 0 := by
    have := natDegree_iterate_derivative p p.natDegree
    omega
  rw [eq_C_of_natDegree_eq_zero hdeg, coeff_iterate_derivative, zero_add,
    Nat.descFactorial_self, ← leadingCoeff, hp.leadingCoeff]
  simp

/-- The derivatives of `t ↦ f(t) − Q(t)` on an open set where `f` is differentiable enough. -/
theorem iteratedDeriv_sub_poly_eqOn {f : ℝ → ℝ} {U : Set ℝ} (hU : IsOpen U) (Q : ℝ[X]) (m : ℕ)
    (hd : ∀ k < m, DifferentiableOn ℝ (iteratedDeriv k f) U) :
    ∀ k ≤ m, Set.EqOn (iteratedDeriv k fun t => f t - Q.eval t)
      (fun t => iteratedDeriv k f t - (derivative^[k] Q).eval t) U := by
  intro k
  induction k with
  | zero => intro _ t _; simp
  | succ k ih =>
    intro hk t ht
    have hev : (iteratedDeriv k fun t => f t - Q.eval t) =ᶠ[nhds t]
        fun t => iteratedDeriv k f t - (derivative^[k] Q).eval t :=
      Filter.eventually_of_mem (hU.mem_nhds ht) (ih (by omega))
    rw [iteratedDeriv_succ, hev.deriv_eq]
    refine ((((hd k (by omega)).differentiableAt (hU.mem_nhds ht)).hasDerivAt.sub
      (Polynomial.hasDerivAt _ t)).deriv).trans ?_
    simp only [iteratedDeriv_succ, Function.iterate_succ_apply']

/-- **DLMF 3.3.5**: for real nodes `x_k` and `f` that is `n + 1` times differentiable on an
open set containing the smallest closed interval `I` containing `x, x₀, …, x_n`,
`R_n(x) = f^{(n+1)}(ξ) ω_{n+1}(x)/(n+1)!` for some `ξ ∈ I`. -/
theorem dlmf_3_3_5 {n : ℕ} (x : Fin (n + 1) → ℝ) (hx : Function.Injective x) (f : ℝ → ℝ)
    {U : Set ℝ} (hU : IsOpen U) (hd : ∀ k ≤ n, DifferentiableOn ℝ (iteratedDeriv k f) U)
    (t : ℝ) (hI : Set.Icc ((insert t (univ.image x)).min' (insert_nonempty _ _))
      ((insert t (univ.image x)).max' (insert_nonempty _ _)) ⊆ U) :
    ∃ ξ ∈ Set.Icc ((insert t (univ.image x)).min' (insert_nonempty _ _))
      ((insert t (univ.image x)).max' (insert_nonempty _ _)),
      lagrangeRem x f t = iteratedDeriv (n + 1) f ξ / (n + 1).factorial *
        (nodal univ x).eval t := by
  set s := insert t (univ.image x)
  have htI : t ∈ Set.Icc (s.min' (insert_nonempty _ _)) (s.max' (insert_nonempty _ _)) :=
    ⟨s.min'_le t (mem_insert_self _ _), s.le_max' t (mem_insert_self _ _)⟩
  obtain ⟨hPdeg, hPev, -⟩ := lagrange_unique x hx (fun k => f (x k))
  set P := interpolate univ x (fun k => f (x k))
  by_cases hnode : ∃ j, t = x j
  · obtain ⟨j, rfl⟩ := hnode
    refine ⟨x j, htI, ?_⟩
    rw [lagrangeRem, hPev j, sub_self, eval_nodal_at_node (mem_univ j), mul_zero]
  push Not at hnode
  have hω : (nodal univ x).eval t ≠ 0 := by
    rw [eval_nodal]; exact prod_ne_zero_iff.mpr fun k _ => sub_ne_zero.mpr (hnode k)
  set K := lagrangeRem x f t / (nodal univ x).eval t
  set Q : ℝ[X] := P + C K * nodal univ x
  -- the auxiliary function vanishes at `t` and at the nodes
  have hzero : ∀ u ∈ s, f u - Q.eval u = 0 := by
    intro u hu
    rcases mem_insert.mp hu with rfl | hu
    · simp only [Q, eval_add, eval_mul, eval_C, K]
      rw [div_mul_cancel₀ _ hω, lagrangeRem]; ring
    · obtain ⟨j, -, rfl⟩ := mem_image.mp hu
      simp only [Q, eval_add, eval_mul, eval_C, hPev j, eval_nodal_at_node (mem_univ j)]
      ring
  have hcard : s.card = n + 2 := by
    rw [card_insert_of_notMem (by simpa [eq_comm] using hnode), card_image_of_injective _ hx,
      card_univ, Fintype.card_fin]
  set e := s.orderEmbOfFin hcard
  have he0 : e 0 = s.min' (insert_nonempty _ _) := by
    rw [show (0 : Fin (n + 2)) = ⟨0, by omega⟩ from rfl, orderEmbOfFin_zero hcard (by omega)]
  have hel : e (Fin.last (n + 1)) = s.max' (insert_nonempty _ _) := by
    rw [show Fin.last (n + 1) = ⟨n + 2 - 1, by omega⟩ from Fin.ext (by simp),
      orderEmbOfFin_last hcard (by omega)]
  have hEq := iteratedDeriv_sub_poly_eqOn hU Q (n + 1) fun k hk => hd k (by omega)
  have hdF : ∀ k < n + 1, DifferentiableOn ℝ (iteratedDeriv k fun u => f u - Q.eval u) U := by
    intro k hk
    exact ((hd k (by omega)).sub (Polynomial.differentiable _).differentiableOn).congr
      (hEq k (by omega))
  obtain ⟨ξ, hξ, hξ0⟩ := exists_iteratedDeriv_eq_zero (n + 1) (fun u => f u - Q.eval u) U hdF e
    e.strictMono (by rw [he0, hel]; exact hI) fun i => hzero _ (orderEmbOfFin_mem s hcard i)
  rw [he0, hel] at hξ
  refine ⟨ξ, hξ, ?_⟩
  have h1 := hEq (n + 1) le_rfl (hI hξ)
  rw [hξ0] at h1
  have hP0 : derivative^[n + 1] P = 0 := iterate_derivative_eq_zero (by omega)
  have hnat : (nodal univ x).natDegree = n + 1 := by
    rw [natDegree_nodal, card_univ, Fintype.card_fin]
  have hω0 : derivative^[n + 1] (nodal univ x) = C ((n + 1).factorial : ℝ) := by
    have := iterate_derivative_monic_natDegree (nodal_monic (s := univ) (v := x))
    rwa [hnat] at this
  simp only [Q, iterate_map_add, hP0, iterate_derivative_C_mul, hω0, zero_add,
    eval_mul, eval_C] at h1
  have hK : K = iteratedDeriv (n + 1) f ξ / (n + 1).factorial := by
    have hf : ((n + 1).factorial : ℝ) ≠ 0 := by positivity
    field_simp
    linarith
  rw [← hK]
  simp only [K]
  field_simp

end Azurite.DLMF
