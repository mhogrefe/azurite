/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter3.Section3

/-!
# DLMF §3.3(ii): Lagrange interpolation with equally-spaced nodes

Equally-spaced nodes `x_k = x₀ + kh`, `k = n₀, …, n₁` (3.3.8–3.3.9: `eqSigma`, `eqN0`, `eqN1`;
`n₀ = −⌊n/2⌋`, `n₁ = n₀ + n`), indexed in Lean by `j = k − n₀ ∈ Fin (n + 1)` (`eqNode`), so
that the results of §3.3(i) apply directly.

* 3.3.10: `lagCoeff` (DLMF's formula) and `lagCoeff'` (the factor `t − k` cancelled), equal off
  the node `t = k` (`lagCoeff_eq`); `eqNode_basis_eval`: `A_k^n(t) = ℓ_k(x₀ + th)`, via
  `∏'_{i} (j − i) = (−1)^{n−j} j! (n − j)!` (`prod_fin_erase_sub`).
* 3.3.7: `dlmf_3_3_7` (DLMF's coefficients, `t` not a node, where 3.3.10 reads `0/0`) and
  `dlmf_3_3_7'` (cancelled coefficients, every real `t`); the remainder `R_{n,t}` is
  `lagrangeRem` of §3.3(i) at `x₀ + th`.
* 3.3.11: `dlmf_3_3_11`, from `dlmf_3_3_5` and `ω_{n+1}(x₀ + th) = h^{n+1} ∏ (t − k)`
  (`eqNode_nodal_eval`), with `ξ` in `[min(x₀ + th, x_{n₀}), max(x₀ + th, x_{n₁})]`
  (`= [x_{n₀}, x_{n₁}]` for `n₀ < t < n₁`); valid for every real `t`.
* 3.3.12–3.3.13: `eqBoundCoeff` (the maximum taken as a supremum over a bounded `t`-set),
  `dlmf_3_3_13`.
* 3.3.14–3.3.15 (linear interpolation): `lagCoeff'_one` (`A_0^1 = 1 − t`, `A_1^1 = t`),
  `dlmf_3_3_14`, `dlmf_3_3_15` (`c₁ = 1/8`, attained at `t = ½`), `dlmf_3_3_15_bound`.
-/

namespace Azurite.DLMF

open Polynomial Finset Lagrange

/-! ### The index range 3.3.8–3.3.9 -/

/-- **DLMF 3.3.9**: `σ = ½(1 − (−1)ⁿ)`. -/
def eqSigma (n : ℕ) : ℤ := (1 - (-1) ^ n) / 2

/-- **DLMF 3.3.8**: `n₀ = −½(n − σ)`. -/
def eqN0 (n : ℕ) : ℤ := -((n - eqSigma n) / 2)

/-- **DLMF 3.3.8**: `n₁ = ½(n + σ)`. -/
def eqN1 (n : ℕ) : ℤ := (n + eqSigma n) / 2

theorem eqSigma_eq (n : ℕ) : eqSigma n = n % 2 := by
  unfold eqSigma
  rcases Nat.even_or_odd n with ⟨m, rfl⟩ | ⟨m, rfl⟩
  · have h : (-1 : ℤ) ^ (m + m) = 1 := by rw [← two_mul, pow_mul]; norm_num
    rw [h]; push_cast; omega
  · have h : (-1 : ℤ) ^ (2 * m + 1) = -1 := by rw [pow_succ, pow_mul]; norm_num
    rw [h]; push_cast; omega

/-- The halving in 3.3.8 is exact: `n₀ = −⌊n/2⌋`. -/
theorem eqN0_eq (n : ℕ) : eqN0 n = -((n : ℤ) / 2) := by
  unfold eqN0; rw [eqSigma_eq]; omega

/-- `n₁ − n₀ = n`: the `n + 1` nodes are `x_{n₀}, …, x_{n₁}`. -/
theorem eqN1_eq (n : ℕ) : eqN1 n = eqN0 n + n := by
  unfold eqN1 eqN0; rw [eqSigma_eq]; omega

/-- The nodes `x_k = x₀ + kh`, `k = n₀, …, n₁`, indexed by `j = k − n₀ ∈ {0, …, n}`. -/
noncomputable def eqNode (x₀ h : ℝ) (n : ℕ) (j : Fin (n + 1)) : ℝ :=
  x₀ + ((eqN0 n + (j : ℕ) : ℤ) : ℝ) * h

theorem eqNode_injective {x₀ h : ℝ} (hh : h ≠ 0) (n : ℕ) : Function.Injective (eqNode x₀ h n) := by
  intro i j hij
  simp only [eqNode, add_right_inj, mul_left_inj' hh, Int.cast_inj] at hij
  exact Fin.ext (by omega)

/-! ### Reindexing `k = n₀ + j` -/

/-- `j ↦ a + j`. -/
def shiftEmb (a : ℤ) (n : ℕ) : Fin (n + 1) ↪ ℤ :=
  ⟨fun j => a + (j : ℕ), fun i j h => Fin.ext (by simpa using h)⟩

@[simp] theorem shiftEmb_apply (a : ℤ) (n : ℕ) (j : Fin (n + 1)) :
    shiftEmb a n j = a + (j : ℕ) := rfl

theorem shiftEmb_map_univ (a : ℤ) (n : ℕ) : univ.map (shiftEmb a n) = Icc a (a + n) := by
  ext m
  simp only [mem_map, mem_univ, true_and, mem_Icc, shiftEmb_apply]
  constructor
  · rintro ⟨i, rfl⟩; have := i.2; exact ⟨by omega, by omega⟩
  · rintro ⟨h1, h2⟩
    exact ⟨⟨(m - a).toNat, by omega⟩, show a + (((m - a).toNat : ℕ) : ℤ) = m by omega⟩

theorem shiftEmb_map_erase (a : ℤ) (n : ℕ) (j : Fin (n + 1)) :
    (univ.erase j).map (shiftEmb a n) = (Icc a (a + n)).erase (a + (j : ℕ)) := by
  ext m
  simp only [mem_map, mem_erase, mem_univ, and_true, mem_Icc, shiftEmb_apply]
  constructor
  · rintro ⟨i, hi, rfl⟩
    have := i.2
    exact ⟨fun h => hi (Fin.ext (by omega)), by omega, by omega⟩
  · rintro ⟨hne, h1, h2⟩
    refine ⟨⟨(m - a).toNat, by omega⟩, fun h => hne ?_,
      show a + (((m - a).toNat : ℕ) : ℤ) = m by omega⟩
    have := congrArg (fun i : Fin (n + 1) => (i : ℕ)) h
    simp only at this
    omega

theorem valEmbedding_map_erase (n : ℕ) (j : Fin (n + 1)) :
    (univ.erase j).map Fin.valEmbedding = (range (n + 1)).erase j := by
  ext m
  simp only [mem_map, mem_erase, mem_univ, and_true, mem_range, Fin.valEmbedding_apply]
  constructor
  · rintro ⟨i, hi, rfl⟩; exact ⟨fun h => hi (Fin.ext h), i.2⟩
  · rintro ⟨hne, hm⟩; exact ⟨⟨m, hm⟩, fun h => hne (by rw [← h]), rfl⟩

/-! ### The coefficients 3.3.10 -/

theorem prod_range_sub_eq_factorial : ∀ j : ℕ, ∏ i ∈ range j, ((j : ℝ) - i) = j.factorial
  | 0 => by simp
  | j + 1 => by
    rw [prod_range_succ', Nat.factorial_succ]
    push_cast
    rw [← prod_range_sub_eq_factorial j]
    simp only [add_sub_add_right_eq_sub, sub_zero]
    ring

/-- `∏'_{i=0}^{j+e} (j − i) = (−1)^e j! e!`. -/
theorem prod_range_erase_sub (j : ℕ) : ∀ e : ℕ,
    ∏ i ∈ (range (j + e + 1)).erase j, ((j : ℝ) - i) = (-1) ^ e * j.factorial * e.factorial
  | 0 => by
    rw [add_zero, range_add_one, erase_insert notMem_range_self, prod_range_sub_eq_factorial]
    simp
  | e + 1 => by
    rw [show j + (e + 1) + 1 = (j + e + 1) + 1 by ring, range_add_one,
      erase_insert_of_ne (by omega), prod_insert (by simp), prod_range_erase_sub j e,
      Nat.factorial_succ]
    push_cast
    ring

theorem prod_fin_erase_sub (n : ℕ) (j : Fin (n + 1)) :
    ∏ i ∈ univ.erase j, (((j : ℕ) : ℝ) - (i : ℕ)) =
      (-1) ^ (n - j) * (j : ℕ).factorial * (n - j).factorial := by
  have h := prod_map (univ.erase j) Fin.valEmbedding fun i => ((j : ℕ) : ℝ) - i
  simp only [Fin.valEmbedding_apply] at h
  have key : ∀ N i : ℕ, i ≤ N → ∏ x ∈ (range (N + 1)).erase i, ((i : ℝ) - x) =
      (-1) ^ (N - i) * i.factorial * (N - i).factorial := by
    intro N i hi
    obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_le hi
    rw [Nat.add_sub_cancel_left]
    exact prod_range_erase_sub i e
  rw [← h, valEmbedding_map_erase]
  exact key n j (Nat.lt_succ_iff.mp j.2)

/-- **DLMF 3.3.10**: the Lagrangian interpolation coefficients
`A_k^n = (−1)^{n₁+k}/((k − n₀)! (n₁ − k)! (t − k)) ∏_{m=n₀}^{n₁} (t − m)`. -/
noncomputable def lagCoeff (n : ℕ) (k : ℤ) (t : ℝ) : ℝ :=
  (-1 : ℝ) ^ (eqN1 n + k) /
      ((k - eqN0 n).toNat.factorial * (eqN1 n - k).toNat.factorial * (t - k)) *
    ∏ m ∈ Icc (eqN0 n) (eqN1 n), (t - m)

/-- 3.3.10 with the factor `t − k` cancelled (the polynomial in `t`, valid also at `t = k`). -/
noncomputable def lagCoeff' (n : ℕ) (k : ℤ) (t : ℝ) : ℝ :=
  (-1 : ℝ) ^ (eqN1 n + k) / ((k - eqN0 n).toNat.factorial * (eqN1 n - k).toNat.factorial) *
    ∏ m ∈ (Icc (eqN0 n) (eqN1 n)).erase k, (t - m)

theorem lagCoeff_eq {n : ℕ} {k : ℤ} (hk : k ∈ Icc (eqN0 n) (eqN1 n)) {t : ℝ} (ht : t ≠ k) :
    lagCoeff n k t = lagCoeff' n k t := by
  have htk : t - k ≠ 0 := sub_ne_zero.mpr ht
  rw [lagCoeff, lagCoeff', ← mul_prod_erase _ (fun m : ℤ => t - m) hk]
  field_simp

/-- `A_k^n(t) = ℓ_k(x₀ + th)`: the coefficients are the Lagrange basis polynomials 3.3.2 at the
equally-spaced nodes, with `k = n₀ + j`. -/
theorem eqNode_basis_eval {x₀ h : ℝ} (hh : h ≠ 0) (n : ℕ) (j : Fin (n + 1)) (t : ℝ) :
    (Lagrange.basis univ (eqNode x₀ h n) j).eval (x₀ + t * h) =
      lagCoeff' n (eqN0 n + (j : ℕ)) t := by
  rw [dlmf_3_3_2]
  have hfac : ∀ i ∈ univ.erase j, (x₀ + t * h - eqNode x₀ h n i) /
      (eqNode x₀ h n j - eqNode x₀ h n i) =
      (t - ((eqN0 n + ((i : ℕ) : ℤ) : ℤ) : ℝ)) / (((j : ℕ) : ℝ) - (i : ℕ)) := by
    intro i _
    simp only [eqNode]
    push_cast
    rw [show x₀ + t * h - (x₀ + (↑(eqN0 n) + ↑↑i) * h) = (t - (↑(eqN0 n) + ↑↑i)) * h by ring,
      show x₀ + (↑(eqN0 n) + ↑↑j) * h - (x₀ + (↑(eqN0 n) + ↑↑i) * h) =
        ((↑↑j : ℝ) - ↑↑i) * h by ring, mul_div_mul_right _ _ hh]
  rw [prod_congr rfl hfac, prod_div_distrib, prod_fin_erase_sub]
  have hnum := prod_map (univ.erase j) (shiftEmb (eqN0 n) n) fun m : ℤ => t - m
  rw [shiftEmb_map_erase] at hnum
  simp only [shiftEmb_apply] at hnum
  rw [lagCoeff', eqN1_eq, hnum]
  have h1 : (eqN0 n + ((j : ℕ) : ℤ) - eqN0 n).toNat = j := by omega
  have h2 : (eqN0 n + (n : ℤ) - (eqN0 n + ((j : ℕ) : ℤ))).toNat = n - j := by omega
  have hsign : (-1 : ℝ) ^ (eqN0 n + (n : ℤ) + (eqN0 n + ((j : ℕ) : ℤ))) =
      (-1) ^ (n - (j : ℕ)) := by
    rw [show eqN0 n + (n : ℤ) + (eqN0 n + ((j : ℕ) : ℤ)) =
        2 * (eqN0 n + ((j : ℕ) : ℤ)) + ((n - (j : ℕ) : ℕ) : ℤ) by omega,
      zpow_add₀ (by norm_num), zpow_mul, zpow_natCast]
    norm_num
  rw [h1, h2, hsign]
  have hs : ((-1 : ℝ) ^ (n - (j : ℕ))) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; simp
  have hf1 : ((j : ℕ).factorial : ℝ) ≠ 0 := by positivity
  have hf2 : ((n - (j : ℕ)).factorial : ℝ) ≠ 0 := by positivity
  have hs0 : ((-1 : ℝ) ^ (n - (j : ℕ))) ≠ 0 := by simp
  field_simp
  linear_combination -(∏ x ∈ univ.erase j, (t - ((eqN0 n + ((x : ℕ) : ℤ) : ℤ) : ℝ))) * hs

/-! ### The interpolation formula 3.3.7 and the remainder 3.3.11 -/

/-- **DLMF 3.3.7** with the cancelled coefficients (valid for every real `t`):
`f(x₀ + th) = ∑_{k=n₀}^{n₁} A_k^n f_k + R_{n,t}`. -/
theorem dlmf_3_3_7' {x₀ h : ℝ} (hh : h ≠ 0) (n : ℕ) (f : ℝ → ℝ) (t : ℝ) :
    f (x₀ + t * h) = ∑ k ∈ Icc (eqN0 n) (eqN1 n), lagCoeff' n k t * f (x₀ + k * h) +
      lagrangeRem (eqNode x₀ h n) f (x₀ + t * h) := by
  rw [lagrangeRem, dlmf_3_3_1, eqN1_eq, ← shiftEmb_map_univ, sum_map]
  simp only [shiftEmb_apply, eqNode_basis_eval hh, eqNode]
  push_cast
  ring

/-- **DLMF 3.3.7** with DLMF's coefficients 3.3.10, for `t` not a node (at `t = k` the
formula 3.3.10 for `A_k^n` is `0/0`; see `dlmf_3_3_7'`). -/
theorem dlmf_3_3_7 {x₀ h : ℝ} (hh : h ≠ 0) (n : ℕ) (f : ℝ → ℝ) {t : ℝ}
    (ht : ∀ k ∈ Icc (eqN0 n) (eqN1 n), t ≠ k) :
    f (x₀ + t * h) = ∑ k ∈ Icc (eqN0 n) (eqN1 n), lagCoeff n k t * f (x₀ + k * h) +
      lagrangeRem (eqNode x₀ h n) f (x₀ + t * h) := by
  rw [sum_congr rfl fun k hk => by rw [lagCoeff_eq hk (ht k hk)]]
  exact dlmf_3_3_7' hh n f t

theorem eqNode_nodal_eval {x₀ h : ℝ} (n : ℕ) (t : ℝ) :
    (nodal univ (eqNode x₀ h n)).eval (x₀ + t * h) =
      h ^ (n + 1) * ∏ k ∈ Icc (eqN0 n) (eqN1 n), (t - k) := by
  rw [eval_nodal, eqN1_eq, ← shiftEmb_map_univ, prod_map]
  simp only [shiftEmb_apply, eqNode]
  rw [show h ^ (n + 1) = ∏ _j : Fin (n + 1), h by simp, ← prod_mul_distrib]
  refine prod_congr rfl fun j _ => ?_
  push_cast
  ring

/-- **DLMF 3.3.11**: `R_{n,t} = h^{n+1}/(n+1)! f^{(n+1)}(ξ) ∏_{k=n₀}^{n₁} (t − k)`, `ξ` in the
smallest closed interval containing `x₀ + th` and the nodes, for `f` that is `n + 1` times
differentiable on an open set containing that interval (as in `dlmf_3_3_5`). For
`n₀ < t < n₁` the interval is `[x_{n₀}, x_{n₁}]`. -/
theorem dlmf_3_3_11 {x₀ h : ℝ} (hh : 0 < h) (n : ℕ) (f : ℝ → ℝ) {U : Set ℝ} (hU : IsOpen U)
    (hd : ∀ k ≤ n, DifferentiableOn ℝ (iteratedDeriv k f) U) (t : ℝ)
    (hI : Set.Icc (min (x₀ + t * h) (x₀ + eqN0 n * h)) (max (x₀ + t * h) (x₀ + eqN1 n * h))
      ⊆ U) :
    ∃ ξ ∈ Set.Icc (min (x₀ + t * h) (x₀ + eqN0 n * h)) (max (x₀ + t * h) (x₀ + eqN1 n * h)),
      lagrangeRem (eqNode x₀ h n) f (x₀ + t * h) =
        h ^ (n + 1) / (n + 1).factorial * iteratedDeriv (n + 1) f ξ *
          ∏ k ∈ Icc (eqN0 n) (eqN1 n), (t - k) := by
  set s := insert (x₀ + t * h) (univ.image (eqNode x₀ h n))
  have hmem : ∀ y ∈ s, y ∈ Set.Icc (min (x₀ + t * h) (x₀ + eqN0 n * h))
      (max (x₀ + t * h) (x₀ + eqN1 n * h)) := by
    intro y hy
    rcases mem_insert.mp hy with rfl | hy
    · exact ⟨min_le_left _ _, le_max_left _ _⟩
    · obtain ⟨j, -, rfl⟩ := mem_image.mp hy
      have hj : (j : ℕ) ≤ n := Nat.lt_succ_iff.mp j.2
      have h1 : (eqN0 n : ℝ) ≤ ((eqN0 n + (j : ℕ) : ℤ) : ℝ) := by
        exact_mod_cast (by omega : eqN0 n ≤ eqN0 n + (j : ℕ))
      have h2 : ((eqN0 n + (j : ℕ) : ℤ) : ℝ) ≤ (eqN1 n : ℝ) := by
        exact_mod_cast (by rw [eqN1_eq]; omega : eqN0 n + (j : ℕ) ≤ eqN1 n)
      refine ⟨(min_le_right _ _).trans ?_, le_trans ?_ (le_max_right _ _)⟩ <;>
        simp only [eqNode] <;> nlinarith
  have hsub : Set.Icc (s.min' (insert_nonempty _ _)) (s.max' (insert_nonempty _ _)) ⊆
      Set.Icc (min (x₀ + t * h) (x₀ + eqN0 n * h)) (max (x₀ + t * h) (x₀ + eqN1 n * h)) :=
    Set.Icc_subset_Icc (s.le_min' _ _ fun y hy => (hmem y hy).1)
      (s.max'_le _ _ fun y hy => (hmem y hy).2)
  obtain ⟨ξ, hξ, hR⟩ := dlmf_3_3_5 (eqNode x₀ h n) (eqNode_injective hh.ne' n) f hU hd
    (x₀ + t * h) (hsub.trans hI)
  refine ⟨ξ, hsub hξ, ?_⟩
  rw [hR, eqNode_nodal_eval]
  ring

/-! ### The error bound 3.3.12–3.3.13 -/

/-- **DLMF 3.3.12**: `c_n = (1/(n+1)!) max_{t ∈ J} ∏_{k=n₀}^{n₁} |t − k|` over a `t`-interval
`J` (the maximum is taken as a supremum). -/
noncomputable def eqBoundCoeff (n : ℕ) (J : Set ℝ) : ℝ :=
  1 / (n + 1).factorial * sSup ((fun t : ℝ => ∏ k ∈ Icc (eqN0 n) (eqN1 n), |t - k|) '' J)

/-- **DLMF 3.3.13**: `|R_{n,t}| ≤ c_n h^{n+1} |f^{(n+1)}(ξ)|` for `t` in a bounded `t`-set `J`,
`ξ` as in `dlmf_3_3_11`. -/
theorem dlmf_3_3_13 {x₀ h : ℝ} (hh : 0 < h) (n : ℕ) (f : ℝ → ℝ) {U : Set ℝ} (hU : IsOpen U)
    (hd : ∀ k ≤ n, DifferentiableOn ℝ (iteratedDeriv k f) U) {J : Set ℝ}
    (hJ : Bornology.IsBounded J) {t : ℝ} (ht : t ∈ J)
    (hI : Set.Icc (min (x₀ + t * h) (x₀ + eqN0 n * h)) (max (x₀ + t * h) (x₀ + eqN1 n * h))
      ⊆ U) :
    ∃ ξ ∈ Set.Icc (min (x₀ + t * h) (x₀ + eqN0 n * h)) (max (x₀ + t * h) (x₀ + eqN1 n * h)),
      |lagrangeRem (eqNode x₀ h n) f (x₀ + t * h)| ≤
        eqBoundCoeff n J * h ^ (n + 1) * |iteratedDeriv (n + 1) f ξ| := by
  obtain ⟨ξ, hξ, hR⟩ := dlmf_3_3_11 hh n f hU hd t hI
  refine ⟨ξ, hξ, ?_⟩
  have hcont : Continuous fun t : ℝ => ∏ k ∈ Icc (eqN0 n) (eqN1 n), |t - k| := by fun_prop
  have hbdd : BddAbove ((fun t : ℝ => ∏ k ∈ Icc (eqN0 n) (eqN1 n), |t - k|) '' J) :=
    (hJ.isCompact_closure.image_of_continuousOn hcont.continuousOn).bddAbove.mono
      (Set.image_mono subset_closure)
  have hle := le_csSup hbdd (Set.mem_image_of_mem _ ht)
  rw [hR, abs_mul, abs_mul, abs_prod, abs_div, abs_of_pos (by positivity : (0 : ℝ) < h ^ (n + 1)),
    abs_of_pos (by positivity : (0 : ℝ) < (n + 1).factorial), eqBoundCoeff]
  have h0 : 0 ≤ |iteratedDeriv (n + 1) f ξ| := abs_nonneg _
  have hf : (0 : ℝ) < (n + 1).factorial := by positivity
  have hp : 0 < h ^ (n + 1) := by positivity
  calc h ^ (n + 1) / (n + 1).factorial * |iteratedDeriv (n + 1) f ξ| *
        ∏ k ∈ Icc (eqN0 n) (eqN1 n), |t - k|
      ≤ h ^ (n + 1) / (n + 1).factorial * |iteratedDeriv (n + 1) f ξ| *
        sSup ((fun t : ℝ => ∏ k ∈ Icc (eqN0 n) (eqN1 n), |t - k|) '' J) :=
        mul_le_mul_of_nonneg_left hle (by positivity)
    _ = _ := by ring

/-! ### Linear interpolation 3.3.14–3.3.15 -/

theorem eqN0_one : eqN0 1 = 0 := by rw [eqN0_eq]; norm_num

theorem eqN1_one : eqN1 1 = 1 := by rw [eqN1_eq, eqN0_one]; norm_num

theorem Icc_zero_one : Icc (0 : ℤ) 1 = {0, 1} := by decide

/-- 3.3.10 for `n = 1`: `A_0^1 = 1 − t`, `A_1^1 = t`. -/
theorem lagCoeff'_one (t : ℝ) : lagCoeff' 1 0 t = 1 - t ∧ lagCoeff' 1 1 t = t := by
  simp only [lagCoeff', eqN0_one, eqN1_one, Icc_zero_one]
  rw [show ({0, 1} : Finset ℤ).erase 1 = {0} by decide,
    show ({0, 1} : Finset ℤ).erase 0 = {1} by decide]
  refine ⟨?_, ?_⟩ <;> simp

/-- **DLMF 3.3.14**: `f_t = (1 − t) f₀ + t f₁ + R_{1,t}` (valid for every real `t`). -/
theorem dlmf_3_3_14 {x₀ h : ℝ} (hh : h ≠ 0) (f : ℝ → ℝ) (t : ℝ) :
    f (x₀ + t * h) = (1 - t) * f x₀ + t * f (x₀ + h) +
      lagrangeRem (eqNode x₀ h 1) f (x₀ + t * h) := by
  rw [dlmf_3_3_7' hh 1 f t]
  simp only [eqN0_one, eqN1_one, Icc_zero_one]
  rw [sum_pair (by norm_num), (lagCoeff'_one t).1, (lagCoeff'_one t).2]
  simp

/-- **DLMF 3.3.15**: `c₁ = 1/8` on `0 < t < 1`. -/
theorem dlmf_3_3_15 : eqBoundCoeff 1 (Set.Ioo 0 1) = 1 / 8 := by
  have hset : (fun t : ℝ => ∏ k ∈ Icc (eqN0 1) (eqN1 1), |t - k|) '' Set.Ioo 0 1 =
      (fun t : ℝ => t * (1 - t)) '' Set.Ioo 0 1 := by
    refine Set.image_congr fun t ht => ?_
    simp only [eqN0_one, eqN1_one, Icc_zero_one]
    rw [prod_pair (by norm_num)]
    push_cast
    rw [sub_zero, abs_of_pos ht.1, abs_of_neg (by linarith [ht.2])]
    ring
  have hg : IsGreatest ((fun t : ℝ => t * (1 - t)) '' Set.Ioo 0 1) (1 / 4) := by
    refine ⟨⟨1 / 2, ⟨by norm_num, by norm_num⟩, by norm_num⟩, ?_⟩
    rintro _ ⟨t, -, rfl⟩
    nlinarith [sq_nonneg (t - 1 / 2)]
  rw [eqBoundCoeff, hset, hg.csSup_eq]
  norm_num [Nat.factorial]

/-- 3.3.13 with 3.3.15: `|R_{1,t}| ≤ h² |f''(ξ)|/8` for `0 < t < 1`, `ξ ∈ [x₀, x₀ + h]`. -/
theorem dlmf_3_3_15_bound {x₀ h : ℝ} (hh : 0 < h) (f : ℝ → ℝ) {U : Set ℝ} (hU : IsOpen U)
    (hd : ∀ k ≤ 1, DifferentiableOn ℝ (iteratedDeriv k f) U) (hI : Set.Icc x₀ (x₀ + h) ⊆ U)
    {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
    ∃ ξ ∈ Set.Icc x₀ (x₀ + h), |lagrangeRem (eqNode x₀ h 1) f (x₀ + t * h)| ≤
      1 / 8 * h ^ 2 * |iteratedDeriv 2 f ξ| := by
  have hmin : min (x₀ + t * h) (x₀ + (eqN0 1 : ℤ) * h) = x₀ := by
    rw [eqN0_one, Int.cast_zero, zero_mul, add_zero]
    exact min_eq_right (by nlinarith [mul_pos ht.1 hh])
  have hmax : max (x₀ + t * h) (x₀ + (eqN1 1 : ℤ) * h) = x₀ + h := by
    rw [eqN1_one, Int.cast_one, one_mul]
    exact max_eq_right (by nlinarith [mul_lt_mul_of_pos_right ht.2 hh])
  obtain ⟨ξ, hξ, hR⟩ := dlmf_3_3_13 hh 1 f hU hd (Metric.isBounded_Ioo 0 1) ht
    (by rw [hmin, hmax]; exact hI)
  rw [hmin, hmax, dlmf_3_3_15] at *
  exact ⟨ξ, hξ, hR⟩

end Azurite.DLMF
