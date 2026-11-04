/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter3.Section6

/-!
# DLMF §3.6(iii): Miller's algorithm

* The Casoratian of two solutions satisfies `a_{n} Cₙ = cₙ C_{n−1}` (`IsRec3.casoratian_succ`), so
  it never vanishes for independent solutions when `cₙ ≠ 0` (`IsRec3.casoratian_ne_zero`).
* Trial values `w_N = 1`, `w_{N+1} = 0` and backward recursion give the trial solution
  (`millerTrial`); on `0, …, N + 1` it is `zₙ/z_N` with `zₙ = wₙ − (w_{N+1}/g_{N+1}) gₙ`
  (`millerZ`, `millerTrial_eq`): the component of the unwanted `gₙ` dies away as `N → ∞`.
* Normalizing factor `Λ` = true `w₀` / trial `w₀` (`millerNorm`): the normalized solutions
  converge to the recessive solution for every fixed `n` (`dlmf_3_6_iii_miller`, `w₀ ≠ 0`).
* Normalization by **3.6.5** `∑ λₙ wₙ = 1` (`millerSumNorm`, truncated at `N`): convergence
  when `(w_{N+1}/g_{N+1}) ∑_{k≤N} λₖ gₖ → 0` (`dlmf_3_6_iii_miller_sum`); no condition on `w₀`
  ("usually superior when the true value of `w₀` is zero or pathologically small").

Not formalized: the repetition with increasing `N` and comparison within a tolerance (an
algorithmic loop), the references (Wimp, Gautschi, Olver, Gil et al.) and continued fractions.
-/

open Filter Topology Finset

namespace Azurite.DLMF

/-! ### The Casoratian of two solutions of 3.6.3 -/

/-- `a_{m+1} C_{m+1} = c_{m+1} C_m` for the Casoratian of two solutions of 3.6.3. -/
theorem IsRec3.casoratian_succ {a b c w g : ℕ → ℂ} (hw : IsRec3 a b c w) (hg : IsRec3 a b c g)
    (m : ℕ) : a (m + 1) * casoratian w g (m + 1) = c (m + 1) * casoratian w g m := by
  unfold casoratian
  linear_combination w (m + 1) * hg.shift m - g (m + 1) * hw.shift m

/-- With `cₙ ≠ 0`, the Casoratian of two independent solutions never vanishes. -/
theorem IsRec3.casoratian_ne_zero {a b c w g : ℕ → ℂ} (hc : ∀ n, 1 ≤ n → c n ≠ 0)
    (hw : IsRec3 a b c w) (hg : IsRec3 a b c g) (h0 : casoratian w g 0 ≠ 0) (n : ℕ) :
    casoratian w g n ≠ 0 := by
  induction n with
  | zero => exact h0
  | succ m ih =>
    intro h
    have := hw.casoratian_succ hg m
    rw [h, mul_zero] at this
    exact mul_ne_zero (hc (m + 1) (by omega)) ih this.symm

/-! ### Miller's algorithm -/

/-- The trial solution: backward recursion from the trial values `w_N = 1`, `w_{N+1} = 0`. -/
noncomputable def millerTrial (a b c : ℕ → ℂ) (N : ℕ) : ℕ → ℂ := bwdRec a b c N 1 0

/-- The trial solution normalized by `Λ = w₀/(trial value of w₀)`. -/
noncomputable def millerNorm (a b c : ℕ → ℂ) (w₀ : ℂ) (N n : ℕ) : ℂ :=
  w₀ / millerTrial a b c N 0 * millerTrial a b c N n

/-- The trial solution normalized by **3.6.5** `∑ λₙ wₙ = 1` (truncated at `N`). -/
noncomputable def millerSumNorm (a b c lam : ℕ → ℂ) (N n : ℕ) : ℂ :=
  millerTrial a b c N n / ∑ k ∈ range (N + 1), lam k * millerTrial a b c N k

/-- The solution `zₙ = wₙ − (w_{N+1}/g_{N+1}) gₙ`, which vanishes at `N + 1`. -/
noncomputable def millerZ (w g : ℕ → ℂ) (N n : ℕ) : ℂ := w n - w (N + 1) / g (N + 1) * g n

theorem millerZ_isRec3 {a b c w g : ℕ → ℂ} (hw : IsRec3 a b c w) (hg : IsRec3 a b c g) (N : ℕ) :
    IsRec3 a b c (millerZ w g N) := fun n hn => by
  unfold millerZ
  linear_combination hw n hn - w (N + 1) / g (N + 1) * hg n hn

theorem millerZ_N {w g : ℕ → ℂ} {N : ℕ} (hg : g (N + 1) ≠ 0) :
    millerZ w g N N = casoratian w g N / g (N + 1) := by
  unfold millerZ casoratian; field_simp

/-- The trial solution is `z/z_N` on `0, …, N + 1`: its component along `g` is
`−w_{N+1}/g_{N+1}` relative to `w`. -/
theorem millerTrial_eq {a b c w g : ℕ → ℂ} (hc : ∀ n, 1 ≤ n → c n ≠ 0) (hw : IsRec3 a b c w)
    (hg : IsRec3 a b c g) {N : ℕ} (hgN : g (N + 1) ≠ 0) (hC : casoratian w g N ≠ 0) {n : ℕ}
    (hn : n ≤ N + 1) : millerTrial a b c N n = millerZ w g N n / millerZ w g N N := by
  have hz : millerZ w g N N ≠ 0 := by rw [millerZ_N hgN]; exact div_ne_zero hC hgN
  have hsol := (millerZ_isRec3 hw hg N).const_mul (millerZ w g N N)⁻¹
  refine ((dlmf_3_6_3_backward hc N 1 0).2.2.2 (fun k => (millerZ w g N N)⁻¹ * millerZ w g N k)
    (fun k hk1 _ => hsol k hk1) (by field_simp) ?_ n hn).symm.trans ?_
  · simp only [millerZ]; field_simp; ring
  · rw [inv_mul_eq_div]

theorem tendsto_millerZ {w g : ℕ → ℂ} (hr : IsRecessiveWrt w g) (n : ℕ) :
    Tendsto (fun N => millerZ w g N n) atTop (𝓝 (w n)) := by
  have h := ((tendsto_add_atTop_iff_nat 1).mpr hr.2).mul_const (g n)
  simpa [millerZ] using (tendsto_const_nhds (x := w n)).sub h

/-- **DLMF §3.6(iii)**, Miller's algorithm: for a recessive solution `w` with `w₀ ≠ 0`, the trial
solutions from `w_N = 1`, `w_{N+1} = 0`, normalized by `Λ = w₀/(trial w₀)`, converge to `wₙ` as
`N → ∞` for every fixed `n`: "the original components of the unwanted solution `gₙ` die away". -/
theorem dlmf_3_6_iii_miller {a b c w g : ℕ → ℂ} (ha : ∀ n, 1 ≤ n → a n ≠ 0)
    (hc : ∀ n, 1 ≤ n → c n ≠ 0) (hw : IsRec3 a b c w) (hw0 : w 0 ≠ 0) (hg : IsRec3 a b c g)
    (hr : IsRecessiveWrt w g) (n : ℕ) :
    Tendsto (fun N => millerNorm a b c (w 0) N n) atTop (𝓝 (w n)) := by
  have hC0 := casoratian_ne_zero_of_recessive ha hw (fun h => hw0 (by simp [h])) hg hr
  have hlim : Tendsto (fun N => w 0 * millerZ w g N n / millerZ w g N 0) atTop
      (𝓝 (w 0 * w n / w 0)) :=
    ((tendsto_millerZ hr n).const_mul (w 0)).div (tendsto_millerZ hr 0) hw0
  rw [mul_div_cancel_left₀ _ hw0] at hlim
  refine hlim.congr' ?_
  have hgN : ∀ᶠ N in atTop, g (N + 1) ≠ 0 := (tendsto_add_atTop_nat 1).eventually hr.1
  filter_upwards [hgN, eventually_ge_atTop n] with N hN hnN
  have hCN := hw.casoratian_ne_zero hc hg hC0 N
  have hz : millerZ w g N N ≠ 0 := by rw [millerZ_N hN]; exact div_ne_zero hCN hN
  unfold millerNorm
  rw [millerTrial_eq hc hw hg hN hCN (by omega), millerTrial_eq hc hw hg hN hCN (by omega)]
  by_cases h0 : millerZ w g N 0 = 0
  · simp [h0]
  · field_simp

/-- **DLMF §3.6(iii)** with the normalization 3.6.5 `∑ λₙ wₙ = 1`: if the truncated sums of the
unwanted components vanish in the limit, `(w_{N+1}/g_{N+1}) ∑_{k≤N} λₖ gₖ → 0`, then the trial
solutions normalized by `∑_{k≤N} λₖ wₖ^{(N)} = 1` converge to `wₙ`. (No condition on `w₀`.) -/
theorem dlmf_3_6_iii_miller_sum {a b c w g lam : ℕ → ℂ} (ha : ∀ n, 1 ≤ n → a n ≠ 0)
    (hc : ∀ n, 1 ≤ n → c n ≠ 0) (hw : IsRec3 a b c w) (hw0 : w ≠ 0) (hg : IsRec3 a b c g)
    (hr : IsRecessiveWrt w g) (hsum : HasSum (fun k => lam k * w k) 1)
    (htail : Tendsto (fun N => w (N + 1) / g (N + 1) * ∑ k ∈ range (N + 1), lam k * g k) atTop
      (𝓝 0)) (n : ℕ) :
    Tendsto (fun N => millerSumNorm a b c lam N n) atTop (𝓝 (w n)) := by
  have hC0 := casoratian_ne_zero_of_recessive ha hw hw0 hg hr
  have hS : Tendsto (fun N => ∑ k ∈ range (N + 1), lam k * w k) atTop (𝓝 1) :=
    (tendsto_add_atTop_iff_nat 1).mpr hsum.tendsto_sum_nat
  have hden : Tendsto (fun N => ∑ k ∈ range (N + 1), lam k * w k -
      w (N + 1) / g (N + 1) * ∑ k ∈ range (N + 1), lam k * g k) atTop (𝓝 (1 - 0)) :=
    hS.sub htail
  have hlim := (tendsto_millerZ hr n).div hden (by norm_num)
  rw [sub_zero, div_one] at hlim
  refine hlim.congr' ?_
  have hgN : ∀ᶠ N in atTop, g (N + 1) ≠ 0 := (tendsto_add_atTop_nat 1).eventually hr.1
  filter_upwards [hgN, eventually_ge_atTop n] with N hN hnN
  have hCN := hw.casoratian_ne_zero hc hg hC0 N
  have hz : millerZ w g N N ≠ 0 := by rw [millerZ_N hN]; exact div_ne_zero hCN hN
  unfold millerSumNorm
  rw [millerTrial_eq hc hw hg hN hCN (by omega),
    sum_congr rfl fun k hk => by
      rw [millerTrial_eq hc hw hg hN hCN (by simp at hk; omega)]]
  have e : ∑ k ∈ range (N + 1), lam k * (millerZ w g N k / millerZ w g N N) =
      (∑ k ∈ range (N + 1), lam k * w k -
        w (N + 1) / g (N + 1) * ∑ k ∈ range (N + 1), lam k * g k) / millerZ w g N N := by
    rw [mul_sum, ← sum_sub_distrib, sum_div]
    refine sum_congr rfl fun k _ => ?_
    unfold millerZ; ring
  simp only [Pi.div_apply]
  rw [e]
  generalize (∑ k ∈ range (N + 1), lam k * w k -
    w (N + 1) / g (N + 1) * ∑ k ∈ range (N + 1), lam k * g k) = D
  by_cases hD : D = 0
  · simp [hD]
  · field_simp

end Azurite.DLMF
