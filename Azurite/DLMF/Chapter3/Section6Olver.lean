/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter3.Section6Inhom

/-!
# DLMF §3.6(v): Olver's algorithm

For 3.6.1 (or 3.6.3 with `dₙ = 0`), `aₙ ≠ 0`:

* `pₙ` (`olverP`): forward recurrence for 3.6.3 with `p₀ = 0`, `p₁ = 1`; `eₙ` (`olverE`) by
  **3.6.8** `aₙeₙ = cₙe_{n−1} − dₙpₙ`, `e₀ = w₀` (`dlmf_3_6_8`). "Forward elimination": for every
  solution `w` of 3.6.1, `eₙ = p_{n+1}wₙ − pₙw_{n+1}` (`olverE_eq`).
* Back substitution **3.6.10** `p_{n+1}wₙ = pₙw_{n+1} + eₙ` from `w_N = 0` (`olverW`,
  `dlmf_3_6_10`) gives `wₙ − (w_N/p_N)pₙ` (`olverW_eq`), the solution of the boundary-value problem
  3.6.7 (`olverW_isBVSol`): the error is `pₙ(w_N/p_N)` (`olver_error`).
* `wₙ/pₙ = ∑_{k≥n} e_k/(p_kp_{k+1})` (`olver_series`, `olver_div_sub`) when `w_N/p_N → 0`, which
  holds under the conditions of §3.6(iv) (`olver_tendsto_div`); so `w_N/p_N` is the tail of the
  series and **3.6.9** tests its first term. The test is eventually passed (`dlmf_3_6_9`).
* Convergence `wₙ^{(N)} → wₙ` (`dlmf_3_6_v_tendsto`), for the inhomogeneous case of §3.6(iv)
  (`dlmf_3_6_v_inhom`) and for the recessive solution of 3.6.3 (`dlmf_3_6_v_recessive`).

Not formalized: the claim that 3.6.9 guarantees relative accuracy `ε` (a heuristic: the tail is
estimated by its first term; DLMF refers to Olver (1967a), Olver and Sookne (1972), Wimp (1984)
for error analyses), the more general normalizing condition.
-/

open Filter Topology Finset

namespace Azurite.DLMF

variable {a b c d : ℕ → ℂ}

/-- `pₙ`: the solution of 3.6.3 with `p₀ = 0`, `p₁ = 1`, by forward recurrence. -/
noncomputable def olverP (a b c : ℕ → ℂ) : ℕ → ℂ := fwdRec a b c 0 1

/-- `eₙ` of **3.6.8**: `aₙ eₙ = cₙ e_{n−1} − dₙ pₙ`, `e₀ = w₀`. -/
noncomputable def olverE (a b c d : ℕ → ℂ) (w₀ : ℂ) : ℕ → ℂ
  | 0 => w₀
  | m + 1 => (c (m + 1) * olverE a b c d w₀ m - d (m + 1) * olverP a b c (m + 1)) / a (m + 1)

theorem olverP_isRec3 (ha : ∀ n, 1 ≤ n → a n ≠ 0) : IsRec3 a b c (olverP a b c) :=
  (dlmf_3_6_3_forward ha 0 1).1

@[simp] theorem olverP_zero : olverP a b c 0 = 0 := rfl

@[simp] theorem olverP_one : olverP a b c 1 = 1 := rfl

/-- **DLMF 3.6.8**. -/
theorem dlmf_3_6_8 (ha : ∀ n, 1 ≤ n → a n ≠ 0) (w₀ : ℂ) {n : ℕ} (hn : 1 ≤ n) :
    a n * olverE a b c d w₀ n = c n * olverE a b c d w₀ (n - 1) - d n * olverP a b c n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have := ha (m + 1) hn
  simp only [olverE, Nat.add_sub_cancel]
  field_simp

/-- Forward elimination: for every solution `w` of 3.6.1,
`eₙ = p_{n+1} wₙ − pₙ w_{n+1}` (the `eₙ` of 3.6.8 with `e₀ = w₀`). -/
theorem olverE_eq (ha : ∀ n, 1 ≤ n → a n ≠ 0) {w : ℕ → ℂ} (hw : IsRec3Inh a b c d w) (n : ℕ) :
    olverE a b c d (w 0) n = olverP a b c (n + 1) * w n - olverP a b c n * w (n + 1) := by
  have hp := olverP_isRec3 (b := b) (c := c) ha
  induction n with
  | zero => simp [olverE]
  | succ m ih =>
    have ham := ha (m + 1) (by omega)
    have e1 := hp.shift m
    have e2 := hw (m + 1) (by omega)
    simp only [Nat.add_sub_cancel] at e2
    simp only [olverE]
    rw [ih, div_eq_iff ham]
    linear_combination (-(w (m + 1))) * e1 + olverP a b c (m + 1) * e2

/-! ### Back substitution 3.6.10 -/

/-- Back substitution `wₙ = (pₙ w_{n+1} + eₙ)/p_{n+1}` from `w_N = 0`: after `k` steps, the value
at `N − k`. -/
noncomputable def olverWAux (a b c d : ℕ → ℂ) (w₀ : ℂ) (N : ℕ) : ℕ → ℂ
  | 0 => 0
  | k + 1 => (olverP a b c (N - (k + 1)) * olverWAux a b c d w₀ N k +
      olverE a b c d w₀ (N - (k + 1))) / olverP a b c (N - k)

/-- The values `w_N^{(N)} = 0, w_{N−1}, …, w₀` of Olver's algorithm. -/
noncomputable def olverW (a b c d : ℕ → ℂ) (w₀ : ℂ) (N n : ℕ) : ℂ :=
  olverWAux a b c d w₀ N (N - n)

/-- **DLMF 3.6.10**: `p_{n+1} wₙ = pₙ w_{n+1} + eₙ` for `n < N`, `w_N = 0`. -/
theorem dlmf_3_6_10 (w₀ : ℂ) {N : ℕ} (hp : ∀ n, 1 ≤ n → n ≤ N → olverP a b c n ≠ 0) :
    olverW a b c d w₀ N N = 0 ∧ ∀ n, n < N →
      olverP a b c (n + 1) * olverW a b c d w₀ N n =
        olverP a b c n * olverW a b c d w₀ N (n + 1) + olverE a b c d w₀ n := by
  refine ⟨by simp [olverW, olverWAux], fun n hn => ?_⟩
  obtain ⟨k, hk⟩ : ∃ k, N - n = k + 1 := ⟨N - n - 1, by omega⟩
  have hk' : N - (n + 1) = k := by omega
  have hpn := hp (n + 1) (by omega) (by omega)
  simp only [olverW, hk, hk', olverWAux, show N - (k + 1) = n by omega,
    show N - k = n + 1 by omega]
  field_simp

/-- The values of Olver's algorithm are `wₙ − (w_N/p_N) pₙ`, `n ≤ N`, for the solution `w` of
3.6.1 with the given `w₀`. -/
theorem olverW_eq (ha : ∀ n, 1 ≤ n → a n ≠ 0) {w : ℕ → ℂ} (hw : IsRec3Inh a b c d w) {N : ℕ}
    (hN : 1 ≤ N) (hp : ∀ n, 1 ≤ n → n ≤ N → olverP a b c n ≠ 0) {n : ℕ} (hn : n ≤ N) :
    olverW a b c d (w 0) N n = w n - w N / olverP a b c N * olverP a b c n := by
  have key : ∀ k, k ≤ N → olverWAux a b c d (w 0) N k =
      w (N - k) - w N / olverP a b c N * olverP a b c (N - k) := by
    intro k
    induction k with
    | zero =>
      intro _
      have := hp N hN le_rfl
      simp only [olverWAux, Nat.sub_zero]
      field_simp
      ring
    | succ k ih =>
      intro hk
      have hpk := hp (N - k) (by omega) (by omega)
      have hE := olverE_eq ha hw (N - (k + 1))
      rw [show N - (k + 1) + 1 = N - k by omega] at hE
      simp only [olverWAux]
      rw [ih (by omega), hE, div_eq_iff hpk]
      ring
  unfold olverW
  rw [key _ (by omega), show N - (N - n) = n by omega]

/-- Olver's values solve the boundary-value problem 3.6.7 (`w₀^{(N)} = w₀`, `w_N^{(N)} = 0`):
the algorithm is forward elimination and back substitution for 3.6.7. -/
theorem olverW_isBVSol (ha : ∀ n, 1 ≤ n → a n ≠ 0) {w : ℕ → ℂ} (hw : IsRec3Inh a b c d w)
    {N : ℕ} (hN : 1 ≤ N) (hp : ∀ n, 1 ≤ n → n ≤ N → olverP a b c n ≠ 0) :
    IsBVSol a b c d (w 0) N (olverW a b c d (w 0) N) := by
  have hP := olverP_isRec3 (b := b) (c := c) ha
  refine ⟨by rw [olverW_eq ha hw hN hp (Nat.zero_le _)]; simp,
    (dlmf_3_6_10 (w 0) hp).1, fun n hn1 hn2 => ?_⟩
  rw [olverW_eq ha hw hN hp (by omega), olverW_eq ha hw hN hp (by omega),
    olverW_eq ha hw hN hp (by omega)]
  linear_combination hw n hn1 - w N / olverP a b c N * hP n hn1

/-! ### Convergence, the series for `wₙ/pₙ`, and the stopping rule 3.6.9 -/

/-- **DLMF §3.6(v)**: if `w_N/p_N → 0` (as under the conditions of §3.6(iv),
`olver_tendsto_div`), Olver's values converge to `wₙ` as `N → ∞`. -/
theorem dlmf_3_6_v_tendsto (ha : ∀ n, 1 ≤ n → a n ≠ 0) {w : ℕ → ℂ} (hw : IsRec3Inh a b c d w)
    (hp : ∀ n, 1 ≤ n → olverP a b c n ≠ 0)
    (hwp : Tendsto (fun N => w N / olverP a b c N) atTop (𝓝 0)) (n : ℕ) :
    Tendsto (fun N => olverW a b c d (w 0) N n) atTop (𝓝 (w n)) := by
  have h := tendsto_const_nhds (x := w n) |>.sub (hwp.mul_const (olverP a b c n))
  rw [zero_mul, sub_zero] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop n, eventually_ge_atTop 1] with N hN hN1
  rw [olverW_eq ha hw hN1 (fun k hk _ => hp k hk) hN]

/-- `wₙ/pₙ − w_{n+1}/p_{n+1} = eₙ/(pₙ p_{n+1})` (3.6.10 divided by `pₙ p_{n+1}`). -/
theorem olver_div_sub (ha : ∀ n, 1 ≤ n → a n ≠ 0) {w : ℕ → ℂ} (hw : IsRec3Inh a b c d w)
    {n : ℕ} (hpn : olverP a b c n ≠ 0) (hpn1 : olverP a b c (n + 1) ≠ 0) :
    w n / olverP a b c n - w (n + 1) / olverP a b c (n + 1) =
      olverE a b c d (w 0) n / (olverP a b c n * olverP a b c (n + 1)) := by
  rw [olverE_eq ha hw]
  field_simp

/-- `wₙ/pₙ = ∑_{k=n}^∞ e_k/(p_k p_{k+1})` (`n ≥ 1`, partial sums), when `w_N/p_N → 0`. -/
theorem olver_series (ha : ∀ n, 1 ≤ n → a n ≠ 0) {w : ℕ → ℂ} (hw : IsRec3Inh a b c d w)
    (hp : ∀ n, 1 ≤ n → olverP a b c n ≠ 0)
    (hwp : Tendsto (fun N => w N / olverP a b c N) atTop (𝓝 0)) {n : ℕ} (hn : 1 ≤ n) :
    Tendsto (fun K => ∑ k ∈ range K, olverE a b c d (w 0) (n + k) /
      (olverP a b c (n + k) * olverP a b c (n + k + 1))) atTop (𝓝 (w n / olverP a b c n)) := by
  have htel : ∀ K, ∑ k ∈ range K, olverE a b c d (w 0) (n + k) /
      (olverP a b c (n + k) * olverP a b c (n + k + 1)) =
        w n / olverP a b c n - w (n + K) / olverP a b c (n + K) := by
    intro K
    induction K with
    | zero => simp
    | succ K ih =>
      rw [sum_range_succ, ih, ← olver_div_sub ha hw (hp _ (by omega)) (hp _ (by omega))]
      ring_nf
  have hshift : Tendsto (fun K => w (n + K) / olverP a b c (n + K)) atTop (𝓝 0) := by
    have := (tendsto_add_atTop_iff_nat n).mpr hwp
    simpa [add_comm] using this
  have hlim := (tendsto_const_nhds (x := w n / olverP a b c n)).sub hshift
  rw [sub_zero] at hlim
  exact hlim.congr fun K => (htel K).symm

/-- The error of Olver's values: `wₙ − wₙ^{(N)} = pₙ (w_N/p_N)`, and `w_N/p_N` is the tail
`∑_{k≥N} e_k/(p_k p_{k+1})` of the series (`olver_series` with `n = N`): 3.6.9 tests its first
term. -/
theorem olver_error (ha : ∀ n, 1 ≤ n → a n ≠ 0) {w : ℕ → ℂ} (hw : IsRec3Inh a b c d w) {N : ℕ}
    (hN : 1 ≤ N) (hp : ∀ n, 1 ≤ n → n ≤ N → olverP a b c n ≠ 0) {n : ℕ} (hn : n ≤ N) :
    w n - olverW a b c d (w 0) N n = olverP a b c n * (w N / olverP a b c N) := by
  rw [olverW_eq ha hw hN hp hn]; ring

/-- **DLMF 3.6.9**: the stopping rule is eventually satisfied — if `e_n/(p_n p_{n+1}) ≠ 0` for
`1 ≤ n ≤ M` and the series of `olver_series` converges, then for every `ε > 0` there is `N ≥ M`
with `|e_N/(p_N p_{N+1})| ≤ ε min_{1≤n≤M} |eₙ/(pₙ p_{n+1})|`. -/
theorem dlmf_3_6_9 (ha : ∀ n, 1 ≤ n → a n ≠ 0) {w : ℕ → ℂ} (hw : IsRec3Inh a b c d w)
    (hp : ∀ n, 1 ≤ n → olverP a b c n ≠ 0)
    (hwp : Tendsto (fun N => w N / olverP a b c N) atTop (𝓝 0)) {M : ℕ} (hM : 1 ≤ M)
    (ht : ∀ n, 1 ≤ n → n ≤ M →
      olverE a b c d (w 0) n / (olverP a b c n * olverP a b c (n + 1)) ≠ 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ N, M ≤ N ∧ ‖olverE a b c d (w 0) N / (olverP a b c N * olverP a b c (N + 1))‖ ≤
      ε * (Finset.Icc 1 M).inf' ⟨1, Finset.mem_Icc.mpr ⟨le_rfl, hM⟩⟩
        (fun n => ‖olverE a b c d (w 0) n / (olverP a b c n * olverP a b c (n + 1))‖) := by
  set m := (Finset.Icc 1 M).inf' ⟨1, Finset.mem_Icc.mpr ⟨le_rfl, hM⟩⟩
    (fun n => ‖olverE a b c d (w 0) n / (olverP a b c n * olverP a b c (n + 1))‖)
  have hm : 0 < m := by
    obtain ⟨n, hn, hmn⟩ := Finset.exists_mem_eq_inf' ⟨1, Finset.mem_Icc.mpr ⟨le_rfl, hM⟩⟩
      (fun n => ‖olverE a b c d (w 0) n / (olverP a b c n * olverP a b c (n + 1))‖)
    simp only [m]
    rw [hmn]
    simp only [Finset.mem_Icc] at hn
    exact norm_pos_iff.mpr (ht n hn.1 hn.2)
  -- the terms tend to zero: differences of `wₙ/pₙ`, which converges to `0`
  have hterm : Tendsto (fun N => olverE a b c d (w 0) N /
      (olverP a b c N * olverP a b c (N + 1))) atTop (𝓝 0) := by
    have h := hwp.sub ((tendsto_add_atTop_iff_nat 1).mpr hwp)
    rw [sub_zero] at h
    refine h.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with N hN
    exact olver_div_sub ha hw (hp N hN) (hp (N + 1) (by omega))
  have hev := (hterm.norm.eventually (gt_mem_nhds (by rw [norm_zero]; positivity :
    ‖(0 : ℂ)‖ < ε * m)))
  obtain ⟨N, hN⟩ := (hev.and (eventually_ge_atTop M)).exists
  exact ⟨N, hN.2, hN.1.le⟩

/-- Under the conditions of §3.6(iv) (`f₀ ≠ 0`, `fₙ/gₙ → 0`, `wₙ/gₙ → 0`), `pₙ` is a multiple of
`g₀fₙ − f₀gₙ` and `w_N/p_N → 0`. -/
theorem olver_tendsto_div (ha : ∀ n, 1 ≤ n → a n ≠ 0) {f g w : ℕ → ℂ}
    (hf : IsRec3 a b c f) (hg : IsRec3 a b c g) (hf0 : f 0 ≠ 0)
    (hgN : ∀ᶠ n in atTop, g n ≠ 0) (hfg : Tendsto (fun n => f n / g n) atTop (𝓝 0))
    (hwg : Tendsto (fun n => w n / g n) atTop (𝓝 0)) :
    Tendsto (fun N => w N / olverP a b c N) atTop (𝓝 0) := by
  have hC := casoratian_ne_zero_of_recessive ha hf (fun h => hf0 (by simp [h])) hg ⟨hgN, hfg⟩
  have hh := bvH_isRec3 hf hg
  have hh1 : bvH f g 1 ≠ 0 := by
    intro h; apply hC; simp only [casoratian, zero_add]; unfold bvH at h; linear_combination -h
  have hpe : olverP a b c = fun n => (bvH f g 1)⁻¹ * bvH f g n :=
    (olverP_isRec3 ha).eq_of_eq ha (hh.const_mul _)
      (by show (0 : ℂ) = _ * bvH f g 0; simp [bvH, mul_comm])
      (by show (1 : ℂ) = (bvH f g 1)⁻¹ * bvH f g 1; rw [inv_mul_cancel₀ hh1])
  have hhg : Tendsto (fun N => (bvH f g 1)⁻¹ * (bvH f g N / g N)) atTop
      (𝓝 ((bvH f g 1)⁻¹ * (g 0 * 0 - f 0))) := by
    refine (((hfg.const_mul (g 0)).sub_const (f 0)).const_mul _).congr' ?_
    filter_upwards [hgN] with N hN
    unfold bvH; field_simp
  have hlim := hwg.div hhg (by simpa using ⟨hh1, hf0⟩)
  rw [zero_div] at hlim
  refine hlim.congr' ?_
  filter_upwards [hgN] with N hN
  rw [hpe]
  simp only [Pi.div_apply]
  field_simp

/-- **DLMF §3.6(v)** under the conditions of §3.6(iv): Olver's values converge to the wanted
solution `wₙ` of 3.6.1. -/
theorem dlmf_3_6_v_inhom (ha : ∀ n, 1 ≤ n → a n ≠ 0) {f g w : ℕ → ℂ}
    (hf : IsRec3 a b c f) (hg : IsRec3 a b c g) (hf0 : f 0 ≠ 0)
    (hgN : ∀ᶠ n in atTop, g n ≠ 0) (hfg : Tendsto (fun n => f n / g n) atTop (𝓝 0))
    (hw : IsRec3Inh a b c d w) (hwg : Tendsto (fun n => w n / g n) atTop (𝓝 0))
    (hp : ∀ n, 1 ≤ n → olverP a b c n ≠ 0) (n : ℕ) :
    Tendsto (fun N => olverW a b c d (w 0) N n) atTop (𝓝 (w n)) :=
  dlmf_3_6_v_tendsto ha hw hp (olver_tendsto_div ha hf hg hf0 hgN hfg hwg) n

/-- **DLMF §3.6(v)** for "the recessive solution of the homogeneous equation (3.6.3)" (`dₙ = 0`,
`w₀ ≠ 0`): Olver's values converge to `wₙ`. -/
theorem dlmf_3_6_v_recessive (ha : ∀ n, 1 ≤ n → a n ≠ 0) {g w : ℕ → ℂ}
    (hw : IsRec3 a b c w) (hw0 : w 0 ≠ 0) (hg : IsRec3 a b c g) (hr : IsRecessiveWrt w g)
    (hp : ∀ n, 1 ≤ n → olverP a b c n ≠ 0) (n : ℕ) :
    Tendsto (fun N => olverW a b c (fun _ => 0) (w 0) N n) atTop (𝓝 (w n)) :=
  dlmf_3_6_v_inhom ha hw hg hw0 hr.1 hr.2 (d := fun _ => 0) (fun k hk => hw k hk) hr.2 hp n

end Azurite.DLMF
