/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter3.Section6Olver

/-!
# DLMF §3.6(v), error analysis: Olver (1967a), §§4–5 and 7

DLMF refers to Olver (1967a) for the convergence proofs and error analyses of §3.6(v). In the
notation of 3.6.1 (Olver's `aᵣ`, `cᵣ` are our `cᵣ`, `aᵣ`), with `pₙ`, `eₙ`, `wₙ^{(N)}` of
`Section6Olver`:

* (4.09)–(4.10): `wₙ^{(N+1)} − wₙ^{(N)} = pₙ e_N/(p_N p_{N+1})` (`olver_4_10`, `olver_4_09`), so the
  effect of `N → N + 1` is known before the back substitution; the criteria (4.11) and (4.12)
  (`olver_4_11`, `olver_4_12`).
* The truncation error (5.01)–(5.02): `wₙ − wₙ^{(N)} = E_N pₙ` with `E_N = ∑_{s≥N} eₛ/(pₛp_{s+1})`
  (`olverTrunc`, `olver_5_01`); the expansion (5.03) `wₙ = pₙ ∑_{s≥n} eₛ/(pₛp_{s+1})` and its
  partial sum (5.04) `= wₙ^{(N)}` (`olver_5_03`, `olver_5_04`, exact): the whole scheme approximates
  the series by partial sums.
* Rounding errors (§7): (7.01) `pₙ = (f₀gₙ − g₀fₙ)/(f₀g₁ − g₀f₁)` (`olver_7_01`), so `pₙ` becomes
  proportional to `gₙ` (`olverP_div_tendsto`); (7.02) the sensitivity `(fₙ/f₀) δk` of the wanted
  solution to its normalizing value (`olver_7_02`); a rounding error in `wₛ^{(N)}` is multiplied by
  `pᵣ/pₛ` in the back substitution (`olver_backsub_propagation`).
* DLMF's criterion 3.6.9: it bounds the next change by `ε|pₙ| min_m |eₘ/(pₘp_{m+1})|`
  (`dlmf_3_6_9_one_step`), a relative change `≤ ε` when the terms have no cancellation
  (`dlmf_3_6_9_relative`).
-/

open Filter Topology Finset

namespace Azurite.DLMF

variable {a b c d : ℕ → ℂ}

/-! ### The terms `eₛ/(pₛ p_{s+1})` and the change `N → N + 1` -/

/-- The terms `eₛ/(pₛ p_{s+1})` of Olver's series (5.02)–(5.03). -/
noncomputable def olverT (a b c d : ℕ → ℂ) (w₀ : ℂ) (s : ℕ) : ℂ :=
  olverE a b c d w₀ s / (olverP a b c s * olverP a b c (s + 1))

/-- The partial sums telescope: `∑_{k<K} e_{n+k}/(p_{n+k}p_{n+k+1}) = wₙ/pₙ − w_{n+K}/p_{n+K}`. -/
theorem olver_partial_sum (ha : ∀ n, 1 ≤ n → a n ≠ 0) {w : ℕ → ℂ} (hw : IsRec3Inh a b c d w)
    (hp : ∀ n, 1 ≤ n → olverP a b c n ≠ 0) {n : ℕ} (hn : 1 ≤ n) (K : ℕ) :
    ∑ k ∈ range K, olverT a b c d (w 0) (n + k) =
      w n / olverP a b c n - w (n + K) / olverP a b c (n + K) := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [sum_range_succ, ih, olverT, ← olver_div_sub ha hw (hp _ (by omega)) (hp _ (by omega))]
    ring_nf

/-- **Olver (4.10)**: `wₙ^{(N+1)} − wₙ^{(N)} = pₙ e_N/(p_N p_{N+1})`, `n ≤ N`: the effect of
changing `N` into `N + 1` can be predicted before any back substitution is carried out. -/
theorem olver_4_10 (ha : ∀ n, 1 ≤ n → a n ≠ 0) {w : ℕ → ℂ} (hw : IsRec3Inh a b c d w) {N : ℕ}
    (hN : 1 ≤ N) (hp : ∀ n, 1 ≤ n → n ≤ N + 1 → olverP a b c n ≠ 0) {n : ℕ} (hn : n ≤ N) :
    olverW a b c d (w 0) (N + 1) n - olverW a b c d (w 0) N n =
      olverP a b c n * olverT a b c d (w 0) N := by
  rw [olverW_eq ha hw (by omega) hp (by omega),
    olverW_eq ha hw hN (fun k h1 h2 => hp k h1 (by omega)) hn, olverT,
    ← olver_div_sub ha hw (hp N hN (by omega)) (hp (N + 1) (by omega) le_rfl)]
  ring

/-- **Olver (4.09)**: `wₙ^{(N+1)} − wₙ^{(N)} = (pₙ/p_{n+1})(w_{n+1}^{(N+1)} − w_{n+1}^{(N)})`. -/
theorem olver_4_09 (ha : ∀ n, 1 ≤ n → a n ≠ 0) {w : ℕ → ℂ} (hw : IsRec3Inh a b c d w) {N : ℕ}
    (hN : 1 ≤ N) (hp : ∀ n, 1 ≤ n → n ≤ N + 1 → olverP a b c n ≠ 0) {n : ℕ} (hn : n + 1 ≤ N) :
    olverW a b c d (w 0) (N + 1) n - olverW a b c d (w 0) N n =
      olverP a b c n / olverP a b c (n + 1) *
        (olverW a b c d (w 0) (N + 1) (n + 1) - olverW a b c d (w 0) N (n + 1)) := by
  rw [olver_4_10 ha hw hN hp (by omega), olver_4_10 ha hw hN hp hn]
  have := hp (n + 1) (by omega) (by omega)
  field_simp

/-- **Olver (4.11)**: if `|p_L e_N/(p_N p_{N+1})| < ½·10^{−D}` then `w_L^{(N)}` and `w_L^{(N+1)}`
agree to `D` decimal places. -/
theorem olver_4_11 (ha : ∀ n, 1 ≤ n → a n ≠ 0) {w : ℕ → ℂ} (hw : IsRec3Inh a b c d w) {N : ℕ}
    (hN : 1 ≤ N) (hp : ∀ n, 1 ≤ n → n ≤ N + 1 → olverP a b c n ≠ 0) {L : ℕ} (hL : L ≤ N)
    {D : ℕ} (h : ‖olverP a b c L * olverT a b c d (w 0) N‖ < 1 / 2 * 10 ^ (-(D : ℤ))) :
    ‖olverW a b c d (w 0) (N + 1) L - olverW a b c d (w 0) N L‖ < 1 / 2 * 10 ^ (-(D : ℤ)) := by
  rwa [olver_4_10 ha hw hN hp hL]

/-- **Olver (4.12)**: if `|e_N/p_{N+1}| < ½·10^{−D}` and `|pₙ| ≤ |p_N|`, then `wₙ^{(N)}` and
`wₙ^{(N+1)}` agree to `D` decimal places. -/
theorem olver_4_12 (ha : ∀ n, 1 ≤ n → a n ≠ 0) {w : ℕ → ℂ} (hw : IsRec3Inh a b c d w) {N : ℕ}
    (hN : 1 ≤ N) (hp : ∀ n, 1 ≤ n → n ≤ N + 1 → olverP a b c n ≠ 0) {n : ℕ} (hn : n ≤ N)
    (hpn : ‖olverP a b c n‖ ≤ ‖olverP a b c N‖) {D : ℕ}
    (h : ‖olverE a b c d (w 0) N / olverP a b c (N + 1)‖ < 1 / 2 * 10 ^ (-(D : ℤ))) :
    ‖olverW a b c d (w 0) (N + 1) n - olverW a b c d (w 0) N n‖ < 1 / 2 * 10 ^ (-(D : ℤ)) := by
  rw [olver_4_10 ha hw hN hp hn]
  have hpN : 0 < ‖olverP a b c N‖ := norm_pos_iff.mpr (hp N hN (by omega))
  calc ‖olverP a b c n * olverT a b c d (w 0) N‖
      = ‖olverP a b c n‖ / ‖olverP a b c N‖ *
          ‖olverE a b c d (w 0) N / olverP a b c (N + 1)‖ := by
        rw [olverT, ← norm_div, ← norm_mul]
        congr 1
        field_simp
    _ ≤ 1 * ‖olverE a b c d (w 0) N / olverP a b c (N + 1)‖ := by
        gcongr
        exact (div_le_one hpN).mpr hpn
    _ < _ := by rw [one_mul]; exact h

/-! ### The truncation error: Olver (5.01)–(5.04) -/

/-- `E_N`, the sum of the series `∑_{s≥N} eₛ/(pₛ p_{s+1})` (Olver (5.02)), as the limit of its
partial sums. -/
noncomputable def olverTrunc (a b c d : ℕ → ℂ) (w₀ : ℂ) (N : ℕ) : ℂ :=
  limUnder atTop fun K => ∑ s ∈ range K, olverT a b c d w₀ (N + s)

/-- **Olver (5.01)–(5.02)**: when `w_N/p_N → 0` the series `E_N` converges (to `w_N/p_N`) and the
truncation error is `wₙ − wₙ^{(N)} = E_N pₙ` for `n ≤ N`. -/
theorem olver_5_01 (ha : ∀ n, 1 ≤ n → a n ≠ 0) {w : ℕ → ℂ} (hw : IsRec3Inh a b c d w)
    (hp : ∀ n, 1 ≤ n → olverP a b c n ≠ 0)
    (hwp : Tendsto (fun N => w N / olverP a b c N) atTop (𝓝 0)) {N : ℕ} (hN : 1 ≤ N) :
    Tendsto (fun K => ∑ s ∈ range K, olverT a b c d (w 0) (N + s)) atTop
        (𝓝 (olverTrunc a b c d (w 0) N)) ∧
      olverTrunc a b c d (w 0) N = w N / olverP a b c N ∧
      ∀ n, n ≤ N →
        w n - olverW a b c d (w 0) N n = olverTrunc a b c d (w 0) N * olverP a b c n := by
  have hs := olver_series ha hw hp hwp hN
  have he : olverTrunc a b c d (w 0) N = w N / olverP a b c N := hs.limUnder_eq
  refine ⟨he ▸ hs, he, fun n hn => ?_⟩
  rw [he, olver_error ha hw hN (fun k h1 _ => hp k h1) hn]
  ring

/-- **Olver (5.03)**: `wₙ = pₙ ∑_{s≥n} eₛ/(pₛ p_{s+1})`, `n ≥ 1`. -/
theorem olver_5_03 (ha : ∀ n, 1 ≤ n → a n ≠ 0) {w : ℕ → ℂ} (hw : IsRec3Inh a b c d w)
    (hp : ∀ n, 1 ≤ n → olverP a b c n ≠ 0)
    (hwp : Tendsto (fun N => w N / olverP a b c N) atTop (𝓝 0)) {n : ℕ} (hn : 1 ≤ n) :
    Tendsto (fun K => olverP a b c n * ∑ s ∈ range K, olverT a b c d (w 0) (n + s)) atTop
      (𝓝 (w n)) := by
  have := (olver_series ha hw hp hwp hn).const_mul (olverP a b c n)
  rwa [mul_div_cancel₀ _ (hp n hn)] at this

/-- **Olver (5.04)**: `wₙ^{(N)} = pₙ ∑_{s=n}^{N−1} eₛ/(pₛ p_{s+1})`, `1 ≤ n ≤ N` (exact, no
convergence needed): the whole computing scheme approximates the series (5.03) by its partial
sums. -/
theorem olver_5_04 (ha : ∀ n, 1 ≤ n → a n ≠ 0) {w : ℕ → ℂ} (hw : IsRec3Inh a b c d w) {N : ℕ}
    (hN : 1 ≤ N) (hp : ∀ n, 1 ≤ n → n ≤ N → olverP a b c n ≠ 0) {n : ℕ} (hn1 : 1 ≤ n)
    (hn : n ≤ N) :
    olverW a b c d (w 0) N n = olverP a b c n * ∑ s ∈ Ico n N, olverT a b c d (w 0) s := by
  -- the partial sums telescope within `1, …, N`
  have htel : ∀ K, n + K ≤ N → ∑ k ∈ range K, olverT a b c d (w 0) (n + k) =
      w n / olverP a b c n - w (n + K) / olverP a b c (n + K) := by
    intro K
    induction K with
    | zero => intro _; simp
    | succ K ih =>
      intro hK
      rw [sum_range_succ, ih (by omega), olverT,
        ← olver_div_sub ha hw (hp _ (by omega) (by omega)) (hp _ (by omega) (by omega))]
      ring_nf
  rw [sum_Ico_eq_sum_range, htel (N - n) (by omega), show n + (N - n) = N by omega,
    olverW_eq ha hw hN hp hn]
  have := hp n hn1 hn
  field_simp

/-! ### Rounding errors: Olver §7 -/

/-- **Olver (7.01)**: `pₙ = (f₀gₙ − g₀fₙ)/(f₀g₁ − g₀f₁)` for independent solutions `f`, `g` of
3.6.3. -/
theorem olver_7_01 (ha : ∀ n, 1 ≤ n → a n ≠ 0) {f g : ℕ → ℂ} (hf : IsRec3 a b c f)
    (hg : IsRec3 a b c g) (hC : casoratian f g 0 ≠ 0) (n : ℕ) :
    olverP a b c n = (f 0 * g n - g 0 * f n) / (f 0 * g 1 - g 0 * f 1) := by
  have hC' : f 0 * g 1 - g 0 * f 1 ≠ 0 := by
    intro h; apply hC; simp only [casoratian, zero_add]; linear_combination h
  have hsol : IsRec3 a b c fun n => (f 0 * g n - g 0 * f n) / (f 0 * g 1 - g 0 * f 1) :=
    fun n hn => by
      simp only
      field_simp
      linear_combination f 0 * hg n hn - g 0 * hf n hn
  exact congrFun ((olverP_isRec3 ha).eq_of_eq ha hsol
    (by rw [olverP_zero, show f 0 * g 0 - g 0 * f 0 = 0 by ring, zero_div])
    (by rw [olverP_one, div_self hC'])) n

/-- `pₙ` ultimately becomes proportional to `gₙ`: `pₙ/gₙ → f₀/(f₀g₁ − g₀f₁) ≠ 0` when
`fₙ/gₙ → 0`. -/
theorem olverP_div_tendsto (ha : ∀ n, 1 ≤ n → a n ≠ 0) {f g : ℕ → ℂ} (hf : IsRec3 a b c f)
    (hg : IsRec3 a b c g) (hC : casoratian f g 0 ≠ 0) (hgN : ∀ᶠ n in atTop, g n ≠ 0)
    (hfg : Tendsto (fun n => f n / g n) atTop (𝓝 0)) :
    Tendsto (fun n => olverP a b c n / g n) atTop (𝓝 (f 0 / (f 0 * g 1 - g 0 * f 1))) := by
  have hC' : f 0 * g 1 - g 0 * f 1 ≠ 0 := by
    intro h; apply hC; simp only [casoratian, zero_add]; linear_combination h
  have h : Tendsto (fun n => (f 0 - g 0 * (f n / g n)) / (f 0 * g 1 - g 0 * f 1)) atTop
      (𝓝 ((f 0 - g 0 * 0) / (f 0 * g 1 - g 0 * f 1))) :=
    (tendsto_const_nhds.sub (hfg.const_mul _)).div_const _
  rw [mul_zero, sub_zero] at h
  refine h.congr' ?_
  filter_upwards [hgN] with n hn
  rw [olver_7_01 ha hf hg hC]
  field_simp

/-- **Olver (7.02)**: a change `δk` in the normalizing value `w₀` changes the wanted solution by
`(fₙ/f₀) δk`; the problem is ill-posed when `|f₀|` is small compared with `|g₀ fₙ/gₙ|`. -/
theorem olver_7_02 (ha : ∀ n, 1 ≤ n → a n ≠ 0) {f g w w' : ℕ → ℂ} (hf : IsRec3 a b c f)
    (hg : IsRec3 a b c g) (hf0 : f 0 ≠ 0) (hgN : ∀ᶠ n in atTop, g n ≠ 0)
    (hfg : Tendsto (fun n => f n / g n) atTop (𝓝 0)) (hw : IsRec3Inh a b c d w)
    (hwg : Tendsto (fun n => w n / g n) atTop (𝓝 0)) (hw' : IsRec3Inh a b c d w')
    (hw'g : Tendsto (fun n => w' n / g n) atTop (𝓝 0)) (n : ℕ) :
    w' n - w n = f n / f 0 * (w' 0 - w 0) := by
  have hv : IsRec3 a b c fun n => w' n - w n := hw'.sub hw
  by_cases h0 : (fun n => w' n - w n) = (0 : ℕ → ℂ)
  · have h1 : w' n - w n = 0 := congrFun h0 n
    have h2 : w' 0 - w 0 = 0 := congrFun h0 0
    rw [h1, h2, mul_zero]
  have hvg : Tendsto (fun n => (w' n - w n) / g n) atTop (𝓝 (0 - 0)) := by
    refine (hw'g.sub hwg).congr' ?_
    filter_upwards [hgN] with n hn
    rw [sub_div]
  rw [sub_zero] at hvg
  obtain ⟨k, hk⟩ := dlmf_3_6_4_unique ha
    ⟨hf, fun h => hf0 (by simp [h]), g, hg, hgN, hfg⟩ ⟨hv, h0, g, hg, hgN, hvg⟩
  have hk0 : w' 0 - w 0 = k * f 0 := congrFun hk 0
  have hkn : w' n - w n = k * f n := congrFun hk n
  rw [hkn, hk0]
  field_simp

/-- **Olver §7**, propagation in the back substitution: a rounding error `δ` introduced in
`wₛ^{(N)}` is multiplied by `pᵣ/pₛ` when transmitted to `wᵣ^{(N)}`, `r ≤ s`: if `u`, `v` both
satisfy 3.6.10 for `r < s`, then `pₛ (uᵣ − vᵣ) = pᵣ (uₛ − vₛ)`. -/
theorem olver_backsub_propagation {p e u v : ℕ → ℂ} {s : ℕ} (hp : ∀ r, 1 ≤ r → r ≤ s → p r ≠ 0)
    (hu : ∀ r, r < s → p (r + 1) * u r = p r * u (r + 1) + e r)
    (hv : ∀ r, r < s → p (r + 1) * v r = p r * v (r + 1) + e r) {r : ℕ} (hr : r ≤ s) :
    p s * (u r - v r) = p r * (u s - v s) := by
  obtain ⟨k, hk, rfl⟩ : ∃ k, k ≤ s ∧ r = s - k := ⟨s - r, by omega, by omega⟩
  clear hr
  induction k with
  | zero => simp
  | succ k ih =>
    have ih := ih (by omega)
    have h1 := hu (s - (k + 1)) (by omega)
    have h2 := hv (s - (k + 1)) (by omega)
    rw [show s - (k + 1) + 1 = s - k by omega] at h1 h2
    have hpk := hp (s - k) (by omega) (by omega)
    apply mul_left_cancel₀ hpk
    linear_combination p s * h1 - p s * h2 + p (s - (k + 1)) * ih

/-! ### What the DLMF criterion 3.6.9 guarantees -/

/-- Under 3.6.9, one more step `N → N + 1` changes `wₙ^{(N)}` by at most
`ε |pₙ| min_{1≤m≤M} |eₘ/(pₘp_{m+1})|`, `n ≤ N`. -/
theorem dlmf_3_6_9_one_step (ha : ∀ n, 1 ≤ n → a n ≠ 0) {w : ℕ → ℂ} (hw : IsRec3Inh a b c d w)
    {N : ℕ} (hN : 1 ≤ N) (hp : ∀ n, 1 ≤ n → n ≤ N + 1 → olverP a b c n ≠ 0) {M : ℕ}
    (hM : 1 ≤ M) {ε : ℝ}
    (h369 : ‖olverT a b c d (w 0) N‖ ≤
      ε * (Finset.Icc 1 M).inf' ⟨1, Finset.mem_Icc.mpr ⟨le_rfl, hM⟩⟩
        (fun m => ‖olverT a b c d (w 0) m‖)) {n : ℕ} (hn : n ≤ N) :
    ‖olverW a b c d (w 0) (N + 1) n - olverW a b c d (w 0) N n‖ ≤
      ε * ‖olverP a b c n‖ * (Finset.Icc 1 M).inf' ⟨1, Finset.mem_Icc.mpr ⟨le_rfl, hM⟩⟩
        (fun m => ‖olverT a b c d (w 0) m‖) := by
  rw [olver_4_10 ha hw hN hp hn, norm_mul]
  calc ‖olverP a b c n‖ * ‖olverT a b c d (w 0) N‖
      ≤ ‖olverP a b c n‖ * (ε * _) := by gcongr
    _ = _ := by ring

/-- When the terms `eₛ/(pₛp_{s+1})` are nonnegative reals (no cancellation in the series (5.04)),
3.6.9 guarantees that the step `N → N + 1` changes `wₙ^{(N)}` by at most the relative amount `ε`,
for `1 ≤ n ≤ min(M, N − 1)`. -/
theorem dlmf_3_6_9_relative (ha : ∀ n, 1 ≤ n → a n ≠ 0) {w : ℕ → ℂ} (hw : IsRec3Inh a b c d w)
    {N : ℕ} (hN : 1 ≤ N) (hp : ∀ n, 1 ≤ n → n ≤ N + 1 → olverP a b c n ≠ 0)
    (hpos : ∀ s, 1 ≤ s → s < N → ∃ t : ℝ, 0 ≤ t ∧ olverT a b c d (w 0) s = t) {M : ℕ}
    (hM : 1 ≤ M) {ε : ℝ} (hε : 0 ≤ ε)
    (h369 : ‖olverT a b c d (w 0) N‖ ≤
      ε * (Finset.Icc 1 M).inf' ⟨1, Finset.mem_Icc.mpr ⟨le_rfl, hM⟩⟩
        (fun m => ‖olverT a b c d (w 0) m‖)) {n : ℕ} (hn1 : 1 ≤ n) (hnM : n ≤ M) (hn : n < N) :
    ‖olverW a b c d (w 0) (N + 1) n - olverW a b c d (w 0) N n‖ ≤
      ε * ‖olverW a b c d (w 0) N n‖ := by
  refine (dlmf_3_6_9_one_step ha hw hN hp hM h369 hn.le).trans ?_
  rw [mul_assoc]
  gcongr
  -- `|wₙ^{(N)}| = |pₙ| ∑_{s=n}^{N−1} tₛ ≥ |pₙ| tₙ ≥ |pₙ| min`
  rw [olver_5_04 ha hw hN (fun k h1 h2 => hp k h1 (by omega)) hn1 hn.le, norm_mul]
  gcongr
  choose t ht using hpos
  have hsum : ∑ s ∈ Ico n N, olverT a b c d (w 0) s =
      ((∑ s ∈ (Ico n N).attach, t s.1 (le_trans hn1 (mem_Ico.mp s.2).1)
        (mem_Ico.mp s.2).2 : ℝ) : ℂ) := by
    rw [← sum_attach (Ico n N)]
    push_cast
    refine sum_congr rfl fun s _ => ?_
    exact (ht s.1 _ _).2
  rw [hsum, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sum_nonneg fun s _ => (ht _ _ _).1)]
  calc (Finset.Icc 1 M).inf' _ (fun m => ‖olverT a b c d (w 0) m‖)
      ≤ ‖olverT a b c d (w 0) n‖ := inf'_le _ (Finset.mem_Icc.mpr ⟨hn1, hnM⟩)
    _ = t n hn1 hn := by
        rw [(ht n hn1 hn).2, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (ht n hn1 hn).1]
    _ ≤ _ := single_le_sum (f := fun s : Ico n N => t s.1 (le_trans hn1 (mem_Ico.mp s.2).1)
        (mem_Ico.mp s.2).2) (fun s _ => (ht _ _ _).1)
        (mem_attach _ (⟨n, mem_Ico.mpr ⟨le_rfl, hn⟩⟩ : Ico n N))

end Azurite.DLMF
