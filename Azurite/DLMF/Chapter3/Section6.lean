/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter2.Section9Recessive
import Mathlib.Algebra.Group.ForwardDiff

/-!
# DLMF §3.6(i)–(ii): linear difference equations, homogeneous equations

**§3.6(i)**: 3.6.1 (`diffLHS`, `n ∈ ℤ`) and its equivalent form **3.6.2** with the forward
difference `Δ` (`dlmf_3_6_2`, `dlmf_3_6_1_iff_3_6_2`, Mathlib `fwdDiff`); homogeneous if `dₙ = 0`
for all `n` (`IsHomogeneousDiff`). "Problems of severe instability" are made precise in §3.6(ii).

**§3.6(ii)**, the homogeneous equation **3.6.3** (`IsRec3`, `n ≥ 1`):
* with `aₙ ≠ 0` the solution with given `w₀`, `w₁` is computed recursively (`fwdRec`) and is
  unique (`dlmf_3_6_3_forward`, `IsRec3.eq_of_eq`); the solutions form a two-dimensional space
  (`IsRec3.eq_comb`, Casoratian `casoratian` of §2.9).
* Rounding errors perturb `wₙ` by multiples of an independent solution `gₙ`: harmless when `wₙ`
  grows at least as fast (`dlmf_3_6_ii_forward_stable`), unbounded relative error when `w` is
  recessive (`dlmf_3_6_ii_forward_unstable`).
* **3.6.4**: recessive (minimal, distinguished) solutions (`IsRecessive`, `IsRecessiveWrt`); such
  `w` is independent of `g` (`casoratian_ne_zero_of_recessive`) and "unique except for a constant
  factor" (`dlmf_3_6_4_unique`).
* Backward recursion with `cₙ ≠ 0` from `w_N`, `w_{N+1}` (`bwdRec`, `dlmf_3_6_3_backward`:
  existence and uniqueness of `w_{N−1}, …, w₀`); its stability: an unwanted multiple of `g` of
  relative size `δ` at `N` (`bwdPerturbed`, `bwdPerturbed_start`) has relative size `→ 0` at every
  fixed `n` as `N → ∞` (`dlmf_3_6_ii_backward_stable`).

Not formalized: the pointers to asymptotic starting values (§2.9) and to §§3.6(iii), 3.6(v).
-/

open Filter Topology fwdDiff

namespace Azurite.DLMF

/-! ### §3.6(i) -/

/-- The left side `aₙ w_{n+1} − bₙ wₙ + cₙ w_{n−1}` of 3.6.1, `n ∈ ℤ`. -/
def diffLHS (a b c w : ℤ → ℂ) (n : ℤ) : ℂ := a n * w (n + 1) - b n * w n + c n * w (n - 1)

/-- **DLMF 3.6.2**: `aₙ Δ²w_{n−1} + (2aₙ − bₙ) Δw_{n−1} + (aₙ − bₙ + cₙ) w_{n−1}` equals the left
side of 3.6.1 (`Δw_{n−1} = wₙ − w_{n−1}`, `Δ²w_{n−1} = Δwₙ − Δw_{n−1}`). -/
theorem dlmf_3_6_2 (a b c w : ℤ → ℂ) (n : ℤ) :
    a n * Δ_[1] (Δ_[1] w) (n - 1) + (2 * a n - b n) * Δ_[1] w (n - 1) +
      (a n - b n + c n) * w (n - 1) = diffLHS a b c w n := by
  simp only [fwdDiff, diffLHS, sub_add_cancel]
  ring

/-- 3.6.1 and 3.6.2 are equivalent. -/
theorem dlmf_3_6_1_iff_3_6_2 (a b c d w : ℤ → ℂ) :
    (∀ n, diffLHS a b c w n = d n) ↔ ∀ n, a n * Δ_[1] (Δ_[1] w) (n - 1) +
      (2 * a n - b n) * Δ_[1] w (n - 1) + (a n - b n + c n) * w (n - 1) = d n := by
  simp only [dlmf_3_6_2]

/-- The difference equation is homogeneous if `dₙ = 0` for all `n`. -/
def IsHomogeneousDiff (d : ℤ → ℂ) : Prop := ∀ n, d n = 0

/-! ### §3.6(ii): 3.6.3 and forward recursion -/

/-- `w` solves **DLMF 3.6.3** `aₙ w_{n+1} − bₙ wₙ + cₙ w_{n−1} = 0` for `n ≥ 1`. -/
def IsRec3 (a b c w : ℕ → ℂ) : Prop :=
  ∀ n, 1 ≤ n → a n * w (n + 1) - b n * w n + c n * w (n - 1) = 0

theorem IsRec3.shift {a b c w : ℕ → ℂ} (h : IsRec3 a b c w) (m : ℕ) :
    a (m + 1) * w (m + 2) - b (m + 1) * w (m + 1) + c (m + 1) * w m = 0 := by
  simpa using h (m + 1) (by omega)

theorem isRec3_of_shift {a b c w : ℕ → ℂ}
    (h : ∀ m, a (m + 1) * w (m + 2) - b (m + 1) * w (m + 1) + c (m + 1) * w m = 0) :
    IsRec3 a b c w := fun n hn => by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hn
  simpa using h m

theorem IsRec3.add {a b c v w : ℕ → ℂ} (hv : IsRec3 a b c v) (hw : IsRec3 a b c w) :
    IsRec3 a b c (v + w) := fun n hn => by
  simp only [Pi.add_apply]; linear_combination hv n hn + hw n hn

theorem IsRec3.const_mul {a b c w : ℕ → ℂ} (hw : IsRec3 a b c w) (k : ℂ) :
    IsRec3 a b c (fun n => k * w n) := fun n hn => by
  linear_combination k * hw n hn

/-- Forward recursion `w_{n+1} = (bₙ wₙ − cₙ w_{n−1})/aₙ`: the pairs `(wₙ, w_{n+1})`. -/
noncomputable def fwdRecPair (a b c : ℕ → ℂ) (w₀ w₁ : ℂ) : ℕ → ℂ × ℂ
  | 0 => (w₀, w₁)
  | m + 1 => ((fwdRecPair a b c w₀ w₁ m).2,
      (b (m + 1) * (fwdRecPair a b c w₀ w₁ m).2 - c (m + 1) * (fwdRecPair a b c w₀ w₁ m).1) /
        a (m + 1))

/-- The solution of 3.6.3 computed recursively from `w₀`, `w₁` for `n = 2, 3, …`. -/
noncomputable def fwdRec (a b c : ℕ → ℂ) (w₀ w₁ : ℂ) (n : ℕ) : ℂ := (fwdRecPair a b c w₀ w₁ n).1

theorem fwdRecPair_snd (a b c : ℕ → ℂ) (w₀ w₁ : ℂ) (n : ℕ) :
    (fwdRecPair a b c w₀ w₁ n).2 = fwdRec a b c w₀ w₁ (n + 1) := by
  simp [fwdRec, fwdRecPair]

/-- **DLMF §3.6(ii)**: with `aₙ ≠ 0`, the solution of 3.6.3 with given `w₀`, `w₁` is computed
recursively for `n = 2, 3, …` (`fwdRec`), and it is the only one. -/
theorem dlmf_3_6_3_forward {a b c : ℕ → ℂ} (ha : ∀ n, 1 ≤ n → a n ≠ 0) (w₀ w₁ : ℂ) :
    IsRec3 a b c (fwdRec a b c w₀ w₁) ∧ fwdRec a b c w₀ w₁ 0 = w₀ ∧
      fwdRec a b c w₀ w₁ 1 = w₁ ∧
      ∀ v, IsRec3 a b c v → v 0 = w₀ → v 1 = w₁ → v = fwdRec a b c w₀ w₁ := by
  refine ⟨isRec3_of_shift fun m => ?_, rfl, rfl, fun v hv h0 h1 => ?_⟩
  · have hm := ha (m + 1) (by omega)
    simp only [fwdRec, fwdRecPair]
    field_simp
    ring
  · have key : ∀ m, v m = (fwdRecPair a b c w₀ w₁ m).1 ∧
        v (m + 1) = (fwdRecPair a b c w₀ w₁ m).2 := by
      intro m
      induction m with
      | zero => exact ⟨h0, h1⟩
      | succ m ih =>
        refine ⟨ih.2, ?_⟩
        have hm := ha (m + 1) (by omega)
        have e := hv.shift m
        rw [ih.1, ih.2] at e
        simp only [fwdRecPair]
        rw [show m + 1 + 1 = m + 2 by rfl]
        field_simp
        linear_combination e
    exact funext fun m => (key m).1

/-- Uniqueness for 3.6.3 given two consecutive values (forward). -/
theorem IsRec3.eq_of_eq {a b c v w : ℕ → ℂ} (ha : ∀ n, 1 ≤ n → a n ≠ 0) (hv : IsRec3 a b c v)
    (hw : IsRec3 a b c w) (h0 : v 0 = w 0) (h1 : v 1 = w 1) : v = w := by
  exact ((dlmf_3_6_3_forward ha (w 0) (w 1)).2.2.2 v hv h0 h1).trans
    ((dlmf_3_6_3_forward ha (w 0) (w 1)).2.2.2 w hw rfl rfl).symm

/-- The solutions of 3.6.3 form a two-dimensional space: two solutions with nonzero Casoratian
`w₀g₁ − w₁g₀` span all solutions. -/
theorem IsRec3.eq_comb {a b c w g v : ℕ → ℂ} (ha : ∀ n, 1 ≤ n → a n ≠ 0) (hw : IsRec3 a b c w)
    (hg : IsRec3 a b c g) (hv : IsRec3 a b c v) (hC : casoratian w g 0 ≠ 0) :
    ∃ α β : ℂ, v = fun n => α * w n + β * g n := by
  refine ⟨(v 0 * g 1 - v 1 * g 0) / casoratian w g 0,
    (w 0 * v 1 - w 1 * v 0) / casoratian w g 0, ?_⟩
  simp only [casoratian, zero_add] at hC ⊢
  refine hv.eq_of_eq ha ((hw.const_mul _).add (hg.const_mul _)) ?_ ?_ <;>
  · show _ = _ + _
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, eq_div_iff hC]
    ring

/-! ### Recessive (minimal, distinguished) solutions -/

/-- 3.6.4 relative to `g`: `g` is eventually nonzero and `wₙ/gₙ → 0` as `n → ∞`. -/
def IsRecessiveWrt (w g : ℕ → ℂ) : Prop :=
  (∀ᶠ n in atTop, g n ≠ 0) ∧ Tendsto (fun n => w n / g n) atTop (𝓝 0)

/-- **DLMF 3.6.4**: a nontrivial solution `w` of 3.6.3 is *recessive* (minimal, distinguished) as
`n → ∞` if `wₙ/gₙ → 0` for a solution `gₙ`. -/
def IsRecessive (a b c w : ℕ → ℂ) : Prop :=
  IsRec3 a b c w ∧ w ≠ 0 ∧ ∃ g, IsRec3 a b c g ∧ IsRecessiveWrt w g

/-- A nontrivial solution that is recessive relative to `g` is independent of `g`. -/
theorem casoratian_ne_zero_of_recessive {a b c w g : ℕ → ℂ} (ha : ∀ n, 1 ≤ n → a n ≠ 0)
    (hw : IsRec3 a b c w) (hw0 : w ≠ 0) (hg : IsRec3 a b c g) (hr : IsRecessiveWrt w g) :
    casoratian w g 0 ≠ 0 := by
  intro hC
  simp only [casoratian, zero_add] at hC
  obtain ⟨hgN, hwg⟩ := hr
  -- `w = λ g`
  obtain ⟨l, hl0, hl1⟩ : ∃ l : ℂ, w 0 = l * g 0 ∧ w 1 = l * g 1 := by
    by_cases h0 : g 0 = 0
    · by_cases h1 : g 1 = 0
      · exfalso
        have hz : g = 0 := hg.eq_of_eq ha (fun n _ => by simp) (by simp [h0]) (by simp [h1])
        obtain ⟨n, hn⟩ := hgN.exists
        exact hn (by simp [hz])
      · refine ⟨w 1 / g 1, ?_, by field_simp⟩
        rw [h0, mul_zero]
        have : w 0 * g 1 = 0 := by rw [h0, mul_zero] at hC; linear_combination hC
        exact (mul_eq_zero.mp this).resolve_right h1
    · refine ⟨w 0 / g 0, by field_simp, ?_⟩
      field_simp
      linear_combination -hC
  have hwl : w = fun n => l * g n :=
    hw.eq_of_eq ha (hg.const_mul l) hl0 hl1
  have hlim : Tendsto (fun n => w n / g n) atTop (𝓝 l) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hgN] with n hn
    rw [hwl]; field_simp
  have hl : l = 0 := tendsto_nhds_unique hlim hwg
  exact hw0 (by rw [hwl, hl]; ext n; simp)

/-- **DLMF §3.6(ii)**: a recessive solution "is unique except for a constant factor". -/
theorem dlmf_3_6_4_unique {a b c w v : ℕ → ℂ} (ha : ∀ n, 1 ≤ n → a n ≠ 0)
    (hw : IsRecessive a b c w) (hv : IsRecessive a b c v) : ∃ k : ℂ, v = fun n => k * w n := by
  obtain ⟨hw, hw0, g, hg, hgN, hwg⟩ := hw
  obtain ⟨hv, -, h, hh, hhN, hvh⟩ := hv
  have hC := casoratian_ne_zero_of_recessive ha hw hw0 hg ⟨hgN, hwg⟩
  obtain ⟨α, β, rfl⟩ := IsRec3.eq_comb ha hw hg hv hC
  obtain ⟨γ, δ, rfl⟩ := IsRec3.eq_comb ha hw hg hh hC
  by_cases hβ : β = 0
  · exact ⟨α, by ext n; simp [hβ]⟩
  exfalso
  by_cases hδ : δ = 0
  · -- `h = γ w`: then `g/w` is unbounded, but `β g/w = γ (v/h) − α` converges
    subst hδ
    simp only [zero_mul, add_zero] at hhN hvh
    have hγ : γ ≠ 0 := by
      obtain ⟨n, hn⟩ := hhN.exists
      exact left_ne_zero_of_mul hn
    have hwN : ∀ᶠ n in atTop, w n ≠ 0 := hhN.mono fun n hn => right_ne_zero_of_mul hn
    have hr : Tendsto (fun n => w n / g n) atTop (𝓝[≠] 0) :=
      tendsto_nhdsWithin_iff.mpr ⟨hwg, (hwN.and hgN).mono fun n hn => div_ne_zero hn.1 hn.2⟩
    have h1 : Tendsto (fun n => ‖β / γ‖ * ‖(w n / g n)⁻¹‖) atTop atTop :=
      (tendsto_norm_inv_nhdsNE_zero_atTop.comp hr).const_mul_atTop
        (norm_pos_iff.mpr (div_ne_zero hβ hγ))
    have h2 : Tendsto (fun n => ‖β / γ‖ * ‖(w n / g n)⁻¹‖) atTop (𝓝 ‖0 - α / γ‖) := by
      refine (((hvh.sub_const (α / γ))).norm).congr' ?_
      filter_upwards [hwN, hgN] with n hn1 hn2
      rw [← norm_mul, inv_div]
      congr 1
      field_simp
      ring
    exact not_tendsto_atTop_of_tendsto_nhds h2 h1
  · -- `v/h → β/δ ≠ 0`
    have hlim : Tendsto (fun n => (α * (w n / g n) + β) / (γ * (w n / g n) + δ)) atTop
        (𝓝 ((α * 0 + β) / (γ * 0 + δ))) :=
      ((hwg.const_mul α).add_const β).div ((hwg.const_mul γ).add_const δ) (by simpa using hδ)
    have hlim' : Tendsto (fun n => (α * w n + β * g n) / (γ * w n + δ * g n)) atTop
        (𝓝 (β / δ)) := by
      simp only [mul_zero, zero_add] at hlim
      refine hlim.congr' ?_
      filter_upwards [hgN] with n hn
      field_simp
    exact div_ne_zero hβ hδ (tendsto_nhds_unique hlim' hvh)

/-- **DLMF §3.6(ii)**, instability of forward recursion: rounding perturbs a recessive `w` by a
multiple `ε g` of the solution `g`, and the relative error `ε gₙ/wₙ` grows without bound. -/
theorem dlmf_3_6_ii_forward_unstable {w g : ℕ → ℂ} (hr : IsRecessiveWrt w g)
    (hwN : ∀ᶠ n in atTop, w n ≠ 0) {ε : ℂ} (hε : ε ≠ 0) :
    Tendsto (fun n => ‖((w n + ε * g n) - w n) / w n‖) atTop atTop := by
  have hr' : Tendsto (fun n => w n / g n) atTop (𝓝[≠] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨hr.2, (hwN.and hr.1).mono fun n hn => div_ne_zero hn.1 hn.2⟩
  refine ((tendsto_norm_inv_nhdsNE_zero_atTop.comp hr').const_mul_atTop
    (norm_pos_iff.mpr hε)).congr' ?_
  filter_upwards [hwN] with n hn
  simp only [Function.comp, add_sub_cancel_left, inv_div, ← norm_mul]
  congr 1
  field_simp

/-- **DLMF §3.6(ii)**: "of little consequence if the wanted solution is growing in magnitude at
least as fast as any other solution": if `|gₙ/wₙ| ≤ M` then the relative error stays `≤ |ε| M`. -/
theorem dlmf_3_6_ii_forward_stable {w g : ℕ → ℂ} {M : ℝ} (hM : ∀ n, ‖g n / w n‖ ≤ M)
    (ε : ℂ) (n : ℕ) :
    ‖((w n + ε * g n) - w n) / w n‖ ≤ ‖ε‖ * M := by
  rw [add_sub_cancel_left, mul_div_assoc, norm_mul]
  exact mul_le_mul_of_nonneg_left (hM n) (norm_nonneg _)

/-! ### Backward recursion -/

/-- Backward recursion `w_{n−1} = (bₙ wₙ − aₙ w_{n+1})/cₙ` from `w_N = x`, `w_{N+1} = y`: after
`k` steps, the pair `(w_{N+1−k}, w_{N−k})`. -/
noncomputable def bwdRecPair (a b c : ℕ → ℂ) (N : ℕ) (x y : ℂ) : ℕ → ℂ × ℂ
  | 0 => (y, x)
  | k + 1 => ((bwdRecPair a b c N x y k).2,
      (b (N - k) * (bwdRecPair a b c N x y k).2 - a (N - k) * (bwdRecPair a b c N x y k).1) /
        c (N - k))

/-- The values `w_{N+1}, w_N, w_{N−1}, …, w₀` generated by backward recursion. -/
noncomputable def bwdRec (a b c : ℕ → ℂ) (N : ℕ) (x y : ℂ) (n : ℕ) : ℂ :=
  (bwdRecPair a b c N x y (N + 1 - n)).1

/-- **DLMF §3.6(ii)**, backward recursion: with `cₙ ≠ 0`, starting from `w_N` and `w_{N+1}`,
3.6.3 generates `w_{N−1}, w_{N−2}, …, w₀` (`bwdRec`), uniquely. -/
theorem dlmf_3_6_3_backward {a b c : ℕ → ℂ} (hc : ∀ n, 1 ≤ n → c n ≠ 0) (N : ℕ) (x y : ℂ) :
    bwdRec a b c N x y N = x ∧ bwdRec a b c N x y (N + 1) = y ∧
      (∀ n, 1 ≤ n → n ≤ N → a n * bwdRec a b c N x y (n + 1) - b n * bwdRec a b c N x y n +
        c n * bwdRec a b c N x y (n - 1) = 0) ∧
      ∀ v : ℕ → ℂ, (∀ n, 1 ≤ n → n ≤ N → a n * v (n + 1) - b n * v n + c n * v (n - 1) = 0) →
        v N = x → v (N + 1) = y → ∀ n, n ≤ N + 1 → v n = bwdRec a b c N x y n := by
  have hpair : ∀ k n, n + k = N + 1 → (bwdRecPair a b c N x y k).1 = bwdRec a b c N x y n := by
    intro k n hk; unfold bwdRec; congr; omega
  refine ⟨by simp [bwdRec, bwdRecPair, show N + 1 - N = 1 by omega],
    by simp [bwdRec, bwdRecPair], fun n hn1 hnN => ?_, fun v hv hx hy => ?_⟩
  · obtain ⟨k, rfl⟩ : ∃ k, N = n + k := ⟨N - n, by omega⟩
    have h0 := hpair k (n + 1) (by omega)
    have h1 := hpair (k + 1) n (by omega)
    have h2 := hpair (k + 2) (n - 1) (by omega)
    rw [← h0, ← h1, ← h2]
    have hn := hc n hn1
    simp only [bwdRecPair, show n + k - k = n by omega]
    field_simp
    ring
  · have key : ∀ k, k ≤ N → v (N + 1 - k) = (bwdRecPair a b c N x y k).1 ∧
        v (N - k) = (bwdRecPair a b c N x y k).2 := by
      intro k
      induction k with
      | zero => intro _; simp [bwdRecPair, hx, hy]
      | succ k ih =>
        intro hk
        obtain ⟨ih1, ih2⟩ := ih (by omega)
        refine ⟨by rw [show N + 1 - (k + 1) = N - k by omega]; exact ih2, ?_⟩
        have e := hv (N - k) (by omega) (by omega)
        rw [show N - k + 1 = N + 1 - k by omega, ih1, ih2, show N - k - 1 = N - (k + 1) by omega]
          at e
        have hn := hc (N - k) (by omega)
        simp only [bwdRecPair]
        field_simp
        linear_combination e
    intro n hn
    rw [← hpair (N + 1 - n) n (by omega)]
    by_cases h : N + 1 - n ≤ N
    · have := (key _ h).1
      rwa [show N + 1 - (N + 1 - n) = n by omega] at this
    · have hn0 : n = 0 := by omega
      subst hn0
      have := (key N le_rfl).2
      simp only [Nat.sub_self] at this
      simpa [bwdRecPair] using this

/-- The solution `w + η_N g` whose value at `N` has relative error `δ` in the direction of `g`:
`η_N = δ w_N/g_N`. -/
noncomputable def bwdPerturbed (w g : ℕ → ℂ) (δ : ℂ) (N n : ℕ) : ℂ :=
  w n + δ * w N / g N * g n

theorem bwdPerturbed_isRec3 {a b c w g : ℕ → ℂ} (hw : IsRec3 a b c w) (hg : IsRec3 a b c g)
    (δ : ℂ) (N : ℕ) : IsRec3 a b c (bwdPerturbed w g δ N) :=
  hw.add (hg.const_mul (δ * w N / g N))

theorem bwdPerturbed_start {w g : ℕ → ℂ} (δ : ℂ) {N : ℕ} (hg : g N ≠ 0) :
    bwdPerturbed w g δ N N - w N = δ * w N := by
  unfold bwdPerturbed; field_simp; ring

/-- **DLMF §3.6(ii)**, stability of backward recursion: if `w` is recessive relative to `g`, an
unwanted multiple of `g` of relative size `δ` at the starting index `N` has, at any fixed `n`,
relative size `δ (w_N/g_N)(gₙ/wₙ) → 0` as `N → ∞`: "the unwanted multiples of `gₙ` now decay in
comparison with `wₙ`". -/
theorem dlmf_3_6_ii_backward_stable {w g : ℕ → ℂ} (hr : IsRecessiveWrt w g) (δ : ℂ) (n : ℕ) :
    Tendsto (fun N => (bwdPerturbed w g δ N n - w n) / w n) atTop (𝓝 0) := by
  have h := (hr.2.const_mul δ).mul_const (g n / w n)
  simp only [mul_zero, zero_mul] at h
  refine h.congr fun N => ?_
  unfold bwdPerturbed
  ring

end Azurite.DLMF
