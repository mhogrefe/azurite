/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter3.Section6
import Azurite.DLMF.Chapter3.Section2Tridiag

/-!
# DLMF §3.6(iv): inhomogeneous equations

For 3.6.1 (`IsRec3Inh`, `aₙcₙ ≠ 0`): solutions differ by complementary functions (solutions of
3.6.3; `IsRec3Inh.add_hom`, `IsRec3Inh.sub`).

* "If … `wₙ` grows (decays) in magnitude at least as fast as any solution of the corresponding
  homogeneous equation, then forward (backward) recursion is stable":
  `dlmf_3_6_iv_forward_stable`, `dlmf_3_6_iv_backward_stable`.
* Under **3.6.6** (`fₙ/gₙ → 0`, `wₙ/gₙ → 0`) forward recursion is unstable
  (`dlmf_3_6_iv_forward_unstable`); if also `fₙ/wₙ → 0`, backward recursion is unstable
  (`dlmf_3_6_iv_backward_unstable`).
* The boundary-value method **3.6.7** (`IsBVSol`; as the tridiagonal system of §3.2(ii):
  `dlmf_3_6_7`, `tridiag_mulVec_row`): for large `N` it is solvable, and `wₙ^{(N)} → wₙ` as
  `N → ∞` with `n` fixed (`dlmf_3_6_iv_boundary`; the error is `−(w_N/h_N) hₙ` with the
  complementary function `hₙ = g₀fₙ − f₀gₙ`, `bvH`, `eq_mul_bvH_of_zero`). The wanted solution is
  determined by `w₀` and 3.6.6 (`dlmf_3_6_iv_wanted_unique`).

**Erratum**: DLMF calls `fₙ`, `gₙ` "two independent solutions … of the corresponding
inhomogeneous equation (the complementary functions)"; complementary functions are solutions of
the corresponding *homogeneous* equation, and that is what the results need (`IsRec3 a b c f`).
-/

open Filter Topology Finset

namespace Azurite.DLMF

/-- `w` solves the inhomogeneous equation **3.6.1** `aₙ w_{n+1} − bₙ wₙ + cₙ w_{n−1} = dₙ`,
`n ≥ 1`. -/
def IsRec3Inh (a b c d w : ℕ → ℂ) : Prop :=
  ∀ n, 1 ≤ n → a n * w (n + 1) - b n * w n + c n * w (n - 1) = d n

/-- A solution of 3.6.1 plus a complementary function is again a solution. -/
theorem IsRec3Inh.add_hom {a b c d w u : ℕ → ℂ} (hw : IsRec3Inh a b c d w)
    (hu : IsRec3 a b c u) : IsRec3Inh a b c d (fun n => w n + u n) := fun n hn => by
  linear_combination hw n hn + hu n hn

/-- The difference of two solutions of 3.6.1 is a complementary function. -/
theorem IsRec3Inh.sub {a b c d v w : ℕ → ℂ} (hv : IsRec3Inh a b c d v)
    (hw : IsRec3Inh a b c d w) : IsRec3 a b c (fun n => v n - w n) := fun n hn => by
  linear_combination hv n hn - hw n hn

/-! ### Stability and instability of recursion -/

/-- **DLMF §3.6(iv)**, forward recursion is stable if `wₙ` grows at least as fast as the
complementary function `fₙ` (`|fₙ/wₙ| ≤ M`): the perturbed solution `w + εf` has relative error
`≤ |ε| M`. -/
theorem dlmf_3_6_iv_forward_stable {a b c d w f : ℕ → ℂ} (hw : IsRec3Inh a b c d w)
    (hf : IsRec3 a b c f) {M : ℝ} (hM : ∀ n, ‖f n / w n‖ ≤ M) (ε : ℂ) :
    IsRec3Inh a b c d (fun n => w n + ε * f n) ∧
      ∀ n, ‖((w n + ε * f n) - w n) / w n‖ ≤ ‖ε‖ * M :=
  ⟨hw.add_hom (hf.const_mul ε), fun n => dlmf_3_6_ii_forward_stable hM ε n⟩

/-- **DLMF §3.6(iv)**, backward recursion is stable if `wₙ` decays at least as fast as `fₙ`
(`|w_N/f_N| ≤ M`): a multiple of `f` of relative size `δ` at the starting index `N` has relative
size `≤ |δ| M |fₙ/wₙ|` at `n`, uniformly in `N`. -/
theorem dlmf_3_6_iv_backward_stable {w f : ℕ → ℂ} {M : ℝ} (hM : ∀ N, ‖w N / f N‖ ≤ M) (δ : ℂ)
    (N n : ℕ) : ‖(bwdPerturbed w f δ N n - w n) / w n‖ ≤ ‖δ‖ * M * ‖f n / w n‖ := by
  have e : (bwdPerturbed w f δ N n - w n) / w n = δ * (w N / f N) * (f n / w n) := by
    unfold bwdPerturbed; ring
  rw [e, norm_mul, norm_mul]
  gcongr
  exact hM N

/-- **DLMF §3.6(iv)**: under 3.6.6 (`wₙ/gₙ → 0`) forward recursion is unstable. -/
theorem dlmf_3_6_iv_forward_unstable {w g : ℕ → ℂ} (hgN : ∀ᶠ n in atTop, g n ≠ 0)
    (hwg : Tendsto (fun n => w n / g n) atTop (𝓝 0)) (hwN : ∀ᶠ n in atTop, w n ≠ 0) {ε : ℂ}
    (hε : ε ≠ 0) : Tendsto (fun n => ‖((w n + ε * g n) - w n) / w n‖) atTop atTop :=
  dlmf_3_6_ii_forward_unstable ⟨hgN, hwg⟩ hwN hε

/-- **DLMF §3.6(iv)**: if also `fₙ/wₙ → 0`, backward recursion is unstable as well: a multiple of
`f` of relative size `δ ≠ 0` at the starting index `N` has relative size `→ ∞` at any fixed `n`
with `fₙ ≠ 0` as `N → ∞`. -/
theorem dlmf_3_6_iv_backward_unstable {w f : ℕ → ℂ} (hwN : ∀ᶠ n in atTop, w n ≠ 0)
    (hfN : ∀ᶠ n in atTop, f n ≠ 0) (hfw : Tendsto (fun n => f n / w n) atTop (𝓝 0)) {δ : ℂ}
    (hδ : δ ≠ 0) {n : ℕ} (hfn : f n ≠ 0) (hwn : w n ≠ 0) :
    Tendsto (fun N => ‖(bwdPerturbed w f δ N n - w n) / w n‖) atTop atTop := by
  have hr : Tendsto (fun N => f N / w N) atTop (𝓝[≠] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨hfw, (hfN.and hwN).mono fun N h => div_ne_zero h.1 h.2⟩
  have hK : 0 < ‖δ * (f n / w n)‖ := norm_pos_iff.mpr (mul_ne_zero hδ (div_ne_zero hfn hwn))
  refine ((tendsto_norm_inv_nhdsNE_zero_atTop.comp hr).const_mul_atTop hK).congr fun N => ?_
  simp only [Function.comp, inv_div, ← norm_mul]
  congr 1
  unfold bwdPerturbed
  ring

/-! ### The boundary-value method 3.6.7 -/

/-- The boundary-value problem of 3.6.7: `w₀^{(N)} = λ`, `w_N^{(N)} = 0`, and 3.6.1 for
`n = 1, …, N − 1`. -/
def IsBVSol (a b c d : ℕ → ℂ) (lam : ℂ) (N : ℕ) (u : ℕ → ℂ) : Prop :=
  u 0 = lam ∧ u N = 0 ∧
    ∀ n, 1 ≤ n → n + 1 ≤ N → a n * u (n + 1) - b n * u n + c n * u (n - 1) = d n

/-- The complementary function `hₙ = g₀ fₙ − f₀ gₙ`, which vanishes at `n = 0`. -/
def bvH (f g : ℕ → ℂ) (n : ℕ) : ℂ := g 0 * f n - f 0 * g n

theorem bvH_isRec3 {a b c f g : ℕ → ℂ} (hf : IsRec3 a b c f) (hg : IsRec3 a b c g) :
    IsRec3 a b c (bvH f g) := fun n hn => by
  unfold bvH; linear_combination g 0 * hf n hn - f 0 * hg n hn

/-- A complementary function vanishing at `0` is a multiple of `h` on `0, …, N`. -/
theorem eq_mul_bvH_of_zero {a b c v h : ℕ → ℂ} (ha : ∀ n, 1 ≤ n → a n ≠ 0) {N : ℕ}
    (hv : ∀ n, 1 ≤ n → n + 1 ≤ N → a n * v (n + 1) - b n * v n + c n * v (n - 1) = 0)
    (hh : IsRec3 a b c h) (hv0 : v 0 = 0) (hh0 : h 0 = 0) {κ : ℂ} (hv1 : v 1 = κ * h 1) :
    ∀ n, n ≤ N → v n = κ * h n := by
  have key : ∀ m, m + 1 ≤ N → v m = κ * h m ∧ v (m + 1) = κ * h (m + 1) := by
    intro m
    induction m with
    | zero => intro _; exact ⟨by rw [hv0, hh0, mul_zero], hv1⟩
    | succ m ih =>
      intro hm
      obtain ⟨ih1, ih2⟩ := ih (by omega)
      refine ⟨ih2, ?_⟩
      have e1 := hv (m + 1) (by omega) (by omega)
      have e2 := hh.shift m
      simp only [Nat.add_sub_cancel] at e1
      rw [ih1, ih2] at e1
      have ham := ha (m + 1) (by omega)
      apply mul_left_cancel₀ ham
      linear_combination e1 - κ * e2
  intro n hn
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · subst h0; rw [hv0, hh0, mul_zero]
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    exact (key m hn).2

/-- **DLMF §3.6(iv)**, the boundary-value method: with `aₙ cₙ ≠ 0`, complementary functions `f`,
`g` with `f₀ ≠ 0`, `gₙ ≠ 0` for large `n` and `fₙ/gₙ → 0`, and a solution `w` of 3.6.1 with
`wₙ/gₙ → 0` (3.6.6): for all large `N` the system 3.6.7 with `λ = w₀` is solvable, and every
choice of solutions `w^{(N)}` satisfies `wₙ^{(N)} → wₙ` as `N → ∞` with `n` fixed. -/
theorem dlmf_3_6_iv_boundary {a b c d f g w : ℕ → ℂ} (ha : ∀ n, 1 ≤ n → a n ≠ 0)
    (hf : IsRec3 a b c f) (hg : IsRec3 a b c g) (hf0 : f 0 ≠ 0)
    (hgN : ∀ᶠ n in atTop, g n ≠ 0) (hfg : Tendsto (fun n => f n / g n) atTop (𝓝 0))
    (hw : IsRec3Inh a b c d w) (hwg : Tendsto (fun n => w n / g n) atTop (𝓝 0)) :
    (∀ᶠ N in atTop, ∃ u, IsBVSol a b c d (w 0) N u) ∧
      ∀ u : ℕ → ℕ → ℂ, (∀ᶠ N in atTop, IsBVSol a b c d (w 0) N (u N)) →
        ∀ n, Tendsto (fun N => u N n) atTop (𝓝 (w n)) := by
  have hC := casoratian_ne_zero_of_recessive ha hf (fun h => hf0 (by simp [h])) hg ⟨hgN, hfg⟩
  have hh := bvH_isRec3 hf hg
  have hh0 : bvH f g 0 = 0 := by simp [bvH]; ring
  have hh1 : bvH f g 1 ≠ 0 := by
    intro h; apply hC; simp only [casoratian, zero_add]; unfold bvH at h; linear_combination -h
  -- `h_N/g_N → −f₀`
  have hhg : Tendsto (fun N => bvH f g N / g N) atTop (𝓝 (g 0 * 0 - f 0)) := by
    refine ((hfg.const_mul (g 0)).sub_const (f 0)).congr' ?_
    filter_upwards [hgN] with N hN
    unfold bvH; field_simp
  rw [mul_zero, zero_sub] at hhg
  have hhN : ∀ᶠ N in atTop, bvH f g N ≠ 0 := by
    have := hhg.eventually_ne (neg_ne_zero.mpr hf0)
    filter_upwards [this] with N hN h0
    exact hN (by rw [h0, zero_div])
  -- `w_N/h_N → 0`
  have hwh : Tendsto (fun N => w N / bvH f g N) atTop (𝓝 0) := by
    have := hwg.div hhg (neg_ne_zero.mpr hf0)
    rw [zero_div] at this
    refine this.congr' ?_
    filter_upwards [hgN] with N hN
    simp only [Pi.div_apply]
    field_simp
  -- the solution of 3.6.7
  have hsol : ∀ N, bvH f g N ≠ 0 →
      IsBVSol a b c d (w 0) N (fun n => w n + (-(w N / bvH f g N)) * bvH f g n) := by
    intro N hN
    refine ⟨by show w 0 + _ * bvH f g 0 = w 0; rw [hh0, mul_zero, add_zero],
      by field_simp; ring, fun n hn _ => ?_⟩
    exact (hw.add_hom (hh.const_mul _)) n hn
  refine ⟨?_, fun u hu n => ?_⟩
  · filter_upwards [hhN] with N hN using ⟨_, hsol N hN⟩
  · have hlim : Tendsto (fun N => w n + (-(w N / bvH f g N)) * bvH f g n) atTop
        (𝓝 (w n + (-0) * bvH f g n)) :=
      tendsto_const_nhds.add (hwh.neg.mul_const _)
    rw [neg_zero, zero_mul, add_zero] at hlim
    refine hlim.congr' ?_
    filter_upwards [hu, hhN, eventually_ge_atTop n, eventually_ge_atTop 1] with N hN hN0 hnN h1N
    obtain ⟨hu0, huN, hueq⟩ := hN
    -- `u − w` is a complementary function on `0, …, N` vanishing at `0`
    have hv : ∀ m, 1 ≤ m → m + 1 ≤ N → a m * (u N (m + 1) - w (m + 1)) -
        b m * (u N m - w m) + c m * (u N (m - 1) - w (m - 1)) = 0 := fun m hm1 hm2 => by
      linear_combination hueq m hm1 hm2 - hw m hm1
    have hmul := eq_mul_bvH_of_zero (v := fun m => u N m - w m) ha hv hh
      (by show u N 0 - w 0 = 0; rw [hu0, sub_self]) hh0
      (κ := (u N 1 - w 1) / bvH f g 1) (by show u N 1 - w 1 = _; field_simp)
    generalize (u N 1 - w 1) / bvH f g 1 = κ at hmul
    have hκ : κ = -(w N / bvH f g N) := by
      have := hmul N le_rfl
      rw [huN, zero_sub] at this
      rw [neg_div', eq_div_iff hN0]
      linear_combination -this
    have := hmul n hnN
    rw [hκ] at this
    linear_combination -this

/-- The wanted solution of the boundary-value method is unique: two solutions of 3.6.1 with the
same `w₀` and `wₙ/gₙ → 0` coincide. -/
theorem dlmf_3_6_iv_wanted_unique {a b c d f g w w' : ℕ → ℂ} (ha : ∀ n, 1 ≤ n → a n ≠ 0)
    (hf : IsRec3 a b c f) (hg : IsRec3 a b c g) (hf0 : f 0 ≠ 0)
    (hgN : ∀ᶠ n in atTop, g n ≠ 0) (hfg : Tendsto (fun n => f n / g n) atTop (𝓝 0))
    (hw : IsRec3Inh a b c d w) (hwg : Tendsto (fun n => w n / g n) atTop (𝓝 0))
    (hw' : IsRec3Inh a b c d w') (hw'g : Tendsto (fun n => w' n / g n) atTop (𝓝 0))
    (h0 : w' 0 = w 0) : w' = w := by
  have B := dlmf_3_6_iv_boundary ha hf hg hf0 hgN hfg hw hwg
  have B' := dlmf_3_6_iv_boundary ha hf hg hf0 hgN hfg hw' hw'g
  rw [h0] at B'
  let u : ℕ → ℕ → ℂ := fun N => Classical.epsilon fun v => IsBVSol a b c d (w 0) N v
  have hu : ∀ᶠ N in atTop, IsBVSol a b c d (w 0) N (u N) :=
    B.1.mono fun N h => Classical.epsilon_spec h
  funext n
  exact tendsto_nhds_unique (B'.2 u hu n) (B.2 u hu n)

/-! ### 3.6.7 as a tridiagonal system (§3.2(ii)) -/

theorem triEntry_split (a' b' c' : ℕ → ℂ) {M : ℕ} (i j : Fin M) :
    triEntry a' b' c' i j = (if j.val = i.val then b' (i + 1) else
      if j.val = i.val + 1 then c' (i + 1) else 0) +
      (if j = i then 0 else if j.val + 1 = i.val then a' (i + 1) else 0) := by
  unfold triEntry
  by_cases h1 : j.val = i.val
  · have : j = i := Fin.ext h1
    simp [this]
  · have h1' : j ≠ i := fun h => h1 (by rw [h])
    by_cases h2 : j.val = i.val + 1
    · simp [h1', h2]; omega
    · simp [h1, h1', h2]

/-- Row `i` of the tridiagonal matrix-vector product. -/
theorem tridiag_mulVec_row (a' b' c' : ℕ → ℂ) {M : ℕ} (x : Fin M → ℂ) (i : Fin M) :
    ((tridiag a' b' c' : AzMatrix ℂ M M).mulVec (AzVector.ofFn x)).toFn i =
      b' (i + 1) * x i + (if h : i.val + 1 < M then c' (i + 1) * x ⟨i.val + 1, h⟩ else 0) +
        (if h : 0 < i.val then a' (i + 1) * x ⟨i.val - 1, by omega⟩ else 0) := by
  rw [AzMatrix.toFn_mulVec, dotProduct]
  simp only [tridiag, AzMatrix.toFn_ofFn, AzVector.toFn_ofFn, triEntry_split, add_mul,
    Finset.sum_add_distrib]
  rw [sum_upper_bidiag i _ _ x, sum_lower_bidiag i _ _ x, zero_mul, zero_add, add_assoc]

/-- **DLMF 3.6.7**: the boundary-value problem (`w₀ = λ`, `w_N = 0`, 3.6.1 for `n = 1, …, N − 1`)
is the tridiagonal system with `−bₙ` on the diagonal, `aₙ` above and `cₙ` below it (3.2.7), for
the unknowns `w₁^{(N)}, …, w_{N−1}^{(N)}` and right side `(d₁ − c₁λ, d₂, …, d_{N−1})`. -/
theorem dlmf_3_6_7 (a b c d : ℕ → ℂ) (lam : ℂ) (N : ℕ) (u : ℕ → ℂ) :
    IsBVSol a b c d lam N u ↔ u 0 = lam ∧ u N = 0 ∧
      (tridiag c (fun j => -b j) a : AzMatrix ℂ (N - 1) (N - 1)).mulVec
        (AzVector.ofFn fun i => u (i.val + 1)) =
        AzVector.ofFn fun i => d (i.val + 1) - if i.val = 0 then c 1 * lam else 0 := by
  unfold IsBVSol
  refine ⟨fun ⟨h0, hN, h⟩ => ⟨h0, hN, ?_⟩, fun ⟨h0, hN, h⟩ => ⟨h0, hN, fun n hn1 hn2 => ?_⟩⟩
  · apply AzVector.toFn_injective
    funext i
    rw [tridiag_mulVec_row, AzVector.toFn_ofFn]
    have e := h (i.val + 1) (by omega) (by omega)
    simp only [Nat.add_sub_cancel] at e
    by_cases hup : i.val + 1 < N - 1 <;> by_cases hlo : 0 < i.val <;>
      simp only [hup, hlo, dite_true, dite_false, add_zero]
    · have hi : i.val ≠ 0 := by omega
      simp only [hi, ite_false, sub_zero]
      rw [show i.val - 1 + 1 = i.val by omega]
      linear_combination e
    · have hi : i.val = 0 := by omega
      simp only [hi, ite_true, zero_add] at e ⊢
      rw [h0] at e
      linear_combination e
    · have hN' : i.val + 1 + 1 = N := by omega
      have hi : i.val ≠ 0 := by omega
      simp only [hi, ite_false, sub_zero]
      rw [hN', hN] at e
      rw [show i.val - 1 + 1 = i.val by omega]
      linear_combination e
    · have hi : i.val = 0 := by omega
      have hN' : i.val + 1 + 1 = N := by omega
      rw [hN', hN] at e
      simp only [hi, ite_true, zero_add] at e ⊢
      rw [h0] at e
      linear_combination e
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have e := congrArg (fun v => AzVector.toFn v ⟨m, by omega⟩) h
    simp only [tridiag_mulVec_row, AzVector.toFn_ofFn] at e
    simp only [Nat.add_sub_cancel]
    by_cases hup : m + 1 < N - 1 <;> by_cases hlo : 0 < m <;>
      simp only [hup, hlo, dite_true, dite_false, add_zero] at e
    · have hi : m ≠ 0 := by omega
      simp only [hi, ite_false, sub_zero] at e
      rw [show m - 1 + 1 = m by omega] at e
      linear_combination e
    · have hi : m = 0 := by omega
      subst hi
      simp only [ite_true, zero_add] at e ⊢
      rw [h0]
      linear_combination e
    · have hN' : m + 1 + 1 = N := by omega
      have hi : m ≠ 0 := by omega
      simp only [hi, ite_false, sub_zero] at e
      rw [show m - 1 + 1 = m by omega] at e
      rw [hN', hN]
      linear_combination e
    · have hi : m = 0 := by omega
      have hN' : m + 1 + 1 = N := by omega
      rw [hN', hN]
      subst hi
      simp only [ite_true, zero_add] at e ⊢
      rw [h0]
      linear_combination e

end Azurite.DLMF
