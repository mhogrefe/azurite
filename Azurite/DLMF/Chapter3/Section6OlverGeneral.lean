/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter3.Section6OlverError

/-!
# DLMF §3.6(v), error analysis: Olver (1967a), §§9–10

The "more general form of normalizing condition" of Olver (1967a) (in the notation of 3.6.1;
Olver's `aᵣ`, `cᵣ` are our `cᵣ`, `aᵣ`):

* (9.01) `∑ mᵣwᵣ = k` (`NormSum`, as the limit of the partial sums); under (9.02)
  `|∑_{r≤N} mᵣgᵣ| → ∞` and (9.03) `∑ mᵣfᵣ = F ≠ 0`, `∑ mᵣhᵣ = H` the unique solution is
  (9.04) `wᵣ = ((k − H)/F) fᵣ + hᵣ` (`olver_9_04`; `eq_comb_of_range` spans solutions on a finite
  range).
* The boundary-value problem (9.05)–(9.07) (`IsGenBVSol`); forward elimination gives the pivotal
  equations (9.10) with `pᵣ`, `qᵣ`, `eᵣ` of (9.11)–(9.13) (`genP`, `genQ`, `genE`,
  `olver_9_10`) and (9.14) (`olver_9_14`).
* **Theorem 2** (`olver_theorem_2`): with (9.08) the solutions `w^{(N)}` converge to `wᵣ`.
* Strict bounds for the truncation error: (10.02) for `ηᵣ = wᵣ^{(N+1)} − wᵣ^{(N)}`
  (`olver_10_02`), (10.03) with bounds `ρᵣ` (`IsRhoBound`, Olver's choice (10.04) in
  `olver_10_04`; `olver_10_03`), (10.05)–(10.06) by induction (`olver_10_06`, `olver_eta_N`), and
  (10.07)–(10.10): `|wᵣ − wᵣ^{(N)}| ≤ ρᵣ(1 + ρ_{r+1})⋯(1 + ρ_{N−1}) E_N` for `r < N` and
  `|w_N| ≤ E_N`, with `E_N` of (10.09) (`olverGenBound`, `olver_10_07`,
  `norm_sub_le_tsum_of_steps`), provided that series converges.

Not formalized: the numerical examples (§§6, 9, 11), §8 (Miller's and Shintani's algorithms as
backward elimination), §11 (the alternative method; its error decomposition (11.10)–(11.11) is
"to the first order of small quantities").
-/

open Filter Topology Finset

namespace Azurite.DLMF

variable {a b c d m : ℕ → ℂ}

/-! ### The general normalizing condition (9.01) and the unique solution (9.04) -/

/-- The normalizing condition `∑_{r≥0} mᵣ wᵣ = k` (Olver (9.01)), as the limit of the partial sums
`∑_{r≤N}`. -/
def NormSum (m w : ℕ → ℂ) (k : ℂ) : Prop :=
  Tendsto (fun N => ∑ r ∈ range (N + 1), m r * w r) atTop (𝓝 k)

/-- Two solutions of 3.6.3 with nonzero Casoratian span the solutions of the homogeneous equation
on `0, …, N`. -/
theorem eq_comb_of_range (ha : ∀ n, 1 ≤ n → a n ≠ 0) {f g v : ℕ → ℂ} (hf : IsRec3 a b c f)
    (hg : IsRec3 a b c g) (hC : casoratian f g 0 ≠ 0) {N : ℕ}
    (hv : ∀ n, 1 ≤ n → n + 1 ≤ N → a n * v (n + 1) - b n * v n + c n * v (n - 1) = 0) :
    ∃ A B : ℂ, ∀ n, n ≤ N → v n = A * f n + B * g n := by
  simp only [casoratian, zero_add] at hC
  refine ⟨(v 0 * g 1 - v 1 * g 0) / (f 0 * g 1 - f 1 * g 0),
    (f 0 * v 1 - f 1 * v 0) / (f 0 * g 1 - f 1 * g 0), ?_⟩
  set A := (v 0 * g 1 - v 1 * g 0) / (f 0 * g 1 - f 1 * g 0)
  set B := (f 0 * v 1 - f 1 * v 0) / (f 0 * g 1 - f 1 * g 0)
  have h0 : v 0 = A * f 0 + B * g 0 := by
    simp only [A, B]
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, eq_div_iff hC]; ring
  have h1 : v 1 = A * f 1 + B * g 1 := by
    simp only [A, B]
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, eq_div_iff hC]; ring
  have key : ∀ n, n + 1 ≤ N →
      v n = A * f n + B * g n ∧ v (n + 1) = A * f (n + 1) + B * g (n + 1) := by
    intro n
    induction n with
    | zero => intro _; exact ⟨h0, h1⟩
    | succ n ih =>
      intro hn
      obtain ⟨ih1, ih2⟩ := ih (by omega)
      refine ⟨ih2, ?_⟩
      have e := hv (n + 1) (by omega) (by omega)
      simp only [Nat.add_sub_cancel] at e
      rw [ih1, ih2] at e
      have ham := ha (n + 1) (by omega)
      apply mul_left_cancel₀ ham
      linear_combination e - A * hf.shift n - B * hg.shift n
  intro n hn
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h; exact h0
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    exact (key k hn).2

/-- **Olver (9.04)**: under (9.02) `|∑_{r≤N} mᵣgᵣ| → ∞` and (9.03) `∑ mᵣfᵣ = F ≠ 0`,
`∑ mᵣhᵣ = H`, the equation 3.6.1 has the unique solution `wᵣ = ((k − H)/F) fᵣ + hᵣ` satisfying
`∑ mᵣwᵣ = k`. -/
theorem olver_9_04 (ha : ∀ n, 1 ≤ n → a n ≠ 0) {f g h : ℕ → ℂ} (hf : IsRec3 a b c f)
    (hg : IsRec3 a b c g) (hC : casoratian f g 0 ≠ 0) (hh : IsRec3Inh a b c d h)
    (h902 : Tendsto (fun N => ‖∑ r ∈ range (N + 1), m r * g r‖) atTop atTop) {F H k : ℂ}
    (hF : NormSum m f F) (hF0 : F ≠ 0) (hH : NormSum m h H) :
    IsRec3Inh a b c d (fun r => (k - H) / F * f r + h r) ∧
      NormSum m (fun r => (k - H) / F * f r + h r) k ∧
      ∀ z, IsRec3Inh a b c d z → NormSum m z k → z = fun r => (k - H) / F * f r + h r := by
  refine ⟨fun n hn => by linear_combination (k - H) / F * hf n hn + hh n hn, ?_,
    fun z hz hzk => ?_⟩
  · have := (hF.const_mul ((k - H) / F)).add hH
    rw [div_mul_cancel₀ _ hF0, sub_add_cancel] at this
    refine this.congr fun N => ?_
    rw [mul_sum, ← sum_add_distrib]
    exact sum_congr rfl fun r _ => by ring
  · obtain ⟨A, B, hAB⟩ := IsRec3.eq_comb ha hf hg (hz.sub hh) hC
    have hz' : ∀ r, z r = A * f r + B * g r + h r := fun r => by
      have : z r - h r = A * f r + B * g r := congrFun hAB r
      linear_combination this
    -- the partial sums of `z` are `A S_f + B S_g + S_h`
    have hsum : ∀ N, ∑ r ∈ range (N + 1), m r * z r = A * ∑ r ∈ range (N + 1), m r * f r +
        B * ∑ r ∈ range (N + 1), m r * g r + ∑ r ∈ range (N + 1), m r * h r := fun N => by
      rw [mul_sum, mul_sum, ← sum_add_distrib, ← sum_add_distrib]
      exact sum_congr rfl fun r _ => by rw [hz' r]; ring
    have hB : B = 0 := by
      by_contra hB
      have hconv : Tendsto (fun N => B * ∑ r ∈ range (N + 1), m r * g r) atTop
          (𝓝 (k - A * F - H)) := by
        have := (hzk.sub (hF.const_mul A)).sub hH
        refine this.congr fun N => ?_
        rw [hsum N]; ring
      have hdiv : Tendsto (fun N => ‖B * ∑ r ∈ range (N + 1), m r * g r‖) atTop atTop := by
        simp only [norm_mul]
        exact h902.const_mul_atTop (norm_pos_iff.mpr hB)
      exact not_tendsto_atTop_of_tendsto_nhds hconv.norm hdiv
    have hA : A = (k - H) / F := by
      have h1 : Tendsto (fun N => ∑ r ∈ range (N + 1), m r * z r) atTop (𝓝 (A * F + 0 + H)) := by
        refine (((hF.const_mul A).add ?_).add hH).congr fun N => (hsum N).symm
        simp only [hB, zero_mul]
        exact tendsto_const_nhds
      have := tendsto_nhds_unique hzk h1
      rw [eq_div_iff hF0]; linear_combination -this
    funext r
    rw [hz' r, hB, hA, zero_mul, add_zero]

/-! ### The extended forward elimination (9.10)–(9.14) -/

/-- `qᵣ = (c₁⋯cᵣ)/(a₁⋯aᵣ)` (Olver (9.11), in the notation of 3.6.1). -/
noncomputable def genQ (a c : ℕ → ℂ) : ℕ → ℂ
  | 0 => 1
  | r + 1 => genQ a c r * (c (r + 1) / a (r + 1))

/-- The pairs `(pᵣ, p_{r+1})` of Olver (9.12)–(9.13): `p₀ = 0`, `p₁ = m₀`,
`p_{r+1} = (bᵣpᵣ − cᵣp_{r−1})/aᵣ + qᵣmᵣ`. -/
noncomputable def genPPair (a b c m : ℕ → ℂ) : ℕ → ℂ × ℂ
  | 0 => (0, m 0)
  | r + 1 => ((genPPair a b c m r).2,
      (b (r + 1) * (genPPair a b c m r).2 - c (r + 1) * (genPPair a b c m r).1) / a (r + 1) +
        genQ a c (r + 1) * m (r + 1))

/-- `pᵣ` of Olver (9.12)–(9.13). -/
noncomputable def genP (a b c m : ℕ → ℂ) (r : ℕ) : ℂ := (genPPair a b c m r).1

/-- `eᵣ` of Olver (9.12)–(9.13): `e₀ = k`, `eᵣ = (cᵣe_{r−1} − dᵣpᵣ)/aᵣ`. -/
noncomputable def genE (a b c d m : ℕ → ℂ) (k : ℂ) : ℕ → ℂ
  | 0 => k
  | r + 1 => (c (r + 1) * genE a b c d m k r - d (r + 1) * genP a b c m (r + 1)) / a (r + 1)

@[simp] theorem genP_zero : genP a b c m 0 = 0 := rfl

@[simp] theorem genP_one : genP a b c m 1 = m 0 := rfl

theorem genP_succ_succ (r : ℕ) : genP a b c m (r + 2) =
    (b (r + 1) * genP a b c m (r + 1) - c (r + 1) * genP a b c m r) / a (r + 1) +
      genQ a c (r + 1) * m (r + 1) := rfl

/-- The boundary-value problem (9.05)–(9.07): 3.6.1 for `r = 1, …, N − 1`,
`∑_{r≤N} mᵣ wᵣ^{(N)} = k`, `w_N^{(N)} = 0`. -/
def IsGenBVSol (a b c d m : ℕ → ℂ) (k : ℂ) (N : ℕ) (u : ℕ → ℂ) : Prop :=
  (∀ r, 1 ≤ r → r + 1 ≤ N → a r * u (r + 1) - b r * u r + c r * u (r - 1) = d r) ∧
    ∑ r ∈ range (N + 1), m r * u r = k ∧ u N = 0

/-- **Olver (9.10)**: forward elimination of (9.05)–(9.07) gives the pivotal equations
`p_{r+1} wᵣ^{(N)} − pᵣ w_{r+1}^{(N)} + qᵣ ∑_{s=r+1}^{N−1} mₛ wₛ^{(N)} = eᵣ`, `r < N`. -/
theorem olver_9_10 (ha : ∀ n, 1 ≤ n → a n ≠ 0) {k : ℂ} {N : ℕ} {u : ℕ → ℂ}
    (hu : IsGenBVSol a b c d m k N u) :
    ∀ r, r < N → genP a b c m (r + 1) * u r - genP a b c m r * u (r + 1) +
      genQ a c r * ∑ s ∈ Ico (r + 1) N, m s * u s = genE a b c d m k r := by
  obtain ⟨heq, hsum, hN⟩ := hu
  intro r
  induction r with
  | zero =>
    intro h0
    simp only [zero_add, genP_one, genP_zero, zero_mul, sub_zero, genQ, genE, one_mul]
    rw [range_eq_Ico, sum_eq_sum_Ico_succ_bot (by omega), sum_Ico_succ_top (by omega), hN,
      mul_zero, add_zero] at hsum
    exact hsum
  | succ r ih =>
    intro hr
    have ih := ih (by omega)
    have e := heq (r + 1) (by omega) (by omega)
    simp only [Nat.add_sub_cancel] at e
    rw [sum_eq_sum_Ico_succ_bot (by omega : r + 1 < N)] at ih
    rw [show r + 1 + 1 = r + 2 by rfl, genP_succ_succ, genE, genQ]
    have := ha (r + 1) (by omega)
    field_simp
    linear_combination c (r + 1) * ih - genP a b c m (r + 1) * e

/-- **Olver (9.14)**: the final pivotal equation `p_N w_{N−1}^{(N)} = e_{N−1}`. -/
theorem olver_9_14 (ha : ∀ n, 1 ≤ n → a n ≠ 0) {k : ℂ} {N : ℕ} (hN : 1 ≤ N) {u : ℕ → ℂ}
    (hu : IsGenBVSol a b c d m k N u) :
    genP a b c m N * u (N - 1) = genE a b c d m k (N - 1) := by
  have := olver_9_10 ha hu (N - 1) (by omega)
  rw [show N - 1 + 1 = N by omega, Ico_self, sum_empty, mul_zero, add_zero, hu.2.2, mul_zero,
    sub_zero] at this
  exact this

/-! ### Theorem 2: convergence of the general algorithm -/

/-- **Olver, Theorem 2**: with (9.02)–(9.03), if for all large `N` the system (9.05)–(9.07) has a
solution `w^{(N)}`, `g_N ≠ 0`, and (9.08) `(f_N/g_N) ∑_{r≤N} mᵣgᵣ → 0`,
`(h_N/g_N) ∑_{r≤N} mᵣgᵣ → 0`, then `wᵣ^{(N)} → wᵣ` as `N → ∞` with `r` fixed. -/
theorem olver_theorem_2 (ha : ∀ n, 1 ≤ n → a n ≠ 0) {f g h : ℕ → ℂ} (hf : IsRec3 a b c f)
    (hg : IsRec3 a b c g) (hC : casoratian f g 0 ≠ 0) (hh : IsRec3Inh a b c d h)
    (h902 : Tendsto (fun N => ‖∑ r ∈ range (N + 1), m r * g r‖) atTop atTop) {F H k : ℂ}
    (hF : NormSum m f F) (hF0 : F ≠ 0) (hH : NormSum m h H) {u : ℕ → ℕ → ℂ}
    (hu : ∀ᶠ N in atTop, IsGenBVSol a b c d m k N (u N)) (hgN : ∀ᶠ N in atTop, g N ≠ 0)
    (h908f : Tendsto (fun N => f N / g N * ∑ r ∈ range (N + 1), m r * g r) atTop (𝓝 0))
    (h908h : Tendsto (fun N => h N / g N * ∑ r ∈ range (N + 1), m r * g r) atTop (𝓝 0))
    (r : ℕ) : Tendsto (fun N => u N r) atTop (𝓝 ((k - H) / F * f r + h r)) := by
  set Sf : ℕ → ℂ := fun N => ∑ r ∈ range (N + 1), m r * f r
  set Sg : ℕ → ℂ := fun N => ∑ r ∈ range (N + 1), m r * g r
  set Sh : ℕ → ℂ := fun N => ∑ r ∈ range (N + 1), m r * h r
  have hSg : ∀ᶠ N in atTop, Sg N ≠ 0 := by
    filter_upwards [h902.eventually_gt_atTop 0] with N hN
    exact norm_pos_iff.mp hN
  -- `f_N/g_N → 0` and `h_N/g_N → 0`
  have hdiv : ∀ {φ : ℕ → ℂ}, Tendsto (fun N => φ N / g N * Sg N) atTop (𝓝 0) →
      Tendsto (fun N => φ N / g N) atTop (𝓝 0) := fun {φ} hφ => by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have := hφ.norm.div_atTop h902
    refine this.congr' ?_
    filter_upwards [hSg] with N hN
    rw [norm_mul, mul_div_assoc, div_self (norm_ne_zero_iff.mpr hN), mul_one]
  have hfg := hdiv h908f
  have hhg := hdiv h908h
  -- the coefficients `A_N`, `B_N`
  set D : ℕ → ℂ := fun N => Sf N - f N / g N * Sg N
  set A : ℕ → ℂ := fun N => (k - Sh N + h N / g N * Sg N) / D N
  set B : ℕ → ℂ := fun N => -(h N / g N) - A N * (f N / g N)
  have hD : Tendsto D atTop (𝓝 (F - 0)) := hF.sub h908f
  rw [sub_zero] at hD
  have hA : Tendsto A atTop (𝓝 ((k - H + 0) / F)) :=
    ((tendsto_const_nhds.sub hH).add h908h).div hD hF0
  rw [add_zero] at hA
  have hB : Tendsto B atTop (𝓝 (-0 - (k - H) / F * 0)) := hhg.neg.sub (hA.mul hfg)
  rw [neg_zero, mul_zero, sub_zero] at hB
  have hlim : Tendsto (fun N => A N * f r + B N * g r + h r) atTop
      (𝓝 ((k - H) / F * f r + 0 * g r + h r)) :=
    ((hA.mul_const _).add (hB.mul_const _)).add tendsto_const_nhds
  rw [zero_mul, add_zero] at hlim
  refine hlim.congr' ?_
  filter_upwards [hu, hgN, hD.eventually_ne hF0, eventually_ge_atTop r] with N hN hgN' hDN hrN
  obtain ⟨heq, hsum, hNN⟩ := hN
  obtain ⟨A', B', hAB⟩ := eq_comb_of_range ha hf hg hC (v := fun n => u N n - h n) (N := N)
    fun n hn1 hn2 => by linear_combination heq n hn1 hn2 - hh n hn1
  have hu' : ∀ n, n ≤ N → u N n = A' * f n + B' * g n + h n := fun n hn => by
    have : u N n - h n = A' * f n + B' * g n := hAB n hn
    linear_combination this
  -- `w_N^{(N)} = 0` and the normalizing sum determine `A'`, `B'`
  have e1 : A' * f N + B' * g N + h N = 0 := by rw [← hu' N le_rfl, hNN]
  have e2 : A' * Sf N + B' * Sg N + Sh N = k := by
    rw [← hsum]
    simp only [Sf, Sg, Sh, mul_sum, ← sum_add_distrib]
    exact (sum_congr rfl fun n hn => by
      rw [hu' n (by simpa [Nat.lt_succ_iff] using hn)]; ring).symm
  have hB' : B' = -(h N + A' * f N) / g N := by
    rw [eq_div_iff hgN']; linear_combination e1
  have hA' : A' = A N := by
    simp only [A, D]
    rw [eq_div_iff hDN]
    linear_combination e2 - Sg N * hB'
  have hB'' : B' = B N := by
    simp only [B]; rw [hB', ← hA']; ring
  rw [hu' r hrN, hA', hB'']

/-! ### Bounds for the truncation error: Olver (10.02)–(10.10) -/

/-- **Olver (10.02)**: for solutions `w^{(N)}`, `w^{(N+1)}` of (9.05)–(9.07) and
`ηᵣ = wᵣ^{(N+1)} − wᵣ^{(N)}`: `p_{r+1}ηᵣ = pᵣη_{r+1} − qᵣ ∑_{s=r+1}^{N} mₛηₛ`, `r < N`. -/
theorem olver_10_02 (ha : ∀ n, 1 ≤ n → a n ≠ 0) {k : ℂ} {N : ℕ} {u u' : ℕ → ℂ}
    (hu : IsGenBVSol a b c d m k N u) (hu' : IsGenBVSol a b c d m k (N + 1) u') {r : ℕ}
    (hr : r < N) :
    genP a b c m (r + 1) * (u' r - u r) = genP a b c m r * (u' (r + 1) - u (r + 1)) -
      genQ a c r * ∑ s ∈ Ico (r + 1) (N + 1), m s * (u' s - u s) := by
  have h1 := olver_9_10 ha hu r hr
  have h2 := olver_9_10 ha hu' r (by omega)
  have e : ∑ s ∈ Ico (r + 1) (N + 1), m s * (u' s - u s) =
      ∑ s ∈ Ico (r + 1) (N + 1), m s * u' s - ∑ s ∈ Ico (r + 1) N, m s * u s := by
    rw [sum_Ico_succ_top (by omega : r + 1 ≤ N) (fun s => m s * (u' s - u s)),
      sum_Ico_succ_top (by omega : r + 1 ≤ N) (fun s => m s * u' s), hu.2.2, sub_zero]
    simp only [mul_sub, sum_sub_distrib]
    ring
  rw [e]
  linear_combination h2 - h1

/-- The hypotheses on the bounds `ρᵣ` of Olver (10.04): `|pᵣ − qᵣm_{r+1}| ≤ ρᵣ|p_{r+1}|` and
`|qᵣmₛ| ≤ ρᵣ|p_{r+1}|` for `s ≥ r + 2`. -/
def IsRhoBound (a b c m : ℕ → ℂ) (ρ : ℕ → ℝ) : Prop :=
  (∀ r, ‖genP a b c m r - genQ a c r * m (r + 1)‖ ≤ ρ r * ‖genP a b c m (r + 1)‖) ∧
    ∀ r s, r + 2 ≤ s → ‖genQ a c r * m s‖ ≤ ρ r * ‖genP a b c m (r + 1)‖

/-- **Olver (10.04)**: with `|mₛ| ≤ M` for all `s`, `ρᵣ` = the greater of
`|pᵣ − qᵣm_{r+1}|/|p_{r+1}|` and `|qᵣ| M/|p_{r+1}|` is such a bound. -/
theorem olver_10_04 (hp : ∀ r, 1 ≤ r → genP a b c m r ≠ 0) {M : ℝ} (hM : ∀ s, ‖m s‖ ≤ M) :
    IsRhoBound a b c m fun r => max (‖genP a b c m r - genQ a c r * m (r + 1)‖ /
      ‖genP a b c m (r + 1)‖) (‖genQ a c r‖ * M / ‖genP a b c m (r + 1)‖) := by
  have hpos : ∀ r, 0 < ‖genP a b c m (r + 1)‖ := fun r =>
    norm_pos_iff.mpr (hp (r + 1) (by omega))
  refine ⟨fun r => ?_, fun r s _ => ?_⟩
  · calc ‖genP a b c m r - genQ a c r * m (r + 1)‖
        = ‖genP a b c m r - genQ a c r * m (r + 1)‖ / ‖genP a b c m (r + 1)‖ *
          ‖genP a b c m (r + 1)‖ := by rw [div_mul_cancel₀ _ (hpos r).ne']
      _ ≤ _ := by gcongr; exact le_max_left _ _
  · calc ‖genQ a c r * m s‖ ≤ ‖genQ a c r‖ * M := by rw [norm_mul]; gcongr; exact hM s
      _ = ‖genQ a c r‖ * M / ‖genP a b c m (r + 1)‖ * ‖genP a b c m (r + 1)‖ := by
          rw [div_mul_cancel₀ _ (hpos r).ne']
      _ ≤ _ := by gcongr; exact le_max_right _ _

theorem IsRhoBound.nonneg {ρ : ℕ → ℝ} (hρ : IsRhoBound a b c m ρ)
    (hp : ∀ r, 1 ≤ r → genP a b c m r ≠ 0) (r : ℕ) : 0 ≤ ρ r := by
  have h := hρ.1 r
  have hpos : 0 < ‖genP a b c m (r + 1)‖ := norm_pos_iff.mpr (hp (r + 1) (by omega))
  by_contra hneg
  push Not at hneg
  linarith [norm_nonneg (genP a b c m r - genQ a c r * m (r + 1)),
    mul_neg_of_neg_of_pos hneg hpos]

/-- **Olver (10.03)**: `|ηᵣ| ≤ ρᵣ (|η_{r+1}| + ⋯ + |η_N|)`, `r < N`. -/
theorem olver_10_03 (ha : ∀ n, 1 ≤ n → a n ≠ 0) (hp : ∀ r, 1 ≤ r → genP a b c m r ≠ 0)
    {ρ : ℕ → ℝ} (hρ : IsRhoBound a b c m ρ) {k : ℂ} {N : ℕ} {u u' : ℕ → ℂ}
    (hu : IsGenBVSol a b c d m k N u) (hu' : IsGenBVSol a b c d m k (N + 1) u') {r : ℕ}
    (hr : r < N) :
    ‖u' r - u r‖ ≤ ρ r * ∑ s ∈ Ico (r + 1) (N + 1), ‖u' s - u s‖ := by
  have h := olver_10_02 ha hu hu' hr
  rw [sum_eq_sum_Ico_succ_bot (by omega : r + 1 < N + 1)] at h
  have hpos : 0 < ‖genP a b c m (r + 1)‖ := norm_pos_iff.mpr (hp (r + 1) (by omega))
  have hρ0 := hρ.nonneg hp r
  rw [sum_eq_sum_Ico_succ_bot (by omega : r + 1 < N + 1), mul_add]
  have key : ‖genP a b c m (r + 1)‖ * ‖u' r - u r‖ ≤ ‖genP a b c m (r + 1)‖ *
      (ρ r * ‖u' (r + 1) - u (r + 1)‖ + ρ r * ∑ s ∈ Ico (r + 1 + 1) (N + 1), ‖u' s - u s‖) := by
    rw [← norm_mul, h]
    have e : genP a b c m r * (u' (r + 1) - u (r + 1)) -
        genQ a c r * (m (r + 1) * (u' (r + 1) - u (r + 1)) +
          ∑ s ∈ Ico (r + 1 + 1) (N + 1), m s * (u' s - u s)) =
        (genP a b c m r - genQ a c r * m (r + 1)) * (u' (r + 1) - u (r + 1)) -
          ∑ s ∈ Ico (r + 1 + 1) (N + 1), genQ a c r * m s * (u' s - u s) := by
      simp only [mul_add, mul_sum, mul_assoc]; ring
    rw [e]
    calc ‖(genP a b c m r - genQ a c r * m (r + 1)) * (u' (r + 1) - u (r + 1)) -
          ∑ s ∈ Ico (r + 1 + 1) (N + 1), genQ a c r * m s * (u' s - u s)‖
        ≤ ‖(genP a b c m r - genQ a c r * m (r + 1)) * (u' (r + 1) - u (r + 1))‖ +
          ‖∑ s ∈ Ico (r + 1 + 1) (N + 1), genQ a c r * m s * (u' s - u s)‖ := norm_sub_le _ _
      _ ≤ ‖genP a b c m r - genQ a c r * m (r + 1)‖ * ‖u' (r + 1) - u (r + 1)‖ +
          ∑ s ∈ Ico (r + 1 + 1) (N + 1), ‖genQ a c r * m s‖ * ‖u' s - u s‖ := by
          rw [norm_mul]
          gcongr
          exact (norm_sum_le _ _).trans (le_of_eq (sum_congr rfl fun s _ => norm_mul _ _))
      _ ≤ ρ r * ‖genP a b c m (r + 1)‖ * ‖u' (r + 1) - u (r + 1)‖ +
          ∑ s ∈ Ico (r + 1 + 1) (N + 1), ρ r * ‖genP a b c m (r + 1)‖ * ‖u' s - u s‖ :=
          add_le_add (mul_le_mul_of_nonneg_right (hρ.1 r) (norm_nonneg _))
            (sum_le_sum fun s hs => mul_le_mul_of_nonneg_right
              (hρ.2 r s (by have := (mem_Ico.mp hs).1; omega)) (norm_nonneg _))
      _ = _ := by rw [← mul_sum]; ring
  exact le_of_mul_le_mul_left key hpos

/-- `η_N = e_N/p_{N+1}` (from (9.14) for `N + 1` and `w_N^{(N)} = 0`). -/
theorem olver_eta_N (ha : ∀ n, 1 ≤ n → a n ≠ 0) (hp : ∀ r, 1 ≤ r → genP a b c m r ≠ 0) {k : ℂ}
    {N : ℕ} {u u' : ℕ → ℂ} (hu : IsGenBVSol a b c d m k N u)
    (hu' : IsGenBVSol a b c d m k (N + 1) u') :
    u' N - u N = genE a b c d m k N / genP a b c m (N + 1) := by
  have := olver_9_14 ha (by omega) hu'
  rw [Nat.add_sub_cancel] at this
  rw [hu.2.2, sub_zero, eq_div_iff (hp (N + 1) (by omega)), mul_comm, this]

/-- **Olver (10.05)–(10.06)**: `|ηᵣ| ≤ ρᵣ(1 + ρ_{r+1})⋯(1 + ρ_{N−1}) |e_N/p_{N+1}|`, `r < N`. -/
theorem olver_10_06 (ha : ∀ n, 1 ≤ n → a n ≠ 0) (hp : ∀ r, 1 ≤ r → genP a b c m r ≠ 0)
    {ρ : ℕ → ℝ} (hρ : IsRhoBound a b c m ρ) {k : ℂ} {N : ℕ} {u u' : ℕ → ℂ}
    (hu : IsGenBVSol a b c d m k N u) (hu' : IsGenBVSol a b c d m k (N + 1) u') {r : ℕ}
    (hr : r < N) :
    ‖u' r - u r‖ ≤ ρ r * (∏ s ∈ Ico (r + 1) N, (1 + ρ s)) *
      ‖genE a b c d m k N / genP a b c m (N + 1)‖ := by
  have hρ0 := hρ.nonneg hp
  -- `S_r = ∑_{s=r+1}^N |η_s| ≤ (1 + ρ_{r+1})⋯(1 + ρ_{N−1}) |η_N|`
  have hS : ∀ j, j + 1 ≤ N → ∑ s ∈ Ico (N - j) (N + 1), ‖u' s - u s‖ ≤
      (∏ s ∈ Ico (N - j) N, (1 + ρ s)) * ‖u' N - u N‖ := by
    intro j
    induction j with
    | zero => intro _; simp
    | succ j ih =>
      intro hj
      have ih := ih (by omega)
      have h3 := olver_10_03 ha hp hρ hu hu' (r := N - (j + 1)) (by omega)
      rw [show N - (j + 1) + 1 = N - j by omega] at h3
      rw [sum_eq_sum_Ico_succ_bot (by omega : N - (j + 1) < N + 1),
        prod_eq_prod_Ico_succ_bot (by omega : N - (j + 1) < N),
        show N - (j + 1) + 1 = N - j by omega]
      have hprod : 0 ≤ ∏ s ∈ Ico (N - j) N, (1 + ρ s) :=
        prod_nonneg fun s _ => by linarith [hρ0 s]
      calc ‖u' (N - (j + 1)) - u (N - (j + 1))‖ + ∑ s ∈ Ico (N - j) (N + 1), ‖u' s - u s‖
          ≤ ρ (N - (j + 1)) * ∑ s ∈ Ico (N - j) (N + 1), ‖u' s - u s‖ +
            ∑ s ∈ Ico (N - j) (N + 1), ‖u' s - u s‖ := by gcongr
        _ = (1 + ρ (N - (j + 1))) * ∑ s ∈ Ico (N - j) (N + 1), ‖u' s - u s‖ := by ring
        _ ≤ (1 + ρ (N - (j + 1))) * ((∏ s ∈ Ico (N - j) N, (1 + ρ s)) * ‖u' N - u N‖) := by
            gcongr; linarith [hρ0 (N - (j + 1))]
        _ = _ := by ring
  have h3 := olver_10_03 ha hp hρ hu hu' hr
  have hS' := hS (N - (r + 1)) (by omega)
  rw [show N - (N - (r + 1)) = r + 1 by omega] at hS'
  rw [← olver_eta_N ha hp hu hu', mul_assoc]
  exact h3.trans (mul_le_mul_of_nonneg_left hS' (hρ0 r))

/-- `E_N` of Olver (10.09): `∑_{j≥0} (1 + ρ_N)⋯(1 + ρ_{N+j−1}) |e_{N+j}/p_{N+j+1}|`. -/
noncomputable def olverGenBound (a b c d m : ℕ → ℂ) (k : ℂ) (ρ : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑' j : ℕ, (∏ s ∈ Ico N (N + j), (1 + ρ s)) *
    ‖genE a b c d m k (N + j) / genP a b c m (N + j + 1)‖

/-- The telescoping bound: if `|wᵣ^{(N+j+1)} − wᵣ^{(N+j)}| ≤ βⱼ` with `∑ βⱼ` convergent and
`wᵣ^{(N)} → wᵣ`, then `|wᵣ − wᵣ^{(N)}| ≤ ∑ βⱼ`. -/
theorem norm_sub_le_tsum_of_steps {u : ℕ → ℂ} {y : ℂ} (hu : Tendsto u atTop (𝓝 y)) {N : ℕ}
    {β : ℕ → ℝ} (hβ : ∀ j, ‖u (N + j + 1) - u (N + j)‖ ≤ β j) (hs : Summable β) :
    ‖y - u N‖ ≤ ∑' j, β j := by
  have htel : ∀ J, u (N + J) - u N = ∑ j ∈ range J, (u (N + j + 1) - u (N + j)) := fun J => by
    induction J with
    | zero => simp
    | succ J ih => rw [sum_range_succ, ← ih, show N + (J + 1) = N + J + 1 by ring]; ring
  have h2 : Tendsto (fun J => u (N + J)) atTop (𝓝 y) :=
    ((tendsto_add_atTop_iff_nat N).mpr hu).congr fun J => by rw [add_comm]
  have h3 : Tendsto (fun J => ‖y - u (N + J)‖) atTop (𝓝 0) := by
    have := (tendsto_const_nhds (x := y)).sub h2
    rw [sub_self] at this
    simpa using this.norm
  have hlim : Tendsto (fun J => ‖y - u (N + J)‖ + ∑ j ∈ range J, β j) atTop
      (𝓝 (0 + ∑' j, β j)) := h3.add hs.hasSum.tendsto_sum_nat
  rw [zero_add] at hlim
  refine ge_of_tendsto' hlim fun J => ?_
  calc ‖y - u N‖ = ‖(y - u (N + J)) + (u (N + J) - u N)‖ := by ring_nf
    _ ≤ ‖y - u (N + J)‖ + ‖u (N + J) - u N‖ := norm_add_le _ _
    _ ≤ ‖y - u (N + J)‖ + ∑ j ∈ range J, β j := by
        gcongr
        rw [htel J]
        exact (norm_sum_le _ _).trans (sum_le_sum fun j _ => hβ j)

/-- **Olver (10.07)–(10.10)**: under the conditions of Theorem 2, for a family of solutions
`w^{(N)}` of (9.05)–(9.07) (`N ≥ N₀`) and bounds `ρ` (10.04), if the series `E_N` (10.09)
converges, then the truncation error satisfies
`|wᵣ − wᵣ^{(N)}| ≤ ρᵣ(1 + ρ_{r+1})⋯(1 + ρ_{N−1}) E_N` for `r < N` and `|w_N| ≤ E_N`. -/
theorem olver_10_07 (ha : ∀ n, 1 ≤ n → a n ≠ 0) {f g h : ℕ → ℂ} (hf : IsRec3 a b c f)
    (hg : IsRec3 a b c g) (hC : casoratian f g 0 ≠ 0) (hh : IsRec3Inh a b c d h)
    (h902 : Tendsto (fun N => ‖∑ r ∈ range (N + 1), m r * g r‖) atTop atTop) {F H k : ℂ}
    (hF : NormSum m f F) (hF0 : F ≠ 0) (hH : NormSum m h H) {u : ℕ → ℕ → ℂ} {N₀ : ℕ}
    (hu : ∀ N, N₀ ≤ N → IsGenBVSol a b c d m k N (u N)) (hgN : ∀ᶠ N in atTop, g N ≠ 0)
    (h908f : Tendsto (fun N => f N / g N * ∑ r ∈ range (N + 1), m r * g r) atTop (𝓝 0))
    (h908h : Tendsto (fun N => h N / g N * ∑ r ∈ range (N + 1), m r * g r) atTop (𝓝 0))
    (hp : ∀ r, 1 ≤ r → genP a b c m r ≠ 0) {ρ : ℕ → ℝ} (hρ : IsRhoBound a b c m ρ) {N : ℕ}
    (hN : N₀ ≤ N) (hE : Summable fun j : ℕ => (∏ s ∈ Ico N (N + j), (1 + ρ s)) *
      ‖genE a b c d m k (N + j) / genP a b c m (N + j + 1)‖) :
    (∀ r, r < N → ‖((k - H) / F * f r + h r) - u N r‖ ≤
      ρ r * (∏ s ∈ Ico (r + 1) N, (1 + ρ s)) * olverGenBound a b c d m k ρ N) ∧
      ‖(k - H) / F * f N + h N‖ ≤ olverGenBound a b c d m k ρ N := by
  have hρ0 := hρ.nonneg hp
  have hconv : ∀ r, Tendsto (fun N => u N r) atTop (𝓝 ((k - H) / F * f r + h r)) :=
    olver_theorem_2 ha hf hg hC hh h902 hF hF0 hH (eventually_atTop.mpr ⟨N₀, hu⟩) hgN h908f h908h
  have hprod0 : ∀ i j, 0 ≤ ∏ s ∈ Ico i j, (1 + ρ s) := fun i j =>
    prod_nonneg fun s _ => by linarith [hρ0 s]
  refine ⟨fun r hr => ?_, ?_⟩
  · have hβ : ∀ j, ‖u (N + j + 1) r - u (N + j) r‖ ≤ ρ r * (∏ s ∈ Ico (r + 1) N, (1 + ρ s)) *
        ((∏ s ∈ Ico N (N + j), (1 + ρ s)) *
          ‖genE a b c d m k (N + j) / genP a b c m (N + j + 1)‖) := fun j => by
      have := olver_10_06 ha hp hρ (hu (N + j) (by omega)) (hu (N + j + 1) (by omega))
        (r := r) (by omega)
      rw [← prod_Ico_consecutive (fun s => 1 + ρ s) (by omega : r + 1 ≤ N)
        (by omega : N ≤ N + j)] at this
      exact this.trans (le_of_eq (by ring))
    have hb := norm_sub_le_tsum_of_steps (u := fun N' => u N' r) (hconv r) hβ (hE.mul_left _)
    rwa [tsum_mul_left] at hb
  · have hβ : ∀ j, ‖u (N + j + 1) N - u (N + j) N‖ ≤ (∏ s ∈ Ico N (N + j), (1 + ρ s)) *
        ‖genE a b c d m k (N + j) / genP a b c m (N + j + 1)‖ := fun j => by
      rcases Nat.eq_zero_or_pos j with hj | hj
      · subst hj
        simp only [add_zero, Ico_self, prod_empty, one_mul]
        rw [olver_eta_N ha hp (hu N hN) (hu (N + 1) (by omega))]
      · have := olver_10_06 ha hp hρ (hu (N + j) (by omega)) (hu (N + j + 1) (by omega))
          (r := N) (by omega)
        refine this.trans ?_
        rw [prod_eq_prod_Ico_succ_bot (by omega : N < N + j)]
        have := hprod0 (N + 1) (N + j)
        have := hρ0 N
        gcongr
        linarith
    have hb := norm_sub_le_tsum_of_steps (u := fun N' => u N' N) (hconv N) hβ hE
    rwa [(hu N hN).2.2, sub_zero] at hb

end Azurite.DLMF
