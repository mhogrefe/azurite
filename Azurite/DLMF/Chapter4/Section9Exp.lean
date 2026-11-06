/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter1.Section12
import Azurite.DLMF.Chapter4.Section9PadeExp

/-!
# DLMF §4.9(ii): Continued fractions for the exponential function

Formalizations of the exponential part of <https://dlmf.nist.gov/4.9>, for every `z ∈ ℂ`. The
convergents are `Cₙ = Aₙ/Bₙ` (`cfA`, `cfB` of §1.12).

* Method (`cf_tendsto_of_err`): if the errors `e^z Bₙ − Ãₙ` of the convergents are
  `γₙ z^{N+1} φ(k, m)` with `γₙ ≠ 0`, then (since `e^z X = Y` forces `X = 0` for polynomials)
  `Bₙ = γₙ Q_{m,k}` and `Ãₙ = γₙ P_{m,k}`, so the convergents are Padé approximants of `e^z`
  (`Section9PadeExp`), which converge along staircases with `k/(m+k) → ½` (`padeExp_tendsto`).
* The errors are computed by induction from the contiguous relations of `φ`
  (`phi_rel_D`, `phi_rel_D'`, `phi_rel_C`).
* 4.9.3, the three continued fractions: `dlmf_4_9_3_one`, `dlmf_4_9_3_two`, `dlmf_4_9_3_three`.
* 4.9.4 (`n ≥ 1`) with 4.9.5 (`eSum`): `dlmf_4_9_4`.

Lorentzen and Waadeland (1992) and Cuyt et al. (2008) are references; §4.9(iii) (powers) is a
reference only.
-/

open Complex Set Filter Topology Finset
open scoped Real Nat

namespace Azurite.DLMF

/-! ### Contiguous relations -/

theorem phi_rel_00 (z : ℂ) : z * expPhi 0 0 z = exp z - 1 := by
  simpa using z_mul_expPhi 0 0 z

theorem phi_rel_0 (β : ℕ) (z : ℂ) :
    z * expPhi 0 (β + 1) z = -1 + (β + 1) * expPhi 0 β z := by
  have := z_mul_expPhi 0 (β + 1) z
  simp at this; linear_combination this

theorem phi_rel_r0 (α : ℕ) (z : ℂ) :
    z * expPhi (α + 1) 0 z = exp z - (α + 1) * expPhi α 0 z := by
  have := z_mul_expPhi (α + 1) 0 z
  simp at this; linear_combination this

theorem phi_rel (α β : ℕ) (z : ℂ) :
    z * expPhi (α + 1) (β + 1) z =
      -(α + 1) * expPhi α (β + 1) z + (β + 1) * expPhi (α + 1) β z := by
  have := z_mul_expPhi (α + 1) (β + 1) z
  simp at this; linear_combination this

/-- `zφ(α+1, β+1) = −(α+β+2)φ(α, β+1) + (β+1)φ(α, β)`. -/
theorem phi_rel_D (α β : ℕ) (z : ℂ) :
    z * expPhi (α + 1) (β + 1) z =
      -(α + β + 2) * expPhi α (β + 1) z + (β + 1) * expPhi α β z := by
  have h1 := phi_rel α β z
  have h2 := expPhi_add α β z
  rw [h1]; linear_combination (-(β + 1) : ℂ) * h2

/-- `zφ(α+1, β+1) = (α+β+2)φ(α+1, β) − (α+1)φ(α, β)`. -/
theorem phi_rel_D' (α β : ℕ) (z : ℂ) :
    z * expPhi (α + 1) (β + 1) z =
      (α + β + 2) * expPhi (α + 1) β z - (α + 1) * expPhi α β z := by
  have h1 := phi_rel α β z
  have h2 := expPhi_add α β z
  rw [h1]; linear_combination (α + 1 : ℂ) * h2

/-- `z²φ(j+2, j+2) = −2(j+2)(2j+3)φ(j+1, j+1) + (j+1)(j+2)φ(j, j)`. -/
theorem phi_rel_C (j : ℕ) (z : ℂ) :
    z ^ 2 * expPhi (j + 2) (j + 2) z =
      -2 * (j + 2) * (2 * j + 3) * expPhi (j + 1) (j + 1) z +
        (j + 1) * (j + 2) * expPhi j j z := by
  have hB := phi_rel_D (j + 1) (j + 1) z
  have hA := phi_rel_D' j (j + 1) z
  have hB' := phi_rel_D j j z
  push_cast at hB hA hB'
  linear_combination z * hB + (-2 * (j + 2) : ℂ) * hA + (j + 2 : ℂ) * hB'

/-! ### The method -/

theorem isPolyFun_cfP {a b : ℂ → ℕ → ℂ} (ha : ∀ i, IsPolyFun fun z => a z i)
    (hb : ∀ i, IsPolyFun fun z => b z i) :
    ∀ i, IsPolyFun (fun z => cfP (a z) (b z) i) ∧ IsPolyFun (fun z => cfQ (a z) (b z) i) := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    match i with
    | 0 => exact ⟨isPolyFun_const 1, isPolyFun_const 0⟩
    | 1 => exact ⟨hb 0, isPolyFun_const 1⟩
    | i + 2 =>
      obtain ⟨p1, q1⟩ := ih (i + 1) (by omega)
      obtain ⟨p0, q0⟩ := ih i (by omega)
      exact ⟨((hb (i + 1)).mul p1).add ((ha (i + 1)).mul p0),
        ((hb (i + 1)).mul q1).add ((ha (i + 1)).mul q0)⟩

theorem cfA_succ_succ {K : Type*} [Field K] (a b : ℕ → K) (r : ℕ) :
    cfA a b (r + 2) = b (r + 2) * cfA a b (r + 1) + a (r + 2) * cfA a b r := rfl

theorem cfB_succ_succ {K : Type*} [Field K] (a b : ℕ → K) (r : ℕ) :
    cfB a b (r + 2) = b (r + 2) * cfB a b (r + 1) + a (r + 2) * cfB a b r := rfl

/-- **The method**: if `e^z Bᵣ − (Aᵣ + g Bᵣ) = γᵣ z^{mᵣ+kᵣ+1} φ(kᵣ, mᵣ)` (eventually) with
`γᵣ ≠ 0`, `kᵣ → ∞` and `kᵣ/(mᵣ+kᵣ) → θ`, then `Bᵣ(z) ≠ 0` eventually and `Aᵣ/Bᵣ → e^z − g(z)`. -/
theorem cf_tendsto_of_err {a b : ℂ → ℕ → ℂ} (ha : ∀ i, IsPolyFun fun z => a z i)
    (hb : ∀ i, IsPolyFun fun z => b z i) {g : ℂ → ℂ} (hg : IsPolyFun g) {m k : ℕ → ℕ}
    {γ : ℕ → ℂ} {θ : ℝ} (hγ : ∀ r, γ r ≠ 0) (hk : Tendsto k atTop atTop)
    (hθ : Tendsto (fun r => (k r : ℝ) / (m r + k r)) atTop (𝓝 θ))
    (hE : ∀ᶠ r in atTop, ∀ z, exp z * cfB (a z) (b z) r - (cfA (a z) (b z) r +
      g z * cfB (a z) (b z) r) = γ r * z ^ (m r + k r + 1) * expPhi (k r) (m r) z) (z : ℂ) :
    (∀ᶠ r in atTop, cfB (a z) (b z) r ≠ 0) ∧
      Tendsto (fun r => cfA (a z) (b z) r / cfB (a z) (b z) r) atTop (𝓝 (exp z - g z)) := by
  have hident : ∀ᶠ r in atTop, ∀ z, cfB (a z) (b z) r = γ r * padeQ (m r) (k r) z ∧
      cfA (a z) (b z) r + g z * cfB (a z) (b z) r = γ r * padeP (m r) (k r) z := by
    filter_upwards [hE] with r hr
    obtain ⟨pA, pB⟩ := isPolyFun_cfP ha hb (r + 1)
    have hX : IsPolyFun fun z => cfB (a z) (b z) r - γ r * padeQ (m r) (k r) z :=
      pB.sub ((isPolyFun_const _).mul (isPolyFun_padeQ _ _))
    have hY : IsPolyFun fun z => (cfA (a z) (b z) r + g z * cfB (a z) (b z) r) -
        γ r * padeP (m r) (k r) z :=
      (pA.add (hg.mul pB)).sub ((isPolyFun_const _).mul (isPolyFun_padeP _ _))
    have key := hX.eq_zero_of_exp_mul hY fun z => by
      have h1 := hr z
      have h2 := padeExp_err (m r) (k r) z
      linear_combination h1 - γ r * h2
    intro z
    have hb0 := key z
    refine ⟨by linear_combination hb0, ?_⟩
    have h1 := hr z
    have h2 := padeExp_err (m r) (k r) z
    rw [sub_eq_zero.mp hb0] at h1
    linear_combination -h1 + γ r * h2 + g z * hb0
  obtain ⟨hQ0, hlim⟩ := padeExp_tendsto hk hθ z
  have hB0 : ∀ᶠ r in atTop, cfB (a z) (b z) r ≠ 0 := by
    filter_upwards [hident, hQ0] with r hr hq
    rw [(hr z).1]; exact mul_ne_zero (hγ r) hq
  refine ⟨hB0, ?_⟩
  have := hlim.sub_const (g z)
  refine this.congr' ?_
  filter_upwards [hident, hB0] with r hr hb'
  obtain ⟨h1, h2⟩ := hr z
  have hq : padeQ (m r) (k r) z ≠ 0 := fun h => hb' (by rw [h1, h, mul_zero])
  rw [show cfA (a z) (b z) r = γ r * padeP (m r) (k r) z - g z * (γ r * padeQ (m r) (k r) z) by
    linear_combination h2 - g z * h1, h1]
  have := hγ r
  field_simp

/-- Staircases with `kᵣ = ⌊r/2⌋` and `mᵣ + kᵣ = r + c` have `kᵣ/(mᵣ+kᵣ) → ½`. -/
theorem staircase_half {m k : ℕ → ℕ} (c : ℝ) (hk : ∀ r, k r = r / 2)
    (hs : ∀ᶠ r in atTop, ((m r + k r : ℕ) : ℝ) = r + c) :
    Tendsto (fun r => (k r : ℝ) / (m r + k r)) atTop (𝓝 (1 / 2)) := by
  have h1 : Tendsto (fun r : ℕ => (r : ℝ) / (r + c)) atTop (𝓝 1) := tendsto_natCast_div_add_atTop c
  have hlo : Tendsto (fun r : ℕ => ((r : ℝ) / (r + c) - 1 / (r + c)) / 2) atTop (𝓝 (1 / 2)) := by
    have h2 : Tendsto (fun r : ℕ => 1 / ((r : ℝ) + c)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right _ c tendsto_natCast_atTop_atTop)
    simpa using (h1.sub h2).div_const 2
  have hhi : Tendsto (fun r : ℕ => (r : ℝ) / (r + c) / 2) atTop (𝓝 (1 / 2)) := by
    simpa using h1.div_const 2
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hhi ?_ ?_
  · filter_upwards [hs, eventually_gt_atTop (⌈-c⌉₊ + 1)] with r hr hr'
    have hpos : (0 : ℝ) < r + c := by
      have := Nat.le_ceil (-c); have : (⌈-c⌉₊ : ℝ) + 1 < r := by exact_mod_cast hr'
      linarith
    push_cast at hr
    rw [hr, hk]
    have : (r : ℝ) - 1 ≤ 2 * ((r / 2 : ℕ) : ℝ) := by
      have := Nat.div_add_mod r 2
      have hm : r % 2 ≤ 1 := by omega
      have : (r : ℝ) = 2 * ((r / 2 : ℕ) : ℝ) + ((r % 2 : ℕ) : ℝ) := by exact_mod_cast this.symm
      have : ((r % 2 : ℕ) : ℝ) ≤ 1 := by exact_mod_cast hm
      linarith
    rw [div_le_div_iff₀ (by norm_num) hpos, div_sub_div_same, div_mul_eq_mul_div, div_le_iff₀ hpos]
    nlinarith
  · filter_upwards [hs, eventually_gt_atTop (⌈-c⌉₊ + 1)] with r hr hr'
    have hpos : (0 : ℝ) < r + c := by
      have := Nat.le_ceil (-c); have : (⌈-c⌉₊ : ℝ) + 1 < r := by exact_mod_cast hr'
      linarith
    push_cast at hr
    rw [hr, hk]
    have : 2 * ((r / 2 : ℕ) : ℝ) ≤ r := by exact_mod_cast Nat.mul_div_le r 2
    rw [div_div, div_le_div_iff₀ hpos (by positivity)]
    nlinarith

/-- The error `F Bᵣ − Aᵣ` satisfies the recurrence of the convergents. -/
theorem cfErr_add_two (a b : ℕ → ℂ) (F : ℂ) (r : ℕ) :
    F * cfB a b (r + 2) - cfA a b (r + 2) =
      b (r + 2) * (F * cfB a b (r + 1) - cfA a b (r + 1)) +
        a (r + 2) * (F * cfB a b r - cfA a b r) := by
  rw [cfA_succ_succ, cfB_succ_succ]; ring

theorem tendsto_half_atTop : Tendsto (fun r : ℕ => r / 2) atTop atTop :=
  Nat.tendsto_div_const_atTop (by norm_num)

/-! ### The second continued fraction of 4.9.3 -/

/-- `aᵣ = (−1)^{r+1} z` in `1 + z/(1 − z/(2 + z/(3 − z/(2 + z/(5 − ⋯)))))`. -/
noncomputable def cf2a (z : ℂ) (r : ℕ) : ℂ := (-1) ^ (r + 1) * z

/-- `b₀ = 1`, `bᵣ = r` (`r` odd), `bᵣ = 2` (`r ≥ 2` even). -/
noncomputable def cf2b (_z : ℂ) (r : ℕ) : ℂ := if r = 0 then 1 else if r % 2 = 1 then (r : ℂ) else 2

theorem cf2_err (j : ℕ) :
    (∀ z, exp z * cfB (cf2a z) (cf2b z) (2 * j) - cfA (cf2a z) (cf2b z) (2 * j) =
      (-1) ^ j / (j ! : ℂ) * z ^ (2 * j + 1) * expPhi j j z) ∧
    (∀ z, exp z * cfB (cf2a z) (cf2b z) (2 * j + 1) - cfA (cf2a z) (cf2b z) (2 * j + 1) =
      (-1) ^ j / (j ! : ℂ) * z ^ (2 * j + 2) * expPhi j (j + 1) z) := by
  induction j with
  | zero =>
    refine ⟨fun z => ?_, fun z => ?_⟩
    · simp only [cfA, cfB, cfP, cfQ, cf2b]
      have := phi_rel_00 z
      simp; linear_combination -this
    · simp only [cfA, cfB, cfP, cfQ, cf2a, cf2b]
      have h0 := phi_rel_00 z
      have h1 := phi_rel_0 0 z
      simp at h1 ⊢
      linear_combination -z * h1 - h0
  | succ j ih =>
    obtain ⟨h0, h1⟩ := ih
    have hfac : ((j + 1)! : ℂ) = (j + 1) * j ! := by push_cast [Nat.factorial_succ]; ring
    have hj : ((j : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero j
    have hjf : (j ! : ℂ) ≠ 0 := by exact_mod_cast j.factorial_ne_zero
    set γ := (-1 : ℂ) ^ j / (j ! : ℂ)
    have hγ1 : (-1 : ℂ) ^ (j + 1) / ((j + 1)! : ℂ) * (j + 1) = -γ := by
      rw [hfac, pow_succ]; field_simp; simp only [γ]; field_simp
    have hE2 : ∀ z, exp z * cfB (cf2a z) (cf2b z) (2 * (j + 1)) -
        cfA (cf2a z) (cf2b z) (2 * (j + 1)) =
        (-1) ^ (j + 1) / ((j + 1)! : ℂ) * z ^ (2 * (j + 1) + 1) * expPhi (j + 1) (j + 1) z := by
      intro z
      rw [show 2 * (j + 1) = 2 * j + 2 by ring, cfErr_add_two, h0, h1]
      have hb : cf2b z (2 * j + 2) = 2 := by
        simp only [cf2b]; split_ifs <;> first | contradiction | omega | ring1
      have ha : cf2a z (2 * j + 2) = -z := by
        simp only [cf2a]; rw [show 2 * j + 2 + 1 = 2 * (j + 1) + 1 by ring, pow_succ, pow_mul]
        norm_num
      rw [hb, ha]
      have hB := phi_rel_D j j z
      linear_combination (-((-1) ^ (j + 1) / ((j + 1)! : ℂ)) * z ^ (2 * j + 2)) * hB +
        (2 * z ^ (2 * j + 2) * expPhi j (j + 1) z - z ^ (2 * j + 2) * expPhi j j z) * hγ1
    refine ⟨hE2, fun z => ?_⟩
    rw [show 2 * (j + 1) + 1 = 2 * j + 1 + 2 by ring, cfErr_add_two,
      show 2 * j + 1 + 1 = 2 * (j + 1) by ring, hE2, h1]
    have hb : cf2b z (2 * j + 1 + 2) = 2 * j + 3 := by
      simp only [cf2b]; split_ifs <;> first | contradiction | omega | (push_cast; ring)
    have ha : cf2a z (2 * j + 1 + 2) = z := by
      simp only [cf2a]; rw [show 2 * j + 1 + 2 + 1 = 2 * (j + 2) by ring, pow_mul]; norm_num
    rw [hb, ha]
    have hA := phi_rel_D' j (j + 1) z
    push_cast at hA
    linear_combination (-((-1) ^ (j + 1) / ((j + 1)! : ℂ)) * z ^ (2 * j + 3)) * hA +
      (z ^ (2 * j + 3) * expPhi j (j + 1) z) * hγ1

/-- **DLMF 4.9.3** (second form): `e^z = 1 + z/(1 − z/(2 + z/(3 − z/(2 + z/(5 − z/(2 + ⋯))))))`
for every `z ∈ ℂ`: the denominators are eventually nonzero and the convergents tend to `e^z`. -/
theorem dlmf_4_9_3_two (z : ℂ) :
    (∀ᶠ r in atTop, cfB (cf2a z) (cf2b z) r ≠ 0) ∧
      Tendsto (fun r => cfA (cf2a z) (cf2b z) r / cfB (cf2a z) (cf2b z) r) atTop
        (𝓝 (exp z)) := by
  have h := cf_tendsto_of_err (a := cf2a) (b := cf2b) (g := fun _ => 0)
    (m := fun r => (r + 1) / 2) (k := fun r => r / 2)
    (γ := fun r => (-1) ^ (r / 2) / ((r / 2)! : ℂ)) (θ := 1 / 2)
    (fun i => (isPolyFun_const _).mul isPolyFun_id) (fun i => isPolyFun_const _)
    (isPolyFun_const 0)
    (fun r => div_ne_zero (pow_ne_zero _ (by norm_num)) (by exact_mod_cast Nat.factorial_ne_zero _))
    tendsto_half_atTop (staircase_half 0 (fun r => rfl) (Eventually.of_forall fun r => by
      push_cast; rw [← Nat.cast_add, show (r + 1) / 2 + r / 2 = r by omega]; simp))
    (Eventually.of_forall fun r z => by
      rcases Nat.even_or_odd' r with ⟨j, rfl | rfl⟩
      · rw [show (2 * j + 1) / 2 = j by omega, show 2 * j / 2 = j by omega,
          show j + j + 1 = 2 * j + 1 by ring, zero_mul, add_zero]
        exact (cf2_err j).1 z
      · rw [show (2 * j + 1 + 1) / 2 = j + 1 by omega, show (2 * j + 1) / 2 = j by omega,
          show j + 1 + j + 1 = 2 * j + 2 by ring, zero_mul, add_zero]
        exact (cf2_err j).2 z) z
  simpa using h

theorem IsPolyFun.congr' {f g : ℂ → ℂ} (hf : IsPolyFun f) (e : ∀ z, f z = g z) :
    IsPolyFun g := by
  obtain ⟨p, hp⟩ := hf; exact ⟨p, fun z => by rw [← e, hp]⟩

theorem isPolyFun_ite (P : Prop) [Decidable P] {f g : ℂ → ℂ} (hf : IsPolyFun f)
    (hg : IsPolyFun g) : IsPolyFun fun z => if P then f z else g z := by
  split_ifs <;> assumption

theorem isPolyFun_const_mul_pow (c : ℂ) (n : ℕ) : IsPolyFun fun z => c * z ^ n :=
  (isPolyFun_const c).mul (isPolyFun_pow n)

/-! ### The third continued fraction of 4.9.3 -/

/-- `a₁ = z`, `a_{n+1} = z²/(4(4n²−1))` in
`1 + z/(1 − z/2 + (z²/(4·3))/(1 + (z²/(4·15))/(1 + (z²/(4·35))/(1 + ⋯))))`. -/
noncomputable def cf3a (z : ℂ) (r : ℕ) : ℂ :=
  if r = 1 then z else z ^ 2 / (4 * (4 * ((r : ℂ) - 1) ^ 2 - 1))

/-- `b₀ = 1`, `b₁ = 1 − z/2`, `b_{n+1} = 1`. -/
noncomputable def cf3b (z : ℂ) (r : ℕ) : ℂ := if r = 1 then 1 - z / 2 else 1

/-- The coefficient `(−1)^j/(2j)!` of the error of the third form. -/
noncomputable def cf3γ (j : ℕ) : ℂ := (-1) ^ j / ((2 * j)! : ℂ)

theorem cf3γ_ne_zero (j : ℕ) : cf3γ j ≠ 0 :=
  div_ne_zero (pow_ne_zero _ (by norm_num)) (by exact_mod_cast Nat.factorial_ne_zero _)

theorem cf3_err_step (j : ℕ) (z : ℂ) :
    cf3γ (j + 2) * z ^ (2 * (j + 2) + 1) * expPhi (j + 2) (j + 2) z =
      1 * (cf3γ (j + 1) * z ^ (2 * (j + 1) + 1) * expPhi (j + 1) (j + 1) z) +
        z ^ 2 / (4 * (4 * (((j + 2 : ℕ) : ℂ) - 1) ^ 2 - 1)) *
          (cf3γ j * z ^ (2 * j + 1) * expPhi j j z) := by
  have hf1 : ((2 * (j + 1))! : ℂ) = (2 * j + 2) * (2 * j + 1) * (2 * j)! := by
    rw [show 2 * (j + 1) = 2 * j + 1 + 1 by ring, Nat.factorial_succ, Nat.factorial_succ]
    push_cast; ring
  have hf2 : ((2 * (j + 2))! : ℂ) = (2 * j + 4) * (2 * j + 3) * (2 * (j + 1))! := by
    rw [show 2 * (j + 2) = 2 * (j + 1) + 1 + 1 by ring, Nat.factorial_succ, Nat.factorial_succ]
    push_cast; ring
  have hF : ((2 * j)! : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  have h1 : (2 * (j : ℂ) + 1) ≠ 0 := by exact_mod_cast (by omega : 2 * j + 1 ≠ 0)
  have h2 : (2 * (j : ℂ) + 3) ≠ 0 := by exact_mod_cast (by omega : 2 * j + 3 ≠ 0)
  have h3 : ((j : ℂ) + 1) ≠ 0 := by exact_mod_cast (by omega : j + 1 ≠ 0)
  have h4 : ((j : ℂ) + 2) ≠ 0 := by exact_mod_cast (by omega : j + 2 ≠ 0)
  have h5 : (2 * (j : ℂ) + 4) ≠ 0 := by exact_mod_cast (by omega : 2 * j + 4 ≠ 0)
  have hq1 : cf3γ (j + 2) * (-2 * (j + 2) * (2 * j + 3)) = cf3γ (j + 1) := by
    simp only [cf3γ]; rw [hf2, hf1, pow_succ, pow_succ]; field_simp; ring
  have hq2 : cf3γ (j + 2) * ((j + 1) * (j + 2)) =
      cf3γ j / (4 * (4 * (((j + 2 : ℕ) : ℂ) - 1) ^ 2 - 1)) := by
    have hD : (4 * (4 * (((j + 2 : ℕ) : ℂ) - 1) ^ 2 - 1)) = 4 * (2 * j + 1) * (2 * j + 3) := by
      push_cast; ring
    simp only [cf3γ]; rw [hD, hf2, hf1, pow_succ, pow_succ]; field_simp; ring
  have hC := phi_rel_C j z
  rw [show 2 * (j + 2) + 1 = 2 * j + 3 + 2 by ring, show 2 * (j + 1) + 1 = 2 * j + 3 by ring]
  linear_combination cf3γ (j + 2) * z ^ (2 * j + 3) * hC +
    z ^ (2 * j + 3) * expPhi (j + 1) (j + 1) z * hq1 + z ^ (2 * j + 3) * expPhi j j z * hq2

theorem cf3_err (j : ℕ) (z : ℂ) :
    exp z * cfB (cf3a z) (cf3b z) j - cfA (cf3a z) (cf3b z) j =
      cf3γ j * z ^ (2 * j + 1) * expPhi j j z := by
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    match j with
    | 0 =>
      simp only [cfA, cfB, cfP, cfQ, cf3b, cf3γ]
      have := phi_rel_00 z
      simp; linear_combination -this
    | 1 =>
      simp only [cfA, cfB, cfP, cfQ, cf3a, cf3b, cf3γ]
      have h00 := phi_rel_00 z
      have h01 := phi_rel_0 0 z
      have h11 := phi_rel_D 0 0 z
      simp at h01 h11 ⊢
      linear_combination (z ^ 2 / 2) * h11 - z * h01 + (z / 2 - 1) * h00
    | j + 2 =>
      rw [cfErr_add_two, ih (j + 1) (by omega), ih j (by omega)]
      have hb : cf3b z (j + 2) = 1 := by simp [cf3b]
      have ha : cf3a z (j + 2) = z ^ 2 / (4 * (4 * (((j + 2 : ℕ) : ℂ) - 1) ^ 2 - 1)) := by
        simp only [cf3a]; split_ifs <;> first | omega | rfl
      rw [hb, ha]; exact (cf3_err_step j z).symm

/-- **DLMF 4.9.3** (third form):
`e^z = 1 + z/(1 − z/2 + (z²/(4·3))/(1 + (z²/(4·15))/(1 + (z²/(4·35))/(1 + ⋯))))`, the partial
numerators being `z²/(4(4n²−1))`, for every `z ∈ ℂ`. -/
theorem dlmf_4_9_3_three (z : ℂ) :
    (∀ᶠ r in atTop, cfB (cf3a z) (cf3b z) r ≠ 0) ∧
      Tendsto (fun r => cfA (cf3a z) (cf3b z) r / cfB (cf3a z) (cf3b z) r) atTop
        (𝓝 (exp z)) := by
  have hθ : Tendsto (fun r : ℕ => ((r : ℕ) : ℝ) / ((r : ℕ) + (r : ℕ))) atTop (𝓝 (1 / 2)) := by
    refine tendsto_const_nhds.congr' (eventually_atTop.2 ⟨1, fun r hr => ?_⟩)
    have : (r : ℝ) ≠ 0 := by exact_mod_cast (by omega : r ≠ 0)
    field_simp; ring
  have h := cf_tendsto_of_err (a := cf3a) (b := cf3b) (g := fun _ => 0)
    (m := fun r => r) (k := fun r => r) (γ := cf3γ) (θ := 1 / 2)
    (fun i => isPolyFun_ite _ isPolyFun_id
      ((isPolyFun_const_mul_pow (4 * (4 * ((i : ℂ) - 1) ^ 2 - 1))⁻¹ 2).congr'
        fun z => by ring))
    (fun i => isPolyFun_ite _ ((isPolyFun_const 1).sub
      ((isPolyFun_const (1 / 2)).mul isPolyFun_id) |>.congr' fun z => by ring)
      (isPolyFun_const 1))
    (isPolyFun_const 0) cf3γ_ne_zero tendsto_id hθ
    (Eventually.of_forall fun r z => by
      rw [zero_mul, add_zero, show r + r + 1 = 2 * r + 1 by ring]; exact cf3_err r z) z
  simpa using h

/-! ### The first continued fraction of 4.9.3 -/

/-- `a₁ = 1`, `aᵣ = (−1)^{r+1} z` (`r ≥ 2`) in
`1/(1 − z/(1 + z/(2 − z/(3 + z/(2 − z/(5 + ⋯))))))`. -/
noncomputable def cf1a (z : ℂ) (r : ℕ) : ℂ := if r = 1 then 1 else (-1) ^ (r + 1) * z

/-- `b₀ = 0`, `b₁ = 1`, `bᵣ = r − 1` (`r ≥ 2` even), `bᵣ = 2` (`r ≥ 3` odd). -/
noncomputable def cf1b (_z : ℂ) (r : ℕ) : ℂ :=
  if r = 0 then 0 else if r = 1 then 1 else if r % 2 = 0 then (r : ℂ) - 1 else 2

theorem cf1_err (j : ℕ) :
    (∀ z, exp z * cfB (cf1a z) (cf1b z) (2 * j + 1) - cfA (cf1a z) (cf1b z) (2 * j + 1) =
      (-1) ^ j / (j ! : ℂ) * z ^ (2 * j + 1) * expPhi j j z) ∧
    (∀ z, exp z * cfB (cf1a z) (cf1b z) (2 * j + 2) - cfA (cf1a z) (cf1b z) (2 * j + 2) =
      (-1) ^ (j + 1) / (j ! : ℂ) * z ^ (2 * j + 2) * expPhi (j + 1) j z) := by
  induction j with
  | zero =>
    refine ⟨fun z => ?_, fun z => ?_⟩
    · simp only [cfA, cfB, cfP, cfQ, cf1a, cf1b]
      have := phi_rel_00 z
      simp; linear_combination -this
    · simp only [cfA, cfB, cfP, cfQ, cf1a, cf1b]
      have h0 := phi_rel_00 z
      have h1 := phi_rel_r0 0 z
      simp at h1 ⊢
      linear_combination z * h1 - h0
  | succ j ih =>
    obtain ⟨h0, h1⟩ := ih
    have hfac : ((j + 1)! : ℂ) = (j + 1) * j ! := by push_cast [Nat.factorial_succ]; ring
    have hj : ((j : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero j
    have hjf : (j ! : ℂ) ≠ 0 := by exact_mod_cast j.factorial_ne_zero
    have hγ1 : (-1 : ℂ) ^ (j + 1) / ((j + 1)! : ℂ) * (j + 1) = -((-1) ^ j / (j ! : ℂ)) := by
      rw [hfac, pow_succ]; field_simp
    have hγ2 : (-1 : ℂ) ^ (j + 1 + 1) / ((j + 1)! : ℂ) * (j + 1) = (-1) ^ j / (j ! : ℂ) := by
      rw [hfac, pow_succ, pow_succ]; field_simp
    have hE1 : ∀ z, exp z * cfB (cf1a z) (cf1b z) (2 * (j + 1) + 1) -
        cfA (cf1a z) (cf1b z) (2 * (j + 1) + 1) =
        (-1) ^ (j + 1) / ((j + 1)! : ℂ) * z ^ (2 * (j + 1) + 1) * expPhi (j + 1) (j + 1) z := by
      intro z
      rw [show 2 * (j + 1) + 1 = 2 * j + 1 + 2 by ring, cfErr_add_two,
        show 2 * j + 1 + 1 = 2 * j + 2 by ring, h0, h1]
      have hb : cf1b z (2 * j + 1 + 2) = 2 := by
        simp only [cf1b]; split_ifs <;> first | contradiction | omega | ring1
      have ha : cf1a z (2 * j + 1 + 2) = z := by
        simp only [cf1a]; rw [ite_eq_right_iff.mpr (by omega),
          show 2 * j + 1 + 2 + 1 = 2 * (j + 2) by ring, pow_mul]; norm_num
      rw [hb, ha]
      have hA := phi_rel_D' j j z
      linear_combination (-((-1) ^ (j + 1) / ((j + 1)! : ℂ)) * z ^ (2 * j + 2)) * hA +
        (z ^ (2 * j + 2) * expPhi j j z - 2 * z ^ (2 * j + 2) * expPhi (j + 1) j z) * hγ1
    refine ⟨hE1, fun z => ?_⟩
    rw [show 2 * (j + 1) + 2 = 2 * j + 2 + 2 by ring, cfErr_add_two,
      show 2 * j + 2 + 1 = 2 * (j + 1) + 1 by ring, hE1, h1]
    have hb : cf1b z (2 * j + 2 + 2) = 2 * j + 3 := by
      simp only [cf1b]; split_ifs <;> first | contradiction | omega | (push_cast; ring)
    have ha : cf1a z (2 * j + 2 + 2) = -z := by
      simp only [cf1a]; rw [ite_eq_right_iff.mpr (by omega),
        show 2 * j + 2 + 2 + 1 = 2 * (j + 2) + 1 by ring, pow_succ, pow_mul]; norm_num
    rw [hb, ha]
    have hB := phi_rel_D (j + 1) j z
    push_cast at hB
    linear_combination (-((-1) ^ (j + 1 + 1) / ((j + 1)! : ℂ)) * z ^ (2 * j + 3)) * hB +
      (-z ^ (2 * j + 3) * expPhi (j + 1) j z) * hγ2

/-- **DLMF 4.9.3** (first form): `e^z = 1/(1 − z/(1 + z/(2 − z/(3 + z/(2 − z/(5 + ⋯))))))` for
every `z ∈ ℂ`. -/
theorem dlmf_4_9_3_one (z : ℂ) :
    (∀ᶠ r in atTop, cfB (cf1a z) (cf1b z) r ≠ 0) ∧
      Tendsto (fun r => cfA (cf1a z) (cf1b z) r / cfB (cf1a z) (cf1b z) r) atTop
        (𝓝 (exp z)) := by
  have h := cf_tendsto_of_err (a := cf1a) (b := cf1b) (g := fun _ => 0)
    (m := fun r => (r - 1) / 2) (k := fun r => r / 2)
    (γ := fun r => (-1) ^ (r / 2) / (((r - 1) / 2)! : ℂ)) (θ := 1 / 2)
    (fun i => isPolyFun_ite _ (isPolyFun_const 1) ((isPolyFun_const _).mul isPolyFun_id))
    (fun i => isPolyFun_const _) (isPolyFun_const 0)
    (fun r => div_ne_zero (pow_ne_zero _ (by norm_num)) (by exact_mod_cast Nat.factorial_ne_zero _))
    tendsto_half_atTop (staircase_half (-1) (fun r => rfl) (eventually_atTop.2 ⟨1, fun r hr => by
      rw [show (r - 1) / 2 + r / 2 = r - 1 by omega, Nat.cast_sub hr]; simp; ring⟩))
    (eventually_atTop.2 ⟨1, fun r hr z => by
      obtain ⟨i, hi⟩ : ∃ i, r = i + 1 := ⟨r - 1, by omega⟩
      subst hi
      rcases Nat.even_or_odd' i with ⟨j, rfl | rfl⟩
      · rw [show (2 * j + 1 - 1) / 2 = j by omega, show (2 * j + 1) / 2 = j by omega,
          show j + j + 1 = 2 * j + 1 by ring, zero_mul, add_zero]
        exact (cf1_err j).1 z
      · rw [show (2 * j + 1 + 1 - 1) / 2 = j by omega, show (2 * j + 1 + 1) / 2 = j + 1 by omega,
          show j + (j + 1) + 1 = 2 * j + 2 by ring, zero_mul, add_zero,
          show 2 * j + 1 + 1 = 2 * j + 2 by ring]
        exact (cf1_err j).2 z⟩) z
  simpa using h

/-! ### 4.9.4: the tail `e^z − e_{n−1}(z)` -/

/-- **DLMF 4.9.5**: the truncated exponential series `eₙ(z) = Σ_{k=0}^n z^k/k!`. -/
noncomputable def eSum (n : ℕ) (z : ℂ) : ℂ := ∑ k ∈ range (n + 1), z ^ k / (k ! : ℂ)

theorem isPolyFun_eSum (n : ℕ) : IsPolyFun (eSum n) :=
  isPolyFun_sum _ fun k _ =>
    (isPolyFun_const_mul_pow ((k ! : ℂ))⁻¹ k).congr' fun z => by ring

/-- Taylor's formula: `e^z − eₚ(z) = z^{p+1}/p! · φ(0, p)`. -/
theorem exp_sub_eSum (p : ℕ) (z : ℂ) :
    exp z - eSum p z = z ^ (p + 1) / (p ! : ℂ) * expPhi 0 p z := by
  induction p with
  | zero => simp [eSum]; linear_combination -(phi_rel_00 z)
  | succ p ih =>
    have hs : eSum (p + 1) z = eSum p z + z ^ (p + 1) / ((p + 1)! : ℂ) := by
      simp only [eSum]; rw [Finset.sum_range_succ]
    have hfac : ((p + 1)! : ℂ) = (p + 1) * p ! := by push_cast [Nat.factorial_succ]; ring
    have hp : ((p : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero p
    have hpf : (p ! : ℂ) ≠ 0 := by exact_mod_cast p.factorial_ne_zero
    have h := phi_rel_0 p z
    have ih' : (exp z - eSum p z) * p ! = z ^ (p + 1) * expPhi 0 p z := by
      rw [ih]; field_simp
    rw [hs, hfac]
    field_simp
    linear_combination (p + 1) * ih' - z ^ (p + 1) * h

theorem exp_sub_eSum_mul (p : ℕ) (z : ℂ) :
    (exp z - eSum p z) * p ! = z ^ (p + 1) * expPhi 0 p z := by
  have hpf : (p ! : ℂ) ≠ 0 := by exact_mod_cast p.factorial_ne_zero
  rw [exp_sub_eSum]; field_simp

/-- `a₁ = zⁿ`, `a₂ = −n! z`, `a_{2j+1} = j z`, `a_{2j+2} = −(n+j) z` (`j ≥ 1`) in
`zⁿ/(n! − n! z/((n+1) + z/((n+2) − (n+1)z/((n+3) + 2z/((n+4) − (n+2)z/((n+5) + ⋯))))))`. -/
noncomputable def cf4a (n : ℕ) (z : ℂ) (r : ℕ) : ℂ :=
  if r = 1 then z ^ n else if r = 2 then -((n ! : ℂ) * z)
  else if r % 2 = 1 then ((r / 2 : ℕ) : ℂ) * z else -(((n + (r / 2 - 1) : ℕ) : ℂ) * z)

/-- `b₀ = 0`, `b₁ = n!`, `bᵣ = n + r − 1` (`r ≥ 2`). -/
noncomputable def cf4b (n : ℕ) (_z : ℂ) (r : ℕ) : ℂ :=
  if r = 0 then 0 else if r = 1 then (n ! : ℂ) else ((n + r - 1 : ℕ) : ℂ)

theorem cf4_err (p j : ℕ) :
    (∀ z, (exp z - eSum p z) * cfB (cf4a (p + 1) z) (cf4b (p + 1) z) (2 * j + 1) -
        cfA (cf4a (p + 1) z) (cf4b (p + 1) z) (2 * j + 1) =
      (-1) ^ j * z ^ (p + 1 + 2 * j + 1) * expPhi j (p + 1 + j) z) ∧
    (∀ z, (exp z - eSum p z) * cfB (cf4a (p + 1) z) (cf4b (p + 1) z) (2 * j + 2) -
        cfA (cf4a (p + 1) z) (cf4b (p + 1) z) (2 * j + 2) =
      (-1) ^ (j + 1) * z ^ (p + 1 + 2 * j + 2) * expPhi (j + 1) (p + 1 + j) z) := by
  have hfac : (((p + 1)! : ℕ) : ℂ) = (p + 1) * p ! := by push_cast [Nat.factorial_succ]; ring
  have hpf : (p ! : ℂ) ≠ 0 := by exact_mod_cast p.factorial_ne_zero
  have hE1 : ∀ z, (exp z - eSum p z) * cfB (cf4a (p + 1) z) (cf4b (p + 1) z) 1 -
      cfA (cf4a (p + 1) z) (cf4b (p + 1) z) 1 = z ^ (p + 1 + 1) * expPhi 0 (p + 1) z := by
    intro z
    simp only [cfA, cfB, cfP, cfQ, cf4a, cf4b]
    simp only [one_ne_zero, ↓reduceIte, mul_zero, mul_one, zero_add]
    rw [hfac]
    have h := phi_rel_0 p z
    have hT := exp_sub_eSum_mul p z
    linear_combination (p + 1) * hT - z ^ (p + 1) * h
  induction j with
  | zero =>
    refine ⟨fun z => by simpa using hE1 z, fun z => ?_⟩
    rw [show 2 * 0 + 2 = 0 + 2 by rfl, cfErr_add_two, hE1]
    have h0 : (exp z - eSum p z) * cfB (cf4a (p + 1) z) (cf4b (p + 1) z) 0 -
        cfA (cf4a (p + 1) z) (cf4b (p + 1) z) 0 = z ^ (p + 1) / (p ! : ℂ) * expPhi 0 p z := by
      simp only [cfA, cfB, cfP, cfQ, cf4b, ↓reduceIte]; rw [← exp_sub_eSum]; ring
    rw [h0]
    have hb : cf4b (p + 1) z (0 + 2) = p + 2 := by
      simp only [cf4b]; split_ifs <;> first | contradiction | omega | (push_cast; ring)
    have ha : cf4a (p + 1) z (0 + 2) = -((p + 1) * p ! * z) := by
      simp only [cf4a]; split_ifs <;> first | contradiction | omega | (rw [hfac])
    rw [hb, ha]
    have hB := phi_rel_D 0 p z
    push_cast at hB
    have hc : ((p + 1) * p ! * z : ℂ) * (z ^ (p + 1) / p ! * expPhi 0 p z) =
        (p + 1) * z ^ (p + 2) * expPhi 0 p z := by field_simp; ring
    linear_combination z ^ (p + 2) * hB - hc
  | succ j ih =>
    obtain ⟨h1, h2⟩ := ih
    have hE3 : ∀ z, (exp z - eSum p z) * cfB (cf4a (p + 1) z) (cf4b (p + 1) z) (2 * (j + 1) + 1) -
        cfA (cf4a (p + 1) z) (cf4b (p + 1) z) (2 * (j + 1) + 1) =
        (-1) ^ (j + 1) * z ^ (p + 1 + 2 * (j + 1) + 1) * expPhi (j + 1) (p + 1 + (j + 1)) z := by
      intro z
      rw [show 2 * (j + 1) + 1 = 2 * j + 1 + 2 by ring, cfErr_add_two,
        show 2 * j + 1 + 1 = 2 * j + 2 by ring, h1, h2]
      have hb : cf4b (p + 1) z (2 * j + 1 + 2) = p + 2 * j + 3 := by
        simp only [cf4b]; split_ifs <;> first | contradiction | omega |
          (rw [show p + 1 + (2 * j + 1 + 2) - 1 = p + 2 * j + 3 by omega]; push_cast; ring)
      have ha : cf4a (p + 1) z (2 * j + 1 + 2) = (j + 1) * z := by
        simp only [cf4a]; split_ifs <;> first | omega |
          (rw [show (2 * j + 1 + 2) / 2 = j + 1 by omega]; push_cast; ring)
      rw [hb, ha]
      have hA := phi_rel_D' j (p + 1 + j) z
      push_cast at hA
      rw [show p + 1 + (j + 1) = p + 1 + j + 1 by ring]
      linear_combination (-((-1) ^ (j + 1) * z ^ (p + 2 * j + 3))) * hA
    refine ⟨hE3, fun z => ?_⟩
    rw [show 2 * (j + 1) + 2 = 2 * j + 2 + 2 by ring, cfErr_add_two,
      show 2 * j + 2 + 1 = 2 * (j + 1) + 1 by ring, hE3, h2]
    have hb : cf4b (p + 1) z (2 * j + 2 + 2) = p + 2 * j + 4 := by
      simp only [cf4b]; split_ifs <;> first | contradiction | omega |
        (rw [show p + 1 + (2 * j + 2 + 2) - 1 = p + 2 * j + 4 by omega]; push_cast; ring)
    have ha : cf4a (p + 1) z (2 * j + 2 + 2) = -((p + j + 2) * z) := by
      simp only [cf4a]; split_ifs <;> first | omega |
        (rw [show (2 * j + 2 + 2) / 2 - 1 = j + 1 by omega]; push_cast; ring)
    rw [hb, ha]
    have hB := phi_rel_D (j + 1) (p + 1 + j) z
    push_cast at hB
    rw [show p + 1 + (j + 1) = p + 1 + j + 1 by ring]
    linear_combination (-((-1) ^ (j + 1 + 1) * z ^ (p + 2 * j + 4))) * hB

/-- **DLMF 4.9.4**: for `n ≥ 1`,
`e^z − e_{n−1}(z) = zⁿ/(n! − n! z/((n+1) + z/((n+2) − (n+1)z/((n+3) + 2z/((n+4) −`
`(n+2)z/((n+5) + 3z/((n+6) − ⋯)))))))` for every `z ∈ ℂ`. -/
theorem dlmf_4_9_4 (n : ℕ) (hn : 1 ≤ n) (z : ℂ) :
    (∀ᶠ r in atTop, cfB (cf4a n z) (cf4b n z) r ≠ 0) ∧
      Tendsto (fun r => cfA (cf4a n z) (cf4b n z) r / cfB (cf4a n z) (cf4b n z) r) atTop
        (𝓝 (exp z - eSum (n - 1) z)) := by
  obtain ⟨p, rfl⟩ : ∃ p, n = p + 1 := ⟨n - 1, by omega⟩
  rw [show p + 1 - 1 = p by omega]
  refine cf_tendsto_of_err (a := cf4a (p + 1)) (b := cf4b (p + 1)) (g := eSum p)
    (m := fun r => p + 1 + (r - 1) / 2) (k := fun r => r / 2)
    (γ := fun r => (-1) ^ (r / 2)) (θ := 1 / 2)
    (fun i => isPolyFun_ite _ (isPolyFun_pow _) (isPolyFun_ite _
      ((isPolyFun_const (-((p + 1)! : ℂ))).mul isPolyFun_id |>.congr' fun z => by ring)
      (isPolyFun_ite _ ((isPolyFun_const _).mul isPolyFun_id)
        ((isPolyFun_const (-(((p + 1 + (i / 2 - 1) : ℕ) : ℂ)))).mul isPolyFun_id |>.congr'
          fun z => by ring))))
    (fun i => isPolyFun_const _) (isPolyFun_eSum p)
    (fun r => pow_ne_zero _ (by norm_num))
    tendsto_half_atTop (staircase_half p (fun r => rfl) (eventually_atTop.2 ⟨1, fun r hr => by
      rw [show p + 1 + (r - 1) / 2 + r / 2 = r + p by omega]; push_cast; ring⟩))
    (eventually_atTop.2 ⟨1, fun r hr z => ?_⟩) z
  obtain ⟨i, rfl⟩ : ∃ i, r = i + 1 := ⟨r - 1, by omega⟩
  rcases Nat.even_or_odd' i with ⟨j, rfl | rfl⟩
  · rw [show (2 * j + 1 - 1) / 2 = j by omega, show (2 * j + 1) / 2 = j by omega,
      show p + 1 + j + j + 1 = p + 1 + 2 * j + 1 by ring, ← (cf4_err p j).1 z]
    ring
  · rw [show (2 * j + 1 + 1 - 1) / 2 = j by omega, show (2 * j + 1 + 1) / 2 = j + 1 by omega,
      show p + 1 + j + (j + 1) + 1 = p + 1 + 2 * j + 2 by ring,
      show 2 * j + 1 + 1 = 2 * j + 2 by ring, ← (cf4_err p j).2 z]
    ring

end Azurite.DLMF
