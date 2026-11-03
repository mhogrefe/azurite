/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/


import Azurite.DLMF.Chapter2.Section11Terminant

/-!
# DLMF §2.11(iii): the expansion 2.11.13 of the terminant, uniformly in `θ` and `α`

After the rotation of the path (`gamma_mul_eiP_rotated`), with `z = ρe^{iθ}` and `q = ρ + α`,
`F_q(z) = (e^{−z}/2π) e^{i(1−q)θ} ∫_0^∞ e^{−ρu} u^{ρ−1} G(u) du`, `G(u) = u^α/(e^{iθ} + u)`,
an integral with a saddle point at `u = 1`. Laplace's method is carried out by moments:

* `gMom ρ m k = ∫_0^∞ e^{−ρu} u^{ρ+m−1} (u − 1)^k du` satisfies
  `ρ μ_{k+1} = (m + k) μ_k + k μ_{k−1}` (`gMom_rec`, integration by parts), so that
  `μ_k = O(ρ^{−⌈k/2⌉}) μ_0` uniformly for bounded `m` (`gMom_bound`) and, for `m = 0`,
  `μ_k = μ_0 · m_k(1/ρ)` with explicit polynomials `m_k` (`mPoly`, `gMom_eq_mPoly`);
* `G` is expanded about `u = 1` (binomial series for `u^α` with the remainder bound
  `binomRem_bound`, geometric series for `1/(e^{iθ} + u)`), with remainders `O(|u − 1|^N)`;
  `J_expansion` combines the two.

Results:

* **2.11.13** (`dlmf_2_11_13`): `F_{ρ+α}(ρe^{iθ}) ∼ e^{−i(ρ+α)θ}/(1 + e^{−iθ}) ·
  e^{−z}Γ(ρ)ρ^{−ρ}/(2π) · ∑ â_{2s}(θ, α)/ρ^s` as `ρ → ∞`, uniformly for `|θ| ≤ π − δ` and
  `|α| ≤ A`, to every order. DLMF writes the prefactor as `e^{−ρ−z}/(2πρ)^{1/2}`; the two differ by
  `Γ(ρ)ρ^{−ρ}e^ρ(ρ/2π)^{1/2} ∼ 1 + 1/(12ρ) + ⋯` (Stirling's series 5.11.3, not yet available), so
  DLMF's `a_{2s}` are the coefficients of the product of the two series.
* The coefficients (`ahat`) are polynomials in `α` and `1/(1 + e^{iθ})`: `â_0 = 1` (`ahat_zero`),
  `â_2 = ½α(α − 1) − α/(1 + e^{iθ}) + 1/(1 + e^{iθ})²` (`ahat_one`); **2.11.14** (`dlmf_2_11_14`):
  DLMF's `a_2 = â_2 + 1/12`.
* **"Exponentially improved"** (`dlmf_2_11_iii_exp_improved`): with `n` from 2.11.8, the remainder
  of 2.11.10 is `O(ρ^{ℜp−1} e^{−ρ}|e^{−z}|)` uniformly in `|ph z| ≤ π − δ` (via
  `Γ(ρ)ρ^{−ρ} ≤ e^{1−ρ}`, `gMom_zero_le_exp`).
-/

open Filter Topology Set MeasureTheory Complex
open scoped Real Interval

namespace Azurite.DLMF

/-! ### The moments of `e^{−ρu} u^{ρ−1}` about `u = 1` -/

/-- `μ_k(m) = ∫_0^∞ e^{−ρu} u^{ρ+m−1} (u − 1)^k du`. -/
noncomputable def gMom (ρ m : ℝ) (k : ℕ) : ℝ :=
  ∫ u in Ioi (0 : ℝ), Real.exp (-(ρ * u)) * u ^ (ρ + m - 1) * (u - 1) ^ k

theorem integrableOn_rpow_exp {ρ s : ℝ} (hρ : 0 < ρ) (hs : 0 < s) :
    IntegrableOn (fun u : ℝ => Real.exp (-(ρ * u)) * u ^ (s - 1)) (Ioi 0) :=
  (integrableOn_rpow_mul_exp_neg' hs hρ).congr_fun (fun u _ => by ring) measurableSet_Ioi

theorem abs_sub_one_pow_le {u : ℝ} (hu : 0 < u) (k : ℕ) :
    |(u - 1) ^ k| ≤ ∑ j ∈ Finset.range (k + 1), (k.choose j : ℝ) * u ^ j := by
  rw [abs_pow]
  calc |u - 1| ^ k ≤ (u + 1) ^ k := by
        gcongr; rw [abs_le]; constructor <;> linarith
    _ = _ := by
        rw [add_pow]; simp only [one_pow, mul_one]
        exact Finset.sum_congr rfl fun j _ => mul_comm _ _

theorem integrableOn_gMom {ρ m : ℝ} (hρ : 0 < ρ) (hm : 0 < ρ + m) (k : ℕ) :
    IntegrableOn (fun u : ℝ => Real.exp (-(ρ * u)) * u ^ (ρ + m - 1) * (u - 1) ^ k) (Ioi 0) := by
  have hint : IntegrableOn (fun u : ℝ => ∑ j ∈ Finset.range (k + 1),
      (k.choose j : ℝ) * (Real.exp (-(ρ * u)) * u ^ (ρ + m + j - 1))) (Ioi 0) :=
    integrable_finsetSum _ fun j _ =>
      (integrableOn_rpow_exp hρ (by positivity : 0 < ρ + m + j)).const_mul _
  refine hint.mono' ?_ ?_
  · refine ContinuousOn.aestronglyMeasurable (fun u hu => ?_) measurableSet_Ioi
    have hu0 : u ≠ 0 := (ne_of_lt hu).symm
    have c1 : ContinuousAt (fun u : ℝ => Real.exp (-(ρ * u))) u := by fun_prop
    have c2 : ContinuousAt (fun u : ℝ => u ^ (ρ + m - 1)) u :=
      Real.continuousAt_rpow_const _ _ (Or.inl hu0)
    have c3 : ContinuousAt (fun u : ℝ => (u - 1) ^ k) u := by fun_prop
    exact ((c1.mul c2).mul c3).continuousWithinAt
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun u hu => ?_)
    have hu0 : (0 : ℝ) < u := hu
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (Real.exp_pos _),
      abs_of_pos (Real.rpow_pos_of_pos hu0 _)]
    calc Real.exp (-(ρ * u)) * u ^ (ρ + m - 1) * |(u - 1) ^ k|
        ≤ Real.exp (-(ρ * u)) * u ^ (ρ + m - 1) *
          ∑ j ∈ Finset.range (k + 1), (k.choose j : ℝ) * u ^ j := by
          gcongr; exact abs_sub_one_pow_le hu0 k
      _ = _ := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [show ρ + m + j - 1 = (ρ + m - 1) + j by ring, Real.rpow_add hu0,
            Real.rpow_natCast]
          ring

theorem gMom_nonneg_zero {ρ m : ℝ} : 0 ≤ gMom ρ m 0 := by
  unfold gMom
  refine setIntegral_nonneg measurableSet_Ioi fun u hu => ?_
  have : (0 : ℝ) < u := hu
  positivity

/-- **The moment recursion**: `ρ μ_{k+1} = (m + k) μ_k + k μ_{k−1}`. -/
theorem gMom_rec {ρ m : ℝ} (hρ : 0 < ρ) (hm : 0 < ρ + m) (k : ℕ) :
    ρ * gMom ρ m (k + 1) = (m + k) * gMom ρ m k + k * gMom ρ m (k - 1) := by
  set f : ℝ → ℝ := fun u => Real.exp (-(ρ * u)) * u ^ (ρ + m) * (u - 1) ^ k
  set g : ℕ → ℝ → ℝ := fun j u => Real.exp (-(ρ * u)) * u ^ (ρ + m - 1) * (u - 1) ^ j
  set f' : ℝ → ℝ := fun u => -ρ * g (k + 1) u + (m + k) * g k u + k * g (k - 1) u
  have hd : ∀ u ∈ Ioi (0 : ℝ), HasDerivAt f (f' u) u := by
    intro u hu
    have hu0 : (0 : ℝ) < u := hu
    have h1 : HasDerivAt (fun u : ℝ => Real.exp (-(ρ * u))) (Real.exp (-(ρ * u)) * (-ρ)) u := by
      simpa using ((hasDerivAt_id u).const_mul ρ).neg.exp
    have h2 := Real.hasDerivAt_rpow_const (x := u) (p := ρ + m) (Or.inl hu0.ne')
    have h3 : HasDerivAt (fun u : ℝ => (u - 1) ^ k) (k * (u - 1) ^ (k - 1)) u := by
      exact (((hasDerivAt_id' u).sub_const (1 : ℝ)).pow k).congr_deriv (by ring)
    have := (h1.mul h2).mul h3
    convert this using 1
    simp only [f', g, Pi.mul_apply]
    have hpow : u ^ (ρ + m) = u ^ (ρ + m - 1) * u := by
      rw [← Real.rpow_add_one hu0.ne']; ring_nf
    rw [hpow]
    rcases k with _ | k
    · simp; ring
    · simp only [Nat.add_sub_cancel, pow_succ]
      push_cast
      ring
  have hint : ∀ j, IntegrableOn (g j) (Ioi 0) := fun j => integrableOn_gMom hρ hm j
  have hint' : IntegrableOn f' (Ioi 0) :=
    (((hint (k + 1)).const_mul (-ρ)).add ((hint k).const_mul _)).add ((hint (k - 1)).const_mul _)
  have hcont : ContinuousWithinAt f (Ici 0) 0 := by
    refine ContinuousAt.continuousWithinAt ?_
    have c1 : ContinuousAt (fun u : ℝ => Real.exp (-(ρ * u))) 0 := by fun_prop
    have c2 : ContinuousAt (fun u : ℝ => u ^ (ρ + m)) 0 :=
      Real.continuousAt_rpow_const _ _ (Or.inr hm.le)
    have c3 : ContinuousAt (fun u : ℝ => (u - 1) ^ k) 0 := by fun_prop
    exact (c1.mul c2).mul c3
  have hlim : Tendsto f atTop (𝓝 0) := by
    have hsum : Tendsto (fun u : ℝ => ∑ j ∈ Finset.range (k + 1), (k.choose j : ℝ) *
        (u ^ (ρ + m + j) * Real.exp (-ρ * u))) atTop (𝓝 0) := by
      rw [show (0 : ℝ) = ∑ j ∈ Finset.range (k + 1), (k.choose j : ℝ) * 0 by simp]
      exact tendsto_finsetSum _ fun j _ =>
        (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero _ _ hρ).const_mul _
    refine squeeze_zero_norm' ?_ hsum
    filter_upwards [eventually_gt_atTop 0] with u hu
    simp only [f]
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (Real.exp_pos _),
      abs_of_pos (Real.rpow_pos_of_pos hu _)]
    calc Real.exp (-(ρ * u)) * u ^ (ρ + m) * |(u - 1) ^ k|
        ≤ Real.exp (-(ρ * u)) * u ^ (ρ + m) *
          ∑ j ∈ Finset.range (k + 1), (k.choose j : ℝ) * u ^ j := by
          gcongr; exact abs_sub_one_pow_le hu k
      _ = _ := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [Real.rpow_add hu (ρ + m) (j : ℝ), Real.rpow_natCast, neg_mul]
          ring
  have h := integral_Ioi_of_hasDerivAt_of_tendsto hcont hd hint' hlim
  have hf0 : f 0 = 0 := by
    simp only [f]; rw [Real.zero_rpow hm.ne']; ring
  rw [hf0, sub_zero] at h
  have i1 : IntegrableOn (fun u => -ρ * g (k + 1) u) (Ioi 0) := (hint _).const_mul _
  have i2 : IntegrableOn (fun u => (m + k) * g k u) (Ioi 0) := (hint _).const_mul _
  have i3 : IntegrableOn (fun u => (k : ℝ) * g (k - 1) u) (Ioi 0) := (hint _).const_mul _
  have i12 : IntegrableOn (fun u => -ρ * g (k + 1) u + (m + k) * g k u) (Ioi 0) := i1.add i2
  have e : ∫ u in Ioi (0 : ℝ), f' u = -ρ * gMom ρ m (k + 1) + (m + k) * gMom ρ m k +
      k * gMom ρ m (k - 1) := by
    simp only [f']
    rw [integral_add i12 i3, integral_add i1 i2, MeasureTheory.integral_const_mul,
      MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
    rfl
  linarith

/-- The shift `μ_0(m + 1) = (1 + m/ρ) μ_0(m)`. -/
theorem gMom_succ_zero {ρ m : ℝ} (hρ : 0 < ρ) (hm : 0 < ρ + m) :
    gMom ρ (m + 1) 0 = (1 + m / ρ) * gMom ρ m 0 := by
  have h1 : gMom ρ (m + 1) 0 = gMom ρ m 1 + gMom ρ m 0 := by
    unfold gMom
    rw [← integral_add (integrableOn_gMom hρ hm 1) (integrableOn_gMom hρ hm 0)]
    refine setIntegral_congr_fun measurableSet_Ioi fun u hu => ?_
    have hu0 : (0 : ℝ) < u := hu
    rw [show ρ + (m + 1) - 1 = (ρ + m - 1) + 1 by ring, Real.rpow_add_one hu0.ne']
    ring
  have h2 := gMom_rec hρ hm 0
  simp at h2
  rw [h1, show gMom ρ m 1 = m / ρ * gMom ρ m 0 by field_simp; linarith]
  ring

/-- `μ_k(m) = O(ρ^{−⌈k/2⌉}) μ_0(m)`, uniformly for `|m| ≤ M` and `ρ ≥ 1`. -/
theorem gMom_bound (M : ℝ) (k : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ ρ : ℝ, 1 ≤ ρ → ∀ m : ℝ, |m| ≤ M →
    0 < ρ + m → |gMom ρ m k| ≤ C / ρ ^ ((k + 1) / 2) * gMom ρ m 0 := by
  suffices H : ∀ k : ℕ, (∃ C : ℝ, 0 ≤ C ∧ ∀ ρ : ℝ, 1 ≤ ρ → ∀ m : ℝ, |m| ≤ M →
      0 < ρ + m → |gMom ρ m k| ≤ C / ρ ^ ((k + 1) / 2) * gMom ρ m 0) ∧
      (∃ C : ℝ, 0 ≤ C ∧ ∀ ρ : ℝ, 1 ≤ ρ → ∀ m : ℝ, |m| ≤ M →
      0 < ρ + m → |gMom ρ m (k + 1)| ≤ C / ρ ^ ((k + 2) / 2) * gMom ρ m 0) from (H k).1
  intro k
  induction k with
  | zero =>
    refine ⟨⟨1, zero_le_one, fun ρ _ m _ _ => ?_⟩, ⟨|M|, abs_nonneg _, fun ρ hρ m hm hρm => ?_⟩⟩
    · simp [abs_of_nonneg gMom_nonneg_zero]
    · have h := gMom_rec (by linarith) hρm 0
      simp at h
      have hρ0 : (0 : ℝ) < ρ := by linarith
      have : gMom ρ m 1 = m / ρ * gMom ρ m 0 := by field_simp; linarith
      rw [this, abs_mul, abs_div, abs_of_pos hρ0, abs_of_nonneg gMom_nonneg_zero]
      simp only [Nat.reduceAdd, Nat.reduceDiv, pow_one]
      exact mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right (hm.trans (le_abs_self M))
        hρ0.le) gMom_nonneg_zero
  | succ k ih =>
    obtain ⟨⟨C₀, hC₀, h₀⟩, ⟨C₁, hC₁, h₁⟩⟩ := ih
    refine ⟨⟨C₁, hC₁, h₁⟩, ⟨(|M| + k + 1) * C₁ + (k + 1) * C₀, by positivity,
      fun ρ hρ m hm hρm => ?_⟩⟩
    have hρ0 : (0 : ℝ) < ρ := by linarith
    have hrec := gMom_rec hρ0 hρm (k + 1)
    simp only [Nat.add_sub_cancel] at hrec
    push_cast at hrec
    have e : gMom ρ m (k + 1 + 1) =
        ((m + (k + 1)) * gMom ρ m (k + 1) + (k + 1) * gMom ρ m k) / ρ := by
      field_simp; linarith
    rw [e, abs_div, abs_of_pos hρ0]
    have hμ := gMom_nonneg_zero (ρ := ρ) (m := m)
    have hpow : ρ ^ ((k + 1) / 2) ≤ ρ ^ ((k + 1 + 1) / 2) :=
      pow_le_pow_right₀ hρ (Nat.div_le_div_right (by omega))
    have hpos : 0 < ρ ^ ((k + 1) / 2) := by positivity
    have hm' : |m + (k + 1)| ≤ |M| + k + 1 := by
      have := abs_add_le m (k + 1)
      rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ k + 1)] at this
      linarith [hm.trans (le_abs_self M)]
    have hb1 := h₁ ρ hρ m hm hρm
    have hb0 := h₀ ρ hρ m hm hρm
    have hexp : (k + 1 + 2) / 2 = (k + 1) / 2 + 1 := by omega
    rw [hexp, pow_succ]
    calc |(m + (k + 1)) * gMom ρ m (k + 1) + (k + 1) * gMom ρ m k| / ρ
        ≤ ((|M| + k + 1) * (C₁ / ρ ^ ((k + 1 + 1) / 2) * gMom ρ m 0) +
          (k + 1) * (C₀ / ρ ^ ((k + 1) / 2) * gMom ρ m 0)) / ρ := by
          gcongr
          refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
          · rw [abs_mul]; exact mul_le_mul hm' hb1 (abs_nonneg _) (by positivity)
          · rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ k + 1)]
            exact mul_le_mul_of_nonneg_left hb0 (by positivity)
      _ ≤ ((|M| + k + 1) * (C₁ / ρ ^ ((k + 1) / 2) * gMom ρ m 0) +
          (k + 1) * (C₀ / ρ ^ ((k + 1) / 2) * gMom ρ m 0)) / ρ := by
          gcongr
      _ = _ := by field_simp

/-- `μ_0(j) ≤ 2^j μ_0(0)` for `ρ ≥ j`. -/
theorem gMom_shift_pos {ρ : ℝ} (hρ : 1 ≤ ρ) (j : ℕ) (hj : (j : ℝ) ≤ ρ) :
    gMom ρ j 0 ≤ 2 ^ j * gMom ρ 0 0 := by
  induction j with
  | zero => simp
  | succ j ih =>
    have hρ0 : (0 : ℝ) < ρ := by linarith
    have hj' : (j : ℝ) ≤ ρ := by push_cast at hj; linarith
    have h := gMom_succ_zero hρ0 (m := j) (by positivity)
    push_cast
    rw [h, pow_succ]
    have : 1 + (j : ℝ) / ρ ≤ 2 := by have := div_le_one_of_le₀ hj' hρ0.le; linarith
    calc (1 + (j : ℝ) / ρ) * gMom ρ j 0 ≤ 2 * (2 ^ j * gMom ρ 0 0) :=
          mul_le_mul this (ih hj') gMom_nonneg_zero (by norm_num)
      _ = _ := by ring

/-- `μ_0(−j) ≤ 2^j μ_0(0)` for `ρ ≥ 2j`. -/
theorem gMom_shift_neg {ρ : ℝ} (hρ : 1 ≤ ρ) (j : ℕ) (hj : 2 * (j : ℝ) ≤ ρ) :
    gMom ρ (-j) 0 ≤ 2 ^ j * gMom ρ 0 0 := by
  induction j with
  | zero => simp
  | succ j ih =>
    have hρ0 : (0 : ℝ) < ρ := by linarith
    have hj' : 2 * (j : ℝ) ≤ ρ := by push_cast at hj; linarith
    have hpos : 0 < ρ + -((j : ℝ) + 1) := by push_cast at hj; linarith
    have h := gMom_succ_zero hρ0 (m := -((j : ℝ) + 1)) hpos
    rw [show -((j : ℝ) + 1) + 1 = -(j : ℝ) by ring] at h
    have hf : 1 / 2 ≤ 1 + -((j : ℝ) + 1) / ρ := by
      rw [neg_div, ← sub_eq_add_neg, le_sub_iff_add_le, ← le_sub_iff_add_le', div_le_iff₀ hρ0]
      push_cast at hj; linarith
    push_cast
    rw [pow_succ]
    have hμ := gMom_nonneg_zero (ρ := ρ) (m := -((j : ℝ) + 1))
    have key : gMom ρ (-((j : ℝ) + 1)) 0 ≤ 2 * gMom ρ (-(j : ℝ)) 0 := by
      rw [h]; nlinarith
    calc gMom ρ (-((j : ℝ) + 1)) 0 ≤ 2 * gMom ρ (-(j : ℝ)) 0 := key
      _ ≤ 2 * (2 ^ j * gMom ρ 0 0) := by gcongr; exact ih hj'
      _ = _ := by ring

/-! ### The polynomials `m_k` -/

/-- `m_0 = 1`, `m_1 = 0`, `m_{k+2}(x) = (k + 1) x (m_{k+1}(x) + m_k(x))`, so that
`μ_k(0) = μ_0(0) m_k(1/ρ)`. -/
noncomputable def mPoly : ℕ → Polynomial ℝ
  | 0 => 1
  | 1 => 0
  | k + 2 => Polynomial.C ((k : ℝ) + 1) * Polynomial.X * (mPoly (k + 1) + mPoly k)

theorem gMom_eq_mPoly {ρ : ℝ} (hρ : 0 < ρ) : ∀ k : ℕ,
    gMom ρ 0 k = gMom ρ 0 0 * (mPoly k).eval (1 / ρ) ∧
      gMom ρ 0 (k + 1) = gMom ρ 0 0 * (mPoly (k + 1)).eval (1 / ρ) := by
  intro k
  induction k with
  | zero =>
    refine ⟨by simp [mPoly], ?_⟩
    have h := gMom_rec hρ (m := 0) (by simpa using hρ) 0
    simp at h
    simp [mPoly, h.resolve_left hρ.ne']
  | succ k ih =>
    refine ⟨ih.2, ?_⟩
    have h := gMom_rec hρ (m := 0) (by simpa using hρ) (k + 1)
    simp only [Nat.add_sub_cancel, zero_add] at h
    rw [show k + 1 + 1 = k + 2 by ring, mPoly, Polynomial.eval_mul, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_add]
    have e : gMom ρ 0 (k + 1 + 1) = ((k + 1) * gMom ρ 0 (k + 1) + (k + 1) * gMom ρ 0 k) / ρ := by
      field_simp; push_cast at h; linarith
    rw [show k + 2 = k + 1 + 1 by ring, e, ih.2, ih.1]
    field_simp

theorem mPoly_coeff_eq_zero : ∀ k s : ℕ, 2 * s < k → (mPoly k).coeff s = 0 := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro s hs
    match k, ih, hs with
    | 0, _, hs => omega
    | 1, _, _ => simp [mPoly]
    | k + 2, ih, hs =>
      rw [mPoly, mul_assoc, Polynomial.coeff_C_mul]
      rcases s with _ | s
      · simp
      · rw [Polynomial.coeff_X_mul, Polynomial.coeff_add, ih (k + 1) (by omega) s (by omega),
          ih k (by omega) s (by omega)]
        simp

/-! ### The binomial series of `u^α` about `u = 1` -/

/-- `binom(α, j) = α(α − 1)⋯(α − j + 1)/j!`. -/
noncomputable def binomC (α : ℂ) (j : ℕ) : ℂ := (descPochhammer ℂ j).eval α / j.factorial

theorem binomC_zero (α : ℂ) : binomC α 0 = 1 := by simp [binomC]

theorem binomC_succ (α : ℂ) (j : ℕ) :
    ((j : ℂ) + 1) * binomC α (j + 1) = α * binomC (α - 1) j := by
  unfold binomC
  rw [descPochhammer_succ_left, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_comp,
    Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_one, Nat.factorial_succ]
  have : ((j.factorial : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos j).ne'
  push_cast
  field_simp

/-- The remainder `u^α − ∑_{j<N} binom(α, j)(u − 1)^j`. -/
noncomputable def bRem (α : ℂ) (N : ℕ) (u : ℝ) : ℂ :=
  (u : ℂ) ^ α - ∑ j ∈ Finset.range N, binomC α j * ((u : ℂ) - 1) ^ j

theorem bRem_one (α : ℂ) (N : ℕ) : bRem α (N + 1) 1 = 0 := by
  unfold bRem
  rw [Finset.sum_range_succ']
  simp [binomC_zero]

theorem hasDerivAt_bRem (α : ℂ) (N : ℕ) {u : ℝ} (hu : 0 < u) :
    HasDerivAt (bRem α (N + 1)) (α * bRem (α - 1) N u) u := by
  have hs : (u : ℂ) ∈ slitPlane := Complex.ofReal_mem_slitPlane.mpr hu
  have h1 : HasDerivAt (fun x : ℝ => (x : ℂ) ^ α) (α * (u : ℂ) ^ (α - 1)) u := by
    have := ((hasDerivAt_id (u : ℂ)).cpow_const (c := α) hs).comp_ofReal
    simpa using this
  have h2 : HasDerivAt (fun x : ℝ => ∑ j ∈ Finset.range (N + 1), binomC α j * ((x : ℂ) - 1) ^ j)
      (∑ j ∈ Finset.range (N + 1), binomC α j * ((j : ℂ) * ((u : ℂ) - 1) ^ (j - 1))) u := by
    refine HasDerivAt.fun_sum fun j _ => ?_
    have := ((((hasDerivAt_id (u : ℂ)).sub_const 1).pow j).const_mul (binomC α j)).comp_ofReal
    simpa using this
  have h := h1.sub h2
  convert h using 1
  · funext x; rfl
  rw [Finset.sum_range_succ']
  simp only [Nat.cast_zero, zero_mul, mul_zero, add_zero, Nat.add_sub_cancel]
  unfold bRem
  rw [mul_sub, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  have := binomC_succ α j
  push_cast
  linear_combination (-((u : ℂ) - 1) ^ j) * this

theorem rpow_le_one_add_of_mem_uIcc {u x c : ℝ} (hu : 0 < u) (hx : x ∈ uIcc 1 u) :
    x ^ c ≤ 1 + u ^ c := by
  have hu' : 0 ≤ u ^ c := Real.rpow_nonneg hu.le c
  rcases le_total 1 u with h | h
  · rw [Set.uIcc_of_le h] at hx
    rcases le_total 0 c with hc | hc
    · linarith [Real.rpow_le_rpow (by linarith [hx.1]) hx.2 hc]
    · have := Real.rpow_le_rpow_of_nonpos one_pos hx.1 hc
      rw [Real.one_rpow] at this; linarith
  · rw [Set.uIcc_of_ge h] at hx
    rcases le_total 0 c with hc | hc
    · have := Real.rpow_le_rpow (by linarith [hx.1]) hx.2 hc
      rw [Real.one_rpow] at this; linarith
    · linarith [Real.rpow_le_rpow_of_nonpos hu hx.1 hc]

/-- **The binomial remainder**: `|u^α − ∑_{j<N} binom(α, j)(u − 1)^j| ≤ K |u − 1|^N (1 + u^{ℜα−N})`
for `u > 0`, uniformly for `|α| ≤ A`. -/
theorem binomRem_bound (N : ℕ) : ∀ A : ℝ, 0 ≤ A → ∃ K : ℝ, 0 ≤ K ∧ ∀ α : ℂ, ‖α‖ ≤ A →
    ∀ u : ℝ, 0 < u → ‖bRem α N u‖ ≤ K * |u - 1| ^ N * (1 + u ^ (α.re - N)) := by
  induction N with
  | zero =>
    intro A _
    refine ⟨1, zero_le_one, fun α _ u hu => ?_⟩
    simp only [bRem, Finset.range_zero, Finset.sum_empty, sub_zero, pow_zero, one_mul,
      Nat.cast_zero]
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hu]
    linarith
  | succ N ih =>
    intro A hA
    obtain ⟨K', hK', hK⟩ := ih (A + 1) (by linarith)
    refine ⟨2 * A * K', by positivity, fun α hα u hu => ?_⟩
    have hpos : ∀ x ∈ uIcc 1 u, 0 < x := fun x hx => by
      rcases le_total 1 u with h | h
      · rw [Set.uIcc_of_le h] at hx; linarith [hx.1]
      · rw [Set.uIcc_of_ge h] at hx; linarith [hx.1]
    set c := α.re - ((N + 1 : ℕ) : ℝ)
    have hbound : ∀ x ∈ uIcc 1 u, ‖α * bRem (α - 1) N x‖ ≤
        A * (K' * |u - 1| ^ N * (2 + u ^ c)) := by
      intro x hx
      have hx0 := hpos x hx
      have hα1 : ‖α - 1‖ ≤ A + 1 := (norm_sub_le _ _).trans (by simp; linarith)
      have h1 := hK (α - 1) hα1 x hx0
      have h2 : |x - 1| ≤ |u - 1| := Set.abs_sub_left_of_mem_uIcc hx
      have h3 : x ^ ((α - 1).re - N) ≤ 1 + u ^ c := by
        have := rpow_le_one_add_of_mem_uIcc (c := (α - 1).re - N) hu hx
        convert this using 3
        simp [c]; ring
      rw [norm_mul]
      refine mul_le_mul hα (h1.trans ?_) (norm_nonneg _) hA
      have h4 : 1 + x ^ ((α - 1).re - N) ≤ 2 + u ^ c := by linarith
      exact mul_le_mul (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) h2 N) hK') h4
        (by positivity) (by positivity)
    have hmvt := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := bRem α (N + 1)) (f' := fun x => α * bRem (α - 1) N x) (s := uIcc 1 u)
      (fun x hx => (hasDerivAt_bRem α N (hpos x hx)).hasDerivWithinAt) hbound (convex_uIcc 1 u)
      (Set.left_mem_uIcc) (Set.right_mem_uIcc)
    rw [bRem_one, sub_zero, Real.norm_eq_abs] at hmvt
    refine hmvt.trans ?_
    have hc0 : 0 ≤ u ^ c := Real.rpow_nonneg hu.le c
    rw [pow_succ]
    have hP : 0 ≤ A * K' * (|u - 1| ^ N * |u - 1|) := by positivity
    nlinarith [mul_nonneg hP hc0]

/-! ### Auxiliary bounds -/

theorem norm_binomC_le (α : ℂ) (i : ℕ) : ‖binomC α i‖ ≤ (‖α‖ + i) ^ i := by
  have hd : ∀ n : ℕ, ‖(descPochhammer ℂ n).eval α‖ ≤ (‖α‖ + n) ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [descPochhammer_succ_right, Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X,
        Polynomial.eval_natCast, norm_mul, pow_succ]
      have h1 : ‖α - n‖ ≤ ‖α‖ + (n + 1 : ℕ) := (norm_sub_le _ _).trans (by simp)
      have h2 : (‖α‖ + n) ^ n ≤ (‖α‖ + (n + 1 : ℕ)) ^ n :=
        pow_le_pow_left₀ (by positivity) (by push_cast; linarith) n
      exact mul_le_mul (ih.trans h2) h1 (norm_nonneg _) (by positivity)
  unfold binomC
  rw [norm_div]
  have hf : (1 : ℝ) ≤ ‖((i.factorial : ℕ) : ℂ)‖ := by
    rw [Complex.norm_natCast]; exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero i)
  exact (div_le_self (norm_nonneg _) hf).trans (hd i)

/-- `|e^{iθ} + u| ≥ sin δ` for `u ≥ 0`, `|θ| ≤ π − δ`, `0 < δ ≤ π/2`. -/
theorem norm_cexp_add_ge {δ θ u : ℝ} (hδ : 0 < δ) (hδ' : δ ≤ π / 2) (hθ : |θ| ≤ π - δ)
    (hu : 0 ≤ u) : Real.sin δ ≤ ‖cexp (θ * I) + u‖ := by
  have h := (one_add_ray hδ hδ' (θ := -θ) (by rwa [abs_neg]) hu).2
  have e : cexp (θ * I) + u = cexp (θ * I) * (1 + u * cexp (((-θ : ℝ) : ℂ) * I)) := by
    rw [mul_add, mul_one, mul_left_comm, ← Complex.exp_add]
    push_cast; ring_nf; simp
  rw [e, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
  exact h

theorem cexp_add_ne_zero {δ θ u : ℝ} (hδ : 0 < δ) (hδ' : δ ≤ π / 2) (hθ : |θ| ≤ π - δ)
    (hu : 0 ≤ u) : cexp (θ * I) + u ≠ 0 := by
  have := norm_cexp_add_ge hδ hδ' hθ hu
  have hs : 0 < Real.sin δ := Real.sin_pos_of_pos_of_lt_pi hδ (by linarith [Real.pi_pos])
  intro h; rw [h, norm_zero] at this; linarith

/-- The geometric re-expansion `1/(c + u) = r ∑_{j<N} (−r(u − 1))^j + (−r(u − 1))^N/(c + u)`,
`r = 1/(1 + c)`. -/
theorem inv_cexp_add_eq {c u : ℂ} (hc : 1 + c ≠ 0) (hu : c + u ≠ 0) (N : ℕ) :
    1 / (c + u) = 1 / (1 + c) * ∑ j ∈ Finset.range N, (-(1 / (1 + c) * (u - 1))) ^ j +
      (-(1 / (1 + c) * (u - 1))) ^ N / (c + u) := by
  set x := -(1 / (1 + c) * (u - 1))
  have hx : c + u = (1 + c) * (1 - x) := by simp only [x]; field_simp; ring
  have hgeom : (1 - x) * ∑ j ∈ Finset.range N, x ^ j = 1 - x ^ N := by
    rw [mul_comm, geom_sum_mul_neg]
  have h1x : 1 - x ≠ 0 := fun h => hu (by rw [hx, h, mul_zero])
  clear_value x
  rw [hx]
  calc 1 / ((1 + c) * (1 - x)) = ((1 - x) * ∑ j ∈ Finset.range N, x ^ j + x ^ N) /
        ((1 + c) * (1 - x)) := by rw [hgeom]; ring
    _ = _ := by field_simp

theorem rpow_le_pow_add_pow {u a : ℝ} (hu : 0 < u) {M : ℕ} (ha : |a| ≤ M) :
    u ^ a ≤ u ^ (M : ℝ) + u ^ (-(M : ℝ)) := by
  rw [abs_le] at ha
  have h1 := Real.rpow_nonneg hu.le (M : ℝ)
  have h2 := Real.rpow_nonneg hu.le (-(M : ℝ))
  rcases le_total 1 u with h | h
  · have := Real.rpow_le_rpow_of_exponent_le h ha.2; linarith
  · have := Real.rpow_le_rpow_of_exponent_ge hu h ha.1; linarith

theorem one_add_pow_le {u : ℝ} (hu : 0 ≤ u) {N M : ℕ} (hNM : N ≤ M) :
    (1 + u) ^ N ≤ 2 ^ N * (1 + u ^ M) := by
  rcases le_total 1 u with h | h
  · calc (1 + u) ^ N ≤ (2 * u) ^ N := pow_le_pow_left₀ (by positivity) (by linarith) N
      _ = 2 ^ N * u ^ N := mul_pow _ _ _
      _ ≤ 2 ^ N * (1 + u ^ M) := by
          gcongr; linarith [pow_le_pow_right₀ h hNM]
  · calc (1 + u) ^ N ≤ 2 ^ N := pow_le_pow_left₀ (by positivity) (by linarith) N
      _ ≤ 2 ^ N * (1 + u ^ M) := by
          have : 0 ≤ u ^ M := pow_nonneg hu M
          nlinarith [pow_pos (two_pos (α := ℝ)) N]

/-- `|p(x) − ∑_{s<K} p_s x^s| ≤ D x^K` for `0 ≤ x ≤ 1`. -/
theorem poly_eval_split (p : Polynomial ℝ) (K : ℕ) {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    |p.eval x - ∑ s ∈ Finset.range K, p.coeff s * x ^ s| ≤
      (∑ s ∈ Finset.range (p.natDegree + 1 + K), |p.coeff s|) * x ^ K := by
  set L := p.natDegree + 1 + K
  rw [Polynomial.eval_eq_sum_range' (n := L) (by omega), ← Finset.sum_Ico_eq_sub _ (by omega)]
  calc |∑ s ∈ Finset.Ico K L, p.coeff s * x ^ s| ≤ ∑ s ∈ Finset.Ico K L, |p.coeff s| * x ^ K := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun s hs => ?_)
        rw [abs_mul, abs_of_nonneg (pow_nonneg hx0 s)]
        exact mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hx0 hx1 (Finset.mem_Ico.mp hs).1)
          (abs_nonneg _)
    _ ≤ _ := by
        rw [← Finset.sum_mul]
        gcongr
        exact fun s hs => Finset.mem_range.mpr (Finset.mem_Ico.mp hs).2

/-! ### The coefficients `â_{2s}` and the algebraic decomposition -/

/-- `r = 1/(1 + e^{iθ})`. -/
noncomputable def rTheta (θ : ℝ) : ℂ := 1 / (1 + cexp (θ * I))

/-- The coefficients of the expansion of `F_{ρ+α}(ρe^{iθ})` in powers of `1/ρ` (relative to the
prefactor with `Γ(ρ)ρ^{−ρ}`): `â_{2s} = ∑_{i,j ≤ 2s} binom(α, i)(−r)^j [x^s] m_{i+j}(x)`. -/
noncomputable def ahat (θ : ℝ) (α : ℂ) (s : ℕ) : ℂ :=
  ∑ i ∈ Finset.range (2 * s + 1), ∑ j ∈ Finset.range (2 * s + 1),
    binomC α i * (-rTheta θ) ^ j * ((mPoly (i + j)).coeff s : ℂ)

theorem ahat_eq_sum (θ : ℝ) (α : ℂ) {s N : ℕ} (hN : 2 * s + 1 ≤ N) :
    ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N,
      binomC α i * (-rTheta θ) ^ j * ((mPoly (i + j)).coeff s : ℂ) = ahat θ α s := by
  have hsub : Finset.range (2 * s + 1) ⊆ Finset.range N := fun i hi =>
    Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hi) hN)
  have hz : ∀ i j : ℕ, 2 * s < i + j → binomC α i * (-rTheta θ) ^ j *
      ((mPoly (i + j)).coeff s : ℂ) = 0 := fun i j h => by
    rw [mPoly_coeff_eq_zero _ _ h]; simp
  unfold ahat
  rw [← Finset.sum_subset hsub (fun i _ hi => Finset.sum_eq_zero fun j _ =>
    hz i j (by simp at hi; omega))]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact (Finset.sum_subset hsub (fun j _ hj => hz i j (by simp at hj; omega))).symm

theorem main_identity (θ : ℝ) (α : ℂ) (K : ℕ) (x : ℂ) :
    ∑ i ∈ Finset.range (2 * K), ∑ j ∈ Finset.range (2 * K), binomC α i * rTheta θ *
      (-rTheta θ) ^ j * ∑ s ∈ Finset.range K, ((mPoly (i + j)).coeff s : ℂ) * x ^ s =
    rTheta θ * ∑ s ∈ Finset.range K, ahat θ α s * x ^ s := by
  set f : ℕ → ℕ → ℕ → ℂ := fun i j s =>
    binomC α i * rTheta θ * (-rTheta θ) ^ j * (((mPoly (i + j)).coeff s : ℂ) * x ^ s)
  calc _ = ∑ i ∈ Finset.range (2 * K), ∑ j ∈ Finset.range (2 * K), ∑ s ∈ Finset.range K,
        f i j s := by simp only [f, Finset.mul_sum]
    _ = ∑ i ∈ Finset.range (2 * K), ∑ s ∈ Finset.range K, ∑ j ∈ Finset.range (2 * K),
        f i j s := Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = ∑ s ∈ Finset.range K, ∑ i ∈ Finset.range (2 * K), ∑ j ∈ Finset.range (2 * K),
        f i j s := Finset.sum_comm
    _ = ∑ s ∈ Finset.range K, rTheta θ * (ahat θ α s * x ^ s) := by
        refine Finset.sum_congr rfl fun s hs => ?_
        have hs' := Finset.mem_range.mp hs
        rw [← ahat_eq_sum θ α (N := 2 * K) (by omega)]
        simp only [f, Finset.mul_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        ring
    _ = _ := by rw [Finset.mul_sum]

theorem integrand_decomp {u : ℝ} {c : ℂ} (hc : 1 + c ≠ 0) (hcu : c + u ≠ 0)
    (α : ℂ) (N : ℕ) :
    (u : ℂ) ^ α / (c + u) = ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N,
        binomC α i * (1 / (1 + c)) * (-(1 / (1 + c))) ^ j * ((u : ℂ) - 1) ^ (i + j) +
      ((∑ i ∈ Finset.range N, binomC α i * ((u : ℂ) - 1) ^ i) *
        (-(1 / (1 + c) * ((u : ℂ) - 1))) ^ N + bRem α N u) / (c + u) := by
  have hP : (u : ℂ) ^ α = (∑ i ∈ Finset.range N, binomC α i * ((u : ℂ) - 1) ^ i) + bRem α N u := by
    rw [bRem]; ring
  have hinv := inv_cexp_add_eq hc hcu N
  set P := ∑ i ∈ Finset.range N, binomC α i * ((u : ℂ) - 1) ^ i
  set r := 1 / (1 + c)
  have hE : bRem α N u * (r * ∑ j ∈ Finset.range N, (-(r * ((u : ℂ) - 1))) ^ j +
      (-(r * ((u : ℂ) - 1))) ^ N / (c + u)) = bRem α N u / (c + u) := by
    rw [← hinv]; ring
  have hPP : P * (r * ∑ j ∈ Finset.range N, (-(r * ((u : ℂ) - 1))) ^ j) =
      ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N,
        binomC α i * r * (-r) ^ j * ((u : ℂ) - 1) ^ (i + j) := by
    simp only [P]
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← mul_assoc, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [show -(r * ((u : ℂ) - 1)) = (-r) * ((u : ℂ) - 1) by ring, mul_pow, pow_add]
    ring
  rw [div_eq_mul_one_div, hinv, hP, add_mul, hE, mul_add, hPP]
  ring

/-! ### The expansion of `J` -/

/-- `J(ρ, θ, α) = ∫_0^∞ e^{−ρu} u^{ρ+α−1}/(e^{iθ} + u) du`. -/
noncomputable def Jint (ρ θ : ℝ) (α : ℂ) : ℂ :=
  ∫ u in Ioi (0 : ℝ), cexp (-(ρ * u)) * (u : ℂ) ^ ((ρ : ℂ) + α - 1) / (cexp (θ * I) + u)

theorem norm_rTheta_le {δ θ : ℝ} (hδ : 0 < δ) (hδ' : δ ≤ π / 2) (hθ : |θ| ≤ π - δ) :
    ‖rTheta θ‖ ≤ 1 / Real.sin δ := by
  have h := norm_cexp_add_ge hδ hδ' hθ zero_le_one
  have hs : 0 < Real.sin δ := Real.sin_pos_of_pos_of_lt_pi hδ (by linarith [Real.pi_pos])
  rw [rTheta, norm_div, norm_one, add_comm]
  push_cast at h
  exact one_div_le_one_div_of_le hs h

/-- **The uniform expansion of `J`**: `J = μ_0 r ∑_{s<K} â_{2s}/ρ^s + O(μ_0 ρ^{−K})`, uniformly for
`|θ| ≤ π − δ`, `|α| ≤ A`. -/
theorem J_expansion (K : ℕ) {δ A : ℝ} (hδ : 0 < δ) (hδ' : δ ≤ π / 2) (hA : 0 ≤ A) :
    ∃ C ρ₀ : ℝ, 1 ≤ ρ₀ ∧ ∀ ρ : ℝ, ρ₀ ≤ ρ → ∀ θ : ℝ, |θ| ≤ π - δ → ∀ α : ℂ, ‖α‖ ≤ A →
      ‖Jint ρ θ α - (gMom ρ 0 0 : ℂ) * rTheta θ *
          ∑ s ∈ Finset.range K, ahat θ α s * ((1 / ρ : ℝ) : ℂ) ^ s‖ ≤
        C * gMom ρ 0 0 / ρ ^ K := by
  set N := 2 * K
  set M : ℕ := N + ⌈A⌉₊ + 1
  set sδ := Real.sin δ
  have hs : 0 < sδ := Real.sin_pos_of_pos_of_lt_pi hδ (by linarith [Real.pi_pos])
  obtain ⟨K₁, hK₁, hbin⟩ := binomRem_bound N A hA
  obtain ⟨C₂, hC₂, hmom⟩ := gMom_bound (M : ℝ) N
  set B : ℝ := (A + N + 1) ^ N
  have hB1 : 1 ≤ B := one_le_pow₀ (by linarith [(N.cast_nonneg : (0 : ℝ) ≤ N)])
  set D : ℝ := ∑ k ∈ Finset.range (2 * N),
    ∑ s ∈ Finset.range ((mPoly k).natDegree + 1 + K), |(mPoly k).coeff s|
  have hD : 0 ≤ D := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
  set C₁ : ℝ := N * B * 2 ^ N * (1 / sδ) ^ N / sδ + K₁ / sδ
  have hC₁ : 0 ≤ C₁ := by positivity
  set Cm : ℝ := (N : ℝ) ^ 2 * B * (1 / sδ) ^ (N + 1) * D
  refine ⟨Cm + C₁ * C₂ * (2 + 2 * 2 ^ M), max 1 (2 * M + A + 2), le_max_left _ _,
    fun ρ hρ θ hθ α hα => ?_⟩
  have hρ1 : 1 ≤ ρ := le_trans (le_max_left _ _) hρ
  have hρ0 : 0 < ρ := by linarith
  have hM0 : (0 : ℝ) ≤ M := M.cast_nonneg
  have hρ2 : 2 * (M : ℝ) + A + 2 ≤ ρ := le_trans (le_max_right _ _) hρ
  have hρM : 2 * (M : ℝ) ≤ ρ := by linarith
  set c := cexp (θ * I)
  set r := rTheta θ
  have hr : r = 1 / (1 + c) := rfl
  have hcu : ∀ u : ℝ, 0 ≤ u → c + u ≠ 0 := fun u hu => cexp_add_ne_zero hδ hδ' hθ hu
  have hc1 : 1 + c ≠ 0 := by rw [add_comm]; exact_mod_cast hcu 1 zero_le_one
  have hcuN : ∀ u : ℝ, 0 ≤ u → sδ ≤ ‖c + u‖ := fun u hu => norm_cexp_add_ge hδ hδ' hθ hu
  have hrN : ‖r‖ ≤ 1 / sδ := norm_rTheta_le hδ hδ' hθ
  have hs1 : sδ ≤ 1 := Real.sin_le_one δ
  have hinvs : 1 ≤ 1 / sδ := by rw [le_div_iff₀ hs]; linarith
  set μ0 := gMom ρ 0 0
  have hμ0 : 0 ≤ μ0 := gMom_nonneg_zero
  set w : ℝ → ℝ := fun u => Real.exp (-(ρ * u)) * u ^ (ρ - 1)
  set b : ℕ → ℕ → ℂ := fun i j => binomC α i * r * (-r) ^ j
  set mainF : ℝ → ℂ := fun u => ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N,
    b i j * ((w u * (u - 1) ^ (i + j) : ℝ) : ℂ)
  set f : ℝ → ℂ := fun u => cexp (-(ρ * u)) * (u : ℂ) ^ ((ρ : ℂ) + α - 1) / (c + u)
  set Rem : ℝ → ℂ := fun u => ((∑ i ∈ Finset.range N, binomC α i * ((u : ℂ) - 1) ^ i) *
    (-(r * ((u : ℂ) - 1))) ^ N + bRem α N u) / (c + u)
  set remF : ℝ → ℂ := fun u => ((w u : ℝ) : ℂ) * Rem u
  -- the decomposition
  have hdec : ∀ u : ℝ, 0 < u → f u = mainF u + remF u := by
    intro u hu
    have hcp : (u : ℂ) ^ ((ρ : ℂ) + α - 1) = ((u ^ (ρ - 1) : ℝ) : ℂ) * (u : ℂ) ^ α := by
      rw [show (ρ : ℂ) + α - 1 = ((ρ - 1 : ℝ) : ℂ) + α by push_cast; ring,
        Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hu.ne'), ← Complex.ofReal_cpow hu.le]
    have hd := integrand_decomp (u := u) hc1 (hcu u hu.le) α N
    rw [← hr] at hd
    calc f u = ((w u : ℝ) : ℂ) * ((u : ℂ) ^ α / (c + u)) := by
          simp only [f, w]; rw [hcp]; push_cast; ring
      _ = _ := by
          rw [hd, mul_add]
          congr 1
          simp only [mainF, b, Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
          push_cast; ring
  -- the pointwise bound on the remainder
  have hRem : ∀ u : ℝ, 0 < u →
      ‖Rem u‖ ≤ C₁ * (|u - 1| ^ N * (2 + u ^ (M : ℝ) + u ^ (-(M : ℝ)))) := by
    intro u hu
    have hY : 0 ≤ u ^ (M : ℝ) := Real.rpow_nonneg hu.le _
    have hZ : 0 ≤ u ^ (-(M : ℝ)) := Real.rpow_nonneg hu.le _
    have hX : 0 ≤ |u - 1| ^ N := pow_nonneg (abs_nonneg _) N
    have hnu : ‖(u : ℂ) - 1‖ = |u - 1| := by
      rw [show (u : ℂ) - 1 = ((u - 1 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
        Real.norm_eq_abs]
    have hP : ‖∑ i ∈ Finset.range N, binomC α i * ((u : ℂ) - 1) ^ i‖ ≤
        N * B * 2 ^ N * (1 + u ^ (M : ℝ)) := by
      calc _ ≤ ∑ i ∈ Finset.range N, ‖binomC α i * ((u : ℂ) - 1) ^ i‖ := norm_sum_le _ _
        _ ≤ ∑ i ∈ Finset.range N, B * (1 + u) ^ N := Finset.sum_le_sum fun i hi => by
            have hiN := Finset.mem_range.mp hi
            have hiR : (i : ℝ) ≤ N := by exact_mod_cast hiN.le
            rw [norm_mul, norm_pow, hnu]
            have h1 : ‖binomC α i‖ ≤ B :=
              (norm_binomC_le α i).trans ((pow_le_pow_left₀ (by positivity) (by linarith) i).trans
                (pow_le_pow_right₀ (by linarith [(N.cast_nonneg : (0 : ℝ) ≤ N)]) hiN.le))
            have h2 : |u - 1| ^ i ≤ (1 + u) ^ N :=
              (pow_le_pow_left₀ (abs_nonneg _) (by rw [abs_le]; constructor <;> linarith) i).trans
                (pow_le_pow_right₀ (by linarith) hiN.le)
            exact mul_le_mul h1 h2 (by positivity) (by linarith)
        _ = N * B * (1 + u) ^ N := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring
        _ ≤ N * B * (2 ^ N * (1 + u ^ (M : ℝ))) := by
            gcongr
            rw [Real.rpow_natCast]
            exact one_add_pow_le hu.le (by omega)
        _ = _ := by ring
    have hx : ‖(-(r * ((u : ℂ) - 1))) ^ N‖ ≤ (1 / sδ) ^ N * |u - 1| ^ N := by
      rw [norm_pow, norm_neg, norm_mul, hnu, mul_pow]
      gcongr
    have hE := hbin α hα u hu
    have hre : |α.re - N| ≤ M := by
      have h1 : |α.re| ≤ A := (Complex.abs_re_le_norm α).trans hα
      have h2 : A ≤ ⌈A⌉₊ := Nat.le_ceil A
      rw [abs_le] at h1 ⊢
      simp only [M]; push_cast
      constructor <;> linarith [(N.cast_nonneg : (0 : ℝ) ≤ N)]
    have hwgt := rpow_le_pow_add_pow hu hre
    have hden := hcuN u hu.le
    set a := (N : ℝ) * B * 2 ^ N * (1 / sδ) ^ N
    have ha : 0 ≤ a := by positivity
    simp only [Rem]
    rw [norm_div]
    calc ‖(∑ i ∈ Finset.range N, binomC α i * ((u : ℂ) - 1) ^ i) * (-(r * ((u : ℂ) - 1))) ^ N +
          bRem α N u‖ / ‖c + u‖
        ≤ (a * (1 + u ^ (M : ℝ)) * |u - 1| ^ N + K₁ * |u - 1| ^ N *
            (1 + u ^ (M : ℝ) + u ^ (-(M : ℝ)))) / sδ := by
          refine div_le_div₀ (by positivity) ((norm_add_le _ _).trans (add_le_add ?_ ?_)) hs hden
          · rw [norm_mul]
            calc _ ≤ (N * B * 2 ^ N * (1 + u ^ (M : ℝ))) * ((1 / sδ) ^ N * |u - 1| ^ N) :=
                  mul_le_mul hP hx (norm_nonneg _) (by positivity)
              _ = _ := by simp only [a]; ring
          · refine hE.trans ?_
            exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ ≤ (a * (2 + u ^ (M : ℝ) + u ^ (-(M : ℝ))) * |u - 1| ^ N + K₁ * |u - 1| ^ N *
            (2 + u ^ (M : ℝ) + u ^ (-(M : ℝ)))) / sδ := by
          refine div_le_div_of_nonneg_right ?_ hs.le
          nlinarith [mul_nonneg ha hX, mul_nonneg hK₁ hX, mul_nonneg (mul_nonneg ha hX) hZ]
      _ = _ := by simp only [C₁, a]; field_simp
  -- integrability
  have hρp : 0 < ρ + (M : ℝ) := by linarith
  have hρm : 0 < ρ + -(M : ℝ) := by linarith
  have hρz : 0 < ρ + 0 := by linarith
  set G : ℝ → ℝ := fun u => C₁ * (2 * (Real.exp (-(ρ * u)) * u ^ (ρ + 0 - 1) * (u - 1) ^ N) +
    Real.exp (-(ρ * u)) * u ^ (ρ + (M : ℝ) - 1) * (u - 1) ^ N +
    Real.exp (-(ρ * u)) * u ^ (ρ + -(M : ℝ) - 1) * (u - 1) ^ N)
  have hGi : IntegrableOn G (Ioi 0) :=
    ((((integrableOn_gMom hρ0 hρz N).const_mul 2).add (integrableOn_gMom hρ0 hρp N)).add
      (integrableOn_gMom hρ0 hρm N)).const_mul C₁
  have hNeven : Even N := ⟨K, by omega⟩
  have hremB : ∀ u : ℝ, 0 < u → ‖remF u‖ ≤ G u := by
    intro u hu
    have hw0 : 0 ≤ w u := by simp only [w]; positivity
    simp only [remF]
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hw0]
    refine (mul_le_mul_of_nonneg_left (hRem u hu) hw0).trans (le_of_eq ?_)
    simp only [w, G]
    rw [hNeven.pow_abs, show ρ + 0 - 1 = ρ - 1 by ring,
      show ρ + (M : ℝ) - 1 = (ρ - 1) + M by ring,
      show ρ + -(M : ℝ) - 1 = (ρ - 1) + -(M : ℝ) by ring,
      Real.rpow_add hu, Real.rpow_add hu]
    ring
  have hfc : ContinuousOn f (Ioi 0) := by
    intro u hu
    have hu0 : (0 : ℝ) < u := hu
    refine ContinuousAt.continuousWithinAt ?_
    have h1 : ContinuousAt (fun u : ℝ => cexp (-(ρ * u))) u := by fun_prop
    have h2 : ContinuousAt (fun u : ℝ => (u : ℂ) ^ ((ρ : ℂ) + α - 1)) u :=
      (continuousAt_cpow_const (Complex.ofReal_mem_slitPlane.mpr hu0)).comp
        Complex.continuous_ofReal.continuousAt
    have h3 : ContinuousAt (fun u : ℝ => c + (u : ℂ)) u := by fun_prop
    exact (h1.mul h2).div h3 (hcu u hu0.le)
  have hgk : ∀ k : ℕ, IntegrableOn (fun u : ℝ => ((w u * (u - 1) ^ k : ℝ) : ℂ)) (Ioi 0) := by
    intro k
    refine (integrableOn_gMom hρ0 hρz k).ofReal.congr_fun (fun u _ => ?_) measurableSet_Ioi
    simp only [w]; congr 2; ring_nf
  have hmainI : IntegrableOn mainF (Ioi 0) := by
    simp only [mainF]
    exact integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
      (hgk (i + j)).const_mul _
  have hremm : AEStronglyMeasurable remF (volume.restrict (Ioi 0)) := by
    refine ((hfc.aestronglyMeasurable measurableSet_Ioi).sub
      hmainI.aestronglyMeasurable).congr ?_
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun u hu => ?_)
    simp only [Pi.sub_apply]
    rw [hdec u hu]; ring
  have hremI : IntegrableOn remF (Ioi 0) :=
    hGi.mono' hremm ((ae_restrict_iff' measurableSet_Ioi).mpr
      (Eventually.of_forall fun u hu => hremB u hu))
  -- the integrals
  have hJ : Jint ρ θ α = (∫ u in Ioi (0 : ℝ), mainF u) + ∫ u in Ioi (0 : ℝ), remF u := by
    rw [Jint, ← integral_add hmainI hremI]
    exact setIntegral_congr_fun measurableSet_Ioi fun u hu => hdec u hu
  have hmainInt : ∫ u in Ioi (0 : ℝ), mainF u =
      ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N, b i j * (gMom ρ 0 (i + j) : ℂ) := by
    simp only [mainF]
    rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
      (hgk (i + j)).const_mul _]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_finsetSum _ fun j _ => (hgk (i + j)).const_mul _]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [MeasureTheory.integral_const_mul, integral_complex_ofReal]
    congr 2
    unfold gMom
    refine setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
    simp only [w]; ring_nf
  -- the main term against the expansion
  set x : ℝ := 1 / ρ
  have hx0 : 0 ≤ x := by positivity
  have hx1 : x ≤ 1 := by rw [div_le_one hρ0]; exact hρ1
  have hxK : x ^ K = 1 / ρ ^ K := by simp only [x]; rw [div_pow, one_pow]
  have hb : ∀ i j : ℕ, i < N → j < N → ‖b i j‖ ≤ B * (1 / sδ) ^ (N + 1) := by
    intro i j hi hj
    have hiR : (i : ℝ) ≤ N := by exact_mod_cast hi.le
    have h1 : ‖binomC α i‖ ≤ B :=
      (norm_binomC_le α i).trans ((pow_le_pow_left₀ (by positivity) (by linarith) i).trans
        (pow_le_pow_right₀ (by linarith [(N.cast_nonneg : (0 : ℝ) ≤ N)]) hi.le))
    simp only [b]
    rw [norm_mul, norm_mul, norm_pow, norm_neg]
    calc ‖binomC α i‖ * ‖r‖ * ‖r‖ ^ j ≤ B * (1 / sδ) * (1 / sδ) ^ j := by gcongr
      _ = B * (1 / sδ) ^ (j + 1) := by ring
      _ ≤ B * (1 / sδ) ^ (N + 1) := by gcongr
  have hmainDiff : ‖∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N, b i j * (gMom ρ 0 (i + j) : ℂ) -
      (μ0 : ℂ) * r * ∑ s ∈ Finset.range K, ahat θ α s * ((1 / ρ : ℝ) : ℂ) ^ s‖ ≤
        Cm * μ0 / ρ ^ K := by
    have hid := main_identity θ α K ((1 / ρ : ℝ) : ℂ)
    have e : ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N, b i j * (gMom ρ 0 (i + j) : ℂ) -
        (μ0 : ℂ) * r * ∑ s ∈ Finset.range K, ahat θ α s * ((1 / ρ : ℝ) : ℂ) ^ s =
        (μ0 : ℂ) * ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N, b i j *
          (((mPoly (i + j)).eval x - ∑ s ∈ Finset.range K, (mPoly (i + j)).coeff s * x ^ s : ℝ) :
            ℂ) := by
      rw [mul_assoc, ← hid, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [(gMom_eq_mPoly hρ0 (i + j)).1]
      simp only [b, x]
      push_cast
      ring
    rw [e, norm_mul, Complex.norm_real, Real.norm_of_nonneg hμ0]
    calc μ0 * ‖∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N, b i j *
          (((mPoly (i + j)).eval x - ∑ s ∈ Finset.range K, (mPoly (i + j)).coeff s * x ^ s : ℝ) :
            ℂ)‖
        ≤ μ0 * ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N,
            B * (1 / sδ) ^ (N + 1) * (D * x ^ K) := by
          gcongr
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i hi => ?_)
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j hj => ?_)
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
          refine mul_le_mul (hb i j (Finset.mem_range.mp hi) (Finset.mem_range.mp hj)) ?_
            (abs_nonneg _) (by positivity)
          refine (poly_eval_split _ K hx0 hx1).trans (mul_le_mul_of_nonneg_right ?_ (by positivity))
          refine Finset.single_le_sum
            (f := fun k => ∑ s ∈ Finset.range ((mPoly k).natDegree + 1 + K), |(mPoly k).coeff s|) (fun k _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) ?_
          simp only [Finset.mem_range] at hi hj ⊢; omega
      _ = Cm * μ0 / ρ ^ K := by
          simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Cm, hxK]
          field_simp
  -- the remainder integral
  have hremInt : ‖∫ u in Ioi (0 : ℝ), remF u‖ ≤ C₁ * C₂ * (2 + 2 * 2 ^ M) * μ0 / ρ ^ K := by
    have hK : (N + 1) / 2 = K := by omega
    have h0 := hmom ρ hρ1 0 (by simp) hρz
    have hp := hmom ρ hρ1 M (by rw [abs_of_nonneg hM0]) hρp
    have hm := hmom ρ hρ1 (-(M : ℝ)) (by rw [abs_neg, abs_of_nonneg hM0]) hρm
    rw [hK] at h0 hp hm
    have sp := gMom_shift_pos hρ1 M (by linarith)
    have sm := gMom_shift_neg hρ1 M hρM
    have hρK : 0 < ρ ^ K := by positivity
    calc ‖∫ u in Ioi (0 : ℝ), remF u‖ ≤ ∫ u in Ioi (0 : ℝ), G u :=
          norm_integral_le_of_norm_le hGi ((ae_restrict_iff' measurableSet_Ioi).mpr
            (Eventually.of_forall fun u hu => hremB u hu))
      _ = C₁ * (2 * gMom ρ 0 N + gMom ρ M N + gMom ρ (-(M : ℝ)) N) := by
          have i1 : IntegrableOn (fun u : ℝ =>
              2 * (Real.exp (-(ρ * u)) * u ^ (ρ + 0 - 1) * (u - 1) ^ N)) (Ioi 0) :=
            (integrableOn_gMom hρ0 hρz N).const_mul 2
          have i2 := integrableOn_gMom hρ0 hρp N
          have i3 := integrableOn_gMom hρ0 hρm N
          have i12 : IntegrableOn (fun u : ℝ =>
              2 * (Real.exp (-(ρ * u)) * u ^ (ρ + 0 - 1) * (u - 1) ^ N) +
              Real.exp (-(ρ * u)) * u ^ (ρ + (M : ℝ) - 1) * (u - 1) ^ N) (Ioi 0) := i1.add i2
          simp only [G]
          rw [MeasureTheory.integral_const_mul, integral_add i12 i3, integral_add i1 i2,
            MeasureTheory.integral_const_mul]
          rfl
      _ ≤ C₁ * (2 * (C₂ / ρ ^ K * μ0) + C₂ / ρ ^ K * (2 ^ M * μ0) +
          C₂ / ρ ^ K * (2 ^ M * μ0)) := by
          gcongr
          · exact (le_abs_self _).trans h0
          · exact (le_abs_self _).trans (hp.trans (by gcongr))
          · exact (le_abs_self _).trans (hm.trans (by gcongr))
      _ = _ := by field_simp; ring
  -- conclusion
  rw [hJ, hmainInt]
  calc ‖(∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N, b i j * (gMom ρ 0 (i + j) : ℂ)) +
        (∫ u in Ioi (0 : ℝ), remF u) -
        (μ0 : ℂ) * r * ∑ s ∈ Finset.range K, ahat θ α s * ((1 / ρ : ℝ) : ℂ) ^ s‖
      ≤ ‖∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N, b i j * (gMom ρ 0 (i + j) : ℂ) -
          (μ0 : ℂ) * r * ∑ s ∈ Finset.range K, ahat θ α s * ((1 / ρ : ℝ) : ℂ) ^ s‖ +
        ‖∫ u in Ioi (0 : ℝ), remF u‖ := by
        rw [show ∀ a b c : ℂ, a + b - c = (a - c) + b from fun a b c => by ring]
        exact norm_add_le _ _
    _ ≤ Cm * μ0 / ρ ^ K + C₁ * C₂ * (2 + 2 * 2 ^ M) * μ0 / ρ ^ K := add_le_add hmainDiff hremInt
    _ = _ := by ring

/-! ### 2.11.13 and 2.11.14 -/

/-- `μ_0 = Γ(ρ)ρ^{−ρ}`. -/
theorem gMom_zero_eq_Gamma {ρ : ℝ} (hρ : 0 < ρ) : gMom ρ 0 0 = Real.Gamma ρ * ρ ^ (-ρ) := by
  rw [← integral_rpow_mul_exp_neg_eq hρ hρ]
  unfold gMom
  refine setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
  simp only [add_zero, pow_zero, mul_one]
  ring

/-- The prefactor of 2.11.13 with `Γ(ρ)ρ^{−ρ}/(2π)` in place of `e^{−ρ}/(2πρ)^{1/2}`:
`e^{−i(ρ+α)θ}/(1 + e^{−iθ}) · e^{−z} Γ(ρ)ρ^{−ρ}/(2π)`, `z = ρe^{iθ}`. -/
noncomputable def terminantPref (ρ θ : ℝ) (α : ℂ) : ℂ :=
  cexp (-(((ρ : ℂ) + α) * (θ * I))) / (1 + cexp (-(θ * I))) * cexp (-(ρ * cexp (θ * I))) *
    ((Real.Gamma ρ * ρ ^ (-ρ) : ℝ) : ℂ) / (2 * π)

/-- **DLMF 2.11.13** (with the prefactor `Γ(ρ)ρ^{−ρ}` in place of `e^{−ρ}(2π/ρ)^{1/2}`; the two
differ by Stirling's series 5.11.3): with `z = ρe^{iθ}` and `q = n + p = ρ + α` (2.11.8),
`F_q(z) ∼ e^{−i(ρ+α)θ}/(1 + e^{−iθ}) · e^{−z}Γ(ρ)ρ^{−ρ}/(2π) · ∑ â_{2s}(θ, α)/ρ^s` as `ρ → ∞`,
uniformly for `θ ∈ [−π + δ, π − δ]` and `|α| ≤ A`. -/
theorem dlmf_2_11_13 (K : ℕ) {δ A : ℝ} (hδ : 0 < δ) (hδ' : δ ≤ π / 2) (hA : 0 ≤ A) :
    ∃ C ρ₀ : ℝ, ∀ ρ : ℝ, ρ₀ ≤ ρ → ∀ θ : ℝ, |θ| ≤ π - δ → ∀ α : ℂ, ‖α‖ ≤ A →
      ‖terminant (ρ + α) (polarW ρ θ) -
          terminantPref ρ θ α * ∑ s ∈ Finset.range K, ahat θ α s / (ρ : ℂ) ^ s‖ ≤
        C * ‖terminantPref ρ θ α‖ / ρ ^ K := by
  obtain ⟨C, ρ₀, hρ₀, hJ⟩ := J_expansion K hδ hδ' hA
  refine ⟨2 * max C 0, max ρ₀ (A + 1), fun ρ hρ θ hθ α hα => ?_⟩
  have hρ0' : ρ₀ ≤ ρ := le_trans (le_max_left _ _) hρ
  have hρA : A + 1 ≤ ρ := le_trans (le_max_right _ _) hρ
  have hρ0 : 0 < ρ := by linarith
  have hq : 0 < ((ρ : ℂ) + α).re := by
    have := Complex.abs_re_le_norm α
    rw [abs_le] at this
    simp; linarith [this.1]
  have hθπ : |θ| < π := by linarith
  have hrot := gamma_mul_eiP_rotated hq hρ0 hθπ
  set μ0 := gMom ρ 0 0
  have hμ0 : 0 ≤ μ0 := gMom_nonneg_zero
  have hμΓ : μ0 = Real.Gamma ρ * ρ ^ (-ρ) := gMom_zero_eq_Gamma hρ0
  set J := Jint ρ θ α
  have hJdef : (∫ u in Ioi (0 : ℝ), cexp (-(ρ * u)) * (u : ℂ) ^ ((ρ : ℂ) + α - 1) /
      (cexp (θ * I) + u)) = J := rfl
  rw [hJdef] at hrot
  set S := ∑ s ∈ Finset.range K, ahat θ α s * ((1 / ρ : ℝ) : ℂ) ^ s
  have hS : ∑ s ∈ Finset.range K, ahat θ α s / (ρ : ℂ) ^ s = S := by
    refine Finset.sum_congr rfl fun s _ => ?_
    push_cast; rw [div_eq_mul_one_div, one_div_pow]
  rw [hS]
  set E := J - (μ0 : ℂ) * rTheta θ * S
  have hE : ‖E‖ ≤ max C 0 * μ0 / ρ ^ K :=
    (hJ ρ hρ0' θ hθ α hα).trans (by gcongr; exact le_max_left _ _)
  have hc : cexp (θ * I) ≠ 0 := Complex.exp_ne_zero _
  have h1c : 1 + cexp (θ * I) ≠ 0 := by
    have := cexp_add_ne_zero hδ hδ' hθ zero_le_one; push_cast at this; rwa [add_comm]
  have h1c' : 1 + cexp (-(θ * I)) ≠ 0 := by
    intro h; apply h1c
    have : cexp (θ * I) * (1 + cexp (-(θ * I))) = cexp (θ * I) + 1 := by
      rw [mul_add, mul_one, ← Complex.exp_add]; simp
    rw [add_comm, ← this, h, mul_zero]
  have hπ : (2 * π : ℂ) ≠ 0 := by exact_mod_cast (by positivity : (2 * π : ℝ) ≠ 0)
  have hG : Complex.Gamma ((ρ : ℂ) + α) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos hq
  -- `F = pref · S + (e^{−z} e^{i(1−q)θ}/2π) E`
  have hF : terminant (ρ + α) (polarW ρ θ) = terminantPref ρ θ α * S +
      cexp (-(ρ * cexp (θ * I))) * cexp ((1 - ((ρ : ℂ) + α)) * (θ * I)) / (2 * π) * E := by
    have hphase : cexp ((1 - ((ρ : ℂ) + α)) * (θ * I)) * rTheta θ =
        cexp (-(((ρ : ℂ) + α) * (θ * I))) / (1 + cexp (-(θ * I))) := by
      rw [rTheta, show (1 - ((ρ : ℂ) + α)) * (θ * I) = θ * I + -(((ρ : ℂ) + α) * (θ * I)) by ring,
        Complex.exp_add]
      have : cexp (θ * I) * (1 + cexp (-(θ * I))) = 1 + cexp (θ * I) := by
        rw [mul_add, mul_one, ← Complex.exp_add]; simp; ring
      field_simp
      rw [← this]
    rw [terminant, show Complex.Gamma ((ρ : ℂ) + α) / (2 * π) * eiP ((ρ : ℂ) + α) (polarW ρ θ) =
      (Complex.Gamma ((ρ : ℂ) + α) * eiP ((ρ : ℂ) + α) (polarW ρ θ)) / (2 * π) by ring, hrot,
      show J = (μ0 : ℂ) * rTheta θ * S + E by simp only [E]; ring, terminantPref, ← hμΓ]
    rw [show cexp (-(ρ * cexp (θ * I))) * cexp ((1 - ((ρ : ℂ) + α)) * (θ * I)) *
        ((μ0 : ℂ) * rTheta θ * S + E) / (2 * π) =
        (cexp ((1 - ((ρ : ℂ) + α)) * (θ * I)) * rTheta θ) * cexp (-(ρ * cexp (θ * I))) *
          (μ0 : ℂ) / (2 * π) * S +
        cexp (-(ρ * cexp (θ * I))) * cexp ((1 - ((ρ : ℂ) + α)) * (θ * I)) / (2 * π) * E by ring,
      hphase]
  rw [hF, add_sub_cancel_left]
  -- the norm comparison
  have hratio : ‖cexp (-(ρ * cexp (θ * I))) * cexp ((1 - ((ρ : ℂ) + α)) * (θ * I)) / (2 * π)‖ * μ0 ≤
      2 * ‖terminantPref ρ θ α‖ := by
    have hnorm1 : ‖1 + cexp (-(θ * I))‖ ≤ 2 := by
      refine (norm_add_le _ _).trans ?_
      rw [norm_one, show -((θ : ℂ) * I) = ((-θ : ℝ) : ℂ) * I by push_cast; ring,
        Complex.norm_exp_ofReal_mul_I]; norm_num
    have hph : ‖cexp ((1 - ((ρ : ℂ) + α)) * (θ * I))‖ =
        ‖cexp (-(((ρ : ℂ) + α) * (θ * I)))‖ := by
      rw [Complex.norm_exp, Complex.norm_exp]; congr 1; simp
    have hpos : 0 < ‖1 + cexp (-(θ * I))‖ := norm_pos_iff.mpr h1c'
    set X := ‖cexp (-(ρ * cexp (θ * I)))‖
    set Y := ‖cexp (-(((ρ : ℂ) + α) * (θ * I)))‖
    set Z := ‖1 + cexp (-(θ * I))‖
    set P := ‖(2 * π : ℂ)‖
    have e1 : ‖cexp (-(ρ * cexp (θ * I))) * cexp ((1 - ((ρ : ℂ) + α)) * (θ * I)) / (2 * π)‖ =
        X * Y / P := by rw [norm_div, norm_mul, hph]
    have e2 : ‖terminantPref ρ θ α‖ = Y / Z * X * μ0 / P := by
      rw [terminantPref, ← hμΓ]
      simp only [norm_div, norm_mul, Complex.norm_real, Real.norm_of_nonneg hμ0]
      simp only [P, X, Y, Z, norm_mul, Complex.norm_real]
    rw [e1, e2]
    have hY2 : Y / 2 ≤ Y / Z := div_le_div_of_nonneg_left (norm_nonneg _) hpos hnorm1
    have hP : 0 < P := norm_pos_iff.mpr hπ
    calc X * Y / P * μ0 = 2 * (Y / 2 * X * μ0 / P) := by ring
      _ ≤ 2 * (Y / Z * X * μ0 / P) := by gcongr
  calc ‖cexp (-(ρ * cexp (θ * I))) * cexp ((1 - ((ρ : ℂ) + α)) * (θ * I)) / (2 * π) * E‖
      ≤ ‖cexp (-(ρ * cexp (θ * I))) * cexp ((1 - ((ρ : ℂ) + α)) * (θ * I)) / (2 * π)‖ *
          (max C 0 * μ0 / ρ ^ K) := by rw [norm_mul]; gcongr
    _ = (‖cexp (-(ρ * cexp (θ * I))) * cexp ((1 - ((ρ : ℂ) + α)) * (θ * I)) / (2 * π)‖ * μ0) *
          max C 0 / ρ ^ K := by ring
    _ ≤ (2 * ‖terminantPref ρ θ α‖) * max C 0 / ρ ^ K := by
        gcongr
    _ = _ := by ring

theorem ahat_zero (θ : ℝ) (α : ℂ) : ahat θ α 0 = 1 := by
  simp [ahat, mPoly, binomC_zero]

/-- `â_2 = ½α(α − 1) − α/(1 + e^{iθ}) + 1/(1 + e^{iθ})²`. -/
theorem ahat_one (θ : ℝ) (α : ℂ) :
    ahat θ α 1 = α * (α - 1) / 2 - α * rTheta θ + rTheta θ ^ 2 := by
  have h2 : mPoly 2 = Polynomial.X := by
    show Polynomial.C (((0 : ℕ) : ℝ) + 1) * Polynomial.X * (mPoly 1 + mPoly 0) = _
    simp [mPoly]
  have h3 : (mPoly 3).coeff 1 = 0 := mPoly_coeff_eq_zero 3 1 (by norm_num)
  have h4 : (mPoly 4).coeff 1 = 0 := mPoly_coeff_eq_zero 4 1 (by norm_num)
  have b1 : binomC α 1 = α := by simp [binomC]
  have b2 : binomC α 2 = α * (α - 1) / 2 := by
    simp [binomC, descPochhammer_succ_right, Nat.factorial]
  simp only [ahat, show 2 * 1 + 1 = 3 by rfl, Finset.sum_range_succ, Finset.sum_range_zero,
    zero_add, h2, h3, h4]
  simp [mPoly, b1, b2, binomC_zero, Polynomial.coeff_X, Polynomial.coeff_one]
  ring

/-- **DLMF 2.11.14**: `a_2(θ, α) = (6α² − 6α + 1)/12 − α/(1 + e^{iθ}) + 1/(1 + e^{iθ})²`
`= â_2(θ, α) + 1/12`, where `1/12` is the first coefficient of Stirling's series
`Γ(ρ)ρ^{−ρ} e^ρ (ρ/2π)^{1/2} ∼ 1 + 1/(12ρ) + ⋯` (5.11.3) that converts the prefactor of
`dlmf_2_11_13` into DLMF's `e^{−ρ}/(2πρ)^{1/2}`; `a_0 = â_0 = 1` (`ahat_zero`). -/
theorem dlmf_2_11_14 (θ : ℝ) (α : ℂ) :
    (6 * α ^ 2 - 6 * α + 1) / 12 - α / (1 + cexp (θ * I)) + 1 / (1 + cexp (θ * I)) ^ 2 =
      ahat θ α 1 + 1 / 12 := by
  rw [ahat_one, rTheta]
  simp only [div_eq_mul_inv, one_mul, inv_pow]
  ring

/-! ### Exponential improvement -/

/-- `Γ(ρ)ρ^{−ρ} ≤ e^{1−ρ}` for `ρ ≥ 1` (`u − ln u ≥ 1`). -/
theorem gMom_zero_le_exp {ρ : ℝ} (hρ : 1 ≤ ρ) : gMom ρ 0 0 ≤ Real.exp (1 - ρ) := by
  have hρ0 : 0 < ρ := by linarith
  have hint0 : IntegrableOn (fun x : ℝ => Real.exp (-1 * x)) (Ioi 0) volume :=
    exp_neg_integrableOn_Ioi 0 one_pos
  have hint1 : IntegrableOn (fun x : ℝ => Real.exp (1 - ρ) * Real.exp (-1 * x)) (Ioi 0) volume :=
    Integrable.const_mul hint0 _
  have hint : IntegrableOn (fun u : ℝ => Real.exp (1 - ρ) * Real.exp (-u)) (Ioi 0) volume :=
    IntegrableOn.congr_fun hint1 (fun u _ => by simp only [neg_mul, one_mul]) measurableSet_Ioi
  calc gMom ρ 0 0 ≤ ∫ u in Ioi (0 : ℝ), Real.exp (1 - ρ) * Real.exp (-u) := by
        refine setIntegral_mono_on (integrableOn_gMom hρ0 (by linarith) 0) hint measurableSet_Ioi
          fun u hu => ?_
        have hu0 : (0 : ℝ) < u := hu
        rw [pow_zero, mul_one, Real.rpow_def_of_pos hu0, ← Real.exp_add, ← Real.exp_add]
        apply Real.exp_le_exp.mpr
        have hl := Real.log_le_sub_one_of_pos hu0
        nlinarith
    _ = Real.exp (1 - ρ) := by
        rw [MeasureTheory.integral_const_mul, integral_exp_neg_Ioi_zero, mul_one]

/-- **"Exponentially improved"**: with `n` given by 2.11.8 (`|n + p − ρ| ≤ A`), the remainder of
2.11.10 after `n` terms is `O(ρ^{ℜp−1} e^{−ρ} |e^{−z}|)`, uniformly for `|ph z| ≤ π − δ`; it is
exponentially small (factor `e^{−|z|}`) compared with `E_p(z) ∼ e^{−z}/z`. -/
theorem dlmf_2_11_iii_exp_improved {p : ℂ} (hp : ∀ m : ℕ, p ≠ -m) {δ A : ℝ} (hδ : 0 < δ)
    (hδ' : δ ≤ π / 2) (hA : 0 ≤ A) :
    ∃ C ρ₀ : ℝ, ∀ ρ : ℝ, ρ₀ ≤ ρ → ∀ θ : ℝ, |θ| ≤ π - δ → ∀ n : ℕ, ‖(n : ℂ) + p - ρ‖ ≤ A →
      ‖genExpInt p (polarW ρ θ) - cexp (-cexp (polarW ρ θ)) / cexp (polarW ρ θ) *
          ∑ s ∈ Finset.range n, (-1) ^ s * (ascPochhammer ℂ s).eval p / cexp (polarW ρ θ) ^ s‖ ≤
        C * ρ ^ (p.re - 1) * Real.exp (-ρ) * ‖cexp (-cexp (polarW ρ θ))‖ := by
  obtain ⟨C, ρ₀, hC⟩ := dlmf_2_11_13 0 hδ hδ' hA
  have hs : 0 < Real.sin δ := Real.sin_pos_of_pos_of_lt_pi hδ (by linarith [Real.pi_pos])
  have hG : Complex.Gamma p ≠ 0 := Complex.Gamma_ne_zero hp
  refine ⟨2 * π / ‖Complex.Gamma p‖ * Real.exp (π * |p.im|) * (max C 0 * Real.exp (π * A) /
    Real.sin δ * Real.exp 1 / (2 * π)), max ρ₀ 1, fun ρ hρ θ hθ n hn => ?_⟩
  have hρ1 : 1 ≤ ρ := le_trans (le_max_right _ _) hρ
  have hρ0 : 0 < ρ := by linarith
  set w := polarW ρ θ
  set α : ℂ := (n : ℂ) + p - ρ
  have hT := hC ρ (le_trans (le_max_left _ _) hρ) θ hθ α hn
  simp only [Finset.range_zero, Finset.sum_empty, mul_zero, sub_zero, pow_zero, div_one] at hT
  have hq : (ρ : ℂ) + α = n + p := by simp only [α]; ring
  rw [hq] at hT
  rw [dlmf_2_11_10 hp w n, add_sub_cancel_left]
  -- the prefactor
  have hpref : ‖terminantPref ρ θ α‖ ≤ Real.exp (π * A) / Real.sin δ *
      ‖cexp (-cexp w)‖ * Real.exp (1 - ρ) / (2 * π) := by
    have h1 : ‖cexp (-(((ρ : ℂ) + α) * (θ * I)))‖ ≤ Real.exp (π * A) := by
      rw [Complex.norm_exp]
      apply Real.exp_le_exp.mpr
      have him : (-(((ρ : ℂ) + α) * (θ * I))).re = θ * α.im := by simp; ring
      rw [him]
      have := Complex.abs_im_le_norm α
      have hθπ : |θ| ≤ π := by linarith
      calc θ * α.im ≤ |θ * α.im| := le_abs_self _
        _ = |θ| * |α.im| := abs_mul _ _
        _ ≤ π * A := mul_le_mul hθπ (this.trans hn) (abs_nonneg _) Real.pi_pos.le
    have h2 : Real.sin δ ≤ ‖1 + cexp (-(θ * I))‖ := by
      have := norm_cexp_add_ge hδ hδ' (θ := -θ) (by rwa [abs_neg]) zero_le_one
      push_cast at this; rwa [add_comm, neg_mul] at this
    have h3 : cexp (-(ρ * cexp (θ * I))) = cexp (-cexp w) := by rw [cexp_polarW hρ0]
    have h4 := gMom_zero_le_exp hρ1
    rw [gMom_zero_eq_Gamma hρ0] at h4
    have hΓ : 0 ≤ Real.Gamma ρ * ρ ^ (-ρ) := by
      have := Real.Gamma_pos_of_pos hρ0; positivity
    rw [terminantPref, h3, norm_div, norm_mul, norm_mul, norm_div, Complex.norm_real,
      Real.norm_of_nonneg hΓ, show ‖(2 * π : ℂ)‖ = 2 * π by
        rw [norm_mul, Complex.norm_two, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le] ]
    have hYZ : ‖cexp (-(((ρ : ℂ) + α) * (θ * I)))‖ / ‖1 + cexp (-(θ * I))‖ ≤
        Real.exp (π * A) / Real.sin δ := div_le_div₀ (by positivity) h1 hs h2
    exact div_le_div_of_nonneg_right (mul_le_mul (mul_le_mul_of_nonneg_right hYZ (norm_nonneg _))
      h4 hΓ (by positivity)) (by positivity)
  -- assemble
  have hpw : ‖cexp ((p - 1) * w)‖ ≤ ρ ^ (p.re - 1) * Real.exp (π * |p.im|) := by
    rw [Complex.norm_exp, show ((p - 1) * w).re = (p.re - 1) * Real.log ρ - p.im * θ by
      simp [w, polarW], Real.exp_sub, Real.rpow_def_of_pos hρ0, mul_comm (Real.log ρ)]
    rw [div_eq_mul_inv, ← Real.exp_neg]
    gcongr
    have hθπ : |θ| ≤ π := by linarith
    calc -(p.im * θ) ≤ |p.im * θ| := neg_le_abs _
      _ = |p.im| * |θ| := abs_mul _ _
      _ ≤ |p.im| * π := mul_le_mul_of_nonneg_left hθπ (abs_nonneg _)
      _ = π * |p.im| := by ring
  have hTn : ‖terminant (n + p) w‖ ≤ max C 0 * ‖terminantPref ρ θ α‖ :=
    hT.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
  rw [norm_mul, norm_mul, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, norm_div,
    show ‖(2 * π : ℂ)‖ = 2 * π by
      rw [norm_mul, Complex.norm_two, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le] ]
  have hπ : 0 < 2 * π := by positivity
  calc 2 * π / ‖Complex.Gamma p‖ * ‖cexp ((p - 1) * w)‖ * ‖terminant (↑n + p) w‖
      ≤ 2 * π / ‖Complex.Gamma p‖ * (ρ ^ (p.re - 1) * Real.exp (π * |p.im|)) *
        (max C 0 * (Real.exp (π * A) / Real.sin δ * ‖cexp (-cexp w)‖ * Real.exp (1 - ρ) /
          (2 * π))) := by
        gcongr
        exact hTn.trans (mul_le_mul_of_nonneg_left hpref (le_max_right _ _))
    _ = _ := by
        rw [show 1 - ρ = 1 + -ρ by ring, Real.exp_add]
        ring

end Azurite.DLMF
