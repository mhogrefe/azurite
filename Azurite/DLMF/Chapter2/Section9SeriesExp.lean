/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/


import Azurite.DLMF.Chapter2.Section9
import Azurite.DLMF.Chapter2.Section7Fabry

/-!
# Asymptotic series: change of variable, division, powers, `exp` (for DLMF §2.9(ii))

Additions to the `HasAsympSeries` calculus of `Section9`:

* `HasAsympSeries.evenSpread_var`: a series in `X = Y²` is a series in `Y` with the coefficients
  spread to even indices (`evenSpread`, from `Section7Fabry`).
* `HasAsympSeries.div_var`: `φ/X ∼ ∑ c_{j+1} Xʲ` when `c₀ = 0`.
* `HasAsympSeries.pow`: `φᵐ ∼ ∑ (c^{⋆m})_d X^d` (`convPow`, iterated Cauchy product).
* `HasAsympSeries.cexp`: `e^φ ∼ ∑ (∑_{m≤d} (c^{⋆m})_d/m!) X^d` (`expCoeff`) when `c₀ = 0`, from the
  remainder bound `Complex.exp_bound`; `expCoeff_low` gives the first four coefficients.
* `twist a j = (−1)ʲ aⱼ` commutes with Cauchy products, powers and `expCoeff`; even spreads are
  invariant.
-/

open Filter Topology Asymptotics Finset Complex

namespace Azurite.DLMF

section Calculus

variable {α : Type*} {l : Filter α} {X Y : α → ℂ}

theorem sum_evenSpread (c : ℕ → ℂ) (y : ℂ) (M : ℕ) :
    ∑ j ∈ range M, evenSpread c j * y ^ j = ∑ i ∈ range ((M + 1) / 2), c i * (y ^ 2) ^ i := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [sum_range_succ, ih]
    rcases Nat.even_or_odd M with ⟨k, rfl⟩ | ⟨k, rfl⟩
    · rw [show (k + k + 1) / 2 = k by omega, show (k + k + 1 + 1) / 2 = k + 1 by omega,
        sum_range_succ]
      congr 1
      simp only [evenSpread, show (k + k) % 2 = 0 by omega, ↓reduceIte,
        show (k + k) / 2 = k by omega]
      rw [← _root_.pow_mul, two_mul]
    · rw [show (2 * k + 1 + 1) / 2 = k + 1 by omega,
        show (2 * k + 1 + 1 + 1) / 2 = k + 1 by omega]
      simp [evenSpread, show (2 * k + 1) % 2 = 1 by omega]

/-- A series in `X = Y²` is a series in `Y`. -/
theorem HasAsympSeries.evenSpread_var (hY : Tendsto Y l (𝓝 0)) (hXY : ∀ t, X t = Y t ^ 2)
    {u : α → ℂ} {c : ℕ → ℂ} (h : HasAsympSeries l X u c) :
    HasAsympSeries l Y u (evenSpread c) := by
  intro M
  have hb : (fun t => X t ^ ((M + 1) / 2)) =O[l] fun t => Y t ^ M :=
    (isBigO_pow_of_le hY (show M ≤ 2 * ((M + 1) / 2) by omega)).congr_left fun t => by
      rw [hXY, ← _root_.pow_mul]
  refine ((h ((M + 1) / 2)).trans hb).congr_left fun t => ?_
  rw [sum_evenSpread, ← hXY]

/-- Division by the variable. -/
theorem HasAsympSeries.div_var (hX0 : ∀ᶠ t in l, X t ≠ 0) {u : α → ℂ} {c : ℕ → ℂ}
    (h : HasAsympSeries l X u c) (hc : c 0 = 0) :
    HasAsympSeries l X (fun t => u t / X t) (fun j => c (j + 1)) := by
  intro M
  have h1 := (h (M + 1)).mul (isBigO_refl (fun t => (X t)⁻¹) l)
  refine h1.congr' ?_ ?_
  · filter_upwards [hX0] with t ht
    rw [sum_range_succ', hc, zero_mul, add_zero, sub_mul, sum_mul, div_eq_mul_inv]
    congr 1
    refine sum_congr rfl fun j _ => ?_
    rw [pow_succ]
    field_simp
  · filter_upwards [hX0] with t ht
    rw [pow_succ]
    field_simp

/-- Iterated Cauchy products: `c^{⋆0} = δ₀`, `c^{⋆(m+1)} = c ⋆ c^{⋆m}`. -/
def convPow (c : ℕ → ℂ) : ℕ → ℕ → ℂ
  | 0 => fun d => if d = 0 then 1 else 0
  | m + 1 => seqConv c (convPow c m)

theorem HasAsympSeries.pow (hX : Tendsto X l (𝓝 0)) {u : α → ℂ} {c : ℕ → ℂ}
    (h : HasAsympSeries l X u c) (m : ℕ) :
    HasAsympSeries l X (fun t => u t ^ m) (convPow c m) := by
  induction m with
  | zero => exact (hasAsympSeries_pow hX 0).congr_fun (Eventually.of_forall fun t => by simp)
  | succ m ih => exact (h.mul hX ih).congr_fun (Eventually.of_forall fun t => by ring)

theorem convPow_low {c : ℕ → ℂ} (hc : c 0 = 0) (m d : ℕ) (hd : d < m) : convPow c m d = 0 := by
  induction m generalizing d with
  | zero => omega
  | succ m ih =>
    simp only [convPow, seqConv]
    refine sum_eq_zero fun j hj => ?_
    have := mem_range.mp hj
    rcases lt_or_ge j m with h | h
    · rw [ih j h, mul_zero]
    · rw [show d - j = 0 by omega, hc, zero_mul]

/-- The coefficients of `e^φ`: `∑_{m≤d} (c^{⋆m})_d/m!`. -/
noncomputable def expCoeff (c : ℕ → ℂ) (d : ℕ) : ℂ :=
  ∑ m ∈ range (d + 1), convPow c m d / (m.factorial : ℂ)

theorem HasAsympSeries.tendsto_zero {u : α → ℂ} {c : ℕ → ℂ} (hX : Tendsto X l (𝓝 0))
    (h : HasAsympSeries l X u c) (hc : c 0 = 0) : Tendsto u l (𝓝 0) := by
  have h1 := (h 1).trans_tendsto (show Tendsto (fun t => X t ^ 1) l (𝓝 0) by simpa using hX)
  simpa [hc] using h1

theorem HasAsympSeries.cexp (hX : Tendsto X l (𝓝 0)) {u : α → ℂ} {c : ℕ → ℂ}
    (h : HasAsympSeries l X u c) (hc : c 0 = 0) :
    HasAsympSeries l X (fun t => Complex.exp (u t)) (expCoeff c) := by
  have hu0 := h.tendsto_zero hX hc
  have huX : u =O[l] X := ((h 1).congr_left fun t => by simp [hc]).congr_right fun t => pow_one _
  intro M
  rcases Nat.eq_zero_or_pos M with rfl | hM
  · simp only [sum_range_zero, sub_zero, pow_zero]
    have := (continuous_exp.tendsto 0).comp hu0
    exact this.isBigO_one ℂ
  have hT : (fun t => Complex.exp (u t) - ∑ m ∈ range M, u t ^ m / (m.factorial : ℂ)) =O[l]
      fun t => u t ^ M := by
    refine IsBigO.of_bound ((M.succ : ℝ) * (M.factorial * M : ℝ)⁻¹) ?_
    filter_upwards [hu0 (Metric.closedBall_mem_nhds (0 : ℂ) one_pos)] with t ht
    rw [Set.mem_preimage, Metric.mem_closedBall, dist_zero_right] at ht
    calc _ ≤ ‖u t‖ ^ M * ((M.succ : ℝ) * (M.factorial * M : ℝ)⁻¹) := Complex.exp_bound ht hM
      _ = _ := by rw [norm_pow, mul_comm]
  have hS : HasAsympSeries l X (fun t => ∑ m ∈ range M, u t ^ m / (m.factorial : ℂ))
      (fun d => ∑ m ∈ range M, convPow c m d / (m.factorial : ℂ)) :=
    HasAsympSeries.sum (range M) (φ := fun m t => u t ^ m / (m.factorial : ℂ))
      (c := fun m d => convPow c m d / (m.factorial : ℂ)) fun m _ =>
        (((h.pow hX m).const_mul ((m.factorial : ℂ)⁻¹)).congr_fun
          (Eventually.of_forall fun t => by rw [div_eq_inv_mul])).congr_coeff
          fun d => by rw [div_eq_inv_mul]
  have hcoef : ∀ d < M, ∑ m ∈ range M, convPow c m d / (m.factorial : ℂ) = expCoeff c d := by
    intro d hd
    rw [expCoeff, ← sum_range_add_sum_Ico _ (show d + 1 ≤ M by omega),
      sum_eq_zero (s := Ico (d + 1) M) fun m hm => by
        rw [convPow_low hc m d (by have := (mem_Ico.mp hm).1; omega), zero_div], add_zero]
  refine ((hT.trans (huX.pow M)).add (hS M)).congr_left fun t => ?_
  have e : ∑ d ∈ range M, (∑ m ∈ range M, convPow c m d / (m.factorial : ℂ)) * X t ^ d =
      ∑ d ∈ range M, expCoeff c d * X t ^ d :=
    sum_congr rfl fun d hd => by rw [hcoef d (mem_range.mp hd)]
  beta_reduce
  rw [e]
  ring

/-- The first four coefficients of `e^φ` when `c₀ = 0`. -/
theorem expCoeff_low {c : ℕ → ℂ} (hc : c 0 = 0) :
    expCoeff c 0 = 1 ∧ expCoeff c 1 = c 1 ∧ expCoeff c 2 = c 2 + c 1 ^ 2 / 2 ∧
      expCoeff c 3 = c 3 + c 1 * c 2 + c 1 ^ 3 / 6 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [expCoeff, convPow, seqConv, sum_range_succ, hc, Nat.factorial] <;> ring

end Calculus

/-! ### The sign twist `j ↦ (−1)ʲ` -/

/-- `(−1)ʲ aⱼ`. -/
def twist (a : ℕ → ℂ) (j : ℕ) : ℂ := (-1) ^ j * a j

theorem seqConv_twist (a b : ℕ → ℂ) : seqConv (twist a) (twist b) = twist (seqConv a b) := by
  funext n
  simp only [seqConv, twist, mul_sum]
  refine sum_congr rfl fun j hj => ?_
  have hj : j ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hj)
  rw [show ((-1 : ℂ)) ^ n = (-1) ^ (n - j) * (-1) ^ j by rw [← pow_add, Nat.sub_add_cancel hj]]
  ring

theorem twist_evenSpread (c : ℕ → ℂ) : twist (evenSpread c) = evenSpread c := by
  funext j
  simp only [twist, evenSpread]
  split_ifs with h
  · rw [Even.neg_one_pow (Nat.even_iff.mpr h), one_mul]
  · rw [mul_zero]

theorem convPow_twist (c : ℕ → ℂ) (m : ℕ) : convPow (twist c) m = twist (convPow c m) := by
  induction m with
  | zero =>
    funext d
    simp only [convPow, twist]
    split_ifs with h
    · rw [h, pow_zero, mul_one]
    · rw [mul_zero]
  | succ m ih => rw [convPow, convPow, ih, seqConv_twist]

theorem expCoeff_twist (c : ℕ → ℂ) : expCoeff (twist c) = twist (expCoeff c) := by
  funext d
  simp only [expCoeff, convPow_twist, twist, mul_sum, mul_div_assoc]

end Azurite.DLMF
