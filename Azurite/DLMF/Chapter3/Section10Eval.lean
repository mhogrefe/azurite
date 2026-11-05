/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter3.Section10

/-!
# DLMF §3.10(iii): Numerical evaluation of continued fractions

* Forward recurrence algorithm: `Aₙ`, `Bₙ` by the three-term recurrences 1.12.5 (`cfA`, `cfB`,
  `dlmf_1_12_5`). Instability, overflow and rescaling are numerical remarks (not formalized).
* Backward recurrence algorithm 3.10.12 (`backU`, `dlmf_3_10_12`): `uₙ = bₙ`,
  `u_k = b_k + a_{k+1}/u_{k+1}`; then `u₀ = Cₙ` (exactly, as nested evaluation).
* Forward series recurrence algorithm 3.10.13–3.10.15 (`fsA`, `fsB`, `fsRho`, `fsT`,
  `dlmf_3_10_14`): for `C = a₀/(1 − a₁/(1 − a₂/(1 − ⋯)))`, `t₀ = a₀`, `t_k = ρ_k t_{k−1}`,
  `ρ₀ = 0`, `ρ_k = a_k(1 + ρ_{k−1})/(1 − a_k(1 + ρ_{k−1}))`, the partial sum
  `t₀ + ⋯ + t_{n−1}` equals the `n`th convergent `Aₙ/Bₙ` (when the `B_k` do not vanish); in fact
  `ρ_k = a_k B_{k−1}/B_{k+1}` and `t_k = a₀a₁⋯a_k/(B_k B_{k+1})` (`fsRho_eq`, `fsT_eq`).
* Steed's algorithm 3.10.16–3.10.17 (`steed`, `dlmf_3_10_17`): `D_n = B_{n−1}/Bₙ`,
  `∇Cₙ = Cₙ − C_{n−1}`, and `Cₙ = Aₙ/Bₙ` (when the `B_k` do not vanish).
* Lentz's and the modified Lentz algorithm, and the references, are not formalized.
-/

open Finset

namespace Azurite.DLMF

variable {K : Type*} [Field K]

/-! ### Backward recurrence -/

/-- **DLMF 3.10.12**: the backward recurrence, `backU a b n m = u_{n−m}`: `uₙ = bₙ`,
`u_k = b_k + a_{k+1}/u_{k+1}`. -/
def backU (a b : ℕ → K) (n : ℕ) : ℕ → K
  | 0 => b n
  | m + 1 => b (n - (m + 1)) + a (n - m) / backU a b n m

/-- **DLMF 3.10.12**: `u₀ = Cₙ`. -/
theorem dlmf_3_10_12 (a b : ℕ → K) (n : ℕ) : backU a b n n = cfConv a b n := by
  have key : ∀ m ≤ n, cfConv a b n = cfw a b (n - m) (backU a b n m - b (n - m)) := by
    intro m
    induction m with
    | zero => intro _; simp [cfConv, backU]
    | succ m ih =>
      intro hm
      rw [ih (by omega)]
      obtain ⟨r, hr⟩ : ∃ r, n - m = r + 1 := ⟨n - m - 1, by omega⟩
      rw [hr, cfw, show n - (m + 1) = r by omega, backU, show n - (m + 1) = r by omega, hr]
      congr 1
      ring
  rw [key n le_rfl, Nat.sub_self, cfw]
  ring

/-! ### The forward series recurrence -/

/-- The partial numerators of 3.10.13: `a₀`, then `−a_k`. -/
def fsA (a : ℕ → K) : ℕ → K
  | 0 => 0
  | 1 => a 0
  | k + 2 => -a (k + 1)

/-- The partial denominators of 3.10.13: `b₀ = 0`, `b_k = 1`. -/
def fsB : ℕ → K
  | 0 => 0
  | _ + 1 => 1

/-- **DLMF 3.10.15**: `ρ₀ = 0`, `ρ_k = a_k(1 + ρ_{k−1})/(1 − a_k(1 + ρ_{k−1}))`. -/
def fsRho (a : ℕ → K) : ℕ → K
  | 0 => 0
  | k + 1 => a (k + 1) * (1 + fsRho a k) / (1 - a (k + 1) * (1 + fsRho a k))

/-- **DLMF 3.10.15**: `t₀ = a₀`, `t_k = ρ_k t_{k−1}`. -/
def fsT (a : ℕ → K) : ℕ → K
  | 0 => a 0
  | k + 1 => fsRho a (k + 1) * fsT a k

theorem fsB_rec (a : ℕ → K) (k : ℕ) :
    cfB (fsA a) fsB (k + 2) = cfB (fsA a) fsB (k + 1) - a (k + 1) * cfB (fsA a) fsB k := by
  show cfQ (fsA a) fsB (k + 1 + 2) =
    cfQ (fsA a) fsB (k + 2) - a (k + 1) * cfQ (fsA a) fsB (k + 1)
  rw [cfQ]
  simp only [fsA, fsB, one_mul]
  ring

theorem fsB_zero (a : ℕ → K) : cfB (fsA a) fsB 0 = 1 := rfl

theorem fsB_one (a : ℕ → K) : cfB (fsA a) fsB 1 = 1 := by
  simp [cfB, cfQ, fsA, fsB]

/-- `ρ_k = a_k B_{k−1}/B_{k+1}` (with `B_{−1} = 0`). -/
theorem fsRho_eq {a : ℕ → K} {n : ℕ} (hB : ∀ k ≤ n + 1, cfB (fsA a) fsB k ≠ 0) :
    ∀ k ≤ n, fsRho a k = a k * cfQ (fsA a) fsB k / cfB (fsA a) fsB (k + 1) := by
  intro k
  induction k with
  | zero => intro _; simp [fsRho, cfQ]
  | succ k ih =>
    intro hk
    have hBk1 := hB (k + 1) (by omega)
    have hBk2 := hB (k + 2) (by omega)
    have h1 : 1 + fsRho a k = cfB (fsA a) fsB k / cfB (fsA a) fsB (k + 1) := by
      rw [ih (by omega)]
      rcases k with _ | m
      · simp [cfQ, fsB_one, fsB_zero]
      · rw [show cfQ (fsA a) fsB (m + 1) = cfB (fsA a) fsB m from rfl, eq_div_iff hBk1,
          add_mul, div_mul_cancel₀ _ hBk1, fsB_rec]
        ring
    have h2 : 1 - a (k + 1) * (cfB (fsA a) fsB k / cfB (fsA a) fsB (k + 1)) =
        cfB (fsA a) fsB (k + 2) / cfB (fsA a) fsB (k + 1) := by
      rw [fsB_rec]; field_simp
    rw [fsRho, h1, h2, show cfQ (fsA a) fsB (k + 1) = cfB (fsA a) fsB k from rfl]
    field_simp

theorem prod_fsA (a : ℕ → K) (k : ℕ) :
    ∏ j ∈ Icc 1 (k + 1), fsA a j = (-1) ^ k * ∏ i ∈ range (k + 1), a i := by
  induction k with
  | zero => simp [fsA]
  | succ k ih =>
    rw [prod_Icc_succ_top (by omega), ih, prod_range_succ a (k + 1),
      show k + 1 + 1 = k + 2 from rfl, fsA, pow_succ]
    ring

/-- `t_k = a₀a₁⋯a_k/(B_k B_{k+1})`. -/
theorem fsT_eq {a : ℕ → K} {n : ℕ} (hB : ∀ k ≤ n + 1, cfB (fsA a) fsB k ≠ 0) :
    ∀ k ≤ n, fsT a k = (∏ i ∈ range (k + 1), a i) /
      (cfB (fsA a) fsB k * cfB (fsA a) fsB (k + 1)) := by
  intro k
  induction k with
  | zero => intro _; simp [fsT, fsB_zero, fsB_one]
  | succ k ih =>
    intro hk
    rw [fsT, ih (by omega), fsRho_eq hB (k + 1) hk,
      show cfQ (fsA a) fsB (k + 1) = cfB (fsA a) fsB k from rfl, prod_range_succ a (k + 1)]
    have h0 := hB k (by omega)
    have h1 := hB (k + 1) (by omega)
    have h2 := hB (k + 2) (by omega)
    field_simp

/-- **DLMF 3.10.14**: the `n`th partial sum `t₀ + t₁ + ⋯ + t_{n−1}` equals the `n`th convergent
`Aₙ/Bₙ` of 3.10.13 (when `B₀, …, Bₙ` do not vanish). -/
theorem dlmf_3_10_14 {a : ℕ → K} {n : ℕ} (hB : ∀ k ≤ n, cfB (fsA a) fsB k ≠ 0) :
    ∑ k ∈ range n, fsT a k = cfA (fsA a) fsB n / cfB (fsA a) fsB n := by
  rw [dlmf_1_12_9 _ _ n hB]
  simp only [fsB, zero_add]
  refine sum_congr rfl fun k hk => ?_
  have hk' := mem_range.mp hk
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [fsT_eq (n := m) (fun j hj => hB j hj) k (by omega), prod_fsA, ← mul_assoc,
    ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow, one_mul]

/-! ### Steed's algorithm -/

/-- **DLMF 3.10.16–3.10.17**: Steed's algorithm, `steed a b n = (Cₙ, Dₙ, ∇Cₙ)`. -/
def steed (a b : ℕ → K) : ℕ → K × K × K
  | 0 => (b 0, 0, 0)
  | 1 => (b 0 + a 1 * (1 / b 1), 1 / b 1, a 1 * (1 / b 1))
  | n + 2 =>
    let D := 1 / ((steed a b (n + 1)).2.1 * a (n + 2) + b (n + 2))
    let dC := (b (n + 2) * D - 1) * (steed a b (n + 1)).2.2
    ((steed a b (n + 1)).1 + dC, D, dC)

/-- **DLMF 3.10.17**: Steed's algorithm computes `Dₙ = B_{n−1}/Bₙ`, `∇Cₙ = Cₙ − C_{n−1}` and
`Cₙ = Aₙ/Bₙ` (when `B₀, …, Bₙ` do not vanish). -/
theorem dlmf_3_10_17 (a b : ℕ → K) (n : ℕ) (hB : ∀ k ≤ n + 1, cfB a b k ≠ 0) :
    (steed a b (n + 1)).2.1 = cfB a b n / cfB a b (n + 1) ∧
      (steed a b (n + 1)).2.2 = cfA a b (n + 1) / cfB a b (n + 1) - cfA a b n / cfB a b n ∧
      (steed a b (n + 1)).1 = cfA a b (n + 1) / cfB a b (n + 1) := by
  induction n with
  | zero =>
    have hb1 : cfB a b 1 = b 1 := by simp [cfB, cfQ]
    have h1 : b 1 ≠ 0 := hb1 ▸ hB 1 le_rfl
    simp only [steed]
    simp [cfA, cfB, cfP, cfQ]
    refine ⟨?_, ?_⟩
    · field_simp; ring
    · field_simp
  | succ n ih =>
    obtain ⟨hD, hdC, hC⟩ := ih fun k hk => hB k (by omega)
    have h0 := hB n (by omega)
    have h1 := hB (n + 1) (by omega)
    have h2 := hB (n + 2) le_rfl
    have hrec : cfB a b (n + 2) = b (n + 2) * cfB a b (n + 1) + a (n + 2) * cfB a b n :=
      (dlmf_1_12_5 a b (n + 1)).2
    have hD' : 1 / (cfB a b n / cfB a b (n + 1) * a (n + 2) + b (n + 2)) =
        cfB a b (n + 1) / cfB a b (n + 2) := by
      have : cfB a b n / cfB a b (n + 1) * a (n + 2) + b (n + 2) =
          cfB a b (n + 2) / cfB a b (n + 1) := by
        field_simp; linear_combination -hrec
      rw [this, one_div_div]
    have hdiff := dlmf_1_12_8 a b (n + 1) h1 h2
    have hdiff0 := dlmf_1_12_8 a b n h0 h1
    have hdC' : (b (n + 2) * (cfB a b (n + 1) / cfB a b (n + 2)) - 1) *
        (cfA a b (n + 1) / cfB a b (n + 1) - cfA a b n / cfB a b n) =
        cfA a b (n + 2) / cfB a b (n + 2) - cfA a b (n + 1) / cfB a b (n + 1) := by
      rw [hdiff, hdiff0, prod_Icc_succ_top (by omega : 1 ≤ n + 2)]
      have hm : b (n + 2) * (cfB a b (n + 1) / cfB a b (n + 2)) - 1 =
          -(a (n + 2) * cfB a b n / cfB a b (n + 2)) := by
        field_simp; linear_combination -hrec
      rw [hm]
      field_simp
      ring
    refine ⟨?_, ?_, ?_⟩
    · simp only [steed]; rw [hD, hD']
    · simp only [steed]; rw [hD, hD', hdC, hdC']
    · simp only [steed]; rw [hD, hD', hdC, hdC', hC]; ring

/-- `C₀ = b₀ = A₀/B₀`. -/
theorem steed_zero (a b : ℕ → K) : (steed a b 0).1 = cfA a b 0 / cfB a b 0 := by
  simp [steed, cfA, cfB, cfP, cfQ]

end Azurite.DLMF
