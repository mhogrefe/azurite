/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# DLMF §1.12: Continued Fractions

Formalizations of <https://dlmf.nist.gov/1.12>, §1.12(i) Notation and §1.12(ii) Convergents,
over any field `K`. The sequences `a b : ℕ → K` carry DLMF's `aₙ` (`n ≥ 1`) and `bₙ` (`n ≥ 0`).

**Indexing and conventions.**
* `cfw a b n w` is `C_n(w)` (1.12.20) and `cfConv a b n` is `Cₙ` (1.12.4), both by DLMF's
  nesting. `CfConverges` is convergence of the continued fraction (1.12.1–1.12.3).
* The canonical numerators and denominators are `cfA a b n = Aₙ` and `cfB a b n = Bₙ`. Their
  shifted versions `cfP a b k = A_{k−1}` and `cfQ a b k = B_{k−1}` carry `A_{−1} = 1` and
  `B_{−1} = 0`.
* Lean has `x/0 = 0`, so identities that evaluate the nested fraction assume `CfNonzero` (no zero
  denominator along the way). Identities stated with `Cₙ = Aₙ/Bₙ` assume nonzero `Bₖ`.
* Statements DLMF gives for `n ≥ 1` or `n ≥ 2` are stated at `n + 1` or `n + 2`.

**Results.**
* 1.12.5–1.12.6: the recurrences and initial values (`dlmf_1_12_5`, `dlmf_1_12_6`).
* 1.12.4 and 1.12.21: `Cₙ = Aₙ/Bₙ` and `C_n(w) = (Aₙ + A_{n−1}w)/(Bₙ + B_{n−1}w)`
  (`dlmf_1_12_4`, `dlmf_1_12_21`); also `C_n(0) = Cₙ` and `C_n(∞) = A_{n−1}/B_{n−1}` as a limit
  over `ℂ` (`dlmf_1_12_21_limits`).
* 1.12.7: the determinant formula (`dlmf_1_12_7`).
* 1.12.8–1.12.14: its consequences, the convergent differences, the series form of `Cₙ`, and the
  recovery of `aₙ`, `bₙ` from the convergents.
* 1.12.15–1.12.17: equivalence transformations (`dlmf_1_12_15`, `dlmf_1_12_16`), and the two
  normal forms of 1.12.17 (`dlmf_1_12_17_one`, `dlmf_1_12_17_two`, `cfD`, `cfD_values`).
* 1.12.18–1.12.19: series as continued fractions (`dlmf_1_12_18`, `dlmf_1_12_19`).
-/

open Filter Topology Finset Bornology

namespace Azurite.DLMF

variable {K : Type*} [Field K]

/-! ### Notation and convergents -/

/-- **DLMF 1.12.20**: `C_n(w) = b₀ + a₁/(b₁ + a₂/(b₂ + ⋯ aₙ/(bₙ + w)))`. -/
def cfw (a b : ℕ → K) : ℕ → K → K
  | 0, w => b 0 + w
  | n + 1, w => cfw a b n (a (n + 1) / (b (n + 1) + w))

/-- **DLMF 1.12.4**: the `n`th approximant (convergent)
`Cₙ = b₀ + a₁/(b₁ + a₂/(b₂ + ⋯ aₙ/bₙ))`. -/
def cfConv (a b : ℕ → K) (n : ℕ) : K := cfw a b n 0

/-- No zero denominator occurs when evaluating `C_n(w)` (in Lean `x/0 = 0`). -/
def CfNonzero (a b : ℕ → K) : ℕ → K → Prop
  | 0, _ => True
  | n + 1, w => b (n + 1) + w ≠ 0 ∧ CfNonzero a b n (a (n + 1) / (b (n + 1) + w))

/-- **DLMF 1.12.3**: the continued fraction `C = b₀ + a₁/(b₁ + a₂/(b₂ + ⋯))` (1.12.1, 1.12.2)
converges to `C` if its convergents `Cₙ` tend to `C`. -/
def CfConverges [TopologicalSpace K] (a b : ℕ → K) (C : K) : Prop :=
  Tendsto (cfConv a b) atTop (𝓝 C)

/-- `cfP a b k = A_{k−1}`: the canonical numerators, shifted so that `A_{−1}` is `cfP a b 0`. -/
def cfP (a b : ℕ → K) : ℕ → K
  | 0 => 1
  | 1 => b 0
  | k + 2 => b (k + 1) * cfP a b (k + 1) + a (k + 1) * cfP a b k

/-- `cfQ a b k = B_{k−1}`: the canonical denominators, shifted so that `B_{−1}` is `cfQ a b 0`. -/
def cfQ (a b : ℕ → K) : ℕ → K
  | 0 => 0
  | 1 => 1
  | k + 2 => b (k + 1) * cfQ a b (k + 1) + a (k + 1) * cfQ a b k

/-- The `n`th canonical numerator `Aₙ`. -/
def cfA (a b : ℕ → K) (n : ℕ) : K := cfP a b (n + 1)

/-- The `n`th canonical denominator `Bₙ`. -/
def cfB (a b : ℕ → K) (n : ℕ) : K := cfQ a b (n + 1)

/-- **DLMF 1.12.5**: `A_k = b_k A_{k−1} + a_k A_{k−2}`, `B_k = b_k B_{k−1} + a_k B_{k−2}`,
`k = 1, 2, …` (here `A_{k−1} = cfP a b k`, `A_{k−2} = cfP a b (k − 1)`). -/
theorem dlmf_1_12_5 (a b : ℕ → K) (k : ℕ) :
    cfA a b (k + 1) = b (k + 1) * cfA a b k + a (k + 1) * cfP a b k ∧
      cfB a b (k + 1) = b (k + 1) * cfB a b k + a (k + 1) * cfQ a b k :=
  ⟨rfl, rfl⟩

/-- **DLMF 1.12.6**: `A_{−1} = 1`, `A₀ = b₀`, `B_{−1} = 0`, `B₀ = 1`. -/
theorem dlmf_1_12_6 (a b : ℕ → K) :
    cfP a b 0 = 1 ∧ cfA a b 0 = b 0 ∧ cfQ a b 0 = 0 ∧ cfB a b 0 = 1 :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- **DLMF 1.12.21**: `C_n(w) = (Aₙ + A_{n−1} w)/(Bₙ + B_{n−1} w)`. -/
theorem dlmf_1_12_21 (a b : ℕ → K) (n : ℕ) :
    ∀ w, CfNonzero a b n w → cfw a b n w = (cfA a b n + cfP a b n * w) /
      (cfB a b n + cfQ a b n * w) := by
  induction n with
  | zero => intro w _; simp [cfw, cfA, cfB, cfP, cfQ]
  | succ n ih =>
    intro w hw
    obtain ⟨hb, hrest⟩ := hw
    rw [cfw, ih _ hrest, ← mul_div_mul_right _ _ hb]
    simp only [cfA, cfB, cfP, cfQ]
    congr 1 <;> field_simp <;> ring

/-- **DLMF 1.12.4**: `Cₙ = Aₙ/Bₙ`. -/
theorem dlmf_1_12_4 (a b : ℕ → K) {n : ℕ} (h : CfNonzero a b n 0) :
    cfConv a b n = cfA a b n / cfB a b n := by
  rw [cfConv, dlmf_1_12_21 a b n 0 h]
  simp

/-! ### The determinant formula and its consequences -/

/-- **DLMF 1.12.7**: `Aₙ B_{n−1} − Bₙ A_{n−1} = (−1)^{n−1} ∏_{k=1}^{n} a_k`, `n = 0, 1, 2, …`. -/
theorem dlmf_1_12_7 (a b : ℕ → K) (n : ℕ) :
    cfA a b n * cfQ a b n - cfB a b n * cfP a b n = (-1) ^ (n + 1) * ∏ k ∈ Icc 1 n, a k := by
  induction n with
  | zero => simp [cfA, cfB, cfP, cfQ]
  | succ n ih =>
    simp only [cfA, cfB] at ih ⊢
    rw [prod_Icc_succ_top (by omega)]
    simp only [cfP, cfQ] at ih ⊢
    linear_combination (-(a (n + 1))) * ih

/-- **DLMF 1.12.8**: `Cₙ − C_{n−1} = (−1)^{n−1} ∏_{k=1}^{n} a_k / (B_{n−1} Bₙ)`, `n = 1, 2, …`
(with `Cₙ = Aₙ/Bₙ`). -/
theorem dlmf_1_12_8 (a b : ℕ → K) (n : ℕ) (h₀ : cfB a b n ≠ 0) (h₁ : cfB a b (n + 1) ≠ 0) :
    cfA a b (n + 1) / cfB a b (n + 1) - cfA a b n / cfB a b n =
      (-1) ^ n * (∏ k ∈ Icc 1 (n + 1), a k) / (cfB a b n * cfB a b (n + 1)) := by
  have h := dlmf_1_12_7 a b (n + 1)
  have hq : cfQ a b (n + 1) = cfB a b n := rfl
  have hp : cfP a b (n + 1) = cfA a b n := rfl
  rw [hq, hp] at h
  rw [div_sub_div _ _ h₁ h₀, div_eq_div_iff (mul_ne_zero h₁ h₀) (mul_ne_zero h₀ h₁)]
  linear_combination (cfB a b n * cfB a b (n + 1)) * h

/-- **DLMF 1.12.9**: `Cₙ = b₀ + a₁/(B₀B₁) − ⋯ + (−1)^{n−1} ∏_{k=1}^{n} a_k/(B_{n−1}Bₙ)`. -/
theorem dlmf_1_12_9 (a b : ℕ → K) (n : ℕ) (hB : ∀ k ≤ n, cfB a b k ≠ 0) :
    cfA a b n / cfB a b n = b 0 + ∑ k ∈ range n,
      (-1) ^ k * (∏ j ∈ Icc 1 (k + 1), a j) / (cfB a b k * cfB a b (k + 1)) := by
  induction n with
  | zero => simp [cfA, cfB, cfP, cfQ]
  | succ n ih =>
    rw [sum_range_succ, ← add_assoc, ← ih fun k hk => hB k (by omega),
      ← dlmf_1_12_8 a b n (hB n (by omega)) (hB (n + 1) le_rfl)]
    ring

/-- **DLMF 1.12.10**: `aₙ = (A_{n−1}Bₙ − AₙB_{n−1})/(A_{n−1}B_{n−2} − A_{n−2}B_{n−1})`,
`n = 1, 2, …` (stated for `n + 1`; requires `a_k ≠ 0`). -/
theorem dlmf_1_12_10 (a b : ℕ → K) (ha : ∀ k ≥ 1, a k ≠ 0) (n : ℕ) :
    a (n + 1) = (cfA a b n * cfB a b (n + 1) - cfA a b (n + 1) * cfB a b n) /
      (cfA a b n * cfQ a b n - cfP a b n * cfB a b n) := by
  have h0 := dlmf_1_12_7 a b n
  have h1 := dlmf_1_12_7 a b (n + 1)
  have hq : cfQ a b (n + 1) = cfB a b n := rfl
  have hp : cfP a b (n + 1) = cfA a b n := rfl
  rw [hq, hp, prod_Icc_succ_top (by omega)] at h1
  have hprod : ∏ k ∈ Icc 1 n, a k ≠ 0 :=
    prod_ne_zero_iff.mpr fun k hk => ha k (mem_Icc.mp hk).1
  have hden : cfA a b n * cfQ a b n - cfP a b n * cfB a b n ≠ 0 := by
    rw [show cfA a b n * cfQ a b n - cfP a b n * cfB a b n =
      cfA a b n * cfQ a b n - cfB a b n * cfP a b n by ring, h0]
    exact mul_ne_zero (pow_ne_zero _ (by norm_num)) hprod
  rw [eq_div_iff hden]
  linear_combination (a (n + 1)) * h0 + h1

/-- **DLMF 1.12.11**: `aₙ = (Bₙ/B_{n−2}) (C_{n−1} − Cₙ)/(C_{n−1} − C_{n−2})`, `n = 2, 3, …`
(stated for `n + 2`). -/
theorem dlmf_1_12_11 (a b : ℕ → K) (ha : ∀ k ≥ 1, a k ≠ 0) (n : ℕ)
    (hB : ∀ k ≤ n + 2, cfB a b k ≠ 0) :
    a (n + 2) = cfB a b (n + 2) / cfB a b n *
      ((cfA a b (n + 1) / cfB a b (n + 1) - cfA a b (n + 2) / cfB a b (n + 2)) /
        (cfA a b (n + 1) / cfB a b (n + 1) - cfA a b n / cfB a b n)) := by
  have e1 := dlmf_1_12_8 a b (n + 1) (hB _ (by omega)) (hB _ le_rfl)
  have e0 := dlmf_1_12_8 a b n (hB _ (by omega)) (hB _ (by omega))
  have hprod : ∀ m, ∏ k ∈ Icc 1 m, a k ≠ 0 := fun m =>
    prod_ne_zero_iff.mpr fun k hk => ha k (mem_Icc.mp hk).1
  rw [show cfA a b (n + 1) / cfB a b (n + 1) - cfA a b (n + 2) / cfB a b (n + 2) =
    -(cfA a b (n + 2) / cfB a b (n + 2) - cfA a b (n + 1) / cfB a b (n + 1)) by ring, e1, e0,
    prod_Icc_succ_top (show 1 ≤ n + 1 + 1 by omega)]
  have := hprod (n + 1)
  have h0 := hB n (by omega)
  have h1 := hB (n + 1) (by omega)
  have h2 := hB (n + 2) le_rfl
  have ha2 := ha (n + 2) (by omega)
  field_simp
  ring

/-- **DLMF 1.12.12**: `bₙ = (AₙB_{n−2} − A_{n−2}Bₙ)/(A_{n−1}B_{n−2} − A_{n−2}B_{n−1})`,
`n = 1, 2, …` (stated for `n + 1`; `A_{n−2} = cfP a b n`, `B_{n−2} = cfQ a b n`). -/
theorem dlmf_1_12_12 (a b : ℕ → K) (ha : ∀ k ≥ 1, a k ≠ 0) (n : ℕ) :
    b (n + 1) = (cfA a b (n + 1) * cfQ a b n - cfP a b n * cfB a b (n + 1)) /
      (cfA a b n * cfQ a b n - cfP a b n * cfB a b n) := by
  have h0 := dlmf_1_12_7 a b n
  have hprod : ∏ k ∈ Icc 1 n, a k ≠ 0 :=
    prod_ne_zero_iff.mpr fun k hk => ha k (mem_Icc.mp hk).1
  have hden : cfA a b n * cfQ a b n - cfP a b n * cfB a b n ≠ 0 := by
    rw [show cfA a b n * cfQ a b n - cfP a b n * cfB a b n =
      cfA a b n * cfQ a b n - cfB a b n * cfP a b n by ring, h0]
    exact mul_ne_zero (pow_ne_zero _ (by norm_num)) hprod
  rw [eq_div_iff hden]
  simp only [cfA, cfB, cfP, cfQ]
  ring

/-- **DLMF 1.12.13**: `bₙ = (Bₙ/B_{n−1}) (Cₙ − C_{n−2})/(C_{n−1} − C_{n−2})`, `n = 2, 3, …`
(stated for `n + 2`). -/
theorem dlmf_1_12_13 (a b : ℕ → K) (ha : ∀ k ≥ 1, a k ≠ 0) (n : ℕ)
    (hB : ∀ k ≤ n + 2, cfB a b k ≠ 0) :
    b (n + 2) = cfB a b (n + 2) / cfB a b (n + 1) *
      ((cfA a b (n + 2) / cfB a b (n + 2) - cfA a b n / cfB a b n) /
        (cfA a b (n + 1) / cfB a b (n + 1) - cfA a b n / cfB a b n)) := by
  have h0 := hB n (by omega)
  have h1 := hB (n + 1) (by omega)
  have h2 := hB (n + 2) le_rfl
  have hd := dlmf_1_12_7 a b (n + 1)
  have hq : cfQ a b (n + 1) = cfB a b n := rfl
  have hp : cfP a b (n + 1) = cfA a b n := rfl
  rw [hq, hp] at hd
  have hprod : ∏ k ∈ Icc 1 (n + 1), a k ≠ 0 :=
    prod_ne_zero_iff.mpr fun k hk => ha k (mem_Icc.mp hk).1
  have hE : cfA a b (n + 1) * cfB a b n - cfB a b (n + 1) * cfA a b n ≠ 0 := by
    rw [hd]
    exact mul_ne_zero (pow_ne_zero _ (by norm_num)) hprod
  have hnum : cfA a b (n + 2) * cfB a b n - cfB a b (n + 2) * cfA a b n =
      b (n + 2) * (cfA a b (n + 1) * cfB a b n - cfB a b (n + 1) * cfA a b n) := by
    simp only [cfA, cfB, cfP, cfQ]
    ring
  rw [div_sub_div _ _ h2 h0, div_sub_div _ _ h1 h0, hnum]
  field_simp

/-- **DLMF 1.12.14**: `b₀ = A₀ = C₀`, `b₁ = B₁`, `a₁ = A₁ − A₀B₁`. -/
theorem dlmf_1_12_14 (a b : ℕ → K) :
    b 0 = cfA a b 0 ∧ cfA a b 0 = cfConv a b 0 ∧ b 1 = cfB a b 1 ∧
      a 1 = cfA a b 1 - cfA a b 0 * cfB a b 1 := by
  refine ⟨rfl, by simp [cfA, cfP, cfConv, cfw], by simp [cfB, cfQ], ?_⟩
  simp [cfA, cfB, cfP, cfQ]
  ring

/-! ### Equivalence -/

/-- **DLMF 1.12.15–1.12.16**: if `d₀ = 1`, `dₙ ≠ 0`, `a′ₙ = dₙd_{n−1}aₙ`, `b′ₙ = dₙbₙ`, then
`A′ₙ = (∏_{k=0}^{n} d_k) Aₙ` and `B′ₙ = (∏_{k=0}^{n} d_k) Bₙ`, so the two continued fractions
have the same convergents (are equivalent). -/
theorem dlmf_1_12_15 (a b a' b' d : ℕ → K) (hd0 : d 0 = 1)
    (ha' : ∀ n ≥ 1, a' n = d n * d (n - 1) * a n) (hb' : ∀ n, b' n = d n * b n) (k : ℕ) :
    cfP a' b' k = (∏ j ∈ range k, d j) * cfP a b k ∧
      cfQ a' b' k = (∏ j ∈ range k, d j) * cfQ a b k := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    match k with
    | 0 => simp [cfP, cfQ]
    | 1 => simp [cfP, cfQ, hb', hd0]
    | k + 2 =>
      obtain ⟨p1, q1⟩ := ih (k + 1) (by omega)
      obtain ⟨p0, q0⟩ := ih k (by omega)
      simp only [cfP, cfQ, p1, q1, p0, q0, hb', ha' (k + 1) (by omega),
        show k + 1 - 1 = k by omega, prod_range_succ]
      constructor <;> ring

/-- Equivalent continued fractions have the same convergents `Aₙ/Bₙ`. -/
theorem dlmf_1_12_16 (a b a' b' d : ℕ → K) (hd0 : d 0 = 1) (hd : ∀ n, d n ≠ 0)
    (ha' : ∀ n ≥ 1, a' n = d n * d (n - 1) * a n) (hb' : ∀ n, b' n = d n * b n) (n : ℕ) :
    cfA a' b' n / cfB a' b' n = cfA a b n / cfB a b n := by
  obtain ⟨hp, hq⟩ := dlmf_1_12_15 a b a' b' d hd0 ha' hb' (n + 1)
  rw [cfA, cfB, hp, hq, mul_div_mul_left _ _ (prod_ne_zero_iff.mpr fun j _ => hd j), cfA, cfB]

/-- **DLMF 1.12.17**, first form: `b₀ + a₁/(b₁ + a₂/(b₂ + ⋯)) =
b₀ + (a₁/b₁)/(1 + (a₂/(b₁b₂))/(1 + ⋯ (aₙ/(b_{n−1}bₙ))/(1 + ⋯)))` (`bₙ ≠ 0`, `n ≥ 1`):
equivalence with `dₙ = 1/bₙ`. -/
theorem dlmf_1_12_17_one (a b : ℕ → K) (hb : ∀ n ≥ 1, b n ≠ 0) (n : ℕ) :
    let a' : ℕ → K := fun k => if k = 1 then a 1 / b 1 else a k / (b (k - 1) * b k)
    let b' : ℕ → K := fun k => if k = 0 then b 0 else 1
    cfA a' b' n / cfB a' b' n = cfA a b n / cfB a b n := by
  intro a' b'
  refine dlmf_1_12_16 a b a' b' (fun k => if k = 0 then 1 else 1 / b k) (by simp)
    (fun k => by
      by_cases hk : k = 0
      · simp [hk]
      · simp [hk, hb k (by omega)]) (fun k hk => ?_)
    (fun k => by
      by_cases hk : k = 0
      · simp [b', hk]
      · simp [b', hk, hb k (by omega)]) n
  have hk0 : k ≠ 0 := by omega
  by_cases hk1 : k = 1
  · subst hk1
    simp [a']
    ring
  · have hk' : k - 1 ≠ 0 := by omega
    simp only [a', hk1, hk0, hk', ↓reduceIte]
    have := hb k hk
    have := hb (k - 1) (by omega)
    field_simp

/-- The scaling factors of the second form of 1.12.17: `d₀ = 1`, `d_{n+1} = 1/(a_{n+1}dₙ)`. -/
def cfD (a : ℕ → K) : ℕ → K
  | 0 => 1
  | n + 1 => 1 / (a (n + 1) * cfD a n)

theorem cfD_ne_zero (a : ℕ → K) (ha : ∀ k ≥ 1, a k ≠ 0) : ∀ n, cfD a n ≠ 0
  | 0 => one_ne_zero
  | n + 1 => one_div_ne_zero (mul_ne_zero (ha (n + 1) (by omega)) (cfD_ne_zero a ha n))

/-- The factors are DLMF's `1/a₁`, `a₁/a₂`, `a₂/(a₁a₃)`, `a₁a₃/(a₂a₄)`, …. -/
theorem cfD_values (a : ℕ → K) (ha : ∀ k ≥ 1, a k ≠ 0) :
    cfD a 1 = 1 / a 1 ∧ cfD a 2 = a 1 / a 2 ∧ cfD a 3 = a 2 / (a 1 * a 3) ∧
      cfD a 4 = a 1 * a 3 / (a 2 * a 4) := by
  have h1 := ha 1 (by omega)
  have h2 := ha 2 (by omega)
  have h3 := ha 3 (by omega)
  have h4 := ha 4 (by omega)
  refine ⟨by simp [cfD], ?_, ?_, ?_⟩ <;> simp [cfD] <;> field_simp

/-- **DLMF 1.12.17**, second form: `b₀ + a₁/(b₁ + ⋯) = b₀ + 1/((1/a₁)b₁ + 1/((a₁/a₂)b₂ +
1/((a₂/(a₁a₃))b₃ + ⋯)))` (`aₙ ≠ 0`): equivalence with `dₙ = cfD a n`. -/
theorem dlmf_1_12_17_two (a b : ℕ → K) (ha : ∀ k ≥ 1, a k ≠ 0) (n : ℕ) :
    cfA (fun _ => 1) (fun k => cfD a k * b k) n / cfB (fun _ => 1) (fun k => cfD a k * b k) n =
      cfA a b n / cfB a b n :=
  dlmf_1_12_16 a b _ _ (cfD a) rfl (cfD_ne_zero a ha) (fun k hk => by
    obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
    simp only [cfD, Nat.add_sub_cancel]
    have := ha (m + 1) (by omega)
    have := cfD_ne_zero a ha m
    field_simp) (fun _ => rfl) n

/-! ### Series -/

/-- **DLMF 1.12.18**: `p₀ + ∑_{k=1}^{n} p₁p₂⋯p_k = p₀ + p₁/(1 − p₂/(1 + p₂ − p₃/(1 + p₃ − ⋯
pₙ/(1 + pₙ))))`: for this continued fraction `Bₙ = 1` and `Aₙ` is the partial sum. -/
theorem dlmf_1_12_18 (p : ℕ → K) (n : ℕ) :
    let a : ℕ → K := fun k => if k = 1 then p 1 else -p k
    let b : ℕ → K := fun k => if k = 0 then p 0 else if k = 1 then 1 else 1 + p k
    cfB a b n = 1 ∧ cfA a b n = p 0 + ∑ k ∈ Icc 1 n, ∏ j ∈ Icc 1 k, p j := by
  intro a b
  have hQ : ∀ k, cfQ a b (k + 1) = 1 ∧ cfQ a b (k + 2) = 1 := by
    intro k
    induction k with
    | zero => simp [cfQ, a, b]
    | succ k ih =>
      refine ⟨ih.2, ?_⟩
      rw [show k + 1 + 2 = (k + 1) + 2 by rfl, cfQ, ih.2, ih.1]
      simp [a, b]
  have hP : ∀ k, cfP a b (k + 1) = p 0 + ∑ i ∈ Icc 1 k, ∏ j ∈ Icc 1 i, p j := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      match k with
      | 0 => simp [cfP, b]
      | 1 => simp [cfP, a, b]
      | k + 2 =>
        rw [show k + 2 + 1 = (k + 1) + 2 by rfl, cfP, ih (k + 1) (by omega), ih k (by omega),
          sum_Icc_succ_top (show 1 ≤ k + 2 by omega), sum_Icc_succ_top (show 1 ≤ k + 1 by omega),
          prod_Icc_succ_top (show 1 ≤ k + 2 by omega)]
        simp only [a, b, show k + 2 ≠ 0 by omega, show k + 2 ≠ 1 by omega, ↓reduceIte]
        ring
  exact ⟨(hQ n).1, hP n⟩

/-- **DLMF 1.12.19**: `∑_{k=0}^{n} c_k x^k = c₀ + c₁x/(1 − (c₂/c₁)x/(1 + (c₂/c₁)x − ⋯
(cₙ/c_{n−1})x/(1 + (cₙ/c_{n−1})x)))` (`c_k ≠ 0`): 1.12.18 with `p₀ = c₀`, `p₁ = c₁x`,
`p_k = (c_k/c_{k−1})x`. -/
theorem dlmf_1_12_19 (c : ℕ → K) (hc : ∀ k ≥ 1, c k ≠ 0) (x : K) (n : ℕ) :
    let p : ℕ → K := fun k => if k = 0 then c 0 else if k = 1 then c 1 * x
      else c k / c (k - 1) * x
    p 0 + ∑ k ∈ Icc 1 n, ∏ j ∈ Icc 1 k, p j = ∑ k ∈ range (n + 1), c k * x ^ k := by
  intro p
  have hprod : ∀ k, ∏ j ∈ Icc 1 (k + 1), p j = c (k + 1) * x ^ (k + 1) := by
    intro k
    induction k with
    | zero => simp [p]
    | succ k ih =>
      rw [prod_Icc_succ_top (by omega), ih]
      simp only [p, show k + 1 + 1 ≠ 0 by omega, show k + 1 + 1 ≠ 1 by omega, ↓reduceIte,
        show k + 1 + 1 - 1 = k + 1 by omega]
      have := hc (k + 1) (by omega)
      field_simp
      ring
  induction n with
  | zero => simp [p]
  | succ n ih =>
    rw [sum_Icc_succ_top (by omega), ← add_assoc, ih, hprod]
    exact (sum_range_succ _ (n + 1)).symm

/-! ### Fractional transformations -/

/-- **DLMF 1.12.21**: `Cₙ(0) = Cₙ`, and `Cₙ(∞) = C_{n−1} = A_{n−1}/B_{n−1}`:
`(Aₙ + A_{n−1}w)/(Bₙ + B_{n−1}w) → A_{n−1}/B_{n−1}` as `w → ∞` (`B_{n−1} ≠ 0`). -/
theorem dlmf_1_12_21_limits (a b : ℕ → ℂ) (n : ℕ) (hQ : cfQ a b n ≠ 0) :
    cfw a b n 0 = cfConv a b n ∧
    Tendsto (fun w => (cfA a b n + cfP a b n * w) / (cfB a b n + cfQ a b n * w)) (cobounded ℂ)
      (𝓝 (cfP a b n / cfQ a b n)) := by
  refine ⟨rfl, ?_⟩
  have hcont : ContinuousAt (fun u : ℂ => (cfA a b n * u + cfP a b n) /
      (cfB a b n * u + cfQ a b n)) 0 :=
    ((continuous_const.mul continuous_id).add continuous_const).continuousAt.div
      ((continuous_const.mul continuous_id).add continuous_const).continuousAt (by simpa)
  have h := hcont.tendsto.comp tendsto_inv₀_cobounded
  simp only [mul_zero, zero_add] at h
  refine h.congr' ?_
  filter_upwards [show ({(0 : ℂ)}ᶜ : Set ℂ) ∈ cobounded ℂ from Bornology.isBounded_singleton]
    with w hw
  have hw0 : w ≠ 0 := hw
  simp only [Function.comp_apply]
  rw [← mul_div_mul_right _ _ hw0]
  congr 1 <;> field_simp

end Azurite.DLMF
