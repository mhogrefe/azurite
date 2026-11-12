/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter5.Section11RatioWatson
import Azurite.DLMF.Chapter4.Section9PadeExp

/-!
# DLMF §5.11(iii): Ratios (5.11.12–5.11.18)

Formalization of <https://dlmf.nist.gov/5.11#iii>, equations 5.11.12–5.11.18. As `z → ∞` in
`|ph z| ≤ π − δ`, with `a, b ∈ ℂ`:

* 5.11.12 (`dlmf_5_11_12`): `Γ(z + a)/Γ(z + b) ∼ z^{a−b}`;
* 5.11.13 (`dlmf_5_11_13`): `z^{b−a} Γ(z + a)/Γ(z + b) ∼ ∑ Gₖ(a, b) z^{−k}`;
* 5.11.14 (`dlmf_5_11_14`): with `w = z + ½(a + b − 1)`,
  `Γ(z + a)/Γ(z + b) ∼ w^{a−b} ∑ Hₖ(a, b) w^{−2k}` (no condition on `ℜ(b − a)`, as in DLMF 1.0.21);
* 5.11.15–5.11.16 (`dlmf_5_11_15`, `dlmf_5_11_16`): the first three `Gₖ`, `Hₖ`;
* 5.11.17–5.11.18 (`ratioG`, `ratioH`, the defining formulas):
  `Gₖ(a, b) = (a−b choose k) B_k^{(a−b+1)}(a)`,
  `Hₖ(a, b) = (a−b choose 2k) B_{2k}^{(a−b+1)}((a−b+1)/2)`,
  with the generalized Bernoulli polynomials of 24.16.1 (`genBernoulli`).

Proof. 5.11.8 gives an expansion with coefficients `eₖ(a, b)` (`isAsympExpansion_gammaRatio_exp`).
For `b = a + m + 1` Watson's lemma identifies `eₖ = Gₖ` (`ratioExpCoeff_eq_nat`). For fixed `a`
and `k` both sides are polynomials in `ρ = a − b` (`IsPolyFun`), equal at `ρ = −1, −2, …`, hence
everywhere (`ratioExpCoeff_eq`). 5.11.14 is 5.11.13 for `(a − c, b − c)` in the variable
`w = z + c`, `c = ½(a + b − 1)`: then `a − c = ½(a − b + 1)`, and `B_k^{(ℓ)}(ℓ/2) = 0` for odd
`k` leaves the even powers.
-/

open Complex Filter Topology Set Asymptotics PowerSeries
open scoped Real Nat

namespace Azurite.DLMF

/-! ### Polynomial functions -/

theorem isPolyFun_eval_sub (P : Polynomial ℂ) (a : ℂ) : IsPolyFun fun z => P.eval (a - z) :=
  ⟨P.comp (Polynomial.C a - Polynomial.X), fun _ => by simp⟩

/-- The formal exponential of polynomial coefficients is polynomial. -/
theorem isPolyFun_cSeriesExp {c : ℂ → ℕ → ℂ} (hc : ∀ s, IsPolyFun fun z => c z s) (k : ℕ) :
    IsPolyFun fun z => cSeriesExp (c z) k := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rcases k with _ | k
    · simpa [cSeriesExp_zero] using isPolyFun_const 1
    · simp only [cSeriesExp_succ, div_eq_mul_inv]
      refine IsPolyFun.mul (isPolyFun_sum _ fun i hi => ?_) (isPolyFun_const _)
      exact ((isPolyFun_const _).mul (hc (i + 1))).mul
        (ih (k - i) (by have := Finset.mem_range.mp hi; omega))

theorem isPolyFun_cBinom (k : ℕ) : IsPolyFun fun z => cBinom z k :=
  ⟨descPochhammer ℂ k * Polynomial.C ((k ! : ℂ))⁻¹, fun z => by simp [cBinom, div_eq_mul_inv]⟩

theorem isPolyFun_lnGammaShiftCoeff_sub (a : ℂ) (s : ℕ) :
    IsPolyFun fun z => lnGammaShiftCoeff (a - z) s := by
  unfold lnGammaShiftCoeff
  by_cases hs : s = 0
  · simpa [hs] using isPolyFun_const 0
  · simp only [hs, ↓reduceIte, div_eq_mul_inv]
    refine ((isPolyFun_const _).mul ?_).mul (isPolyFun_const _)
    have := isPolyFun_eval_sub ((Polynomial.bernoulli (s + 1)).map (algebraMap ℚ ℂ)) a
    simpa [Polynomial.aeval_def, Polynomial.eval_map] using this

theorem isPolyFun_genBernoulli_add_one (a : ℂ) (k : ℕ) :
    IsPolyFun fun z => genBernoulli (z + 1) a k := by
  unfold genBernoulli
  refine (isPolyFun_const _).mul (isPolyFun_cSeriesExp (fun s => ?_) k)
  unfold genBernoulliSeq
  exact ((isPolyFun_id.add (isPolyFun_const 1)).mul (isPolyFun_const _)).add (isPolyFun_const _)

/-! ### `eₖ(a, b) = Gₖ(a, b)` -/

/-- **DLMF 5.11.17**: `Gₖ(a, b) = (a−b choose k) B_k^{(a−b+1)}(a)`. -/
noncomputable def ratioG (a b : ℂ) (k : ℕ) : ℂ := cBinom (a - b) k * genBernoulli (a - b + 1) a k

/-- **DLMF 5.11.18**: `Hₖ(a, b) = (a−b choose 2k) B_{2k}^{(a−b+1)}((a − b + 1)/2)`. -/
noncomputable def ratioH (a b : ℂ) (k : ℕ) : ℂ :=
  cBinom (a - b) (2 * k) * genBernoulli (a - b + 1) ((a - b + 1) / 2) (2 * k)

theorem dlmf_5_11_17 (a b : ℂ) (k : ℕ) :
    ratioG a b k = cBinom (a - b) k * genBernoulli (a - b + 1) a k := rfl

theorem dlmf_5_11_18 (a b : ℂ) (k : ℕ) :
    ratioH a b k = cBinom (a - b) (2 * k) * genBernoulli (a - b + 1) ((a - b + 1) / 2) (2 * k) :=
  rfl

/-- The coefficients of 5.11.8 exponentiated are DLMF's `Gₖ`. -/
theorem ratioExpCoeff_eq (a b : ℂ) (k : ℕ) : ratioExpCoeff a b k = ratioG a b k := by
  set F : ℂ → ℂ := fun ρ => ratioExpCoeff a (a - ρ) k - cBinom ρ k * genBernoulli (ρ + 1) a k
    with hF
  have hpoly : IsPolyFun F := by
    refine IsPolyFun.sub ?_ ((isPolyFun_cBinom k).mul (isPolyFun_genBernoulli_add_one a k))
    unfold ratioExpCoeff ratioLogCoeff
    exact isPolyFun_cSeriesExp (fun s => (isPolyFun_const _).sub
      (isPolyFun_lnGammaShiftCoeff_sub a s)) k
  obtain ⟨P, hP⟩ := hpoly
  have hroot : ∀ m : ℕ, P.IsRoot (-((m : ℂ) + 1)) := fun m => by
    rw [Polynomial.IsRoot, ← hP, hF]
    simp only [sub_neg_eq_add]
    rw [ratioExpCoeff_eq_nat, show -((m : ℂ) + 1) + 1 = 1 - ((m + 1 : ℕ) : ℂ) by push_cast; ring,
      sub_self]
  have hP0 : P = 0 := by
    refine Polynomial.eq_zero_of_infinite_isRoot P ?_
    refine Set.infinite_of_injective_forall_mem (f := fun m : ℕ => -((m : ℂ) + 1))
      (fun m n h => by simpa using h) hroot
  have h := hP (a - b)
  rw [hP0, Polynomial.eval_zero, hF] at h
  simp only [sub_sub_cancel] at h
  rw [ratioG]
  linear_combination h

/-! ### DLMF 5.11.12–5.11.16 -/

/-- **DLMF 5.11.13**: as `z → ∞` in `|ph z| ≤ π − δ`,
`Γ(z + a)/Γ(z + b) ∼ z^{a−b} ∑_{k≥0} Gₖ(a, b)/zᵏ`, i.e.
`z^{b−a} Γ(z + a)/Γ(z + b) ∼ ∑ Gₖ z^{−k}`. -/
theorem dlmf_5_11_13 (a b : ℂ) {δ : ℝ} (hδ : 0 < δ) (hδπ : δ ≤ π) :
    IsAsympExpansionDLMF (closedSectorDLMF 0 (π - δ))
      (fun z => Gamma (z + a) / Gamma (z + b) / z ^ (a - b)) (ratioG a b) := by
  have h := isAsympExpansion_gammaRatio_exp a b hδ hδπ
  rwa [show ratioExpCoeff a b = ratioG a b from funext (ratioExpCoeff_eq a b)] at h

theorem cBinom_zero (z : ℂ) : cBinom z 0 = 1 := by simp [cBinom]

theorem cBinom_one (z : ℂ) : cBinom z 1 = z := by simp [cBinom]

theorem cBinom_two (z : ℂ) : cBinom z 2 = z * (z - 1) / 2 := by
  simp [cBinom, descPochhammer_succ_right, Nat.factorial]

/-- **DLMF 5.11.12**: `Γ(z + a)/Γ(z + b) ∼ z^{a−b}` as `z → ∞` in `|ph z| ≤ π − δ`. -/
theorem dlmf_5_11_12 (a b : ℂ) {δ : ℝ} (hδ : 0 < δ) (hδπ : δ ≤ π) :
    AsympEqDLMF (Bornology.cobounded ℂ ⊓ 𝓟 (closedSectorDLMF 0 (π - δ)))
      (fun z => Gamma (z + a) / Gamma (z + b)) (fun z => z ^ (a - b)) := by
  have h := isAsympExpansionDLMF_iff.mp (dlmf_5_11_13 a b hδ hδπ)
  have ht := h.tendsto (tendsto_inv_atInf _)
  unfold AsympEqDLMF
  simpa [ratioG, cBinom_zero, genBernoulli_zero] using ht

/-- **DLMF 5.11.15**: `G₀ = 1`, `G₁ = ½(a − b)(a + b − 1)`,
`G₂ = (1/12)(a−b choose 2)(3(a + b − 1)² − (a − b + 1))`. -/
theorem dlmf_5_11_15 (a b : ℂ) :
    ratioG a b 0 = 1 ∧ ratioG a b 1 = 1 / 2 * (a - b) * (a + b - 1) ∧
      ratioG a b 2 = 1 / 12 * cBinom (a - b) 2 * (3 * (a + b - 1) ^ 2 - (a - b + 1)) := by
  refine ⟨by simp [ratioG, cBinom_zero, genBernoulli_zero], ?_, ?_⟩
  · rw [ratioG, cBinom_one, genBernoulli_one]; ring
  · rw [ratioG, genBernoulli_two]; ring

theorem genBernoulli_half_four (ℓ : ℂ) :
    genBernoulli ℓ (ℓ / 2) 4 = (2 * ℓ + 5 * ℓ ^ 2) / 240 := by
  have h3 : bernoulli' 3 = 0 := bernoulli'_three
  have h4 : bernoulli' 4 = -1 / 30 := bernoulli'_four
  rw [genBernoulli, cSeriesExp_succ]
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add]
  norm_num [cSeriesExp_succ, cSeriesExp_one, cSeriesExp_zero, Finset.sum_range_succ,
    genBernoulliSeq, bernLog, h3, h4, bernoulli'_two, bernoulli'_one, Nat.factorial]
  ring

/-- **DLMF 5.11.16**: `H₀ = 1`, `H₁ = −(1/12)(a−b choose 2)(a − b + 1)`,
`H₂ = (1/240)(a−b choose 4)(2(a − b + 1) + 5(a − b + 1)²)`. -/
theorem dlmf_5_11_16 (a b : ℂ) :
    ratioH a b 0 = 1 ∧ ratioH a b 1 = -(1 / 12) * cBinom (a - b) 2 * (a - b + 1) ∧
      ratioH a b 2 = 1 / 240 * cBinom (a - b) 4 *
        (2 * (a - b + 1) + 5 * (a - b + 1) ^ 2) := by
  refine ⟨by simp [ratioH, cBinom_zero, genBernoulli_zero], ?_, ?_⟩
  · rw [ratioH, show 2 * 1 = 2 by rfl, genBernoulli_two]; ring
  · rw [ratioH, show 2 * 2 = 4 by rfl, genBernoulli_half_four]; ring

/-! ### DLMF 5.11.14 -/

/-- `Gₖ` at `(a − c, b − c)`, `c = ½(a + b − 1)`, vanishes for odd `k` and is `H_{k/2}` for
even `k`. -/
theorem ratioG_shift_odd (a b : ℂ) {k : ℕ} (hk : Odd k) :
    ratioG (a - (a + b - 1) / 2) (b - (a + b - 1) / 2) k = 0 := by
  rw [ratioG, show a - (a + b - 1) / 2 - (b - (a + b - 1) / 2) = a - b by ring,
    show a - (a + b - 1) / 2 = (a - b + 1) / 2 by ring, genBernoulli_half_odd _ hk, mul_zero]

theorem ratioG_shift_even (a b : ℂ) (j : ℕ) :
    ratioG (a - (a + b - 1) / 2) (b - (a + b - 1) / 2) (2 * j) = ratioH a b j := by
  rw [ratioG, ratioH, show a - (a + b - 1) / 2 - (b - (a + b - 1) / 2) = a - b by ring,
    show a - (a + b - 1) / 2 = (a - b + 1) / 2 by ring]

theorem sum_range_two_mul_split (f : ℕ → ℂ) (n : ℕ) :
    ∑ s ∈ Finset.range (2 * n), f s = ∑ j ∈ Finset.range n, (f (2 * j) + f (2 * j + 1)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 2 * (n + 1) = 2 * n + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ, ih,
      Finset.sum_range_succ]
    ring

/-- **DLMF 5.11.14**: as `z → ∞` in `|ph z| ≤ π − δ`, with `w = z + ½(a + b − 1)`,
`Γ(z + a)/Γ(z + b) ∼ w^{a−b} ∑_{k≥0} Hₖ(a, b)/w^{2k}`: for every `n`,
`w^{b−a} Γ(z + a)/Γ(z + b) − ∑_{k<n} Hₖ w^{−2k} = O(w^{−2n})`. -/
theorem dlmf_5_11_14 (a b : ℂ) {δ : ℝ} (hδ : 0 < δ) (hδπ : δ ≤ π) (n : ℕ) :
    (fun z => Gamma (z + a) / Gamma (z + b) / (z + (a + b - 1) / 2) ^ (a - b) -
        ∑ k ∈ Finset.range n, ratioH a b k / (z + (a + b - 1) / 2) ^ (2 * k)) =O[
      Bornology.cobounded ℂ ⊓ 𝓟 (closedSectorDLMF 0 (π - δ))]
      fun z => ((z + (a + b - 1) / 2) ^ (2 * n))⁻¹ := by
  set c := (a + b - 1) / 2
  set a' := a - c
  set b' := b - c
  have h13 := isAsympExpansionDLMF_iff.mp (dlmf_5_11_13 a' b' (half_pos hδ)
    (by linarith [Real.pi_pos]))
  rw [show π - δ / 2 = π - δ / 2 from rfl] at h13
  have h := (h13.comp_tendsto (tendsto_shift_sector hδ c)) (2 * n)
  refine (h.congr' ?_ ?_)
  · filter_upwards with z
    simp only [Function.comp_apply]
    rw [show z + c + a' = z + a by simp only [a', c]; ring,
      show z + c + b' = z + b by simp only [b', c]; ring,
      show a' - b' = a - b by simp only [a', b']; ring, eval_trunc_eq_sum]
    congr 1
    -- the odd coefficients vanish
    rw [sum_range_two_mul_split]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hodd : ratioG a' b' (2 * j + 1) = 0 := ratioG_shift_odd a b (odd_two_mul_add_one j)
    have heven : ratioG a' b' (2 * j) = ratioH a b j := ratioG_shift_even a b j
    rw [coeff_mk, coeff_mk, hodd, zero_mul, add_zero, heven, inv_pow, div_eq_mul_inv]
  · filter_upwards with z
    simp [inv_pow]

end Azurite.DLMF
