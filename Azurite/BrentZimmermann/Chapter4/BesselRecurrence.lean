/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.BrentZimmermann.Chapter4.Bessel
import Mathlib.Analysis.SpecialFunctions.Stirling

/-!
# Brent–Zimmermann §4.7.1: Evaluation of Bessel functions

The Bessel functions satisfy the three-term recurrence

  `J_{ν−1}(x) + J_{ν+1}(x) = (2ν/x) J_ν(x)`,                                                (4.51)

hence `J_{ν−1}/J_ν = 2ν/x − 1/(J_ν/J_{ν+1})`, which gives the continued fraction

  `J_ν(x)/J_{ν−1}(x) = 1/(2ν/x −) 1/(2(ν+1)/x −) 1/(2(ν+2)/x −) …`                           (4.52)

for the ratio (`ν ≥ 1`); this alone does not give `J_0` or `J_1`.  Miller's algorithm runs the
recurrence

  `f_{ν−1} + f_{ν+1} = (2ν/x) f_ν`                                                            (4.53)

backwards from `f_{ν'+1} = 0`, `f_{ν'} = 1` with `ν'` large, obtaining `f_0 ≈ c J_0(x)`, and
fixes the scale `c` with

  `J_0(x) + 2 ∑_{ν≥1} J_{2ν}(x) = 1`.                                                         (4.54)

The recurrence has the two independent solutions `J_ν` and `Y_ν`; `|Y_ν(x)|` grows exponentially
for `ν > ex/2` while `J_ν(x)` is bounded, so the unwanted component grows in the forward direction
and decays in the backward direction.  More precisely

  `J_ν(x) ~ (ex/(2ν))^ν / √(2πν)`,   `Y_ν(x) ~ −√(2/(πν)) (2ν/(ex))^ν`                    (4.55)

as `ν → ∞` with `x` fixed.

What is formalized:

* (4.51): `besselJNat_recurrence` (`(x/2)(J_n + J_{n+2}) = (n+1) J_{n+1}` from the series, by
  shifting one sum and the coefficient identity `bessel_rec_term`), then for all `ν ∈ ℤ`
  `besselJ_recurrence` (`x (J_{ν−1} + J_{ν+1}) = 2ν J_ν`) and the division form
  `besselJ_recurrence'` for `x ≠ 0`.
* (4.52): the one-step identity `besselJ_ratio_step`; `besselRatioCF x ν k r` — the `k`-fold
  nested fraction `1/(2ν/x −) … 1/(2(ν+k−1)/x − r)`; the *exact* finite identity
  `besselJ_ratio_eq_cf` (`J_ν/J_{ν−1} = besselRatioCF x ν k (J_{ν+k}/J_{ν+k−1})` whenever the
  intermediate `J`'s are nonzero); the coefficient sequences `besselCFNum`, `besselCFDen` of
  (4.52) in the `contFrac` framework and `approximant_besselCF` (its `k`-th approximant is
  `besselRatioCF x ν k 0`).
* (4.54): `hasSum_besselJ_int` (`∑_{ν∈ℤ} J_ν(x) = 1`), `hasSum_neg_one_zpow_besselJ`
  (`∑ (−1)^ν J_ν(x) = 1`), `hasSum_two_mul_besselJ_even`, and `besselJ_even_sum` (4.54).
* (4.53), Miller's algorithm: `millerSeq x N` (`f_{N+1} = 0`, `f_N = 1`, backward recurrence),
  `millerSeq_rec`, and the exact Casoratian identity `millerSeq_casoratian`:
  `f_ν J_{ν+1} − f_{ν+1} J_ν = J_{N+1}(x)` for `ν ≤ N` — so `f_ν/J_ν − f_{ν+1}/J_{ν+1} =
  J_{N+1}(x)/(J_ν J_{ν+1})` (`millerSeq_div_sub`): the computed sequence is proportional to
  `J` up to a defect proportional to the tiny `J_{N+1}(x)`.
* The solution space of (4.53): `IsBesselRecSol`, closed under `add`/`smul`, `casoratian`
  (constant), `eq_of_init` (a solution is determined by `f 0`, `f 1`), `exists_eq_comb` (every
  solution is a combination of two solutions with nonzero Casoratian), and
  `isBesselRecSol_besselJ`.
* The `J` half of (4.55) as inequalities: `abs_besselJNat_le`
  (`|J_n(x)| ≤ (|x|/2)^n/n! · e^(x²/4)`), `abs_besselJNat_le_stirling`
  (`|J_n(x)| ≤ e^(x²/4)/√(2πn) · (e|x|/(2n))^n`), `tendsto_besselJNat_atTop` (`J_n(x) → 0`).

Not formalized: convergence of (4.52) to the ratio (the text only says it "gives" the
fraction), `Y_ν` as a solution of (4.53) and its growth (4.55) (`besselY` is only defined), the
forward-instability statement, the region where Miller's algorithm is most effective, §4.12.
-/

namespace Azurite

namespace BZ

open Filter Topology Finset

/-! ### The recurrence (4.51) -/

/-- The coefficient identity behind (4.51), for the shifted terms `j + 1`. -/
theorem bessel_rec_term (n j : ℕ) (x : ℝ) :
    x / 2 * (besselCoeff n (j + 1) * (x / 2) ^ (2 * (j + 1) + n))
      + x / 2 * (besselCoeff (n + 2) j * (x / 2) ^ (2 * j + (n + 2)))
      = (n + 1) * (besselCoeff (n + 1) (j + 1) * (x / 2) ^ (2 * (j + 1) + (n + 1))) := by
  unfold besselCoeff
  rw [show 2 * (j + 1) + n = 2 * j + n + 2 by ring, show 2 * j + (n + 2) = 2 * j + n + 2 by ring,
    show 2 * (j + 1) + (n + 1) = 2 * j + n + 3 by ring,
    show n + (j + 1) = n + j + 1 by ring, show n + 2 + j = n + j + 1 + 1 by ring,
    show n + 1 + (j + 1) = n + j + 1 + 1 by ring, Nat.factorial_succ (n + j + 1),
    Nat.factorial_succ (n + j), Nat.factorial_succ j, pow_succ (x / 2) (2 * j + n + 2),
    pow_succ (-1 : ℝ) j]
  push_cast
  field_simp
  ring

/-- The `j = 0` term of (4.51). -/
theorem bessel_rec_term_zero (n : ℕ) (x : ℝ) :
    x / 2 * (besselCoeff n 0 * (x / 2) ^ (2 * 0 + n))
      = (n + 1) * (besselCoeff (n + 1) 0 * (x / 2) ^ (2 * 0 + (n + 1))) := by
  unfold besselCoeff
  rw [show 2 * 0 + n = n by ring, show 2 * 0 + (n + 1) = n + 1 by ring, add_zero, add_zero,
    Nat.factorial_succ n, pow_succ (x / 2) n]
  simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, one_mul]
  push_cast
  field_simp

/-- (4.51) in the factorial form: `(x/2)(J_n + J_{n+2}) = (n+1) J_{n+1}`. -/
theorem besselJNat_recurrence (n : ℕ) (x : ℝ) :
    x / 2 * (besselJNat n x + besselJNat (n + 2) x) = (n + 1) * besselJNat (n + 1) x := by
  have h0 := summable_besselJNat_term n x
  have h1 := summable_besselJNat_term (n + 1) x
  have h2 := summable_besselJNat_term (n + 2) x
  have hA : HasSum (fun j => x / 2 * (besselCoeff n (j + 1) * (x / 2) ^ (2 * (j + 1) + n)))
      (x / 2 * (besselJNat n x - besselCoeff n 0 * (x / 2) ^ (2 * 0 + n))) := by
    have := (hasSum_nat_add_iff' 1).mpr h0.hasSum
    rw [sum_range_one] at this
    exact this.mul_left (x / 2)
  have hB : HasSum (fun j => x / 2 * (besselCoeff (n + 2) j * (x / 2) ^ (2 * j + (n + 2))))
      (x / 2 * besselJNat (n + 2) x) := h2.hasSum.mul_left (x / 2)
  have hC : HasSum (fun j => ((n : ℝ) + 1) *
      (besselCoeff (n + 1) (j + 1) * (x / 2) ^ (2 * (j + 1) + (n + 1))))
      ((n + 1) * (besselJNat (n + 1) x - besselCoeff (n + 1) 0 * (x / 2) ^ (2 * 0 + (n + 1)))) := by
    have := (hasSum_nat_add_iff' 1).mpr h1.hasSum
    rw [sum_range_one] at this
    exact this.mul_left _
  have hAB := (hA.add hB).congr_fun fun j => (bessel_rec_term n j x).symm
  have huniq := hC.unique hAB
  have h00 := bessel_rec_term_zero n x
  linear_combination -huniq + h00

/-- (4.51) for all `ν ∈ ℤ`, product form: `x (J_{ν−1} + J_{ν+1}) = 2ν J_ν`. -/
theorem besselJ_recurrence (ν : ℤ) (x : ℝ) :
    x * (besselJ (ν - 1) x + besselJ (ν + 1) x) = 2 * ν * besselJ ν x := by
  rcases ν with n | n
  · rcases n with _ | n
    · simp only [Int.ofNat_eq_natCast, Nat.cast_zero, zero_sub, zero_add, Int.cast_zero,
        mul_zero, zero_mul]
      have h := besselJ_neg 1 x
      push_cast at h
      rw [h]
      ring
    · simp only [Int.ofNat_eq_natCast]
      rw [show ((n + 1 : ℕ) : ℤ) - 1 = (n : ℤ) by push_cast; ring,
        show ((n + 1 : ℕ) : ℤ) + 1 = ((n + 2 : ℕ) : ℤ) by push_cast; ring, besselJ_natCast,
        besselJ_natCast, besselJ_natCast]
      have := besselJNat_recurrence n x
      push_cast
      linear_combination 2 * this
  · rw [Int.negSucc_eq, show -((n : ℤ) + 1) - 1 = -((n + 2 : ℕ) : ℤ) by push_cast; ring,
      show -((n : ℤ) + 1) + 1 = -((n : ℕ) : ℤ) by ring, besselJ_neg, besselJ_neg,
      show -((n : ℤ) + 1) = -((n + 1 : ℕ) : ℤ) by push_cast; ring, besselJ_neg, besselJ_natCast,
      besselJ_natCast, besselJ_natCast]
    have := besselJNat_recurrence n x
    push_cast
    linear_combination 2 * (-1 : ℝ) ^ n * this

/-- (4.51): `J_{ν−1} + J_{ν+1} = (2ν/x) J_ν` for `x ≠ 0`. -/
theorem besselJ_recurrence' {x : ℝ} (hx : x ≠ 0) (ν : ℤ) :
    besselJ (ν - 1) x + besselJ (ν + 1) x = 2 * ν / x * besselJ ν x := by
  have h := besselJ_recurrence ν x
  have : 2 * (ν : ℝ) / x * besselJ ν x = x * (besselJ (ν - 1) x + besselJ (ν + 1) x) / x := by
    rw [h]; ring
  rw [this, mul_div_cancel_left₀ _ hx]

/-! ### The continued fraction (4.52) -/

/-- The one-step identity behind (4.52): `J_ν/J_{ν−1} = 1/(2ν/x − J_{ν+1}/J_ν)`. -/
theorem besselJ_ratio_step {x : ℝ} (hx : x ≠ 0) {ν : ℤ} (h1 : besselJ ν x ≠ 0) :
    besselJ ν x / besselJ (ν - 1) x = 1 / (2 * ν / x - besselJ (ν + 1) x / besselJ ν x) := by
  have h := besselJ_recurrence' hx ν
  have : 2 * (ν : ℝ) / x - besselJ (ν + 1) x / besselJ ν x = besselJ (ν - 1) x / besselJ ν x := by
    rw [eq_div_iff h1, sub_mul, div_mul_cancel₀ _ h1]
    linear_combination -h
  rw [this, one_div_div]

/-- The `k`-fold nested fraction of (4.52) with tail `r`:
`1/(2ν/x −) 1/(2(ν+1)/x −) … 1/(2(ν+k−1)/x − r)`. -/
noncomputable def besselRatioCF (x : ℝ) : ℤ → ℕ → ℝ → ℝ
  | _, 0, r => r
  | ν, k + 1, r => 1 / (2 * ν / x - besselRatioCF x (ν + 1) k r)

/-- (4.52) as an exact finite identity: if `J_ν, …, J_{ν+k−1}` do not vanish at `x ≠ 0`, then
`J_ν/J_{ν−1}` is the `k`-fold fraction closed by the true tail `J_{ν+k}/J_{ν+k−1}`. -/
theorem besselJ_ratio_eq_cf {x : ℝ} (hx : x ≠ 0) (ν : ℤ) (k : ℕ)
    (hJ : ∀ i : ℕ, i < k → besselJ (ν + i) x ≠ 0) :
    besselJ ν x / besselJ (ν - 1) x
      = besselRatioCF x ν k (besselJ (ν + k) x / besselJ (ν + k - 1) x) := by
  induction k generalizing ν with
  | zero => simp [besselRatioCF]
  | succ k ih =>
    have h1 : besselJ ν x ≠ 0 := by simpa using hJ 0 (by omega)
    rw [besselJ_ratio_step hx h1, besselRatioCF]
    congr 2
    have := ih (ν + 1) (fun i hi => by
      have := hJ (i + 1) (by omega)
      rwa [show ν + ((i + 1 : ℕ) : ℤ) = ν + 1 + i by push_cast; ring] at this)
    rw [show ν + 1 - 1 = ν by ring] at this
    rw [this, show ν + 1 + (k : ℤ) = ν + ((k + 1 : ℕ) : ℤ) by push_cast; ring]

/-- The partial numerators of (4.52): `a₁ = 1`, `a_j = −1` for `j ≥ 2`. -/
noncomputable def besselCFNum (j : ℕ) : ℝ := if j = 1 then 1 else -1

/-- The partial denominators of (4.52): `b₀ = 0`, `b_j = 2(ν+j−1)/x` for `j ≥ 1`. -/
noncomputable def besselCFDen (x : ℝ) (ν : ℤ) (j : ℕ) : ℝ :=
  if j = 0 then 0 else 2 * (ν + j - 1) / x

/-- The inner fractions of (4.52): with all partial numerators `−1`,
`2ν/x + (−1)/(2(ν+1)/x + (−1)/…) = 2ν/x − besselRatioCF x (ν+1) k 0`. -/
theorem approximant_besselCF_inner {a : ℕ → ℝ} (ha : ∀ j, 1 ≤ j → a j = -1) (x : ℝ) (ν : ℤ)
    (k : ℕ) :
    approximant a (fun j : ℕ => 2 * ((ν : ℝ) + j) / x) k
      = 2 * ν / x - besselRatioCF x (ν + 1) k 0 := by
  induction k generalizing ν a with
  | zero => simp [besselRatioCF]
  | succ k ih =>
    simp only [approximant_succ, ha 1 le_rfl]
    have hfun : (fun j : ℕ => 2 * ((ν : ℝ) + ((j + 1 : ℕ) : ℝ)) / x)
        = fun j : ℕ => 2 * (((ν + 1 : ℤ) : ℝ) + j) / x := by
      funext j; push_cast; ring
    rw [hfun, ih (fun j hj => ha (j + 1) (by omega)), besselRatioCF]
    push_cast
    ring

/-- The `k`-th approximant of (4.52) is the `k`-fold fraction with tail `0`. -/
theorem approximant_besselCF (x : ℝ) (ν : ℤ) (k : ℕ) :
    approximant besselCFNum (besselCFDen x ν) k = besselRatioCF x ν k 0 := by
  rcases k with _ | k
  · simp [besselCFDen, besselRatioCF]
  · have hb0 : besselCFDen x ν 0 = 0 := by simp [besselCFDen]
    have ha1 : besselCFNum 1 = 1 := by simp [besselCFNum]
    have ha : ∀ j, 1 ≤ j → besselCFNum (j + 1) = -1 := fun j hj => by
      rw [besselCFNum, ite_eq_right (by omega)]
    have hfun : (fun j => besselCFDen x ν (j + 1)) = fun j : ℕ => 2 * ((ν : ℝ) + j) / x := by
      funext j
      rw [besselCFDen, ite_eq_right (Nat.succ_ne_zero j)]
      push_cast
      ring
    rw [approximant_succ, hb0, ha1, hfun, approximant_besselCF_inner ha, besselRatioCF, zero_add]

/-! ### The normalization (4.54) -/

/-- `∑_{ν ∈ ℤ} J_ν(x) = 1` ((4.47) at `t = 1`). -/
theorem hasSum_besselJ_int (x : ℝ) : HasSum (fun ν : ℤ => besselJ ν x) 1 := by
  have := hasSum_besselJ_generating one_ne_zero x
  simpa using this

/-- `∑_{ν ∈ ℤ} (−1)^ν J_ν(x) = 1` ((4.47) at `t = −1`). -/
theorem hasSum_neg_one_zpow_besselJ (x : ℝ) :
    HasSum (fun ν : ℤ => (-1) ^ ν * besselJ ν x) 1 := by
  have := hasSum_besselJ_generating (by norm_num : (-1 : ℝ) ≠ 0) x
  rw [show x / 2 * (-1 - 1 / -1) = 0 by norm_num, Real.exp_zero] at this
  exact this

/-- `∑_{k ≥ 0} 2 J_{2k}(x) = 1 + J_0(x)`. -/
theorem hasSum_two_mul_besselJ_even (x : ℝ) :
    HasSum (fun k : ℕ => 2 * besselJ (2 * k) x) (1 + besselJ 0 x) := by
  have h := (hasSum_besselJ_int x).nat_add_neg
  have h2 : HasSum (fun n : ℕ => (1 + (-1) ^ n) * besselJ n x) (1 + besselJ 0 x) :=
    h.congr_fun fun n => by rw [besselJ_neg]; ring
  have hinj : Function.Injective (fun k : ℕ => 2 * k) := mul_right_injective₀ two_ne_zero
  have hzero : ∀ n, n ∉ Set.range (fun k : ℕ => 2 * k) →
      (1 + (-1 : ℝ) ^ n) * besselJ n x = 0 := by
    intro n hn
    have hodd : Odd n := by
      rcases Nat.even_or_odd n with ⟨m, hm⟩ | ho
      · exact absurd (Set.mem_range.mpr ⟨m, by show 2 * m = n; omega⟩) hn
      · exact ho
    rw [hodd.neg_one_pow]
    ring
  have := (hinj.hasSum_iff hzero).mpr h2
  refine this.congr_fun fun k => ?_
  simp only [Function.comp_apply]
  rw [pow_mul, neg_one_sq, one_pow]
  push_cast
  ring

/-- (4.54): `J_0(x) + 2 ∑_{ν ≥ 1} J_{2ν}(x) = 1`. -/
theorem besselJ_even_sum (x : ℝ) : besselJ 0 x + 2 * ∑' k : ℕ, besselJ (2 * (k + 1)) x = 1 := by
  have h := (hasSum_nat_add_iff' 1).mpr (hasSum_two_mul_besselJ_even x)
  rw [sum_range_one] at h
  have := h.tsum_eq
  rw [tsum_mul_left, Nat.cast_zero, mul_zero] at this
  push_cast at this ⊢
  linarith

/-! ### Miller's algorithm (4.53) -/

/-- Miller's backward sequence: `f_ν = 0` for `ν ≥ N+1`, `f_N = 1`, and
`f_ν = (2(ν+1)/x) f_{ν+1} − f_{ν+2}` for `ν < N` (the recurrence (4.53) at index `ν+1`). -/
noncomputable def millerSeq (x : ℝ) (N : ℕ) (ν : ℕ) : ℝ :=
  if N + 1 ≤ ν then 0
  else if ν = N then 1
  else 2 * (ν + 1) / x * millerSeq x N (ν + 1) - millerSeq x N (ν + 2)
termination_by N + 1 - ν

theorem millerSeq_of_le (x : ℝ) {N ν : ℕ} (h : N + 1 ≤ ν) : millerSeq x N ν = 0 := by
  rw [millerSeq, ite_eq_left h]

theorem millerSeq_self (x : ℝ) (N : ℕ) : millerSeq x N N = 1 := by
  rw [millerSeq, ite_eq_right (by omega), ite_eq_left rfl]

theorem millerSeq_of_lt (x : ℝ) {N ν : ℕ} (h : ν < N) :
    millerSeq x N ν = 2 * (ν + 1) / x * millerSeq x N (ν + 1) - millerSeq x N (ν + 2) := by
  rw [millerSeq, ite_eq_right (by omega), ite_eq_right (by omega)]

/-- The Miller sequence satisfies (4.53) for `1 ≤ μ ≤ N`. -/
theorem millerSeq_rec (x : ℝ) {N μ : ℕ} (hμ : 1 ≤ μ) (hμN : μ ≤ N) :
    millerSeq x N (μ - 1) + millerSeq x N (μ + 1) = 2 * μ / x * millerSeq x N μ := by
  have h := millerSeq_of_lt x (N := N) (ν := μ - 1) (by omega)
  rw [show μ - 1 + 1 = μ by omega, show μ - 1 + 2 = μ + 1 by omega, Nat.cast_pred hμ] at h
  rw [h]
  ring

/-- The Casoratian of the Miller sequence against `J`: `f_ν J_{ν+1} − f_{ν+1} J_ν = J_{N+1}(x)`
for all `ν ≤ N`.  So `f` is proportional to `J` up to a defect of size `J_{N+1}(x)`. -/
theorem millerSeq_casoratian {x : ℝ} (hx : x ≠ 0) (N : ℕ) :
    ∀ ν, ν ≤ N →
      millerSeq x N ν * besselJ (ν + 1) x - millerSeq x N (ν + 1) * besselJ ν x
        = besselJ (N + 1) x := by
  suffices h : ∀ d ν, ν + d = N →
      millerSeq x N ν * besselJ (ν + 1) x - millerSeq x N (ν + 1) * besselJ ν x
        = besselJ (N + 1) x from fun ν hν => h (N - ν) ν (by omega)
  intro d
  induction d with
  | zero =>
    intro ν hν
    obtain rfl : ν = N := by omega
    rw [millerSeq_self, millerSeq_of_le x le_rfl]
    ring
  | succ d ih =>
    intro ν hν
    have hν' := ih (ν + 1) (by omega)
    have hf := millerSeq_of_lt x (N := N) (ν := ν) (by omega)
    have hJ := besselJ_recurrence' hx ((ν : ℤ) + 1)
    rw [show (ν : ℤ) + 1 - 1 = ν by ring] at hJ
    rw [show ν + 1 + 1 = ν + 2 from rfl] at hν'
    push_cast at hν' hJ ⊢
    rw [hf]
    linear_combination (-millerSeq x N (ν + 1)) * hJ + hν'

/-- The ratio form of the Casoratian identity:
`f_ν/J_ν − f_{ν+1}/J_{ν+1} = J_{N+1}/(J_ν J_{ν+1})`. -/
theorem millerSeq_div_sub {x : ℝ} (hx : x ≠ 0) {N ν : ℕ} (hν : ν ≤ N)
    (h0 : besselJ ν x ≠ 0) (h1 : besselJ (ν + 1) x ≠ 0) :
    millerSeq x N ν / besselJ ν x - millerSeq x N (ν + 1) / besselJ (ν + 1) x
      = besselJ (N + 1) x / (besselJ ν x * besselJ (ν + 1) x) := by
  rw [div_sub_div _ _ h0 h1, mul_comm (besselJ (ν : ℤ) x) (millerSeq x N (ν + 1)),
    millerSeq_casoratian hx N ν hν]

/-! ### The solution space of (4.53) -/

/-- `f : ℕ → ℝ` solves the recurrence (4.53): `f (μ−1) + f (μ+1) = (2μ/x) f μ` for `μ ≥ 1`. -/
def IsBesselRecSol (x : ℝ) (f : ℕ → ℝ) : Prop :=
  ∀ μ : ℕ, 1 ≤ μ → f (μ - 1) + f (μ + 1) = 2 * μ / x * f μ

theorem isBesselRecSol_besselJ {x : ℝ} (hx : x ≠ 0) :
    IsBesselRecSol x fun n : ℕ => besselJ n x := by
  intro μ hμ
  have := besselJ_recurrence' hx μ
  rw [Int.cast_natCast] at this
  simp only
  rw [Nat.cast_pred hμ, Nat.cast_succ]
  exact this

theorem IsBesselRecSol.add {x : ℝ} {f g : ℕ → ℝ} (hf : IsBesselRecSol x f)
    (hg : IsBesselRecSol x g) : IsBesselRecSol x (f + g) := fun μ hμ => by
  simp only [Pi.add_apply]
  linear_combination hf μ hμ + hg μ hμ

theorem IsBesselRecSol.smul {x : ℝ} {f : ℕ → ℝ} (hf : IsBesselRecSol x f) (c : ℝ) :
    IsBesselRecSol x (c • f) := fun μ hμ => by
  simp only [Pi.smul_apply, smul_eq_mul]
  linear_combination c * hf μ hμ

/-- The Casoratian `f_n g_{n+1} − f_{n+1} g_n` of two solutions is constant. -/
theorem IsBesselRecSol.casoratian {x : ℝ} {f g : ℕ → ℝ} (hf : IsBesselRecSol x f)
    (hg : IsBesselRecSol x g) (n : ℕ) :
    f n * g (n + 1) - f (n + 1) * g n = f 0 * g 1 - f 1 * g 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hf' := hf (n + 1) (by omega)
    have hg' := hg (n + 1) (by omega)
    rw [Nat.add_sub_cancel] at hf' hg'
    rw [← ih]
    linear_combination (-g (n + 1)) * hf' + f (n + 1) * hg'

/-- A solution is determined by its first two values. -/
theorem IsBesselRecSol.eq_of_init {x : ℝ} {f g : ℕ → ℝ} (hf : IsBesselRecSol x f)
    (hg : IsBesselRecSol x g) (h0 : f 0 = g 0) (h1 : f 1 = g 1) : f = g := by
  funext n
  induction n using Nat.twoStepInduction with
  | zero => exact h0
  | one => exact h1
  | more n ih0 ih1 =>
    have hf' := hf (n + 1) (by omega)
    have hg' := hg (n + 1) (by omega)
    rw [Nat.add_sub_cancel, show n + 1 + 1 = n + 2 from rfl] at hf' hg'
    linear_combination hf' - hg' - ih0 + (2 * ((n + 1 : ℕ) : ℝ) / x) * ih1

/-- Every solution is a linear combination of two solutions with nonzero Casoratian (the
"general solution" of the text; with `g = J_ν`, `h = Y_ν` once `Y` is known to solve (4.53)). -/
theorem IsBesselRecSol.exists_eq_comb {x : ℝ} {f g h : ℕ → ℝ} (hg : IsBesselRecSol x g)
    (hh : IsBesselRecSol x h) (hW : g 0 * h 1 - g 1 * h 0 ≠ 0) (hf : IsBesselRecSol x f) :
    ∃ a b : ℝ, f = fun n => a * g n + b * h n := by
  refine ⟨(f 0 * h 1 - f 1 * h 0) / (g 0 * h 1 - g 1 * h 0),
    (g 0 * f 1 - g 1 * f 0) / (g 0 * h 1 - g 1 * h 0), ?_⟩
  have hc : IsBesselRecSol x fun n => (f 0 * h 1 - f 1 * h 0) / (g 0 * h 1 - g 1 * h 0) * g n
      + (g 0 * f 1 - g 1 * f 0) / (g 0 * h 1 - g 1 * h 0) * h n :=
    (hg.smul _).add (hh.smul _)
  refine hf.eq_of_init hc ?_ ?_
  · rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, eq_div_iff hW]
    ring
  · rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, eq_div_iff hW]
    ring

/-! ### Size of `J_n(x)` for large `n` (the `J` half of (4.55)) -/

/-- `|J_n(x)| ≤ (|x|/2)^n / n! · e^(x²/4)`. -/
theorem abs_besselJNat_le (n : ℕ) (x : ℝ) :
    |besselJNat n x| ≤ (|x| / 2) ^ n / n.factorial * Real.exp (x ^ 2 / 4) := by
  have hnorm : Summable fun j => ‖besselCoeff n j * (x / 2) ^ (2 * j + n)‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun j => norm_besselCoeff_mul_pow_le (abs_nonneg x) le_rfl n j) (summable_besselBound |x| n)
  have hexp := hasSum_exp_series (x ^ 2 / 4)
  have hbound : ∀ j, ‖besselCoeff n j * (x / 2) ^ (2 * j + n)‖
      ≤ (|x| / 2) ^ n / n.factorial * ((x ^ 2 / 4) ^ j / j.factorial) := by
    intro j
    rw [Real.norm_eq_abs, abs_mul, abs_besselCoeff_eq, abs_pow, abs_div, abs_two, pow_add,
      pow_mul, show (|x| / 2) ^ 2 = x ^ 2 / 4 by rw [div_pow, sq_abs]; norm_num]
    have hfac : (n.factorial : ℝ) ≤ (n + j).factorial := by
      exact_mod_cast Nat.factorial_le (Nat.le_add_right n j)
    have hle : (1 : ℝ) / (j.factorial * (n + j).factorial) ≤ 1 / (j.factorial * n.factorial) :=
      one_div_le_one_div_of_le (by positivity) (by gcongr)
    calc 1 / (j.factorial * (n + j).factorial : ℝ) * ((x ^ 2 / 4) ^ j * (|x| / 2) ^ n)
        ≤ 1 / (j.factorial * n.factorial : ℝ) * ((x ^ 2 / 4) ^ j * (|x| / 2) ^ n) := by gcongr
      _ = (|x| / 2) ^ n / n.factorial * ((x ^ 2 / 4) ^ j / j.factorial) := by ring
  have h0 : |besselJNat n x| = ‖∑' j, besselCoeff n j * (x / 2) ^ (2 * j + n)‖ := by
    unfold besselJNat
    exact (Real.norm_eq_abs _).symm
  have h1 : ‖∑' j, besselCoeff n j * (x / 2) ^ (2 * j + n)‖
      ≤ ∑' j, ‖besselCoeff n j * (x / 2) ^ (2 * j + n)‖ := norm_tsum_le_tsum_norm hnorm
  have h2 : ∑' j, ‖besselCoeff n j * (x / 2) ^ (2 * j + n)‖
      ≤ ∑' j, (|x| / 2) ^ n / n.factorial * ((x ^ 2 / 4) ^ j / j.factorial) :=
    hnorm.tsum_le_tsum hbound (hexp.summable.mul_left _)
  have h3 : ∑' j, (|x| / 2) ^ n / n.factorial * ((x ^ 2 / 4) ^ j / j.factorial)
      = (|x| / 2) ^ n / n.factorial * Real.exp (x ^ 2 / 4) := by
    rw [tsum_mul_left, hexp.tsum_eq]
  rw [h0, ← h3]
  exact h1.trans h2

/-- The Stirling form: `|J_n(x)| ≤ e^(x²/4)/√(2πn) · (e|x|/(2n))^n` for `n ≥ 1` — the upper-bound
half of `J_ν(x) ~ (ex/(2ν))^ν/√(2πν)` in (4.55). -/
theorem abs_besselJNat_le_stirling {n : ℕ} (hn : 1 ≤ n) (x : ℝ) :
    |besselJNat n x|
      ≤ Real.exp (x ^ 2 / 4) / Real.sqrt (2 * Real.pi * n) * (Real.exp 1 * |x| / (2 * n)) ^ n := by
  have hs := Stirling.le_factorial_stirling n
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hpos : 0 < Real.sqrt (2 * Real.pi * n) * (n / Real.exp 1) ^ n := by positivity
  calc |besselJNat n x| ≤ (|x| / 2) ^ n / n.factorial * Real.exp (x ^ 2 / 4) :=
        abs_besselJNat_le n x
    _ ≤ (|x| / 2) ^ n / (Real.sqrt (2 * Real.pi * n) * (n / Real.exp 1) ^ n)
          * Real.exp (x ^ 2 / 4) := by gcongr
    _ = Real.exp (x ^ 2 / 4) / Real.sqrt (2 * Real.pi * n) * (Real.exp 1 * |x| / (2 * n)) ^ n := by
        rw [div_pow, div_pow, div_pow, mul_pow, mul_pow]
        field_simp

/-- `J_n(x) → 0` as `n → ∞` for fixed `x`. -/
theorem tendsto_besselJNat_atTop (x : ℝ) : Tendsto (fun n => besselJNat n x) atTop (𝓝 0) := by
  have h : Tendsto (fun n : ℕ => (|x| / 2) ^ n / n.factorial * Real.exp (x ^ 2 / 4)) atTop
      (𝓝 (0 * Real.exp (x ^ 2 / 4))) :=
    (FloorSemiring.tendsto_pow_div_factorial_atTop (|x| / 2)).mul_const _
  rw [zero_mul] at h
  exact squeeze_zero_norm (fun n => by rw [Real.norm_eq_abs]; exact abs_besselJNat_le n x) h

end BZ

end Azurite
