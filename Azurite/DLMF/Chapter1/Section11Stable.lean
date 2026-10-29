/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Topology.UnitInterval

/-!
# DLMF §1.11(v): Stable Polynomials

Formalizations of <https://dlmf.nist.gov/1.11.v>, including a complete proof of the
**Hurwitz (Routh–Hurwitz) criterion**, which is not in Mathlib.

* 1.11.24: `IsStable` (all zeros have negative real part).
* 1.11.25–1.11.26: `hurwitzD f k = Dₖ = det (a_{2j+1−i})`, with DLMF's explicit
  `D₁`, `D₂`, `D₃` (`dlmf_1_11_25_one`, `_two`, `_three`).
* The criterion: `dlmf_1_11_v_hurwitz`. For `f ≠ 0`, `f` is stable iff `a₀ ≠ 0`,
  `D_{2k} > 0`, and `sign D_{2k+1} = sign a₀`.

Proof outline:

1. **Reversal** (`isStable_iff_hStable`). Pass to `g(z) = ∑ aᵢ z^{n−i} = zⁿ f(1/z)`, whose
   Hurwitz coefficients are the `aᵢ`. The form `hurwitz_criterion` then says `g` is stable iff
   `a₀ᵏ Dₖ > 0` for `k = 1, …, n`.
2. **The Routh step.** Set `μ = a₀/a₁`, let `B` be the odd part of `g`, and put
   `g₁ = g − μzB` (`hpoly_routh`).
   * Determinants: `Δ_{k+1}(g) = a₁ Δ_k(g₁)` (`hdet_succ`), via one unitriangular row operation
     and an expansion along column 0.
   * Stability: for `μ > 0`, `g` is stable iff `g₁` is (`hStable_routh_iff`). The proof uses the
     homotopy `hₜ = g + tμz(A − μzB)`. Its leading coefficient stays `a₀`, and `h₁ = (μz + 1)g₁`.
     By parity (`parity_parts_eq_zero`), no `hₜ` vanishes on `iℝ` unless `g` does.
   * Along the homotopy, the set of `t` where `hₜ` has a zero with `Re ≥ 0` is open (root
     persistence `exists_root_near`, via the factorization over `ℂ`). It is also closed
     (Cauchy bound `norm_le_of_root` plus Bolzano–Weierstrass). So it is all of `[0, 1]` or
     empty (`exists_rhp_root_iff_of_homotopy`).
3. **Vieta** (`div_pos_of_hStable`): stability forces `a₁/a₀ > 0`. Induction on the degree then
   finishes the proof.
-/

open Polynomial Finset Complex Filter Topology
open scoped ComplexConjugate

namespace Azurite.DLMF

/-! ### Polynomials in Hurwitz form `∑_{i=0}^{n} cᵢ z^{n−i}` -/

/-- `∑_{i=0}^{n} cᵢ z^{n−i}` as a complex polynomial with real coefficients. -/
noncomputable def hpoly (c : ℕ → ℝ) (n : ℕ) : ℂ[X] :=
  ∑ i ∈ range (n + 1), C (c i : ℂ) * X ^ (n - i)

/-- The coefficients with even index `i` (the terms `z^{n−i}` of the parity of `n`). -/
def cEven (c : ℕ → ℝ) (i : ℕ) : ℝ := if Even i then c i else 0

/-- The coefficients with odd index `i`. -/
def cOdd (c : ℕ → ℝ) (i : ℕ) : ℝ := if Even i then 0 else c i

theorem coeff_hpoly (c : ℕ → ℝ) (n d : ℕ) :
    (hpoly c n).coeff d = if d ≤ n then (c (n - d) : ℂ) else 0 := by
  rw [hpoly, finsetSum_coeff]
  simp only [coeff_C_mul_X_pow]
  split_ifs with hd
  · rw [Finset.sum_eq_single (n - d)]
    · exact ite_eq_left_iff.mpr fun h => absurd (by omega) h
    · intro i hi hne
      simp only [show ¬(d = n - i) by intro h; apply hne; have := mem_range.mp hi; omega,
        ↓reduceIte]
    · intro h
      exact absurd (mem_range.mpr (by omega)) h
  · exact Finset.sum_eq_zero fun i hi => by
      simp only [show ¬(d = n - i) by have := mem_range.mp hi; omega, ↓reduceIte]

theorem eval_hpoly (c : ℕ → ℝ) (n : ℕ) (z : ℂ) :
    (hpoly c n).eval z = ∑ i ∈ range (n + 1), (c i : ℂ) * z ^ (n - i) := by
  simp [hpoly, eval_finsetSum]

theorem hpoly_add (c d : ℕ → ℝ) (n : ℕ) :
    hpoly (fun i => c i + d i) n = hpoly c n + hpoly d n := by
  simp only [hpoly, ← sum_add_distrib, ofReal_add, C_add, add_mul]

theorem hpoly_even_add_odd (c : ℕ → ℝ) (n : ℕ) :
    hpoly (cEven c) n + hpoly (cOdd c) n = hpoly c n := by
  rw [← hpoly_add]
  congr 1
  funext i
  simp only [cEven, cOdd]
  split_ifs <;> ring

theorem conj_eval_hpoly (c : ℕ → ℝ) (n : ℕ) (z : ℂ) :
    conj ((hpoly c n).eval z) = (hpoly c n).eval (conj z) := by
  simp [eval_hpoly, map_sum, map_mul, map_pow, conj_ofReal]

theorem neg_one_pow_sub {n i : ℕ} (hi : i ≤ n) :
    ((-1 : ℂ) ^ (n - i)) = (-1) ^ n * (-1) ^ i := by
  have h : ((-1 : ℂ) ^ (n - i)) * (-1) ^ i = (-1) ^ n := by
    rw [← pow_add, Nat.sub_add_cancel hi]
  have h2 : ((-1 : ℂ) ^ i) * (-1) ^ i = 1 := by rw [← pow_add, ← two_mul, pow_mul]; simp
  calc ((-1 : ℂ) ^ (n - i)) = (-1) ^ (n - i) * ((-1) ^ i * (-1) ^ i) := by rw [h2, mul_one]
    _ = (-1) ^ n * (-1) ^ i := by rw [← mul_assoc, h]

theorem eval_neg_hpoly_cEven (c : ℕ → ℝ) (n : ℕ) (z : ℂ) :
    (hpoly (cEven c) n).eval (-z) = (-1) ^ n * (hpoly (cEven c) n).eval z := by
  rw [eval_hpoly, eval_hpoly, mul_sum]
  refine sum_congr rfl fun i hi => ?_
  have hi' : i ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hi)
  rw [neg_pow, neg_one_pow_sub hi']
  simp only [cEven]
  split_ifs with he
  · rw [he.neg_one_pow]
    ring
  · simp

theorem eval_neg_hpoly_cOdd (c : ℕ → ℝ) (n : ℕ) (z : ℂ) :
    (hpoly (cOdd c) n).eval (-z) = -((-1) ^ n * (hpoly (cOdd c) n).eval z) := by
  rw [eval_hpoly, eval_hpoly, mul_sum, ← sum_neg_distrib]
  refine sum_congr rfl fun i hi => ?_
  have hi' : i ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hi)
  rw [neg_pow, neg_one_pow_sub hi']
  simp only [cOdd]
  split_ifs with he
  · simp
  · rw [(Nat.not_even_iff_odd.mp he).neg_one_pow]
    ring

/-- On the imaginary axis the two parity parts cannot cancel: if `E(−z) = sE(z)`,
`O(−z) = −sO(z)` (`s = ±1`) and both have real coefficients, then `E(iω) + O(iω) = 0` forces
`E(iω) = O(iω) = 0`. -/
theorem parity_parts_eq_zero {E O : ℂ → ℂ} {s : ℂ} (hs : s ≠ 0) (hE : ∀ z, E (-z) = s * E z)
    (hO : ∀ z, O (-z) = -(s * O z)) (hEc : ∀ z, conj (E z) = E (conj z))
    (hOc : ∀ z, conj (O z) = O (conj z)) {ω : ℝ} (h : E (ω * I) + O (ω * I) = 0) :
    E (ω * I) = 0 ∧ O (ω * I) = 0 := by
  have hc : conj ((ω : ℂ) * I) = -(ω * I) := by simp
  have h1 := congrArg conj h
  rw [map_add, hEc, hOc, hc, hE, hO, map_zero] at h1
  have hEO : E (ω * I) = O (ω * I) := by
    have : s * (E (ω * I) - O (ω * I)) = 0 := by linear_combination h1
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left hs)
  have hE0 : E (ω * I) = 0 := by linear_combination (h + hEO) / 2
  exact ⟨hE0, by rw [← hEO, hE0]⟩

/-! ### The Routh reduction -/

/-- One Routh step: `c′ᵢ = c_{i+1}` for even `i`, `c′ᵢ = c_{i+1} − μ c_{i+2}` for odd `i`,
`μ = c₀/c₁`. -/
noncomputable def routh (c : ℕ → ℝ) (i : ℕ) : ℝ :=
  if Even i then c (i + 1) else c (i + 1) - c 0 / c 1 * c (i + 2)

/-- The Routh step as a polynomial identity: `g − μ z B = g₁`, `B` the odd part. -/
theorem hpoly_routh {c : ℕ → ℝ} {n : ℕ} (hc1 : c 1 ≠ 0) (hc : ∀ i > n + 1, c i = 0) :
    hpoly c (n + 1) - C ((c 0 / c 1 : ℝ) : ℂ) * X * hpoly (cOdd c) (n + 1) =
      hpoly (routh c) n := by
  ext d
  rw [coeff_sub, mul_assoc, coeff_C_mul, coeff_hpoly, coeff_hpoly]
  rcases d with _ | e
  · rw [coeff_X_mul_zero, mul_zero, sub_zero]
    simp only [zero_le, ↓reduceIte, Nat.sub_zero, routh]
    split_ifs
    · rfl
    · rw [hc (n + 2) (by omega)]
      simp
  · rw [coeff_X_mul, coeff_hpoly]
    simp only [cOdd, routh]
    by_cases h1 : e + 1 ≤ n
    · have h2 : e ≤ n + 1 := by omega
      simp only [h1, h2, show e + 1 ≤ n + 1 by omega, ↓reduceIte]
      rw [show n + 1 - (e + 1) = n - e by omega, show n + 1 - e = n - e + 1 by omega,
        show n - (e + 1) + 1 = n - e by omega, show n - (e + 1) + 2 = n - e + 1 by omega]
      have hpar : Even (n - (e + 1)) ↔ Even (n - e + 1) := by
        rw [show n - e + 1 = n - (e + 1) + 2 by omega, Nat.even_add]
        simp
      by_cases he : Even (n - (e + 1))
      · simp only [he, ↓reduceIte, hpar.mp he]
        simp
      · simp only [he, ↓reduceIte, show ¬ Even (n - e + 1) from fun h => he (hpar.mpr h)]
        push_cast
        ring
    · simp only [h1, ↓reduceIte]
      by_cases h2 : e + 1 ≤ n + 1
      · have he : e = n := by omega
        rw [he]
        simp only [le_refl, show n ≤ n + 1 by omega, ↓reduceIte, Nat.sub_self,
          show n + 1 - n = 1 by omega]
        have h1' : (c 1 : ℂ) ≠ 0 := ofReal_ne_zero.mpr hc1
        simp [show ¬ Even 1 by decide]
        field_simp
        ring
      · by_cases h3 : e ≤ n + 1
        · have he : e = n + 1 := by omega
          rw [he]
          simp
        · simp [h2, h3]

/-! ### Hurwitz determinants -/

/-- The Hurwitz determinant `det (a_{2j+1−i})_{0 ≤ i, j < k}` of a coefficient sequence
`a : ℤ → ℝ`. -/
noncomputable def hdet (a : ℤ → ℝ) (k : ℕ) : ℝ :=
  (Matrix.of fun i j : Fin k => a (2 * (j : ℤ) + 1 - i)).det

/-- One Routh step on Hurwitz determinants: `Δ_{k+1}(a) = a₁ Δ_k(a′)` where
`a′_m = a_{m+1}` (`m` even), `a′_m = a_{m+1} − μ a_{m+2}` (`m` odd), if `a₀ = μ a₁` and
`a_m = 0` for `m < 0`. -/
theorem hdet_succ (a : ℤ → ℝ) (μ : ℝ) (ha : ∀ m < 0, a m = 0) (h0 : a 0 - μ * a 1 = 0)
    (k : ℕ) :
    hdet a (k + 1) = a 1 *
      hdet (fun m => if Odd m then a (m + 1) - μ * a (m + 2) else a (m + 1)) k := by
  set M : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ := Matrix.of fun i j => a (2 * (j : ℤ) + 1 - i)
  set L : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ := Matrix.of fun i j =>
    if i = j then 1 else if (j : ℕ) + 1 = i ∧ Odd (i : ℕ) then -μ else 0 with hLdef
  have hL : L.det = 1 := by
    rw [Matrix.det_of_isLowerTriangular]
    · simp [L]
    · intro i j hij
      have hij' : i < j := hij
      simp only [L, Matrix.of_apply, ne_of_lt hij', ↓reduceIte]
      have : ¬ ((j : ℕ) + 1 = i) := by have := Fin.lt_def.mp hij'; omega
      simp [this]
  set N : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ := Matrix.of fun i j =>
    a (2 * (j : ℤ) + 1 - i) - if Odd (i : ℕ) then μ * a (2 * (j : ℤ) + 2 - i) else 0 with hNdef
  have hLM : L * M = N := by
    ext i j
    rw [Matrix.mul_apply]
    have hsplit : ∀ l : Fin (k + 1), L i l * M l j = (if l = i then M i j else 0) +
        (if (l : ℕ) + 1 = i ∧ Odd (i : ℕ) then -μ * M l j else 0) := by
      intro l
      simp only [L, Matrix.of_apply]
      by_cases hli : l = i
      · subst hli
        simp
      · have : ¬ (i = l) := fun h => hli h.symm
        simp only [this, hli, ↓reduceIte, zero_add]
        split_ifs <;> ring
    rw [Finset.sum_congr rfl fun l _ => hsplit l, sum_add_distrib, Finset.sum_ite_eq']
    simp only [mem_univ, ↓reduceIte, N, M, Matrix.of_apply]
    by_cases hodd : Odd (i : ℕ)
    · have hi0 : 1 ≤ (i : ℕ) := by obtain ⟨r, hr⟩ := hodd; omega
      have hmem : (⟨(i : ℕ) - 1, by omega⟩ : Fin (k + 1)) ∈ (univ : Finset (Fin (k + 1))) :=
        mem_univ _
      rw [Finset.sum_eq_single_of_mem _ hmem]
      · simp only [show (i : ℕ) - 1 + 1 = i by omega, hodd, and_self, ↓reduceIte]
        push_cast [Nat.cast_sub hi0]
        ring_nf
      · intro l _ hl
        have : ¬ ((l : ℕ) + 1 = i) := fun h => hl (Fin.ext (by simp; omega))
        simp [this]
    · simp [hodd]
  have hdetM : hdet a (k + 1) = N.det := by
    rw [hdet, ← hLM, Matrix.det_mul, hL, one_mul]
  rw [hdetM, Matrix.det_succ_column_zero, Fin.sum_univ_succ]
  have hcol : ∀ r : Fin k, N r.succ 0 = 0 := by
    intro r
    simp only [N, Matrix.of_apply, Fin.val_succ, Fin.val_zero, Nat.cast_zero, mul_zero, zero_add]
    by_cases hr : (r : ℕ) = 0
    · simp only [hr, zero_add, show Odd 1 by decide, ↓reduceIte, Nat.cast_one]
      norm_num
      linarith [h0]
    · have h1 : a (1 - ((r : ℕ) + 1 : ℕ)) = 0 := ha _ (by push_cast; omega)
      rw [h1]
      split_ifs with ho
      · have : a (2 - ((r : ℕ) + 1 : ℕ)) = 0 := ha _ (by
          obtain ⟨q, hq⟩ := ho
          push_cast
          omega)
        rw [this]
        ring
      · ring
  simp only [hcol, mul_zero, zero_mul, Finset.sum_const_zero, add_zero, Fin.val_zero, pow_zero,
    one_mul, Fin.succAbove_zero]
  congr 1
  · simp [N]
  · rw [hdet]
    congr 1
    ext i j
    simp only [N, Matrix.submatrix_apply, Matrix.of_apply, Fin.val_succ]
    push_cast
    have hpar : Odd ((i : ℕ) + 1) ↔ Odd (2 * (j : ℤ) + 1 - i) := by
      rw [Nat.odd_iff, Int.odd_iff]
      omega
    by_cases ho : Odd ((i : ℕ) + 1)
    · simp only [ho, ↓reduceIte, hpar.mp ho]
      ring_nf
    · simp only [ho, ↓reduceIte, show ¬ Odd (2 * (j : ℤ) + 1 - i) from fun h => ho (hpar.mpr h)]
      ring_nf

/-! ### Roots of complex polynomials -/

/-- A complex polynomial is (Hurwitz) stable if all its zeros have negative real part. -/
def HStable (p : ℂ[X]) : Prop := ∀ z : ℂ, p.eval z = 0 → z.re < 0

theorem pow_card_le_norm_prod (z₀ : ℂ) {ε : ℝ} (hε : 0 ≤ ε) (s : Multiset ℂ)
    (h : ∀ a ∈ s, ε ≤ ‖z₀ - a‖) :
    ε ^ Multiset.card s ≤ ‖(s.map fun a => z₀ - a).prod‖ := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, norm_mul, Multiset.card_cons, pow_succ, mul_comm]
    exact mul_le_mul (h a (Multiset.mem_cons_self a s))
      (ih fun b hb => h b (Multiset.mem_cons_of_mem hb)) (pow_nonneg hε _) (norm_nonneg _)

/-- Root persistence: if `|p(z₀)| < |lc(p)| εⁿ`, then `p` has a zero within `ε` of `z₀`. -/
theorem exists_root_near {p : ℂ[X]} {z₀ : ℂ} {ε : ℝ} (hε : 0 ≤ ε)
    (h : ‖p.eval z₀‖ < ‖p.leadingCoeff‖ * ε ^ p.natDegree) :
    ∃ w, p.eval w = 0 ∧ ‖z₀ - w‖ < ε := by
  have hcard := splits_iff_card_roots.mp (IsAlgClosed.splits p)
  have hfac := C_leadingCoeff_mul_prod_multiset_X_sub_C hcard
  have hp0 : p ≠ 0 := by
    rintro rfl
    simp at h
  by_contra hno
  push Not at hno
  have hbound := pow_card_le_norm_prod z₀ hε p.roots fun a ha =>
    hno a ((mem_roots hp0).mp ha)
  have heval : p.eval z₀ = p.leadingCoeff * (p.roots.map fun a => z₀ - a).prod := by
    conv_lhs => rw [← hfac]
    simp [eval_multiset_prod, Multiset.map_map]
  rw [heval, norm_mul, ← hcard] at h
  exact absurd (mul_le_mul_of_nonneg_left hbound (norm_nonneg _)) (not_le.mpr h)

/-- A Cauchy-type bound: a zero of `p = a z^N + ∑_{k<N} p_k z^k` with `|p_k| ≤ K` satisfies
`|z| ≤ max 1 (NK/|a|)`. -/
theorem norm_le_of_root {p : ℂ[X]} {N : ℕ} (hN : 1 ≤ N) (hdeg : p.natDegree ≤ N)
    (hlead : p.coeff N ≠ 0) {K : ℝ} (hK : ∀ k < N, ‖p.coeff k‖ ≤ K) {z : ℂ}
    (hz : p.eval z = 0) : ‖z‖ ≤ max 1 (N * K / ‖p.coeff N‖) := by
  by_contra hlt
  push Not at hlt
  obtain ⟨h1, h2⟩ := max_lt_iff.mp hlt
  have ha : 0 < ‖p.coeff N‖ := norm_pos_iff.mpr hlead
  have hK0 : 0 ≤ K := (norm_nonneg _).trans (hK 0 (by omega))
  rw [eval_eq_sum_range' (Nat.lt_succ_of_le hdeg), sum_range_succ] at hz
  have hmain : ‖p.coeff N‖ * ‖z‖ ^ N ≤ N * K * ‖z‖ ^ (N - 1) := by
    have heq : p.coeff N * z ^ N = -∑ k ∈ range N, p.coeff k * z ^ k := by
      linear_combination hz
    calc ‖p.coeff N‖ * ‖z‖ ^ N = ‖∑ k ∈ range N, p.coeff k * z ^ k‖ := by
          rw [← norm_pow, ← norm_mul, heq, norm_neg]
      _ ≤ ∑ k ∈ range N, ‖p.coeff k‖ * ‖z‖ ^ k := by
          refine (norm_sum_le _ _).trans (le_of_eq ?_)
          simp [norm_pow]
      _ ≤ ∑ _k ∈ range N, K * ‖z‖ ^ (N - 1) := by
          refine sum_le_sum fun k hk => ?_
          exact mul_le_mul (hK k (mem_range.mp hk))
            (pow_le_pow_right₀ h1.le (by have := mem_range.mp hk; omega)) (by positivity) hK0
      _ = N * K * ‖z‖ ^ (N - 1) := by simp; ring
  have hzpos : 0 < ‖z‖ ^ (N - 1) := by positivity
  have : ‖p.coeff N‖ * ‖z‖ ≤ N * K := by
    have h' : ‖z‖ ^ N = ‖z‖ ^ (N - 1) * ‖z‖ := by
      rw [← pow_succ, Nat.sub_add_cancel hN]
    rw [h'] at hmain
    nlinarith
  have := (div_lt_iff₀ ha).mp h2
  linarith

theorem natDegree_hpoly_le (c : ℕ → ℝ) (n : ℕ) : (hpoly c n).natDegree ≤ n :=
  natDegree_le_iff_coeff_eq_zero.mpr fun d hd => by
    rw [coeff_hpoly]
    simp [show ¬ d ≤ n by exact_mod_cast not_le.mpr hd]

theorem hpoly_natDegree {c : ℕ → ℝ} {n : ℕ} (hc0 : c 0 ≠ 0) :
    (hpoly c n).natDegree = n ∧ (hpoly c n).leadingCoeff = c 0 := by
  have hcoeff : (hpoly c n).coeff n = c 0 := by simp [coeff_hpoly]
  have hdeg : (hpoly c n).natDegree = n :=
    natDegree_eq_of_le_of_coeff_ne_zero (natDegree_hpoly_le c n)
      (by rw [hcoeff]; exact_mod_cast hc0)
  exact ⟨hdeg, by rw [leadingCoeff, hdeg, hcoeff]⟩

/-- Vieta: a stable polynomial `c₀zⁿ + c₁z^{n−1} + ⋯` (`n ≥ 1`) has `c₁/c₀ > 0`. -/
theorem div_pos_of_hStable {c : ℕ → ℝ} {n : ℕ} (hc0 : c 0 ≠ 0)
    (hst : HStable (hpoly c (n + 1))) : 0 < c 1 / c 0 := by
  obtain ⟨hdeg, hlc⟩ := hpoly_natDegree (n := n + 1) hc0
  set p := hpoly c (n + 1)
  have hp0 : p ≠ 0 := fun h => by
    rw [h, natDegree_zero] at hdeg
    omega
  have hnext : p.nextCoeff = c 1 := by
    rw [nextCoeff_of_natDegree_pos (by omega), hdeg, coeff_hpoly]
    simp
  have hv := (IsAlgClosed.splits p).nextCoeff_eq_neg_sum_roots_mul_leadingCoeff
  rw [hnext, hlc] at hv
  have hcard := splits_iff_card_roots.mp (IsAlgClosed.splits p)
  -- the real part of the sum of the roots is negative
  have hre : ∀ s : Multiset ℂ, s ≠ 0 → (∀ a ∈ s, a.re < 0) → s.sum.re < 0 := by
    intro s
    induction s using Multiset.induction_on with
    | empty => intro h; exact absurd rfl h
    | cons a s ih =>
      intro _ hall
      rw [Multiset.sum_cons, add_re]
      by_cases hs : s = 0
      · subst hs
        simpa using hall a (Multiset.mem_cons_self a 0)
      · linarith [hall a (Multiset.mem_cons_self a s),
          ih hs fun b hb => hall b (Multiset.mem_cons_of_mem hb)]
  have hne : p.roots ≠ 0 := by
    intro h
    rw [h, Multiset.card_zero, hdeg] at hcard
    omega
  have hneg := hre p.roots hne fun a ha => hst a ((mem_roots hp0).mp ha)
  have hc0' : (c 0 : ℂ) ≠ 0 := ofReal_ne_zero.mpr hc0
  have hq : ((c 1 / c 0 : ℝ) : ℂ) = -p.roots.sum := by
    push_cast
    rw [hv]
    field_simp
  have := congrArg re hq
  rw [ofReal_re, neg_re] at this
  linarith

/-! ### The Routh step preserves stability -/

/-- The coefficients of `A₁ = A − μzB` vanish from degree `n` on (`A`, `B` the parity parts of
`∑_{i=0}^{n+1} cᵢ z^{n+1−i}`, `μ = c₀/c₁`). -/
theorem coeff_A₁_eq_zero {c : ℕ → ℝ} {n : ℕ} (hc1 : c 1 ≠ 0) {e : ℕ} (he : n ≤ e) :
    (hpoly (cEven c) (n + 1) - C ((c 0 / c 1 : ℝ) : ℂ) * X * hpoly (cOdd c) (n + 1)).coeff e
      = 0 := by
  rw [coeff_sub, mul_assoc, coeff_C_mul]
  obtain ⟨d, rfl⟩ : ∃ d, e = n + d := ⟨e - n, by omega⟩
  rcases d with _ | _ | d
  · rw [add_zero, coeff_hpoly]
    simp only [show n ≤ n + 1 by omega, ↓reduceIte, show n + 1 - n = 1 by omega, cEven,
      show ¬ Even 1 by decide]
    rcases n with _ | m
    · simp
    · rw [coeff_X_mul, coeff_hpoly]
      simp [cOdd, show m + 1 + 1 - m = 2 by omega]
  · rw [coeff_hpoly, show n + (0 + 1) = n + 1 by omega, coeff_X_mul, coeff_hpoly]
    simp only [le_refl, ↓reduceIte, Nat.sub_self, cEven, cOdd, show n ≤ n + 1 by omega,
      show n + 1 - n = 1 by omega, show Even 0 by decide, show ¬ Even 1 by decide]
    have : (c 1 : ℂ) ≠ 0 := ofReal_ne_zero.mpr hc1
    push_cast
    field_simp
    ring
  · rw [coeff_hpoly, show n + (d + 1 + 1) = (n + d + 1) + 1 by omega, coeff_X_mul, coeff_hpoly]
    simp only [show ¬ (n + d + 1 + 1 ≤ n + 1) by omega, ↓reduceIte]
    by_cases hd : n + d + 1 ≤ n + 1
    · simp [hd, cOdd, show n + 1 - (n + d + 1) = 0 by omega]
    · simp [hd]

/-- Stability along an affine homotopy `P + tQ` (`0 ≤ t ≤ 1`) of polynomials of fixed degree `N`
and fixed leading coefficient, none of which vanishes on the imaginary axis: `P` has a zero in
the closed right half-plane iff `P + Q` does. -/
theorem exists_rhp_root_iff_of_homotopy {P Q : ℂ[X]} {N : ℕ} {a : ℂ} (hN : 1 ≤ N) (ha : a ≠ 0)
    (hle : ∀ t : ℝ, (P + C (t : ℂ) * Q).natDegree ≤ N)
    (htop : ∀ t : ℝ, (P + C (t : ℂ) * Q).coeff N = a)
    (him : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → ∀ z, (P + C (t : ℂ) * Q).eval z = 0 → z.re ≠ 0) :
    (∃ z, P.eval z = 0 ∧ 0 ≤ z.re) ↔ (∃ z, (P + Q).eval z = 0 ∧ 0 ≤ z.re) := by
  have hev : ∀ (t : ℝ) z, (P + C (t : ℂ) * Q).eval z = P.eval z + t * Q.eval z := fun t z => by
    simp
  have hdeg : ∀ t : ℝ, (P + C (t : ℂ) * Q).natDegree = N := fun t =>
    natDegree_eq_of_le_of_coeff_ne_zero (hle t) (by rw [htop]; exact ha)
  have hlc : ∀ t : ℝ, (P + C (t : ℂ) * Q).leadingCoeff = a := fun t => by
    rw [leadingCoeff, hdeg, htop]
  -- a uniform bound for the zeros
  set K : ℝ := ∑ k ∈ range N, (‖P.coeff k‖ + ‖Q.coeff k‖) with hKdef
  have hbound : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → ∀ z, P.eval z + t * Q.eval z = 0 →
      ‖z‖ ≤ max 1 (N * K / ‖a‖) := by
    intro t ht0 ht1 z hz
    have := norm_le_of_root (p := P + C (t : ℂ) * Q) hN (hle t) (by rw [htop]; exact ha)
      (K := K) (fun k hk => by
        rw [coeff_add, coeff_C_mul]
        calc ‖P.coeff k + (t : ℂ) * Q.coeff k‖ ≤ ‖P.coeff k‖ + ‖Q.coeff k‖ := by
              refine (norm_add_le _ _).trans (add_le_add le_rfl ?_)
              rw [norm_mul, norm_real, Real.norm_of_nonneg ht0]
              exact mul_le_of_le_one_left (norm_nonneg _) ht1
          _ ≤ K := single_le_sum (f := fun k => ‖P.coeff k‖ + ‖Q.coeff k‖)
              (fun i _ => by positivity) (mem_range.mpr hk))
      (by rw [hev]; exact hz)
    rwa [htop] at this
  set S : Set unitInterval := {t | ∃ z, P.eval z + (t : ℝ) * Q.eval z = 0 ∧ 0 ≤ z.re}
    with hSdef
  have hFcont : Continuous fun q : ℝ × ℂ => P.eval q.2 + (q.1 : ℂ) * Q.eval q.2 :=
    (P.continuous.comp continuous_snd).add
      ((continuous_ofReal.comp continuous_fst).mul (Q.continuous.comp continuous_snd))
  have hopen : IsOpen S := by
    rw [Metric.isOpen_iff]
    rintro t ⟨z₀, hz₀, hre⟩
    have hr : 0 < z₀.re :=
      lt_of_le_of_ne hre (him t t.2.1 t.2.2 z₀ (by rw [hev]; exact hz₀)).symm
    set K₀ := ‖Q.eval z₀‖
    refine ⟨‖a‖ * z₀.re ^ N / (K₀ + 1), by positivity, fun t' ht' => ?_⟩
    rw [Metric.mem_ball, Subtype.dist_eq, Real.dist_eq] at ht'
    have hdiff : P.eval z₀ + ((t' : ℝ) : ℂ) * Q.eval z₀ = (((t' : ℝ) - t : ℝ) : ℂ) * Q.eval z₀ := by
      push_cast
      linear_combination hz₀
    have hsmall : ‖(P + C ((t' : ℝ) : ℂ) * Q).eval z₀‖ <
        ‖(P + C ((t' : ℝ) : ℂ) * Q).leadingCoeff‖ *
          z₀.re ^ (P + C ((t' : ℝ) : ℂ) * Q).natDegree := by
      rw [hev, hdiff, hlc, hdeg, norm_mul, norm_real, Real.norm_eq_abs]
      have hK1 : K₀ + 1 ≠ 0 := by positivity
      calc |(t' : ℝ) - t| * K₀ ≤ |(t' : ℝ) - t| * (K₀ + 1) := by
            nlinarith [abs_nonneg ((t' : ℝ) - t), norm_nonneg (Q.eval z₀)]
        _ < ‖a‖ * z₀.re ^ N / (K₀ + 1) * (K₀ + 1) := by gcongr
        _ = ‖a‖ * z₀.re ^ N := by field_simp
    obtain ⟨w, hw, hdist⟩ := exists_root_near hr.le hsmall
    refine ⟨w, by rw [← hev]; exact hw, ?_⟩
    have := abs_re_le_norm (z₀ - w)
    rw [sub_re] at this
    linarith [le_abs_self (z₀.re - w.re)]
  have hclosed : IsClosed S := by
    rw [← isSeqClosed_iff_isClosed]
    intro x p hx hlim
    choose z hz using hx
    have hzM : ∀ k, z k ∈ Metric.closedBall (0 : ℂ) (max 1 (N * K / ‖a‖)) := fun k => by
      rw [mem_closedBall_zero_iff]
      exact hbound _ (x k).2.1 (x k).2.2 _ (hz k).1
    obtain ⟨w, -, φ, hφ, hlimz⟩ := (isCompact_closedBall _ _).tendsto_subseq hzM
    have hlimt : Tendsto (fun k => ((x (φ k) : ℝ))) atTop (𝓝 (p : ℝ)) :=
      (continuous_subtype_val.tendsto p).comp (hlim.comp hφ.tendsto_atTop)
    have h1 := (hFcont.tendsto ((p : ℝ), w)).comp (hlimt.prodMk_nhds hlimz)
    refine ⟨w, tendsto_nhds_unique h1 (tendsto_const_nhds.congr fun k => ((hz (φ k)).1).symm),
      (isClosed_le continuous_const continuous_re).mem_of_tendsto hlimz
        (Eventually.of_forall fun k => (hz (φ k)).2)⟩
  have hiff : (⟨0, unitInterval.zero_mem⟩ : unitInterval) ∈ S ↔
      (⟨1, unitInterval.one_mem⟩ : unitInterval) ∈ S := by
    rcases isClopen_iff.mp ⟨hclosed, hopen⟩ with h | h <;> simp [h]
  simp only [hSdef, Set.mem_ofPred_eq, ofReal_zero, zero_mul, add_zero, ofReal_one,
    one_mul] at hiff
  simpa [eval_add] using hiff

/-- **The Routh step** (for `μ = c₀/c₁ > 0`): `∑_{i=0}^{n+1} cᵢ z^{n+1−i}` is stable iff the
reduced polynomial `∑_{i=0}^{n} c′ᵢ z^{n−i}` is. Proof: the homotopy `hₜ = g + tμz(A − μzB)`
keeps the leading coefficient `c₀`, has a zero on the imaginary axis only if `g` does, and
`h₁ = (μz + 1) g₁`. -/
theorem hStable_routh_iff {c : ℕ → ℝ} {n : ℕ} (hc0 : c 0 ≠ 0) (hc1 : c 1 ≠ 0)
    (hμ : 0 < c 0 / c 1) (hc : ∀ i > n + 1, c i = 0) :
    HStable (hpoly c (n + 1)) ↔ HStable (hpoly (routh c) n) := by
  obtain ⟨μ, hμdef⟩ : ∃ μ : ℝ, μ = c 0 / c 1 := ⟨_, rfl⟩
  rw [← hμdef] at hμ
  obtain ⟨A, hA⟩ : ∃ A, A = hpoly (cEven c) (n + 1) := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B, B = hpoly (cOdd c) (n + 1) := ⟨_, rfl⟩
  have hAB : ∀ z, (hpoly c (n + 1)).eval z = A.eval z + B.eval z := fun z => by
    rw [← hpoly_even_add_odd c (n + 1), eval_add, hA, hB]
  have hg₁ : ∀ z, (hpoly (routh c) n).eval z = A.eval z - μ * z * B.eval z + B.eval z :=
    fun z => by
      rw [← hpoly_routh hc1 hc, eval_sub, hAB, ← hμdef, ← hB]
      simp only [eval_mul, eval_C, eval_X]
      ring
  have hAn : ∀ z, A.eval (-z) = (-1) ^ (n + 1) * A.eval z := by
    rw [hA]; exact eval_neg_hpoly_cEven c (n + 1)
  have hBn : ∀ z, B.eval (-z) = -((-1) ^ (n + 1) * B.eval z) := by
    rw [hB]; exact eval_neg_hpoly_cOdd c (n + 1)
  have hAc : ∀ z, conj (A.eval z) = A.eval (conj z) := by rw [hA]; exact conj_eval_hpoly _ _
  have hBc : ∀ z, conj (B.eval z) = B.eval (conj z) := by rw [hB]; exact conj_eval_hpoly _ _
  have hs : ((-1 : ℂ) ^ (n + 1)) ≠ 0 := pow_ne_zero _ (by norm_num)
  by_cases hax : ∃ ω : ℝ, (hpoly c (n + 1)).eval (ω * I) = 0
  · obtain ⟨ω, hω⟩ := hax
    obtain ⟨hA0, hB0⟩ := parity_parts_eq_zero (E := fun z => A.eval z)
      (O := fun z => B.eval z) hs hAn hBn hAc hBc (by rw [← hAB]; exact hω)
    have h1 : ¬ HStable (hpoly c (n + 1)) := fun hst => by
      have := hst _ hω
      simp at this
    have h2 : ¬ HStable (hpoly (routh c) n) := fun hst => by
      have := hst (ω * I) (by
        rw [hg₁, show A.eval (ω * I) = 0 from hA0, show B.eval (ω * I) = 0 from hB0]
        ring)
      simp at this
    exact iff_of_false h1 h2
  push Not at hax
  -- the homotopy `g + t Q`, `Q = μz(A − μzB)`
  set Q : ℂ[X] := C (μ : ℂ) * X * (A - C (μ : ℂ) * X * B) with hQdef
  have hQev : ∀ z, Q.eval z = μ * z * (A.eval z - μ * z * B.eval z) := fun z => by simp [hQdef]
  have hQcoeff : ∀ k, n + 1 ≤ k → Q.coeff k = 0 := by
    intro k hk
    obtain ⟨e, rfl⟩ : ∃ e, k = e + 1 := ⟨k - 1, by omega⟩
    rw [hQdef, mul_assoc, coeff_C_mul, coeff_X_mul, hA, hB, hμdef,
      coeff_A₁_eq_zero hc1 (by omega), mul_zero]
  have hle : ∀ t : ℝ, (hpoly c (n + 1) + C (t : ℂ) * Q).natDegree ≤ n + 1 := fun t =>
    natDegree_le_iff_coeff_eq_zero.mpr fun k hk => by
      have hk' : n + 1 < k := by exact_mod_cast hk
      rw [coeff_add, coeff_C_mul, hQcoeff k hk'.le, coeff_hpoly]
      simp [show ¬ k ≤ n + 1 by omega]
  have htop : ∀ t : ℝ, (hpoly c (n + 1) + C (t : ℂ) * Q).coeff (n + 1) = c 0 := fun t => by
    rw [coeff_add, coeff_C_mul, hQcoeff _ le_rfl, coeff_hpoly]
    simp
  have him : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → ∀ z,
      (hpoly c (n + 1) + C (t : ℂ) * Q).eval z = 0 → z.re ≠ 0 := by
    intro t ht _ z hz hre
    obtain ⟨ω, rfl⟩ : ∃ ω : ℝ, z = ω * I := ⟨z.im, by apply Complex.ext <;> simp [hre]⟩
    rw [eval_add, eval_mul, eval_C, hQev, hAB] at hz
    set O : ℂ → ℂ := fun w => B.eval w + (t : ℂ) * (μ * w * (A.eval w - μ * w * B.eval w))
      with hOdef
    have hO : ∀ w, O (-w) = -((-1) ^ (n + 1) * O w) := fun w => by
      simp only [hOdef, hAn, hBn]
      ring
    have hOc : ∀ w, conj (O w) = O (conj w) := fun w => by
      simp only [hOdef, map_add, map_mul, map_sub, hAc, hBc, conj_ofReal]
    obtain ⟨hA0, hO0⟩ := parity_parts_eq_zero (E := fun w => A.eval w) (ω := ω) hs hAn hO hAc
      hOc (by simp only [hOdef]; linear_combination hz)
    simp only [hOdef] at hO0 hA0
    rw [hA0] at hO0
    have hpos : (1 + (t : ℂ) * μ ^ 2 * ω ^ 2) ≠ 0 := by
      have : (0 : ℝ) < 1 + t * μ ^ 2 * ω ^ 2 := by positivity
      exact_mod_cast this.ne'
    have hB0 : B.eval (ω * I) = 0 := by
      have : B.eval (ω * I) * (1 + (t : ℂ) * μ ^ 2 * ω ^ 2) = 0 := by
        linear_combination hO0 + ((t : ℂ) * μ ^ 2 * ω ^ 2 * B.eval (ω * I)) * I_sq
      exact (mul_eq_zero.mp this).resolve_right hpos
    exact hax ω (by rw [hAB, hA0, hB0, add_zero])
  have hc0' : (c 0 : ℂ) ≠ 0 := ofReal_ne_zero.mpr hc0
  have key := exists_rhp_root_iff_of_homotopy (by omega) hc0' hle htop him
  have hend : ∀ z, (hpoly c (n + 1) + Q).eval z =
      ((μ : ℂ) * z + 1) * (hpoly (routh c) n).eval z := fun z => by
    rw [eval_add, hQev, hAB, hg₁]
    ring
  have hg_iff : HStable (hpoly c (n + 1)) ↔
      ¬ ∃ z, (hpoly c (n + 1)).eval z = 0 ∧ 0 ≤ z.re := by
    simp only [HStable, not_exists, not_and, not_le]
  have hg₁_iff : HStable (hpoly (routh c) n) ↔
      ¬ ∃ z, (hpoly c (n + 1) + Q).eval z = 0 ∧ 0 ≤ z.re := by
    constructor
    · rintro hst ⟨z, hz, hre⟩
      rw [hend] at hz
      rcases mul_eq_zero.mp hz with h | h
      · have hz' : z = ((-(1 / μ) : ℝ) : ℂ) := by
          have : (μ : ℂ) ≠ 0 := ofReal_ne_zero.mpr hμ.ne'
          push_cast
          field_simp
          linear_combination h
        rw [hz', ofReal_re] at hre
        have : 0 < 1 / μ := by positivity
        linarith
      · exact absurd (hst z h) (not_lt.mpr hre)
    · intro h z hz
      by_contra hre
      exact h ⟨z, by rw [hend, hz, mul_zero], not_lt.mp hre⟩
  rw [hg_iff, hg₁_iff, key]

/-! ### The Hurwitz criterion -/

/-- The coefficient sequence on `ℤ`, zero for negative indices. -/
def hz (c : ℕ → ℝ) (m : ℤ) : ℝ := if 0 ≤ m then c m.toNat else 0

theorem hz_routh {c : ℕ → ℝ} (hc1 : c 1 ≠ 0) :
    hz (routh c) = fun m => if Odd m then hz c (m + 1) - c 0 / c 1 * hz c (m + 2)
      else hz c (m + 1) := by
  funext m
  simp only [hz, routh]
  by_cases hm : 0 ≤ m
  · have h1 : 0 ≤ m + 1 := by omega
    have h2 : 0 ≤ m + 2 := by omega
    simp only [hm, h1, h2, ↓reduceIte, show (m + 1).toNat = m.toNat + 1 by omega,
      show (m + 2).toNat = m.toNat + 2 by omega]
    have hpar : Even m.toNat ↔ ¬ Odd m := by
      rw [Nat.even_iff, Int.not_odd_iff_even, Int.even_iff]
      omega
    by_cases he : Even m.toNat
    · simp [he, hpar.mp he]
    · simp [he, show Odd m from not_not.mp (fun h => he (hpar.mpr h))]
  · simp only [hm, ↓reduceIte]
    by_cases hm1 : m = -1
    · subst hm1
      simp only [show Odd (-1 : ℤ) by decide, ↓reduceIte, show (0 : ℤ) ≤ -1 + 1 by omega,
        show (0 : ℤ) ≤ -1 + 2 by omega, show (-1 + 1 : ℤ).toNat = 0 by rfl,
        show (-1 + 2 : ℤ).toNat = 1 by rfl]
      field_simp
      ring
    · have h1 : ¬ (0 ≤ m + 1) := by omega
      split_ifs with ho h2 <;> try simp
      · exfalso
        rw [Int.odd_iff] at ho
        omega

theorem hdet_zero (a : ℤ → ℝ) : hdet a 0 = 1 := by
  simp [hdet]

theorem hdet_one (a : ℤ → ℝ) : hdet a 1 = a 1 := by
  simp [hdet, Matrix.det_unique]

theorem pos_mul_iff_of_ratio {c₀ c₁ X : ℝ} (hc1 : c₁ ≠ 0) (hμ : 0 < c₀ / c₁) (j : ℕ) :
    0 < c₀ ^ (j + 1) * (c₁ * X) ↔ 0 < c₁ ^ j * X := by
  have heq : c₀ ^ (j + 1) * (c₁ * X) = ((c₀ / c₁) ^ (j + 1) * c₁ ^ 2) * (c₁ ^ j * X) := by
    rw [div_pow]
    field_simp
    ring
  rw [heq]
  exact mul_pos_iff_of_pos_left (by positivity)

/-- **Hurwitz criterion** (in Hurwitz form): `∑_{i=0}^{n} cᵢ z^{n−i}` with `c₀ ≠ 0` is stable iff
`c₀ᵏ Δₖ > 0` for `k = 1, …, n`, `Δₖ = det (c_{2j+1−i})`. -/
theorem hurwitz_criterion (n : ℕ) : ∀ c : ℕ → ℝ, c 0 ≠ 0 → (∀ i > n, c i = 0) →
    (HStable (hpoly c n) ↔ ∀ k, 1 ≤ k → k ≤ n → 0 < c 0 ^ k * hdet (hz c) k) := by
  induction n with
  | zero =>
    intro c hc0 _
    refine iff_of_true (fun z hz => ?_) (fun k hk1 hk => by omega)
    rw [eval_hpoly] at hz
    simp at hz
    exact absurd hz hc0
  | succ n ih =>
    intro c hc0 hc
    have hcz : hz c 1 = c 1 := by simp [hz]
    by_cases hc1 : c 1 = 0
    · refine iff_of_false (fun hst => ?_) (fun h => ?_)
      · have := div_pos_of_hStable hc0 hst
        rw [hc1, zero_div] at this
        exact lt_irrefl _ this
      · have := h 1 le_rfl (by omega)
        rw [hdet_one, hcz, hc1, mul_zero] at this
        exact lt_irrefl _ this
    by_cases hμ : 0 < c 0 / c 1
    · have hr0 : routh c 0 = c 1 := by simp [routh]
      have hrz : ∀ i > n, routh c i = 0 := fun i hi => by
        simp only [routh, hc (i + 1) (by omega), hc (i + 2) (by omega)]
        simp
      rw [hStable_routh_iff hc0 hc1 hμ hc, ih (routh c) (by rw [hr0]; exact hc1) hrz, hr0]
      have hstep : ∀ j, hdet (hz c) (j + 1) = c 1 * hdet (hz (routh c)) j := by
        intro j
        rw [hdet_succ (hz c) (c 0 / c 1) (fun m hm => by simp [hz, not_le.mpr hm])
          (by simp only [hz]; norm_num; field_simp; ring) j, hcz, hz_routh hc1]
      constructor
      · intro h k hk1 hk
        obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
        rw [hstep, pos_mul_iff_of_ratio hc1 hμ]
        rcases Nat.eq_zero_or_pos j with hj | hj
        · subst hj
          simp [hdet_zero]
        · exact h j hj (by omega)
      · intro h j hj1 hj
        have := h (j + 1) (by omega) (by omega)
        rwa [hstep, pos_mul_iff_of_ratio hc1 hμ] at this
    · refine iff_of_false (fun hst => ?_) (fun h => ?_)
      · have h1 := div_pos_of_hStable hc0 hst
        exact hμ (by
          rw [div_pos_iff] at h1 ⊢
          tauto)
      · have := h 1 le_rfl (by omega)
        rw [hdet_one, hcz, pow_one] at this
        exact hμ (by
          rw [mul_pos_iff] at this
          rw [div_pos_iff]
          tauto)

/-! ### DLMF's formulation -/

/-- **DLMF 1.11.24**: a polynomial `f(z) = a₀ + a₁z + ⋯ + aₙzⁿ` with real coefficients is
*stable* if all its zeros have negative real part. -/
def IsStable (f : ℝ[X]) : Prop := ∀ z : ℂ, aeval z f = 0 → z.re < 0

/-- **DLMF 1.11.25–1.11.26**: `Dₖ = det [h_k^{(1)}, h_k^{(3)}, …, h_k^{(2k−1)}]`, the column
`h_k^{(m)}` being the first `k` of `a_m, a_{m−1}, a_{m−2}, …` (`aⱼ = 0` for `j < 0` or `j > n`);
entry `(i, j)` is `a_{2j+1−i}`. -/
noncomputable def hurwitzD (f : ℝ[X]) (k : ℕ) : ℝ := hdet (hz f.coeff) k

/-- **DLMF 1.11.25**: `D₁ = a₁`. -/
theorem dlmf_1_11_25_one (f : ℝ[X]) : hurwitzD f 1 = f.coeff 1 := by
  simp [hurwitzD, hdet_one, hz]

/-- **DLMF 1.11.25**: `D₂ = det [[a₁, a₃], [a₀, a₂]]`. -/
theorem dlmf_1_11_25_two (f : ℝ[X]) :
    hurwitzD f 2 = Matrix.det !![f.coeff 1, f.coeff 3; f.coeff 0, f.coeff 2] := by
  simp only [hurwitzD, hdet, Matrix.det_fin_two, Matrix.of_apply]
  norm_num [hz]

/-- **DLMF 1.11.25**: `D₃ = det [[a₁, a₃, a₅], [a₀, a₂, a₄], [0, a₁, a₃]]`. -/
theorem dlmf_1_11_25_three (f : ℝ[X]) :
    hurwitzD f 3 = Matrix.det !![f.coeff 1, f.coeff 3, f.coeff 5; f.coeff 0, f.coeff 2,
      f.coeff 4; 0, f.coeff 1, f.coeff 3] := by
  simp only [hurwitzD, hdet, Matrix.det_fin_three, Matrix.of_apply]
  norm_num [hz]

/-- The reversed polynomial: `∑ aᵢ z^{n−i} = zⁿ f(1/z)`. -/
theorem eval_hpoly_coeff {f : ℝ[X]} {z : ℂ} (hz0 : z ≠ 0) :
    (hpoly f.coeff f.natDegree).eval z = z ^ f.natDegree * aeval z⁻¹ f := by
  rw [eval_hpoly, aeval_eq_sum_range, mul_sum]
  refine sum_congr rfl fun i hi => ?_
  have hi' : i ≤ f.natDegree := Nat.lt_succ_iff.mp (mem_range.mp hi)
  rw [Complex.real_smul, pow_sub₀ _ hz0 hi', inv_pow]
  ring

theorem isStable_iff_hStable {f : ℝ[X]} (hf : f ≠ 0) (h0 : f.coeff 0 ≠ 0) :
    IsStable f ↔ HStable (hpoly f.coeff f.natDegree) := by
  have hlead : (hpoly f.coeff f.natDegree).eval 0 ≠ 0 := by
    rw [← coeff_zero_eq_eval_zero, coeff_hpoly]
    simpa using hf
  have haeval0 : aeval (0 : ℂ) f ≠ 0 := by
    simpa [aeval_def, eval₂_at_zero] using h0
  have hre : ∀ z : ℂ, z ≠ 0 → (z⁻¹.re < 0 ↔ z.re < 0) := fun z hz => by
    rw [inv_re, div_lt_iff₀ (normSq_pos.mpr hz), zero_mul]
  constructor
  · intro hst z hz
    have hz0 : z ≠ 0 := by rintro rfl; exact hlead hz
    rw [eval_hpoly_coeff hz0] at hz
    have := hst z⁻¹ ((mul_eq_zero.mp hz).resolve_left (pow_ne_zero _ hz0))
    exact (hre z hz0).mp this
  · intro hst z hz
    have hz0 : z ≠ 0 := by rintro rfl; exact haeval0 hz
    have := hst z⁻¹ (by rw [eval_hpoly_coeff (inv_ne_zero hz0), inv_inv, hz, mul_zero])
    exact (hre z hz0).mp this

theorem pos_mul_iff_sign_eq {a x : ℝ} (ha : a ≠ 0) :
    0 < a * x ↔ SignType.sign x = SignType.sign a := by
  rcases lt_or_gt_of_ne ha with h | h
  · rw [sign_neg h, sign_eq_neg_one_iff, mul_pos_iff]
    constructor
    · rintro (⟨h1, -⟩ | ⟨-, h2⟩)
      · linarith
      · exact h2
    · intro hx
      exact Or.inr ⟨h, hx⟩
  · rw [sign_pos h, sign_eq_one_iff]
    exact mul_pos_iff_of_pos_left h

/-- **DLMF §1.11(v), Hurwitz criterion**: `f(z) = a₀ + ⋯ + aₙzⁿ` (`aₙ ≠ 0`, real coefficients)
is stable iff `a₀ ≠ 0`, `D_{2k} > 0` for `k = 1, …, ⌊n/2⌋`, and `sign D_{2k+1} = sign a₀` for
`k = 0, 1, …, ⌊n/2 − 1/2⌋`. -/
theorem dlmf_1_11_v_hurwitz {f : ℝ[X]} (hf : f ≠ 0) :
    IsStable f ↔ f.coeff 0 ≠ 0 ∧
      (∀ k, 1 ≤ k → 2 * k ≤ f.natDegree → 0 < hurwitzD f (2 * k)) ∧
      (∀ k, 2 * k + 1 ≤ f.natDegree →
        SignType.sign (hurwitzD f (2 * k + 1)) = SignType.sign (f.coeff 0)) := by
  by_cases h0 : f.coeff 0 = 0
  · refine iff_of_false (fun hst => ?_) (fun h => h.1 h0)
    have := hst 0 (by simp [aeval_def, eval₂_at_zero, h0])
    simp at this
  rw [isStable_iff_hStable hf h0, hurwitz_criterion f.natDegree f.coeff h0
    (fun i hi => coeff_eq_zero_of_natDegree_lt hi)]
  simp only [ne_eq, h0, not_false_eq_true, true_and]
  have ha2 : 0 < f.coeff 0 ^ 2 := by positivity
  constructor
  · intro h
    refine ⟨fun k hk1 hk => ?_, fun k hk => ?_⟩
    · have := h (2 * k) (by omega) hk
      rw [pow_mul] at this
      exact (mul_pos_iff_of_pos_left (pow_pos ha2 k)).mp this
    · have := h (2 * k + 1) (by omega) hk
      rw [pow_succ, pow_mul, mul_assoc] at this
      exact (pos_mul_iff_sign_eq h0).mp ((mul_pos_iff_of_pos_left (pow_pos ha2 k)).mp this)
  · rintro ⟨heven, hodd⟩ k hk1 hk
    rcases Nat.even_or_odd k with ⟨m, rfl⟩ | ⟨m, rfl⟩
    · rw [← two_mul, pow_mul]
      exact mul_pos (pow_pos ha2 m) (heven m (by omega) (by omega))
    · rw [pow_succ, pow_mul, mul_assoc]
      exact mul_pos (pow_pos ha2 m) ((pos_mul_iff_sign_eq h0).mpr (hodd m hk))

end Azurite.DLMF
