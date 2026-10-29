/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Tactic.LinearCombination

/-!
# DLMF §1.11(i): Division Algorithm

Formalizations of <https://dlmf.nist.gov/1.11.i> over any commutative ring. The coefficients are
`a : ℕ → R` with degree bound `n`, or the coefficients of a `Polynomial`.

* Horner's scheme:
  * 1.11.3: `horner a α n k = b_k`, computed by DLMF's downward recursion
    `b_n = a_n`, `b_k = α b_{k+1} + a_k` (`horner_top`, `horner_succ`).
  * 1.11.2: `dlmf_1_11_2` (by telescoping) and `dlmf_1_11_2_poly`.
  * 1.11.4: `dlmf_1_11_4` and `dlmf_1_11_4_poly`, `f(α) = b₀`.
* Extended Horner scheme:
  * 1.11.5: `dlmf_1_11_5`, the scheme applied to the `b_k`.
  * 1.11.6: `dlmf_1_11_6`, `f′(α) = c₁`, since `f′(α) = q(α)` for `f = (z − α)q + b₀`.
* Division: 1.11.7, `dlmf_1_11_7`. Over a field, `f = g q + r` with `deg r < deg g` (`r = 0`
  allowed, of degree `−∞`), and `q`, `r` are unique.
-/

open Polynomial Finset

namespace Azurite.DLMF

variable {R : Type*} [CommRing R]

/-! ### Horner's scheme -/

/-- The Horner recursion run `m` steps down from the top coefficient: `b_n, b_{n−1}, …`. -/
def hornerStep (a : ℕ → R) (α : R) (n : ℕ) : ℕ → R
  | 0 => a n
  | m + 1 => α * hornerStep a α n m + a (n - (m + 1))

/-- **DLMF 1.11.3**: Horner's scheme `b_n = a_n`, `b_k = α b_{k+1} + a_k` (`k = n − 1, …, 0`). -/
def horner (a : ℕ → R) (α : R) (n k : ℕ) : R := hornerStep a α n (n - k)

theorem horner_top (a : ℕ → R) (α : R) (n : ℕ) : horner a α n n = a n := by
  simp [horner, hornerStep]

theorem horner_succ (a : ℕ → R) (α : R) {n k : ℕ} (hk : k < n) :
    horner a α n k = α * horner a α n (k + 1) + a k := by
  unfold horner
  obtain ⟨m, hm⟩ : ∃ m, n - k = m + 1 := ⟨n - k - 1, by omega⟩
  rw [hm, hornerStep, show n - (k + 1) = m by omega, show n - (m + 1) = k by omega]

/-- **DLMF 1.11.1–1.11.2**: `f(z) = a_n zⁿ + ⋯ + a₀ = (z − α)(b_n z^{n−1} + ⋯ + b₁) + b₀`. -/
theorem dlmf_1_11_2 (a : ℕ → R) (α z : R) (n : ℕ) :
    ∑ k ∈ range (n + 1), a k * z ^ k =
      (z - α) * ∑ k ∈ range n, horner a α n (k + 1) * z ^ k + horner a α n 0 := by
  set b := horner a α n
  have hrec : ∀ k ∈ range n, α * b (k + 1) = b k - a k := fun k hk => by
    show α * horner a α n (k + 1) = horner a α n k - a k
    rw [horner_succ a α (mem_range.mp hk)]
    ring
  have htel := Finset.sum_range_sub (fun k => b k * z ^ k) n
  have h1 : (z - α) * ∑ k ∈ range n, b (k + 1) * z ^ k =
      ∑ k ∈ range n, (b (k + 1) * z ^ (k + 1) - b k * z ^ k) +
        ∑ k ∈ range n, a k * z ^ k := by
    rw [mul_sum, ← sum_add_distrib]
    refine sum_congr rfl fun k hk => ?_
    have := hrec k hk
    linear_combination (-(z ^ k)) * this
  rw [h1, htel, sum_range_succ, show b n = a n from horner_top a α n]
  ring

/-- **DLMF 1.11.4**: `f(α) = b₀`. -/
theorem dlmf_1_11_4 (a : ℕ → R) (α : R) (n : ℕ) :
    ∑ k ∈ range (n + 1), a k * α ^ k = horner a α n 0 := by
  rw [dlmf_1_11_2 a α α n, sub_self, zero_mul, zero_add]

/-- Horner's scheme on the shifted coefficients `b_{k+1}` is Horner's scheme from index `1`. -/
theorem horner_shift (a : ℕ → R) (α : R) (n k : ℕ) :
    horner (fun j => a (j + 1)) α n k = horner a α (n + 1) (k + 1) := by
  unfold horner
  rw [show n + 1 - (k + 1) = n - k by omega]
  have : ∀ m ≤ n, hornerStep (fun j => a (j + 1)) α n m = hornerStep a α (n + 1) m := by
    intro m hm
    induction m with
    | zero => rfl
    | succ m ih =>
      simp only [hornerStep, ih (by omega), show n - (m + 1) + 1 = n + 1 - (m + 1) by omega]
  exact this _ (Nat.sub_le n k)

/-! ### Polynomial forms -/

theorem horner_map {S : Type*} [CommRing S] (φ : R →+* S) (a : ℕ → R) (α : R) (n k : ℕ) :
    horner (fun j => φ (a j)) (φ α) n k = φ (horner a α n k) := by
  unfold horner
  induction n - k with
  | zero => rfl
  | succ m ih => simp only [hornerStep, ih, map_add, map_mul]

/-- **DLMF 1.11.2** for a polynomial `f` of degree `n`: `f = (z − α) q + b₀` with
`q = b_n z^{n−1} + ⋯ + b₁`. -/
theorem dlmf_1_11_2_poly (f : R[X]) (α : R) :
    f = (X - C α) * ∑ k ∈ range f.natDegree,
        C (horner f.coeff α f.natDegree (k + 1)) * X ^ k + C (horner f.coeff α f.natDegree 0) := by
  have h := dlmf_1_11_2 (fun k => C (f.coeff k)) (C α) X f.natDegree
  simp only [horner_map C] at h
  conv_lhs => rw [as_sum_range_C_mul_X_pow f]
  exact h

/-- **DLMF 1.11.4** for a polynomial: `f(α) = b₀`. -/
theorem dlmf_1_11_4_poly (f : R[X]) (α : R) : f.eval α = horner f.coeff α f.natDegree 0 := by
  rw [eval_eq_sum_range, dlmf_1_11_4]

/-! ### Extended Horner scheme -/

/-- **DLMF 1.11.5**: `c_n = a_n`, `c_k = α c_{k+1} + b_k` — Horner's scheme applied to the `b_k`. -/
theorem dlmf_1_11_5 (a : ℕ → R) (α : R) (n : ℕ) :
    horner (horner a α n) α n n = a n ∧ ∀ k < n,
      horner (horner a α n) α n k = α * horner (horner a α n) α n (k + 1) + horner a α n k :=
  ⟨by rw [horner_top, horner_top], fun _ hk => horner_succ _ α hk⟩

/-- **DLMF 1.11.6**: `f′(α) = c₁` (for `deg f = n ≥ 1`). -/
theorem dlmf_1_11_6 (f : R[X]) (α : R) (hn : 1 ≤ f.natDegree) :
    (derivative f).eval α = horner (horner f.coeff α f.natDegree) α f.natDegree 1 := by
  set n := f.natDegree
  set b := horner f.coeff α n
  set q : R[X] := ∑ k ∈ range n, C (b (k + 1)) * X ^ k
  have hf := dlmf_1_11_2_poly f α
  have hder : derivative f = q + (X - C α) * derivative q := by
    conv_lhs => rw [hf]
    simp [derivative_mul, q, b, n]
  rw [hder, eval_add, eval_mul, eval_sub, eval_X, eval_C, sub_self, zero_mul, add_zero]
  -- `q(α)` by Horner's scheme on the coefficients `b_{k+1}`
  obtain ⟨m, hm⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hq : q.eval α = ∑ k ∈ range (m + 1), b (k + 1) * α ^ k := by
    simp [q, eval_finsetSum, hm]
  rw [hq, dlmf_1_11_4 (fun k => b (k + 1)) α m, horner_shift, ← hm]

/-! ### Division of polynomials -/

/-- **DLMF 1.11.7**: for polynomials `f`, `g ≠ 0` there are `q`, `r` with `f = g q + r` and
`deg r < deg g` (`r = 0` has degree `−∞`), and they are unique. -/
theorem dlmf_1_11_7 {K : Type*} [Field K] (f : K[X]) {g : K[X]} (hg : g ≠ 0) :
    (∃ q r : K[X], f = g * q + r ∧ r.degree < g.degree) ∧
      ∀ q r q' r' : K[X], f = g * q + r → r.degree < g.degree → f = g * q' + r' →
        r'.degree < g.degree → q = q' ∧ r = r' := by
  refine ⟨⟨f / g, f % g, (EuclideanDomain.div_add_mod f g).symm, degree_mod_lt f hg⟩, ?_⟩
  intro q r q' r' h hr h' hr'
  have hgq : g * (q - q') = r' - r := by linear_combination h' - h
  have hqq : q = q' := by
    by_contra hne
    have h1 : g.degree ≤ (g * (q - q')).degree := degree_le_mul_left g (sub_ne_zero.mpr hne)
    have h2 : (r' - r).degree < g.degree := (degree_sub_le r' r).trans_lt (max_lt hr' hr)
    rw [hgq] at h1
    exact absurd (h1.trans_lt h2) (lt_irrefl _)
  refine ⟨hqq, ?_⟩
  rw [hqq, sub_self, mul_zero] at hgq
  exact (sub_eq_zero.mp hgq.symm).symm

end Azurite.DLMF
