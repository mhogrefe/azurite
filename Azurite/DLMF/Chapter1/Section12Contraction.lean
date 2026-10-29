/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.DLMF.Chapter1.Section12
import Mathlib.Topology.Compactification.OnePoint.Basic

/-!
# DLMF §1.12(iii)–(iv): Existence of Convergents; Contraction and Extension

Formalizations of <https://dlmf.nist.gov/1.12.iii> and <https://dlmf.nist.gov/1.12.iv>.
Convergents are points of the extended plane `ℂ ∪ {∞}` (`OnePoint ℂ`): `convPt a b n` is
`Aₙ/Bₙ`, equal to `∞` when `Bₙ = 0`.

* 1.12.22 (`dlmf_1_12_22`): `{Cₙ}` is the sequence of convergents of a continued fraction with
  `aₙ ≠ 0` iff `C₀ ≠ ∞` and `Cₙ ≠ C_{n−1}`.
  * `⇒` is the determinant formula 1.12.7.
  * `⇐` builds `aₙ`, `bₙ` from representatives `(z, 1)`, `(1, 0)` by Cramer's rule.
* Contraction and extension: the definitions `IsContraction` and `IsExtension`.
* Even part (`C′ₙ = C₂ₙ`):
  * it exists iff `b_{2k} ≠ 0` (`dlmf_1_12_iv_even_exists`);
  * 1.12.23: it is given explicitly by `evenA`, `evenB` (`dlmf_1_12_23`, with `A′_k = λ_k A_{2k}`
    from `dlmf_1_12_23_numer`).
* Odd part (`C′ₙ = C_{2n+1}`):
  * it exists iff `b_{2k+1} ≠ 0` (`dlmf_1_12_iv_odd_exists`);
  * 1.12.24: it is given explicitly by `oddA`, `oddB` (`dlmf_1_12_24`, `dlmf_1_12_24_numer`).
* Both existence criteria rest on `C_{n+2} = Cₙ ⟺ b_{n+2} = 0` (`convPt_add_two_eq_iff`). Both
  explicit forms rest on the two-step recurrence `cf_two_step`.
-/

open Finset OnePoint

namespace Azurite.DLMF

/-! ### Convergents in the extended plane -/

/-- The point `A/B` of `ℂ ∪ {∞}` (`∞` when `B = 0`). -/
noncomputable def cfPoint (A B : ℂ) : OnePoint ℂ := if B = 0 then ∞ else ((A / B : ℂ) : OnePoint ℂ)

/-- The `n`th convergent `Cₙ = Aₙ/Bₙ` as a point of `ℂ ∪ {∞}`. -/
noncomputable def convPt (a b : ℕ → ℂ) (n : ℕ) : OnePoint ℂ := cfPoint (cfA a b n) (cfB a b n)

theorem cfPoint_eq_iff {A B A' B' : ℂ} (h : ¬ (A = 0 ∧ B = 0)) (h' : ¬ (A' = 0 ∧ B' = 0)) :
    cfPoint A B = cfPoint A' B' ↔ A * B' - A' * B = 0 := by
  unfold cfPoint
  by_cases hB : B = 0 <;> by_cases hB' : B' = 0
  · simp [hB, hB']
  · have hA : A ≠ 0 := fun hA => h ⟨hA, hB⟩
    simp only [hB, hB', ↓reduceIte, mul_zero, sub_zero]
    exact iff_of_false (infty_ne_coe _) (mul_ne_zero hA hB')
  · have hA' : A' ≠ 0 := fun hA => h' ⟨hA, hB'⟩
    simp only [hB, hB', ↓reduceIte, mul_zero, zero_sub, neg_eq_zero]
    exact iff_of_false (coe_ne_infty _) (mul_ne_zero hA' hB)
  · simp only [hB, hB', ↓reduceIte, coe_eq_coe, div_eq_div_iff hB hB', sub_eq_zero]

/-- A representative `(z, 1)` of `z`, and `(1, 0)` of `∞`. -/
noncomputable def ptRep (p : OnePoint ℂ) : ℂ × ℂ := p.elim (1, 0) fun z => (z, 1)

@[simp] theorem ptRep_infty : ptRep ∞ = (1, 0) := rfl

@[simp] theorem ptRep_coe (z : ℂ) : ptRep z = (z, 1) := rfl

theorem cfPoint_ptRep (p : OnePoint ℂ) : cfPoint (ptRep p).1 (ptRep p).2 = p := by
  induction p using OnePoint.rec with
  | infty => simp [cfPoint]
  | coe z => simp [cfPoint]

theorem ptRep_ne_zero (p : OnePoint ℂ) : ¬ ((ptRep p).1 = 0 ∧ (ptRep p).2 = 0) := by
  induction p using OnePoint.rec with
  | infty => simp
  | coe z => simp

/-- The canonical numerator and denominator never vanish together (`aₖ ≠ 0`). -/
theorem cfAB_ne_zero {a b : ℕ → ℂ} (ha : ∀ k ≥ 1, a k ≠ 0) (n : ℕ) :
    ¬ (cfA a b n = 0 ∧ cfB a b n = 0) := by
  rintro ⟨h1, h2⟩
  have := dlmf_1_12_7 a b n
  rw [h1, h2] at this
  simp only [zero_mul, sub_self] at this
  exact (mul_ne_zero (pow_ne_zero _ (by norm_num))
    (prod_ne_zero_iff.mpr fun k hk => ha k (mem_Icc.mp hk).1)) this.symm

theorem convPt_succ_ne {a b : ℕ → ℂ} (ha : ∀ k ≥ 1, a k ≠ 0) (n : ℕ) :
    convPt a b (n + 1) ≠ convPt a b n := by
  rw [convPt, convPt, Ne, cfPoint_eq_iff (cfAB_ne_zero ha _) (cfAB_ne_zero ha _)]
  have := dlmf_1_12_7 a b (n + 1)
  have hq : cfQ a b (n + 1) = cfB a b n := rfl
  have hp : cfP a b (n + 1) = cfA a b n := rfl
  rw [hq, hp] at this
  intro h0
  have : (-1 : ℂ) ^ (n + 1 + 1) * ∏ k ∈ Icc 1 (n + 1), a k = 0 := by
    rw [← this]
    linear_combination h0
  exact (mul_ne_zero (pow_ne_zero _ (by norm_num))
    (prod_ne_zero_iff.mpr fun k hk => ha k (mem_Icc.mp hk).1)) this

/-- Cramer's rule: `w = b v + a u` with `b = (w × u)/(v × u)`, `a = (v × w)/(v × u)`. -/
theorem cramer {u v w : ℂ × ℂ} (hD : v.1 * u.2 - v.2 * u.1 ≠ 0) :
    (w.1 * u.2 - w.2 * u.1) / (v.1 * u.2 - v.2 * u.1) * v.1 +
        (v.1 * w.2 - v.2 * w.1) / (v.1 * u.2 - v.2 * u.1) * u.1 = w.1 ∧
      (w.1 * u.2 - w.2 * u.1) / (v.1 * u.2 - v.2 * u.1) * v.2 +
        (v.1 * w.2 - v.2 * w.1) / (v.1 * u.2 - v.2 * u.1) * u.2 = w.2 := by
  constructor <;> rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, div_eq_iff hD] <;>
    ring

/-- **DLMF 1.12.22**: a sequence `{Cₙ}` in `ℂ ∪ {∞}` is the sequence of convergents of a
continued fraction (1.12.3, `aₙ ≠ 0`) iff `C₀ ≠ ∞` and `Cₙ ≠ C_{n−1}`, `n = 1, 2, …`. -/
theorem dlmf_1_12_22 (C : ℕ → OnePoint ℂ) :
    (∃ a b : ℕ → ℂ, (∀ k ≥ 1, a k ≠ 0) ∧ ∀ n, convPt a b n = C n) ↔
      C 0 ≠ ∞ ∧ ∀ n, C (n + 1) ≠ C n := by
  constructor
  · rintro ⟨a, b, ha, hC⟩
    refine ⟨?_, fun n => ?_⟩
    · rw [← hC 0]
      simp [convPt, cfPoint, cfA, cfB, cfP, cfQ, coe_ne_infty]
    · rw [← hC, ← hC]
      exact convPt_succ_ne ha n
  · rintro ⟨h0, hne⟩
    obtain ⟨z, hz⟩ : ∃ z : ℂ, C 0 = z := by
      induction h : C 0 using OnePoint.rec with
      | infty => exact absurd h h0
      | coe z => exact ⟨z, rfl⟩
    set vec : ℕ → ℂ × ℂ := fun k => if k = 0 then (1, 0) else ptRep (C (k - 1)) with hvec
    set cr : ℂ × ℂ → ℂ × ℂ → ℂ := fun x y => x.1 * y.2 - x.2 * y.1 with hcr
    have hcross : ∀ k, cr (vec (k + 1)) (vec k) ≠ 0 := by
      intro k
      rcases k with _ | k
      · simp [hvec, hcr, hz]
      · simp only [hvec, hcr, show k + 1 + 1 ≠ 0 by omega, show k + 1 ≠ 0 by omega, ↓reduceIte,
          show k + 1 + 1 - 1 = k + 1 by omega, show k + 1 - 1 = k by omega]
        intro h
        apply hne k
        rw [← cfPoint_ptRep (C (k + 1)), ← cfPoint_ptRep (C k)]
        exact (cfPoint_eq_iff (ptRep_ne_zero _) (ptRep_ne_zero _)).mpr (by linear_combination h)
    set b : ℕ → ℂ := fun n => if n = 0 then z else
      cr (vec (n + 1)) (vec (n - 1)) / cr (vec n) (vec (n - 1)) with hb
    set a : ℕ → ℂ := fun n => if n = 0 then 0 else
      cr (vec n) (vec (n + 1)) / cr (vec n) (vec (n - 1)) with ha
    have hPQ : ∀ k, cfP a b k = (vec k).1 ∧ cfQ a b k = (vec k).2 := by
      intro k
      induction k using Nat.strong_induction_on with
      | _ k ih =>
        match k with
        | 0 => simp [cfP, cfQ, hvec]
        | 1 => simp [cfP, cfQ, hvec, hb, hz]
        | k + 2 =>
          obtain ⟨p1, q1⟩ := ih (k + 1) (by omega)
          obtain ⟨p0, q0⟩ := ih k (by omega)
          have hc := hcross k
          rw [show cfP a b (k + 2) = b (k + 1) * cfP a b (k + 1) + a (k + 1) * cfP a b k from rfl,
            show cfQ a b (k + 2) = b (k + 1) * cfQ a b (k + 1) + a (k + 1) * cfQ a b k from rfl,
            p1, q1, p0, q0]
          simp only [hb, ha, show k + 1 ≠ 0 by omega, ↓reduceIte, show k + 1 - 1 = k by omega]
          simp only [hcr] at hc ⊢
          exact cramer hc
    refine ⟨a, b, fun k hk => ?_, fun n => ?_⟩
    · obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
      simp only [ha, show m + 1 ≠ 0 by omega, ↓reduceIte, show m + 1 - 1 = m by omega]
      refine div_ne_zero ?_ (hcross m)
      have := hcross (m + 1)
      simp only [hcr] at this ⊢
      intro h
      exact this (by linear_combination -h)
    · rw [convPt, cfA, cfB, (hPQ (n + 1)).1, (hPQ (n + 1)).2]
      simp only [hvec, show n + 1 ≠ 0 by omega, ↓reduceIte, Nat.add_sub_cancel]
      exact cfPoint_ptRep _

/-! ### Contraction and extension -/

/-- A *contraction* `C′` of `C`: its convergents form a subsequence of those of `C`. Conversely
`C` is an *extension* of `C′`. -/
def IsContraction (a' b' a b : ℕ → ℂ) : Prop :=
  ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ n, convPt a' b' n = convPt a b (φ n)

/-- `C` is an extension of `C′` iff `C′` is a contraction of `C`. -/
def IsExtension (a b a' b' : ℕ → ℂ) : Prop := IsContraction a' b' a b

/-- `A_{n+2}B_n − B_{n+2}A_n = b_{n+2}(A_{n+1}B_n − B_{n+1}A_n)`. -/
theorem cf_two_step_det (a b : ℕ → ℂ) (n : ℕ) :
    cfA a b (n + 2) * cfB a b n - cfB a b (n + 2) * cfA a b n =
      b (n + 2) * (cfA a b (n + 1) * cfB a b n - cfB a b (n + 1) * cfA a b n) := by
  simp only [cfA, cfB, cfP, cfQ]
  ring

/-- `C_{n+2} = Cₙ` iff `b_{n+2} = 0`. -/
theorem convPt_add_two_eq_iff {a b : ℕ → ℂ} (ha : ∀ k ≥ 1, a k ≠ 0) (n : ℕ) :
    convPt a b (n + 2) = convPt a b n ↔ b (n + 2) = 0 := by
  rw [convPt, convPt, cfPoint_eq_iff (cfAB_ne_zero ha _) (cfAB_ne_zero ha _)]
  have h := cf_two_step_det a b n
  have hd := dlmf_1_12_7 a b (n + 1)
  have hq : cfQ a b (n + 1) = cfB a b n := rfl
  have hp : cfP a b (n + 1) = cfA a b n := rfl
  rw [hq, hp] at hd
  rw [hd] at h
  have hne : (-1 : ℂ) ^ (n + 1 + 1) * ∏ k ∈ Icc 1 (n + 1), a k ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (by norm_num))
      (prod_ne_zero_iff.mpr fun k hk => ha k (mem_Icc.mp hk).1)
  rw [show cfA a b (n + 2) * cfB a b n - cfA a b n * cfB a b (n + 2) =
    cfA a b (n + 2) * cfB a b n - cfB a b (n + 2) * cfA a b n by ring, h]
  exact ⟨fun h0 => (mul_eq_zero.mp h0).resolve_right hne, fun h0 => by rw [h0, zero_mul]⟩

/-- DLMF §1.12(iv): the even part (`C′ₙ = C₂ₙ`) of `C` exists iff `b_{2k} ≠ 0`, `k = 1, 2, …`. -/
theorem dlmf_1_12_iv_even_exists {a b : ℕ → ℂ} (ha : ∀ k ≥ 1, a k ≠ 0) :
    (∃ a' b' : ℕ → ℂ, (∀ k ≥ 1, a' k ≠ 0) ∧ ∀ n, convPt a' b' n = convPt a b (2 * n)) ↔
      ∀ k ≥ 1, b (2 * k) ≠ 0 := by
  rw [dlmf_1_12_22]
  constructor
  · rintro ⟨-, h⟩ k hk
    obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
    have := h m
    rw [show 2 * (m + 1) = 2 * m + 2 by ring] at this ⊢
    exact fun h0 => this ((convPt_add_two_eq_iff ha _).mpr h0)
  · intro h
    refine ⟨by simp [convPt, cfPoint, cfA, cfB, cfP, cfQ, coe_ne_infty], fun n => ?_⟩
    rw [show 2 * (n + 1) = 2 * n + 2 by ring, Ne, convPt_add_two_eq_iff ha]
    have := h (n + 1) (by omega)
    rwa [show 2 * (n + 1) = 2 * n + 2 by ring] at this

/-- DLMF §1.12(iv): the odd part (`C′ₙ = C_{2n+1}`) of `C` exists iff `b_{2k+1} ≠ 0`,
`k = 0, 1, 2, …`. -/
theorem dlmf_1_12_iv_odd_exists {a b : ℕ → ℂ} (ha : ∀ k ≥ 1, a k ≠ 0) :
    (∃ a' b' : ℕ → ℂ, (∀ k ≥ 1, a' k ≠ 0) ∧ ∀ n, convPt a' b' n = convPt a b (2 * n + 1)) ↔
      ∀ k, b (2 * k + 1) ≠ 0 := by
  rw [dlmf_1_12_22]
  have h1 : convPt a b (2 * 0 + 1) ≠ ∞ ↔ b 1 ≠ 0 := by
    have hB1 : cfB a b 1 = b 1 := by simp [cfB, cfQ]
    rw [show 2 * 0 + 1 = 1 by rfl, convPt, hB1, cfPoint]
    split_ifs with h
    · simp [h]
    · simp [h, coe_ne_infty]
  constructor
  · rintro ⟨h0, h⟩ k
    rcases k with _ | m
    · exact h1.mp h0
    · have := h m
      rw [show 2 * (m + 1) + 1 = (2 * m + 1) + 2 by ring] at this ⊢
      exact fun h0 => this ((convPt_add_two_eq_iff ha _).mpr h0)
  · intro h
    refine ⟨h1.mpr (h 0), fun n => ?_⟩
    rw [show 2 * (n + 1) + 1 = (2 * n + 1) + 2 by ring, Ne, convPt_add_two_eq_iff ha]
    have := h (n + 1)
    rwa [show 2 * (n + 1) + 1 = 2 * n + 1 + 2 by ring] at this

/-- The two-step recurrence: `b_{n−2}A_n = (b_{n−2}(b_nb_{n−1} + a_n) + b_na_{n−1})A_{n−2}
− a_{n−2}a_{n−1}b_nA_{n−4}` (and the same for `B`), stated with `n = m + 3`. -/
theorem cf_two_step (a b : ℕ → ℂ) (m : ℕ) :
    b (m + 1) * cfP a b (m + 4) = (b (m + 1) * (b (m + 3) * b (m + 2) + a (m + 3)) +
        b (m + 3) * a (m + 2)) * cfP a b (m + 2) - a (m + 1) * a (m + 2) * b (m + 3) * cfP a b m ∧
    b (m + 1) * cfQ a b (m + 4) = (b (m + 1) * (b (m + 3) * b (m + 2) + a (m + 3)) +
        b (m + 3) * a (m + 2)) * cfQ a b (m + 2) -
        a (m + 1) * a (m + 2) * b (m + 3) * cfQ a b m := by
  constructor <;> simp only [cfP, cfQ] <;> ring

/-- The partial numerators of the even part (1.12.23). -/
def evenA (a b : ℕ → ℂ) (k : ℕ) : ℂ :=
  if k = 1 then a 1 * b 2
  else -(a (2 * k - 2) * a (2 * k - 1) * (if k = 2 then 1 else b (2 * k - 4)) * b (2 * k))

/-- The partial denominators of the even part (1.12.23). -/
def evenB (a b : ℕ → ℂ) (k : ℕ) : ℂ :=
  if k = 0 then b 0 else if k = 1 then a 2 + b 1 * b 2
  else a (2 * k - 1) * b (2 * k) + b (2 * k - 2) * (a (2 * k) + b (2 * k - 1) * b (2 * k))

/-- The scaling `λ_k = b₂b₄⋯b_{2k−2}` of the even part. -/
def evenScale (b : ℕ → ℂ) : ℕ → ℂ
  | 0 => 1
  | 1 => 1
  | k + 2 => evenScale b (k + 1) * b (2 * k + 2)

theorem evenScale_succ (b : ℕ → ℂ) (k : ℕ) :
    evenScale b (k + 1) = evenScale b k * (if k = 0 then 1 else b (2 * k)) := by
  rcases k with _ | k
  · simp [evenScale]
  · simp [evenScale, show 2 * (k + 1) = 2 * k + 2 by ring]

theorem evenScale_ne_zero {b : ℕ → ℂ} (hb : ∀ k ≥ 1, b (2 * k) ≠ 0) : ∀ k, evenScale b k ≠ 0
  | 0 => one_ne_zero
  | 1 => one_ne_zero
  | k + 2 => mul_ne_zero (evenScale_ne_zero hb (k + 1)) (by
      have := hb (k + 1) (by omega)
      rwa [show 2 * (k + 1) = 2 * k + 2 by ring] at this)

/-- **DLMF 1.12.23**: the even part `b₀ + a₁b₂/(a₂ + b₁b₂ − a₂a₃b₄/(a₃b₄ + b₂(a₄ + b₃b₄) −
a₄a₅b₂b₆/(a₅b₆ + b₄(a₆ + b₅b₆) − ⋯)))` has `A′_k = λ_k A_{2k}`, `B′_k = λ_k B_{2k}`. -/
theorem dlmf_1_12_23_numer (a b : ℕ → ℂ) (k : ℕ) :
    cfA (evenA a b) (evenB a b) k = evenScale b k * cfA a b (2 * k) ∧
      cfB (evenA a b) (evenB a b) k = evenScale b k * cfB a b (2 * k) := by
  simp only [cfA, cfB]
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    match k with
    | 0 => simp [cfP, cfQ, evenB, evenScale]
    | 1 =>
      simp only [cfP, cfQ, evenA, evenB, evenScale]
      norm_num
      constructor <;> ring
    | k + 2 =>
      obtain ⟨p1, q1⟩ := ih (k + 1) (by omega)
      obtain ⟨p0, q0⟩ := ih k (by omega)
      obtain ⟨t1, t2⟩ := cf_two_step a b (2 * k + 1)
      rw [show k + 2 + 1 = (k + 1) + 2 by ring]
      rw [show cfP (evenA a b) (evenB a b) (k + 1 + 2) = evenB a b (k + 2) *
          cfP (evenA a b) (evenB a b) (k + 2) + evenA a b (k + 2) *
          cfP (evenA a b) (evenB a b) (k + 1) from rfl,
        show cfQ (evenA a b) (evenB a b) (k + 1 + 2) = evenB a b (k + 2) *
          cfQ (evenA a b) (evenB a b) (k + 2) + evenA a b (k + 2) *
          cfQ (evenA a b) (evenB a b) (k + 1) from rfl]
      rw [show k + 2 = k + 1 + 1 by ring] at p1 q1 ⊢
      rw [p1, q1, p0, q0]
      rw [show 2 * (k + 1 + 1) + 1 = 2 * k + 1 + 4 by ring,
        show 2 * (k + 1) + 1 = 2 * k + 1 + 2 by ring, show 2 * k + 1 = 2 * k + 1 + 0 by ring]
      have hs1 := evenScale_succ b (k + 1)
      have hs0 := evenScale_succ b k
      simp only [show k + 1 ≠ 0 by omega, ↓reduceIte, show 2 * (k + 1) = 2 * k + 2 by ring]
        at hs1
      simp only [evenA, evenB, show k + 1 + 1 ≠ 0 by omega, show k + 1 + 1 ≠ 1 by omega,
        ↓reduceIte, show 2 * (k + 1 + 1) = 2 * k + 4 by omega,
        show (k + 1 + 1 = 2) ↔ k = 0 by omega]
      rw [hs1, hs0]
      simp only [show 2 * k + 4 - 1 = 2 * k + 3 by omega, show 2 * k + 4 - 2 = 2 * k + 2 by omega,
        show 2 * k + 4 - 4 = 2 * k by omega]
      simp only [show 2 * k + 1 + 0 + 1 = 2 * k + 2 by ring,
        show 2 * k + 1 + 0 + 2 = 2 * k + 3 by ring,
        show 2 * k + 1 + 0 + 3 = 2 * k + 4 by ring, show 2 * k + 1 + 0 + 4 = 2 * k + 5 by ring,
        show 2 * k + 1 + 0 = 2 * k + 1 by ring] at t1 t2 ⊢
      constructor
      · split_ifs with hk
        · subst hk
          simp only [mul_zero, Nat.zero_add] at t1 ⊢
          linear_combination (-evenScale b 0) * t1
        · linear_combination (-(evenScale b k * b (2 * k))) * t1
      · split_ifs with hk
        · subst hk
          simp only [mul_zero, Nat.zero_add] at t2 ⊢
          linear_combination (-evenScale b 0) * t2
        · linear_combination (-(evenScale b k * b (2 * k))) * t2

/-- **DLMF 1.12.23**: if `b_{2k} ≠ 0` (`k ≥ 1`), the continued fraction 1.12.23 is the even part
of `C`: `C′ₙ = C₂ₙ`. -/
theorem dlmf_1_12_23 {a b : ℕ → ℂ} (hb : ∀ k ≥ 1, b (2 * k) ≠ 0) (n : ℕ) :
    convPt (evenA a b) (evenB a b) n = convPt a b (2 * n) := by
  obtain ⟨hA, hB⟩ := dlmf_1_12_23_numer a b n
  have hs := evenScale_ne_zero hb n
  rw [convPt, convPt, hA, hB, cfPoint, cfPoint, mul_div_mul_left _ _ hs]
  simp [hs]

/-- The partial numerators of the odd part (1.12.24). -/
noncomputable def oddA (a b : ℕ → ℂ) (k : ℕ) : ℂ :=
  if k = 1 then -(a 1 * a 2 * b 3 / b 1)
  else -(a (2 * k - 1) * a (2 * k) * b (2 * k - 3) * b (2 * k + 1))

/-- The partial denominators of the odd part (1.12.24). -/
noncomputable def oddB (a b : ℕ → ℂ) (k : ℕ) : ℂ :=
  if k = 0 then (a 1 + b 0 * b 1) / b 1
  else a (2 * k) * b (2 * k + 1) + b (2 * k - 1) * (a (2 * k + 1) + b (2 * k) * b (2 * k + 1))

/-- The scaling `μ₀ = 1/b₁`, `μ_{k+1} = μ_k b_{2k+1}` of the odd part. -/
noncomputable def oddScale (b : ℕ → ℂ) : ℕ → ℂ
  | 0 => 1 / b 1
  | k + 1 => oddScale b k * b (2 * k + 1)

theorem oddScale_ne_zero {b : ℕ → ℂ} (hb : ∀ k, b (2 * k + 1) ≠ 0) : ∀ k, oddScale b k ≠ 0
  | 0 => one_div_ne_zero (hb 0)
  | k + 1 => mul_ne_zero (oddScale_ne_zero hb k) (hb k)

/-- **DLMF 1.12.24**: the odd part `(a₁ + b₀b₁)/b₁ − (a₁a₂b₃/b₁)/(a₂b₃ + b₁(a₃ + b₂b₃) −
a₃a₄b₁b₅/(a₄b₅ + b₃(a₅ + b₄b₅) − ⋯))` has `A′_k = μ_k A_{2k+1}`, `B′_k = μ_k B_{2k+1}`
(`b₁ ≠ 0`). -/
theorem dlmf_1_12_24_numer {a b : ℕ → ℂ} (hb1 : b 1 ≠ 0) (k : ℕ) :
    cfA (oddA a b) (oddB a b) k = oddScale b k * cfA a b (2 * k + 1) ∧
      cfB (oddA a b) (oddB a b) k = oddScale b k * cfB a b (2 * k + 1) := by
  simp only [cfA, cfB]
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    match k with
    | 0 =>
      simp only [cfP, cfQ, oddB, oddScale]
      norm_num
      constructor
      · field_simp
        ring
      · field_simp
    | 1 =>
      obtain ⟨t1, t2⟩ := cf_two_step a b 0
      simp only [cfP, cfQ, oddA, oddB, oddScale] at t1 t2 ⊢
      norm_num at t1 t2 ⊢
      constructor
      · field_simp
        linear_combination (-1 : ℂ) * t1
      · field_simp
        linear_combination (-1 : ℂ) * t2
    | k + 2 =>
      obtain ⟨p1, q1⟩ := ih (k + 1) (by omega)
      obtain ⟨p0, q0⟩ := ih k (by omega)
      obtain ⟨t1, t2⟩ := cf_two_step a b (2 * k + 2)
      rw [show cfP (oddA a b) (oddB a b) (k + 2 + 1) = oddB a b (k + 2) *
          cfP (oddA a b) (oddB a b) (k + 2) + oddA a b (k + 2) *
          cfP (oddA a b) (oddB a b) (k + 1) from rfl,
        show cfQ (oddA a b) (oddB a b) (k + 2 + 1) = oddB a b (k + 2) *
          cfQ (oddA a b) (oddB a b) (k + 2) + oddA a b (k + 2) *
          cfQ (oddA a b) (oddB a b) (k + 1) from rfl]
      rw [show k + 2 = k + 1 + 1 by ring] at p1 q1 ⊢
      rw [p1, q1, p0, q0]
      simp only [oddA, oddB, oddScale, show k + 1 + 1 ≠ 0 by omega, show k + 1 + 1 ≠ 1 by omega,
        ↓reduceIte, show 2 * (k + 1 + 1) = 2 * k + 4 by omega,
        show 2 * k + 4 - 1 = 2 * k + 3 by omega, show 2 * k + 4 - 3 = 2 * k + 1 by omega,
        show 2 * (k + 1) + 1 = 2 * k + 3 by ring, show 2 * k + 4 + 1 = 2 * k + 5 by ring]
      simp only [show 2 * k + 2 + 1 = 2 * k + 3 by ring, show 2 * k + 2 + 2 = 2 * k + 4 by ring,
        show 2 * k + 2 + 3 = 2 * k + 5 by ring, show 2 * k + 2 + 4 = 2 * k + 6 by ring,
        show 2 * k + 1 + 1 = 2 * k + 2 by ring] at t1 t2 ⊢
      constructor
      · linear_combination (-(oddScale b k * b (2 * k + 1))) * t1
      · linear_combination (-(oddScale b k * b (2 * k + 1))) * t2

/-- **DLMF 1.12.24**: if `b_{2k+1} ≠ 0`, the continued fraction 1.12.24 is the odd part of `C`:
`C′ₙ = C_{2n+1}`. -/
theorem dlmf_1_12_24 {a b : ℕ → ℂ} (hb : ∀ k, b (2 * k + 1) ≠ 0) (n : ℕ) :
    convPt (oddA a b) (oddB a b) n = convPt a b (2 * n + 1) := by
  obtain ⟨hA, hB⟩ := dlmf_1_12_24_numer (a := a) (hb 0) n
  have hs := oddScale_ne_zero hb n
  rw [convPt, convPt, hA, hB, cfPoint, cfPoint, mul_div_mul_left _ _ hs]
  simp [hs]

end Azurite.DLMF
