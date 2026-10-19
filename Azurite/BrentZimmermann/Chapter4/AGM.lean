/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.BrentZimmermann.Chapter4.TangentAlgorithm

/-!
# Brent–Zimmermann §4.8: Arithmetic-geometric mean (introduction)

The (theoretically) fastest methods for very large precision use the AGM iteration of Gauss and
Legendre, with complexity `O(M(n) log n)` (large implicit constant).  Given `(a₀, b₀)`,

  `(a_{j+1}, b_{j+1}) = ((a_j + b_j)/2, √(a_j b_j))`,

which for real positive starting values converges quadratically to `AGM(a₀, b₀)`.  It is useful
because (1) it converges quadratically — eventually the number of correct digits doubles at each
step, so `O(log n)` iterations suffice; (2) each step costs `O(M(n))` (square root by Newton,
§3.5, §4.2.3); (3) suitable starting values give logarithms, other elementary functions, and
constants such as `π`, `ln 2`.

What is formalized (real positive starting values):

* `agmStep`, `agmSeq a b j`, the components `agmA`, `agmB`; positivity `agm_pos`.
* The sandwich `b_{j+1} ≤ a_{j+1}` (AM–GM, `agmB_le_agmA_succ`), `a` antitone and `b` monotone
  from index `1` (`agmA_antitone`, `agmB_monotone`), `b_j ≤ a_j` for `j ≥ 1`.
* The gap identity `a_{j+1} − b_{j+1} = (√a_j − √b_j)²/2` (`agm_gap_succ`), the linear bound
  `≤ (a_j − b_j)/2` and the quadratic bound `≤ (a_j − b_j)²/(8 b_j)` (`agm_gap_succ_le_half`,
  `agm_gap_succ_le_sq`); hence `a_{j+1} − b_{j+1} ≤ (a_1 − b_1)/2^j` (`agm_gap_le_half_pow`) and
  the quadratic convergence `a_{j+1} − b_{j+1} ≤ 8 b_1 ((a_1 − b_1)/(8 b_1))^(2^j)` (`agm_gap_le`,
  via the generic `quadratic_decay`).
* The limit `AGM a b` (as `⨅ j, a_{j+1}`): `tendsto_agmA`, `tendsto_agmB`, the bracket
  `b_j ≤ AGM a b ≤ a_j` (`j ≥ 1`), `min a b ≤ AGM a b ≤ max a b`, symmetry `AGM_comm`,
  `AGM_self`, invariance `AGM_step` (`AGM(a, b) = AGM((a+b)/2, √(ab))`), homogeneity `AGM_smul`.
* The iteration count: once `a_1 ≤ 5 b_1`, `n ≤ 2^j` gives `a_{j+1} − b_{j+1} ≤ 8 b_1 / 2^n`
  (`agm_gap_le_two_pow`), so `Nat.clog 2 n + 1` iterations reach `n` bits (`agm_iterations`):
  the `O(log n)` iterations of the text.

Not formalized: the cost model (`O(M(n))` per step, `O(M(n) log n)` total), complex starting
values (§4.8.5, §4.12), and the applications (later subsections).
-/

namespace Azurite

namespace BZ

open Filter Topology

/-! ### The iteration -/

/-- One AGM step `(a, b) ↦ ((a + b)/2, √(ab))`. -/
noncomputable def agmStep (p : ℝ × ℝ) : ℝ × ℝ := ((p.1 + p.2) / 2, Real.sqrt (p.1 * p.2))

/-- The AGM iteration started at `(a, b)`. -/
noncomputable def agmSeq (a b : ℝ) : ℕ → ℝ × ℝ
  | 0 => (a, b)
  | j + 1 => agmStep (agmSeq a b j)

/-- `a_j`. -/
noncomputable def agmA (a b : ℝ) (j : ℕ) : ℝ := (agmSeq a b j).1

/-- `b_j`. -/
noncomputable def agmB (a b : ℝ) (j : ℕ) : ℝ := (agmSeq a b j).2

variable {a b : ℝ}

theorem agmA_zero : agmA a b 0 = a := rfl

theorem agmB_zero : agmB a b 0 = b := rfl

theorem agmA_succ (j : ℕ) : agmA a b (j + 1) = (agmA a b j + agmB a b j) / 2 := rfl

theorem agmB_succ (j : ℕ) : agmB a b (j + 1) = Real.sqrt (agmA a b j * agmB a b j) := rfl

theorem agm_pos (ha : 0 < a) (hb : 0 < b) : ∀ j, 0 < agmA a b j ∧ 0 < agmB a b j := by
  intro j
  induction j with
  | zero => exact ⟨ha, hb⟩
  | succ j ih =>
    refine ⟨?_, ?_⟩
    · rw [agmA_succ]; linarith [ih.1, ih.2]
    · rw [agmB_succ]; exact Real.sqrt_pos.mpr (mul_pos ih.1 ih.2)

/-- AM–GM: `b_{j+1} ≤ a_{j+1}`. -/
theorem agmB_le_agmA_succ (ha : 0 < a) (hb : 0 < b) (j : ℕ) :
    agmB a b (j + 1) ≤ agmA a b (j + 1) := by
  obtain ⟨hA, hB⟩ := agm_pos ha hb j
  rw [agmA_succ, agmB_succ]
  exact Real.sqrt_le_iff.mpr ⟨by positivity, by nlinarith [sq_nonneg (agmA a b j - agmB a b j)]⟩

theorem agmB_le_agmA (ha : 0 < a) (hb : 0 < b) {j : ℕ} (hj : 1 ≤ j) : agmB a b j ≤ agmA a b j := by
  obtain ⟨j, rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  exact agmB_le_agmA_succ ha hb j

/-- `a` is antitone from index `1`. -/
theorem agmA_antitone (ha : 0 < a) (hb : 0 < b) : Antitone fun j => agmA a b (j + 1) :=
  antitone_nat_of_succ_le fun j => by
    rw [agmA_succ (j + 1)]
    linarith [agmB_le_agmA_succ ha hb j]

/-- `b` is monotone from index `1`. -/
theorem agmB_monotone (ha : 0 < a) (hb : 0 < b) : Monotone fun j => agmB a b (j + 1) :=
  monotone_nat_of_le_succ fun j => by
    obtain ⟨hA, hB⟩ := agm_pos ha hb (j + 1)
    rw [agmB_succ (j + 1)]
    exact (Real.le_sqrt hB.le (by positivity)).mpr
      (by nlinarith [agmB_le_agmA_succ ha hb j])

/-! ### The gap `a_j − b_j` -/

/-- `a_{j+1} − b_{j+1} = (√a_j − √b_j)²/2`. -/
theorem agm_gap_succ (ha : 0 < a) (hb : 0 < b) (j : ℕ) :
    agmA a b (j + 1) - agmB a b (j + 1)
      = (Real.sqrt (agmA a b j) - Real.sqrt (agmB a b j)) ^ 2 / 2 := by
  obtain ⟨hA, hB⟩ := agm_pos ha hb j
  rw [agmA_succ, agmB_succ, Real.sqrt_mul hA.le]
  have h1 := Real.sq_sqrt hA.le
  have h2 := Real.sq_sqrt hB.le
  linear_combination (-1 / 2 : ℝ) * h1 + (-1 / 2 : ℝ) * h2

/-- The linear bound `a_{j+1} − b_{j+1} ≤ (a_j − b_j)/2` once `b_j ≤ a_j`. -/
theorem agm_gap_succ_le_half (ha : 0 < a) (hb : 0 < b) {j : ℕ} (hj : 1 ≤ j) :
    agmA a b (j + 1) - agmB a b (j + 1) ≤ (agmA a b j - agmB a b j) / 2 := by
  obtain ⟨hA, hB⟩ := agm_pos ha hb j
  have hle := agmB_le_agmA ha hb hj
  rw [agm_gap_succ ha hb]
  have hs := Real.sq_sqrt hA.le
  have ht := Real.sq_sqrt hB.le
  have hst := Real.sqrt_le_sqrt hle
  have ht0 := Real.sqrt_nonneg (agmB a b j)
  nlinarith [mul_le_mul_of_nonneg_left hst ht0]

/-- The quadratic bound `a_{j+1} − b_{j+1} ≤ (a_j − b_j)²/(8 b_j)` once `b_j ≤ a_j`. -/
theorem agm_gap_succ_le_sq (ha : 0 < a) (hb : 0 < b) {j : ℕ} (hj : 1 ≤ j) :
    agmA a b (j + 1) - agmB a b (j + 1) ≤ (agmA a b j - agmB a b j) ^ 2 / (8 * agmB a b j) := by
  obtain ⟨hA, hB⟩ := agm_pos ha hb j
  have hle := agmB_le_agmA ha hb hj
  rw [agm_gap_succ ha hb, div_le_div_iff₀ (by norm_num) (by positivity)]
  have hs := Real.sq_sqrt hA.le
  have ht := Real.sq_sqrt hB.le
  have hst : 0 ≤ Real.sqrt (agmA a b j) - Real.sqrt (agmB a b j) := by
    linarith [Real.sqrt_le_sqrt hle]
  have ht0 := Real.sqrt_nonneg (agmB a b j)
  have hkey : 0 ≤ (Real.sqrt (agmA a b j) - Real.sqrt (agmB a b j)) ^ 2
      * ((Real.sqrt (agmA a b j) - Real.sqrt (agmB a b j))
        * (Real.sqrt (agmA a b j) + 3 * Real.sqrt (agmB a b j))) :=
    mul_nonneg (sq_nonneg _) (mul_nonneg hst (by positivity))
  nlinarith [hkey]

/-- `a_{j+1} − b_{j+1} ≤ (a_1 − b_1)/2^j`. -/
theorem agm_gap_le_half_pow (ha : 0 < a) (hb : 0 < b) (j : ℕ) :
    agmA a b (j + 1) - agmB a b (j + 1) ≤ (agmA a b 1 - agmB a b 1) / 2 ^ j := by
  induction j with
  | zero => simp
  | succ j ih =>
    calc agmA a b (j + 1 + 1) - agmB a b (j + 1 + 1)
        ≤ (agmA a b (j + 1) - agmB a b (j + 1)) / 2 := agm_gap_succ_le_half ha hb (by omega)
      _ ≤ (agmA a b 1 - agmB a b 1) / 2 ^ j / 2 := by gcongr
      _ = (agmA a b 1 - agmB a b 1) / 2 ^ (j + 1) := by rw [pow_succ]; ring

/-- Quadratic decay: if `e_{j+1} ≤ C e_j²` with `e ≥ 0`, then `C e_j ≤ (C e_0)^(2^j)`. -/
theorem quadratic_decay {e : ℕ → ℝ} {C : ℝ} (hC : 0 ≤ C) (he : ∀ j, 0 ≤ e j)
    (h : ∀ j, e (j + 1) ≤ C * e j ^ 2) : ∀ j, C * e j ≤ (C * e 0) ^ (2 ^ j) := by
  intro j
  induction j with
  | zero => simp
  | succ j ih =>
    calc C * e (j + 1) ≤ C * (C * e j ^ 2) := mul_le_mul_of_nonneg_left (h j) hC
      _ = (C * e j) ^ 2 := by ring
      _ ≤ ((C * e 0) ^ (2 ^ j)) ^ 2 := pow_le_pow_left₀ (mul_nonneg hC (he j)) ih 2
      _ = (C * e 0) ^ (2 ^ (j + 1)) := by rw [← pow_mul, pow_succ]

/-- Quadratic convergence: `a_{j+1} − b_{j+1} ≤ 8 b_1 ((a_1 − b_1)/(8 b_1))^(2^j)`. -/
theorem agm_gap_le (ha : 0 < a) (hb : 0 < b) (j : ℕ) :
    agmA a b (j + 1) - agmB a b (j + 1)
      ≤ 8 * agmB a b 1 * ((agmA a b 1 - agmB a b 1) / (8 * agmB a b 1)) ^ (2 ^ j) := by
  have hb1 : 0 < agmB a b 1 := (agm_pos ha hb 1).2
  have hC : 0 ≤ 1 / (8 * agmB a b 1) := by positivity
  have hdecay := quadratic_decay (e := fun j => agmA a b (j + 1) - agmB a b (j + 1))
    (C := 1 / (8 * agmB a b 1)) hC
    (fun j => by linarith [agmB_le_agmA_succ ha hb j])
    (fun j => by
      have h1 := agm_gap_succ_le_sq ha hb (j := j + 1) (by omega)
      have h2 : agmB a b 1 ≤ agmB a b (j + 1) := agmB_monotone ha hb (Nat.zero_le j)
      have h3 : 0 ≤ (agmA a b (j + 1) - agmB a b (j + 1)) ^ 2 := sq_nonneg _
      calc agmA a b (j + 1 + 1) - agmB a b (j + 1 + 1)
          ≤ (agmA a b (j + 1) - agmB a b (j + 1)) ^ 2 / (8 * agmB a b (j + 1)) := h1
        _ ≤ (agmA a b (j + 1) - agmB a b (j + 1)) ^ 2 / (8 * agmB a b 1) := by gcongr
        _ = 1 / (8 * agmB a b 1) * (agmA a b (j + 1) - agmB a b (j + 1)) ^ 2 := by ring) j
  rw [zero_add] at hdecay
  calc agmA a b (j + 1) - agmB a b (j + 1)
      = 8 * agmB a b 1 * (1 / (8 * agmB a b 1) * (agmA a b (j + 1) - agmB a b (j + 1))) := by
        field_simp
    _ ≤ 8 * agmB a b 1 * (1 / (8 * agmB a b 1) * (agmA a b 1 - agmB a b 1)) ^ (2 ^ j) := by
        gcongr
    _ = 8 * agmB a b 1 * ((agmA a b 1 - agmB a b 1) / (8 * agmB a b 1)) ^ (2 ^ j) := by ring

/-! ### The limit -/

/-- `AGM(a, b)`, as the infimum of the antitone sequence `a_{j+1}`. -/
noncomputable def AGM (a b : ℝ) : ℝ := ⨅ j : ℕ, agmA a b (j + 1)

theorem agmB_one_le_agmA_succ (ha : 0 < a) (hb : 0 < b) (j : ℕ) :
    agmB a b 1 ≤ agmA a b (j + 1) :=
  (agmB_monotone ha hb (Nat.zero_le j)).trans (agmB_le_agmA_succ ha hb j)

theorem bddBelow_agmA (ha : 0 < a) (hb : 0 < b) :
    BddBelow (Set.range fun j => agmA a b (j + 1)) :=
  ⟨agmB a b 1, fun _ ⟨j, hj⟩ => hj ▸ agmB_one_le_agmA_succ ha hb j⟩

theorem tendsto_agmA_succ (ha : 0 < a) (hb : 0 < b) :
    Tendsto (fun j => agmA a b (j + 1)) atTop (𝓝 (AGM a b)) :=
  tendsto_atTop_ciInf (agmA_antitone ha hb) (bddBelow_agmA ha hb)

theorem tendsto_agmA (ha : 0 < a) (hb : 0 < b) : Tendsto (agmA a b) atTop (𝓝 (AGM a b)) :=
  (tendsto_add_atTop_iff_nat 1).mp (tendsto_agmA_succ ha hb)

/-- The gap tends to `0`. -/
theorem tendsto_agm_gap (ha : 0 < a) (hb : 0 < b) :
    Tendsto (fun j => agmA a b (j + 1) - agmB a b (j + 1)) atTop (𝓝 0) := by
  have h : Tendsto (fun j : ℕ => (agmA a b 1 - agmB a b 1) / 2 ^ j) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_pow_atTop_atTop_of_one_lt one_lt_two)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h
    (fun j => by linarith [agmB_le_agmA_succ ha hb j]) (fun j => agm_gap_le_half_pow ha hb j)

theorem tendsto_agmB_succ (ha : 0 < a) (hb : 0 < b) :
    Tendsto (fun j => agmB a b (j + 1)) atTop (𝓝 (AGM a b)) := by
  have := (tendsto_agmA_succ ha hb).sub (tendsto_agm_gap ha hb)
  rw [sub_zero] at this
  refine this.congr fun j => ?_
  ring

theorem tendsto_agmB (ha : 0 < a) (hb : 0 < b) : Tendsto (agmB a b) atTop (𝓝 (AGM a b)) :=
  (tendsto_add_atTop_iff_nat 1).mp (tendsto_agmB_succ ha hb)

/-- `AGM a b ≤ a_j` for `j ≥ 1`. -/
theorem AGM_le_agmA (ha : 0 < a) (hb : 0 < b) {j : ℕ} (hj : 1 ≤ j) : AGM a b ≤ agmA a b j := by
  obtain ⟨j, rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  exact ciInf_le (bddBelow_agmA ha hb) j

/-- `b_j ≤ AGM a b` for `j ≥ 1`. -/
theorem agmB_le_AGM (ha : 0 < a) (hb : 0 < b) {j : ℕ} (hj : 1 ≤ j) : agmB a b j ≤ AGM a b := by
  obtain ⟨j, rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  refine le_ciInf fun i => ?_
  rcases le_or_gt j i with hji | hij
  · exact (agmB_monotone ha hb hji).trans (agmB_le_agmA_succ ha hb i)
  · exact (agmB_le_agmA_succ ha hb j).trans (agmA_antitone ha hb hij.le)

theorem min_le_AGM (ha : 0 < a) (hb : 0 < b) : min a b ≤ AGM a b := by
  refine le_trans ?_ (agmB_le_AGM ha hb le_rfl)
  rw [agmB_succ, agmA_zero, agmB_zero]
  refine (Real.le_sqrt (by positivity) (by positivity)).mpr ?_
  rcases le_total a b with h | h
  · rw [min_eq_left h]; nlinarith
  · rw [min_eq_right h]; nlinarith

theorem AGM_le_max (ha : 0 < a) (hb : 0 < b) : AGM a b ≤ max a b := by
  refine (AGM_le_agmA ha hb le_rfl).trans ?_
  rw [agmA_succ, agmA_zero, agmB_zero]
  rcases le_total a b with h | h
  · rw [max_eq_right h]; linarith
  · rw [max_eq_left h]; linarith

/-! ### Symmetry, invariance, homogeneity -/

theorem agmSeq_comm_succ (a b : ℝ) : ∀ j, agmSeq a b (j + 1) = agmSeq b a (j + 1) := by
  intro j
  induction j with
  | zero =>
    show agmStep (a, b) = agmStep (b, a)
    simp only [agmStep, Prod.mk.injEq]
    exact ⟨by ring, by rw [mul_comm]⟩
  | succ j ih => show agmStep (agmSeq a b (j + 1)) = agmStep (agmSeq b a (j + 1)); rw [ih]

theorem AGM_comm (a b : ℝ) : AGM a b = AGM b a := by
  unfold AGM agmA
  simp only [agmSeq_comm_succ]

theorem agmSeq_self (ha : 0 ≤ a) : ∀ j, agmSeq a a j = (a, a) := by
  intro j
  induction j with
  | zero => rfl
  | succ j ih =>
    show agmStep (agmSeq a a j) = (a, a)
    rw [ih]
    simp only [agmStep, Prod.mk.injEq]
    exact ⟨by ring, Real.sqrt_mul_self ha⟩

theorem AGM_self (ha : 0 ≤ a) : AGM a a = a := by
  unfold AGM agmA
  simp only [agmSeq_self ha, ciInf_const]

theorem agmSeq_step (a b : ℝ) (j : ℕ) :
    agmSeq ((a + b) / 2) (Real.sqrt (a * b)) j = agmSeq a b (j + 1) := by
  induction j with
  | zero => rfl
  | succ j ih => show agmStep _ = agmStep _; rw [ih]

/-- The AGM is invariant under one step: `AGM(a, b) = AGM((a+b)/2, √(ab))`. -/
theorem AGM_step (ha : 0 < a) (hb : 0 < b) : AGM a b = AGM ((a + b) / 2) (Real.sqrt (a * b)) := by
  have h1 : Tendsto (agmA ((a + b) / 2) (Real.sqrt (a * b))) atTop (𝓝 (AGM a b)) := by
    have := tendsto_agmA_succ ha hb
    refine this.congr fun j => ?_
    simp only [agmA, agmSeq_step]
  exact tendsto_nhds_unique h1
    (tendsto_agmA (by positivity) (Real.sqrt_pos.mpr (mul_pos ha hb)))

theorem agmSeq_smul {c : ℝ} (hc : 0 ≤ c) (a b : ℝ) :
    ∀ j, agmSeq (c * a) (c * b) j = (c * agmA a b j, c * agmB a b j) := by
  intro j
  induction j with
  | zero => rfl
  | succ j ih =>
    show agmStep _ = _
    rw [ih]
    simp only [agmStep, agmA_succ, agmB_succ, Prod.mk.injEq]
    refine ⟨by ring, ?_⟩
    rw [show c * agmA a b j * (c * agmB a b j) = c ^ 2 * (agmA a b j * agmB a b j) by ring,
      Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq hc]

/-- Homogeneity: `AGM(ca, cb) = c · AGM(a, b)` for `c > 0`. -/
theorem AGM_smul {c : ℝ} (hc : 0 < c) (ha : 0 < a) (hb : 0 < b) :
    AGM (c * a) (c * b) = c * AGM a b := by
  have h1 : Tendsto (agmA (c * a) (c * b)) atTop (𝓝 (c * AGM a b)) := by
    have := (tendsto_agmA ha hb).const_mul c
    refine this.congr fun j => ?_
    simp only [agmA, agmSeq_smul hc.le]
  exact tendsto_nhds_unique (tendsto_agmA (by positivity) (by positivity)) h1

/-! ### Strictness for distinct starting values -/

/-- `a_n ≠ b_n` for all `n` when `a ≠ b`: the gap `(√a_n − √b_n)²/2` never vanishes. -/
theorem agmA_ne_agmB (ha : 0 < a) (hb : 0 < b) (hab : a ≠ b) : ∀ n, agmA a b n ≠ agmB a b n
  | 0 => hab
  | n + 1 => by
    intro h
    have hg := agm_gap_succ ha hb n
    rw [sub_eq_zero.mpr h] at hg
    obtain ⟨hA, hB⟩ := agm_pos ha hb n
    have hsq : (Real.sqrt (agmA a b n) - Real.sqrt (agmB a b n)) ^ 2 = 0 := by linarith
    have := sub_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp hsq)
    exact agmA_ne_agmB ha hb hab n ((Real.sqrt_inj hA.le hB.le).mp this)

theorem agmB_lt_agmA (ha : 0 < a) (hb : 0 < b) (hab : a ≠ b) {n : ℕ} (hn : 1 ≤ n) :
    agmB a b n < agmA a b n :=
  lt_of_le_of_ne (agmB_le_agmA ha hb hn) (agmA_ne_agmB ha hb hab n).symm

/-- `b_n < AGM(a, b)` strictly for `n ≥ 1` when `a ≠ b`. -/
theorem agmB_lt_AGM (ha : 0 < a) (hb : 0 < b) (hab : a ≠ b) {n : ℕ} (hn : 1 ≤ n) :
    agmB a b n < AGM a b := by
  obtain ⟨hA, hB⟩ := agm_pos ha hb n
  have h1 : agmB a b n < agmB a b (n + 1) := by
    rw [agmB_succ, Real.lt_sqrt hB.le]
    nlinarith [agmB_lt_agmA ha hb hab hn]
  exact h1.trans_le (agmB_le_AGM ha hb (by omega))

/-- `AGM(a, b) < a_n` strictly for `n ≥ 1` when `a ≠ b`. -/
theorem AGM_lt_agmA (ha : 0 < a) (hb : 0 < b) (hab : a ≠ b) {n : ℕ} (hn : 1 ≤ n) :
    AGM a b < agmA a b n := by
  have h1 : agmA a b (n + 1) < agmA a b n := by
    rw [agmA_succ]; linarith [agmB_lt_agmA ha hb hab hn]
  exact (AGM_le_agmA ha hb (by omega)).trans_lt h1

/-! ### The number of iterations -/

/-- Once `a_1 ≤ 5 b_1`, `n ≤ 2^j` gives `a_{j+1} − b_{j+1} ≤ 8 b_1 / 2^n`: the number of correct
bits doubles at each step. -/
theorem agm_gap_le_two_pow (ha : 0 < a) (hb : 0 < b) (h : agmA a b 1 - agmB a b 1 ≤ 4 * agmB a b 1)
    {j n : ℕ} (hn : n ≤ 2 ^ j) :
    agmA a b (j + 1) - agmB a b (j + 1) ≤ 8 * agmB a b 1 / 2 ^ n := by
  have hb1 : 0 < agmB a b 1 := (agm_pos ha hb 1).2
  have hr0 : 0 ≤ (agmA a b 1 - agmB a b 1) / (8 * agmB a b 1) := by
    have := agmB_le_agmA_succ ha hb 0
    positivity
  have hr1 : (agmA a b 1 - agmB a b 1) / (8 * agmB a b 1) ≤ 1 / 2 := by
    rw [div_le_iff₀ (by positivity)]; linarith
  calc agmA a b (j + 1) - agmB a b (j + 1)
      ≤ 8 * agmB a b 1 * ((agmA a b 1 - agmB a b 1) / (8 * agmB a b 1)) ^ (2 ^ j) :=
        agm_gap_le ha hb j
    _ ≤ 8 * agmB a b 1 * (1 / 2) ^ (2 ^ j) := by gcongr
    _ ≤ 8 * agmB a b 1 * (1 / 2) ^ n :=
        mul_le_mul_of_nonneg_left
          (pow_le_pow_of_le_one (a := (1 / 2 : ℝ)) (by norm_num) (by norm_num) hn)
          (by positivity)
    _ = 8 * agmB a b 1 / 2 ^ n := by rw [one_div_pow]; ring

/-- `⌈log₂ n⌉ + 1` iterations give `n` bits (after the linear phase `a_1 ≤ 5 b_1`): the
`O(log n)` iterations of the text. -/
theorem agm_iterations (ha : 0 < a) (hb : 0 < b) (h : agmA a b 1 - agmB a b 1 ≤ 4 * agmB a b 1)
    (n : ℕ) :
    agmA a b (Nat.clog 2 n + 1) - agmB a b (Nat.clog 2 n + 1) ≤ 8 * agmB a b 1 / 2 ^ n :=
  agm_gap_le_two_pow ha hb h (Nat.le_pow_clog one_lt_two n)

end BZ

end Azurite
