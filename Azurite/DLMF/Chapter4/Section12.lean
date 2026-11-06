/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# DLMF §4.12: Generalized logarithms and exponentials

Formalizations of <https://dlmf.nist.gov/4.12>.

* 4.12.1–4.12.2: `IsGenExp φ` (`φ(x+1) = e^{φ(x)}` for `x > −1`, `φ(0) = 0`, `φ` strictly
  increasing on `[0, 1]`); 4.12.3–4.12.4: `IsGenLog ψ`.
* "Its inverse `ψ(x)` is called a generalized logarithm. It, too, is strictly increasing when
  `0 ≤ x ≤ 1`, and (4.12.3), (4.12.4)": `isGenLog_of_inverse`.
* "These functions are not unique": `genExpOf h` extends any strictly increasing `h` on `[0, 1]`
  with `h(0) = 0`, `h(1) = 1` to a generalized exponential (`isGenExp_genExpOf`);
  `genExp_not_unique`.
* The simplest choice 4.12.5–4.12.10: `simpleGenExp` (= `genExpOf id`) and `simpleGenLog`
  (with the iterated logarithm and the integer `ℓ` of 4.12.10, `dlmf_4_12_9`), mutually inverse
  (`genLog_genExp`, `genExp_genLog`).
* "Both `φ(x)` and `ψ(x)` are continuously differentiable": `contDiffOn_genExp` (on `(−1, ∞)`),
  `contDiff_genLog`.

In Lean `log 0 = 0`, so "the positive integer `ℓ` determined by 4.12.10" is pinned down by also
requiring the earlier iterates to be positive (so that `ln^ℓ x` is defined in the real sense).
-/

open Set Filter Topology Real

namespace Azurite.DLMF

/-! ### Definitions 4.12.1–4.12.4 -/

/-- **DLMF 4.12.1–4.12.2**: a generalized exponential: `φ(x+1) = e^{φ(x)}` (`−1 < x < ∞`),
`φ(0) = 0`, strictly increasing for `0 ≤ x ≤ 1`. -/
def IsGenExp (φ : ℝ → ℝ) : Prop :=
  (∀ x, -1 < x → φ (x + 1) = exp (φ x)) ∧ φ 0 = 0 ∧ StrictMonoOn φ (Icc 0 1)

/-- **DLMF 4.12.3–4.12.4**: a generalized logarithm: `ψ(e^x) = 1 + ψ(x)` (`−∞ < x < ∞`),
`ψ(0) = 0`, strictly increasing for `0 ≤ x ≤ 1`. -/
def IsGenLog (ψ : ℝ → ℝ) : Prop :=
  (∀ x, ψ (exp x) = 1 + ψ x) ∧ ψ 0 = 0 ∧ StrictMonoOn ψ (Icc 0 1)

theorem IsGenExp.one {φ : ℝ → ℝ} (h : IsGenExp φ) : φ 1 = 1 := by
  have := h.1 0 (by norm_num); rw [zero_add, h.2.1, exp_zero] at this; exact this

theorem IsGenExp.pos {φ : ℝ → ℝ} (h : IsGenExp φ) {y : ℝ} (hy : 0 < y) : 0 < φ y := by
  rcases le_or_gt y 1 with h1 | h1
  · have := h.2.2 ⟨le_rfl, zero_le_one⟩ ⟨hy.le, h1⟩ hy; rwa [h.2.1] at this
  · have := h.1 (y - 1) (by linarith); rw [sub_add_cancel] at this; rw [this]; exact exp_pos _

theorem IsGenExp.gt_one {φ : ℝ → ℝ} (h : IsGenExp φ) {y : ℝ} (hy : 1 < y) : 1 < φ y := by
  have := h.1 (y - 1) (by linarith); rw [sub_add_cancel] at this
  have h0 := h.pos (show (0 : ℝ) < y - 1 by linarith)
  rw [this]; linarith [add_one_lt_exp h0.ne']

theorem IsGenExp.neg {φ : ℝ → ℝ} (h : IsGenExp φ) {y : ℝ} (hy : -1 < y) (hy0 : y < 0) :
    φ y < 0 := by
  have he := h.1 y hy
  have h1 : φ (y + 1) < 1 := by
    have := h.2.2 ⟨by linarith, by linarith⟩ ⟨zero_le_one, le_rfl⟩ (by linarith : y + 1 < 1)
    rwa [h.one] at this
  rw [he, ← exp_zero, exp_lt_exp] at h1
  exact h1

/-- **DLMF §4.12**: the inverse `ψ` of a generalized exponential is a generalized logarithm:
strictly increasing on `[0, 1]`, with 4.12.3 and 4.12.4. -/
theorem isGenLog_of_inverse {φ ψ : ℝ → ℝ} (hφ : IsGenExp φ)
    (hψ : ∀ x, -1 < ψ x ∧ φ (ψ x) = x) (hψφ : ∀ y, -1 < y → ψ (φ y) = y) : IsGenLog ψ := by
  refine ⟨fun x => ?_, ?_, ?_⟩
  · obtain ⟨h1, h2⟩ := hψ x
    have := hφ.1 (ψ x) h1
    rw [h2] at this
    rw [← this, hψφ _ (by linarith)]; ring
  · have := hψφ 0 (by norm_num); rwa [hφ.2.1] at this
  · have hmem : ∀ x ∈ Icc (0 : ℝ) 1, ψ x ∈ Icc (0 : ℝ) 1 := fun x hx => by
      obtain ⟨h1, h2⟩ := hψ x
      constructor
      · by_contra h; push Not at h
        have := hφ.neg h1 h; rw [h2] at this; linarith [hx.1]
      · by_contra h; push Not at h
        have := hφ.gt_one h; rw [h2] at this; linarith [hx.2]
    intro a ha b hb hab
    by_contra h; push Not at h
    have := hφ.2.2.monotoneOn (hmem b hb) (hmem a ha) h
    rw [(hψ a).2, (hψ b).2] at this
    linarith

/-! ### Generalized exponentials from their values on `[0, 1]` -/

/-- The generalized exponential with prescribed values `h` on `[0, 1]`:
`ln h(x + 1)` for `−1 < x < 0` and `exp^{⌊x⌋}(h(x − ⌊x⌋))` for `x ≥ 0`. -/
noncomputable def genExpOf (h : ℝ → ℝ) (x : ℝ) : ℝ :=
  if x < 0 then log (h (x + 1)) else exp^[⌊x⌋₊] (h (x - ⌊x⌋₊))

theorem genExpOf_of_mem_Icc {h : ℝ → ℝ} (h0 : h 0 = 0) (h1 : h 1 = 1) {x : ℝ}
    (hx : x ∈ Icc (0 : ℝ) 1) : genExpOf h x = h x := by
  rcases hx.2.lt_or_eq with hx1 | rfl
  · simp [genExpOf, not_lt.mpr hx.1, Nat.floor_eq_zero.mpr hx1]
  · simp [genExpOf, h0, h1]

/-- Any strictly increasing `h` on `[0, 1]` with `h(0) = 0`, `h(1) = 1` extends to a generalized
exponential. -/
theorem isGenExp_genExpOf {h : ℝ → ℝ} (h0 : h 0 = 0) (h1 : h 1 = 1)
    (hm : StrictMonoOn h (Icc 0 1)) : IsGenExp (genExpOf h) := by
  refine ⟨fun x hx => ?_, by simp [genExpOf, h0], ?_⟩
  · rcases lt_or_ge x 0 with hx0 | hx0
    · have hpos : 0 < h (x + 1) := by
        have := hm ⟨le_rfl, zero_le_one⟩ ⟨by linarith, by linarith⟩ (by linarith : (0:ℝ) < x + 1)
        rwa [h0] at this
      rw [genExpOf_of_mem_Icc h0 h1 ⟨by linarith, by linarith⟩]
      simp only [genExpOf, hx0, ↓reduceIte]
      rw [exp_log hpos]
    · simp only [genExpOf, not_lt.mpr hx0, not_lt.mpr (by linarith : (0 : ℝ) ≤ x + 1),
        ↓reduceIte]
      rw [Nat.floor_add_one hx0, Function.iterate_succ_apply']
      congr 2
      push_cast; ring_nf
  · exact hm.congr fun x hx => (genExpOf_of_mem_Icc h0 h1 hx).symm

/-- The simplest generalized exponential (4.12.5–4.12.7). -/
noncomputable def simpleGenExp : ℝ → ℝ := genExpOf id

theorem isGenExp_genExp : IsGenExp simpleGenExp :=
  isGenExp_genExpOf rfl rfl fun _ _ _ _ h => h

/-- **DLMF §4.12**: generalized exponentials are not unique (`h(x) = x²` gives another one). -/
theorem genExp_not_unique :
    IsGenExp (genExpOf fun x => x ^ 2) ∧ genExpOf (fun x => x ^ 2) ≠ simpleGenExp := by
  refine ⟨isGenExp_genExpOf (by norm_num) (by norm_num) fun a ha b _ hab => by
    show a ^ 2 < b ^ 2; nlinarith [ha.1], fun h => ?_⟩
  have := congrFun h (1 / 2)
  rw [simpleGenExp, genExpOf_of_mem_Icc (by norm_num) (by norm_num) ⟨by norm_num, by norm_num⟩,
    genExpOf_of_mem_Icc rfl rfl ⟨by norm_num, by norm_num⟩] at this
  norm_num at this

/-- **DLMF 4.12.5** (`φ`): `φ(x) = x` for `0 ≤ x ≤ 1`. -/
theorem dlmf_4_12_5_exp {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) : simpleGenExp x = x :=
  genExpOf_of_mem_Icc rfl rfl hx

/-- **DLMF 4.12.6**: `φ(x) = ln(x + 1)` for `−1 < x < 0`. -/
theorem dlmf_4_12_6 {x : ℝ} (hx : x < 0) : simpleGenExp x = log (x + 1) := by
  simp [simpleGenExp, genExpOf, hx]

/-- **DLMF 4.12.7**: `φ(x) = exp ⋯ exp (x − ⌊x⌋)` (`⌊x⌋` times) for `x > 1`. -/
theorem dlmf_4_12_7 {x : ℝ} (hx : 1 < x) : simpleGenExp x = exp^[⌊x⌋₊] (x - ⌊x⌋₊) := by
  simp [simpleGenExp, genExpOf, not_lt.mpr (by linarith : (0 : ℝ) ≤ x)]

/-! ### The simplest generalized logarithm -/

/-- `ℓ + ln^ℓ x` computed with fuel: stop as soon as the argument is `< 1`. -/
noncomputable def iterLogPsi : ℕ → ℝ → ℝ
  | 0, x => x
  | n + 1, x => if x < 1 then x else 1 + iterLogPsi n (log x)

/-- The simplest generalized logarithm (4.12.5, 4.12.8, 4.12.9). -/
noncomputable def simpleGenLog (x : ℝ) : ℝ := if x < 0 then exp x - 1 else iterLogPsi (⌊x⌋₊ + 1) x

theorem iterLogPsi_spec : ∀ (N : ℕ) (x : ℝ), 0 ≤ x → x < N →
    ∃ ℓ : ℕ, (∀ k < ℓ, 1 ≤ log^[k] x) ∧ 0 ≤ log^[ℓ] x ∧ log^[ℓ] x < 1 ∧
      iterLogPsi N x = ℓ + log^[ℓ] x
  | 0, x, hx, hN => absurd hN (by simp; linarith)
  | N + 1, x, hx, hN => by
    by_cases h1 : x < 1
    · exact ⟨0, by simp, by simpa using hx, by simpa using h1, by simp [iterLogPsi, h1]⟩
    · push Not at h1
      have hl0 : 0 ≤ log x := log_nonneg h1
      have hlN : log x < N := by
        have := log_le_sub_one_of_pos (by linarith : 0 < x); push_cast at hN; linarith
      obtain ⟨ℓ, h1', h2', h3', h4'⟩ := iterLogPsi_spec N (log x) hl0 hlN
      refine ⟨ℓ + 1, fun k hk => ?_, by rwa [Function.iterate_succ_apply],
        by rwa [Function.iterate_succ_apply], ?_⟩
      · rcases k with _ | j
        · simpa using h1
        · rw [Function.iterate_succ_apply]; exact h1' j (by omega)
      · simp only [iterLogPsi, not_lt.mpr h1, ↓reduceIte]
        rw [h4', Function.iterate_succ_apply]; push_cast; ring

theorem iterLogPsi_fuel : ∀ (N M : ℕ) (x : ℝ), 0 ≤ x → x < N → x < M →
    iterLogPsi N x = iterLogPsi M x
  | 0, _, x, hx, hN, _ => absurd hN (by simp; linarith)
  | _ + 1, 0, x, hx, _, hM => absurd hM (by simp; linarith)
  | N + 1, M + 1, x, hx, hN, hM => by
    by_cases h1 : x < 1
    · simp [iterLogPsi, h1]
    · push Not at h1
      have hl := log_le_sub_one_of_pos (by linarith : 0 < x)
      simp only [iterLogPsi, not_lt.mpr h1, ↓reduceIte]
      push_cast at hN hM
      rw [iterLogPsi_fuel N M (log x) (log_nonneg h1) (by linarith) (by linarith)]

theorem genLog_of_nonneg {x : ℝ} (hx : 0 ≤ x) {N : ℕ} (hN : x < N) :
    simpleGenLog x = iterLogPsi N x := by
  simp only [simpleGenLog, not_lt.mpr hx, ↓reduceIte]
  exact iterLogPsi_fuel _ _ x hx (by exact_mod_cast Nat.lt_floor_add_one x) hN

/-- **DLMF 4.12.5** (`ψ`): `ψ(x) = x` for `0 ≤ x ≤ 1`. -/
theorem dlmf_4_12_5_log {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) : simpleGenLog x = x := by
  rw [genLog_of_nonneg hx.1 (N := 2) (by norm_num; linarith [hx.2])]
  rcases hx.2.lt_or_eq with h | rfl
  · simp [iterLogPsi, h]
  · simp [iterLogPsi]

/-- **DLMF 4.12.8**: `ψ(x) = e^x − 1` for `x < 0`. -/
theorem dlmf_4_12_8 {x : ℝ} (hx : x < 0) : simpleGenLog x = exp x - 1 := by simp [simpleGenLog, hx]

/-- **DLMF 4.12.9–4.12.10**: for `x > 1`, `ψ(x) = ℓ + ln ⋯ ln x` (`ℓ` times), where `ℓ` is the
positive integer with `0 ≤ ln^ℓ x < 1` (the earlier iterates being positive). -/
theorem dlmf_4_12_9 {x : ℝ} (hx : 1 < x) :
    ∃ ℓ : ℕ, (1 ≤ ℓ ∧ (∀ k < ℓ, 0 < log^[k] x) ∧ 0 ≤ log^[ℓ] x ∧ log^[ℓ] x < 1) ∧
      simpleGenLog x = ℓ + log^[ℓ] x ∧
      ∀ ℓ' : ℕ, (1 ≤ ℓ' ∧ (∀ k < ℓ', 0 < log^[k] x) ∧ 0 ≤ log^[ℓ'] x ∧ log^[ℓ'] x < 1) →
        ℓ' = ℓ := by
  have hx0 : (0 : ℝ) ≤ x := by linarith
  obtain ⟨ℓ, h1, h2, h3, h4⟩ := iterLogPsi_spec (⌊x⌋₊ + 1) x hx0
    (by exact_mod_cast Nat.lt_floor_add_one x)
  have hℓ : 1 ≤ ℓ := by
    rcases ℓ with _ | ℓ
    · simp at h3; linarith
    · omega
  have hP : ∀ ℓ₁ ℓ₂ : ℕ, ℓ₁ < ℓ₂ → (∀ k < ℓ₂, 0 < log^[k] x) → log^[ℓ₁] x < 1 →
      0 ≤ log^[ℓ₂] x → False := by
    intro ℓ₁ ℓ₂ h12 hpos hlt hge
    have hneg : log^[ℓ₁ + 1] x < 0 := by
      rw [Function.iterate_succ_apply']; exact log_neg (hpos ℓ₁ h12) hlt
    rcases (Nat.succ_le_of_lt h12).lt_or_eq with h | h
    · exact absurd (hpos _ h) (not_lt.mpr hneg.le)
    · rw [← h] at hge; linarith
  refine ⟨ℓ, ⟨hℓ, fun k hk => by linarith [h1 k hk], h2, h3⟩, by
    rw [genLog_of_nonneg hx0 (by exact_mod_cast Nat.lt_floor_add_one x), h4],
    fun ℓ' ⟨_, hpos', h2', h3'⟩ => ?_⟩
  rcases lt_trichotomy ℓ' ℓ with h | h | h
  · exact (hP ℓ' ℓ h (fun k hk => by linarith [h1 k hk]) h3' h2).elim
  · exact h
  · exact (hP ℓ ℓ' h hpos' h3 h2').elim

/-- **DLMF 4.12.3** for the simplest choice. -/
theorem genLog_exp (x : ℝ) : simpleGenLog (exp x) = 1 + simpleGenLog x := by
  rcases lt_or_ge x 0 with hx | hx
  · rw [dlmf_4_12_5_log ⟨(exp_pos x).le, (exp_lt_one_iff.mpr hx).le⟩, dlmf_4_12_8 hx]; ring
  · have hxe : x < ⌊exp x⌋₊ := by
      have h1 : x < ⌊x + 1⌋₊ := by rw [Nat.floor_add_one hx]; exact_mod_cast Nat.lt_floor_add_one x
      have h2 : (⌊x + 1⌋₊ : ℝ) ≤ ⌊exp x⌋₊ := by
        exact_mod_cast Nat.floor_le_floor (by linarith [add_one_le_exp x])
      linarith
    rw [genLog_of_nonneg (exp_pos x).le (by exact_mod_cast Nat.lt_floor_add_one (exp x)),
      genLog_of_nonneg hx hxe]
    simp only [iterLogPsi, not_lt.mpr (one_le_exp hx), ↓reduceIte, log_exp]

theorem isGenLog_genLog : IsGenLog simpleGenLog :=
  ⟨genLog_exp, dlmf_4_12_5_log ⟨le_rfl, zero_le_one⟩,
    (show StrictMonoOn id (Icc (0 : ℝ) 1) from fun _ _ _ _ h => h).congr
      fun _ hx => (dlmf_4_12_5_log hx).symm⟩

theorem genLog_gt (x : ℝ) : -1 < simpleGenLog x := by
  rcases lt_or_ge x 0 with hx | hx
  · rw [dlmf_4_12_8 hx]; linarith [exp_pos x]
  · obtain ⟨ℓ, -, h2, -, h4⟩ := iterLogPsi_spec (⌊x⌋₊ + 1) x hx
      (by exact_mod_cast Nat.lt_floor_add_one x)
    rw [genLog_of_nonneg hx (by exact_mod_cast Nat.lt_floor_add_one x), h4]
    have : (0 : ℝ) ≤ ℓ := Nat.cast_nonneg ℓ
    linarith

/-- The simplest `ψ` is the inverse of the simplest `φ` ("Correspondingly"). -/
theorem genLog_genExp {y : ℝ} (hy : -1 < y) : simpleGenLog (simpleGenExp y) = y := by
  suffices h : ∀ n : ℕ, ∀ y : ℝ, -1 < y → y < n → simpleGenLog (simpleGenExp y) = y from
    h (⌊y⌋₊ + 1) y hy (by exact_mod_cast Nat.lt_floor_add_one y)
  intro n
  induction n with
  | zero =>
    intro y hy hy0
    have hy0 : y < 0 := by simpa using hy0
    have hl : log (y + 1) < 0 := log_neg (by linarith) (by linarith)
    rw [dlmf_4_12_6 hy0, dlmf_4_12_8 hl, exp_log (by linarith)]; ring
  | succ n ih =>
    intro y hy hyn
    rcases lt_or_ge y 1 with h1 | h1
    · rcases lt_or_ge y 0 with h0 | h0
      · exact ih y hy (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
      · rw [dlmf_4_12_5_exp ⟨h0, h1.le⟩, dlmf_4_12_5_log ⟨h0, h1.le⟩]
    · have he := isGenExp_genExp.1 (y - 1) (by linarith)
      rw [sub_add_cancel] at he
      rw [he, genLog_exp, ih (y - 1) (by linarith) (by push_cast at hyn; linarith)]; ring

theorem genExp_genLog (x : ℝ) : simpleGenExp (simpleGenLog x) = x := by
  have hneg : ∀ x : ℝ, x < 0 → simpleGenExp (simpleGenLog x) = x := fun x hx => by
    rw [dlmf_4_12_8 hx, dlmf_4_12_6 (by linarith [exp_lt_one_iff.mpr hx]), sub_add_cancel, log_exp]
  suffices h : ∀ n : ℕ, ∀ x : ℝ, x < n → simpleGenExp (simpleGenLog x) = x from
    h (⌊x⌋₊ + 1) x (by
      rcases lt_or_ge x 0 with hx | hx
      · linarith [(Nat.cast_nonneg (⌊x⌋₊ + 1) : (0 : ℝ) ≤ _)]
      · exact_mod_cast Nat.lt_floor_add_one x)
  intro n
  induction n with
  | zero => intro x hx; exact hneg x (by simpa using hx)
  | succ n ih =>
    intro x hxn
    rcases lt_or_ge x 1 with h1 | h1
    · rcases lt_or_ge x 0 with h0 | h0
      · exact hneg x h0
      · rw [dlmf_4_12_5_log ⟨h0, h1.le⟩, dlmf_4_12_5_exp ⟨h0, h1.le⟩]
    · have hx0 : 0 < x := by linarith
      have hl := log_le_sub_one_of_pos hx0
      have hg : simpleGenLog x = simpleGenLog (log x) + 1 := by
        rw [add_comm, ← genLog_exp, exp_log hx0]
      rw [hg, isGenExp_genExp.1 _ (genLog_gt _), ih (log x) (by push_cast at hxn; linarith),
        exp_log hx0]

/-! ### Continuous differentiability -/

/-- Gluing at `0`: `g = f₁` on `(a, 0]`, `g = f₂` on `[0, b)`, with matching continuous
derivatives at `0`, is `C¹` on `(a, b)`. -/
theorem contDiffOn_glue {a b : ℝ} (ha : a < 0) (hb : 0 < b) {g f₁ f₂ d₁ d₂ : ℝ → ℝ}
    (h1 : ∀ x ∈ Ioc a 0, HasDerivAt f₁ (d₁ x) x) (h2 : ∀ x ∈ Ico 0 b, HasDerivAt f₂ (d₂ x) x)
    (hc1 : ∀ x ∈ Ioc a 0, ContinuousAt d₁ x) (hc2 : ∀ x ∈ Ico 0 b, ContinuousAt d₂ x)
    (hd0 : d₁ 0 = d₂ 0) (hg1 : ∀ x ∈ Ioc a 0, g x = f₁ x) (hg2 : ∀ x ∈ Ico 0 b, g x = f₂ x) :
    ContDiffOn ℝ 1 g (Ioo a b) := by
  set d : ℝ → ℝ := fun x => if x < 0 then d₁ x else d₂ x with hd
  have hnhds : Ioc a 0 ∪ Ico 0 b ∈ 𝓝 (0 : ℝ) :=
    mem_of_superset (Ioo_mem_nhds ha hb) fun x hx => by
      rcases le_or_gt x 0 with h | h
      · exact Or.inl ⟨hx.1, h⟩
      · exact Or.inr ⟨h.le, hx.2⟩
  have hderiv : ∀ x ∈ Ioo a b, HasDerivAt g (d x) x := by
    intro x hx
    rcases lt_trichotomy x 0 with h | rfl | h
    · have hev : g =ᶠ[𝓝 x] f₁ := eventually_of_mem (Ioo_mem_nhds hx.1 h) fun y hy =>
        hg1 y ⟨hy.1, hy.2.le⟩
      simp only [hd, h, ↓reduceIte]
      exact (h1 x ⟨hx.1, h.le⟩).congr_of_eventuallyEq hev
    · have hl : HasDerivWithinAt g (d₁ 0) (Ioc a 0) 0 :=
        (h1 0 ⟨ha, le_rfl⟩).hasDerivWithinAt.congr hg1 (hg1 0 ⟨ha, le_rfl⟩)
      have hr : HasDerivWithinAt g (d₁ 0) (Ico 0 b) 0 := by
        rw [hd0]; exact (h2 0 ⟨le_rfl, hb⟩).hasDerivWithinAt.congr hg2 (hg2 0 ⟨le_rfl, hb⟩)
      simp only [hd, lt_irrefl, ↓reduceIte]
      rw [← hd0]
      exact (hl.union hr).hasDerivAt hnhds
    · have hev : g =ᶠ[𝓝 x] f₂ := eventually_of_mem (Ioo_mem_nhds h hx.2) fun y hy =>
        hg2 y ⟨hy.1.le, hy.2⟩
      simp only [hd, not_lt.mpr h.le, ↓reduceIte]
      exact (h2 x ⟨h.le, hx.2⟩).congr_of_eventuallyEq hev
  have hcont : ∀ x ∈ Ioo a b, ContinuousAt d x := by
    intro x hx
    rcases lt_trichotomy x 0 with h | rfl | h
    · have hev : d₁ =ᶠ[𝓝 x] d := eventually_of_mem (Iio_mem_nhds h) fun y hy => by
        simp [hd, mem_Iio.mp hy]
      exact (hc1 x ⟨hx.1, h.le⟩).congr hev
    · have hl : ContinuousWithinAt d (Iic 0) 0 :=
        (hc1 0 ⟨ha, le_rfl⟩).continuousWithinAt.congr (fun y hy => by
          rcases (mem_Iic.mp hy).lt_or_eq with h' | rfl
          · simp [hd, h']
          · simp [hd, hd0]) (by simp [hd, hd0])
      have hr : ContinuousWithinAt d (Ici 0) 0 :=
        (hc2 0 ⟨le_rfl, hb⟩).continuousWithinAt.congr (fun y hy => by
          simp [hd, not_lt.mpr (mem_Ici.mp hy)]) (by simp [hd])
      have := hl.union hr
      rwa [Iic_union_Ici, continuousWithinAt_univ] at this
    · have hev : d₂ =ᶠ[𝓝 x] d := eventually_of_mem (Ioi_mem_nhds h) fun y hy => by
        simp [hd, not_lt.mpr (mem_Ioi.mp hy).le]
      exact (hc2 x ⟨h.le, hx.2⟩).congr hev
  rw [show (1 : WithTop ℕ∞) = 0 + 1 from rfl, contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioo]
  refine ⟨fun x hx => (hderiv x hx).differentiableAt.differentiableWithinAt, by simp, ?_⟩
  rw [contDiffOn_zero]
  have hdc : ContinuousOn d (Ioo a b) := fun x hx => (hcont x hx).continuousWithinAt
  exact hdc.congr fun x hx => (hderiv x hx).deriv

theorem contDiffOn_union_of_isOpen {f : ℝ → ℝ} {U V : Set ℝ} (hU : IsOpen U) (hV : IsOpen V)
    (h1 : ContDiffOn ℝ 1 f U) (h2 : ContDiffOn ℝ 1 f V) : ContDiffOn ℝ 1 f (U ∪ V) :=
  contDiffOn_of_locally_contDiffOn fun _ hx => hx.elim
    (fun hxU => ⟨U, hU, hxU, h1.mono inter_subset_right⟩)
    (fun hxV => ⟨V, hV, hxV, h2.mono inter_subset_right⟩)

theorem contDiffOn_genExp_base : ContDiffOn ℝ 1 simpleGenExp (Ioo (-1) 1) := by
    refine contDiffOn_glue (by norm_num) one_pos (f₁ := fun x => log (x + 1))
      (d₁ := fun x => (x + 1)⁻¹) (f₂ := id) (d₂ := fun _ => 1) (fun x hx => ?_)
      (fun x _ => hasDerivAt_id x) (fun x hx => ?_) (fun _ _ => continuousAt_const)
      (by norm_num) (fun x hx => ?_) (fun x hx => dlmf_4_12_5_exp ⟨hx.1, hx.2.le⟩)
    · have hx1 : x + 1 ≠ 0 := ne_of_gt (by linarith [hx.1])
      simpa [one_div] using ((hasDerivAt_id' x).add_const 1).log hx1
    · exact (continuous_id.add continuous_const).continuousAt.inv₀
        (ne_of_gt (by show (0 : ℝ) < x + 1; linarith [hx.1]))
    · rcases hx.2.lt_or_eq with h | rfl
      · exact dlmf_4_12_6 h
      · simp [dlmf_4_12_5_exp (x := 0) ⟨le_rfl, zero_le_one⟩]

theorem contDiffOn_genExp_aux (n : ℕ) : ContDiffOn ℝ 1 simpleGenExp (Ioo (-1) (n + 1)) := by
  induction n with
  | zero => simpa using contDiffOn_genExp_base
  | succ n ih =>
    have hV : ContDiffOn ℝ 1 simpleGenExp (Ioo 0 ((n + 1 : ℕ) + 1)) := by
      have hc : ContDiffOn ℝ 1 (fun x => exp (simpleGenExp (x - 1))) (Ioo 0 ((n + 1 : ℕ) + 1)) :=
        contDiff_exp.comp_contDiffOn (ih.comp (contDiffOn_id.sub contDiffOn_const)
          fun x hx => ⟨by show -1 < x - 1; linarith [hx.1], by
            show x - 1 < ((n : ℕ) : ℝ) + 1; push_cast at hx; linarith [hx.2]⟩)
      refine hc.congr fun x hx => ?_
      have := isGenExp_genExp.1 (x - 1) (by linarith [hx.1])
      rwa [sub_add_cancel] at this
    exact (contDiffOn_union_of_isOpen isOpen_Ioo isOpen_Ioo contDiffOn_genExp_base hV).mono
      fun x hx => by
        rcases lt_or_ge x 1 with h | h
        · exact Or.inl ⟨hx.1, h⟩
        · exact Or.inr ⟨by linarith, hx.2⟩

/-- **DLMF §4.12**: the simplest `φ` is continuously differentiable on `(−1, ∞)`. -/
theorem contDiffOn_genExp : ContDiffOn ℝ 1 simpleGenExp (Ioi (-1)) :=
  contDiffOn_of_locally_contDiffOn fun x hx =>
    ⟨Ioo (-1) (⌊x⌋₊ + 1), isOpen_Ioo, ⟨hx, Nat.lt_floor_add_one x⟩,
      (contDiffOn_genExp_aux ⌊x⌋₊).mono inter_subset_right⟩

theorem one_add_le_exp_iterate (n : ℕ) : (n : ℝ) + 1 ≤ exp^[n] 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply']; push_cast
    linarith [add_one_le_exp (exp^[n] 1)]

theorem contDiffOn_genLog_aux (n : ℕ) : ContDiffOn ℝ 1 simpleGenLog (Iio (exp^[n] 1)) := by
  induction n with
  | zero =>
    simp only [Function.iterate_zero, id]
    have hA : ContDiffOn ℝ 1 simpleGenLog (Iio 0) :=
      ((contDiff_exp.sub contDiff_const).contDiffOn).congr fun x hx => dlmf_4_12_8 hx
    have hB : ContDiffOn ℝ 1 simpleGenLog (Ioo (-1) 1) :=
      contDiffOn_glue (by norm_num) one_pos (f₁ := fun x => exp x - 1) (d₁ := exp)
        (f₂ := id) (d₂ := fun _ => 1) (fun x _ => (hasDerivAt_exp x).sub_const 1)
        (fun x _ => hasDerivAt_id x) (fun x _ => continuous_exp.continuousAt)
        (fun _ _ => continuousAt_const) (by simp)
        (fun x hx => by
          rcases hx.2.lt_or_eq with h | rfl
          · exact dlmf_4_12_8 h
          · simp [dlmf_4_12_5_log (x := 0) ⟨le_rfl, zero_le_one⟩])
        (fun x hx => dlmf_4_12_5_log ⟨hx.1, hx.2.le⟩)
    exact (contDiffOn_union_of_isOpen isOpen_Iio isOpen_Ioo hA hB).mono fun x hx => by
      rcases lt_or_ge x 0 with h | h
      · exact Or.inl h
      · exact Or.inr ⟨by linarith, hx⟩
  | succ n ih =>
    have hE : 0 < exp^[n] 1 := by
      linarith [one_add_le_exp_iterate n, (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    rw [Function.iterate_succ_apply']
    have hV : ContDiffOn ℝ 1 simpleGenLog (Ioo 0 (exp (exp^[n] 1))) := by
      have hc : ContDiffOn ℝ 1 (fun x => 1 + simpleGenLog (log x)) (Ioo 0 (exp (exp^[n] 1))) :=
        contDiffOn_const.add (ih.comp (contDiffOn_log.mono fun x hx => (mem_Ioo.mp hx).1.ne')
          fun x hx => (log_lt_iff_lt_exp hx.1).mpr hx.2)
      refine hc.congr fun x hx => ?_
      rw [← genLog_exp, exp_log hx.1]
    exact (contDiffOn_union_of_isOpen isOpen_Iio isOpen_Ioo ih hV).mono fun x hx => by
      rcases lt_or_ge x (exp^[n] 1) with h | h
      · exact Or.inl h
      · exact Or.inr ⟨by linarith, hx⟩

/-- **DLMF §4.12**: the simplest `ψ` is continuously differentiable on `ℝ`. -/
theorem contDiff_genLog : ContDiff ℝ 1 simpleGenLog := by
  rw [← contDiffOn_univ]
  exact contDiffOn_of_locally_contDiffOn fun x _ =>
    ⟨Iio (exp^[⌊x⌋₊] 1), isOpen_Iio,
      by show x < _; linarith [Nat.lt_floor_add_one x, one_add_le_exp_iterate ⌊x⌋₊],
      (contDiffOn_genLog_aux ⌊x⌋₊).mono inter_subset_right⟩

end Azurite.DLMF
