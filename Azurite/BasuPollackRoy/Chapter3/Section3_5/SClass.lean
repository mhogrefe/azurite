/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Azurite.BasuPollackRoy.Chapter3.Section3_5.TotalDeriv

/-! # BPR §3.5 — the classes `𝒮^ℓ(U, B)` and Nash functions

Let `U ⊆ R^k` be a semialgebraic open set and `B ⊆ R^p` a semialgebraic set. The set of
semialgebraic functions from `U` to `B` for which all partial derivatives up to order `ℓ`
exist and are continuous is denoted `𝒮^ℓ(U, B)` (`SClass ℓ U B`; order `0` means
semialgebraic and continuous), and the class `𝒮^∞(U, B)` is the intersection of
`𝒮^ℓ(U, B)` for all finite `ℓ` (`SClassInfty`). The ring `𝒮^ℓ(U, R)` is abbreviated
`𝒮^ℓ(U)` (`sFunctions`, a `Subring` of all functions `R^k → R`), and the ring
`𝒮^∞(U, R)` is also called the **ring of Nash functions** (`nashFunctions`).

The scalar predicate `IsSFunction ℓ U c` is recursive: order `0` is
`IsSemialgContinuousOn`, and order `ℓ + 1` additionally requires every partial derivative
to exist on `U` with a value function of class `ℓ` (existence suffices: the value function
is unique on open `U` by `HasPartialDerivAtIn.unique`, and automatically semialgebraic by
`isSemialgebraicFunction_partialDeriv`).

The ring structure rests on the sum and product rules for the derivative
(`HasDerivAtIn.add`, `HasDerivAtIn.mul` — the latter via the limit algebra
`LimitAtInR.add`/`LimitAtInR.mul`), lifted to partial derivatives and propagated through
the orders by induction (`IsSFunction.add`, `IsSFunction.mul`, `IsSFunction.neg`). -/

namespace Azurite.BPR

open MvPolynomial

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]

/-! ### Limit algebra -/

omit [IsStrictOrderedRing R] [IsRealClosed R] in
theorem LimitAtInR.congr {g₁ g₂ : R → R} {M : Set R} {x₀ y₀ : R}
    (hcong : ∀ t ∈ M, t ≠ x₀ → g₁ t = g₂ t) (h : LimitAtInR g₁ M x₀ y₀) :
    LimitAtInR g₂ M x₀ y₀ := fun r hr =>
  let ⟨δ, hδ, hb⟩ := h r hr
  ⟨δ, hδ, fun t htM htne htδ => by
    rw [← hcong t htM htne]
    exact hb t htM htne htδ⟩

omit [IsRealClosed R] in
theorem LimitAtInR.add {g₁ g₂ : R → R} {M : Set R} {x₀ y₁ y₂ : R}
    (h₁ : LimitAtInR g₁ M x₀ y₁) (h₂ : LimitAtInR g₂ M x₀ y₂) :
    LimitAtInR (fun t => g₁ t + g₂ t) M x₀ (y₁ + y₂) := by
  intro r hr
  obtain ⟨δ₁, hδ₁, hb₁⟩ := h₁ (r / 2) (by linarith)
  obtain ⟨δ₂, hδ₂, hb₂⟩ := h₂ (r / 2) (by linarith)
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun t htM htne htδ => ?_⟩
  have e₁ := hb₁ t htM htne (htδ.trans_le (min_le_left _ _))
  have e₂ := hb₂ t htM htne (htδ.trans_le (min_le_right _ _))
  have hident : g₁ t + g₂ t - (y₁ + y₂) = (g₁ t - y₁) + (g₂ t - y₂) := by ring
  rw [hident]
  calc |(g₁ t - y₁) + (g₂ t - y₂)| ≤ |g₁ t - y₁| + |g₂ t - y₂| := abs_add_le _ _
    _ < r / 2 + r / 2 := add_lt_add e₁ e₂
    _ = r := by ring

omit [IsStrictOrderedRing R] [IsRealClosed R] in
theorem LimitAtInR.neg {g : R → R} {M : Set R} {x₀ y₀ : R}
    (h : LimitAtInR g M x₀ y₀) : LimitAtInR (fun t => -(g t)) M x₀ (-y₀) := fun r hr =>
  let ⟨δ, hδ, hb⟩ := h r hr
  ⟨δ, hδ, fun t htM htne htδ => by
    have := hb t htM htne htδ
    have hident : -(g t) - -y₀ = -(g t - y₀) := by ring
    rw [hident, abs_neg]
    exact this⟩

omit [IsRealClosed R] in
theorem LimitAtInR.mul {g₁ g₂ : R → R} {M : Set R} {x₀ y₁ y₂ : R}
    (h₁ : LimitAtInR g₁ M x₀ y₁) (h₂ : LimitAtInR g₂ M x₀ y₂) :
    LimitAtInR (fun t => g₁ t * g₂ t) M x₀ (y₁ * y₂) := by
  intro r hr
  -- bound the moduli of the limits and a window for `g₁`
  have hB : 0 < |y₁| + |y₂| + 1 := by positivity
  set ε : R := min 1 (r / (2 * (|y₁| + |y₂| + 1))) with hεd
  have hε : 0 < ε := lt_min one_pos (by positivity)
  obtain ⟨δ₁, hδ₁, hb₁⟩ := h₁ ε hε
  obtain ⟨δ₂, hδ₂, hb₂⟩ := h₂ ε hε
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun t htM htne htδ => ?_⟩
  have e₁ := hb₁ t htM htne (htδ.trans_le (min_le_left _ _))
  have e₂ := hb₂ t htM htne (htδ.trans_le (min_le_right _ _))
  -- `g₁ g₂ − y₁ y₂ = g₁ (g₂ − y₂) + y₂ (g₁ − y₁)`
  have hident : g₁ t * g₂ t - y₁ * y₂
      = g₁ t * (g₂ t - y₂) + y₂ * (g₁ t - y₁) := by ring
  have hg₁ : |g₁ t| ≤ |y₁| + 1 := by
    have h := abs_add_le (g₁ t - y₁) y₁
    have : g₁ t - y₁ + y₁ = g₁ t := by ring
    rw [this] at h
    have hε1 : ε ≤ 1 := min_le_left _ _
    linarith
  have hεr : ε ≤ r / (2 * (|y₁| + |y₂| + 1)) := min_le_right _ _
  rw [hident]
  calc |g₁ t * (g₂ t - y₂) + y₂ * (g₁ t - y₁)|
      ≤ |g₁ t * (g₂ t - y₂)| + |y₂ * (g₁ t - y₁)| := abs_add_le _ _
    _ = |g₁ t| * |g₂ t - y₂| + |y₂| * |g₁ t - y₁| := by rw [abs_mul, abs_mul]
    _ ≤ (|y₁| + 1) * ε + |y₂| * ε := by
        refine add_le_add ?_ ?_
        · exact mul_le_mul hg₁ e₂.le (abs_nonneg _) (by positivity)
        · exact mul_le_mul_of_nonneg_left e₁.le (abs_nonneg _)
    _ = (|y₁| + |y₂| + 1) * ε := by ring
    _ ≤ (|y₁| + |y₂| + 1) * (r / (2 * (|y₁| + |y₂| + 1))) :=
        mul_le_mul_of_nonneg_left hεr (by positivity)
    _ = r / 2 := by field_simp
    _ < r := by linarith

omit [IsRealClosed R] in
theorem limitAtInR_const (M : Set R) (x₀ a : R) :
    LimitAtInR (fun _ => a) M x₀ a := fun r hr =>
  ⟨1, one_pos, fun t _ _ _ => by rw [sub_self, abs_zero]; exact hr⟩

/-! ### Derivative algebra: sum and product rules -/

omit [IsRealClosed R] in
/-- **Sum rule.** -/
theorem HasDerivAtIn.add {g₁ g₂ : R → R} {M : Set R} {x₀ d₁ d₂ : R}
    (h₁ : HasDerivAtIn g₁ M x₀ d₁) (h₂ : HasDerivAtIn g₂ M x₀ d₂) :
    HasDerivAtIn (fun t => g₁ t + g₂ t) M x₀ (d₁ + d₂) := by
  refine LimitAtInR.congr (g₁ := fun t =>
    (g₁ t - g₁ x₀) / (t - x₀) + (g₂ t - g₂ x₀) / (t - x₀)) ?_
    (LimitAtInR.add h₁ h₂)
  intro t _ htne
  have hts : t - x₀ ≠ 0 := sub_ne_zero.mpr htne
  field_simp
  ring

omit [IsRealClosed R] in
/-- **Product rule.** -/
theorem HasDerivAtIn.mul {g₁ g₂ : R → R} {M : Set R} {x₀ d₁ d₂ : R}
    (h₁ : HasDerivAtIn g₁ M x₀ d₁) (h₂ : HasDerivAtIn g₂ M x₀ d₂) :
    HasDerivAtIn (fun t => g₁ t * g₂ t) M x₀ (g₁ x₀ * d₂ + g₂ x₀ * d₁) := by
  have hcont₁ : LimitAtInR g₁ M x₀ (g₁ x₀) := h₁.limitAtInR_self
  have hcomb : LimitAtInR (fun t =>
      g₁ t * ((g₂ t - g₂ x₀) / (t - x₀)) + g₂ x₀ * ((g₁ t - g₁ x₀) / (t - x₀)))
      M x₀ (g₁ x₀ * d₂ + g₂ x₀ * d₁) :=
    LimitAtInR.add (LimitAtInR.mul hcont₁ h₂)
      (LimitAtInR.mul (limitAtInR_const M x₀ (g₂ x₀)) h₁)
  refine LimitAtInR.congr ?_ hcomb
  intro t _ htne
  have hts : t - x₀ ≠ 0 := sub_ne_zero.mpr htne
  field_simp
  ring

omit [IsRealClosed R] in
/-- Constant functions have derivative `0` everywhere (special case of
`hasDerivAtIn_of_constOn`). -/
theorem hasDerivAtIn_const (a : R) (M : Set R) (x₀ : R) :
    HasDerivAtIn (fun _ => a) M x₀ 0 :=
  hasDerivAtIn_of_constOn (fun _ _ => rfl) rfl

/-! ### Partial-derivative algebra -/

omit [IsRealClosed R] in
theorem HasPartialDerivAtIn.add {k : ℕ} {c₁ c₂ : (Fin k → R) → R} {U : Set (Fin k → R)}
    {i : Fin k} {x : Fin k → R} {d₁ d₂ : R}
    (h₁ : HasPartialDerivAtIn c₁ U i x d₁) (h₂ : HasPartialDerivAtIn c₂ U i x d₂) :
    HasPartialDerivAtIn (fun y => c₁ y + c₂ y) U i x (d₁ + d₂) :=
  HasDerivAtIn.add h₁ h₂

omit [IsRealClosed R] in
theorem HasPartialDerivAtIn.mul {k : ℕ} {c₁ c₂ : (Fin k → R) → R} {U : Set (Fin k → R)}
    {i : Fin k} {x : Fin k → R} {d₁ d₂ : R}
    (h₁ : HasPartialDerivAtIn c₁ U i x d₁) (h₂ : HasPartialDerivAtIn c₂ U i x d₂) :
    HasPartialDerivAtIn (fun y => c₁ y * c₂ y) U i x
      (c₁ (Function.update x i (x i)) * d₂ + c₂ (Function.update x i (x i)) * d₁) :=
  HasDerivAtIn.mul h₁ h₂

omit [IsStrictOrderedRing R] [IsRealClosed R] in
theorem HasPartialDerivAtIn.neg {k : ℕ} {c : (Fin k → R) → R} {U : Set (Fin k → R)}
    {i : Fin k} {x : Fin k → R} {d : R} (h : HasPartialDerivAtIn c U i x d) :
    HasPartialDerivAtIn (fun y => -(c y)) U i x (-d) :=
  HasDerivAtIn.neg h

omit [IsRealClosed R] in
theorem hasPartialDerivAtIn_const {k : ℕ} (a : R) (U : Set (Fin k → R)) (i : Fin k)
    (x : Fin k → R) : HasPartialDerivAtIn (fun _ => a) U i x 0 :=
  hasDerivAtIn_const a _ _

/-! ### `IsSemialgContinuousOn` constants (the binary closures `IsSemialgContinuousOn.add`,
`.mul`, `.neg` are provided by `Azurite/BasuPollackRoy/Chapter3/Section3_3`) -/

theorem isSemialgContinuousOn_constFun {k : ℕ} {U : Set (Fin k → R)}
    (hU : IsSemialgebraicSet U) (a : R) :
    IsSemialgContinuousOn U (fun _ => a) := by
  constructor
  · have heq : scalarFun (fun _ : Fin k → R => a) = polyFun (C a) :=
      funext fun u => funext fun i => by simp [scalarFun, polyFun, constPt]
    rw [heq]
    exact polyFun_isSemialgebraicFunction_on hU _
  · exact continuousOn_const

/-! ### The classes `𝒮^ℓ` -/

/-- The scalar class `𝒮^ℓ(U)`, recursively: order `0` is semialgebraic-and-continuous,
and order `ℓ + 1` additionally requires every partial derivative to exist on `U` with a
value function of class `ℓ`. -/
def IsSFunction {k : ℕ} : ℕ → Set (Fin k → R) → ((Fin k → R) → R) → Prop
  | 0, U, c => IsSemialgContinuousOn U c
  | ℓ + 1, U, c => IsSemialgContinuousOn U c ∧
      ∀ j : Fin k, ∃ gj : (Fin k → R) → R,
        (∀ x ∈ U, HasPartialDerivAtIn c U j x (gj x)) ∧ IsSFunction ℓ U gj

omit [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R] in
theorem isSFunction_zero_iff {k : ℕ} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    [IsRealClosed R] {U : Set (Fin k → R)} {c : (Fin k → R) → R} :
    IsSFunction 0 U c ↔ IsSemialgContinuousOn U c := Iff.rfl

omit [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R] in
theorem isSFunction_succ_iff {k ℓ : ℕ} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    [IsRealClosed R] {U : Set (Fin k → R)} {c : (Fin k → R) → R} :
    IsSFunction (ℓ + 1) U c ↔ IsSemialgContinuousOn U c ∧
      ∀ j : Fin k, ∃ gj : (Fin k → R) → R,
        (∀ x ∈ U, HasPartialDerivAtIn c U j x (gj x)) ∧ IsSFunction ℓ U gj := Iff.rfl

/-- Every order includes the order-`0` data. -/
theorem IsSFunction.isSemialgContinuousOn {k ℓ : ℕ} {U : Set (Fin k → R)}
    {c : (Fin k → R) → R} (h : IsSFunction ℓ U c) : IsSemialgContinuousOn U c := by
  cases ℓ with
  | zero => exact h
  | succ ℓ => exact h.1

/-- `𝒮^{ℓ+1} ⊆ 𝒮^ℓ`. -/
theorem IsSFunction.of_succ {k : ℕ} {U : Set (Fin k → R)} :
    ∀ {ℓ : ℕ} {c : (Fin k → R) → R}, IsSFunction (ℓ + 1) U c → IsSFunction ℓ U c
  | 0, _, h => h.1
  | _ + 1, _, h =>
    ⟨h.1, fun j =>
      let ⟨gj, hgj, hS⟩ := h.2 j
      ⟨gj, hgj, hS.of_succ⟩⟩

/-- `𝒮^ℓ` is antitone in the order. -/
theorem IsSFunction.mono {k : ℕ} {U : Set (Fin k → R)} {c : (Fin k → R) → R}
    {ℓ m : ℕ} (hml : m ≤ ℓ) (h : IsSFunction ℓ U c) : IsSFunction m U c := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hml
  clear hml
  induction n with
  | zero => exact h
  | succ n ih => exact ih h.of_succ

/-- **`𝒮^ℓ(U, B)`**: the set of semialgebraic functions from `U` to `B` for which all
partial derivatives up to order `ℓ` exist and are continuous (coordinatewise
`IsSFunction`, with the map sending `U` into `B`). -/
def SClass {k p : ℕ} (ℓ : ℕ) (U : Set (Fin k → R)) (B : Set (Fin p → R)) :
    Set ((Fin k → R) → (Fin p → R)) :=
  {f | Set.MapsTo f U B ∧ ∀ l : Fin p, IsSFunction ℓ U (fun y => f y l)}

/-- **`𝒮^∞(U, B)`**: the intersection of the `𝒮^ℓ(U, B)` for all finite `ℓ`. -/
def SClassInfty {k p : ℕ} (U : Set (Fin k → R)) (B : Set (Fin p → R)) :
    Set ((Fin k → R) → (Fin p → R)) :=
  ⋂ ℓ : ℕ, SClass ℓ U B

omit [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R] in
theorem mem_sClassInfty_iff {k p : ℕ} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    [IsRealClosed R] {U : Set (Fin k → R)} {B : Set (Fin p → R)}
    {f : (Fin k → R) → (Fin p → R)} :
    f ∈ SClassInfty U B ↔ ∀ ℓ : ℕ, f ∈ SClass ℓ U B := Set.mem_iInter

omit [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R] in
/-- `𝒮^ℓ(U, B)` is antitone in `ℓ`. -/
theorem SClass.antitone {k p : ℕ} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    [IsRealClosed R] {U : Set (Fin k → R)} {B : Set (Fin p → R)} {ℓ m : ℕ} (hml : m ≤ ℓ) :
    SClass (R := R) (k := k) (p := p) ℓ U B ⊆ SClass m U B :=
  fun _ hf => ⟨hf.1, fun l => (hf.2 l).mono hml⟩

/-! ### Ring structure -/

/-- Constants are `𝒮^ℓ` for every `ℓ`. -/
theorem isSFunction_const {k : ℕ} {U : Set (Fin k → R)} (hU : IsSemialgebraicSet U)
    (a : R) : ∀ ℓ : ℕ, IsSFunction ℓ U (fun _ : Fin k → R => a)
  | 0 => isSemialgContinuousOn_constFun hU a
  | ℓ + 1 =>
    ⟨isSemialgContinuousOn_constFun hU a, fun j =>
      ⟨fun _ => 0, fun x _ => hasPartialDerivAtIn_const a U j x,
        isSFunction_const hU 0 ℓ⟩⟩

/-- `𝒮^ℓ` is closed under addition and multiplication (simultaneous induction: the
product rule at order `ℓ + 1` consumes both closures at order `ℓ`). -/
theorem isSFunction_add_mul {k : ℕ} {U : Set (Fin k → R)} (hU : IsSemialgebraicSet U) :
    ∀ ℓ : ℕ,
      (∀ c₁ c₂ : (Fin k → R) → R, IsSFunction ℓ U c₁ → IsSFunction ℓ U c₂ →
        IsSFunction ℓ U (fun y => c₁ y + c₂ y)) ∧
      (∀ c₁ c₂ : (Fin k → R) → R, IsSFunction ℓ U c₁ → IsSFunction ℓ U c₂ →
        IsSFunction ℓ U (fun y => c₁ y * c₂ y))
  | 0 => ⟨fun _ _ h₁ h₂ => IsSemialgContinuousOn.add hU h₁ h₂,
      fun _ _ h₁ h₂ => IsSemialgContinuousOn.mul hU h₁ h₂⟩
  | ℓ + 1 => by
    obtain ⟨ihadd, ihmul⟩ := isSFunction_add_mul (U := U) hU ℓ
    constructor
    · rintro c₁ c₂ ⟨hsc₁, hd₁⟩ ⟨hsc₂, hd₂⟩
      refine ⟨IsSemialgContinuousOn.add hU hsc₁ hsc₂, fun j => ?_⟩
      obtain ⟨g₁, hg₁, hS₁⟩ := hd₁ j
      obtain ⟨g₂, hg₂, hS₂⟩ := hd₂ j
      exact ⟨fun y => g₁ y + g₂ y,
        fun x hx => (hg₁ x hx).add (hg₂ x hx), ihadd _ _ hS₁ hS₂⟩
    · rintro c₁ c₂ ⟨hsc₁, hd₁⟩ ⟨hsc₂, hd₂⟩
      refine ⟨IsSemialgContinuousOn.mul hU hsc₁ hsc₂, fun j => ?_⟩
      obtain ⟨g₁, hg₁, hS₁⟩ := hd₁ j
      obtain ⟨g₂, hg₂, hS₂⟩ := hd₂ j
      refine ⟨fun y => c₁ y * g₂ y + c₂ y * g₁ y, fun x hx => ?_, ?_⟩
      · have h := (hg₁ x hx).mul (hg₂ x hx)
        simp only [Function.update_eq_self] at h
        exact h
      · -- `c₁ g₂ + c₂ g₁ ∈ 𝒮^ℓ`: products of an `𝒮^{ℓ+1}` (hence `𝒮^ℓ`) function
        -- with an `𝒮^ℓ` one, then a sum
        have hc₁ℓ : IsSFunction ℓ U c₁ := IsSFunction.of_succ ⟨hsc₁, hd₁⟩
        have hc₂ℓ : IsSFunction ℓ U c₂ := IsSFunction.of_succ ⟨hsc₂, hd₂⟩
        exact ihadd _ _ (ihmul _ _ hc₁ℓ hS₂) (ihmul _ _ hc₂ℓ hS₁)

theorem IsSFunction.add' {k ℓ : ℕ} {U : Set (Fin k → R)} {c₁ c₂ : (Fin k → R) → R}
    (hU : IsSemialgebraicSet U) (h₁ : IsSFunction ℓ U c₁) (h₂ : IsSFunction ℓ U c₂) :
    IsSFunction ℓ U (fun y => c₁ y + c₂ y) :=
  (isSFunction_add_mul hU ℓ).1 _ _ h₁ h₂

theorem IsSFunction.mul' {k ℓ : ℕ} {U : Set (Fin k → R)} {c₁ c₂ : (Fin k → R) → R}
    (hU : IsSemialgebraicSet U) (h₁ : IsSFunction ℓ U c₁) (h₂ : IsSFunction ℓ U c₂) :
    IsSFunction ℓ U (fun y => c₁ y * c₂ y) :=
  (isSFunction_add_mul hU ℓ).2 _ _ h₁ h₂

theorem IsSFunction.neg' {k : ℕ} {U : Set (Fin k → R)} (hU : IsSemialgebraicSet U) :
    ∀ {ℓ : ℕ} {c : (Fin k → R) → R}, IsSFunction ℓ U c →
      IsSFunction ℓ U (fun y => -(c y))
  | 0, _, h => IsSemialgContinuousOn.neg hU h
  | _ + 1, _, h =>
    ⟨IsSemialgContinuousOn.neg hU h.1, fun j =>
      let ⟨gj, hgj, hS⟩ := h.2 j
      ⟨fun y => -(gj y), fun x hx => (hgj x hx).neg, IsSFunction.neg' hU hS⟩⟩

/-- **The ring `𝒮^ℓ(U)`** (BPR's `𝒮^ℓ(U, R)`), as a subring of all functions
`R^k → R`. -/
def sFunctions {k : ℕ} (ℓ : ℕ) (U : Set (Fin k → R)) (hU : IsSemialgebraicSet U) :
    Subring ((Fin k → R) → R) where
  carrier := {c | IsSFunction ℓ U c}
  zero_mem' := isSFunction_const hU 0 ℓ
  one_mem' := isSFunction_const hU 1 ℓ
  add_mem' h₁ h₂ := h₁.add' hU h₂
  mul_mem' h₁ h₂ := h₁.mul' hU h₂
  neg_mem' h := IsSFunction.neg' hU h

/-- **The ring of Nash functions `𝒮^∞(U)`** (BPR's `𝒮^∞(U, R)`), as a subring of all
functions `R^k → R`: scalar functions of class `𝒮^ℓ` for every finite `ℓ`. -/
def nashFunctions {k : ℕ} (U : Set (Fin k → R)) (hU : IsSemialgebraicSet U) :
    Subring ((Fin k → R) → R) where
  carrier := {c | ∀ ℓ : ℕ, IsSFunction ℓ U c}
  zero_mem' ℓ := isSFunction_const hU 0 ℓ
  one_mem' ℓ := isSFunction_const hU 1 ℓ
  add_mem' h₁ h₂ ℓ := (h₁ ℓ).add' hU (h₂ ℓ)
  mul_mem' h₁ h₂ ℓ := (h₁ ℓ).mul' hU (h₂ ℓ)
  neg_mem' h ℓ := IsSFunction.neg' hU (h ℓ)

end Azurite.BPR
